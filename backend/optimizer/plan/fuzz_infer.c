#include "postgres.h"
#include <limits.h>
#include <math.h>
#include <assert.h>
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "nodes/primnodes.h"
#include "nodes/nodes.h"
#include "nodes/pg_list.h"
#include "catalog/pg_statistic_d.h"

#include "parser/parse_node.h"

#include "optimizer/fuzz_infer.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/appendinfo.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/inherit.h"
#include "optimizer/optimizer.h"
#include "optimizer/paramassign.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/plancat.h"
#include "optimizer/planmain.h"
#include "optimizer/planner.h"
#include "optimizer/prep.h"
#include "optimizer/subselect.h"
#include "optimizer/tlist.h"

#include "utils/float.h"
#include "utils/selfuncs.h"
#include "utils/lsyscache.h"
#include "utils/numeric.h"




double query_var_average(PlannerInfo *root, Var *var)
{
    int sz;
    VariableStatData vardata;
	AttStatsSlot sslot;

    if (!IsA(var, Var))
    {
        elog(WARNING, "<query_var_average> TYPE_ERROR: arg->type = [%d], T_Var = [%d]", ((Node*)var)->type, T_Var);
        return 0.0;
    }
    

    examine_variable(root, (Node *)var, 0, &vardata);
    get_attstatsslot(&sslot, vardata.statsTuple, STATISTIC_KIND_HISTOGRAM,
			0, ATTSTATSSLOT_VALUES);
    sz = sslot.nvalues;

    if (sz == 0)
    {
        elog(WARNING, "<query_var_average> size == 0, returnning 0.0");
        return 0.0;
    }
    
    return datum_to_double(sslot.values[(sz + 1) / 2]);
}


OpExpr *copy_and_transpose(PlannerInfo *root, OpExpr *curop, int reserve_relid)
{
    Var *obj_var;
    Var *copied_var;
    double obj_ratio = 0.0;
    double deleted_value;
    double new_value;
    OpExpr *copied_cur;
    OpExpr *agri_expr = (OpExpr *) linitial(curop->args);
    Const *const_value = (Const *) lsecond(curop->args);
    Const *new_const;

    collect_var_info(root, (Expr *)agri_expr, reserve_relid, &obj_var, &obj_ratio, &deleted_value);

    if ((obj_ratio < 0 ? -obj_ratio : obj_ratio) < 1e-9)
    {
        elog(ERROR, "<copy_and_transpose> obj_ratio = 0.");
    }
    new_value = (datum_to_double(const_value->constvalue) - deleted_value) / obj_ratio;

    // TODO 接下来应该是利用 obj_bar 和  new_value 组成一个新的 OpExpr
    // 然后用这个 OpExpr 来获得选择率
    copied_var = (Var *) copyObject(curop);
    new_const = create_const_from_double(new_value);
    copied_cur = (OpExpr *) copyObject(curop);
    copied_cur->args = list_make2(copied_var, new_const);
    elog(WARNING, "<copy_and_transpose> new_const = [%lf]", new_value);
    return copied_cur;
}


bool collect_var_info(PlannerInfo *root, Expr *cur, int reserve_relid,
                    Var **obj_var, double *obj_ratio, double *deleted_value)
{
    Expr *lefttree;
    Expr *righttree;
    bool lresult;
    bool rresult;

    OpExpr *opcur;
    Const *sonconst;
    Var *sonvar;
    Var *curvar;

    if (IsA(cur, Var))
    {
        curvar = (Var *) cur;
        elog(WARNING, "[curvar->varno] = [%d]", curvar->varno);
        if (curvar->varno == reserve_relid)
        {
            *obj_var = curvar;
            return true;
        }    
        else
            return false;
    }
    else if (IsA(cur, Const))
    {
        return false;
    }


    opcur = (OpExpr *) cur;
    lefttree = linitial(opcur->args);
    righttree = lsecond(opcur->args);

    switch (opcur->opno)
    {
        case 1758:   // '+' for NUMERIC

            lresult = collect_var_info(root, lefttree,  reserve_relid, obj_var, obj_ratio, deleted_value);
            rresult = collect_var_info(root, righttree, reserve_relid, obj_var, obj_ratio, deleted_value);
            elog(WARNING, "<> <> Entering 1758.");

            if (lresult || rresult)
            {
                *obj_ratio = 1.0;
            }

            if (!lresult)
            {
                if (IsA(lefttree, Var))
                {
                    *deleted_value += query_var_average(root, (Var *) lefttree);
                }
                    
                if (IsA(lefttree, Const))
                {
                    sonconst = (Const *) lefttree;
                    *deleted_value += datum_to_double(sonconst->constvalue);
                }
            }

            if (!rresult)
            {
                if (IsA(righttree, Var))
                {
                    *deleted_value += query_var_average(root, (Var *) righttree);
                }
                    
                if (IsA(righttree, Const))
                {
                    sonconst = (Const *) righttree;
                    *deleted_value += datum_to_double(sonconst->constvalue);
                }
            }
            

            break;
        
        case 1760:   // '*' for NUMERIC;

            lresult = collect_var_info(root, lefttree,  reserve_relid, obj_var, obj_ratio, deleted_value);
            rresult = collect_var_info(root, righttree, reserve_relid, obj_var, obj_ratio, deleted_value);

            if (lresult)
            {
                sonconst = (Const *) righttree;
                *obj_ratio = datum_to_double(sonconst->constvalue);
            }
            else if (rresult)
            {
                sonconst = (Const *) lefttree;
                *obj_ratio = datum_to_double(sonconst->constvalue);
            }
            else if (IsA(lefttree, Var))
            {
                sonconst = (Const *) righttree;
                *deleted_value += query_var_average(root, (Var *)lefttree) * datum_to_double(sonconst->constvalue);
            }
            else if (IsA(righttree, Var))
            {
                sonconst = (Const *) lefttree;
                *deleted_value += query_var_average(root, (Var *)righttree) * datum_to_double(sonconst->constvalue);
            }
            else 
                elog(WARNING, "<collect_var_info> Well, I do not know what happened.");


            break;

        default:
            elog(WARNING, "<collect_var_info> Detected quirky opno: [%d]", opcur->opno);
    }
    return false;
}



// 关于转换值和创建节点的函数

double datum_to_double(Datum datum) {
	double val = convert_numeric_to_scalar(datum, NUMERICOID, NULL);
	return val;
}

Const *create_const_from_double(double v) 
{
	char *fval;
	Value *val;
	
	fval = (char *) palloc(16 + 1);	 // 我只是猜测这里是 16 位
	sprintf(fval, "%f", v);
	val = makeFloat(fval);
	return make_const(NULL, val, -1);
}