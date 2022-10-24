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

#include "optimizer/lfindex.h"
#include "optimizer/plannode_function.h"


// ************************** 预处理部分 *******************


void preprocess_filters(PlannerInfo *pni, LFIndex *lfi, Expr *cur_op, List *ridlist, List *depthlist, List** filterlist)
{
    int i, j, temp1, temp2, r1, r2;
    int len = ridlist->length;
    double whatever = 0;
    Expr *input_expr = cur_op;
    Expr *res_expr;
    
    double *factorlist = palloc((len + 1) * sizeof(double));
    double *selectivity_list = palloc((len + 1) * sizeof(double));
    double theconst = 0.0;
    double tempvalue;
    double tempconst;

    List *varlist = NIL;
    Var *obj_var;

    // Const *rhsnode = (Const *) lsecond(((OpExpr *) cur_op)->args);
    double *rightconst = palloc((len + 1) * sizeof(double));

    // 保证深度从小到大
    for (i = len - 1; i >= 1; i--)
        for (j = i - 1; j >= 0; j--)
            if (list_nth_int(depthlist, j) > list_nth_int(depthlist, i))
            {
                temp1 = list_nth_int(depthlist, i);
                temp2 = list_nth_int(depthlist, j);

                r1 = list_nth_int(ridlist, i);
                r2 = list_nth_int(ridlist, j);

                lfirst_int(list_nth_cell(depthlist, i)) = temp2;
                lfirst_int(list_nth_cell(depthlist, j)) = temp1;

                lfirst_int(list_nth_cell(ridlist, i)) = r2;
                lfirst_int(list_nth_cell(ridlist, j)) = r1;
            }
    
    // 每次使用 copy_and_reserve 去除一个 relid
    // XXX 这里假设了每个 relid 都只包含一个 feature！
    *filterlist = lappend(*filterlist, cur_op);
    rightconst[0] =  constvalue_to_double(((Const *) lsecond(((OpExpr *) cur_op)->args))->constvalue);

    // feature1 + feature2 + feature3 < 10
    // 根据深度排序：(feature1, feature2, feature3)
    // 移除 feature1 ==> feature2 + featuer3 ...
    // 移除 feature2 ==> feature3 ...


    elog(WARNING, "<preprocess_filters>  loop begin.");
    for (i = 0; i < len; i++)
    {
        res_expr = copy_and_delete_op(input_expr, list_nth_int(ridlist, i), lfi, &whatever, 1, &tempvalue, &tempconst);
        rightconst[i + 1] = constvalue_to_double(((Const *) lsecond(((OpExpr *) res_expr)->args))->constvalue);

        *filterlist = lappend(*filterlist, res_expr);
        input_expr = res_expr;

        factorlist[i] = tempvalue;

        if (theconst == 0.0)
            theconst = tempconst;

        elog(WARNING, "<preprocess_filters> ridlist[%d] = [%d], factor[i] = [%.15f]", i, list_nth_int(ridlist, i), tempvalue);

        collect_var_info(pni, linitial(((OpExpr *)cur_op)->args)
            , list_nth_int(ridlist, i), &obj_var, &tempvalue, &tempconst);
        varlist = lappend(varlist, obj_var);
    }

    elog(WARNING, "<preprocess_filters> loop is ok..");
    elog(WARNING, "<preprocess_filters> varlist->length = [%d]", varlist->length);
    elog(WARNING, "<preprocess_filters> varlist[0] = [%p]", list_nth(varlist, 0));
    elog(WARNING, "<preprocess_filters> varno = [%d]", ((Var*)list_nth(varlist, 0))->varno);

    // varlist:     feature1 feature2 feature3
    // factorlist:  1.0        2.0      3.0
    // rightconsts: 10.0          8.0     5.0
    // feature1 + feature2 + feature2 + 1.23(theconst) < rightconst[i]

    selectivity_list[0] = calc_selec(pni, varlist, factorlist, len, theconst, rightconst, 0);
    selectivity_list[1] = calc_selec(pni, varlist, factorlist, len, theconst, rightconst, 1);
    selectivity_list[2] = calc_selec(pni, varlist, factorlist, len, theconst, rightconst, 2);
    selectivity_list[3] = calc_selec(pni, varlist, factorlist, len, theconst, rightconst, 3);

    for (i = 0; i < len; i += 1)
    {
        elog(WARNING, "<preprocess_filters> selectivity_list[%d] = [%.10f]", i, selectivity_list[i]);
    }

    elog(WARNING, "<preprocess_filters> the const = [%lf]", theconst);
    elog(WARNING, "\n<preprocess_filters> is ok, (*filterlist)->length = [%d].", (*filterlist)->length);
}

double calc_selec(PlannerInfo *pni, List *varlist, double *factorlist, int len, double leftconst, double *rightconsts, int base)
{
    int i, t0, t1, t2, t3;
    VariableStatData vardata;
    AttStatsSlot sslots[4];
    double per_prob = 1.0;
    double shares = 0.0;
    double v0, v1, v2, v3;

    elog(WARNING, "<preprocess_filters> ok1");
    for (i = 0; i < len; i += 1)
    {
        elog(WARNING, "<preprocess_filters> ok1.1");
        examine_variable(pni, (Node *)list_nth(varlist, i), 0, &vardata);
        elog(WARNING, "<preprocess_filters> ok1.2");
        get_attstatsslot(&sslots[i], vardata.statsTuple, STATISTIC_KIND_HISTOGRAM, 0, ATTSTATSSLOT_VALUES);
        elog(WARNING, "<preprocess_filters> ok1.3");
        per_prob = per_prob / sslots[i].nvalues;
    }
    elog(WARNING, "<preprocess_filters> ok2");
    
    if (base == 0)
    {
        // 应该用最大值 / 平均值
        // 
        for (t0 = 0; t0 < sslots[0].nvalues; t0 += 1)
            {
                v0 = factorlist[0] * sslots[0].values[t0];
                for (t1 = 0; t1 < sslots[1].nvalues; t1 += 1)
                {
                    v1 = factorlist[1] * sslots[1].values[t1];
                    for (t2 = 0; t2 < sslots[2].nvalues; t2 += 1)
                    {
                        v2 = factorlist[2] * sslots[2].values[t2];
                        for (t3 = 0; t3 < sslots[3].nvalues; t3 += 1)
                        {
                            v3 = factorlist[3] * sslots[3].values[t3];
                            if (v0 + v1 + v2 + v3 + leftconst >= rightconsts[0])
                                shares += 1.0;
                        }
                    }
                }
            }
    }
    else if (base == 1)
    {
        for (t1 = 0; t1 < sslots[1].nvalues; t1 += 1)
                {
                    v1 = factorlist[1] * sslots[1].values[t1];
                    for (t2 = 0; t2 < sslots[2].nvalues; t2 += 1)
                    {
                        v2 = factorlist[2] * sslots[2].values[t2];
                        for (t3 = 0; t3 < sslots[3].nvalues; t3 += 1)
                        {
                            v3 = factorlist[3] * sslots[3].values[t3];
                            if (v1 + v2 + v3 + leftconst >= rightconsts[1])
                                shares += 1.0;
                        }
                    }
                }
    }
    else if (base == 2)
    {
        for (t2 = 0; t2 < sslots[2].nvalues; t2 += 1)
            {
                v2 = factorlist[2] * sslots[2].values[t2];
                for (t3 = 0; t3 < sslots[3].nvalues; t3 += 1)
                {
                    v3 = factorlist[3] * sslots[3].values[t3];
                    if (v2 + v3 + leftconst >= rightconsts[2])
                        shares += 1.0;
                }
            }
    }
    else if (base == 3)
    {
        for (t3 = 0; t3 < sslots[3].nvalues; t3 += 1)
            {
                v3 = factorlist[3] * sslots[3].values[t3];
                if (v3 + leftconst >= rightconsts[3])
                    shares += 1.0;
            }
    }

    return shares * per_prob;
}

// **************************  *******************


double query_var_average(PlannerInfo *root, Var *var)
{
    int sz;
    VariableStatData vardata;
	AttStatsSlot sslot;
    double answer;

    if (!IsA(var, Var))
    {
        elog(WARNING, "<query_var_average> TYPE_ERROR: arg->type = [%d], T_Var = [%d]", ((Node*)var)->type, T_Var);
        return 0.0;
    }
    else
    {
        elog(WARNING, "<query_var_average> querying for a Var..., varno = [%d]", var->varno);
    }
    

    examine_variable(root, (Node *)var, 0, &vardata);
    elog(WARNING, "<examine_variable> is ok.");
    get_attstatsslot(&sslot, vardata.statsTuple, STATISTIC_KIND_HISTOGRAM,
			0, ATTSTATSSLOT_VALUES);
    elog(WARNING, "<get_attstatsslot> is ok.");
    sz = sslot.nvalues;
    elog(WARNING, "[sslot.nvalues] = [%d]", sz);
    if (sz == 0)
    {
        elog(WARNING, "<query_var_average> size == 0, returnning 0.0");
        return 0.0;
    }
    
    // FIXME: only for JOB
    if (var->vartype == INT4OID)
        answer = datum_to_int(sslot.values[(sz + 1) / 2]);
    else
        answer = datum_to_double(sslot.values[(sz + 1) / 2]);
    elog(WARNING, "varno = [%d], average = [%lf]", var->varno, answer);
    return answer;
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


    elog(WARNING, "<copy_and_transpose> reserve_relid = [%d].", reserve_relid);
    collect_var_info(root, (Expr *)agri_expr, reserve_relid, &obj_var, &obj_ratio, &deleted_value);



    if ((obj_ratio < 0 ? -obj_ratio : obj_ratio) < 1e-15)
    {
        elog(ERROR, "<copy_and_transpose> [Fail] obj_ratio = [%.20f].", obj_ratio);
    }

    elog(WARNING, "<copy_and_transpose> [Okay] obj_ratio = [%.20f].", obj_ratio);
    new_value = (datum_to_double(const_value->constvalue) - deleted_value) / obj_ratio;


    elog(WARNING, "<copy_and_transpose> [Okay] deleted_value = [%.10f].", deleted_value);
    elog(WARNING, "<copy_and_transpose> [Okay] const_value = [%.10f].", datum_to_double(const_value->constvalue));


    copied_cur = (OpExpr *) copyObject(curop);
    if (obj_ratio < 0)
    {
        // new_value = -new_value;
        if (copied_cur->opno == 1755) // <= to >=
            copied_cur->opno = 1757; 

        else if (copied_cur->opno == 1757)  // >= to <=
            copied_cur->opno = 1755;    
    }
        

    copied_var = (Var *) copyObject(obj_var);
    new_const = create_const_from_double(new_value);
    
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
    Var *curvar;

    if (IsA(cur, Var))
    {
        curvar = (Var *) cur;
        elog(WARNING, "[Var] [curvar->varno] = [%d]", curvar->varno);
        if (curvar->varno == reserve_relid)
        {
            *obj_var = curvar;
            return true;
        }    
        else
            return false;
    }
    else if (IsA(cur, FuncExpr))
    {
        curvar = (Var *) linitial(((FuncExpr *)cur)->args);
        elog(WARNING, "[FuncExpr] [curvar->varno] = [%d]", curvar->varno);
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
            // elog(WARNING, "<> <> Entering 1758.");
            lresult = collect_var_info(root, lefttree,  reserve_relid, obj_var, obj_ratio, deleted_value);
            rresult = collect_var_info(root, righttree, reserve_relid, obj_var, obj_ratio, deleted_value);
            

            if (lresult || rresult)
            {
                *obj_ratio = 1.0;
            }

            if (!lresult)
            {
                // elog(WARNING, "[result 1.1]");
                if (IsA(lefttree, Var))
                {
                    *deleted_value += query_var_average(root, (Var *) lefttree);
                }
                    
                if (IsA(lefttree, Const))
                {
                    sonconst = (Const *) lefttree;
                    *deleted_value += datum_to_double(sonconst->constvalue);
                }

                if (IsA(lefttree, FuncExpr))
                {
                    curvar = (Var *) linitial(((FuncExpr *)cur)->args);
                    *deleted_value += query_var_average(root, curvar);
                }
            }

            if (!rresult)
            {
                // elog(WARNING, "[result 1.2]");
                if (IsA(righttree, Var))
                {
                    *deleted_value += query_var_average(root, (Var *) righttree);
                }
                    
                if (IsA(righttree, Const))
                {
                    sonconst = (Const *) righttree;
                    *deleted_value += datum_to_double(sonconst->constvalue);
                }

                if (IsA(righttree, FuncExpr))
                {
                    curvar = (Var *) linitial(((FuncExpr *)cur)->args);
                    *deleted_value += query_var_average(root, curvar);
                }
            }
            

            break;
        
        case 1760:   // '*' for NUMERIC;
            // elog(WARNING, "<> <> Entering 1760.");
            lresult = collect_var_info(root, lefttree,  reserve_relid, obj_var, obj_ratio, deleted_value);
            rresult = collect_var_info(root, righttree, reserve_relid, obj_var, obj_ratio, deleted_value);

            if (lresult)
            {
                // elog(WARNING, "[result 2.1]");
                sonconst = (Const *) righttree;
                *obj_ratio = datum_to_double(sonconst->constvalue);
            }
            else if (rresult)
            {
                // elog(WARNING, "[result 2.2]");
                sonconst = (Const *) lefttree;
                *obj_ratio = datum_to_double(sonconst->constvalue);
            }
            else if (IsA(lefttree, Var))
            {
                // elog(WARNING, "[result 2.3]");
                sonconst = (Const *) righttree;
                *deleted_value += query_var_average(root, (Var *)lefttree) * datum_to_double(sonconst->constvalue);
            }
            else if(IsA(lefttree, FuncExpr))
            {
                // elog(WARNING, "[result 2.4]");
                sonconst = (Const *) righttree;
                curvar = (Var *) linitial(((FuncExpr *)lefttree)->args);
                *deleted_value += query_var_average(root, curvar) * datum_to_double(sonconst->constvalue);
            }
            else if (IsA(righttree, Var))
            {
                // elog(WARNING, "[result 2.5]");
                sonconst = (Const *) lefttree;
                *deleted_value += query_var_average(root, (Var *)righttree) * datum_to_double(sonconst->constvalue);
            }
            else if(IsA(righttree, FuncExpr))
            {
                // elog(WARNING, "[result 2.6]");
                sonconst = (Const *) lefttree;
                curvar = (Var *) linitial(((FuncExpr *)righttree)->args);
                /*
                elog(WARNING, "type = [%d] ,T_Var = [%d]", ((Node*)curvar)->type, T_Var);
                double v1 = query_var_average(root, curvar);
                elog(WARNING, "[result 2.6] v1 = [%lf]", v1);
                double v2 = datum_to_double(sonconst->constvalue);
                elog(WARNING, "[result 2.6] v2 = [%lf]", v2);
                */
                *deleted_value += query_var_average(root, curvar) * datum_to_double(sonconst->constvalue);
            }
            else 
                elog(WARNING, "<collect_var_info> Well, I do not know what happened.");


            break;

        default:
            elog(WARNING, "I don't think this is a OpExpr, type = [%d]", ((Node *)opcur) -> type);
            elog(WARNING, "<collect_var_info> Detected quirky opno: [%d]", opcur->opno);
    }
    return false;
}


// *********************** 关于第二步的实现 *******************

/* 第二步的入口：将 root 为根的子树中的 Filter 移动到最好的位置 */
List *move_filter_local_optimal(Shadow_Plan *root, LFIndex *lfi, PlannerInfo *pni)
{
    Shadow_Plan *begin_node = root;
    Shadow_Plan *end_node;
    Shadow_Plan *local_opt_node;
    List *result_list = NIL;       // empty list
    bool has_segment;
    

    while (IsA(begin_node->plan, NestLoop))
    {
        has_segment = collect_segment(lfi, begin_node, &end_node);
        if (!has_segment)
            break;
        else
        {
            elog(WARNING, "Using [move_filter_toopt]!\n");
            local_opt_node = move_filter_toopt(pni, begin_node, end_node);
            result_list = lappend(result_list, local_opt_node);
            begin_node = end_node->lefttree;
        }
    }

    elog(WARNING, "\n res of move_filter_local_optimal: ");
    begin_node = root;
    while (IsA(begin_node->plan, NestLoop))
    {
        elog(WARNING, "is local optimal = [%d]", list_member_ptr(result_list, begin_node));
        begin_node = begin_node->lefttree;
    }

    return result_list;
}

/* collect_segment 尝试从某个点开始获取一段节点
    [return] : 是否可以确定一个段
    [input: begin_node] : 段的起始点
    [output: end_node] : 段的结束点
*/

bool collect_segment(LFIndex *lfi, Shadow_Plan *begin_node, Shadow_Plan **end_node)
{
    bool found_endnode = false;
    Shadow_Plan *cur_node = begin_node;
    int scanrel;

    while (!found_endnode)
    {
        if (IsA(cur_node->righttree->plan, SeqScan) || IsA(cur_node->righttree->plan, IndexScan))
        {
            scanrel = ((Scan *)cur_node->righttree->plan)->scanrelid;
            if (Is_feature_relid(lfi, scanrel))
            {
                found_endnode = true;
                *end_node = cur_node;
                break;
            }
        }

        if (IsA(cur_node->lefttree->plan, NestLoop))
            cur_node = cur_node->lefttree;
        else
        {
            found_endnode = false;
            break;
        }
    }
    return found_endnode;
}


double get_filter_selectivity(PlannerInfo *pnl, OpExpr *cur_op, int reserve_relid)
{
    OpExpr *transed_op = copy_and_transpose(pnl, cur_op, reserve_relid);
    int oproid = transed_op->opno;
    int collation = transed_op->opcollid;
    List *args = transed_op->args;
    Var *cur_var = (Var *) linitial(args);
    Const *cur_const = (Const *) lsecond(args);
    Datum constval = cur_const->constvalue;
    FmgrInfo opproc;
    double res;
    VariableStatData vardata;

    elog(WARNING, "<get_filter_selectivity> returning oproid [%d]", oproid);
    elog(WARNING, "<get_filter_selectivity> returning collation [%d]", collation);

    examine_variable(pnl, (Node *)cur_var, 0, &vardata);
    
    fmgr_info(get_opcode(oproid), &opproc);
    if (oproid == 1757)
        res = ineq_histogram_selectivity(pnl, &vardata, oproid, &opproc, true, true, 0, constval, NUMERICOID);
    else if (oproid == 1755)
        res = ineq_histogram_selectivity(pnl, &vardata, oproid, &opproc, false, true, 0, constval, NUMERICOID);
    else
        elog(ERROR, "<get_filter_selectivity> oproid not belongs to {1755, 1757}.");
    elog(WARNING, "<get_filter_selectivity> returning selectivity of [%lf]", res);
    return res;
}


/* get_filter_selectivity
   给定一个不等式, 现在尝试估计它的选择率
*/

/*
double get_filter_selectivity(PlannerInfo *pnl, LFIndex *lfi, OpExpr *cur_op)
{

    
}
*/
double get_join_cost(Shadow_Plan *cur_node)
{
    double per_join_cost = 0.01;
    int rows1 = ((Plan *) cur_node->lefttree->plan)->plan_rows;
    int rows2 = ((Plan*) cur_node->righttree->plan)->plan_rows;
    return per_join_cost * rows1 * rows2;
}

Shadow_Plan *move_filter_toopt(PlannerInfo *pni, Shadow_Plan *begin_node, Shadow_Plan *end_node)
{
    NestLoop *nsl = (NestLoop*) end_node->plan;

    double filter_per_cpu_cost = 0.01;
    int feature_relid = ((Scan *)end_node->righttree->plan)->scanrelid;
    double filter_rate = get_filter_selectivity(pni, llast(nsl->join.joinqual), feature_relid);

    Shadow_Plan * cur_node = begin_node;
    Shadow_Plan * opt_node = cur_node;
    double sum_save_join_cost = 0.0;
    double opt_node_delta_cost = 0.0;
    double cur_node_delta_cost = 0.0;

    while(cur_node != end_node->lefttree)
    {
        cur_node_delta_cost = (cur_node->plan->plan_rows) * filter_per_cpu_cost - sum_save_join_cost;
        if(cur_node_delta_cost < opt_node_delta_cost)
        {
            opt_node = cur_node;
            opt_node_delta_cost = cur_node_delta_cost;
        }
        sum_save_join_cost += (1.0 - filter_rate) * get_join_cost(cur_node); 
        cur_node = cur_node->lefttree;
    }
    return opt_node;

}

// *********************** EndOf 第二步 *******************

// *********************** 关于第三步的实现 *******************

List *transfer_node_to_list(Shadow_Plan* root)
{
    List *join_node_list = NIL;
    Shadow_Plan *cur = root;
    elog(WARNING, "<transfer_node_to_list> begin.");
    while (IsA(cur->plan, NestLoop))
    {
        join_node_list = lappend(join_node_list, cur);
        cur = cur->lefttree;
    }
    elog(WARNING, "<transfer_node_to_list> is ok.");
    return join_node_list;
}


/* merge_filter
    [input: root] 开始合并的根节点
    [input: opt_join_node_list] 在第二步中所确定的需要插入 Filter 的节点
*/

void merge_filter(Shadow_Plan *root, List *opt_join_node_list, LFIndex *lfi) // 注意这里的 root 不是 planner.c 里面的 root
{
    // Prepare: join_node_list 是 root 下方所有节点作为一个 List
    List *join_node_list = transfer_node_to_list(root);
    
    int node_size = join_node_list->length;
    int i;
    int *flag = palloc(node_size * sizeof(int));

    double *conditional_filter_rate = palloc(node_size * sizeof(double));
    double *absolute_filter_rate = palloc(node_size * sizeof(double));
    double *push_down_rows = palloc(node_size * sizeof(double));

    int n, k, lst_index;
    double filter_cost;
    double sum_join_cost;
    double cost_min;
    double cur_cost;
    double *total_cost = palloc(node_size * sizeof(double));
    int *move_from = palloc(node_size * sizeof(int));

    int last_ptr;
    int cur_ptr;

    double cost_per_filter = 0.01;  // FIXME         
    double cost_per_join = 0.01;    // FIXME

    elog(WARNING, "<merge_filter> join_node_list = [%p]", join_node_list);
    elog(WARNING, "<merge_filter> reached checkpoint(1).");
    memset(flag, 0, node_size * sizeof(int));
    // 整理第二步的结果
    for (i = 0; i < node_size; i += 1)
    {
        // 如果在 opt_join_node_list 中的话, 则说明该节点上有 Filter
        // 后续 merge 需要考虑这些节点
        if (list_member_ptr(opt_join_node_list, list_nth(join_node_list, i)))
            flag[i] = 1;    
        else
            flag[i] = -1;
    }

    // Prepare for absolute filter rate.

    for (int i = 0; i < node_size; i += 1)
    {
        if (flag[i] == 1) // FIXME 这里之后补充
            conditional_filter_rate[i] = 0.5;
        else
            conditional_filter_rate[i] = 1.0; // 没有 Filter
        
        absolute_filter_rate[i] = (i == 0) ? conditional_filter_rate[i]: 
            absolute_filter_rate[i-1] * conditional_filter_rate[i];
        
        push_down_rows[i] = ((Shadow_Plan *)list_nth(join_node_list, i))->plan->plan_rows 
                                * absolute_filter_rate[i];
    }
    elog(WARNING, "<merge_filter> reached checkpoint(2).");
    // Dynamic programming part.
 

    // FIXME 需要考虑那些不是 Filter 的 NestLoop
    memset(total_cost, 0, node_size * sizeof(double));
    for (n = 0; n < node_size; n += 1)
    {
        cost_min = 1e20; // 设置极大值
        lst_index = n;
        for (i = 0; i < n; i += 1)
        {
            filter_cost = cost_per_filter * push_down_rows[n] 
                * absolute_filter_rate[i] / absolute_filter_rate[n];
            sum_join_cost = 0.0;
            for (k = i + 1; k <= n; k += 1)
            {
                // join cost
                sum_join_cost += cost_per_join * push_down_rows[k] 
                    * absolute_filter_rate[i] / absolute_filter_rate[k];
            }
            cur_cost = total_cost[i] + sum_join_cost + filter_cost;
            elog(WARNING, "(n, i) = [%d %d], cur_cost = [%lf] = [%lf] + [%lf] + [%lf]", n, i, cur_cost, 
                total_cost[i], sum_join_cost, filter_cost);
            if (cur_cost < cost_min)
            {
                cost_min = cur_cost;
                lst_index = i;
            }
        }
        total_cost[n] = (n > 0) ? cost_min :
            cost_per_filter * push_down_rows[0] * absolute_filter_rate[0];
        move_from[n] = lst_index;
    }

    elog(WARNING, "<merge_filter> reached checkpoint(3).");
    elog(WARNING, "\n flag array = ");
    
    
    last_ptr = node_size - 1;
    cur_ptr = move_from[last_ptr];
    while (cur_ptr != 0)
    {
        for (i = cur_ptr + 1; i < last_ptr; i += 1)
            flag[i] = 0;
        last_ptr = cur_ptr;
        cur_ptr = move_from[last_ptr];
    }
    
    for (i = 0; i < node_size; i += 1)
    {
        elog(WARNING, "i = [%d], flag[i] = [%d], move_from[i] = [%d]", i, flag[i], move_from[i]);
    }
    
    // ************************** Move Filter 部分
    move_filter_impl(root, lfi, node_size, flag);
    elog(WARNING, "OUT of move_filter_impl");

    pfree(conditional_filter_rate);
    pfree(absolute_filter_rate);
    pfree(push_down_rows);
    pfree(total_cost);
    pfree(move_from);
    pfree(flag);
}


void move_filter_impl(Shadow_Plan *root, LFIndex *lfi, int node_size, int flag[])
{
    int count = 0;
    Shadow_Plan *cur_node = root;
    Shadow_Plan *end_node;
    Shadow_Plan *filter_pos = NULL;
    NestLoop *nsl;
    NestLoop *nsl_to;

    while (count < node_size && flag[count] != -1)
    {
        elog(WARNING, "count = [%d]", count);
        if (!collect_segment(lfi, cur_node, &end_node))
            break;
        if (flag[count] == 1)
            filter_pos = cur_node;
        // beginnode * *(f) * * * endnode * | beginnode * * * endnode *(f)
        // (f1 + f2) + f3 < c1                        (f1 + f2) < c2
        if (cur_node == end_node)
        {
            // 移动Filter
            if (filter_pos == NULL)
            {
                nsl = (NestLoop *) end_node->plan;
                nsl->join.joinqual = list_delete_last(nsl->join.joinqual);
            }
            else if (filter_pos != end_node)
            {
                nsl = (NestLoop *) end_node->plan;
                nsl_to = (NestLoop *) filter_pos->plan;

                nsl_to->join.joinqual = lappend(nsl_to->join.joinqual, llast(nsl->join.joinqual));
                nsl->join.joinqual = list_delete_last(nsl->join.joinqual);
            }

            // 移动完毕之后, 需要清空 filter_pos
            filter_pos = NULL;
        }

        count += 1;
        cur_node = cur_node->lefttree;
    }
}


// *********************** EndOf 第三步 *******************

// 关于转换值和创建节点的函数

double datum_to_double(Datum datum) {
	double val = convert_numeric_to_scalar(datum, NUMERICOID, NULL);
	return val;
}

double datum_to_int(Datum datum) {
	double val = DatumGetInt32(datum);
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