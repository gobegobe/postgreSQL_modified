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


double *preprocess_filters(PlannerInfo *pni, LFIndex *lfi, Expr *cur_op, List *ridlist, List *depthlist, List** filterlist)
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
        // res_expr 是完整的 Filter
        res_expr = copy_and_delete_op(input_expr, list_nth_int(ridlist, i), lfi, &whatever, 1, &tempvalue, &tempconst);
        
        // rightconst [array of DOUBLE] 保存右侧常数的值
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

    for (i = 0; i < len; i += 1)
    {
        elog(WARNING, "<pf> i = [%d], ridlist[i] = [%d], factor[i] = [%.15f], rightconst[i] = [%.15f]",
            i, list_nth_int(ridlist, i), factorlist[i], rightconst[i]);
    }
    
    // 现在开始计算选择率
    selectivity_list[0] = calc_selec(pni, lfi, varlist, ridlist, factorlist, len, theconst, rightconst, 0);
    selectivity_list[1] = calc_selec(pni, lfi, varlist, ridlist, factorlist, len, theconst, rightconst, 1);
    selectivity_list[2] = calc_selec(pni, lfi, varlist, ridlist, factorlist, len, theconst, rightconst, 2);
    selectivity_list[3] = calc_selec(pni, lfi, varlist, ridlist, factorlist, len, theconst, rightconst, 3);

    for (i = 0; i < len; i += 1)
    {
        elog(WARNING, "<preprocess_filters> selectivity_list[%d] = [%.20f]", i, selectivity_list[i]);
    }

    elog(WARNING, "<preprocess_filters> the const = [%lf]", theconst);
    elog(WARNING, "\n<preprocess_filters> is ok, (*filterlist)->length = [%d].", (*filterlist)->length);

    pfree(factorlist);
    pfree(rightconst);
    return selectivity_list;
}

double calc_selec(PlannerInfo *pni, LFIndex *lfi, List *varlist, List *ridlist, double *factorlist, 
    int len, double leftconst, double *rightconsts, int base)
{
    int i, j, t0, t1, t2, t3;
    VariableStatData vardata;
    AttStatsSlot sslots[4];
    double per_prob = 1.0;
    double shares = 0.0;
    double v0, v1, v2, v3;
    double **diag;

    elog(WARNING, "<preprocess_filters> ok1");
    for (i = 0; i < len; i += 1)
    {
        examine_variable(pni, (Node *)list_nth(varlist, i), 0, &vardata);
        get_attstatsslot(&sslots[i], vardata.statsTuple, STATISTIC_KIND_HISTOGRAM, 0, ATTSTATSSLOT_VALUES);

        if (i >= base)
            per_prob = per_prob / sslots[i].nvalues;

        elog(WARNING, "<>preprocess_filters> for i = [%d], sslots[i].nvalues = [%d]", i, sslots[i].nvalues);

    }
    elog(WARNING, "<preprocess_filters> ok, [per_prob] = [%.15f]", per_prob);
    
    // diagram 直方图中的数值（实际上是 histogram...）
    // diag[i][j] 是 第 i 个feature的第 j 根柱子的“最小值”
    diag = palloc(4 * sizeof(double *));

    for (i = 0; i < len; i += 1)
    {
        diag[i] = palloc(sslots[i].nvalues * sizeof(double));
        for (j = 0; j < sslots[i].nvalues; j += 1)
            diag[i][j] = constvalue_to_double(sslots[i].values[j]);
    }
        

    if (base == 0)
    {
        // 应该用最大值 / 平均值
       
        for (t0 = 0; t0 < sslots[0].nvalues; t0 += 1)
            {
                v0 = (t0 < sslots[0].nvalues - 1) ? 
                        factorlist[0] * (diag[0][t0] + diag[0][t0+1]) / 2.0:
                        factorlist[0] * (diag[0][t0] * find_max_value(lfi, list_nth_int(ridlist, 0))) / 2.0;

                for (t1 = 0; t1 < sslots[1].nvalues; t1 += 1)
                {
                    v1 = (t1 < sslots[1].nvalues - 1) ? 
                        factorlist[1] * (diag[1][t1] + diag[1][t1+1]) / 2.0:
                        factorlist[1] * (diag[1][t1] * find_max_value(lfi, list_nth_int(ridlist, 1))) / 2.0;

                    for (t2 = 0; t2 < sslots[2].nvalues; t2 += 1)
                    {
                        v2 = (t2 < sslots[2].nvalues - 1) ? 
                            factorlist[2] * (diag[2][t2] + diag[2][t2+1]) / 2.0:
                            factorlist[2] * (diag[2][t2] * find_max_value(lfi, list_nth_int(ridlist, 2))) / 2.0;


                        for (t3 = 0; t3 < sslots[3].nvalues; t3 += 1)
                        {
                            v3 = (t3 < sslots[3].nvalues - 1) ? 
                                factorlist[3] * (diag[3][t3] + diag[3][t3+1]) / 2.0:
                                factorlist[3] * (diag[3][t3] * find_max_value(lfi, list_nth_int(ridlist, 3))) / 2.0;

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
            v1 = (t1 < sslots[1].nvalues - 1) ? 
                        factorlist[1] * (diag[1][t1] + diag[1][t1+1]) / 2.0:
                        factorlist[1] * (diag[1][t1] * find_max_value(lfi, list_nth_int(ridlist, 1))) / 2.0;

            for (t2 = 0; t2 < sslots[2].nvalues; t2 += 1)
            {
                v2 = (t2 < sslots[2].nvalues - 1) ? 
                            factorlist[2] * (diag[2][t2] + diag[2][t2+1]) / 2.0:
                            factorlist[2] * (diag[2][t2] * find_max_value(lfi, list_nth_int(ridlist, 2))) / 2.0;

                for (t3 = 0; t3 < sslots[3].nvalues; t3 += 1)
                {
                    v3 = (t3 < sslots[3].nvalues - 1) ? 
                        factorlist[3] * (diag[3][t3] + diag[3][t3+1]) / 2.0:
                        factorlist[3] * (diag[3][t3] * find_max_value(lfi, list_nth_int(ridlist, 3))) / 2.0;

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
            v2 = (t2 < sslots[2].nvalues - 1) ? 
                            factorlist[2] * (diag[2][t2] + diag[2][t2+1]) / 2.0:
                            factorlist[2] * (diag[2][t2] * find_max_value(lfi, list_nth_int(ridlist, 2))) / 2.0;

            for (t3 = 0; t3 < sslots[3].nvalues; t3 += 1)
            {
                v3 = (t3 < sslots[3].nvalues - 1) ? 
                    factorlist[3] * (diag[3][t3] + diag[3][t3+1]) / 2.0:
                    factorlist[3] * (diag[3][t3] * find_max_value(lfi, list_nth_int(ridlist, 3))) / 2.0;

                if (v2 + v3 + leftconst >= rightconsts[2])
                    shares += 1.0;
            }
        }
    }
    else if (base == 3)
    {
        for (t3 = 0; t3 < sslots[3].nvalues; t3 += 1)
        {
            v3 = (t3 < sslots[3].nvalues - 1) ? 
                factorlist[3] * (diag[3][t3] + diag[3][t3+1]) / 2.0:
                factorlist[3] * (diag[3][t3] * find_max_value(lfi, list_nth_int(ridlist, 3))) / 2.0;
            if (v3 + leftconst >= rightconsts[3])
                shares += 1.0;
        }
    }

    elog(WARNING, "base = [%d], shares = [%.2f], leftconst = [%.10f]", base, shares, leftconst);

    for (i = 0; i < 4; i += 1)
        pfree(diag[i]);
    pfree(diag);

    if (shares == 0.0) 
    {
        shares = 1.0;
        elog(WARNING, "Oh nooooooooo: shares == 0!!!");
    }


    return shares * per_prob;
}

// **************************  *******************

/* query_var_average (deprecated) 求出某一列的平均值
    [in: PlannerInfo* root] : 计划的统计信息
    [in: Var *var] : 需要求平均值的这一列的 Var*
*/

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

/* copy_and_transpose (deprecated) : 这是在之前尝试通过统计平均值来估算选择率时, 使用的函数 */

/*
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
*/


/* collect_var_info 在一个表达式中收集一些信息(这个函数很可能是没有必要的, 如果代码写得更好的话...)
    [in: PlannerInfo root] 计划信息
    [in: Expr* cur] 当前递归阶段的节点
    [in: int reserve_relid] 需要进行信息收集的那个列的 relid
    [out: Var*] object_var: reserve_relid 对应的那个 Var* 
    [out: double] object_ratio: reserve_relid 对应的列的系数
    [out: double] deleted_value: (deprecated) 这个列所带来的被删除的值(之前使用平均数来统计)
*/

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
            
            if (lresult || rresult)
                *obj_ratio = 1.0;
            
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
            elog(WARNING, "I don't think this is a OpExpr, type = [%d]", ((Node *)opcur) -> type);
            elog(WARNING, "<collect_var_info> Detected quirky opno: [%d]", opcur->opno);
    }
    return false;
}


// *********************** 关于第二步的实现 *******************

/* 第二步的入口：将 root 为根的子树中的 Filter 移动到最好的位置 */
List *move_filter_local_optimal(Shadow_Plan *root, LFIndex *lfi, PlannerInfo *pni, double *selectivity_list)
{
    Shadow_Plan *begin_node = root;
    Shadow_Plan *end_node;
    Shadow_Plan *local_opt_node;
    List *result_list = NIL;       // empty list
    bool has_segment;
    int selectivity_index = 0;
    
    while (IsA(begin_node->plan, NestLoop))
    {
        has_segment = collect_segment(lfi, begin_node, &end_node);
        if (!has_segment)
            break;
        else
        {
            elog(WARNING, "Using [move_filter_toopt]!\n");
            local_opt_node = move_filter_toopt(pni, begin_node, end_node, selectivity_list[selectivity_index]);
            result_list = lappend(result_list, local_opt_node);

            elog(WARNING, "Outof [move_filter_toopt]!\n");
            if (IsA(end_node->lefttree->plan, NestLoop))
                begin_node = end_node->lefttree;
            else if (IsA(end_node->righttree->plan, NestLoop))
                begin_node = end_node->righttree;
            else
                break;
            
            selectivity_index += 1;
        }
    }

    return result_list;
}

/* collect_segment 尝试从某个点开始获取一段节点
    [return] -> bool: 是否可以确定一个段
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
                cur_node->is_endnode = true;
                found_endnode = true;
                *end_node = cur_node;
                break;
            }
        }
        else if (IsA(cur_node->lefttree->plan, SeqScan) || IsA(cur_node->lefttree->plan, IndexScan))
        {
            scanrel = ((Scan *)cur_node->lefttree->plan)->scanrelid;
            if (Is_feature_relid(lfi, scanrel))
            {
                cur_node->is_endnode = true;
                found_endnode = true;
                *end_node = cur_node;
                break;
            }
        }

        if (IsA(cur_node->lefttree->plan, NestLoop))
            cur_node = cur_node->lefttree;
        else if (IsA(cur_node->righttree->plan, NestLoop))
            cur_node = cur_node->righttree;
        else
        {
            found_endnode = false;
            break;
        }
    }
    return found_endnode;
}


/* get_join_cost 
   根据节点 cur_node 及其左右子节点上面的信息, 估算出 join 的代价
   [return] : 当前认为的 join 的代价
   [in: Shadow_plan* cur_node] 所考虑的节点
*/
double get_join_cost(Shadow_Plan *cur_node)
{
    double per_join_cost = 0.01;
    int rows1 = ((Plan *) cur_node->lefttree->plan)->plan_rows;
    int rows2 = ((Plan*) cur_node->righttree->plan)->plan_rows;
    return per_join_cost * rows1 * rows2;
}


Shadow_Plan *move_filter_toopt(PlannerInfo *pni, Shadow_Plan *begin_node, Shadow_Plan *end_node, double selectivity)
{
    double filter_per_cpu_cost = 0.01;
    double filter_rate;
    Shadow_Plan * cur_node = begin_node;
    Shadow_Plan * opt_node = cur_node;
    double sum_save_join_cost = 0.0;
    double opt_node_delta_cost = 0.0;
    double cur_node_delta_cost = 0.0;
    
    filter_rate = selectivity;

    while(cur_node != end_node->lefttree && cur_node != end_node->righttree)
    {
        cur_node_delta_cost = (cur_node->plan->plan_rows) * filter_per_cpu_cost - sum_save_join_cost;
        if(cur_node_delta_cost < opt_node_delta_cost)
        {
            opt_node = cur_node;
            opt_node_delta_cost = cur_node_delta_cost;
        }
        sum_save_join_cost += (1.0 - filter_rate) * get_join_cost(cur_node); 
        if (IsA(cur_node->lefttree->plan, NestLoop))
            cur_node = cur_node->lefttree;
        else if (IsA(cur_node->righttree->plan, NestLoop))
            cur_node = cur_node->righttree;
        else
            break;
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

        if (IsA(cur->lefttree->plan, NestLoop))
            cur = cur->lefttree;
        else if (IsA(cur->righttree->plan, NestLoop))
            cur = cur->righttree;
        else
            break;
    }
    elog(WARNING, "<transfer_node_to_list> is ok.");
    return join_node_list;
}


/*  merge_filter: 这个函数执行 Filter 的合并
    [input: Shadow_Plan* root] 开始合并的根节点
    [input: List* opt_join_node_list] 在第二步中所确定的需要插入 Filter 的节点
    [input: LFIndex* lfi] : 关于 feature 的信息
*/

int *merge_filter(Shadow_Plan *root, List *opt_join_node_list, 
    LFIndex *lfi, double *selectivity_list)
// 注意这里的 root 不是 planner.c 里面的 root
{
    // Prepare: join_node_list 是 root 下方所有节点作为一个 List
    List *join_node_list = transfer_node_to_list(root);
    int node_size = join_node_list->length;
    int part_node_size = node_size;

    int i, n, k, lst_index, last_ptr;
    int segcounter = 0;
    
    double filter_cost;
    double sum_join_cost;
    double cost_min;
    double cur_cost;

    int     *flag = palloc(node_size * sizeof(int));
    double  *total_cost = palloc(node_size * sizeof(double));
    int     *move_from = palloc(node_size * sizeof(int));
    double  *conditional_filter_rate = palloc(node_size * sizeof(double));
    double  *absolute_filter_rate = palloc(node_size * sizeof(double));
    double  *push_down_rows = palloc(node_size * sizeof(double));

    const double cost_per_filter = 0.01;  // FIXME         
    const double cost_per_join = 0.01;    // FIXME

    elog(WARNING, "<merge_filter> join_node_list = [%p]", join_node_list);
    elog(WARNING, "<merge_filter> reached checkpoint(1).");

    memset(move_from, 0, node_size * sizeof(int));

    // 整理第二步的结果
    for (i = 0; i < node_size; i += 1)
    {
        // 如果在 opt_join_node_list 中的话, 则说明该节点上有 Filter, 后续 merge 需要考虑这些节点
        if (list_member_ptr(opt_join_node_list, list_nth(join_node_list, i)))
            flag[i] = 1;    
        else
            flag[i] = 0;
    }

    // *********************** Prepare for absolute filter rate. ***********************

    for (i = 0; i < node_size; i += 1)
    {
        // absolute_filter_rate ==> 预处理的 selectivity
        // conditional_filter_rate[i] <== absolute_filter_rate[i], [i+1]
        absolute_filter_rate[i] = selectivity_list[segcounter];
        elog(WARNING, "i = [%d], segcounter = [%d]", i, segcounter);
        
        if (((Shadow_Plan *) list_nth(join_node_list, i))->is_endnode) 
            segcounter += 1;

        if (i == node_size - 1)
            conditional_filter_rate[i] = absolute_filter_rate[i];

        if (i > 0)
            conditional_filter_rate[i-1] = absolute_filter_rate[i-1] / absolute_filter_rate[i];

        push_down_rows[i] = absolute_filter_rate[i] * ((Shadow_Plan *)list_nth(join_node_list, i))->plan->plan_rows;

        if (segcounter == lfi->feature_num)
        {
            part_node_size = i + 1;
            break;
        }
    }

    for (i = 0; i < node_size; i += 1)
        elog(WARNING, "i = [%d/%d], condition = [%lf], absol = [%lf]", i, node_size-1,  conditional_filter_rate[i], absolute_filter_rate[i]);
    
    elog(WARNING, "<merge_filter> node_size = [%d], part_node_size = [%d]\n", node_size, part_node_size);
    
    // *********************** Dynamic programming part. ***********************
 
    memset(total_cost, 0, node_size * sizeof(double));
    for (n = 0; n < part_node_size; n += 1)
    {
        cost_min = 1e20; // 设置极大值
        lst_index = n;
        for (i = 0; i < n; i += 1)
        {
            filter_cost = cost_per_filter * push_down_rows[n] * absolute_filter_rate[i] / absolute_filter_rate[n];
            sum_join_cost = 0.0;
            for (k = i + 1; k <= n; k += 1)
            {   // join cost
                sum_join_cost += cost_per_join * push_down_rows[k]  * absolute_filter_rate[i] / absolute_filter_rate[k];
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
        total_cost[n] = (n > 0) ? cost_min : cost_per_filter * push_down_rows[0] * absolute_filter_rate[0];
        move_from[n] = lst_index;
    }

    elog(WARNING, "<merge_filter> reached checkpoint(3).");

    // elog(ERROR, "\n stopped. ");
    elog(WARNING, "\n flag array = ");
    
    last_ptr = part_node_size - 1;
    do
    {
        for (i = move_from[last_ptr] + 1; i < last_ptr; i += 1)
            flag[i] = 0;
        last_ptr = move_from[last_ptr];
    } while (last_ptr != 0);
    
    for (i = 0; i < part_node_size; i += 1)
    {
        elog(WARNING, "i = [%d], flag[i] = [%d], move_from[i] = [%d]", i, flag[i], move_from[i]);
    }
    
    // ************************** Move Filter 部分 ***********************
    // move_filter_impl(root, lfi, node_size, flag);
    
    elog(WARNING, "OUT of move_filter_impl");

    pfree(conditional_filter_rate);
    pfree(absolute_filter_rate);
    pfree(push_down_rows);
    pfree(total_cost);
    pfree(move_from);
    
    return flag;
}

/*
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

        if (IsA(cur_node->lefttree->plan, NestLoop))
            cur_node = cur_node->lefttree;
        else if (IsA(cur_node->righttree->plan, NestLoop))
            cur_node = cur_node->righttree;
    }
}
*/

// *********************** EndOf 第三步 *******************

// *********************** (Utils) 关于转换值和创建节点的函数 ***********************

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