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
    // selectivity_list[] 的定义如下: 
    
    // selectivity_list[0] 表示共同考虑第 0, 1, 2, 3 个 feature 的选择率 (此时是一个完整的 filter)
    selectivity_list[0] = calc_selec(pni, lfi, varlist, ridlist, factorlist, len, theconst, rightconst, 0);

    // selectivity_list[1] 表示共同考虑第 1, 2, 3 个 feature 的选择率 (处理掉了第一个 feature)
    selectivity_list[1] = calc_selec(pni, lfi, varlist, ridlist, factorlist, len, theconst, rightconst, 1);

    // selectivity_list[2] 表示共同考虑第 2, 3 个 feature 的选择率 (处理掉了 2 个 feature)
    selectivity_list[2] = calc_selec(pni, lfi, varlist, ridlist, factorlist, len, theconst, rightconst, 2);

    // selectivity_list[0] 表示只考虑第 3 个 feature 的选择率 (处理掉了 3 个 feature, 只剩下一个 feature)
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



/* get_join_cost 
   根据节点 cur_node 及其左右子节点上面的信息, 估算出 join 的代价
   [return] : 当前认为的 join 的代价
   [in: Shadow_plan* cur_node] 所考虑的节点
*/


double get_join_cost(Shadow_Plan *cur_node)
{
    double cpu_join_cost_per_tuple = DEFAULT_CPU_TUPLE_COST + DEFAULT_CPU_OPERATOR_COST;
    int rows1 = ((Plan *) cur_node->lefttree->plan)->plan_rows;
    int rows2 = ((Plan*) cur_node->righttree->plan)->plan_rows;
    return cpu_join_cost_per_tuple * rows1 * rows2;
}


/* get_segment_table
   [Shadow_Plan *root: in] : 根部的计划树节点
   [LFIndex *lfi] : 全局的 LFIndex 信息
*/
List *get_segment_table(Shadow_Plan *root, LFIndex *lfi)
{
    List *segment_table = NIL;
    List *current_segment_nodes = NIL;

    int scanrel;
    int segment_count = 0;
    Shadow_Plan *cur_node = root;

    while (true)
    {
        current_segment_nodes = lappend(current_segment_nodes, cur_node);
        
        if (IsA(cur_node->righttree->plan, SeqScan) || IsA(cur_node->righttree->plan, IndexScan))
        {
            scanrel = ((Scan *)cur_node->righttree->plan)->scanrelid;
            if (Is_feature_relid(lfi, scanrel))
            {
                segment_table = lappend(segment_table, current_segment_nodes);

                // elog(WARNING, "segment = [%d], this segment contains [%d] nodes.", segment_count, current_segment_nodes->length);
                current_segment_nodes = NIL;
                segment_count += 1;
            }
        }
        else if (IsA(cur_node->lefttree->plan, SeqScan) || IsA(cur_node->lefttree->plan, IndexScan))
        {
            scanrel = ((Scan *)cur_node->lefttree->plan)->scanrelid;
            if (Is_feature_relid(lfi, scanrel))
            {
                segment_table = lappend(segment_table, current_segment_nodes);

                // elog(WARNING, "segment = [%d], this segment contains [%d] nodes.", segment_count, current_segment_nodes->length);
                current_segment_nodes = NIL;
                segment_count += 1;
            }
        }

        if (segment_count == lfi->feature_num)
            break;
        
        if (IsA(cur_node->righttree->plan, NestLoop))
            cur_node = cur_node->righttree;
        else if (IsA(cur_node->lefttree->plan, NestLoop))
            cur_node = cur_node->lefttree;

    }
    return segment_table;

}


/* 使用一步决定 filter 的位置 */
int *determine_filter(Shadow_Plan *root, LFIndex *lfi, double *selectivity_list)
{
    /*
        segment_table (List *) 会保存若干个 (List *)
        srgment_table 第i项 (是List *) 会保存若干个 (Shadow_plan *)
    */

    List *segment_table = get_segment_table(root, lfi);
    List *seg_inner_nodes;

    int i, j, k;
    int segment_num = segment_table->length;
    int seg_inner_num;
    int total_node_count = 0;

    // segment_inner_base_cost 是没有我们添加的 filter 的情况下, 计算出的 [join cost + filter cost]
    // 比如现在计算 join cost = lefttreee.rows * righttree.rows * join_per_cpu_cost
    // 可先把 [lefttreee.rows * righttree.rows * join_per_cpu_cost] 计算出来
    // absolute_filter_rate

    // 每一段内部的基础值
    double *segment_inner_base_cost = palloc(segment_num * sizeof(double));
    // 从计划树底部到某一段的基础值的前缀和
    double *segments_base_cost_sum = palloc(segment_num * sizeof(double));
    // 动态规划的结果：在第 i 段必须设置 filter 的时候, 从计划树底部到这个段的最小代价和
    double *total_min_cost = palloc(segment_num * sizeof(double));
    // transfer_from[i] : 从底部到第 i 段在取得最小总代价的时候, 它是从哪一段转移的
    // transfer_from[i] = k, 那么说明如果 第 i 段必须要有一个 filter 的话，它的最近的一个 filter 在第 k 段
    int *transfer_from = palloc(segment_num * sizeof(int));
    // best_choice_node[i] : 第 i 段中最好的那个 filter 位置是 **段内部的第几个节点**
    int *best_choice_node = palloc(segment_num * sizeof(int));

    // 输出结果相关变量
    int current_segment_id = 0;
    int accumulate_node_count = 0;
    int *flag;

    // *********************** Step1: 计算段内部的代价 ***********************
    // index 越大, 代表段越深
    for (i = segment_num - 1; i >= 0; i -= 1)
    {

        Shadow_Plan *cur_node;

        seg_inner_nodes = (List *) list_nth(segment_table, i);
        seg_inner_num = seg_inner_nodes->length;
        total_node_count += seg_inner_num;

        elog(WARNING, "seg_inner_num[%d] = [%d]", i, seg_inner_num);

        for (j = seg_inner_num - 1; j >= 0; j -= 1)
        {
            cur_node = (Shadow_Plan *) list_nth(seg_inner_nodes, j);
            // 段内部 join 的代价
            segment_inner_base_cost[i] += get_join_cost(cur_node);
        }

        if (i == segment_num - 1)
            segments_base_cost_sum[i] = segment_inner_base_cost[i];
        else
            segments_base_cost_sum[i] = segments_base_cost_sum[i + 1] + segment_inner_base_cost[i];

    }
    // *********************** 计算段内部的代价 ***********************
    // here is ok?
    elog(WARNING, "checkpoint 1 is ok.");
    for (i = segment_num - 1; i >= 0; i -= 1)
    {
        const double per_feature_compute_cost = (2 * DEFAULT_CPU_OPERATOR_COST);

        double sum_save_join_cost = 0.0;
        double cur_node_delta_cost = 0.0;
        double opt_node_delta_cost = 1e20;
        Shadow_Plan *cur_node;
        int no_transfer_best_choice;

        seg_inner_nodes = (List *) list_nth(segment_table, i);
        seg_inner_num = seg_inner_nodes->length;

        /********************* 更深处没有任何 filter 的情况 *********************/

        for (j = 0; j < seg_inner_num; j += 1)
        {
            double filter_per_cpu_cost = per_feature_compute_cost * (segment_num - i);

            cur_node = (Shadow_Plan *) list_nth(seg_inner_nodes, j);
            cur_node_delta_cost = (cur_node->plan->plan_rows) * filter_per_cpu_cost - sum_save_join_cost;
            if(cur_node_delta_cost < opt_node_delta_cost)
            {
                opt_node_delta_cost = cur_node_delta_cost;
                no_transfer_best_choice = j;
            }
            sum_save_join_cost += (1.0 - selectivity_list[i + 1]) * get_join_cost(cur_node); 
        }

        // total_min_cost[i]: 从“最深的段”开始到第i段（包括第i段）的代价
        total_min_cost[i] = segments_base_cost_sum[i] + opt_node_delta_cost;
        elog(WARNING,"i = [%d], BASIC tranfrom_k_total_cost = [%.10f]", i, total_min_cost[i]);
        
        transfer_from[i] = -1;
        best_choice_node[i] = no_transfer_best_choice;

        if (i == segment_num - 1)
            continue;
        /********************* 计算上一次使用 filter 是从哪个段完成转移 *********************/
        for (k = i + 1; k < segment_num; k += 1)
        {

            int tranfrom_k_best_choice = 0;

            double trans_from_k_conditional_rate = selectivity_list[i + 1] / selectivity_list[k + 1];
            
            double tranfrom_k_total_cost = 
                    total_min_cost[k] + 
                    selectivity_list[k + 1] * (segments_base_cost_sum[i + 1] - segments_base_cost_sum[k]);

            double filter_per_cpu_cost = per_feature_compute_cost * (k - i);

            sum_save_join_cost = 0.0;
            cur_node_delta_cost = 0.0;
            opt_node_delta_cost = 1e20;

            /********************* 上一个 filter 来自于 k 段条件下,该段内部最好的位置 *********************/
            // j 是该段内部正在枚举的 “放置 filter” 的节点的 index
            for (j = 0; j < seg_inner_num; j += 1)
            {
                cur_node = (Shadow_Plan *) list_nth(seg_inner_nodes, j);
                cur_node_delta_cost = (cur_node->plan->plan_rows * selectivity_list[k + 1]) 
                                      * filter_per_cpu_cost - sum_save_join_cost;
                if(cur_node_delta_cost < opt_node_delta_cost)
                {
                    tranfrom_k_best_choice = j;
                    opt_node_delta_cost = cur_node_delta_cost;
                }
                // TODO TODO TODO TODO
                sum_save_join_cost += (1.0 - trans_from_k_conditional_rate) * get_join_cost(cur_node); 
            }
            tranfrom_k_total_cost += segments_base_cost_sum[i] + opt_node_delta_cost;

            elog(WARNING,"i, k, best_choice(j) = [%d, %d, %d], tranfrom_k_total_cost = [%.10f]", 
                i, k, tranfrom_k_best_choice, tranfrom_k_total_cost);
            if (tranfrom_k_total_cost < total_min_cost[i])
            {
                total_min_cost[i] = tranfrom_k_total_cost;
                transfer_from[i] = k;
                best_choice_node[i] = tranfrom_k_best_choice;
            }
        }
        
    }
    elog(WARNING, "checkpoint 2 is ok. [total_node_count] = [%d] ", total_node_count);
    
    /********************* 求出结果 flag *********************/
    
    flag = palloc(total_node_count * sizeof(int));
    memset(flag, 0, total_node_count * sizeof(int));
    
    elog(WARNING, "checkpoint 2.5 is ok.");
    while (true)
    {
        elog(WARNING, "accumulate_node_count = [%d]", accumulate_node_count);
        elog(WARNING, "current_segment_id = [%d]", current_segment_id);
        elog(WARNING, "transfer_from[current_segment_id] = [%d]", transfer_from[current_segment_id]);
        elog(WARNING, "best_choice_node[current_segment_id] = [%d]", best_choice_node[current_segment_id]);

        flag[accumulate_node_count + best_choice_node[current_segment_id]] = 1;
        if (transfer_from[current_segment_id] == -1)
            break;
        else
        {
            for (j = current_segment_id; j < transfer_from[current_segment_id]; j += 1)
                accumulate_node_count += ((List *) list_nth(segment_table, j))->length;
            current_segment_id = transfer_from[current_segment_id];
        }
    }

    elog(WARNING, "checkpoint 3 is ok.");
    

    pfree(segment_inner_base_cost);
    pfree(segments_base_cost_sum);
    pfree(total_min_cost);
    pfree(transfer_from);
    pfree(best_choice_node);
        
    elog (WARNING, "flag array  = ");
    for (i = 0; i < total_node_count; i += 1)
        elog(WARNING, "flag[%d] = [%d]", i, flag[i]);

    return flag;
}


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