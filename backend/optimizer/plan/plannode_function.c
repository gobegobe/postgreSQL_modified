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

#include "optimizer/plannode_function.h"
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
#include "optimizer/lfindex.h"

#include "utils/float.h"

/* Init_LFIndex 初始化 LFIndex, 其中是所有写死的内容
 */

void Init_LFIndex(LFIndex* lfi, Query* parse)
{
    RangeTblEntry *rte;
    ListCell *lc;
    int i = 0;
    lfi->feature_num = 4;

    for (i = 1; i <= lfi->feature_num; i += 1)
        lfi->feature_rel_ids[i] = NULL;

    /*  当前各表对应的 Oid, 
        暂时需要根据机器手动修改, 并且嵌入到代码中
		16493, // title::production_year
		30055, // votes
		30061, // budget
		30069  // gross
	*/

    
    i = 0;
	foreach(lc, parse->rtable)
	{
		rte = (RangeTblEntry *) lfirst(lc);
		i += 1;
		switch(rte->relid)
		{
			case 16512: // title::production_year

                /*
                    BUG FIX: 下面这一行的作用是一个简单的布丁(虽然使用了很多时间排查)
                    JOB 32B中，会出现两个 title，这带来了很大的问题，总之我们只选择 t1
                */
                if (lfi->feature_rel_ids[1] == NULL)
				    lfi->feature_rel_ids[1] = lappend_int(lfi->feature_rel_ids[1], i);
				break;
			case 30114: // votes
				lfi->feature_rel_ids[2] = lappend_int(lfi->feature_rel_ids[2], i);
				break;
			case 30120: // budget
				lfi->feature_rel_ids[3] = lappend_int(lfi->feature_rel_ids[3], i);
				break;
			case 30126: // gross
				lfi->feature_rel_ids[4] = lappend_int(lfi->feature_rel_ids[4], i);
				break;
			default:
				break;
		}
	}

    for (i = 1; i <= lfi->feature_num; i++)
    {
        elog(WARNING, "feature_rel_ids length = %d", lfi->feature_rel_ids[i]->length);
    }

    // model weight
    lfi->W[0] = 24.685979;      // const value 1
    lfi->W[1] = -0.0092697;     // title::production_year
    lfi->W[2] = 6.9222664e-06;  // votes
    lfi->W[3] = -5.029019e-09;  // budget
    lfi->W[4] = -3.092156e-10;  // gross

    // column number
    lfi->feature_col_ids[0] = -1;   // 常数
    lfi->feature_col_ids[1] = 5;    // production_year 是 title 的第 5 列
    lfi->feature_col_ids[2] = 3;    // votes 是 mi_votes 的第 3 列
    lfi->feature_col_ids[3] = 3;    // budget 是 mi_votes 的第 3 列
    lfi->feature_col_ids[4] = 3;    // gross 是 mi_votes 的第 3 列

    // feature range of MIN values
    lfi->min_values[0] = 0.0;
    lfi->min_values[1] = 1880.0;
    lfi->min_values[2] = 5.0;
    lfi->min_values[3] = 0.0;
    lfi->min_values[4] = 30.0;

    // feature range of MAX values
    lfi->max_values[0] = 0.0;
    lfi->max_values[1] = 2019.0;
    lfi->max_values[2] = 967526;
    lfi->max_values[3] = 300000000.0;
    lfi->max_values[4] = 4599322004.0;

    // label-relative info
    lfi->has_upper_thd = false;
    lfi->has_lower_thd = false;
    lfi->label_upper_value = get_float8_infinity();
    lfi->label_upper_value = -get_float8_infinity();

    lfi->split_node_deepest = 1;
}

/*  set_feature_contidion
    [in] lfi: 需要处理的 LFIndex
    我们显式地指出, 这里将要使用 feature condition
 */
void set_feature_contidion(LFIndex *lfi)
{
    int i;

    for (i = 1; i <= lfi->feature_num; i += 1)
    {
        lfi->min_values[i] = lfi->min_conditions[i];
        lfi->max_values[i] = lfi->max_conditions[i];
    }
}

bool Is_feature_relid(LFIndex *lfi, int relid)
{
    int i;
    for (i = 1; i <= lfi->feature_num; i += 1)
        if (list_member_int(lfi->feature_rel_ids[i], relid))
            return true;
    return false;
}


// *************** 关于影子树的实现

/* build_shadow_plan: Build a ShadowPlan Tree from a Plan Tree.
 * [in] curplan: 所要构建的影子树的根节点指针
 * [return] 构建所得的影子树的根节点指针
 */

Shadow_Plan *build_shadow_plan(Plan *curplan) 
{
	// 变量定义
	Shadow_Plan *res;
	// 变量定义结束
	if (curplan == NULL) return (Shadow_Plan*) NULL;

	res = makeNode(Shadow_Plan);
	res->spliters = NULL;
	res->plan = curplan;
	if (curplan->lefttree) 
		res->lefttree = build_shadow_plan(curplan->lefttree);
	if (curplan->righttree)
		res->righttree = build_shadow_plan(curplan->righttree);
	return res;
}


/* find_sole_op: 一个工具函数, 找到整棵 Plan 树中的那个 Filter
 * 在 JOB 中, 选择找到那个 "小于不等式" 或 "大于不等式" 所对应的 Filter
 * [in] cur: 当前递归栈中所考虑的节点
 * [out] fi: 所找到的 filter 信息, 用于输出
 */
void find_sole_op(Shadow_Plan *cur, FilterInfo *fi) 
{

    ListCell *lc;
    NestLoop *nsl;
    OpExpr *op;

    // 现在只考虑 NestLoop
    // 如果当前节点是 Join 的话, 则需要考虑它上面的 Filter
    if (IsA(cur->plan, NestLoop))
    {
        nsl = (NestLoop*)cur->plan;
        foreach(lc, nsl->join.joinqual)
        {
            if (IsA(lfirst(lc), OpExpr))
            {
                op = (OpExpr *) lfirst(lc);
                if (op->opno == 1755 || op->opno == 1757)
                {
                    fi->shadow_roots = lappend(fi->shadow_roots, cur);
                    fi->filter_ops = lappend(fi->filter_ops, op);
                }
                    
            }
        }
    }
    
    if (cur->lefttree)
        find_sole_op(cur->lefttree, fi);
    if (cur->righttree)
        find_sole_op(cur->righttree, fi);
}

/* find_split_node: 在计划树上寻找 Split Node
 * [in] cur_plan: 当前递归栈中国所考虑的影子树节点
 * [in] minrows_node: 当前递归栈中, 从根节点到 cur_plan 上, rows 最小的那个节点
 * [in] min_rows: 当前递归栈中 minrows_node 对应的节点所对应的 rows
 * [in] feature_rel_ids: 被 Split Node 所考虑的那些 relid, 对于一个 Scan 节点而言, 
        只有当它所扫描的那个表在 feature_rel_ids 中的时候, 才会被某个中间的 SplitNode 所考虑
 */

void find_split_node
(Shadow_Plan *cur_plan, Shadow_Plan *minrows_node, double min_rows, LFIndex *lfi, int depth1, int depth2) 
{

    // 当前进行了很大程度上的简化：假定计划树上的节点只有
    // 1. NestLoop Join 节点
    // 2. 一些 Scan 节点，包括 IndexScan 和 SeqScan
    int relid;
    int i;
    bool is_member;
    Shadow_Plan *next_node;
    double next_minrows;

    // 假定: 即使有Agg, 也只会出现一次, 且在根节点上面
    if (nodeTag(cur_plan->plan) == T_Agg)
    {
        next_node = cur_plan->lefttree;
        find_split_node(next_node, next_node, next_node->plan->plan_rows, lfi, depth1 + 1, depth2 + 1);
        return;
    }
	else if (nodeTag(cur_plan->plan) == T_NestLoop) 
    {
		next_node = minrows_node;
		next_minrows = min_rows;
		if (cur_plan->plan->plan_rows <= min_rows) {
			next_minrows = cur_plan->plan->plan_rows;
			next_node = cur_plan;
		}
		if (cur_plan->lefttree != NULL)
			find_split_node(cur_plan->lefttree, next_node, next_minrows, lfi, depth2, depth2 + 1);
		if (cur_plan->righttree != NULL)
			find_split_node(cur_plan->righttree,  next_node, next_minrows, lfi, depth2, depth2 + 1);
		return;
	}

	// Not a "Join Node"
    // Shadow_plan 的 spliters 这个域一开始是 NULL
    // 这样做的好处之一是可以判断一个节点是否为 SplitNode 

    relid = ((Scan*)cur_plan->plan)->scanrelid;
    is_member = false;

    for (i = 1; i <= lfi->feature_num; i++) {
        if (list_member_int(lfi->feature_rel_ids[i], relid))
            is_member = true;
    }

    if (!is_member) return;
    elog(WARNING, "Scan spotted, relid = %d, depth1 = %d, depth2 = %d\n", relid, depth1, depth2);
    minrows_node->spliters = lappend(minrows_node->spliters, (void *)cur_plan);
}

/* find_value：根据传入的条件寻找某一列的min值
 * Parameter:
 * [in] feature_rel_ids: 需要考虑的 feature 的 relid
 * [in] min_values: 与feature_rel_ids 一一对应，保存relid 对应的min value值
 * [in] relid: 目标的最小id
 * [out] return: relid对应的 min value 值
 */

double find_min_value(LFIndex *lfi, int relid) {
    int i;

    for (i = 1; i <= lfi->feature_num; i++)
    {
        if (list_member_int(lfi->feature_rel_ids[i], relid))
            return lfi->min_values[i];
    }
    return 10.00; // just for debug, should not reach here.
}

double find_max_value(LFIndex *lfi, int relid) {
    int i;

    for (i = 1; i <= lfi->feature_num; i++)
    {
        if (list_member_int(lfi->feature_rel_ids[i], relid))
            return lfi->max_values[i];
    }
    return 10.00; // just for debug, should not reach here.
}


/*  copy_and_delete_op 在一个表达式树中，删除 delete_relid 相关的表达式节点，并返回新的副本
 *  cur: 当前递归节点;
 *  prt: cur 的父亲节点 
 *  delete_relid:  想要去除的那个 relid
 *  feature_rel_ids: 本次查询相关的 feature 的 relid 的列表
 *  min_values: 本次查询相关的 feature 的最小值，与 feature_rel_ids 一一对应
 *  [out] deleted_value: 作为结果返回给父节点，是以cur为根的子树中，那些被排除的feature的最小值的总和
 */


Expr *copy_and_delete_op(Expr *cur, int delete_relid, LFIndex *lfi, double *deleted_value) 
{
    // 变量定义
    double del_value_fromnow;
    Expr *left;
    Expr *right;
    Expr *lresult;
    Expr *rresult;

    OpExpr *res;
    OpExpr *opcur;

    Var *vr;
    // 变量定义结束

    if (cur->type == T_Const) // 常量节点
    {
        return copyObject(cur);
    }
    else if (cur->type == T_Var) // feature 节点
    {
        // 屎山是这里吗？
        if ( ((Var*)cur)->varno == delete_relid) // 当前的 Var 需要被去除
        {
            if (list_member_int(lfi->feature_rel_ids[2], delete_relid))
                (*deleted_value) += find_max_value(lfi, delete_relid);
            else
                (*deleted_value) += find_min_value(lfi, delete_relid);

            return NULL;
        }
        else
            return copyObject(cur);
    }
    else if (cur->type == T_FuncExpr)
    {
        vr = (Var *) linitial(((FuncExpr *)cur)->args);
        if (vr->varno == delete_relid)
        {
            if (list_member_int(lfi->feature_rel_ids[2], delete_relid))
                (*deleted_value) += find_max_value(lfi, delete_relid);
            else
                (*deleted_value) += find_min_value(lfi, delete_relid);
            return NULL;
        }
        else   
            return copyObject(cur);
    }
    // else： 现在 cur 可以确定为 OpExpr
    
    // linitial 代表取某个 List* 的第一个值的 void* 形式 (lsecond 是第二个值的 void*)
    // 观察代码可以发现, 它是一个左值

    opcur = (OpExpr *) cur;
    left = (Expr*) linitial(opcur->args);
    right =  (Expr*) lsecond(opcur->args);

    // res 首先为当前节点 cur 的复制, 一个细节是这里把args复制了, 它是一个必要的操作
    res = copyObject(opcur);

    del_value_fromnow = 0;

    switch (opcur->opno) 
    {
        case 1755:    // '<=' for NUMERIC
        case 1757:    // '>=' for NUMERIC
            // 现在假设任何 < 号右侧都是一个常数，且 < 永远在 OpExpr 的根节点
            linitial(res->args) = copy_and_delete_op(linitial(res->args), delete_relid, lfi, &del_value_fromnow);
            lsecond(res->args) = copy_const_withdelta((Const*)lsecond(res->args), -del_value_fromnow);
            return (Expr *)res;
            break;
        
        case 1758:   // '+' for NUMERIC

            lresult = copy_and_delete_op(
                linitial(res->args), delete_relid, lfi, &del_value_fromnow);     
            rresult = copy_and_delete_op(
                lsecond(res->args), delete_relid, lfi, &del_value_fromnow);

            (*deleted_value) += del_value_fromnow;

            if (lresult == NULL && rresult == NULL) 
                return NULL;
            else if(lresult == NULL)
                return rresult;
            else if(rresult == NULL)
                return lresult;
            else 
            {
                linitial(res->args) = lresult;
                lsecond(res->args) = rresult;
                return (Expr *)res;
            }
            break;
            
        case 1760:   // '*' for NUMERIC
            // 对于 * 运算符, 暂时认为其左右节点中, 至少有一个是常数节点

            lresult = copy_and_delete_op(
                linitial(res->args), delete_relid, lfi, &del_value_fromnow);     
            rresult = copy_and_delete_op(
                lsecond(res->args), delete_relid, lfi, &del_value_fromnow);
            
            if (left->type == T_Const) 
            {
                (*deleted_value) += 
                    constvalue_to_double(((Const *)lresult)->constvalue) * del_value_fromnow;
            } 
            else if (right->type == T_Const) 
            {
                (*deleted_value) += 
                    constvalue_to_double(((Const *)rresult)->constvalue) * del_value_fromnow;
            }

            if (lresult == NULL || rresult == NULL)
                return NULL;
            else 
            {
                linitial(res->args) = lresult;
                lsecond(res->args) = rresult;
                return (Expr *)res;
            }
            break;

        default:
            elog(WARNING, "Error 114514: Met some trouble... opno = [%d]\n", opcur->opno);
            assert(false);
            break;
    }
}


/* distribute_joinqual 函数使用 Shadow_plan 进行重写
 * cur: 当前递归处理中的节点
 * op_passed_tome: 来自父亲节点传下来的 OpExpr
 * feature_rel_ids: 本次查询相关的 feature 的 relid 的列表
 * min_values: 本次查询相关的 feature 的最小值，与 feature_rel_ids 一一对应
 */

/*
void distribute_joinqual_shadow(Shadow_Plan *cur, Expr *op_passed_tome, LFIndex *lfi, OpExpr **subop, int depth) {

    // 变量定义(为了遵循源代码风格)
    Plan *lefttree;
    Plan *righttree;
    Scan *othertree;
    NestLoop *nsl;

    Expr *modified_op;
    OpExpr *middle_result;
    OpExpr *sub_result;

    double whatever;
    int delete_relid;
    
    // 变量定义结束

    elog(WARNING, "Function<distribute_joinqual_shadow>, depth = %d, cur->plan->type = %d\n", depth, cur->plan->type);

    whatever = 0;
    sub_result = NULL;
    lefttree = cur->plan->lefttree;
    righttree = cur->plan->righttree;

    // **如果当前节点为 Split Node，则将父亲节点传下来的 OpExpr 装备到 joinqual 上 **
    if (cur->spliters != NULL) 
    {
        elog(WARNING, "depth = %d, entering way [1].\n", depth);
        nsl = (NestLoop*) cur->plan;
        if (op_passed_tome != NULL && depth != 1) {
            nsl->join.joinqual = lappend(nsl->join.joinqual, op_passed_tome);
        }
        lfi->split_node_deepest = depth;


        if (lefttree->type == T_NestLoop)
        {
            elog(WARNING, "depth = %d, entering way [1.1].\n", depth);
            othertree = (Scan*) cur->plan->righttree;
            delete_relid = othertree->scanrelid;
            modified_op = copy_and_delete_op(llast(nsl->join.joinqual), delete_relid, lfi, &whatever);

            distribute_joinqual_shadow(cur->lefttree, modified_op, lfi, &sub_result, depth + 1);
            
            
            elog(WARNING, "depth = %d, entering constrct_targetlist_nonleaf[1].", depth);
            middle_result = construct_targetlist_nonleaf(cur, lfi, delete_relid, op_passed_tome, sub_result, depth);
            *subop = middle_result; 
            
        }
        
        else if (righttree->type == T_NestLoop)
        {
            elog(WARNING, "depth = %d, entering way [1.2].\n", depth);
            othertree = (Scan*) cur->plan->lefttree;
            delete_relid = othertree->scanrelid;
            modified_op = copy_and_delete_op(llast(nsl->join.joinqual), delete_relid, lfi, &whatever);
            

            distribute_joinqual_shadow(cur->righttree, modified_op, lfi, &sub_result, depth + 1);

            
            elog(WARNING, "depth = %d, entering constrct_targetlist_nonleaf[2].", depth);
            middle_result = construct_targetlist_nonleaf(cur, lfi, delete_relid, op_passed_tome, sub_result, depth);
            *subop = middle_result; 
            
        }

        else // 已经到达叶子
        { 
            elog(WARNING, "depth = %d, entering way [1.3].\n", depth);
            elog(WARNING, "depth = %d, entering constrct_targetlist_leaf[3].", depth);
            middle_result = constrct_targetlist_leaf(cur, lfi, op_passed_tome, depth);
            *subop = middle_result; 
            
        }

    }
    else 
    {
        elog(WARNING, "depth = %d, entering way [2].\n", depth);
        if (lefttree->type == T_NestLoop) 
        {
            elog(WARNING, "depth = %d, entering way [2.1].\n", depth);
            othertree = (Scan*) cur->plan->righttree;
            delete_relid = othertree->scanrelid;
            modified_op = copy_and_delete_op(op_passed_tome, delete_relid, lfi, &whatever);
            distribute_joinqual_shadow(cur->lefttree, modified_op, lfi, &sub_result, depth + 1);

            
            elog(WARNING, "depth = %d, entering constrct_targetlist_nonleaf[4].", depth);
            middle_result = construct_targetlist_nonleaf(cur, lfi, delete_relid, op_passed_tome, sub_result, depth);
            *subop = middle_result; 
            
        }
        else if (cur->plan->righttree->type == T_NestLoop)
        {
            elog(WARNING, "depth = %d, entering way [2.2].\n", depth);
            othertree = (Scan*) cur->plan->lefttree;
            delete_relid = othertree->scanrelid;
            modified_op = copy_and_delete_op(op_passed_tome, delete_relid, lfi, &whatever);
            distribute_joinqual_shadow(cur->righttree, modified_op, lfi, &sub_result, depth + 1);

            
            elog(WARNING, "depth = %d, entering constrct_targetlist_nonleaf[5].", depth);
            middle_result = construct_targetlist_nonleaf(cur, lfi, delete_relid, op_passed_tome, sub_result, depth);
            *subop = middle_result; 
            
        } 
        else if(cur->plan->type == T_NestLoop)  // 最后一个 NestLoop 节点
        {
            elog(WARNING, "depth = %d, entering way [2.3].\n", depth);
            elog(WARNING, "depth = %d, entering constrct_targetlist_leaf[6].", depth);
            middle_result = constrct_targetlist_leaf(cur, lfi, op_passed_tome, depth);
            *subop = middle_result; 
            
            // 作为值返回的 middle_result 可能就是 NULL, 但有对应的处理 
        }
        else
        {
            elog(WARNING, "depth = %d, entering way [2.4].\n", depth);
        }
        // else: cur 是一个 Scan 节点, do nothing
    }
}
*/

void distribute_joinqual_shadow(Shadow_Plan *cur, Expr *op_passed_tome, LFIndex *lfi, OpExpr **subop, int depth) {

    // 变量定义(为了遵循源代码风格)
    Plan *lefttree;
    Plan *righttree;
    Scan *othertree;
    NestLoop *nsl;

    Expr *modified_op;
    OpExpr *middle_result;
    OpExpr *sub_result;

    double whatever;
    int delete_relid;
    
    // 变量定义结束

    elog(WARNING, "Function<distribute_joinqual_shadow>, depth = %d, cur->plan->type = %d\n", depth, cur->plan->type);

    whatever = 0;
    sub_result = NULL;
    lefttree = cur->plan->lefttree;
    righttree = cur->plan->righttree;

    

    nsl = (NestLoop*) cur->plan;
    lfi->split_node_deepest = depth;

    if (lefttree->type == T_NestLoop)
    {
        elog(WARNING, "depth = %d, entering way [1].\n", depth);
        othertree = (Scan*) cur->plan->righttree;
        delete_relid = othertree->scanrelid;
        
        if (op_passed_tome != NULL && Is_feature_relid(lfi, delete_relid))
        {
            if (depth != 1)
            {
                elog(WARNING, "depth = %d, using op_passed_tome.\n", depth);
                nsl->join.joinqual = lappend(nsl->join.joinqual, op_passed_tome);
            }
            modified_op = copy_and_delete_op(llast(nsl->join.joinqual), delete_relid, lfi, &whatever);
        }
        else
            modified_op = op_passed_tome;
        
        distribute_joinqual_shadow(cur->lefttree, modified_op, lfi, &sub_result, depth + 1);
        
        elog(WARNING, "depth = %d, entering constrct_targetlist_nonleaf[1].", depth);
        middle_result = construct_targetlist_nonleaf(cur, lfi, delete_relid, op_passed_tome, sub_result, depth);
        *subop = middle_result; 
        
    }
    
    else if (righttree->type == T_NestLoop)
    {
        elog(WARNING, "depth = %d, entering way [2].\n", depth);
        othertree = (Scan*) cur->plan->lefttree;
        delete_relid = othertree->scanrelid;

        if (op_passed_tome != NULL && depth != 1 && Is_feature_relid(lfi, delete_relid))
        {
            if (depth != 1)
            {
                elog(WARNING, "depth = %d, using op_passed_tome.\n", depth);
                nsl->join.joinqual = lappend(nsl->join.joinqual, op_passed_tome);
            }
            modified_op = copy_and_delete_op(llast(nsl->join.joinqual), delete_relid, lfi, &whatever);
        }
        else
            modified_op = op_passed_tome;

        
        distribute_joinqual_shadow(cur->righttree, modified_op, lfi, &sub_result, depth + 1);

        elog(WARNING, "depth = %d, entering constrct_targetlist_nonleaf[2].", depth);
        middle_result = construct_targetlist_nonleaf(cur, lfi, delete_relid, op_passed_tome, sub_result, depth);
        *subop = middle_result; 
        
    }

    else // 已经到达叶子
    { 
        elog(WARNING, "depth = %d, entering way [3].\n", depth);
        elog(WARNING, "depth = %d, entering constrct_targetlist_leaf[3].", depth);
        middle_result = constrct_targetlist_leaf(cur, lfi, op_passed_tome, depth);
        *subop = middle_result; 
        
    }

}

OpExpr *construct_targetlist_nonleaf(Shadow_Plan *cur, LFIndex *lfi, int delete_relid, 
    Expr *op_passed_tome, OpExpr *res_from_bottom, int depth)
{

    int i;
    OpExpr *individual_scan;
    OpExpr *middle_result;
    List *filter_args;
    NestLoop *nsl;
    TargetEntry *tnt;

    
    // 需要处理对 delete_relid 的扫描了

    // 这里需要分别处理, 是因为只有在第一次的时候, 需要保留常数
    nsl = (NestLoop*) cur->plan;
    i = ((Plan *)nsl)->targetlist->length;
    if (!Is_feature_relid(lfi, delete_relid))
    {
        elog(WARNING, "In nonleaf, entering way0.");
        middle_result = res_from_bottom;
    }
    else if (!res_from_bottom)
    {
        elog(WARNING, "In nonleaf, entering way1.");
        middle_result = (OpExpr *) copy_and_reserve(op_passed_tome, delete_relid, true);
    }
    else
    {
        elog(WARNING, "In nonleaf, entering way2.");
        individual_scan = (OpExpr *) copy_and_reserve(op_passed_tome, delete_relid, false);
        middle_result = makeNode(OpExpr);
        middle_result->opno = 1758;         // "+" for NUMERIC
        middle_result->opfuncid = 1724;
        middle_result->opresulttype = NUMERICOID;   
        middle_result->opretset = false;
        middle_result->opcollid = 0;
        middle_result->inputcollid = 0;
        middle_result->location = -1;
        middle_result->args = list_make2(res_from_bottom, individual_scan);
        
        if (res_from_bottom == NULL)
        {
            elog(WARNING, "Shit, res_from_bottom == NULL.");
        }
        else if(individual_scan == NULL)
        {
        elog(WARNING, "Shit, individual_scan == NULL.");    
        }

        if (nsl->join.joinqual != NULL && isInferFilter(llast(nsl->join.joinqual)))
        {
            filter_args = ((OpExpr *)llast(nsl->join.joinqual))->args;
            linitial(filter_args) = middle_result;
        }
        
    }

    if (middle_result != NULL && depth <= lfi->split_node_deepest)
    {
        tnt = makeTargetEntry((Expr *) middle_result, i + 1, NULL, false);
        ((Plan *)nsl)->targetlist = lappend(((Plan *)nsl)->targetlist, tnt);
    }

    return middle_result;
}


OpExpr *constrct_targetlist_leaf(Shadow_Plan *cur, LFIndex *lfi, Expr *op_passed_tome, int depth)
{
    OpExpr *middle_result;
    NestLoop *nsl;
    TargetEntry *tnt;
    int i;
    int scanrelid1 = ((Scan *)cur->plan->lefttree)->scanrelid;
    int scanrelid2 = ((Scan *)cur->plan->righttree)->scanrelid;

    if (!Is_feature_relid(lfi, scanrelid1) && !Is_feature_relid(lfi, scanrelid2))
    {
        elog(WARNING, "In Leaf, returning NULL. relid = [%d, %d]", scanrelid1, scanrelid2);
        return NULL;
    }
    else
    {
        elog(WARNING, "In Leaf, constucting middle result.");
        // nsl == current NeStedLoop node
        nsl = (NestLoop*) cur->plan;
        i = ((Plan *)nsl)->targetlist->length;
        middle_result = linitial(( (OpExpr*)op_passed_tome)->args);


        if (depth <= lfi->split_node_deepest)
        {
            tnt = makeTargetEntry((Expr *) middle_result, i + 1, NULL, false);
            ((Plan *)nsl)->targetlist = lappend(((Plan *)nsl)->targetlist, tnt);
        }
        
        return middle_result;
    }
    
}



// ===========================

Expr *copy_and_reserve(Expr *cur, int reserve_relid, bool reserve_const) 
{
    // 变量定义
    Expr *lresult;
    Expr *rresult;

    OpExpr *res;
    OpExpr *opcur;

    Var *vr;
    // 变量定义结束

    if (cur->type == T_Const) 
    {
        // 常量节点本来需要进行删除, 但是考虑到乘法节点暂时不删除, 而是在加法节点中处理
        return cur;
    }
    else if (cur->type == T_Var) // feature 节点
    {
        if ( ((Var*)cur)->varno == reserve_relid) // 当前的 Var 需要被保留，直接返回
        {
            return cur;
        }
        else
            return NULL;
    }
    else if (cur->type == T_FuncExpr)
    {
        vr = (Var *) linitial(((FuncExpr *)cur)->args);
        if (vr->varno == reserve_relid)
        {
            return cur;
        }
        else   
            return NULL;
    }

    opcur = (OpExpr *) cur;
    res = copyObject(opcur);

    switch (opcur->opno) 
    {
        case 1755:    // '<=' for NUMERIC
        case 1757:    // '>=' for NUMERIC
            // 现在假设任何 <= 号右侧都是一个常数，且 <= 永远在 OpExpr 的根节点
            linitial(res->args) = copy_and_reserve(linitial(res->args), reserve_relid, reserve_const);

            return linitial(res->args); // 注意，这里返回的是根节点的左子树，即只保留 "lhs <= rhs" 中 lhs 这一部分
            break;
        
        case 1758:   // '+' for NUMERIC

            lresult = copy_and_reserve(
                linitial(res->args), reserve_relid, reserve_const);     
            rresult = copy_and_reserve(
                lsecond(res->args), reserve_relid, reserve_const);

            if (lresult == NULL && rresult == NULL) 
                return NULL;
            else if(lresult == NULL || 
                (!reserve_const && nodeTag(linitial(res->args)) == T_Const)) // 特殊判断: 抛弃加法的 Const 节点
                return rresult;
            else if(rresult == NULL || 
                (!reserve_const && nodeTag(lsecond(res->args)) == T_Const))  // 特殊判断: 抛弃加法的 Const 节点
                return lresult;
            else {
                linitial(res->args) = lresult;
                lsecond(res->args) = rresult;
                return (Expr *)res;
            }
            
            break;
            
        case 1760:   // '*' for NUMERIC
            // 对于 * 运算符, 暂时认为其左右节点中, 至少有一个是常数节点

            lresult = copy_and_reserve(
                linitial(res->args), reserve_relid, reserve_const);     
            rresult = copy_and_reserve(
                lsecond(res->args), reserve_relid, reserve_const);

            if (lresult == NULL || rresult == NULL)
                return NULL;
            else {
                linitial(res->args) = lresult;
                lsecond(res->args) = rresult;
                return (Expr *)res;
            }
            break;

        default:
            assert(false);
            break;
    }
}


// ************** 关于 <构造节点> 的函数

// TODO: 该函数需要支持 double
/* copy_const_withdelta: 对于一个 Const 节点, 复制并更改它上面的值, 返回一个新的 Const 节点
 * Paratemer:
 * [in] cur: 构造新节点的基础节点
 * [in] delta: 新节点的值 == (cur 节点上面的值 + delta)
 * [return] 指向新节点的指针 (Const *)
 */

Const *copy_const_withdelta(Const *cur, double delta) {
    double origin_value;
    origin_value = constvalue_to_double(cur->constvalue);
    return create_const_node(origin_value + delta);
}
