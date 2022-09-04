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

void Init_inferinfo(InferInfo* ifi, Query* parse)
{
    RangeTblEntry *rte;
    ListCell *lc;
    int i = 0;

    /*  当前各表对应的 Oid
		16493, // title::production_year
		30055, // votes
		30061, // budget
		30069	// gross
	*/
    ifi->feature_num = 4;
    i = 0;
	foreach(lc, parse->rtable)
	{
		rte = (RangeTblEntry *) lfirst(lc);
		i += 1;
		switch(rte->relid)
		{
			case 16493:
				ifi->splitable_relids[0] = i;
				break;
			case 30055:
				ifi->splitable_relids[1] = i;
				break;
			case 30061:
				ifi->splitable_relids[2] = i;
				break;
			case 30069:
				ifi->splitable_relids[3] = i;
				break;
			default:
				break;
		}
	}

    for (i = 0; i < 4; i++)
    {
        ifi->min_values[i] = 1.0;
        ifi->max_values[i] = 1.0;
    }
}

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
 * [in] splitable_relids: 被 Split Node 所考虑的那些 relid, 对于一个 Scan 节点而言, 
        只有当它所扫描的那个表在 splitable_relids 中的时候, 才会被某个中间的 SplitNode 所考虑
 */

void find_split_node
(Shadow_Plan *cur_plan, Shadow_Plan *minrows_node, double min_rows, InferInfo *ifi) 
{

    // 当前进行了很大程度上的简化：假定计划树上的节点只有
    // 1. NestLoop Join 节点
    // 2. 一些 Scan 节点，包括 IndexScan 和 SeqScan
    int relid;
    int i;
    bool is_member;

	if (nodeTag(cur_plan->plan) == T_NestLoop) {
		Shadow_Plan *next_node = minrows_node;
		double next_minrows = min_rows;
		if (cur_plan->plan->plan_rows <= min_rows) {
			next_minrows = cur_plan->plan->plan_rows;
			next_node = cur_plan;
		}
		if (cur_plan->lefttree != NULL)
			find_split_node(cur_plan->lefttree, next_node, next_minrows, ifi);
		if (cur_plan->righttree != NULL)
			find_split_node(cur_plan->righttree,  next_node, next_minrows, ifi);
		return;
	}

	// Not a "Join Node"
    // Shadow_plan 的 spliters 这个域一开始是 NULL
    // 这样做的好处之一是可以判断一个节点是否为 SplitNode 

    relid = ((Scan*)cur_plan->plan)->scanrelid;
    is_member = false;

    for (i = 0; i < ifi->feature_num; i++) {
        if (relid == ifi->splitable_relids[i])
            is_member = true;
    }

    if (!is_member) return;

    minrows_node->spliters = lappend(minrows_node->spliters, (void *)cur_plan);
}

// ==============================================
/*  copy_op
 *  该函数的作用是复制一个 Expr 节点并返回副本的指针
 *  该函数所支持的节点需要独立更新，现在只支持 Var、Const、OpExpr
 */

Expr *copy_op(Expr *cur) {

    // 变量定义
    Var *res1;
    Const *res2;
    OpExpr *res;
    ListCell lc1, lc2;
    List *lst;
    // 变量定义结束

    if (cur->type == T_Var) {
        
        res1 = makeNode(Var);
        memcpy(res1, cur, sizeof(Var));
        return (Expr*)res1;
    }   
    else if (cur->type == T_Const) {
        
        res2 = makeNode(Const);
        memcpy(res2, cur, sizeof(Const));
        return (Expr*)res2;
    }
    else if (cur->type == T_OpExpr) {
        
        res = makeNode(OpExpr);
        memcpy(res, cur, sizeof(OpExpr));

        if (res->args->length == 0) 
            return (Expr*)res;
        
        
        lc1.ptr_value = copy_op((Expr *)res->args->elements[0].ptr_value);
        lc2.ptr_value = copy_op((Expr *)res->args->elements[1].ptr_value);

        
        lst = list_make2_impl(T_List, lc1, lc2);
        res->args = lst;

        return (Expr*)res;
    }

    assert(false);
}



/* find_value：根据传入的条件寻找某一列的min值
 * Parameter:
 * [in] splitable_relids: 需要考虑的 feature 的 relid
 * [in] min_values: 与splitable_relids 一一对应，保存relid 对应的min value值
 * [in] relid: 目标的最小id
 * [out] return: relid对应的 min value 值
 */

double find_min_value(InferInfo *ifi, int relid) {
    int cur_relid;
    int i;

    for (i = 0; i < ifi->feature_num; i++)
    {
        cur_relid = ifi->splitable_relids[i];
        if (cur_relid == relid)
            return ifi->min_values[i];
        i += 1;
    }
    return 10.00; // just for debug, should not reach here.
}

double find_max_value(InferInfo *ifi, int relid) {
    int cur_relid;
    int i;

    for (i = 0; i < ifi->feature_num; i++)
    {
        cur_relid = ifi->splitable_relids[i];
        if (cur_relid == relid)
            return ifi->max_values[i];
        i += 1;
    }
    return 10.00; // just for debug, should not reach here.
}


/*  copy_and_delete_op 在一个表达式树中，删除 delete_relid 相关的表达式节点，并返回新的副本
 *  cur: 当前递归节点;
 *  prt: cur 的父亲节点 
 *  delete_relid:  想要去除的那个 relid
 *  splitable_relids: 本次查询相关的 feature 的 relid 的列表
 *  min_values: 本次查询相关的 feature 的最小值，与 splitable_relids 一一对应
 *  [out] deleted_value: 作为结果返回给父节点，是以cur为根的子树中，那些被排除的feature的最小值的总和
 */


Expr *copy_and_delete_op(Expr *cur, int delete_relid, InferInfo *ifi, double *deleted_value) 
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
        if ( ((Var*)cur)->varno == delete_relid) // 当前的 Var 需要被去除
        {
            (*deleted_value) += find_min_value(ifi, delete_relid);
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
            (*deleted_value) += find_min_value(ifi, delete_relid);
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
            linitial(res->args) = copy_and_delete_op(linitial(res->args), delete_relid, ifi, &del_value_fromnow);
            lsecond(res->args) = copy_const_withdelta((Const*)lsecond(res->args), -del_value_fromnow);
            return (Expr *)res;
            break;
        
        case 1758:   // '+' for NUMERIC

            lresult = copy_and_delete_op(
                linitial(res->args), delete_relid, ifi, &del_value_fromnow);     
            rresult = copy_and_delete_op(
                lsecond(res->args), delete_relid, ifi, &del_value_fromnow);

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
                linitial(res->args), delete_relid, ifi, &del_value_fromnow);     
            rresult = copy_and_delete_op(
                lsecond(res->args), delete_relid, ifi, &del_value_fromnow);
            
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
            elog(LOG, "Error 114514: Met some trouble...\n");
            assert(false);
            break;
    }
}


/* distribute_joinqual 函数使用 Shadow_plan 进行重写
 * cur: 当前递归处理中的节点
 * op_passed_tome: 来自父亲节点传下来的 OpExpr
 * splitable_relids: 本次查询相关的 feature 的 relid 的列表
 * min_values: 本次查询相关的 feature 的最小值，与 splitable_relids 一一对应
 */

void distribute_joinqual_shadow(Shadow_Plan *cur, Expr *op_passed_tome, InferInfo *ifi, OpExpr **subop, int depth) {

    // 变量定义(为了遵循源代码风格)
    Plan *lefttree;
    Scan *righttree;
    NestLoop *nsl;

    Expr *modified_op;
    OpExpr *cur_expr; 
    OpExpr *middle_result;
    OpExpr *sub_result;
    OpExpr *individual_scan;
    OpExpr *cur_op;

    double whatever;
    int i;
    TargetEntry *tnt; 
    int delete_relid;
    
    // 变量定义结束

    whatever = 0;
    lefttree = cur->plan->lefttree;
    // **如果当前节点为 Split Node，则将父亲节点传下来的 OpExpr 装备到 joinqual 上 **
    if (cur->spliters != NULL) 
    {
        // 未来修改方向：check list length
        nsl = (NestLoop*) cur->plan;
        if (op_passed_tome != NULL) {
            nsl->join.joinqual = lappend(nsl->join.joinqual, op_passed_tome);
        }


        // TODO: 需要一个更普适性的判断叶子节点的方法 (如果JOB中有非左深树的情况下需要处理)

        if (lefttree->type == T_NestLoop)
        {
            righttree = (Scan*) cur->plan->righttree;
            delete_relid = righttree->scanrelid;

            // TODO：如果右子树是一个无关表...
            modified_op = copy_and_delete_op(llast(nsl->join.joinqual), delete_relid, ifi, &whatever);

            // origintp = ((NestLoop*) cur->plan)->join.joinqual->elements[0].ptr_value;
            // tptp = copy_op( origintp );
            // ((NestLoop*) cur->plan)->join.joinqual->elements[0].ptr_value = tptp;


            distribute_joinqual_shadow(cur->lefttree, modified_op, ifi, &sub_result, depth + 1);

            

            // copy_and_reserve 直接返回的是一个加法表达式
            individual_scan = (OpExpr *) copy_and_reserve(llast(nsl->join.joinqual), delete_relid);
            // 2 * x2 + x1 + 3 * x3 + 4 < 10
            // 当前右子树: scan ==> x1
            // copy_and_delete ==> 2 * x2 + 3 * x3 + 4 < 9
            // copy_and_reserve ==> (x1)
            // 修改后的 part infer filter : ((x1) + (2 * x2 + 3 * x3 + 4)) < 10
            middle_result = makeNode(OpExpr);
            
            middle_result->opno = 1758;         // "+" for NUMERIC
            middle_result->opfuncid = 1724;
            middle_result->opresulttype = NUMERICOID;   
            middle_result->opretset = false;
            middle_result->opcollid = 0;
            middle_result->inputcollid = 0;
            middle_result->location = -1;
            middle_result->args = list_make2(sub_result, individual_scan);

            i = cur->plan->targetlist->length;
            tnt = makeTargetEntry((Expr *) middle_result, i + 1, NULL, false);
            cur->plan->targetlist = lappend(cur->plan->targetlist, tnt);
            
            cur_op = llast(nsl->join.joinqual);
            linitial(cur_op->args) = middle_result;

            *subop = middle_result;
        }
        
        else // 已经到达叶子
        {
            // nsl == current NeStedLoop node
            i = ((Plan *)nsl)->targetlist->length;
            cur_expr = llast(nsl->join.joinqual);
            middle_result = linitial(cur_expr->args);
            tnt = makeTargetEntry((Expr *) middle_result, i + 1, NULL, false);
            ((Plan *)nsl)->targetlist = lappend(((Plan *)nsl)->targetlist, tnt);
            *subop = middle_result;
        }

    }
    else 
    {
        if (lefttree->type == T_NestLoop) 
        {
            distribute_joinqual_shadow(cur->lefttree, op_passed_tome, ifi, subop, depth + 1);
            i = cur->plan->targetlist->length;
            middle_result = *subop;
            tnt = makeTargetEntry((Expr *) middle_result, i + 1, NULL, false);
            cur->plan->targetlist = lappend(cur->plan->targetlist, tnt);
        }
        // else : 是Scan 节点, do nothing
    }
}


// ===========================

Expr *copy_and_reserve(Expr *cur, int reserve_relid) 
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
            linitial(res->args) = copy_and_reserve(linitial(res->args), reserve_relid);

            return linitial(res->args); // 注意，这里返回的是根节点的左子树，即只保留 "lhs <= rhs" 中 lhs 这一部分
            break;
        
        case 1758:   // '+' for NUMERIC

            lresult = copy_and_reserve(
                linitial(res->args), reserve_relid);     
            rresult = copy_and_reserve(
                lsecond(res->args), reserve_relid);

            if (lresult == NULL && rresult == NULL) 
                return NULL;
            else if(lresult == NULL || nodeTag(linitial(res->args)) == T_Const) // 特殊判断: 抛弃加法的 Const 节点
                return rresult;
            else if(rresult == NULL || nodeTag(lsecond(res->args)) == T_Const)  // 特殊判断: 抛弃加法的 Const 节点
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
                linitial(res->args), reserve_relid);     
            rresult = copy_and_reserve(
                lsecond(res->args), reserve_relid);

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

/* collect_relid : 一个工具函数, 扫描一个 OpExpr, 并将其中所有的 Var->varno 添加到 lst 列表中
 * [in] cur: 当前递归栈中所扫描的节点
 * [out] lst: 列表, 所有 varno 都会被放到这个列表中
 */

/*
void collect_relid(Expr *cur, List *lst) {

    Var *cur_var;
    OpExpr *cur_op;

    switch (NodeTag(cur)) {

        case T_Const:
            return;
        case T_Var:
            cur_var = (Var *) cur;
            if (!list_member_int(lst, (int) cur_var->varno))
                lst = lappend_int(lst, (int) cur_var->varno);
            break;
        case T_OpExpr:
            cur_op = (OpExpr *) cur;
            collect_relid( linitial(cur_op->args), lst);
            collect_relid( lsecond(cur_op->args), lst);
            break;
        default:
            break;
    }

}

OpExpr *make_restrict(OpExpr *op, bool use_max, int lmt) {  // 最大值小于一个 Const

    OpExpr *res;
    List *args;
    Const *cst;

    res = makeNode(OpExpr);
    res->opno = (use_max) ? 97 : 521;
    res->opfuncid = (use_max) ? 66 : 147;
    res->opresulttype = 16;
    res->opretset = false;
    res->opcollid = 0;
    res->inputcollid = 0;
    res->location = -1;

    cst = my_make_const(lmt); // 这里先设置 max < 5

    args = list_make2(op, cst);
    res->args = args;
    return res;
}
*/