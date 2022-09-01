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

/*
 * Build a ShadowPlan Tree from a Plan Tree.
 */

Shadow_Plan *build_shadow_plan(Plan *curplan) {

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


OpExpr *find_sole_op(Shadow_Plan *cur) {

    List *joinqual;
    OpExpr *res1;
    OpExpr *res2;

    if (cur->plan->type != T_NestLoop)
        return NULL;
    
    joinqual = ((NestLoop*) cur->plan)->join.joinqual;
    if (joinqual != NULL)
        return (OpExpr *) linitial(joinqual);
    
    if (cur->lefttree)
    {
        res1 = find_sole_op(cur->lefttree);
        if (res1)
            return res1;
    }
    if (cur->righttree)
    {
        res2 = find_sole_op(cur->righttree);
        if (res2)
            return res2;
    }
    return NULL;
}



/* 
    在计划树上寻找 Split Node
 */

void find_split_node
(Shadow_Plan *cur_plan, Shadow_Plan *minrows_node, double min_rows, List *splitable_relids) {

    // 当前进行了很大程度上的简化：假定计划树上的节点只有
    // 1. NestLoop Join 节点
    // 2. 一些 Scan 节点，包括 IndexScan 和 SeqScan
    int relid;


	if (cur_plan->plan->type == T_NestLoop) {
		Shadow_Plan *next_node = minrows_node;
		double next_minrows = min_rows;
		if (cur_plan->plan->plan_rows <= min_rows) {
			next_minrows = cur_plan->plan->plan_rows;
			next_node = cur_plan;
		}
		if (cur_plan->lefttree != NULL)
			find_split_node(cur_plan->lefttree, next_node, next_minrows, splitable_relids);
		if (cur_plan->righttree != NULL)
			find_split_node(cur_plan->righttree,  next_node, next_minrows, splitable_relids);
		return;
	}

	// Not a "Join Node"
    // Shadow_plan 的 spliters 这个域一开始是 NULL
    // 这样做的好处之一是可以判断一个节点是否为 SplitNode 

    relid = ((IndexScan*)cur_plan->plan)->scan.scanrelid;
    if (!list_member_int(splitable_relids, relid))
        return;

    if (minrows_node->spliters == NULL) {
        minrows_node->spliters = list_make1((void *) cur_plan);
    }
    else {
        minrows_node->spliters = lappend(minrows_node->spliters, (void *)cur_plan);
    }
}

void collect_relid(Expr *cur, List *lst) {

    Var *cur_var;
    OpExpr *cur_op;

    switch (cur->type) {

        case T_Const:
            return;
        case T_Var:
            cur_var = (Var *) cur;
            lappend_int(lst, (int) cur_var->varno);
            break;
        case T_OpExpr:

            cur_op = (OpExpr *) cur;
            collect_relid(cur_op->args->elements[0].ptr_value, lst);
            collect_relid(cur_op->args->elements[1].ptr_value, lst);
            break;
        default:
            break;
    }

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

Const *copy_const_withdelta(Const *cur, int delta) {

    Const *res;
    res = makeNode(Const);
    memcpy(res, cur, sizeof(Const));
    res->constvalue = cur->constvalue + delta;
    return res;
}

Const *my_make_const(int value) {
    Const *res;

    res = makeNode(Const);
    res->consttype = 23;
    res->consttypmod = -1;
    res->constcollid = 0;
    res->constlen = 4;
    res->constvalue = value;
    res->constisnull = false;
    res->constbyval = true;
    res->location = -1;
    return res;
}

/* find_value：根据传入的条件寻找某一列的min值
 * [in] splitable_relids: 需要考虑的 feature 的 relid
 * [in] min_values: 与splitable_relids 一一对应，保存relid 对应的min value值
 * [in] relid: 目标的最小id
 * [out] return: relid对应的 min value 值
 */

int find_value(List *splitable_relids, List *values, int relid) {
    ListCell *cell1;
    ListCell *cell2;
    int cur_relid;
    int cur_min;

    forboth(cell1, splitable_relids, cell2, values) {
        cur_relid = lfirst_int(cell1);
        cur_min = lfirst_int(cell2);
        if (cur_relid == relid)
            return cur_min;
    }
    return 10;
}


/*  copy_and_delete_op 在一个表达式树中，删除 delete_relid 相关的表达式节点，并返回新的副本
 *  cur: 当前递归节点;
 *  prt: cur 的父亲节点 
 *  delete_relid:  想要去除的那个 relid
 *  splitable_relids: 本次查询相关的 feature 的 relid 的列表
 *  min_values: 本次查询相关的 feature 的最小值，与 splitable_relids 一一对应
 *  [out] deleted_value: 作为结果返回给父节点，是以cur为根的子树中，那些被排除的feature的最小值的总和
 */


Expr *copy_and_delete_op(Expr *cur, int delete_relid, List *splitable_relids, List *min_values, int *deleted_value) 
{
    // 变量定义
    int del_value_fromnow;
    Expr *left;
    Expr *right;
    Expr *lresult;
    Expr *rresult;

    OpExpr *res;
    OpExpr *opcur;
    // 变量定义结束

    if (cur->type == T_Const) // 常量节点
    {
        return cur;
    }
    else if (cur->type == T_Var) // feature 节点
    {
        if ( ((Var*)cur)->varno == delete_relid) // 当前的 Var 需要被去除
        {
            (*deleted_value) += find_value(splitable_relids, min_values, delete_relid);
            return NULL;
        }
        else
            return cur;
    }
    // else： 现在 cur 可以确定为 OpExpr
    
    // linitial 代表取某个 List* 的第一个值的 void* 形式 (lsecond 是第二个值的 void*)
    // 观察代码可以发现, 它是一个左值

    opcur = (OpExpr *) cur;
    left = (Expr*) linitial(opcur->args);
    right =  (Expr*) lsecond(opcur->args);

    del_value_fromnow = 0;

    // res 首先为当前节点 cur 的复制, 一个细节是这里把args复制了, 它是一个必要的操作
    res = makeNode(OpExpr);
    memcpy(res, opcur, sizeof(OpExpr));
    res->args = list_copy(opcur->args);

    switch (opcur->opno) 
    {
        case 97:    // '<' for integer

            // 现在假设任何 < 号右侧都是一个常数，且 < 永远在 OpExpr 的根节点
            linitial(res->args) = copy_and_delete_op(
                linitial(res->args), delete_relid, splitable_relids, min_values, &del_value_fromnow);
            lsecond(res->args) = copy_const_withdelta((Const*)lsecond(res->args), -del_value_fromnow);
            return (Expr *)res;
            break;
        
        case 551:   // '+' for integer

            lresult = copy_and_delete_op(
                linitial(res->args), delete_relid, splitable_relids, min_values, &del_value_fromnow);     
            rresult = copy_and_delete_op(
                lsecond(res->args), delete_relid, splitable_relids, min_values, &del_value_fromnow);

            (*deleted_value) += del_value_fromnow;

            if (lresult == NULL && rresult == NULL) 
                return NULL;
            else if(lresult == NULL)
                return rresult;
            else if(rresult == NULL)
                return lresult;
            else {
                linitial(res->args) = lresult;
                lsecond(res->args) = rresult;
                return (Expr *)res;
            }
                

            break;
            
        case 514:   // '*' for integer
            // 对于 * 运算符, 暂时认为其左右节点中, 至少有一个是常数节点

            lresult = copy_and_delete_op(
                linitial(res->args), delete_relid, splitable_relids, min_values, &del_value_fromnow);     
            rresult = copy_and_delete_op(
                lsecond(res->args), delete_relid, splitable_relids, min_values, &del_value_fromnow);
            
            if (left->type == T_Const) {
                (*deleted_value) += ((Const *)lresult)->constvalue * del_value_fromnow;
            } else if (right->type == T_Const) {
                (*deleted_value) += ((Const *)rresult)->constvalue * del_value_fromnow;
            }

            

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


/* distribute_joinqual 函数使用 Shadow_plan 进行重写
 * cur: 当前递归处理中的节点
 * op_passed_tome: 来自父亲节点传下来的 OpExpr
 * splitable_relids: 本次查询相关的 feature 的 relid 的列表
 * min_values: 本次查询相关的 feature 的最小值，与 splitable_relids 一一对应
 */

void distribute_joinqual_shadow(Shadow_Plan *cur, Expr *op_passed_tome, InferInfo *ifi, OpExpr **subop, int depth) {

    // 变量定义(为了遵循源代码风格)
    Plan *lefttree;
    IndexScan *righttree;

    Expr *modified_op;
    List *cur_joinqual;
    void *origintp;
    void *tptp;
    OpExpr *cur_expr; 
    OpExpr *middle_result;
    OpExpr *sub_result;
    OpExpr *individual_scan;
    OpExpr *cur_op;

    int whatever;
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
        if (op_passed_tome != NULL) {
            cur_joinqual = list_make1(op_passed_tome);
            ((NestLoop*) cur->plan)->join.joinqual = cur_joinqual;
        }


        // TODO: 需要一个更普适性的判断叶子节点的方法 (如果JOB中有非左深树的情况下需要处理)

        if (lefttree->type == T_NestLoop)
        {
            righttree = (IndexScan*) cur->plan->righttree;
            delete_relid = (righttree->scan).scanrelid;

            // TODO：如果右子树是一个无关表...
            modified_op = copy_and_delete_op(
                linitial( ((NestLoop*)cur->plan)->join.joinqual),
                delete_relid, ifi->splitable_relids, ifi->min_values, &whatever
            );

            origintp = ((NestLoop*) cur->plan)->join.joinqual->elements[0].ptr_value;
            tptp = copy_op( origintp );
            ((NestLoop*) cur->plan)->join.joinqual->elements[0].ptr_value = tptp;


            distribute_joinqual_shadow(cur->lefttree, modified_op, ifi, &sub_result, depth + 1);

            i = cur->plan->targetlist->length;
            individual_scan = (OpExpr *) 
                copy_and_reserve(linitial( ((NestLoop*)cur->plan)->join.joinqual), delete_relid);

            // 2 * x2 + x1 + 3 * x3 + 4 < 10
            // 当前右子树: scan ==> x1
            // copy_and_delete ==> 2 * x2 + 3 * x3 + 4 < 9
            // copy_and_reserve ==> (x1)
            // 修改后的 part infer filter : ((x1) + (2 * x2 + 3 * x3 + 4)) < 10

            // copy_and_reserve 直接返回的是一个加法表达式
            individual_scan = linitial(individual_scan->args);
    
            middle_result = makeNode(OpExpr);
            
            middle_result->opno = 551;
            middle_result->opfuncid = 177;
            middle_result->opresulttype = 23;
            middle_result->opretset = false;
            middle_result->opcollid = 0;
            middle_result->inputcollid = 0;
            middle_result->location = -1;
            middle_result->args = list_make2(sub_result, individual_scan);

            tnt = makeTargetEntry((Expr *) middle_result, i + 1, NULL, false);
            cur->plan->targetlist = lappend(cur->plan->targetlist, tnt);
            
            cur_op = linitial( ((NestLoop*) cur->plan)->join.joinqual);
            linitial(cur_op->args) = middle_result;

            *subop = middle_result;
        }
        
        else // 已经到达叶子
        {
            i = cur->plan->targetlist->length;
            cur_expr = linitial(((NestLoop*) cur->plan)->join.joinqual);
            middle_result = linitial(cur_expr->args);
            tnt = makeTargetEntry((Expr *) middle_result, i + 1, NULL, false);
            cur->plan->targetlist = lappend(cur->plan->targetlist, tnt);
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
        // else : 是Scan 节点
    }

    if (depth == 1) 
    {
        list_delete_last(cur->plan->targetlist);
    }
    if (depth == 2)
    {
        cur->plan->targetlist = list_delete_nth_cell(
            cur->plan->targetlist, 1
        );
    }
    /*
    if (depth == 1)
    {
        int temp1, temp2;
        OpExpr *ano = copy_and_reserve(linitial( ((NestLoop*)cur->plan)->join.joinqual),
            1, ifi, &temp1, &temp2);
        OpExpr *adder1 = linitial(ano->args);
        OpExpr *adder2 = ((TargetEntry *) lthird(cur->plan->targetlist))->expr;
        OpExpr *sum = makeNode(OpExpr);
        sum->opno = 551;
        sum->opfuncid = 177;
        sum->opresulttype = 23;
        sum->opretset = false;
        sum->opcollid = 0;
        sum->inputcollid = 0;
        sum->location = -1;
        sum->args = list_make2(adder1, adder2);
        ((NestLoop*) cur->plan)->join.joinqual = list_make1(
            make_restrict(sum, true, 15)
        );

        cur->plan->targetlist = list_delete_nth_cell(
            cur->plan->targetlist, 3
        );

        cur->plan->targetlist = list_delete_nth_cell(
            cur->plan->targetlist, 2
        );
    }

    
    if (depth == 2)
    {
        cur->plan->targetlist = list_delete_nth_cell(
            cur->plan->targetlist, 1
        );
    }
    */
}


// ===========================

Expr *copy_and_reserve(Expr *cur, int reserve_relid) 
{
    // 变量定义
    Expr *lresult;
    Expr *rresult;

    OpExpr *res;
    OpExpr *opcur;

    // 变量定义结束

    if (cur->type == T_Const) // 常量节点需要进行删除
    {
        return cur;
    }
    else if (cur->type == T_Var) // feature 节点
    {
        if ( ((Var*)cur)->varno == reserve_relid) // 当前的 Var 需要被保留，直接返回
        {
            return cur;
        }
        else
        {
            return NULL;
        }
    }

    opcur = (OpExpr *) cur;

    res = makeNode(OpExpr);
    memcpy(res, opcur, sizeof(OpExpr));
    res->args = list_copy(opcur->args);

    switch (opcur->opno) 
    {
        case 97:    // '<' for integer

            // 现在假设任何 < 号右侧都是一个常数，且 < 永远在 OpExpr 的根节点
            linitial(res->args) = copy_and_reserve(
                linitial(res->args), reserve_relid);

            return linitial(res->args); // 注意，这里返回的是根节点的左子树，可能为 NULL
            break;
        
        case 551:   // '+' for integer

            lresult = copy_and_reserve(
                linitial(res->args), reserve_relid);     
            rresult = copy_and_reserve(
                lsecond(res->args), reserve_relid);

            if (lresult == NULL && rresult == NULL) 
                return NULL;
            else if(lresult == NULL)
                return rresult;
            else if(rresult == NULL)
                return lresult;
            else {
                linitial(res->args) = lresult;
                lsecond(res->args) = rresult;
                return (Expr *)res;
            }
            
            break;
            
        case 514:   // '*' for integer
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


/*
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

void assign_single_range(Plan *cur, InferInfo *ifi)
{
    IndexScan *idxcur;
    int cur_relid;
    OpExpr *min_restrict;
    OpExpr *max_restrict;

    switch (cur->type)
    {
        case T_IndexScan:
            idxcur = (IndexScan *) cur;
            cur_relid = idxcur->scan.scanrelid;
            
            min_restrict = make_restrict(cur_relid, false, 0);
            max_restrict = make_restrict(cur_relid, true, 5);

            if (cur->qual == NULL) {
                cur->qual = list_make2(min_restrict, max_restrict);
            } else {
                cur->qual = lappend(cur->qual, min_restrict);
                cur->qual = lappend(cur->qual, max_restrict);
            }
            break;
        
        default:
            break;
    }
}

void assign_value_range(Shadow_Plan *cur, InferInfo *ifi)
{

    // 变量定义(为了遵循源代码风格)
    Plan *lefttree;
    Plan *righttree;
    // 变量定义结束

    // 这里有一个先验知识：默认除了叶子节点的右子树都是 IndexScan
    lefttree = cur->plan->lefttree;
    righttree = cur->plan->righttree;
    
    assign_single_range(righttree, ifi);

    if (lefttree->type == T_IndexScan) 
    {
        assign_single_range(lefttree, ifi);
    }
    else 
    {
        assign_value_range(cur->lefttree, ifi);
    }
    
} 


*/