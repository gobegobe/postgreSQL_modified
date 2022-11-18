#ifndef plannodefunction_h
#define plannodefunction_h

#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "nodes/primnodes.h"
#include "nodes/nodes.h"


/* ----------------------------------------------------------------
 * Shadow Plan Node
 */
typedef struct Shadow_Plan {
	NodeTag type;
	Plan *plan;

	List *spliters;
	bool is_endnode;
	
	struct Shadow_Plan *parent;
	struct Shadow_Plan *lefttree;
	struct Shadow_Plan *righttree;
} Shadow_Plan;

/* ----------------------------------------------------------------
 * LFIndex : 保存运行时所需的所有中间信息
 */

typedef struct LFIndex {
    NodeTag type;
    int feature_num;
    double W[5];                // Model 相关的 weight
    List *feature_rel_ids[5];     // feature 相关的 relid
    int feature_col_ids[5];     // feature 相关的 column number
    double min_values[5];       // splitable_relids 中每个表的最小值，一一对应
    double max_values[5];       // splitable_relids 中每个表的最大值，一一对应

    double min_conditions[5];   // 使用 lfindex 计算出的 feature condition (MIN)
    double max_conditions[5];   // 使用 lfindex 计算出的 feature condition (MAX)

    // 保存 Label 相关信息, 未来或许会使用
    bool has_upper_thd; // default value is false;
    bool has_lower_thd; // default value is false;
    double label_upper_value;
    double label_lower_value;

    // 中间处理信息
    int split_node_deepest;

} LFIndex;

/* ----------------------------------------------------------------
 * FilterInfo : 为未来预留的接口: 保存所有看到的初始 Filter
 * 如果未来要对两个 Filter 进行下推的话, 应该从这里取
 */

typedef struct FilterInfo {
    NodeTag type;
    List *shadow_roots;      // 自顶向下推 Filter 的起点(一些Shadow_plan) 的列表
    List *filter_ops;        // 与 shadow_roots 一一对应, 需要向下推的 Filter
                             // 注意, 这里使用双列表设计的原因是一个 shadow_root 可能对应多个 filter
} FilterInfo;


// ---------- LFIndex Functions -----------------------------------

void Init_LFIndex(LFIndex* lfi, Query* parse);

// ---------- Util Functions -----------------------------------

bool Is_feature_relid(LFIndex *lfi, int relid);

Shadow_Plan *build_shadow_plan(Plan *curplan, Shadow_Plan *parent);

void find_sole_op(Shadow_Plan *cur, FilterInfo *fi);

void find_split_node (Shadow_Plan *cur_plan, Shadow_Plan *minrows_node, double min_rows, LFIndex *lfi, int depth1, int depth2,
    List **ridlist, List **depthlist, int *max_depth);

double find_min_value(LFIndex *lfi, int relid);

double find_max_value(LFIndex *lfi, int relid);

// ---------- Filter-distribute Functions -----------------------------------

Expr *copy_and_delete_op(Expr *cur, int delete_relid, LFIndex *lfi,
    double *deleted_value, double current_fac, double *factor, double *leftconst);

void pushdown_get_filterflags(Shadow_Plan *cur, LFIndex *lfi, int *filter_flags);

void greedy_get_filterflags(Shadow_Plan *cur, LFIndex *lfi, int *filter_flags);

void distribute_by_flag(Shadow_Plan *cur, LFIndex *lfi, 
    int depth, int segmentcounter,
    OpExpr **subop, int *filter_flags, List *filterlist);

// ---------- Middle-result-passing Functions -----------------------------------
// 以下三个函数为传递中间结果而设计

OpExpr *construct_targetlist_nonleaf(Shadow_Plan *cur, LFIndex *lfi, int delete_relid, 
    Expr *op_passed_tome, OpExpr *res_from_bottom, int depth, int emplace_filter);

OpExpr *constrct_targetlist_leaf(Shadow_Plan *cur, LFIndex *lfi, Expr *op_passed_tome, int depth);

Expr *copy_and_reserve(Expr *cur, int reserve_relid, bool reserve_const) ;

// ---------- Node creating Functions -----------------------------------

Const *copy_const_withdelta(Const *cur, double delta);

#endif