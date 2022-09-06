#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "nodes/primnodes.h"
#include "nodes/nodes.h"


typedef struct InferInfo {
    NodeTag type;
    int feature_num;
    double W[5];                // Model 相关的 weight
    int feature_rel_ids[5];     // feature 相关的 relid
    int feature_col_ids[5];     // feature 相关的 column number
    double min_values[5];       // splitable_relids 中每个表的最小值，一一对应
    double max_values[5];       // splitable_relids 中每个表的最大值，一一对应

    double min_conditions[5];   // 使用 lfindex 计算出的 feature condition (MIN)
    double max_conditions[5];   // 使用 lfindex 计算出的 feature condition (MAX)
} InferInfo;

typedef struct FilterInfo {
    NodeTag type;
    List *shadow_roots;      // 自顶向下推 Filter 的起点(一些Shadow_plan) 的列表
    List *filter_ops;        // 与 shadow_roots 一一对应, 需要向下推的 Filter
                             // 注意, 这里使用双列表设计的原因是一个 shadow_root 可能对应多个 filter
} FilterInfo;


void Init_inferinfo(InferInfo* ifi, Query* parse);

void set_feature_contidion(InferInfo *ifi);

Shadow_Plan *build_shadow_plan(Plan *curplan);

void find_sole_op(Shadow_Plan *cur, FilterInfo *fi);

void find_split_node
(Shadow_Plan *cur_plan, Shadow_Plan *minrows_node, double min_rows, InferInfo *ifi, int depth1, int depth2);


double find_min_value(InferInfo *ifi, int relid);
double find_max_value(InferInfo *ifi, int relid);

Const *copy_const_withdelta(Const *cur, double delta);

Expr *copy_and_delete_op(Expr *cur, int delete_relid, InferInfo *ifi, double *deleted_value);

void distribute_joinqual_shadow(Shadow_Plan *cur, Expr *op_passed_tome, InferInfo *ifi, OpExpr **subop, int depth);

// 关于查找 feature 初始值
OpExpr *make_restrict(OpExpr *op, bool use_max, int lmt);

Expr *copy_and_reserve(Expr *cur, int reserve_relid) ;

// 关于建立节点

Const *my_make_const(int value);
