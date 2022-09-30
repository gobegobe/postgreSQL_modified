#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "nodes/primnodes.h"
#include "nodes/nodes.h"


typedef struct LFIndex {
    NodeTag type;
    int feature_num;
    double W[8];                // Model 相关的 weight
    List *feature_rel_ids[8];     // feature 相关的 relid
    int feature_col_ids[8];     // feature 相关的 column number
    double min_values[8];       // splitable_relids 中每个表的最小值，一一对应
    double max_values[8];       // splitable_relids 中每个表的最大值，一一对应

    double min_conditions[8];   // 使用 lfindex 计算出的 feature condition (MIN)
    double max_conditions[8];   // 使用 lfindex 计算出的 feature condition (MAX)

    // 保存 Label 相关信息, 未来或许会使用
    bool has_upper_thd; // default value is false;
    bool has_lower_thd; // default value is false;
    double label_upper_value;
    double label_lower_value;

    // 中间处理信息
    int split_node_deepest;

} LFIndex;

bool Is_feature_relid(LFIndex *lfi, int relid);

typedef struct FilterInfo {
    NodeTag type;
    List *shadow_roots;      // 自顶向下推 Filter 的起点(一些Shadow_plan) 的列表
    List *filter_ops;        // 与 shadow_roots 一一对应, 需要向下推的 Filter
                             // 注意, 这里使用双列表设计的原因是一个 shadow_root 可能对应多个 filter
} FilterInfo;

bool double_same(double v1, double v2);

void Init_LFIndex(LFIndex* lfi, Query* parse);

void set_feature_contidion(LFIndex *lfi);

Shadow_Plan *build_shadow_plan(Plan *curplan);

void find_sole_op(Shadow_Plan *cur, FilterInfo *fi);

void find_split_node
(Shadow_Plan *cur_plan, Shadow_Plan *minrows_node, double min_rows, LFIndex *lfi, int depth1, int depth2);


double find_min_value(LFIndex *lfi, int relid, int relcolid);
double find_max_value(LFIndex *lfi, int relid, int relcolid);

Const *copy_const_withdelta(Const *cur, double delta);

Expr *copy_and_delete_op(Expr *cur, int delete_relid, LFIndex *lfi, double *deleted_value);

void distribute_joinqual_shadow(Shadow_Plan *cur, Expr *op_passed_tome, LFIndex *lfi, OpExpr **subop, int depth);

OpExpr *construct_targetlist_nonleaf(Shadow_Plan *cur, LFIndex *lfi, int delete_relid, 
    Expr *op_passed_tome, OpExpr *res_from_bottom, int depth);


OpExpr *constrct_targetlist_leaf(Shadow_Plan *cur, LFIndex *lfi, Expr *op_passed_tome, int depth);

// 关于查找 feature 初始值
OpExpr *make_restrict(OpExpr *op, bool use_max, int lmt);

Expr *copy_and_reserve(Expr *cur, int reserve_relid, bool reserve_const) ;

// 关于建立节点

Const *my_make_const(int value);
