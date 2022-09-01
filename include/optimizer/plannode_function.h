#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "nodes/primnodes.h"
#include "nodes/nodes.h"


typedef struct InferInfo {
    NodeTag type;
    List *splitable_relids;  // feature 相关的 relid
    List *min_values;        // splitable_relids 中每个表的最小值，一一对应
    List *max_values;        // splitable_relids 中每个表的最大值，一一对应
} InferInfo;


Shadow_Plan *build_shadow_plan(Plan *curplan);
OpExpr *find_sole_op(Shadow_Plan *cur);
void find_split_node
(Shadow_Plan *cur_plan, Shadow_Plan *minrows_node, double min_rows, List *splitable_relids);
Expr *copy_op(Expr *cur);

int find_value(List *splitable_relids, List *min_values, int relid);
Const *my_make_const(int value);
Const *copy_const_withdelta(Const *cur, int delta);
Expr *copy_and_delete_op(Expr *cur, int delete_relid, List *splitable_relids, List *min_values, int *deleted_value);
void collect_relid(Expr *cur, List *lst);

void distribute_joinqual_shadow(Shadow_Plan *cur, Expr *op_passed_tome, InferInfo *ifi, OpExpr **subop, int depth);

// 关于查找 feature 初始值
OpExpr *make_restrict(OpExpr *op, bool use_max, int lmt);

Expr *copy_and_reserve(Expr *cur, int reserve_relid) ;


