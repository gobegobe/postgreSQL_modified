#ifndef fuzz_inferh
#define fuzz_inferh

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

#include "optimizer/lfindex.h"
#include "optimizer/plannode_function.h"


void preprocess_filters(PlannerInfo *pni, LFIndex *lfi, Expr *cur_op, List *ridlist, List *depthlist, List** filterlist);

double calc_selec(PlannerInfo *pni, LFIndex *lfi, List *varlist, List *ridlist, double *factorlist, 
    int len, double leftconst, double *rightconsts, int base);

/* 在给定全局信息 PlannerInfo 的情况下, 通过直方图查询 var 这一列的平均值 */
double query_var_average(PlannerInfo *root, Var *var);


/* 
   将某个 OpExpr 所在的不等式切换成 [Var < ConstValue] 的格式。
   PG 的代价估计确实很不准: 例如 feature1 < 50.0 可以使用直方图估算，
   但是  2.0 * feature1 < 100.0 就不会估算了, 会直接返回 0.33。
   考虑到我们的情况实际上是较为简单的, 只有一个线性的不等式, 所以这里我们手动地处理一下。
*/

OpExpr *copy_and_transpose(PlannerInfo *root, OpExpr *curop, int reserve_relid);

/* 
    被 copy_and_transpose 调用的子函数
    我们需要收集以下几个信息：
    *obj_var       ->  varno = reverve_relid 的那个 Var*
    *obj_ratio     ->  上述 Var 对应的系数
    *deleted_value ->  除去这个 Var 之后，其余的那些行, 它们的均值之和
*/

bool collect_var_info(PlannerInfo *root, Expr *cur, int reserve_relid,
                    Var **obj_var, double *obj_ratio, double *deleted_value);


/* 将 datum 所包含的浮点数换成可以被 C 语言处理的类型 */
double datum_to_double(Datum datum);
double datum_to_int(Datum datum);

/* 创建一个 Const 节点，其中的值为 v */
Const *create_const_from_double(double v);

// ********************** 第二步相关 *******************
List * move_filter_local_optimal(Shadow_Plan *root, LFIndex *lfi, PlannerInfo *pni);

bool collect_segment(LFIndex *lfi, Shadow_Plan *begin_node, Shadow_Plan **end_node);

double get_filter_selectivity(PlannerInfo *pnl, OpExpr *cur_op, int reserve_relid);

double get_join_cost(Shadow_Plan *cur_node);

Shadow_Plan *move_filter_toopt(PlannerInfo *pni, Shadow_Plan *begin_node, Shadow_Plan *end_node);



// ********************** 第三步相关 *******************

List *transfer_node_to_list(Shadow_Plan* root);

void merge_filter(Shadow_Plan *root, List *opt_join_node_list, LFIndex *lfi);

void move_filter_impl(Shadow_Plan *root, LFIndex *lfi, int node_size, int flag[]);

#endif