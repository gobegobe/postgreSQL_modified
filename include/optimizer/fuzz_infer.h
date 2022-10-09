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


/* 将 datum 所包含的浮点数换成可以被 C 语言处理的 double 类型 */
double datum_to_double(Datum datum);

/* 创建一个 Const 节点，其中的值为 v */
Const *create_const_from_double(double v);