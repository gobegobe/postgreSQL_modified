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


double *preprocess_filters(PlannerInfo *pni, LFIndex *lfi, Expr *cur_op, List *ridlist, List *depthlist, List** filterlist);

double calc_selec(PlannerInfo *pni, LFIndex *lfi, List *varlist, List *ridlist, double *factorlist, 
    int len, double leftconst, double *rightconsts, int base);


/* 
    被 copy_and_transpose 调用的子函数
    我们需要收集以下几个信息：
    *obj_var       ->  varno = reverve_relid 的那个 Var*
    *obj_ratio     ->  上述 Var 对应的系数
    *deleted_value ->  除去这个 Var 之后，其余的那些行, 它们的均值之和
*/

bool collect_var_info(PlannerInfo *root, Expr *cur, int reserve_relid,
                    Var **obj_var, double *obj_ratio, double *deleted_value);




/* 创建一个 Const 节点，其中的值为 v */
Const *create_const_from_double(double v);

double get_join_cost(Shadow_Plan *cur_node);

int *determine_filter(Shadow_Plan *root, LFIndex *lfi, double *selectivity_list);

List *get_segment_table(Shadow_Plan *root, LFIndex *lfi);

/* 将 datum 所包含的浮点数换成可以被 C 语言处理的类型 */
double datum_to_double(Datum datum);
double datum_to_int(Datum datum);

#endif