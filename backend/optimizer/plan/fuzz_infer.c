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

#include "optimizer/fuzz_infer.h"
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
#include "utils/selfuncs.h"
#include "utils/lsyscache.h"
#include "utils/numeric.h"

double datum_to_double(Datum datum) {
	double val = convert_numeric_to_scalar(datum, NUMERICOID, NULL);
	return val;
}


double query_var_average(PlannerInfo *root, Var *var)
{
    int sz;
    VariableStatData vardata;
	AttStatsSlot sslot;

    if (!IsA(var, Var))
    {
        elog(WARNING, "<query_var_average> TYPE_ERROR: arg->type = [%d], T_Var = [%d]", ((Node*)var)->type, T_Var);
        return 0.0;
    }
    

    examine_variable(root, var, 0, &vardata);
    get_attstatsslot(&sslot, vardata.statsTuple, STATISTIC_KIND_HISTOGRAM,
			0, ATTSTATSSLOT_VALUES);
    sz = sslot.nvalues;

    if (sz == 0)
    {
        elog(WARNING, "<query_var_average> size == 0, returnning 0.0");
        return 0.0;
    }
    
    return datum_to_double(sslot.values[(sz + 1) / 2]);
}