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

#include "utils/numeric.h"
#include "utils/selfuncs.h"
#include "utils/float.h"

#include "parser/parse_coerce.h"
#include "parser/parse_node.h"
#include "c.h"
// ==========================================

// 判断当前filter是否为infer对应filter，返回 true or false。 
bool isInferFilter(void *qual) {

	OpExpr *op;

	switch ( ((Node*)qual)->type)
	{
		case T_OpExpr:
		{
			op = (OpExpr*) qual;
			if (op->opno == 1755 || op->opno == 1757)
				return true;
			return false;
			break;
		}
		default:
		{
			return false;
			break;
		}
	}
	
	return false;
}


double constvalue_to_double(Datum datum) {
	double val = convert_numeric_to_scalar(datum, NUMERICOID, NULL);
	return val;
}

// 从Query中获得label condition
// 返回一个 <RangeInfo 的 List> 类型
List *get_label_condition(Query *parse)
{

  	RangeInfo *label_condition;
	ListCell *lc;
	OpExpr *op;
	List *quals;
	List *label_feature_index_list;

	label_condition = NULL;
	label_feature_index_list = NULL;
	// 实际上 parse->jointree->quals 不一定是 List*, 在定义中是 Node*
	// 当前 parse->jointree->quals 实际上是一个 OpExpr*
	// 在 JOB1a 中，可以发现 parse->jointree->quals 真的是一个 List*
  	quals = ((BoolExpr *) parse->jointree->quals)->args;

  	foreach (lc, quals)
  	{
		// 适用于JOB测试的判断即可 
		op = (OpExpr *) lfirst(lc);	

		if (isInferFilter(lfirst(lc)))
		{
			label_condition = makeNode(RangeInfo);
			// 从q中得知查询中label值是包含上界还是下界，常量值为多少。 

			switch (op->opno)
			{
				
				case 1755: 	// <= for NUMERIC
					label_condition->has_upper_thd = true; 
					label_condition->has_lower_thd = false; 
					label_condition->label_upper_value = constvalue_to_double(((Const *) lsecond(op->args))->constvalue); 
					label_condition->label_lower_value = -get_float8_infinity(); 
					break;
				
				case 1757: // >= for NUMERIC
					label_condition->has_upper_thd = false; 
					label_condition->has_lower_thd = true; 
					label_condition->label_upper_value = get_float8_infinity();
					label_condition->label_lower_value = constvalue_to_double(((Const *) lsecond(op->args))->constvalue);
					break;

				default:
					break;
			}
			label_feature_index_list = lappend(label_feature_index_list, label_condition);
		} 
	}
  	return label_feature_index_list;
}


void 
add_quals_using_label_range(Query *parse, LFIndex *lfi) // entry point, in function standard_planner
{
	RangeInfo *label_condition;
	RangeInfo *lf_index;
	List *lf_index_list = NULL;
	List *quals_prototype = NULL;
	List *argslist;
	List *label_feature_index_list;
	ListCell *lc;
	ListCell *lf_lc;
	OpExpr *up_op;
	OpExpr *low_op;
	int counter = 0;
	// ========================================
	
	// 如果在 jointree 中没有任何的限制条件, 则不需要计算 lfindex
	if (parse->jointree->quals == NULL)
		return;

	label_feature_index_list = get_label_condition(parse);


	argslist = ((BoolExpr *) parse->jointree->quals)->args;
	foreach(lc, argslist) {
		quals_prototype = lappend(quals_prototype, lfirst(lc));
	}

	// 下面这一行虽然是 foreach 但是由于在 JOB 上的实验暂时只添加一个 Filter, 所以只会运行一次

	foreach(lf_lc, label_feature_index_list)
	{
		label_condition = lfirst(lf_lc);
		lf_index_list = compute_lf_index(label_condition, lfi); 

		lfi->has_upper_thd = label_condition->has_upper_thd;
		lfi->has_lower_thd = label_condition->has_lower_thd;
		lfi->label_upper_value = label_condition->label_upper_value;
		lfi->label_lower_value = label_condition->label_lower_value;

		foreach(lc, lf_index_list)
		{
			lf_index = (RangeInfo *) lfirst(lc);
			if (lf_index == NULL) continue;

			counter += 1;
			if (lf_index->has_upper_thd)
			{
				if(!lf_index->is_trans) // W 为正，feature有上界
				{ 
					up_op = create_additional_upper_qual(lf_index->feature_relid, lf_index->feature_colid,
						lf_index->feature_upper_value, lf_index->feature_typeoid);

					elog(LOG, "now, counter = %d, [%d] [%d] [%lf] [%d]\n", counter, lf_index->feature_relid, lf_index->feature_colid, lf_index->feature_upper_value,lf_index->feature_typeoid);
				}
				else // W 为负，feature有下界 
				{ 
					up_op = create_additional_lower_qual(lf_index->feature_relid, lf_index->feature_colid,
					lf_index->feature_lower_value, lf_index->feature_typeoid);

					elog(LOG, "now, counter = %d, [%d] [%d] [%lf] [%d]\n", 
						counter, lf_index->feature_relid, lf_index->feature_colid, lf_index->feature_upper_value,
						lf_index->feature_typeoid);
				}
				// parse->jointree->quals = (Node *)lappend((List *)parse->jointree->quals, up_op);
				quals_prototype = lappend(quals_prototype, up_op);
			}
			else if (lf_index->has_lower_thd)
			{ 
				if(!lf_index->is_trans) // W 为正，feature有下界
				{ 	
					low_op = create_additional_lower_qual(lf_index->feature_relid, lf_index->feature_colid, 
						lf_index->feature_lower_value, lf_index->feature_typeoid);

					elog(LOG, "now, counter = %d, [%d] [%d] [%lf] [%d]\n", 
						counter, lf_index->feature_relid, lf_index->feature_colid, lf_index->feature_upper_value,
						lf_index->feature_typeoid);
				}
				else	// W 为负，feature有上界 
				{ 	
					low_op = create_additional_upper_qual(lf_index->feature_relid, lf_index->feature_colid,
						lf_index->feature_upper_value, lf_index->feature_typeoid);	
					
					elog(LOG, "now, counter = %d, [%d] [%d] [%lf] [%d]\n", 
						counter, lf_index->feature_relid, lf_index->feature_colid, lf_index->feature_upper_value,
						lf_index->feature_typeoid);
				}
				// parse->jointree->quals = (Node *)lappend((List *)parse->jointree->quals, low_op);
				quals_prototype = lappend(quals_prototype, low_op);
			}
		}
	}
	parse->jointree->quals = (Node *) makeBoolExpr(AND_EXPR, quals_prototype, -1);

	// 选择使用 feature_condition
	set_feature_contidion(lfi);
	elog(LOG, "counter = %d\n", counter);
}

 
List *compute_lf_index(RangeInfo *label_condition, LFIndex *lfi)
{	
	double sum_min_y, sum_max_y;
	double feature_min, feature_max; 
	double inf_min_y, inf_max_y;
	double tmp;
	int i;

	bool is_trans_flag[5] = {false, false, false, false, false}; 
	List *lf_index_list;
	RangeInfo *lf_index;

	lf_index_list = list_make1(NULL);
	// 处理W为负的情况
	for (i = 1; i <= lfi->feature_num; i++)
		if (lfi->W[i] < 0.0)
		{
			tmp = lfi->min_values[i];
			lfi->min_values[i] = lfi->max_values[i] * (-1.0);
			lfi->max_values[i] = tmp * (-1.0);
			lfi->W[i] = lfi->W[i] * (-1.0);
			is_trans_flag[i] = true;
		}

	// 处理单边label range情况
	inf_min_y = lfi->W[0]; // 用户没有给label下界时，下界的值 
	inf_max_y = lfi->W[0]; // 用户没有给label上界时，上界的值 
	for (i = 1; i <= lfi->feature_num; i++)
	{
		inf_min_y += lfi->W[i] * lfi->min_values[i];
		inf_max_y += lfi->W[i] * lfi->max_values[i];
	}

	if (!label_condition->has_upper_thd)	 // thd = threshold
	{
		label_condition->label_upper_value = inf_max_y;
	}
	if (!label_condition->has_lower_thd)
	{
		label_condition->label_lower_value = inf_min_y;
	}

	// 开始计算
	sum_min_y = label_condition->label_lower_value - lfi->W[0]; 
	sum_max_y = label_condition->label_upper_value - lfi->W[0]; 
	for (i = 1; i <= lfi->feature_num; i++)
	{
		sum_min_y -= lfi->W[i] * lfi->max_values[i];
		sum_max_y -= lfi->W[i] * lfi->min_values[i];
	}
	for (i = 1; i <= lfi->feature_num; i++)
	{
		// 计算feature range
		feature_min = Max((sum_min_y / lfi->W[i] + lfi->max_values[i]), lfi->min_values[i]); 
		feature_max = Min((sum_max_y / lfi->W[i] + lfi->min_values[i]), lfi->max_values[i]);

		// 记录feature range
		lf_index = makeNode(RangeInfo);
		lf_index->has_upper_thd = label_condition->has_upper_thd; 
		lf_index->has_lower_thd = label_condition->has_lower_thd; 
		lf_index->label_upper_value = label_condition->label_upper_value; 
		lf_index->label_lower_value = label_condition->label_lower_value; 
		lf_index->feature_relid = lfi->feature_rel_ids[i];
		lf_index->feature_colid = lfi->feature_col_ids[i];
		if (!is_trans_flag[i])
		{
			lf_index->is_trans = false;
			lf_index->feature_upper_value = feature_max;
			lf_index->feature_lower_value = feature_min;
			lf_index->weight_value = lfi->W[i];

			lfi->min_conditions[i] = feature_min;
			lfi->max_conditions[i] = feature_max;
		}
		else	// W 负的情况，把feature取值范围和模型参数还原
		{
			lf_index->is_trans = true;
			lf_index->feature_upper_value = (-1.0) * feature_min;
			lf_index->feature_lower_value = (-1.0) * feature_max;
			lf_index->weight_value = (-1.0) * lfi->W[i];

			lfi->min_conditions[i] = feature_max;
			lfi->max_conditions[i] = feature_min;
		}

		lf_index->feature_typeoid = (i == 1) ? INT4OID : NUMERICOID;

		lf_index_list = lappend(lf_index_list, lf_index);
  	}
  	return lf_index_list;
}


// ***************************
// Create Node Functions

Node *create_numeric_var_node_from_int4(int rtb_id, int rtb_col) 
{
	Var *curvar;
	Node *coerced_var;

	curvar = makeVar(rtb_id, rtb_col, INT4OID, -1, 0, 0);
	/*
	    核心问题：现在原本的 feature 是保存的 Ingeter.
	    正在尝试是否能将其修改为 Numeric,
		这里调用函数 coerce_type 将表中保存的 INT4 转换为 NUMERIC
	*/
	coerced_var = coerce_to_target_type(NULL, (Node *)curvar, INT4OID, NUMERICOID, -1, 
		COERCION_IMPLICIT, COERCE_IMPLICIT_CAST, -1);
	return coerced_var;
}

Node *create_numeric_var_node_from_numeric(int rtb_id, int rtb_col) 
{
	Var *curvar;
	curvar = makeVar(rtb_id, rtb_col, NUMERICOID, -1, 0, 0);
	return (Node *) curvar;
}

Const *create_const_node(double up_thd) 
{
	char *fval;
	Value *val;
	
	fval = (char *) palloc(16 + 1);	 // 我只是猜测这里是 16 位
	sprintf(fval, "%f", up_thd);
	val = makeFloat(fval);
	return make_const(NULL, val, -1);
}


// ****************************
// Create Rstrict


OpExpr *create_additional_upper_qual(int rtb_id, int rtb_col, const double up_thd, int typeoid) 
{
	List *args_list;
	OpExpr *op;

	if (typeoid == INT4OID) {	// 对于 production_year 这个列需要先转换成 NUMERIC
		args_list = list_make2(
			create_numeric_var_node_from_int4(rtb_id, rtb_col),
			create_const_node(up_thd)
		);
	}
	else {
		args_list = list_make2(
			create_numeric_var_node_from_numeric(rtb_id, rtb_col),
			create_const_node(up_thd)
		);
	}
	
	op = makeNode(OpExpr);
	/*
		这里的 1754 和 1722 再次写死,  对应着 numeric 变量类型的 "<".
		'<' = 1754 (backend/catalog/postgres.bki)
		numeric_lt = 1722 (backend/utils/fmgrtab.c)
		尽管如此，我一直在想怎么避免这样的写死的开发方式...
	*/
	op->opno = 1754;		
	op->opfuncid = 1722;

	op->opresulttype = 16;	// boolean
	op->opretset = false;
	op->opcollid = 0;
	op->inputcollid = 0;
	op->args = args_list;
	op->location = -1;
	return op;
}

OpExpr *create_additional_lower_qual(int rtb_id, int rtb_col, const double lo_thd, int typeoid) 
{
	List *args_list;
	OpExpr *op;


	if (typeoid == INT4OID) {	// 对于 production_year 这个列需要先转换成 NUMERIC
		args_list = list_make2(
			create_numeric_var_node_from_int4(rtb_id, rtb_col),
			create_const_node(lo_thd)
		);
	}
	else {
		args_list = list_make2(
			create_numeric_var_node_from_numeric(rtb_id, rtb_col),
			create_const_node(lo_thd)
		);
	}

	op = makeNode(OpExpr);
	op->opno = 1756;		
	op->opfuncid = 1720;

	op->opresulttype = 16;	// boolean
	op->opretset = false;
	op->opcollid = 0;
	op->inputcollid = 0;
	op->args = args_list;
	op->location = -1;
	return op;
}