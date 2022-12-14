#ifndef lfindex_h
#define lfindex_h

#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "nodes/primnodes.h"
#include "nodes/nodes.h"

#include "optimizer/plannode_function.h"

// A private struct in lfindex.h / lfindex.c
// Store intermediate values, and will finally store its value into LFInfo struct

typedef struct RangeInfo {
    NodeTag type;

    bool has_upper_thd; // default value is false;
    bool has_lower_thd; // default value is false;
    double label_upper_value;
    double label_lower_value;

    int feature_relid;
    int feature_colid;
    double feature_upper_value;
    double feature_lower_value;
    
    double feature_range_max;
    double feature_range_min;

    int feature_typeoid;

    bool is_trans; // default value is false;
    double weight_value;
	
} RangeInfo;


// =========================================================
// **************** Cauculation Functions

void set_feature_contidion(LFIndex *lfi);

List *get_label_condition(Query *parse);

void add_quals_using_label_range(Query *parse, LFIndex *lfi);

List *compute_lf_index(RangeInfo *label_condition, LFIndex *lfi);


// =========================================================
// **************** Util Functions

bool double_same(double v1, double v2);

bool isInferFilter(void *qual);

double constvalue_to_double(Datum datum);

// =========================================================
// **************** Create Node Functions

Node *create_numeric_var_node_from_int4(int rtb_id, int rtb_col);

Node *create_numeric_var_node_from_numeric(int rtb_id, int rtb_col);

Const *create_const_node(double up_thd);


// **************** Create Restrict

OpExpr *create_additional_upper_qual(int rtb_id, int rtb_col, const double up_thd, int typeoid);

OpExpr *create_additional_lower_qual(int rtb_id, int rtb_col, const double lo_thd, int typeoid);

#endif