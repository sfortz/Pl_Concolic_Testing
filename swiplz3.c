//
//  aux.c
//
//
//  Created by German Vidal on 24/01/2018.
//

#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<string.h>
#include<memory.h>
#include<setjmp.h>
#include<z3.h>
#include<SWI-Prolog.h>

#define LOG_Z3_CALLS

#ifdef LOG_Z3_CALLS
#define LOG_MSG(msg) Z3_append_log(msg)
#else
#define LOG_MSG(msg) ((void)0)
#endif

#define MAXCONS 64
#define MAXSCOPES 64
#define MAXVARS 256
#define MAXTERMS 256
#define MAXARGS 256

/* Some global variables */

Z3_config cfg;  //we consider a single configuration
Z3_context ctx[MAXCONS]; //but MAXCONS different contexts
Z3_solver z3s[MAXCONS];  //and solvers

Z3_sort term_sorts[MAXCONS]; //The type containing terms

Z3_symbol int_var_names[MAXCONS][MAXVARS];
Z3_func_decl int_var_decls[MAXCONS][MAXVARS];
Z3_symbol term_var_names[MAXCONS][MAXVARS];
Z3_func_decl term_var_decls[MAXCONS][MAXVARS];
Z3_symbol term_names[MAXCONS][MAXTERMS];
Z3_func_decl term_decls[MAXCONS][MAXTERMS];

int term_arities[MAXCONS][MAXTERMS]; /* List of the arities of the corresponding terms */
int numintvar[MAXCONS] = { 0 }; /* current number of integer variables in each context */
int numtermvar[MAXCONS] = { 0 }; /* current number of term  variables in each context */
int numintparentvar[MAXCONS][MAXSCOPES] = { 0 }; /* current number of integer variables in the parent scope of each context */
int numtermparentvar[MAXCONS][MAXSCOPES] = { 0 }; /* current number of term  variables in the parent scope of each context */
int numterm[MAXCONS] = { 0 }; /* current number of grounded terms */

long cur = 0; /* current context */

/**
 \brief exit gracefully in case of error.
 */
void exitf(const char* message)
{
    fprintf(stderr,"BUG: %s.\n", message);
    exit(1);
}

/**
 \brief exit if unreachable code was reached.
 */
void unreachable()
{
    exitf("unreachable code was reached");
}


/***************************************************/
/*               some pretty printing              */
/***************************************************/

/**
 \brief Return a char* containing an int given in a certain base.
 */
char* itoa(int val, int base)
{
    static char buffer[32] = {0};
    snprintf(buffer, base, "%d", val);
    return buffer;
}

/**
 \brief Display a symbol in the given output stream.
 */
void display_symbol(Z3_context c, FILE * out, Z3_symbol s)
{
    switch (Z3_get_symbol_kind(c, s)) {
        case Z3_INT_SYMBOL:
            fprintf(out, "#%d", Z3_get_symbol_int(c, s));
            break;
        case Z3_STRING_SYMBOL:
            fprintf(out, "%s", Z3_get_symbol_string(c, s));
            break;
        default:
            unreachable();
    }
}

/**
 \brief Display the given type.
 */
void display_sort(Z3_context c, FILE * out, Z3_sort ty)
{
    switch (Z3_get_sort_kind(c, ty)) {
        case Z3_UNINTERPRETED_SORT:
            display_symbol(c, out, Z3_get_sort_name(c, ty));
            break;
        case Z3_BOOL_SORT:
            fprintf(out, "bool");
            break;
        case Z3_INT_SORT:
            fprintf(out, "int");
            break;
        case Z3_REAL_SORT:
            fprintf(out, "real");
            break;
        case Z3_BV_SORT:
            fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
            break;
        case Z3_ARRAY_SORT:
            fprintf(out, "[");
            display_sort(c, out, Z3_get_array_sort_domain(c, ty));
            fprintf(out, "->");
            display_sort(c, out, Z3_get_array_sort_range(c, ty));
            fprintf(out, "]");
            break;
        case Z3_DATATYPE_SORT:
   	    if (Z3_get_datatype_sort_num_constructors(c, ty) != 1)
            {
		fprintf(out, "%s", Z3_sort_to_string(c,ty));
		break;
	    }
            {
                unsigned num_fields = Z3_get_tuple_sort_num_fields(c, ty);
                unsigned i;
                fprintf(out, "(");
                for (i = 0; i < num_fields; i++) {
                    Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
                    if (i > 0) {fprintf(out, ", ");}
                display_sort(c, out, Z3_get_range(c, field));
                }
            fprintf(out, ")");
            break;
            }
        default:
            fprintf(out, "unknown[");
            display_symbol(c, out, Z3_get_sort_name(c, ty));
            fprintf(out, "]");
            break;
    }
}



/**
 \brief Custom ast pretty printer.

 This function demonstrates how to use the API to navigate terms.
 */
void display_ast(Z3_context c, FILE * out, Z3_ast v)
{
    switch (Z3_get_ast_kind(c, v)) {
        case Z3_NUMERAL_AST: {
            Z3_sort t;
            fprintf(out, "%s", Z3_get_numeral_string(c, v));
            t = Z3_get_sort(c, v);
            fprintf(out, ":");
            display_sort(c, out, t);
            break;
        }
        case Z3_APP_AST: {
            unsigned i;
            Z3_app app = Z3_to_app(c, v);
            unsigned num_fields = Z3_get_app_num_args(c, app);
            Z3_func_decl d = Z3_get_app_decl(c, app);
            fprintf(out, "%s", Z3_func_decl_to_string(c, d));
            if (num_fields > 0) {
                fprintf(out, "[");
                for (i = 0; i < num_fields; i++) {
                    if (i > 0) {
                        fprintf(out, ", ");
                    }
                    display_ast(c, out, Z3_get_app_arg(c, app, i));
                }
                fprintf(out, "]");
            }
            break;
        }
        case Z3_QUANTIFIER_AST: {
            fprintf(out, "quantifier");
            ;
        }
        default:
            fprintf(out, "#unknown");
    }
}

/**
 \brief Custom function interpretations pretty printer.
 */
void display_function_interpretations(Z3_context c, FILE * out, Z3_model m)
{
    unsigned num_functions, i;

    fprintf(out, "function interpretations:\n");

    num_functions = Z3_model_get_num_funcs(c, m);
    for (i = 0; i < num_functions; i++) {
        Z3_func_decl fdecl;
        Z3_symbol name;
        Z3_ast func_else;
        unsigned num_entries = 0, j;
        Z3_func_interp_opt finterp;

        fdecl = Z3_model_get_func_decl(c, m, i);
        finterp = Z3_model_get_func_interp(c, m, fdecl);
        Z3_func_interp_inc_ref(c, finterp);
        name = Z3_get_decl_name(c, fdecl);
        display_symbol(c, out, name);
        fprintf(out, " = {");
        if (finterp)
        num_entries = Z3_func_interp_get_num_entries(c, finterp);
        for (j = 0; j < num_entries; j++) {
            unsigned num_args, k;
            Z3_func_entry fentry = Z3_func_interp_get_entry(c, finterp, j);
            Z3_func_entry_inc_ref(c, fentry);
            if (j > 0) {
                fprintf(out, ", ");
            }
            num_args = Z3_func_entry_get_num_args(c, fentry);
            fprintf(out, "(");
            for (k = 0; k < num_args; k++) {
                if (k > 0) {
                    fprintf(out, ", ");
                }
                display_ast(c, out, Z3_func_entry_get_arg(c, fentry, k));
            }
            fprintf(out, "|->");
            display_ast(c, out, Z3_func_entry_get_value(c, fentry));
            fprintf(out, ")");
            Z3_func_entry_dec_ref(c, fentry);
        }
        if (num_entries > 0) {
            fprintf(out, ", ");
        }
        fprintf(out, "(else|->");
        func_else = Z3_func_interp_get_else(c, finterp);
        display_ast(c, out, func_else);
        fprintf(out, ")}\n");
        Z3_func_interp_dec_ref(c, finterp);
    }
}

/**
 \brief Custom model pretty printer.
 */
void display_model(Z3_context c, FILE * out, Z3_model m)
{
    unsigned num_constants;
    unsigned i;

    if (!m) return;

    num_constants = Z3_model_get_num_consts(c, m);
    for (i = 0; i < num_constants; i++) {
        Z3_symbol name;
        Z3_func_decl cnst = Z3_model_get_const_decl(c, m, i);
        Z3_ast a, v;
        Z3_bool ok;
        name = Z3_get_decl_name(c, cnst);
        display_symbol(c, out, name);
        fprintf(out, " = ");
        a = Z3_mk_app(c, cnst, 0, 0);
        v = a;
        ok = Z3_model_eval(c, m, a, 1, &v);
        display_ast(c, out, v);
        fprintf(out, "\n");
    }
    display_function_interpretations(c, out, m);
}



/***************************************************/
/*               make a new context                */
/***************************************************/

/**
 \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    char *error = NULL;

    printf("Error: %s\n\n", Z3_get_error_msg(c,e));

    switch(e)
    {
        case Z3_OK:
            error = "Z3_OK";
            break;
        case Z3_SORT_ERROR:
            error = "Z3_SORT_ERROR";
            break;
        case Z3_IOB:
            error = "Z3_IOB";
            break;
        case Z3_INVALID_ARG:
            error = "Z3_INVALID_ARG";
            break;
        case Z3_PARSER_ERROR:
            error = "Z3_PARSER_ERROR";
            break;
        case Z3_NO_PARSER:
            error = "Z3_NO_PARSER";
            break;
        case Z3_INVALID_PATTERN:
            error = "Z3_INVALID_PATTERN";
            break;
        case Z3_MEMOUT_FAIL:
            error = "Z3_MEMOUT_FAIL";
            break;
        case Z3_FILE_ACCESS_ERROR:
            error = "Z3_FILE_ACCESS_ERROR";
            break;
        case Z3_INTERNAL_FATAL:
            error = "Z3_INTERNAL_FATAL";
            break;
        case Z3_INVALID_USAGE:
            error = "Z3_INVALID_USAGE";
            break;
        case Z3_DEC_REF_ERROR:
            error = "Z3_DEC_REF_ERROR";
            break;
        case Z3_EXCEPTION:
            error = "Z3_EXCEPTION";
            break;
        default:
            error = "Z3 BUG: unknown error";
    }

    term_t t1 = PL_new_term_ref();
    t1 = PL_new_functor(PL_new_atom(error), 0);
    PL_raise_exception(t1);    /* raise the exception */
}

/**
 Create a configuration
 */
static foreign_t pl_mk_config()
{
    cfg = Z3_mk_config();
    return 1;
}

/**
 Delete a configuration
 */
static foreign_t pl_del_config()
{
    Z3_del_config(cfg);
    return 1;
}

/**
 Set a configuration parameter
 */
static foreign_t pl_set_param_value(term_t param, term_t value)
{
    char *par = NULL;
    char *val = NULL;
    if (!PL_get_chars(param,&par,CVT_STRING))
        return PL_warning("z3_set_parameter_value/1: instantiation fault (parameter)");
    if (!PL_get_chars(value,&val,CVT_STRING))
        return PL_warning("z3_set_parameter_value/1: instantiation fault (value)");

    Z3_set_param_value(cfg,par,val);
    return 1;
}

/**
 Create a context with index ind using the current configuration
 Enable tracing to stderr and register standard error handler.
 */
static foreign_t pl_mk_context(term_t ind)
{
    int rval;

    if (cur<MAXCONS) {
        ctx[cur] = Z3_mk_context(cfg);
        Z3_set_error_handler(ctx[cur], error_handler);
        rval = PL_unify_integer(ind,cur);
        cur++;
    } else {
        return PL_warning("z3_mk_context/1: max contexts reached");
    }
    return rval;
}

/**
 Create a solver associated to the context with index ind
 */
static foreign_t pl_mk_solver(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_mk_solver/2: instantiation fault");

    z3s[i] = Z3_mk_solver(ctx[i]);
    Z3_solver_inc_ref(ctx[i], z3s[i]);

    return 1;
}

/**
 Delete a solver associated to the context with index ind
 */
static foreign_t pl_del_solver(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_del_solver/2: instantiation fault");

    Z3_solver_dec_ref(ctx[i], z3s[i]);

    return 1;
}


/**
 Delete a context with index ind
 */
static foreign_t pl_del_context(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
        return PL_warning("z3_del_context/1: instantiation fault");

    Z3_del_context(ctx[i]);

    return 1;
}

/**
 Create a backtracking point in the context with index ind
 */
static foreign_t pl_push(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_push/1: instantiation fault");

    int s = Z3_solver_get_num_scopes(ctx[i],z3s[i]);
    numintparentvar[i][s] = numintvar[i];
    numtermparentvar[i][s] = numtermvar[i];

    //printf("\n\nscope %i var = %i\n",s,numtermvar[i]);

        //printf("Push from scope %i ", s);
    Z3_solver_push(ctx[i],z3s[i]);
       // printf("to scope %i\n", Z3_solver_get_num_scopes(ctx[i],z3s[i]));
    int t = Z3_solver_get_num_scopes(ctx[i],z3s[i]);
    //printf("scope %i var = %i\n",t,numtermvar[i]);
    return 1;
}

/**
 Backtrack one point in the context with index ind
 */
static foreign_t pl_pop(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_pop/1: instantiation fault");

    int t = Z3_solver_get_num_scopes(ctx[i],z3s[i]);
    //printf("scope %i var = %i\n",t,numtermvar[i]);

       // printf("Pop from scope %i ", Z3_solver_get_num_scopes(ctx[i],z3s[i]));
    Z3_solver_pop(ctx[i],z3s[i],1);

    int s = Z3_solver_get_num_scopes(ctx[i],z3s[i]);
    numintvar[i] = numintparentvar[i][s];
    numtermvar[i] = numtermparentvar[i][s];
       // printf("to scope %i\n", s);

   // printf("scope %i var = %i\n\n",s,numtermvar[i]);

    return 1;
}

/**
 \brief Create a variable using the given name and type.
 */
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/**
 \brief Create an integer variable using the given name.
 */
Z3_ast mk_int_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
 \brief Create a real variable using the given name.
 */
Z3_ast mk_real_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_real_sort(ctx);
    return mk_var(ctx, name, ty);
}

static foreign_t pl_mk_int_vars(term_t ind, term_t varlist)
{
    int i;

    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_parse_string/2: instantiation fault (context)");

    term_t plvar = PL_new_term_ref();   /* the elements */
    term_t list = PL_copy_term_ref(varlist); /* copy (we modify list) */

    while( PL_get_list(list, plvar, list) )
    {
        char *varname = NULL;
        if (!PL_get_chars(plvar,&varname,CVT_STRING))
        return PL_warning("z3_mk_int_vars/2: instantiation fault");

        Z3_ast v = mk_int_var(ctx[i], varname);
        int_var_names[i][numintvar[i]] = Z3_mk_string_symbol(ctx[i], varname);
        int_var_decls[i][numintvar[i]] = Z3_get_app_decl(ctx[i],  Z3_to_app(ctx[i], v));
        numintvar[i]=numintvar[i]+1;
    }

    return PL_get_nil(list);

}

/**
 Gets the name of the functor from the Prolog pair: (functor, arity)
 */
static char* get_term_name(term_t functor)
{
    char *termstr;
    int n;
    atom_t name;

    term_t a = PL_new_term_ref();

    n = PL_get_arg(1, functor, a);
    n = PL_get_chars(a, &termstr, CVT_ALL);

    return termstr;
}

/**
 Gets the arity of the functor from the Prolog pair: (functor, arity)
 */
static int get_term_arity(term_t functor)
{
    char *s;
    int arity, n;
    atom_t name;

    term_t a = PL_new_term_ref();

    n = PL_get_arg(2, functor, a);
    n = PL_get_chars(a, &s, CVT_ALL);
    arity = atoi(s);

    return arity;
}

/**
 Constructs the accessor name for the "name" functor
 */
static Z3_symbol get_accessor_name(Z3_context ctx_i, char* name)
{
    Z3_symbol is_sym;
    char *buffer = malloc (4 + strlen(name));
    strcpy (buffer, "is_");
    strcat(buffer,name);
    is_sym = Z3_mk_string_symbol(ctx_i,buffer);
    free (buffer);

    return is_sym;
}

/**
 Constructs the accessor name for the jth arguments of the "name" functor
 */
static Z3_symbol get_node_accessor_name(Z3_context ctx_i, char* name, int j)
{
    Z3_symbol arg;
    char *buffer = malloc (10 + strlen(name));
    strcpy(buffer,name);
    strcat(buffer,"_arg_");
    strcat(buffer,itoa(j,10));
    arg = Z3_mk_string_symbol(ctx_i, buffer);
    free (buffer);

    return arg;
}

/**
 Declares the Term datatype
 */
static foreign_t pl_mk_term_type(term_t ind, term_t termlist){

    int i;

    if ( !PL_get_integer(ind, &i) )
        return PL_warning("z3_parse_string/2: instantiation fault (context)");

    Z3_context ctx_i = ctx[i];
    Z3_constructor constructors[MAXTERMS];
    Z3_symbol sym, is_sym;
    unsigned j;

    term_t head = PL_new_term_ref();   /* the elements */
    term_t list = PL_copy_term_ref(termlist); /* copy (we modify list) */

    numterm[i] = 0;

    while(PL_get_list(list, head, list)){
        char *name = get_term_name(head);
        int arity = get_term_arity(head);

        sym = Z3_mk_string_symbol(ctx_i,name);
        is_sym = get_accessor_name(ctx_i,name);

        term_names[i][numterm[i]] = sym;
        term_arities[i][numterm[i]] = arity;

        if (arity == 0){
            constructors[numterm[i]] = Z3_mk_constructor(ctx_i, sym, is_sym, 0,0,0,0);
        }else{
            Z3_symbol node_accessor_names[arity];
            for (j = 0; j < arity; ++j) {
                node_accessor_names[j] = get_node_accessor_name(ctx_i,name,j);
            };

            Z3_sort   node_accessor_sorts[MAXARGS] = { 0 };
            unsigned  node_accessor_sort_refs[MAXARGS] = { 0 };

            constructors[numterm[i]] = Z3_mk_constructor(ctx_i, sym, is_sym,
            arity, node_accessor_names, node_accessor_sorts, node_accessor_sort_refs);
        }

        numterm[i]++;
    }

    /* create the new recursive datatype */
    term_sorts[i] = Z3_mk_datatype(ctx_i,Z3_mk_string_symbol(ctx_i, "Term"),numterm[i],constructors);

    for (j = 0; j < numterm[i]; ++j){
        Z3_func_decl decl, is_decl;
        int arity = term_arities[i][j];
        if (arity == 0){
            /* retrieve the new declarations: constructors (a_decl, b_decl, succ_decl), testers (is_a_decl, is_b_decl, is_succ_del), and accessors (arg_decl) */
            Z3_query_constructor(ctx_i, constructors[j], 0, &decl, &is_decl, 0);
        }else{
            Z3_func_decl node_accessors[arity];
            /* retrieve the new declarations: constructors (a_decl, b_decl, succ_decl), testers (is_a_decl, is_b_decl, is_succ_del), and accessors (arg_decl) */
            Z3_query_constructor(ctx_i, constructors[j], arity, &decl, &is_decl, node_accessors);
        }
        term_decls[i][j] = decl;
        /* delete auxiliary/helper structures */
        Z3_del_constructor(ctx_i, constructors[j]);
    }

    return PL_get_nil(list);
}

static foreign_t pl_mk_term_vars(term_t ind, term_t varlist)
{
    int i;

    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_parse_string/2: instantiation fault (context)");

    term_t plvar = PL_new_term_ref();   /* the elements */
    term_t list = PL_copy_term_ref(varlist); /* copy (we modify list) */

    while( PL_get_list(list, plvar, list) )
    {
        char *varname = NULL;
        if (!PL_get_chars(plvar,&varname,CVT_STRING))
        return PL_warning("z3_mk_pred_vars/2: instantiation fault");

        Z3_ast v = mk_var(ctx[i], varname, term_sorts[i]);
        term_var_names[i][numtermvar[i]] = Z3_mk_string_symbol(ctx[i], varname);
        term_var_decls[i][numtermvar[i]] = Z3_get_app_decl(ctx[i],  Z3_to_app(ctx[i], v));
        numtermvar[i]=numtermvar[i]+1;
    }

    return PL_get_nil(list);

}

/**
 Declares a new integer variable intvarname in context ind
 */
static foreign_t pl_assert_int_string(term_t ind, term_t plstr)
{
    Z3_error_code e;
    int i;
    unsigned j;

    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_assert_int_string/2: instantiation fault (context)");

    char *z3string = NULL;
    if (!PL_get_chars(plstr,&z3string,CVT_STRING))
    return PL_warning("z3_assert_int_string/2: instantiation fault (string)");

    Z3_ast_vector fs = Z3_parse_smtlib2_string(ctx[i], z3string, 0,0,0, numintvar[i], int_var_names[i], int_var_decls[i]);

    //printf("--asserted formula: %s\n", Z3_ast_vector_to_string(ctx[i], fs));

    e = Z3_get_error_code(ctx[i]);
    if (e != Z3_OK) goto err;

    for (j = 0; j < Z3_ast_vector_size(ctx[i], fs); ++j) {
        Z3_solver_assert(ctx[i], z3s[i], Z3_ast_vector_get(ctx[i], fs, j));
    }

    return 1;

err:
    printf("Z3 error: %s.\n", Z3_get_error_msg(ctx[i], e));
    return 0;
}

/**
 Declares a new term variable termvarname in context ind
 */
static foreign_t pl_assert_term_string(term_t ind, term_t plstr)
{
    Z3_error_code e;
    int i;
    unsigned j;

    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_assert_term_string/2: instantiation fault (context)");

    Z3_context ctx_i = ctx[i];

    char *z3string = NULL;
    if (!PL_get_chars(plstr,&z3string,CVT_STRING))
    return PL_warning("z3_assert_term_string/2: instantiation fault (string)");

    Z3_symbol sort_name = Z3_get_sort_name(ctx_i, term_sorts[i]);

    int k = numtermvar[i] + numterm[i];
    Z3_symbol names[k];
    Z3_func_decl decls[k];

    for(j = 0; j < numtermvar[i]; ++j){
        names[j] = term_var_names[i][j];
        decls[j] = term_var_decls[i][j];
  //      Z3_string test = Z3_get_symbol_string( ctx_i,term_var_names[i][j]);
  //      printf("term_var_names: %s\n", test);
    }

/*
    for(j = 0; j < numterm[i]; ++j){
        names[j+ numtermvar[i]] = term_names[i][j];
        decls[j+ numtermvar[i]] = term_decls[i][j];
        Z3_string test = Z3_get_symbol_string( ctx_i,term_names[i][j]);
        printf("term_names: %s\n", test);
    }
*/
  //      printf("OK... %s\n",z3string);
      //  printf("Param Values: %i = %i + %i\n", k,numtermvar[i],numterm[i]);
    Z3_ast_vector fs = Z3_parse_smtlib2_string(ctx_i, z3string, 1, &sort_name, &term_sorts[i], numtermvar[i], names, decls);
    //Z3_ast_vector fs = Z3_parse_smtlib2_string(ctx_i, z3string, 1, &sort_name, &term_sorts[i], k, names, decls);

//printf("formula asserted\n");
    //printf("--asserted formula: %s\n", Z3_ast_vector_to_string(ctx_i, fs));

    e = Z3_get_error_code(ctx[i]);
    if (e != Z3_OK) goto err;

    for (j = 0; j < Z3_ast_vector_size(ctx_i, fs); ++j) {
        Z3_solver_assert(ctx[i], z3s[i], Z3_ast_vector_get(ctx_i, fs, j));
    }

    return 1;

err:
    printf("Z3 error: %s.\n", Z3_get_error_msg(ctx[i], e));
    return 0;
}


/**
    Check the satisfiability of a context with index ind
 */
static foreign_t pl_check(term_t ind)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
        return PL_warning("z3_check/1: instantiation fault");

    Z3_lbool result = Z3_solver_check(ctx[i],z3s[i]);

    Z3_model m = 0;

    int rval=1;

    switch (result) {
        case Z3_L_FALSE:
            //printf("unsat\n");
            rval = 0;
            break;
        case Z3_L_TRUE:
            //printf("sat\n");
            break;
        case Z3_L_UNDEF:
            //printf("undef\n");
            break;
    }
    return rval;
}

/**
 Show the computed model for a context ind
 */
static foreign_t pl_print_model(term_t ind, term_t t)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_get_model/1: instantiation fault");

    Z3_model m = 0;

    m = Z3_solver_get_model(ctx[i], z3s[i]);
    if (m) Z3_model_inc_ref(ctx[i], m);

    char const *str = Z3_model_to_string(ctx[i], m);
    //printf("MODEL:\n%s", Z3_model_to_string(ctx[i], m));

    int rmod;
    rmod = PL_unify_string_chars(t, str);

    return rmod;
}

/**
 Show the computed model for an integer variable
 */
static foreign_t pl_get_model_intvar_eval(term_t ind, term_t varname, term_t varval)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_get_model_intvar_eval/3: instantiation fault (context)");

    char *vn = NULL;
    if (!PL_get_chars(varname,&vn,CVT_STRING))
    return PL_warning("z3_get_model_intvar_eval/3: instantiation fault (varname)");

    Z3_model m = 0;

    m = Z3_solver_get_model(ctx[i], z3s[i]);
    if (m) Z3_model_inc_ref(ctx[i], m);

    Z3_ast n = mk_int_var(ctx[i], vn);
    Z3_ast v;

    int val;
    if (Z3_model_eval(ctx[i], m, n, 1, &v)) {
        Z3_get_numeral_int(ctx[i], v, &val);
    } else {
        exitf("failed to evaluate the variable");
    }

    int rval;
    rval = PL_unify_integer(varval, val);

    return rval;
}

static term_t mk_term(Z3_context ctx, Z3_ast v){

    functor_t functor = PL_new_term_ref();
    term_t term  = PL_new_term_ref();
    unsigned j;

    Z3_app app = Z3_to_app(ctx, v);
    Z3_func_decl f = Z3_get_app_decl(ctx, app);
    Z3_symbol sym = Z3_get_decl_name(ctx, f);
    char const *name = Z3_get_symbol_string(ctx, sym);
    int arity = Z3_get_arity(ctx, f);

    functor = PL_new_functor(PL_new_atom(name), arity);

    if (arity == 0) {
        j = PL_cons_functor(term, functor);
    } else {
        term_t args[arity];
        for (j = 0; j < arity; ++j){
            Z3_ast arg = Z3_get_app_arg(ctx, app, j);
            args[j] = mk_term(ctx, arg);
        }

        switch (arity) {
        case 1:
            j = PL_cons_functor(term, functor, args[0]);
            break;
        case 2:
            j = PL_cons_functor(term, functor, args[0], args[1]);
            break;
        case 3:
            j = PL_cons_functor(term, functor, args[0], args[1], args[2]);
            break;
        case 4:
            j = PL_cons_functor(term, functor, args[0], args[1], args[2], args[3]);
            break;
        case 5:
            j = PL_cons_functor(term, functor, args[0], args[1], args[2], args[3], args[4]);
            break;
        case 6:
            j = PL_cons_functor(term, functor, args[0], args[1], args[2], args[3], args[4], args[5]);
            break;
        case 7:
            j = PL_cons_functor(term, functor, args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
            break;
        case 8:
            j = PL_cons_functor(term, functor, args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
            break;
        case 9:
            j = PL_cons_functor(term, functor, args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8]);
            break;
        case 10:
            j = PL_cons_functor(term, functor, args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], args[8], args[9]);
            break;
        default:
            exitf("functor with too many arguments (huge arity)");
        }
    }

    return term;
}

/**
 Show the computed model for a term variable
 */
static foreign_t pl_get_model_termvar_eval(term_t ind, term_t varname, term_t varval)
{
    int i;
    if ( !PL_get_integer(ind, &i) )
    return PL_warning("z3_get_model_intvar_eval/3: instantiation fault (context)");

    char *vn = NULL;
    if (!PL_get_chars(varname,&vn,CVT_STRING))
    return PL_warning("z3_get_model_intvar_eval/3: instantiation fault (varname)");

    Z3_model m = 0;

    m = Z3_solver_get_model(ctx[i], z3s[i]);
    if (m) Z3_model_inc_ref(ctx[i], m);

    Z3_ast n = mk_var(ctx[i], vn, term_sorts[i]);
    Z3_ast v;

    term_t val = PL_new_term_ref();

    if (Z3_model_eval(ctx[i], m, n, 1, &v)) {
        val = mk_term(ctx[i], v);
    } else {
        exitf("failed to evaluate the variable");
    }

    int rval;
    rval = PL_unify(varval, val);

    return rval;
}

/***************************************************/
/*         registered SWI Prolog predicates        */
/***************************************************/

install_t install()
{
    PL_register_foreign("z3_mk_config", 0, pl_mk_config, 0);
    PL_register_foreign("z3_del_config", 0, pl_del_config, 0);
    PL_register_foreign("z3_set_param_value", 2, pl_set_param_value, 0);
    PL_register_foreign("z3_mk_new_context", 1, pl_mk_context, 0);
    PL_register_foreign("z3_del_context", 1, pl_del_context, 0);
    PL_register_foreign("z3_mk_solver", 1, pl_mk_solver, 0);
    PL_register_foreign("z3_del_solver", 1, pl_del_solver, 0);
    PL_register_foreign("z3_push", 1, pl_push, 0);
    PL_register_foreign("z3_pop", 1, pl_pop, 0);
    PL_register_foreign("z3_mk_int_vars", 2, pl_mk_int_vars, 0);
    PL_register_foreign("z3_mk_term_type", 2, pl_mk_term_type, 0);
    PL_register_foreign("z3_mk_term_vars", 2, pl_mk_term_vars, 0);
    PL_register_foreign("z3_assert_int_string_", 2, pl_assert_int_string, 0);
    PL_register_foreign("z3_assert_term_string_", 2, pl_assert_term_string, 0);
    PL_register_foreign("z3_check", 1, pl_check, 0);
    PL_register_foreign("z3_print_model", 2, pl_print_model, 0);
    PL_register_foreign("z3_get_model_intvar_eval", 3, pl_get_model_intvar_eval, 0);
    PL_register_foreign("z3_get_model_termvar_eval", 3, pl_get_model_termvar_eval, 0);

}
