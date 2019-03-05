/**
   \brief Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when
   \c f is injective in the second argument.

   \sa assert_inj_axiom.
*/
void quantifier_example1()
{
    Z3_config  cfg;
    Z3_context ctx;
    Z3_solver s;
    Z3_sort       int_sort;
    Z3_symbol         f_name;
    Z3_sort       f_domain[2];
    Z3_func_decl f;
    Z3_ast            x, y, w, v, fxy, fwv;
    Z3_ast            p1, p2, p3, not_p3;

    cfg = Z3_mk_config();
    /* If quantified formulas are asserted in a logical context, then
       Z3 may return L_UNDEF. In this case, the model produced by Z3 should be viewed as a potential/candidate model.
    */

    /*
       The current model finder for quantified formulas cannot handle injectivity.
       So, we are limiting the number of iterations to avoid a long "wait".
    */
    Z3_global_param_set("smt.mbqi.max_iterations", "10");
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    s = mk_solver(ctx);

    /* declare function f */
    int_sort    = Z3_mk_int_sort(ctx);
    f_name      = Z3_mk_string_symbol(ctx, "f");
    f_domain[0] = int_sort;
    f_domain[1] = int_sort;
    f           = Z3_mk_func_decl(ctx, f_name, 2, f_domain, int_sort);

    /* assert that f is injective in the second argument. */
    assert_inj_axiom(ctx, s, f, 1);

    /* create x, y, v, w, fxy, fwv */
    x           = mk_int_var(ctx, "x");
    y           = mk_int_var(ctx, "y");
    v           = mk_int_var(ctx, "v");
    w           = mk_int_var(ctx, "w");
    fxy         = mk_binary_app(ctx, f, x, y);
    fwv         = mk_binary_app(ctx, f, w, v);

    /* assert f(x, y) = f(w, v) */
    p1          = Z3_mk_eq(ctx, fxy, fwv);
    Z3_solver_assert(ctx, s, p1);

    /* prove f(x, y) = f(w, v) implies y = v */
    p2          = Z3_mk_eq(ctx, y, v);
    printf("prove: f(x, y) = f(w, v) implies y = v\n");
    prove(ctx, s, p2, true);

    /* disprove f(x, y) = f(w, v) implies x = w */
    /* using check2 instead of prove */
    p3          = Z3_mk_eq(ctx, x, w);
    not_p3      = Z3_mk_not(ctx, p3);
    Z3_solver_assert(ctx, s, not_p3);
    printf("disprove: f(x, y) = f(w, v) implies x = w\n");
    printf("that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable\n");
    check2(ctx, s, Z3_L_UNDEF);
    printf("reason for last failure: %s\n",  Z3_solver_get_reason_unknown(ctx, s));
    del_solver(ctx, s);
    Z3_del_context(ctx);
    /* reset global parameters set by this function */
    Z3_global_param_reset_all();
}
/*
  pattern: ((f (:var 0) (:var 1)))

  assert axiom:
  (forall ((x!1 Int) (x!2 Int))
    (! (= (inv!0 (f x!2 x!1)) x!1) :pattern ((f x!2 x!1))))
  prove: f(x, y) = f(w, v) implies y = v
  valid
  disprove: f(x, y) = f(w, v) implies x = w
  that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable
  unknown
  potential model:
  w = 2:int
  v = 1:int
  y = 1:int
  x = 0:int
  function interpretations:
  f = {...}
  reason for last failure: (incomplete quantifiers)
*/

/**
   \brief Demonstrates how to initialize the parser symbol table.
 */
void parser_example3()
{
    Z3_config  cfg;
    Z3_context ctx;
    Z3_solver s;
    Z3_sort       int_sort;
    Z3_symbol     g_name;
    Z3_sort       g_domain[2];
    Z3_func_decl  g;
    Z3_ast_vector thm;

    cfg = Z3_mk_config();
    /* See quantifier_example1 */
    Z3_set_param_value(cfg, "model", "true");
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    s = mk_solver(ctx);

    /* declare function g */
    int_sort    = Z3_mk_int_sort(ctx);
    g_name      = Z3_mk_string_symbol(ctx, "g");
    g_domain[0] = int_sort;
    g_domain[1] = int_sort;
    g           = Z3_mk_func_decl(ctx, g_name, 2, g_domain, int_sort);

    assert_comm_axiom(ctx, s, g);

    thm = Z3_parse_smtlib2_string(ctx,
                           "(assert (forall ((x Int) (y Int)) (=> (= x y) (= (g x 0) (g 0 y)))))",
                           0, 0, 0,
                           1, &g_name, &g);
    printf("formula: %s\n", Z3_ast_vector_to_string(ctx, thm));
    prove(ctx, s, Z3_ast_vector_get(ctx, thm, 0), true);

    del_solver(ctx, s);
    Z3_del_context(ctx);
}

/*
  assert axiom:
  (ast-vector
    (forall ((x Int) (y Int)) (= (g x y) (g y x))))
  formula: (ast-vector
    (forall ((x Int) (y Int)) (=> (= x y) (= (g x 0) (g 0 y)))))
  valid
*/
