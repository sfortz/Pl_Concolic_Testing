/**
   \brief Demonstrates how to initialize the parser symbol table.
 */
void my_example2()
{
    Z3_context ctx;
    Z3_solver solver;
    Z3_ast x, zero, one, two, x_eq_zero, x_eq_one, x_eq_two;

    ctx = mk_context();
    solver = mk_solver(ctx);
    
    x = mk_int_var(ctx, "x");
    int result;
    
    Z3_solver_inc_ref(ctx, solver);
    
  // --------- ZERO -----------------  
        
   
    Z3_solver_push(ctx, solver);
    
    zero        = mk_int(ctx, 0);
    x_eq_zero     = Z3_mk_eq(ctx, x, zero);
    
    Z3_solver_assert(ctx, solver, x_eq_zero);

    printf("%s \n", Z3_ast_to_string(ctx, x_eq_zero));

    result = Z3_solver_check (ctx, solver);
    printf("Sat Result : %d\n", result);
    printf("Model : %s\n", Z3_model_to_string (ctx,  Z3_solver_get_model (ctx, solver)));
    Z3_solver_pop(ctx, solver, 1);
    
  // --------- ONE -----------------  
    
    Z3_solver_push(ctx, solver);
    
    one         = mk_int(ctx, 1);
    x_eq_one     = Z3_mk_eq(ctx, x, one);
    
    Z3_solver_assert(ctx, solver, x_eq_one);
    printf("%s \n", Z3_ast_to_string(ctx, x_eq_one));
    
    result = Z3_solver_check (ctx, solver);
    printf("Sat Result : %d\n", result);
    printf("Model : %s\n", Z3_model_to_string (ctx,  Z3_solver_get_model (ctx, solver)));
    Z3_solver_pop(ctx, solver, 1);
    
  // --------- END -----------------
  
    Z3_solver_dec_ref(ctx, solver);
}
