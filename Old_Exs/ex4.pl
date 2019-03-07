/* very simple example showing the functionality of the Z3 functions */

:- use_module(swiplz3).

main :-
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
    
   
    C1 = [X=0], 
    z3_intconstr2smtlib(N,[],C1,VarsC1,C1smtlib2),
    (VarsC1=[] -> true ; z3_mk_int_vars(N,VarsC1)),
    C2 = [X=1],
    z3_intconstr2smtlib(N,C1,C2,VarsC2,C2smtlib2),
    (VarsC2=[] -> true ; z3_mk_int_vars(N,VarsC2)),
            nl,print([C2]),nl,
/* first constraint */ 

    z3_push(N),
    z3_assert_int_string(N,C1smtlib2),
    (z3_check(N) ->
        z3_print_model(N),
        get_context_vars(N,VVS),
        get_model_var_eval(N,VVS,Values),
        %%        nl,format("Variables: "),print(VVS),
        %%        nl,format("Values:    "),print(Values),
        term_variables([C1],AllVars),
        AllVars=Values,
        format("Solved formulas: "),print(C1),
        nl
    ;
        true
    ),
    
    z3_pop(N),
    
    
/* second constraint */
    z3_push(N),
    z3_assert_int_string(N,C2smtlib2),  
    (z3_check(N) ->
        z3_print_model(N),
        get_context_vars(N,VVS2),
        get_model_var_eval(N,VVS2,Values2),
        %%        nl,format("Variables: "),print(VVS2),
        %%        nl,format("Values:    "),print(Values2),
        nl,print([C2]),nl,
        term_variables([C2],AllVars2),
        AllVars2=Values2,
        format("Solved formulas: "),print([C2]),
        nl
    ;
        true
    ),
    z3_pop(N),
    
    z3_del_solver(N),
    z3_del_context(N).


