/* very simple example showing the functionality of the Z3 functions */

:- use_module(swiplz3).

main :-
    C1 = [X=0],
    C2 = [Y=1],
    ex_rec([C1,C2]).
    
ex_rec([H]) :- ex(H).
ex_rec([H|T]) :-  
    ex(H),
    ex_rec(T).
    
    
ex(C) :-
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
     
    z3_intconstr2smtlib(N,[],C,VarsC1,C1smtlib2),
    (VarsC1=[] -> true ; z3_mk_int_vars(N,VarsC1)),
   
    z3_push(N),
    z3_assert_int_string(N,C1smtlib2),
    (z3_check(N) ->
        z3_print_model(N),
        get_context_vars(N,VVS),
        get_model_var_eval(N,VVS,Values),
        %%        nl,format("Variables: "),print(VVS),
        %%        nl,format("Values:    "),print(Values),
        term_variables([C],AllVars),
        AllVars=Values,
        format("Solved formulas: "),print(C),
        nl
    ;
        true
    ),
    
    z3_pop(N),
    z3_del_solver(N),
    z3_del_context(N).


