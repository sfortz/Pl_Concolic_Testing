/* very simple example showing the functionality of the Z3 functions */

:- use_module(swiplz3).

main :-
    C1 = [X=0],
    C2 = [Y=1],
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
    ex_rec(N,[],[C1,C2]),
    z3_del_solver(N),
    z3_del_context(N).
    
ex_rec(N,Vars,[H]) :- 
    copy_term(H,C), 
    print(C), 
    ex(N,[],Vars,H).
ex_rec(N,Vars,[H|T]) :-  
    ex_rec(N,Vars_,T),
    copy_term(H,C), print(C),
    ex(N,Vars_,Vars,C).
    
    
ex(N,OldVars,NewVars,C) :-
    z3_push(N),
    z3_intconstr2smtlib(N,OldVars,C,VarsC1,C1smtlib2),
    (VarsC1=[] -> true ; z3_mk_int_vars(N,VarsC1)),
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
    append(OldVars,VarsC1,NewVars),
    z3_pop(N).


