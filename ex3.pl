/* very simple example showing the functionality of the Z3 functions over terms and Predicates, with quantifiers*/

/*   From Example A:
        (push)
        (assert (= X (s a)))
        (assert (forall ((Y Term)) (not (= X (s Y)))))
        (assert (= X c))
        (check-sat)
        (get-model)
        (pop)
*/

:- use_module(swiplz3).

main :-
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
    z3_push(N),
/* first constraint */
    C1 =  [X \= (s(a))],
    z3_termconstr2smtlib(N,[],[],C1,VarsC1,TermsC1,C1smtlib2),
    z3_mk_term_type(N,TermsC1),
    (VarsC1=[] -> true ; z3_mk_term_vars(N,VarsC1)),
    z3_assert_term_string(N,C1smtlib2),
/* second constraint */ 
    C2 = [forall(var(Y), X \= (s(Y)))],                      
    z3_termconstr2smtlib(N,C1,TermsC1,C2,VarsC2,TermsC12,C2smtlib2),
    z3_mk_term_type(N,TermsC12),
    (VarsC2=[] -> true ; z3_mk_term_vars(N,VarsC2)),
    z3_assert_term_string(N,C2smtlib2),
/* third constraint */
    C3 = [X \= c],
    z3_termconstr2smtlib(N,(C1,C2),TermsC12,C3,VarsC3,TermsC123,C3smtlib2),
    z3_mk_term_type(N,TermsC123),
    (VarsC3=[] -> true ; z3_mk_term_vars(N,VarsC3)),
    z3_assert_term_string(N,C3smtlib2),
/* checking satisfiability */
    (z3_check(N) ->
        z3_print_model(N),
        get_context_vars(N,VVS),
        get_model_varT_eval(N,VVS,Values),
        %%        nl,format("Variables: "),print(VVS),
        %%        nl,format("Values:    "),print(Values),
        term_variables([C1,C2,C3],AllVars),
        AllVars=Values,
        format("Solved formulas: "),print([C1,C2,C3]),
        nl
    ;
        true
    ),
    z3_pop(N),
    z3_del_solver(N),
    z3_del_context(N).
    
/* C2 = [Y=div(X,3)], */    
 

