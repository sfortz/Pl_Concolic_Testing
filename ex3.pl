/* very simple example showing the functionality of the Z3 functions over terms and Predicates, with quantifiers*/

/*   From Example A */

:- use_module(swiplz3).

main :-
    C1 = [X1 \= (s(a))],
    C2 = [forall(var(Y1), X1 \= (s(Y1)))],                 
    C3 = [X1 \= c],
    solve(C1,C2,C3),
    nl,
    C4 = [X2 = (s(a))],
    C5 = [forall(var(Y2), X2 \= (s(Y2)))],              
    C6 = [X2 \= c],
    solve(C4,C5,C6),
    nl,
    C7 = [X3 \= (s(a))],
    C8 = [X3 = (s(_))], 
    C9 = [X3 \= c],
    solve(C7,C8,C9),
    nl,
    C10 = [X4 \= (s(a))],
    C11 = [forall(var(Y4), X4 \= (s(Y4)))],              
    C12 = [X4 = c],
    solve(C10,C11,C12),
    nl,
    C13 = [X5 = (s(a))],
    C14 = [X5 = (s(_))],
    C15 = [X5 \= c],
    solve(C13,C14,C15),
    nl,
    C16 = [X6 = (s(a))],
    C17 = [forall(var(Y6), X6 \= (s(Y6)))],                     
    C18 = [X6 = c],
    solve(C16,C17,C18),
    nl,
    C19 = [X7 \= (s(a))],
    C20 = [X7 = (s(_))],
    C21 = [X7 = c],
    solve(C19,C20,C21),
    nl,
    C22 = [X8 = (s(a))],
    C23 = [X8 = (s(_))],                        
    C24 = [X8 = c],
    solve(C22,C23,C24).

solve(C1,C2,C3) :- 
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
    z3_push(N),
    Terms = [(a,0),(b,0),(c,0),(s,1)],
/* first constraint */
    z3_termconstr2smtlib(N,[],Terms,C1,VarsC1,TermsC1,C1smtlib2),
    z3_mk_term_type(N,TermsC1),
    (VarsC1=[] -> true ; z3_mk_term_vars(N,VarsC1)),
    z3_assert_term_string(N,C1smtlib2),
/* second constraint */                    
    z3_termconstr2smtlib(N,C1,TermsC1,C2,VarsC2,TermsC12,C2smtlib2),
    z3_mk_term_type(N,TermsC12),
    (VarsC2=[] -> true ; z3_mk_term_vars(N,VarsC2)),
    z3_assert_term_string(N,C2smtlib2),
/* third constraint */
    z3_termconstr2smtlib(N,(C1,C2),TermsC12,C3,VarsC3,TermsC123,C3smtlib2),
    z3_mk_term_type(N,TermsC123),
    (VarsC3=[] -> true ; z3_mk_term_vars(N,VarsC3)),
    z3_assert_term_string(N,C3smtlib2),
/* checking satisfiability */
    (z3_check(N) ->
        z3_print_model(N,_),
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
