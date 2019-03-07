/* very simple example showing the functionality of the Z3 functions over terms and Predicates, with quantifiers*/

/*   From Example A */

:- use_module(swiplz3).

main :-
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
    C1 = [X \= (s(a))],
    C2 = [forall(var(Y), X \= (s(Y)))],                 
    C3 = [X \= c],
    mk_push_pop(N,C1,C2,C3),
    nl,
    C4 = [X = (s(a))],
    C5 = [forall(var(Y), X \= (s(Y)))],              
    C6 = [X \= c],
    mk_push_pop(N,C4,C5,C6),
    nl,
    C7 = [X \= (s(a))],
    C8 = [X = (s(Y))], 
    C9 = [X \= c],
    mk_push_pop(N,C7,C8,C9),
    nl,
    C10 = [X \= (s(a))],
    C11 = [forall(var(Y), X \= (s(Y)))],              
    C12 = [X = c],
    mk_push_pop(N,C10,C11,C12),
    nl,
    C13 = [X = (s(a))],
    C14 = [X = (s(Y))],
    C15 = [X \= c],
    mk_push_pop(N,C13,C14,C15),
    nl,
    C16 = [X = (s(a))],
    C17 = [forall(var(Y), X \= (s(Y)))],                     
    C18 = [X = c],
    mk_push_pop(N,C16,C17,C18),
    nl,
    C19 = [X \= (s(a))],
    C20 = [X = (s(Y))],
    C21 = [X = c],
    mk_push_pop(N,C19,C20,C21),
    nl,
    C22 = [X = (s(a))],
    C23 = [X = (s(Y))],                        
    C24 = [X = c],
    mk_push_pop(N,C22,C23,C24),
    z3_del_solver(N),
    z3_del_context(N).

mk_push_pop(N,C1,C2,C3) :- 
/* first constraint */
    z3_termconstr2smtlib(N,[],[],C1,VarsC1,TermsC1,C1smtlib2),
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
    z3_push(N),
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
    z3_pop(N).
