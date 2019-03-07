/* very simple example showing the functionality of the Z3 functions over terms and Predicates, with quantifiers*/

/*   From Example A */

:- use_module(swiplz3).

main :-
    C1 = [X3 \= (s(Y))],
    ici(C1).
    /*
    C7 = [X3 \= (s(a))],
    C8 = [X3 = (s(_))], 
    C9 = [X3 \= c],
    solve(C7,C8,C9),
    nl.*/

solve(C1,C2,C3) :- 
    copy_term((C1,C2,C3),(CC1,CC2,CC3)),
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
    z3_push(N),
    Terms = [(a,0),(b,0),(c,0),(s,1)],
/* first constraint */
    z3_termconstr2smtlib(N,[],Terms,CC1,VarsC1,TermsC1,C1smtlib2),
    z3_mk_term_type(N,TermsC1),
    (VarsC1=[] -> true ; z3_mk_term_vars(N,VarsC1)),
    z3_assert_term_string(N,C1smtlib2),
/* second constraint */                    
    z3_termconstr2smtlib(N,CC1,TermsC1,CC2,VarsC2,TermsC12,C2smtlib2),
    z3_mk_term_type(N,TermsC12),
    (VarsC2=[] -> true ; z3_mk_term_vars(N,VarsC2)),
    z3_assert_term_string(N,C2smtlib2),
/* third constraint */
    z3_termconstr2smtlib(N,(CC1,CC2),TermsC12,CC3,VarsC3,TermsC123,C3smtlib2),
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
        term_variables([CC1,CC2,CC3],AllVars),
        AllVars=Values,
        format("Solved formulas: "),print([CC1,CC2,CC3]),
        nl
    ;
        true
    ),
    z3_pop(N),
    z3_del_solver(N),
    z3_del_context(N),
    print("Old Formulas:"), nl,
    print([C1,C2,C3]),nl,
    print("Variables C8:"),nl,
    test(C2,_),nl.
    
    
    
test(Vars,VarsStr) :-   
    print("Line:"),print(Vars),nl,
    numbervars(Vars), 
    get_varnames(Vars,VarsStr).
    
ici(C) :-
    T =[X3 \= (s(Y))],
    /* Getting the names of the variables into a list of strings. 
       Should be used only in the function where the variables are definied.
       Variables are listed by order of appearance. */
    numbervars(T), 
    const2vars_list(T,LV),
    vars2str(LV,SMT),
    /* Variables names are now recorded into SMT.*/
    print("SMT = "),
    print(SMT).
    
/* Takes a list of char codes and returns a list of the corresponding strings. */
vars2str([V],[SMT]):-
    string_codes(SMT,V).
vars2str([LV|R],SMT):-
    vars2str(R,SMT2),
    string_codes(SMT1,LV),
    append([SMT1],SMT2,SMT).
     
/* Transforms a list of constraints into a list of strings, representing the variables. Must be called after "numbervars". */
const2vars_list([C],LV) :-
    !,const2vars(C,LV).
const2vars_list([C|R],LV) :-
    const2vars(C,LV1),
    const2vars(R,LV2),
    append(LV1,LV2,LV).  
 
/* variable */
const2vars(T,LV) :-   
    functor(T,'$VAR',1),!,
    write_to_chars(T,SMT),
    LV=[SMT].    

/* term/0 */
const2vars(T,LV) :- 
    functor(T,_,0),!,
    LV=[].
        
/* term/Arity */     
const2vars(T,LV) :-
    functor(T,_,Arity), !,
    vars_in_args(T,Arity,LV).
    
/* Create the list of variables in the arguments of the functor T */  
vars_in_args(T,1,LV):-
    arg(1,T,A),
    const2vars(A,LV).
vars_in_args(T,I,LV) :- 
    I_ is (I - 1),
    vars_in_args(T,I_,LV1),
    arg(I,T,A),
    const2vars(A,LV2),
    append(LV1,LV2,LV).        
