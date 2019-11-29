:- module(swiplz3, [get_varnames/2,z3_mk_config/0,z3_set_param_value/2,z3_mk_context/1,z3_mk_solver/1,z3_del_config/0,z3_del_solver/1,z3_del_context/1,z3_push/1,z3_pop/2,z3_assert_int_string/2,z3_assert_term_string/4,z3_intconstr2smtlib/5,z3_termconstr2smtlib/5,z3_check/1,z3_mk_int_vars/2,z3_mk_term_type/4,z3_mk_term_vars/2,z3_print_model/2,get_context_vars/2,get_model_var_eval/3,get_model_varT_eval/3]).

:- use_foreign_library(swiplz3).

z3_mk_context(N) :-
    z3_mk_new_context(N),
    retractall(var(N,_)).


retract_var(_,[]).
retract_var(N,[H|T]):-
    retract(var(N,H)),
    retract_var(N,T).

z3_pop(N,Vars):-
    retract_var(N,Vars),
    z3_pop(N).

:- dynamic var/2.

/*
   get_varnames/2 takes a list of variables produced by numbervars
   and returns a list of strings
*/
get_varnames([],[]).
get_varnames([V|VR],[VN|VRN]) :-
    write_to_chars(V,VN_),
    string_codes(VN,VN_),
    get_varnames(VR,VRN).

/*
    intconstr2smtlib/5 takes a context, the constraints so far, a new constraint
    (over integers) and returns a list of strings with the names of the new variables
    and a string with the SMTLIB2 representation "(assert ... )"
*/

z3_intconstr2smtlib(Context,OldC,C,NewVarsStr,SMT) :-
    copy_term((OldC,C),(OldCC,CC)),
    term_variables(OldCC,OldCCVars),
    term_variables(CC,CCVars),
    numbervars((OldCCVars,CCVars)),
    subtract(CCVars,OldCCVars,NewVars),
    get_varnames(NewVars,NewVarsStr),
    (NewVarsStr=[] -> true
    ;
      assert_vars(Context,NewVarsStr)
    ),
    constr2smt(CC,SMT_),
    string_codes(SMT,SMT_),!.

/*
    z3_assert_int_string/2 takes an SMT formula with integer variables and asserts it to a context
*/

z3_assert_int_string(N,SMT) :-
    string_codes(SMT,SMTC),
    string_codes("(assert ",S1),
    string_codes(")",S2),
    append(S1,SMTC,S3),
    append(S3,S2,SMTLIB2_),
    string_codes(SMTLIB2,SMTLIB2_),
    z3_assert_int_string_(N,SMTLIB2).


/*
    z3_assert_term_string/2 takes an SMT formula with term variables and asserts it to a context
*/

z3_assert_term_string(N,SMT,Int,List) :-
    string_codes(SMT,SMTC),
    string_codes("(assert ",S1),
    string_codes(")",S2),
    append(S1,SMTC,S3),
    append(S3,S2,SMTLIB2_),
    string_codes(SMTLIB2,SMTLIB2_),
    z3_assert_term_string_(N,SMTLIB2,Int,List).


assert_vars(_,[]).
assert_vars(N,[X|R]) :-
    assertz(var(N,X)),
    assert_vars(N,R).

assert_terms(_,[]).
assert_terms(N,[(X,Y)|R]) :-
    assertz(term(N,X,Y)),
    assert_terms(N,R).

get_context_vars(N,VVS) :-
    findall(VV,var(N,VV),VVS).

get_model_var_eval(_,[],[]) :- !.
get_model_var_eval(N,[Var|R],[Val|RR]) :-
    z3_get_model_intvar_eval(N,Var,Val),
    get_model_var_eval(N,R,RR).

get_model_varT_eval(_,[],[]) :- !.
get_model_varT_eval(N,[Var|R],[Val|RR]) :-
    z3_get_model_termvar_eval(N,Var,Val),
    get_model_varT_eval(N,R,RR).

var_decl([],[]).
var_decl([V|R],SS) :-
    string_codes("(declare-const ",S1),
    write_to_chars(V,Var),
    append(S1,Var,S2),
    string_codes(" Int) ",S3),
    append(S2,S3,S),
    var_decl(R,RS),
    append(S,RS,SS).

/*
    constr2smt/2 translates a list of simple integer constraints (>,<,=,\=,>=,=< and +,-,*,div,mod,rem)
    to a list of codes representing an SMTLIB2 string
*/

constr2smt([C],SMT) :-
    !,con2smt(C,SMT).
constr2smt(List,SMT) :-
    con2smt_list(List,SMT_),
    string_codes("(and ",S1),
    append(S1,SMT_,S2),
    string_codes(")",S3),
    append(S2,S3,SMT).

con2smt_list([C],SMT) :-
    !,con2smt(C,SMT).
con2smt_list([C|R],SMT) :-
    con2smt(C,SMT1),
    con2smt_list(R,SMTR),
    string_codes(" ",Blank),
    append(SMT1,Blank,S),
    append(S,SMTR,SMT).

/* expression rooted by a binary operator */
con2smt(T,SMT) :-
    functor(T,F,2),!,transf(F,S1,S2),
    arg(1,T,Arg1),con2smt(Arg1,SMT1),
    arg(2,T,Arg2),con2smt(Arg2,SMT2),
    string_codes(" ",Blank),
    append(S1,SMT1,S),append(S,Blank,S_),
    append(S_,SMT2,S__),append(S__,S2,SMT).

/* negative number */
con2smt(T,SMT) :-
    functor(T,-,1),!,transf(-,S1,S2),
    arg(1,T,Arg1),con2smt(Arg1,SMT1),
    append(S1,SMT1,S),append(S,S2,SMT).

/* integer */
con2smt(T,SMT) :-
    integer(T),!,
    atom_codes(T,SMT).

/* variable */
con2smt(T,SMT) :-
    functor(T,'$VAR',1),!,
    write_to_chars(T,SMT).

/* unsupported term */
con2smt(T,_SMT) :-
    throw(unsupported_constraint(T)).

/* binary operators */
transf(>,S1,S2) :- string_codes("(> ",S1),string_codes(")",S2).
transf(<,S1,S2) :- string_codes("(< ",S1),string_codes(")",S2).
transf(>=,S1,S2) :- string_codes("(>= ",S1),string_codes(")",S2).
transf(=<,S1,S2) :- string_codes("(<= ",S1),string_codes(")",S2).
transf(=,S1,S2) :- string_codes("(= ",S1),string_codes(")",S2).
transf(\=,S1,S2) :- string_codes("(not (= ",S1),string_codes("))",S2).
transf(*,S1,S2) :- string_codes("(* ",S1),string_codes(")",S2).
transf(+,S1,S2) :- string_codes("(+ ",S1),string_codes(")",S2).
transf(-,S1,S2) :- string_codes("(- ",S1),string_codes(")",S2).
transf(div,S1,S2) :- string_codes("(div ",S1),string_codes(")",S2).
transf(mod,S1,S2) :- string_codes("(mod ",S1),string_codes(")",S2).
transf(rem,S1,S2) :- string_codes("(rem ",S1),string_codes(")",S2).

/* unary operators */
transf(-,S1,S2) :- string_codes("(- ",S1),string_codes(")",S2).

/*
    z3_termconstr2smtlib/5 takes a context, the constraints so far, a
    new constraint (over terms and predicates) and returns a list of strings
    with the names of the new variables and a string with the SMTLIB2
    representation "(assert ... )"
*/
z3_termconstr2smtlib(Context,OldC,C,NewVarsStr,SMT) :-

    term_variables(OldC,OldCVars),
    term_variables(C,CVars),

    subtract(CVars,OldCVars,NewVars),
    copy_term((C,NewVars),(CC,CNewVars)),
    numbervars(CNewVars),

    get_varnames(CNewVars,NewVarsStr),
    (NewVarsStr=[] -> true
    ;
      assert_vars(Context,NewVarsStr)
    ),
    constrP2smt(CC,_,SMT_),
    string_codes(SMT,SMT_),!.

/*
    constrP2smt/2 translates a list of simple constraints (=,\=) over predicates
    to a list of codes representing an SMTLIB2 string
*/

constrP2smt([C],LT,SMT) :-
    !,conP2smt(C,LT,SMT).
constrP2smt(List,LT,SMT) :-
    conP2smt_list(List,LT,SMT_),
    string_codes("(and ",S1),
    append(S1,SMT_,S2),
    string_codes(")",S3),
    append(S2,S3,SMT).

conP2smt_list([C],LT,SMT) :-
    !,conP2smt(C,LT,SMT).
conP2smt_list([C|R],LT,SMT) :-
    conP2smt(C,LT1,SMT1),
    conP2smt_list(R,LT2,SMT2),
    string_codes(" ",Blank),
    append(SMT1,Blank,S),
    append(LT1,LT2,LT),
    append(S,SMT2,SMT).

/* expression rooted by a binary operator */
conP2smt(T,LT,SMT) :-
    functor(T,F,2),
    transfT(F,S1,S2),!,
    arg(1,T,Arg1),conP2smt(Arg1,LT1,SMT1),
    arg(2,T,Arg2),conP2smt(Arg2,LT2,SMT2),
    string_codes(" ",Blank),
    append(S1,SMT1,S),append(S,Blank,S_),
    append(S_,SMT2,S__),append(S__,S2,SMT),
    append(LT1,LT2,LT).

/* var declaration */
conP2smt(T,LT,SMT) :-
    functor(T,var,1),!,transfT(var,S1,S2),
    arg(1,T,Arg1),conP2smt(Arg1,LT,SMT1),
    append(S1,SMT1,S),append(S,S2,SMT).

/* variable */
conP2smt(T,LT,SMT) :-
    functor(T,'$VAR',1),!,
    LT=[],
    write_to_chars(T,SMT).

/* integer */
conP2smt(T,LT,SMT) :-
    integer(T),!,
    LT=[],
    atom_codes(T,SMT_),
    string_codes("(int ",S1),
    string_codes(")",S2),
    append(S1,SMT_,S),append(S,S2,SMT).

/* list */
conP2smt(T,LT,SMT) :-
    functor(T,'[|]',2), !,
    get_args_list(T,1,LTH,Head),
    get_args_list(T,2,LTT,Tail),
    append(LTH,LTT,LT),
    string_codes(Head,SMT1), % string E
    string_codes(Tail,SMT2), % string F
    string_codes("(cons (insert ",S1),
    string_codes(" (list ",S2),
    string_codes(")))",S3),
    append(S1,SMT1,S),append(S,S2,S_),
    append(S_,SMT2,S__),append(S__,S3,SMT).

/* term/0 */
conP2smt(T,LT,SMT) :-
    functor(T,N,0),!,
    LT=[(N,0)],
    write_to_chars(N,SMT).

/* term/Arity */
conP2smt(T,LT,SMT) :-
    functor(T,N,Arity), !,
    write_to_chars(N,SMT1),
    list_of_args(T,Arity, LT_, SMT2),
    string_codes(" ",Blank),
    string_codes("(",S1),string_codes(")",S2),
    append(S1,SMT1,S),append(S,Blank,SBlank),
    append(SBlank,SMT2,S_),append(S_,S2,SMT),
    LT = [(N,Arity)|LT_].

/* unsupported term */
conP2smt(T,LT,_SMT) :-
    LT=[],
    throw(unsupported_constraint(T)).


/* Take the Nth arguments of the functor T (useful for lists) */
get_args_list(T,N,LT,SMT) :-
    arg(N,T,A),
    conP2smt(A,LT,SMT).

/* Create the list of the arguments of the functor T */
list_of_args(T,1,LT,Args):-
    arg(1,T,A),
    conP2smt(A,LT,Args).

list_of_args(T,I,LT,Args) :-
    I_ is (I - 1),
    list_of_args(T,I_,LT1,Args_),
    arg(I,T,A),
    conP2smt(A,LT2,SMT),
    string_codes(" ",Blank),
    append(Args_,Blank,SBlank),append(SBlank,SMT,Args),
    append(LT1,LT2,LT).

/* binary operators */
/*
transfT(>,S1,S2) :- string_codes("(> ",S1),string_codes(")",S2).
transfT(<,S1,S2) :- string_codes("(< ",S1),string_codes(")",S2).
transfT(>=,S1,S2) :- string_codes("(>= ",S1),string_codes(")",S2).
transfT(=<,S1,S2) :- string_codes("(<= ",S1),string_codes(")",S2).
transfT(*,S1,S2) :- string_codes("(* ",S1),string_codes(")",S2).
transfT(+,S1,S2) :- string_codes("(+ ",S1),string_codes(")",S2).
transfT(-,S1,S2) :- string_codes("(- ",S1),string_codes(")",S2).
transfT(div,S1,S2) :- string_codes("(div ",S1),string_codes(")",S2).
transfT(mod,S1,S2) :- string_codes("(mod ",S1),string_codes(")",S2).
transfT(rem,S1,S2) :- string_codes("(rem ",S1),string_codes(")",S2).*/
transfT(=,S1,S2) :- string_codes("(= ",S1),string_codes(")",S2).
transfT(\=,S1,S2) :- string_codes("(not (= ",S1),string_codes("))",S2).
transfT(forall,S1,S2) :- string_codes("(forall ",S1),string_codes(")",S2).
transfT(exists,S1,S2) :- string_codes("(exists ",S1),string_codes(")",S2).

/* unary operators */
transfT(var,S1,S2) :- string_codes("((",S1),string_codes(" Term))",S2).
