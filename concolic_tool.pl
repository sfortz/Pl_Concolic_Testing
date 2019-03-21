%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  Concolic testing
%
%  Only tested in SWI Prolog, http://www.swi-prolog.org/
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(prolog_reader).
:- use_module(swiplz3).

:- dynamic filename/1.
:- dynamic depthk/1. %% max term depth
:- dynamic interactive/0. %% used to decide which clause of write_form to use

main :- catch(call_with_time_limit(1000000, mainT), X, error_process(X)).

  error_process(time_limit_exceeded) :- write('Timeout exceeded'), halt.
  error_process(X) :- write('Unknown Error' : X), nl, halt.


%% goal is a list of atoms, File is the input program
mainT :-
        CGoal = p(s(a)),
        GroundPos = [1],
        K = 2,
        File = 'examples/ex01.pl',
    functor(CGoal,P,N), % Concrete Goal
    functor(SGoal,P,N), % Symbolic Goal
    cleaning,
    assertz(depthk(K)),
    %
    assertz(filename(File)),
    prolog_reader:load_file(File),
    %
    assertz(constants(['o'])), %% 'o' is just some 'fresh' constant for the negatives cases to succeed..
    assertz(functions([])),
    %
    %% adding clause labels:
    assertz(labeled([])),
    copy_term(SGoal,Atom),
    assertz(not_labeled(Atom)),
    add_clause_labels,
    %
    %%initial info:
    ground_vars(SGoal,GroundPos,GroundVars),
    print('Initial goal:          '),println_atom(CGoal),
    print('Symbolic initial goal: '),println_atom(SGoal),
    print('Ground variables:      '),println_atom(GroundVars),
    %
    assertz(traces([])),
    assertz(testcases([])),
    assertz(pending_test_case(CGoal)),
    %
    concolic_testing(SGoal,GroundVars).

%% Extracting the (universal) type from the program. So far only atoms and functors are allowed.

:- dynamic constants/1.
:- dynamic functions/1.

esig_atom_list([]).
esig_atom_list([A|R]) :- esig_atom(A),esig_atom_list(R).

esig_atom(A) :- A=..[_|Args], esig_term_list(Args).

esig_term_list([]).
esig_term_list([T|R]) :- esig_term(T), esig_term_list(R).

esig_term(T) :- var(T),!.
esig_term(T) :- atom(T), !, update_constants(T).
esig_term(T) :- number(T), !, update_constants(T).
esig_term(T) :- compound(T), !, functor(T,F,N), update_functions(F,N), T=..[F|Args], esig_term_list(Args).
esig_term(_T) :- nl,format("ERROR. Type not supported.",[]), nl, halt.

update_constants(C) :- constants(CL), member(C,CL), !.
update_constants(C) :- constants(CL), retractall(constants(_)), !, assertz(constants([C|CL])).

update_functions(F,N) :- functions(FL), member(fun(F,N),FL), !.
update_functions(F,N) :- functions(FL), retractall(functions(_)), !, assertz(functions([fun(F,N)|FL])).


%%%
ground_vars(G,GPos,GVars) :-
  G=..[_|Vars],
  sort(GPos,SortedGPos),
  gvars(Vars,1,SortedGPos,GVars).

gvars(_,_N,[],[]) :- !.
gvars([V|RV],N,[P|RN],[V|GRV]) :-
  N = P,!, M is N+1, gvars(RV,M,RN,GRV).
gvars([_|RV],N,[P|RN],GRV) :-
  N \== P, M is N+1, gvars(RV,M,[P|RN],GRV).

/* adding clause labels: */

:- dynamic labeled/1.
:- dynamic not_labeled/1.
:- dynamic cl/2.  %% for programs

add_clause_labels :-
  \+ not_labeled(_), fail.
add_clause_labels :-
  retract(not_labeled(G)),
  functor(G,P,N),labeled(Labeled),  %\+ member(pred(P,N),Labeled),
  retractall(labeled(_)),assertz(labeled([pred(P,N)|Labeled])),!,
  findall(cl(G,Body),prolog_reader:get_clause_as_list(G,Body),L), acl(L,1,P,N),
  add_clause_labels.
add_clause_labels.

update_not_labeled(B) :-
  (not_labeled(C),B=@=C -> true
   ; assertz(not_labeled(B))).

acl([],_,_,_).
acl([cl(H,Body)|R],K,P,N) :-
  H =..[P|Args],
  esig_term_list(Args), %% for extracting types
  esig_atom_list(Body), %% for extracting types
  append(Args,[l(P,N,K)],NewArgs),
  H2=..[P|NewArgs],
  add_dump_parameters(Body,BodyR),
  assertz(cl(H2,BodyR)),
  K2 is K+1,
  acl(R,K2,P,N).

add_dump_parameters([],[]).
add_dump_parameters([A|R],[AA|RR]) :-
  functor(A,P,N), A=..[P|Args],
  % updating the pending predicates...
  functor(B,P,N),labeled(Labeled),
  (member(pred(P,N),Labeled) -> true
   ; update_not_labeled(B)),
  %
  append(Args,[_],NewArgs),
  AA=..[P|NewArgs],
  add_dump_parameters(R,RR).

:- dynamic traces/1.
:- dynamic testcases/1.
:- dynamic pending_test_case/1.

update_testcases(CGoal,Trace) :-
  testcases(Cases),
  (member(testcase(CGoal,Trace),Cases),! ; retractall(testcases(_)),assertz(testcases([testcase(CGoal,Trace)|Cases]))),!.

update_pending_test_cases([]) :- !.
update_pending_test_cases([C|R]) :-
  pending_test_case(D), C =@= D,!,   %% variants
  update_pending_test_cases(R).
update_pending_test_cases([C|R]) :-
  assertz(pending_test_case(C)),
  update_pending_test_cases(R).

add_dump_label(A,B) :-
  A=..[P|Args],
  append(Args,[_],NewArgs),
  B=..[P|NewArgs].

del_dump_label(A,B) :-
  A=..[P|Args],
  append(NewArgs,[_],Args),
  B=..[P|NewArgs].

%%%%%%%%%%%%%%%%%%%%%%%%%%
% Concolic testing... So it should be important! 
%%%%%%%%%%%%%%%%%%%%%%%%%%

concolic_testing(_,_) :- %% success !
  \+(pending_test_case(_)), !, %On vérifie qu'il n'y a plus de tests en attente.
  nl,println('Procedure complete!'),
  testcases(Cases),reverse(Cases,RCases),nl,print_testcases(RCases),!.

concolic_testing(SGoal,GroundVars) :-  %% new test case!
  copy_term(foo(SGoal,GroundVars),foo(SGoalCopy,GroundVarsCopy)),
  copy_term(foo(SGoal,GroundVars),foo(SGoalCopy2,GroundVarsCopy2)),
  retract(pending_test_case(CGoal)),!,
  copy_term(CGoal,CGoalCopy),
  add_dump_label(CGoalCopy,CGoalCopyLabel),
  add_dump_label(SGoalCopy,SGoalCopyLabel),
  println(eval([CGoalCopyLabel],[SGoalCopyLabel],GroundVarsCopy,[],Trace,[],Alts)),
  %
  eval([CGoalCopyLabel],[SGoalCopyLabel],GroundVarsCopy,[],Trace,[],Alts),!,
  %
  traces(Traces),
  (member(Trace,Traces) -> println(["HERE:", SGoal,GroundVars]) %concolic_testing(SGoal,GroundVars)
  ;
   update_testcases(CGoal,Trace),!,
   retractall(traces(_)),assertz(traces([Trace|Traces])), %% we updated the considered test cases
   print('Computed trace:          '),println(Trace),
   print('Considered alternatives: '),println_atom(Alts),
   %% get_new_trace(Trace,Alts,[Trace|Traces],Labels,Atom,NTrace), %% non-deterministic!
   findall(foo(Labels,Atom,NTrace,GroundVarsCopy2),
           (get_new_trace(Trace,Alts,[Trace|Traces],Labels,Atom,NTrace), Atom=SGoalCopy2,matches(Atom,Labels,GroundVarsCopy2)),
           List), %% now it is deterministic!
   print('new cases: '),println(List),
   %% updating new traces (yet to be done)
   %% get_traces(List,NewTraces),traces(Traces2),retractall(traces(_)),append(Traces2,NewTraces,Traces3),assertz(traces(Traces3)),
   %% bad idea: these are PREFIXES of new traces !!
   get_new_goals(List,NewGoals),
   update_pending_test_cases(NewGoals),
   concolic_testing(SGoal,GroundVars)
  ).
/*
concolic_testing(SGoal,GroundVars) :-
  concolic_testing(SGoal,GroundVars).*/

get_new_goals([],[]).
get_new_goals([foo(_,Atom,_,_)|R],[Atom|RR]) :- get_new_goals(R,RR).

get_new_trace(Trace,Alts,Traces,Labels,Atom,NewTrace) :-
  prefix(PTrace,Trace), length(PTrace,N),M is N+1,
  nth1(M,Alts,(A,L)),
  oset_power(L,LPower),
  print('All possibilities: '), println(LPower),
  print('Visited traces:    '),println(Traces),nl,
  member(LL,LPower),  %% nondeterministic!!
  append(PTrace,[LL],NewTrace),
  println(\+(member(NewTrace,Traces))),
  \+(member(NewTrace,Traces)),
  Labels=LL,Atom=A.

matches(A,LPos,G) :-
  % println(matches(A,LPos,G)),
  %% get first all matching clauses:
  copy_term(A,Acopy),add_dump_label(Acopy,AcopyLabel),
  findall(N,(cl(AcopyLabel,_),get_atom_label(AcopyLabel,N)),ListAll),
  subtract(ListAll,LPos,LNeg),
  %% get head of clauses LPos and LNeg:
  functor(A,P,Arity),
  get_heads(P,Arity,LPos,HPos),
  get_heads(P,Arity,LNeg,HNeg),
  matches_aux(A,HNeg,HPos,G).

get_heads(_P,_Arity,[],[]).
get_heads(P,Arity,[N|RN],[H2|RH]) :-
  functor(H,P,Arity),
  H=..[P|Args], append(Args,[N],Args2),
  NH=..[P|Args2],
  cl(NH,_),
  append(Args_,[_],Args2),
  H2=..[P|Args_],
  get_heads(P,Arity,RN,RH).

get_atom_label(A,Label) :- A=..[_F|Args], last(Args,Label).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% (not so) naive term generation
%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_terms([]).
generate_terms([X|XR]) :-
  depthk(K),
  term(K,X),
  generate_terms(XR).

term(_,_X).
term(_,C) :- constants(CL), member(C,CL).
term(K,T) :-
	K>0,
	functions(FL), member(fun(F,N),FL),
	J is K-1, term_list(J,N,[],Args),
	T=..[F|Args].

term_list(_K,0,Args,ArgsR) :- !, reverse(Args,ArgsR).
term_list(K,N,Args,Args_) :-
	term(K,A),
	M is N-1,
	term_list(K,M,[A|Args],Args_).

%%%%%%%%%%%
cleaning :-
  retractall(depthk(_)),
  retractall(filename(_)),
  retractall(labeled(_)),
  retractall(not_labeled(_)),
  retractall(cl(_,_)),
  retractall(pending_test_case(_)),
  retractall(constants(_)),
  retractall(functions(_)),
  retractall(traces(_)),
  retractall(testcases(_)).

change_label(Label,[_],[Label]) :- !.
change_label(Label,[X|R],[X|RR]) :- change_label(Label,R,RR).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% main transition rules

% success
eval([],[],_GroundTerms,Trace,TraceR,Alts,AltsR) :- 
  reverse(Trace,TraceR),reverse(Alts,AltsR).

% unfolding:
eval([A|RA],[B|RB],GroundTerms,Trace,NewTrace,Alts,NewAlts) :-
  copy_term(A,Acopy),copy_term(B,Bcopy),copy_term(B,Bcopy2),
  cl(A,Body), %% non-deterministic !!!!!!!!!!!
  get_atom_label(A,LabelA),
  findall(N,(cl(Acopy,_),get_atom_label(Acopy,N)),ListLabels),
  findall(K,(cl(Bcopy,_),get_atom_label(Bcopy,K)),ListAllLabels),
  append(Body,RA,CGoal),
  %% we require B to match only the same clauses as the concrete goal:
  B=..[P|Args], change_label(LabelA,Args,ArgsLabelA),NewB=..[P|ArgsLabelA],
  cl(NewB,BodyR), %% deterministic !!!!!!!!!!!
  append(BodyR,RB,SGoal),
  del_dump_label(Bcopy2,Bcopy2NoLabel),
  eval(CGoal,SGoal,GroundTerms,[ListLabels|Trace],NewTrace,[(Bcopy2NoLabel,ListAllLabels)|Alts],NewAlts).

% failing:
eval([A|_RA],[B|_RB],_GroundTerms,Trace,TraceR,Alts,NewAlts) :-
  \+(cl(A,_Body)),
  reverse([[]|Trace],TraceR),
  copy_term(B,Bcopy),copy_term(B,Bcopy2),
  findall(K,(cl(Bcopy,_),get_atom_label(Bcopy,K)),ListAllLabels),
  del_dump_label(Bcopy2,Bcopy2NoLabel),
  reverse([(Bcopy2NoLabel,ListAllLabels)|Alts],NewAlts).

% END main transition rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% some pretty-printing utilities..
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_testcases([]).
print_testcases([testcase(A,_)|R]) :-
  print_atom(A),nl,
  print_testcases(R).

println(X) :- print(X),nl.
print_atom(X) :- copy_term(X,C),numbervars(C,0,_),print(C).
println_atom(X) :- copy_term(X,C),numbervars(C,0,_),print(C),nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Sophie's stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

matches_aux(A,HNegs,HPos,VarsToBeGrounded) :-
        writeln(in-matches_aux(A,HNegs,HPos,VarsToBeGrounded)),
	%
	% check the preconditions:
	preconds(A,HNegs,HPos,VarsToBeGrounded),
	%
	compound_name_arguments(A,_,[Var]),
	get_constraints(Var,HNegs,HPos,Consts),
	solve(Consts,Mod,Sat),
	%
	(Sat -> 
	    split_model(Mod,ValsMod),
	    z3_to_term_list(ValsMod,Terms),
            append(VarsToBeGrounded, _, Terms) %% Verif que c'est OK si N > 2	
            ;
         nl,Sat
        ),	
        writeln(out-matches_aux(A,HNegs,HPos,VarsToBeGrounded)),
        nl,Sat.

        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Checking the preconditions for solving constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

preconds(A,HNegs,HPos,VarsToBeGrounded) :-
	forall(member(Hp,HPos),Hp=A),
	forall(member(Hn,HNegs),Hn=A),
	term_variables(A,VarsA), term_variables(HPos-HNegs,VarsHs),
	strict_empty_intersection(VarsA,VarsHs),
	strict_is_largely_incuded(VarsToBeGrounded,VarsA).
  
strict_mem(X,[Y|_]) :- X == Y, !.
strict_mem(X,[_|Ys]) :- strict_mem(X,Ys).
strict_not_mem(X,Xs) :-
	strict_not_mem_(Xs,X).

  strict_not_mem_([],_X).
  strict_not_mem_([Y|Zs],X) :-
	Y \== X,
	strict_not_mem_(Zs,X).

strict_empty_intersection([],_).
strict_empty_intersection([X|Xs],Vars) :-
	strict_not_mem(X,Vars),
	strict_empty_intersection(Xs,Vars).
	
strict_is_largely_incuded([],_).
strict_is_largely_incuded([X|Xs],Ys) :-
	strict_mem(X,Ys),
	strict_is_largely_incuded(Xs,Ys).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Writing the constraints in a correct form for the Z3 interface
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_constraints(A,HNegs,HPos,Constrs) :- 
        get_pos_consts(A,HPos,PosConsts),
        get_neg_consts(A,HNegs,NegConsts),
        append(PosConsts,NegConsts,Constrs).	

%%  GERER PLUSIEURS ARGUMENTS !!! %%
get_pos_consts(_,[],[]).
get_pos_consts(A,[H|T],Constrs) :-
        compound_name_arguments(H,_,[Args]),
        C1 = [[A = (Args)]],
        get_pos_consts(A,T,C2),
        append(C1,C2,Constrs).

%%  GERER PLUSIEURS ARGUMENTS !!! %%
get_neg_consts(_,[],[]).
get_neg_consts(A,[H|T],Constrs) :-
        compound_name_arguments(H,_,[Args]),
	copy_term(Args,CArgs),
	term_variables(CArgs,VCArgs),
        forall_terms(VCArgs,A,CArgs,C1),
        get_neg_consts(A,T,C2),
        append([[C1]],C2,Constrs).

forall_terms([],A,Args,Pred):- Pred = (A \= (Args)).   
forall_terms([H|T],A,Args,Pred) :-
        forall_terms(T,A,Args,Pred1),
        Pred = forall(var(H),Pred1). 
        
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Z3 solver
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Modif pour > 3 contraintes
solve([C1,C2,C3],Model,Sat) :- 
    copy_term((C1,C2,C3),(CC1,CC2,CC3)),
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config,
    z3_push(N),
    Terms = [(a,0),(b,0),(c,0),(s,1),(f,1)],
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
        z3_print_model(N,Model),
        get_context_vars(N,VVS),
        get_model_varT_eval(N,VVS,Values),
        term_variables([CC1,CC2,CC3],AllVars),
        AllVars=Values,
        Sat = true
    ;
        Sat = false
    ),
    z3_pop(N),
    z3_del_solver(N),
    z3_del_context(N).	
        
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Spliting a Z3 (string) model into Prolog terms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     
split_model(Model,Vals) :- 
    split_string(Model, "\n", "\s\t\n", L),
    split_affectation(L, Vals).    

split_affectation([],[]).      
split_affectation([H],[Affect]) :-
    split_string(H, "->", " ", [_,"",Affect]).         
split_affectation([H|T],Vals) :-
    split_affectation(T,Vals1),
    split_string(H, "->", " ", [_,"",Affect]),
    append([Affect],Vals1,Vals). 
    
       
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Transforming a list of strings representing a Z3 terms into a list 
%  of Prolog terms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
z3_to_term_list([],[]).
z3_to_term_list([T|Z3Terms],Terms) :-
        z3_to_term(T,Term),
        z3_to_term_list(Z3Terms,Terms_),
        append([Term],Terms_,Terms).

z3_to_term(Z3Str,Term) :-
        sub_string(Z3Str, 0, 1, _, "("),
        sub_string(Z3Str, _, 1, 0, ")"),
        sub_string(Z3Str, 1, _, 1, Str),!, 
        split_string(Str, " ", "", [Name|Args]),
        get_str_args(Args,StrArgs),
        string_concat(Name,"(",Str1),
        string_concat(Str1, StrArgs, Str2),
        string_concat(Str2, ")", Str3),
        term_string(Term, Str3).
z3_to_term(Z3Str,Term) :- term_string(Term, Z3Str),!. 

get_str_args([A],A).
get_str_args([A|Args],StrArgs) :- 
        get_str_args(Args,StrArgs_),
        string_concat(A,",",Str),
        string_concat(Str, StrArgs_, StrArgs).
     
