%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  Concolic testing
%
%  Only tested in SWI Prolog, http://www.swi-prolog.org/
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(lists)).
:- use_module(library(dialect/hprolog)).
%:- use_module(library(dialect/sicstus)).
:- use_module(prolog_reader).

:- use_module(library(charsio)).

%:- dynamic rr/2.  %% residual rule
:- dynamic filename/1.
:- dynamic initial_goal/1.

%:- dynamic global_query/1.  %% processed global query (without ground positions)
%:- dynamic q/2.             %% unfolded query (Query,GroundPos)

:- dynamic cli_option/1.
:- dynamic cli_initial_cg/1.
:- dynamic cli_initial_sg/1.
:- dynamic cli_initial_ground/1.
:- dynamic cli_initial_depth/1.
:- dynamic cli_initial_timeout/1.
:- dynamic cli_initial_trace/0.
:- dynamic cli_initial_file/1.

:- dynamic depthk/1. %% max term depth


main :-
    prolog_flag(argv,ArgV),
    get_options(ArgV,Options,RemArgV), !,
    (member(verbose,Options) -> (assert_verbose, print(Options),nl)
      ; (member(very_verbose,Options) -> (assert_verbose,assert_very_verbose, print(Options),nl) ; true)),
    ((member(cg(CG),Options),convert_entry_to_term(CG,CGT),assert(cli_initial_cg(CGT)),fail)
      ; true),
    ((member(sg(SG),Options),convert_entry_to_term(SG,SGT),assert(cli_initial_sg(SGT)),fail)
      ; true),
    ((member(depth(K),Options),convert_entry_to_term(K,KT),assert(cli_initial_depth(KT)),fail)
      ; true),
    ((member(timeout(K),Options),convert_entry_to_term(K,KT),assert(cli_initial_timeout(KT)),fail)
      ; true),
    (member(with_trace,Options) -> assert(cli_initial_trace); true),
    ((member(ground(Ground),Options),convert_entry_to_term(Ground,GroundT),assert(cli_initial_ground(GroundT)),fail)
      ; true),
    (member(interactive,Options) -> assert(interactive) ; true),
    ((member(help,Options) ; RemArgV=[]) -> print_help ; true),
    ((member(file(FILE),Options),assert(cli_initial_file(FILE)),fail)
      ; true),
    main_cli.

:- dynamic interactive/0. %% used to decide which clause of write_form to use

main_cli :-
  cli_initial_cg(Q),
  %cli_initial_sg(K),
  cli_initial_ground(NR),
  cli_initial_depth(K),
  cli_initial_timeout(T),
  cli_initial_file(File),
  !,
  (cli_initial_trace -> main(Q,NR,K,T,true,File) ; main(Q,NR,K,T,false,File)).

:- dynamic with_trace/0.

  main(Q,NR,K,T,Trace,File) :-
    retractall(with_trace), 
    (Trace -> assert(with_trace); true),
    catch(call_with_time_limit(T, mainT(Q,NR,K,File)), X, error_process(X)).


  error_process(time_limit_exceeded) :- write('Timeout exceeded'), nl, print_test_cases, halt.
  error_process(X) :- write('Unknown Error' : X), nl, halt.

%% This one prints both test cases and pending test cases:
print_test_cases :- nl,println('Time limit exceeded!'),
                    testcases(Cases),  %% processed test cases
                    reverse(Cases,CasesR),
                    nl, println('Processed test cases: '),
                    print_testcases(CasesR),
                    nl, println('Pending test cases: '),
                    findall(Goal,pending_test_case(Goal),PendingCases),  %% pensing tests cases
                    list_to_set(PendingCases,PendingCasesL),  %% this is just to remove duplicates
                    reverse(PendingCasesL,PendingCasesLR),nl,print_testcases_2(PendingCasesLR),!.
      


get_options([],Rec,Rem) :- !,Rec=[],Rem=[].
get_options(Inputs,RecognisedOptions,RemOptions) :-
   (recognise_option(Inputs,Flag,RemInputs)
     -> (RecognisedOptions = [Flag|RecO2],
         assert(cli_option(Flag)), %%print(Flag),nl,
         RemO2 = RemOptions)
     ;  (Inputs = [H|RemInputs], RemOptions = [H|RemO2], RecO2 = RecognisedOptions)
   ),
   get_options(RemInputs,RecO2,RemO2).

recognise_option(Inputs,Flag,RemInputs) :-
   recognised_option(Heads,Flag),
   append(Heads,RemInputs,Inputs).

recognised_option(['-cg',Q],cg(Q)).
recognised_option(['-sg',Q],sg(Q)).
recognised_option(['-ground',G],ground(G)).
recognised_option(['-depth',Depth],depth(Depth)).
recognised_option(['-timeout',Depth],timeout(Depth)).
recognised_option(['-trace'],with_trace).
recognised_option(['-interactive'],interactive).
recognised_option(['-file',NT],file(NT)).
recognised_option(['-v'],verbose).
recognised_option(['-verbose'],verbose).
recognised_option(['-vv'],very_verbose).
recognised_option(['-very_verbose'],very_verbose).
recognised_option(['-help'],help).

%:- use_module(library(codesio)).

convert_entry_to_term(CLIGOAL,Term) :-
   on_exception(Exception,
      (atom_codes(CLIGOAL,Codes),
       read_from_chars(Codes,Term)),
      (nl,print('### Illegal Command-Line Goal: "'), print(CLIGOAL),print('"'),nl,
       format("### Use following format: \"Goal.\"~n",[]),
       print('### Exception: '), print(Exception),nl,
       halt)
     ).


print_help.

assert_interactive :- assert(interactive).

%% goal is a list of atoms, File is the input program
mainT(CGoal,GroundPos,K,File) :-
    functor(CGoal,P,N),
    functor(SGoal,P,N),
    cleaning,
    %% comment the next three asserts for the cgi-bin version:
    %assert_very_verbose,
    %assert_verbose,
    %assert_interactive,
    %
    assert(depthk(K)),
    %
    assert(filename(File)),
    vprintln(load_file(File)),
    flush_output(user),
    prolog_reader:load_file(File),
    vprintln(finished_loading_file(File)),
    flush_output(user),
    %
    assertz(constants(['o'])), %% 'o' is just some 'fresh' constant for the negatives cases to succeed..
    assertz(functions([])),
    %
    %% adding clause labels:
    assert(labeled([])),
    copy_term(SGoal,Atom),
    assert(not_labeled(Atom)),
    add_clause_labels,
    %
    %%initial info:
    ground_vars(SGoal,GroundPos,GroundVars),
    vprint('Initial goal:          '),vprintln_atom(CGoal),
    vprint('Symbolic initial goal: '),vprintln_atom(SGoal),
    vprint('Ground variables:      '),vprintln_atom(GroundVars),
    %
    assert(traces([])),
    assert(testcases([])),
    assert(pending_test_case(CGoal)),
    %%SGoal =.. [P|Args], append(Args,[_],NewArgs), SGoal2=..[P|NewArgs],
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
  retractall(labeled(_)),assert(labeled([pred(P,N)|Labeled])),!,
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

/*
%% this first one is just for debugging:
concolic_testing(Goals,SGoal,GroundVars) :-
  println(concolic_testing(Goals,SGoal,GroundVars)),fail.
*/

concolic_testing(_,_) :- %% success !
  \+(pending_test_case(_)), !,
  nl,println('Procedure complete!'),
  testcases(Cases),reverse(Cases,RCases),nl,print_testcases(RCases),!.

/*
concolic_testing(SGoal,GroundVars) :-  %% test case already considered..
  copy_term(foo(SGoal,GroundVars),foo(SGoalCopy,GroundVarsCopy)),
  retract(pending_test_case(CGoal)),
  eval(CGoal,SGoalCopy,GroundVarsCopy,[],Trace,[],_Alts),
  traces(Traces), member(Trace,Traces),!,
  concolic_testing(SGoal,GroundVars).
*/

concolic_testing(SGoal,GroundVars) :-  %% new test case!
  traces(Traces),copy_term(foo(SGoal,GroundVars),foo(SGoalCopy,GroundVarsCopy)),
  copy_term(foo(SGoal,GroundVars),foo(SGoalCopy2,GroundVarsCopy2)),
  retract(pending_test_case(CGoal)),!,
  copy_term(CGoal,CGoalCopy),
  add_dump_label(CGoalCopy,CGoalCopyLabel),
  add_dump_label(SGoalCopy,SGoalCopyLabel),
  vprintln(eval([CGoalCopyLabel],[SGoalCopyLabel],GroundVarsCopy,[],Trace,[],Alts)),
  %
  eval([CGoalCopyLabel],[SGoalCopyLabel],GroundVarsCopy,[],Trace,[],Alts),!,
  %
  traces(Traces),
  (member(Trace,Traces) -> concolic_testing(SGoal,GroundVars)
  ;
   update_testcases(CGoal,Trace),!,
   retractall(traces(_)),assertz(traces([Trace|Traces])), %% we updated the considered test cases
   vprint('Computed trace:          '),vprintln(Trace),
   vprint('Considered alternatives: '),vprintln_atom(Alts),
   %% get_new_trace(Trace,Alts,[Trace|Traces],Labels,Atom,NTrace), %% non-deterministic!
   findall(foo(Labels,Atom,NTrace,GroundVarsCopy2),
           (get_new_trace(Trace,Alts,[Trace|Traces],Labels,Atom,NTrace),Atom=SGoalCopy2,matches(Atom,Labels,GroundVarsCopy2)),
           List), %% now it is deterministic!
   vprint('new cases: '),vprintln(List),
   %% updating new traces (yet to be done)
   %% get_traces(List,NewTraces),traces(Traces2),retractall(traces(_)),append(Traces2,NewTraces,Traces3),assertz(traces(Traces3)),
   %% bad idea: these are PREFIXES of new traces !!
   get_new_goals(List,NewGoals),
   update_pending_test_cases(NewGoals),
   concolic_testing(SGoal,GroundVars)
  ).

concolic_testing(SGoal,GroundVars) :-
  concolic_testing(SGoal,GroundVars).

/*
concolic_testing([],_,_) :- %% success !
  nl,println('Full coverage!'),
  testcases(Cases),reverse(Cases,RCases),nl,print_testcases(RCases),!.
concolic_testing([CGoal|R],SGoal,GroundVars) :-  %% test case already considered..
  eval(CGoal,SGoal,GroundVars,[],Trace,[],_Alts),
  traces(Traces), member(Trace,Traces),!,
  concolic_testing(R,SGoal,GroundVars).
concolic_testing([CGoal|R],SGoal,GroundVars) :-  %% new test case!
  traces(Traces),copy_term(foo(SGoal,GroundVars),foo(SGoalCopy,GroundVarsCopy)),
  copy_term(foo(SGoal,GroundVars),foo(SGoalCopy2,GroundVarsCopy2)),
  copy_term(CGoal,CGoalCopy),
  vprintln(eval(CGoalCopy,SGoalCopy,GroundVarsCopy,[],Trace,[],Alts)),
  %
  eval(CGoalCopy,SGoalCopy,GroundVarsCopy,[],Trace,[],Alts),!,
  %
  update_testcases(CGoal,Trace),!,
  retractall(traces(_)),assertz(traces([Trace|Traces])), %% we updated the considered test cases
  vprint('Computed trace:          '),vprintln(Trace),
  vprint('Considered alternatives: '),vprintln(Alts),
  %% get_new_trace(Trace,Alts,[Trace|Traces],Labels,Atom,NTrace), %% non-deterministic!
  findall(foo(Labels,Atom,NTrace,GroundVarsCopy2),
          (get_new_trace(Trace,Alts,[Trace|Traces],Labels,Atom,NTrace),[Atom]=SGoalCopy2,matches(Atom,Labels,GroundVarsCopy2)),
          List), %% now it is deterministic!
  vprint('new cases: '),vprintln(List),
  %% updating new traces (yet to be done)
  %% get_traces(List,NewTraces),traces(Traces2),retractall(traces(_)),append(Traces2,NewTraces,Traces3),assertz(traces(Traces3)),
  %% bad idea: these are PREFIXES of new traces !!
  get_new_goals(List,NewGoals),
  append(R,NewGoals,NewGoals2),
  %%println(concolic_testing(NewGoals2,SGoal,GroundVars)),
  concolic_testing(NewGoals2,SGoal,GroundVars).
*/
/*
concolic_testing(_,_,_) :- %% success !
  nl,println('Full coverage!'),
  testcases(Cases),reverse(Cases,RCases),nl,print_testcases(RCases),!.
*/

print_testcases([]).
print_testcases([testcase(A,Trace)|R]) :-
  print_atom(A),
  (with_trace -> print(' with trace '),print_trace(Trace) ; nl),
  print_testcases(R).

print_trace([]) :- nl.
print_trace([S|R]) :- print('{'),print_trace_step(S),print('} '),print_trace(R).

print_trace_step([]).
print_trace_step([l(P,N,K)]) :- !,print('('),print(P),print('/'),print(N),print(','),print(K),print(')').
print_trace_step([l(P,N,K)|R]) :- print('('),print(P),print('/'),print(N),print(','),print(K),print('),'),print_trace_step(R).

print_testcases_2([]).
print_testcases_2([A|R]) :-
  print_atom(A),nl,
  print_testcases_2(R).

get_new_goals([],[]).
get_new_goals([foo(_,Atom,_,_)|R],[Atom|RR]) :- get_new_goals(R,RR).

get_new_trace(Trace,Alts,Traces,Labels,Atom,NewTrace) :-
  prefix(PTrace,Trace), length(PTrace,N),M is N+1,
  nth1(M,Alts,(A,L)),
  oset_power(L,LPower),
  vprint('All possibilities: '), vprintln(LPower),
  vprint('Visited traces:    '),vprintln(Traces),
  member(LL,LPower),  %% nondeterministic!!
  append(PTrace,[LL],NewTrace),
  vprintln(\+(member(NewTrace,Traces))),
  \+(member(NewTrace,Traces)),
  %vprintln('New trace to consider: '), vprintln(NewTrace),
  Labels=LL,Atom=A.

matches(A,LPos,G) :-
  % println(matches(A,LPos,G)),
  %% get first all matching clauses:
  copy_term(A,Acopy),add_dump_label(Acopy,AcopyLabel),
  %%findall(N,(prolog_reader:get_clause_as_list(Acopy,_),get_clause_number(Acopy,N)),ListAll),
  findall(N,(cl(AcopyLabel,_),get_atom_label(AcopyLabel,N)),ListAll),
  subtract(ListAll,LPos,LNeg),
  %% get head of clauses LPos and LNeg:
  functor(A,P,Arity),
  get_heads(P,Arity,LPos,HPos),
  get_heads(P,Arity,LNeg,HNeg),
  %nl,(   (matches_aux_ori(A,HNeg,HPos,G),fail); matches_aux(A,HNeg,HPos,G)).
  matches_aux(A,HNeg,HPos,G).



matches_aux_ori(A,HNeg,HPos,G) :-
  %writeln(in-matches_aux_ori(A,HNeg,HPos,G)),
  A=..[_P|R], %% we do not want to instantiate the clause numbers!
  term_variables(R,Vars),
  generate_terms(Vars),
  %println(generate_terms(Vars)),
  matches_neg(A,HNeg,HPos,G),
  %println(matches_neg(A,HNeg,HPos,G)),
  %writeln(out-matches_aux_ori(A,HNeg,HPos,G)),
  true.

matches_neg(A,[],HPos,G) :-
  matches_pos(A,HPos,G).
matches_neg(A,[H|HR],HPos,G) :-
  \+ unifiable(A,H,_),
  matches_neg(A,HR,HPos,G).

matches_pos(_A,[],G) :- ground(G),!.
matches_pos(A,[H|HR],G) :-
  unifiable(A,H,_),
  matches_pos(A,HR,G).


get_heads(_P,_Arity,[],[]).
get_heads(P,Arity,[N|RN],[H2|RH]) :-
  functor(H,P,Arity),
  %H=..[P,N|_],
  %%prolog_reader:get_clause_as_list(H,_),
  H=..[P|Args], append(Args,[N],Args2),
  NH=..[P|Args2],
  cl(NH,_),
  append(Args_,[_],Args2),
  %append(Args_,[_],Args__),
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
%  retractall(cli_option(_)),
  retractall(cli_initial_cg(_)),
  retractall(cli_initial_sg(_)),
  retractall(cli_initial_ground(_)),
  retractall(cli_initial_depth(_)),
  retractall(cli_initial_depth(_)),
  retractall(cli_initial_trace),
  retractall(cli_initial_timeout(_)),
  %retractall(with_trace),
  retractall(depthk(_)),
  retractall(cli_initial_file(_)),
%  retractall(interactive),
  retractall(verbose),
  retractall(very_verbose),
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% main transition rules

% just for debugging
eval(CGoal,SGoal,GroundTerms,Trace,Trace_,Alts,Alts_) :-
  vprintln_atom(eval(CGoal,SGoal,GroundTerms,Trace,Trace_,Alts,Alts_)),
  fail.

% success
eval([],[],_GroundTerms,Trace,TraceR,Alts,AltsR) :- reverse(Trace,TraceR),reverse(Alts,AltsR).

% unfolding:
eval([A|RA],[B|RB],GroundTerms,Trace,NewTrace,Alts,NewAlts) :-
  copy_term(A,Acopy),copy_term(B,Bcopy),copy_term(B,Bcopy2),
  %%prolog_reader:get_clause_as_list(A,Body), %% non-deterministic !!!!!!!!!!!
  cl(A,Body), %% non-deterministic !!!!!!!!!!!
  get_atom_label(A,LabelA),
  %%findall(N,(prolog_reader:get_clause_as_list(Acopy,_),get_clause_label(Acopy,N)),ListLabels),
  %%findall(K,(prolog_reader:get_clause_as_list(Bcopy,_),get_clause_label(Bcopy,K)),ListAllLabels),
  findall(N,(cl(Acopy,_),get_atom_label(Acopy,N)),ListLabels),
  findall(K,(cl(Bcopy,_),get_atom_label(Bcopy,K)),ListAllLabels),
  append(Body,RA,CGoal),
  %% we require B to match only the same clauses as the concrete goal:
  B=..[P|Args], change_label(LabelA,Args,ArgsLabelA),NewB=..[P|ArgsLabelA],
  %%B=..[P,_LabelB|R], NewB=..[P,LabelA|R],
  %%prolog_reader:get_clause_as_list(NewB,BodyR), %% deterministic !!!!!!!!!!!
  cl(NewB,BodyR), %% deterministic !!!!!!!!!!!
  append(BodyR,RB,SGoal),
  del_dump_label(Bcopy2,Bcopy2NoLabel),
  eval(CGoal,SGoal,GroundTerms,[ListLabels|Trace],NewTrace,[(Bcopy2NoLabel,ListAllLabels)|Alts],NewAlts).

% failing:
eval([A|_RA],[B|_RB],_GroundTerms,Trace,TraceR,Alts,NewAlts) :-
  %%\+(prolog_reader:get_clause_as_list(A,_Body)),
  \+(cl(A,_Body)),
  reverse([[]|Trace],TraceR),
  copy_term(B,Bcopy),copy_term(B,Bcopy2),
  %%findall(K,(prolog_reader:get_clause_as_list(Bcopy,_),get_clause_label(Bcopy,K)),ListAllLabels),
  findall(K,(cl(Bcopy,_),get_atom_label(Bcopy,K)),ListAllLabels),
  del_dump_label(Bcopy2,Bcopy2NoLabel),
  reverse([(Bcopy2NoLabel,ListAllLabels)|Alts],NewAlts).

/*
%% just for debugging..
eval(CGoal,SGoal,GroundTerms,Trace,Trace_) :-
  print('(10) ERROR!! '),
  println_atom(eval(CGoal,CGoalAns,SGoal,SGoalAns,GroundTerms,Trace,TraceR)),
  halt.
*/


% END main transition rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


no_builtins([]).
no_builtins([A|R]) :-
  \+(predicate_property(A,built_in)),
  !,
  no_builtins(R).


ground_enough(A) :- ground(A),!.
ground_enough((_A =.. [B|_R])) :- ground(B),!.
ground_enough(call(A)) :- nonvar(A),!.
ground_enough((_X is Y)) :- ground(Y),!.
ground_enough((X = Y)) :- ground(X),ground(Y),!. %% this version is needed for flattening!
/*
ground_enough((_X = Y)) :- ground(Y),!.
ground_enough((X = _Y)) :- ground(X),!.
*/




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% some pretty-printing utilities..
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic verbose/0.
:- dynamic very_verbose/0.

assert_verbose :- verbose -> true ; assert(verbose).
assert_very_verbose :- very_verbose -> true ; assert(very_verbose).
vprint(X) :- (verbose -> print(user,X) ; true).
vprintln(X) :- (verbose -> (print(user,X),nl(user)) ; true).
vprintln_atom(X) :- (verbose -> (copy_term(X,C),numbervars(C,0,_),print(user,C),nl(user)) ; true).
vvprint(X) :- (very_verbose -> print(user,X) ; true).
vvprintln(X) :- (very_verbose -> (print(user,X),nl(user)) ; true).
vvprintln_atom(X) :- (very_verbose -> (copy_term(X,C),numbervars(C,0,_),print(user,C),nl(user)) ; true).
println(X) :- print(user,X),nl(user).
print_atom(X) :- copy_term(X,C),numbervars(C,0,_),print(user,C).
println_atom(X) :- copy_term(X,C),numbervars(C,0,_),print(user,C),nl(user).


copy(In, Out) :-
        repeat,
            (   at_end_of_stream(In)
            ->  !
            ;   read_pending_input(In, Chars, []),
                format(Out, '~s', [Chars]),
                flush_output(Out),
                fail
            ).


l2d([],true).
l2d([A],A) :- !.
l2d([A|R],(A,B)) :- l2d(R,B).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% some benchmarks
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cex1 :- main(p(s(a)),[1],2,10,false,'examples/ex01.pl').
cex2 :- main(p(s(a)),[],2,10,false,'examples/ex01.pl').

cex3 :- main(p(s(a),a),[1,2],2,10,false,'examples/ex02.pl').
cex4 :- main(p(s(a),a),[1],2,10,false,'examples/ex02.pl').
cex5 :- main(p(s(a),a),[],2,10,true,'examples/ex02.pl').
cex6 :- main(p(s(a),a),[2],2,10,true,'examples/ex02.pl').

cex7 :- main(nat(0),[1],2,10,true,'examples/ex03.pl').
cex8 :- main(nat(0),[],2,10,false,'examples/ex03.pl'). % non-termination

%%cex9 :- main(f(a,a),[1],1,10,false,'examples/g.pl').
cex9 :- main(generate(empty,_A,_B),[1],1,10,false,'examples/ex07.pl').


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Fred's stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

matches_aux(A,HNegs,HPos,VarsToBeGrounded) :-
	%writeln(in-matches_aux(A,HNegs,HPos,VarsToBeGrounded)),
	%
	% check the preconditions:
	preconds(A,HNegs,HPos,VarsToBeGrounded),
	%
	positive_atoms([A|HPos],B,UVariablesInB),
	%
	copy_term(A-VarsToBeGrounded,Ac-VarsToBeGroundedc),
	unifiable(Ac,B,Theta),
	% NB: now we use the new copy. The newest variables comes as lhs in theta
	% hence u-Variables (which are older) are on rhs, so that grounding_subst
	% has a chance to leave the u-variables unbounded.
	%
	grounding_subst(VarsToBeGroundedc,Theta,B,Eta),
	%
	compose_subst(Theta,Eta,Sigma),
	%
	domain(Sigma,B,DomSigmaB),
	strict_empty_intersection(DomSigmaB,UVariablesInB),
	%
	apply_term_subst_term(Ac,Sigma,ASigma),
	forall(member(Hneg,HNegs),\+ (ASigma=Hneg)),
	%
	% sanity test: it should always succeed by property of the PosNeg
	(   forall(member(Hp,HPos),\+ \+ (ASigma=Hp))
	->  true
	;   throw(bug-matches_aux(Ac,HNegs,HPos,VarsToBeGrounded))),
	%
	A=ASigma,
	%writeln(out-matches_aux(A,HNegs,HPos,VarsToBeGrounded)),
	true.


preconds(A,HNegs,HPos,VarsToBeGrounded) :-
	forall(member(Hp,HPos),Hp=A),
	forall(member(Hn,HNegs),Hn=A),
	term_variables(A,VarsA), term_variables(HPos-HNegs,VarsHs),
	strict_empty_intersection(VarsA,VarsHs),
	strict_is_largely_incuded(VarsToBeGrounded,VarsA).


grounding_subst(VarsToBeGrounded,Theta,B,Eta) :-
	apply_term_subst_term(VarsToBeGrounded,Theta,VTBGTheta),
	%
	copy_term(VTBGTheta,VTBGThetac),
	generate_ground_terms(VTBGThetac),
	unifiable(VTBGTheta,VTBGThetac,Eta1),
	%
	compose_subst(Theta,Eta1,Sigma1),
	range(Sigma1,B,NewVarsToBeGround),
	%
	copy_term(NewVarsToBeGround,NewVarsToBeGroundc),
	generate_ground_terms(NewVarsToBeGroundc),
	unifiable(NewVarsToBeGround,NewVarsToBeGroundc,Eta2),
	%
	compose_subst(Eta1,Eta2,Eta).

%%%%

domain([],[]).
domain([V=_|Subst],[V|Dom]) :-
	domain(Subst,Dom).

domain(Subst,Atom,Dom) :-
	domain(Subst,DomSubst),
	term_variables(Atom,Vars),
	strict_intersection(Vars,DomSubst,Dom).

%%

range(Subst,Ran) :-
	range_aux(Subst,[],Ran).

  range_aux([],R,R).
  range_aux([_=T|Subst],R0,R) :-
	term_variables(T,Vars),
	strict_union(Vars,R0,R1),
	range_aux(Subst,R1,R).


range(Subst,Atom,Vars) :-
	restrict_subst_atom_subst(Subst,Atom,SAtom),
	range(SAtom,Vars).

restrict_subst_atom_subst(S1,A,S2) :-
	term_variables(A,Vars),
	restrict_sas(S1,Vars,S2).

  restrict_sas([],_Vars,[]).
  restrict_sas([X=T|S1],Vars,[X=T|S2]) :-
	strict_mem(X,Vars), !,
	restrict_sas(S1,Vars,S2).
  restrict_sas([_|S1],Vars,S2) :-
	restrict_sas(S1,Vars,S2).



%%

apply_term_subst_term(Ground,_Subst,Ground) :-
	ground(Ground), !.
apply_term_subst_term(Var,Subst,Term) :-
	var(Var), !, apply_var_subst_term(Var,Subst,Term).
apply_term_subst_term(Term,Subst,Res) :-
	functor(Term,F,N),functor(Res,F,N),
	apply_term_subst_term(1,N,Term,Subst,Res).

  apply_term_subst_term(P,N,_Term,_Subst,_Res) :- P > N, !.
  apply_term_subst_term(I,N,Term,Subst,Res) :-
	I =< N, J is I+1,
	arg(I,Term,Ti), arg(I,Res,Ri),
	apply_term_subst_term(Ti,Subst,Ri),
	apply_term_subst_term(J,N,Term,Subst,Res).

  apply_var_subst_term(Var,Subst,Term) :-
	apply_subst_var_term(Subst,Var,Term).

    apply_subst_var_term([Var1=Term1|_],Var,Term) :-
	Var1 == Var, !, Term=Term1.
    apply_subst_var_term([_|Subst],Var,Term) :-
	apply_subst_var_term(Subst,Var,Term).
    apply_subst_var_term([],Var,Var).

%%

compose_subst(S1,S2,S3) :-
	apply_subst_subst(S1,S2,S12),
	append(S12,S2,S4),
	simplify_subst(S4,S3).

  apply_subst_subst([],_S2,[]).
  apply_subst_subst([X=T|S1],S2,[X=U|S3]) :-
	apply_term_subst_term(T,S2,U),
	apply_subst_subst(S1,S2,S3).

  simplify_subst([],[]).
  simplify_subst([X=T|Subst],[X=T|SimpSubst]) :-
	X \== T, !, simplify_subst(Subst,SimpSubst).
  simplify_subst([_|Subst],SimpSubst) :-
	simplify_subst(Subst,SimpSubst).







:- begin_tests(matches_aux).

% matches_aux(A,HNegs,HPos,VarsToBeGrounded)

test(0) :- cex1, cex2, cex3, cex4, cex5, cex6, cex7, cex8.

test(1) :-
	matches_aux(p(_),[],[],[]).

test(2) :-
	matches_aux(p(X),[],[],[X]),!,
	ground(X).

test(posneg_ex1) :-
	matches_aux(p(X),[p(s(0))],[p(s(Y))],[X]),!,
	ground(X), X=s(Z), Z\==0, var(Y).

test(posneg_ex2,[fail]) :-
	matches_aux(p(X),[p(f(_Z))],[p(a),p(b)],[X]).

test(posneg_ex3,[fail]) :-
	matches_aux(p(_X),[p(f(_Z))],[p(a),p(b)],[]).

test(3) :-
	matches_aux(p(T,0),[],[p(a,_X),p(b,_Y)],[]),
	var(T).

test(4,[fail]) :-
	matches_aux(p(T,0),[],[p(a,_X),p(b,_Y)],[T]).

test(5,[fail]) :-
	matches_aux(p(_X),[p(_Y)],[],[]).


:- end_tests(matches_aux).


%% positive_atoms(+HPos,-B,-UVariablesInB)
%% where HPos is a non-empty list
positive_atoms(HPos,B,UVariablesInB) :-
	HPos=[_|_],
	copy_term(HPos,HPos0),
	strict_shrink(HPos0,HPos1),
	pa_1st_while(HPos1,HPos2),
	pa_2nd_while(HPos2,B,[],Uvars),
	term_variables(B,Bvars),
	strict_intersection(Bvars,Uvars,UVariablesInB).


pa_1st_while(HPos0,HPos) :-
	append(As,[B1|HPos1],HPos0),
	append(Bs,[B2|Cs],HPos1),
	simple_disag_pair(B1,B2,P1,P2),
	!,
	P1=P2,
	append([As,[B1|Bs],[B2|Cs]],HPos2),
	strict_shrink(HPos2,HPos3),
	pa_1st_while(HPos3,HPos).
pa_1st_while(HPos,HPos).


pa_2nd_while([B],B,Uvars,Uvars) :- !.
pa_2nd_while([B1,B2|B2s],B,Uvars0,Uvars) :-
	complex_disag_pair(B1,B2,_P1,_P2,X1-Tx1,X2-Tx2),
	!,
	X1=NewUVar,
	X2=NewUVar,
	Uvars1=[NewUVar|Uvars0],
	strict_shrink([Tx1,Tx2|B2s],Cs),
	pa_2nd_while(Cs,B,Uvars1,Uvars).

%%
simple_disag_pair(T1,T2,_,_) :-
	var(T1), occurs_check(T1,T2), !, fail.
simple_disag_pair(T1,T2,_,_) :-
	var(T2), occurs_check(T2,T1), !, fail.
simple_disag_pair(T1,T2,P1,P2) :-
	(var(T1) ; var(T2)), !,
	P1=T1, P2=T2.
simple_disag_pair(T1,T2,P1,P2) :-
	functor(T1,F,N), functor(T2,F,N),
	between(1,N,J),	arg(J,T1,T1j), arg(J,T2,T2j),
	simple_disag_pair(T1j,T2j,P1,P2).

  occurs_check(X,T) :- term_variables(T,VarsT), strict_mem(X,VarsT).


complex_disag_pair(T1,T2,_,_,_,_) :-
	var(T1), T1 == T2, !,
	fail.
complex_disag_pair(T1,T2,P1,P2,X1-Tx1,X2-Tx2) :-
	(var(T1) ; var(T2)), !,
	P1=T1, P2=T2, Tx1=X1, Tx2=X2.
complex_disag_pair(T1,T2,P1,P2,X1-Tx1,X2-Tx2) :-
	functor(T1,F,N), functor(T2,G,P), dif(F-N,G-P), !,
	P1=T1, P2=T2,
	Tx1=X1, Tx2=X2.
complex_disag_pair(T1,T2,P1,P2,Y1-Tx1,Y2-Tx2) :-
	functor(T1,F,N), functor(T2,F,N),
	between(1,N,J),	arg(J,T1,T1j), arg(J,T2,T2j),
	complex_disag_pair(T1j,T2j,P1,P2,Y1-Ty1,Y2-Ty2),
	build_term(T1,J,Ty1,Tx1),
	build_term(T2,J,Ty2,Tx2).

  build_term(T,J,X,Tx) :-
	functor(T,F,_N),
	T=..[F|Args],
	same_length(Args,Brgs),
	Tx=..[F|Brgs],
	build_children(J,Args,Brgs,X).

    build_children(1,[_Arg|Args],[X|Args],X) :- !.
    build_children(J,[A|As],[A|Bs],X) :-
	J >= 2, K is J -1,
	build_children(K,As,Bs,X).

%%

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

strict_shrink([],[]).
strict_shrink([A],[A]) :- !.
strict_shrink([A1,A2|As],[A1|Bs]) :-
	strict_not_mem(A1,[A2|As]), !,
	strict_shrink([A2|As],Bs).
strict_shrink([_A1,A2|As],Bs) :-
	strict_shrink([A2|As],Bs).

strict_intersection([],_,[]).
strict_intersection([A|As],Bs,Cs) :-
	strict_not_mem(A,Bs), !,
	strict_intersection(As,Bs,Cs).
strict_intersection([A|As],Bs,[A|Cs]) :-
	strict_intersection(As,Bs,Cs).

strict_is_largely_incuded([],_).
strict_is_largely_incuded([X|Xs],Ys) :-
	strict_mem(X,Ys),
	strict_is_largely_incuded(Xs,Ys).

strict_union([],Bs,Bs).
strict_union([X|Xs],Bs,Cs) :-
	strict_mem(X,Bs), !,
	strict_union(Xs,Bs,Cs).
strict_union([X|Xs],Bs,[X|Cs]) :-
	strict_union(Xs,Bs,Cs).

%%%%

generate_ground_terms([]).
generate_ground_terms([X|XR]) :-
  depthk(K),
  term(K,X),
  ground(X),
  generate_ground_terms(XR).


:- begin_tests(positive_atoms).

test(unif7_fail,[fail]) :-
	positive_atoms([],_,_).

test(unif7_example0) :-
	positive_atoms([p(X)],B,Us),
	nonvar(B), B = p(U), var(U),
	var(X), X \== U, Us==[].

test(unif7_example1) :-
	positive_atoms([p(a),p(b),p(c)],B,Us),
	nonvar(B), B = p(U), var(U), Us==[U].

test(unif7_example2) :-
	positive_atoms([p(a,_),p(b,_),p(Z,Z)],B,Us),
	nonvar(B), B = p(U,X), var(U), X==a, Us==[U].

test(unif7_example3) :-
	positive_atoms([p(s(a)),p(s(b)),p(_)],B,Us),
	nonvar(B), B = p(s(U)), var(U), Us==[U].

test(unif7_example4) :-
	positive_atoms([p(s(a),s(c)),p(s(b),s(c)),p(Z,Z)],B,Us),
	% not the answer given in the unification7.pdf, but another correct one
	nonvar(B), B = p(SU,SV),
	nonvar(SU), SU=s(U), var(U),
	nonvar(SV), SV=s(V), U \== V,
	Us==[U,V].

test(unif7_example5) :-
	positive_atoms([p(s(f(X)),X),p(s(g(a)),_Y),p(Z,Z)],B,Us),
	% not the answer given in the unification7.pdf
	nonvar(B), B = p(SU,V), nonvar(SU), SU=s(U), var(V), U\==V, Us==[U,V].

test(unif7_example6) :-
	positive_atoms([p(a,a),p(b,b)],B,Us),
	nonvar(B), B=p(U,V), var(U), var(V), U\==V, Us==[U,V].

test(unif7_example7) :-
	positive_atoms([p(a,b),p(b,a)],B,Us),
	nonvar(B), B=p(U,V), var(U), var(V), U\==V, Us=[U,V].

:- end_tests(positive_atoms).

/* TBD:

?- main(p(a),[],2,'examples/foo.pl').

then we only get:

 p(a) with trace [[]]
 p(s(a)) with trace [[l(p,1,1),l(p,1,2)]]
 p(A) with trace [[l(p,1,1),l(p,1,2),l(p,1,3)]]
 p(f(A)) with trace [[l(p,1,3)],[l(r,1,1),l(r,1,2)]]
 true.

which is incomplete. By replacing the call to matches_aux by a call
to matches_aux_ori, we get the correct result:

 p(a) with trace [[]]
 p(s(A)) with trace [[l(p,1,1),l(p,1,2)]]
 p(A) with trace [[l(p,1,1),l(p,1,2),l(p,1,3)]]
 p(s(c)) with trace [[l(p,1,2)],[]]
 p(s(b)) with trace [[l(p,1,2)],[l(q,1,2)]]
 p(f(A)) with trace [[l(p,1,3)],[l(r,1,1),l(r,1,2)]]
 p(f(c)) with trace [[l(p,1,3)],[l(r,1,2)]]
 p(f(b)) with trace [[l(p,1,3)],[]]
 p(f(a)) with trace [[l(p,1,3)],[l(r,1,1)]]


 ?- matches_aux(p(_G4508),[p(s(a)),p(s(_G5359))],[p(f(_G5281))],[]).
_G4508 = f(_G2538).

?- matches_aux_ori(p(_G4508),[p(s(a)),p(s(_G5359))],[p(f(_G5281))],[]).
_G4508 = f(_G2509) ;
_G4508 = f(c) ;
_G4508 = f(b) ;
_G4508 = f(a) ;
_G4508 = f(o) ;
_G4508 = f(f(_G4074)) ;
_G4508 = f(f(c)) ;
_G4508 = f(f(b)) ;
_G4508 = f(f(a)) ;
_G4508 = f(f(o)) ;
_G4508 = f(s(_G4074)) ;
_G4508 = f(s(c)) ;
_G4508 = f(s(b)) ;
_G4508 = f(s(a)) ;
_G4508 = f(s(o)) ;
false.

*/



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% End of Fred's stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%







