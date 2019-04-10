%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  Concolic testing
%
%  Only tested in SWI Prolog, http://www.swi-prolog.org/
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(prolog_reader).
:- use_module(swiplz3).
:- use_module(z3_parser).

:- dynamic filename/1.

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
    ((member(cg(CG),Options),convert_entry_to_term(CG,CGT),assertz(cli_initial_cg(CGT)),fail)
      ; true),
    ((member(sg(SG),Options),convert_entry_to_term(SG,SGT),assertz(cli_initial_sg(SGT)),fail)
      ; true),
    ((member(depth(K),Options),convert_entry_to_term(K,KT),assertz(cli_initial_depth(KT)),fail)
      ; true),
    ((member(timeout(K),Options),convert_entry_to_term(K,KT),assertz(cli_initial_timeout(KT)),fail)
      ; true),
    (member(with_trace,Options) -> assertz(cli_initial_trace); true),
    ((member(ground(Ground),Options),convert_entry_to_term(Ground,GroundT),assertz(cli_initial_ground(GroundT)),fail)
      ; true),
    (member(interactive,Options) -> assertz(interactive) ; true),
    ((member(help,Options) ; RemArgV=[]) -> print_help ; true),
    ((member(file(FILE),Options),assertz(cli_initial_file(FILE)),fail)
      ; true),
    main_cli.

:- dynamic interactive/0. %% used to decide which clause of write_form to use

main_cli :-
    cli_initial_cg(Q),
    cli_initial_ground(NR),
    cli_initial_depth(K),
    cli_initial_timeout(T),
    cli_initial_file(File),!,
    (cli_initial_trace -> main(Q,NR,K,T,true,File); main(Q,NR,K,T,false,File)).

:- dynamic with_trace/0.

main(Q,NR,K,T,Trace,File) :-
    retractall(with_trace), 
    (Trace -> assertz(with_trace); true),
    catch(call_with_time_limit(T, mainT(Q,NR,K,File)), X, error_process(X)).


error_process(time_limit_exceeded) :- 
    write('Timeout exceeded'), nl, print_test_cases, halt.
error_process(X) :- write('Unknown Error' : X), nl, halt.

%% This one prints both test cases and pending test cases:
print_test_cases :- 
    nl,println('Time limit exceeded!'),
    testcases(Cases),  %% processed test cases
    reverse(Cases,CasesR),
    nl, println('Processed test cases: '),
    print_testcases(CasesR),
    nl, println('Pending test cases: '),
    findall(Goal,pending_test_case(Goal),PendingCases), %% pensing tests cases
    list_to_set(PendingCases,PendingCasesL), %% this is just to remove duplicates
    reverse(PendingCasesL,PendingCasesLR),
    nl,print_testcases_2(PendingCasesLR),!.
      
get_options([],Rec,Rem) :- !,Rec=[],Rem=[].
get_options(Inputs,RecognisedOptions,RemOptions) :-
    (recognise_option(Inputs,Flag,RemInputs)
     -> (RecognisedOptions = [Flag|RecO2],
         assertz(cli_option(Flag)),
         RemO2 = RemOptions)
     ;  (Inputs = [H|RemInputs], 
         RemOptions = [H|RemO2], 
         RecO2 = RecognisedOptions)
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

assert_interactive :- assertz(interactive).

%% goal is a list of atoms, File is the input program
mainT(CGoal,GroundPos,K,File) :-
    functor(CGoal,P,N), % Concrete Goal
    functor(SGoal,P,N), % Symbolic Goal
    cleaning,
    %% comment the next three asserts for the cgi-bin version:   ////To KEEP!
    %assert_very_verbose,
    %assert_verbose,
    %assert_interactive,
    %
    assertz(depthk(K)),
    %
    assertz(filename(File)),
    vprintln(load_file(File)),
    flush_output(user),
    prolog_reader:load_file(File),
    vprintln(finished_loading_file(File)),
    flush_output(user),
    %
    assertz(constants(['o'])), %% 'o' is just some 'fresh' constant for the negatives cases to succeed.
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
    vprint('Initial goal:          '),vprintln_atom(CGoal),
    vprint('Symbolic initial goal: '),vprintln_atom(SGoal),
    vprint('Ground variables:      '),vprintln_atom(GroundVars),
    %
    assertz(traces([])),
    assertz(testcases([])),
    assertz(pending_test_case(CGoal)),
    %
    z3_init_context(Ctx),
    %% Declaring terms:
    constants(C),
    get_consts(C,Consts),
    functions(F),
    get_fun(F,Functions),
    labeled(Preds),
    get_pred(Preds,Predicates),
    append(Consts,Functions,Terms_),
    append(Terms_,Predicates,Terms), 
    z3_mk_term_type(Ctx,Terms),
    concolic_testing(Ctx,SGoal,GroundVars),
    z3_clear_context(Ctx).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Dealing with Z3 contexts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

z3_init_context(N) :-
    z3_mk_config,
    z3_set_param_value("model","true"),
    z3_mk_context(N),
    z3_mk_solver(N),
    z3_del_config.

z3_clear_context(N) :-  
    z3_del_solver(N),
    z3_del_context(N).
    
%%%%%%%%%%%
cleaning :-
    retractall(cli_option(_)),
    retractall(cli_initial_cg(_)),
    retractall(cli_initial_sg(_)),
    retractall(cli_initial_ground(_)),
    retractall(cli_initial_depth(_)),
    retractall(cli_initial_depth(_)),
    retractall(cli_initial_trace),
    retractall(cli_initial_timeout(_)),
    retractall(with_trace),
    retractall(depthk(_)),
    retractall(cli_initial_file(_)),
    retractall(interactive),
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extracting the (universal) type from the program. 
% So far only atoms and functors are allowed.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Getting list of constants, functions and predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
             
get_consts([],[]).
get_consts([C|Consts],List) :- 
    get_consts(Consts,List_),
    List = [(C,0)|List_].

get_fun([],[]).
get_fun([fun(Name,Arity)|Funs],List):-
    get_fun(Funs,List_),
    List = [(Name,Arity)|List_].
        
get_pred([],[]).
get_pred([pred(Name,Arity)|Preds],List):-
    get_pred(Preds,List_),
    List = [(Name,Arity)|List_].

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Adding (clause) labels
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic labeled/1.
:- dynamic not_labeled/1.
:- dynamic cl/2.  %% for programs

add_clause_labels :- \+ not_labeled(_), fail.
add_clause_labels :-
    retract(not_labeled(G)),
    functor(G,P,N),labeled(Labeled), 
    retractall(labeled(_)),assertz(labeled([pred(P,N)|Labeled])),!,
    findall(cl(G,Body),prolog_reader:get_clause_as_list(G,Body),L), 
    acl(L,1,P,N),
    add_clause_labels.
    add_clause_labels.

update_not_labeled(B) :-
    (not_labeled(C),B=@=C -> true; assertz(not_labeled(B))).

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
    (member(pred(P,N),Labeled) -> true; update_not_labeled(B)),
    %
    append(Args,[_],NewArgs),
    AA=..[P|NewArgs],
    add_dump_parameters(R,RR).

add_dump_label(A,B) :-
    A=..[P|Args],
    append(Args,[_],NewArgs),
    B=..[P|NewArgs].

del_dump_label(A,B) :-
    A=..[P|Args],
    append(NewArgs,[_],Args),
    B=..[P|NewArgs].
  
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Updating (pending) test cases
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic traces/1.
:- dynamic testcases/1.
:- dynamic pending_test_case/1.

update_testcases(CGoal,Trace) :-
    testcases(Cases),
    (member(testcase(CGoal,Trace),Cases),! 
     ;    
     retractall(testcases(_)),
     assertz(testcases([testcase(CGoal,Trace)|Cases]))
    ),!.

update_pending_test_cases([]) :- !.
update_pending_test_cases([C|R]) :-
    pending_test_case(D), C =@= D,!,   %% variant
    update_pending_test_cases(R).
update_pending_test_cases([C|R]) :-
    assertz(pending_test_case(C)),
    update_pending_test_cases(R).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Printing test cases
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Concolic testing algorithm
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

concolic_testing(_,_,_) :- %% success !
    \+(pending_test_case(_)),!, % On vérifie qu'il n'y a plus de tests en attente.
    nl,println('Procedure complete!'),
    testcases(Cases),reverse(Cases,RCases),nl,print_testcases(RCases),!.

concolic_testing(Ctx,SGoal,GroundVars) :- 
    copy_term(foo(SGoal,GroundVars),foo(SGoalCopy,GroundVarsCopy)),
    retract(pending_test_case(CGoal)),!,
    copy_term(CGoal,CGoalCopy),
    copy_term(SGoal,SGoalCopy2),
    add_dump_label(CGoalCopy,CGoalCopyLabel),
    add_dump_label(SGoalCopy2,SGoalCopyLabel),
    vprintln(eval([CGoalCopyLabel],[SGoalCopyLabel],GroundVarsCopy,[],Trace,[],Alts)),
    %
    eval([CGoalCopyLabel],[SGoalCopyLabel],[],Trace,[],Alts),!,
    %
    traces(Traces),
    (member(Trace,Traces) -> 
        concolic_testing(Ctx,SGoal,GroundVars)
        ;
        update_testcases(CGoal,Trace),!,
        retractall(traces(_)),
        assertz(traces([Trace|Traces])), %% we updated the considered test cases
        vprint('Computed trace:          '),vprintln(Trace),
        vprint('Considered alternatives: '),vprintln_atom(Alts),

        findall(
            foo(SGoalCopy,NTrace,GroundVarsCopy),
            get_new_trace(Trace,Alts,[Trace|Traces],NTrace,Ctx,SGoalCopy, GroundVarsCopy),
            List
        ), %% now it is deterministic!
        vprint('new cases: '),vprintln(List),
        get_new_goals(List,NewGoals),
        update_pending_test_cases(NewGoals),
        concolic_testing(Ctx,SGoal,GroundVars)
    ).

get_new_goals([],[]).
get_new_goals([foo(Atom,_,_)|R],[Atom|RR]) :- get_new_goals(R,RR).

get_new_trace(Trace,Alts,Traces,NewTrace,Ctx,SGoal,GroundVars) :- 
    %writeln(in-get_new_trace(Trace,Alts,Traces)),
    prefix(PTrace,Trace), length(PTrace,N),
    nth0(N,Alts,(_,L)),
    %writeln(N),
    oset_power(L,LPower),
    vprint('All possibilities: '), vprintln(LPower),
    vprint('Visited traces:    '),vprintln(Traces),
    member(Labels,LPower),  %% nondeterministic!!  %% Crée les branches
    append(PTrace,[Labels],NewTrace), %% Création de la nouvelle trace: préfix + labels
    vprintln(\+(member(NewTrace,Traces))), %% A VERIFIER: Une trace ne peut pas préfixer une autre!
    \+(member(NewTrace,Traces)),
    matches(Ctx,SGoal,NewTrace,GroundVars).

  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  
  
matches(Ctx,A,Trace,G) :-
    append(Trace,LPos),
    get_list_clauses(LPos,CPos),
    %nl,write("Trace: "),writeln(Trace),
    %write("CPos: "),writeln(CPos),
    get_all_neg_labels(A,Trace,LNeg),
    get_list_clauses(LNeg,CNeg),
    %write("CNeg: "),writeln(CNeg),
    matches_aux(Ctx,A,CNeg,CPos,G). 

get_all_neg_labels(_,[],[]).
get_all_neg_labels(A,[[]],NegLabels) :- get_neg_labels(A,[],NegLabels).
get_all_neg_labels(A,[T|Trace],NegLabels) :- 
    get_neg_labels(A,T,NL),
    get_next_goal(T,A_),
    get_all_neg_labels(A_,Trace,NegLabels_),
    append(NL,NegLabels_,NegLabels).    
    
get_neg_labels(A,PosLabels,NegLabels) :-
    copy_term(A,Acopy),
    add_dump_label(Acopy,AcopyLabel),
    findall(Label,(
        cl(AcopyLabel,_),
        get_atom_label(AcopyLabel,Label)
    ),ListAll),
    subtract(ListAll,PosLabels,NegLabels).

get_next_goal([L|_],Goal):-
    findall(Body,   
            (cl(ALabel,Body),get_atom_label(ALabel,L)),
            [List]), 
    (List = [Pred|_] -> %% Do I need to deal with the end of the list?
        Pred=..[F|Args],
        length(Args,M),
        N is M-1,
        compound_name_arity(Goal,F,N)
        ;
        List = []
    ).
              
get_list_clauses([],[]).
get_list_clauses([L|LList],[H|HList]) :- 
    findall(H,(cl(V,_),get_atom_label(V,H,L)),[H]),
    get_list_clauses(LList,HList).

get_atom_label(A,Label) :- A=..[_F|Args], last(Args,Label).
get_atom_label(A,Pred,Label) :- 
    A=..[_|ArgsLab], 
    last(ArgsLab,Label),!,
    del_dump_label(A,Pred).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% main transition rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% success
eval([],[],Trace,TraceR,Alts,AltsR) :- 
  reverse(Trace,TraceR),reverse(Alts,AltsR).

% unfolding:
eval([A|RA],[B|RB],Trace,NewTrace,Alts,NewAlts) :-
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
    eval(CGoal,SGoal,[ListLabels|Trace],NewTrace,[(Bcopy2NoLabel,ListAllLabels)|Alts],NewAlts).

% failing:
eval([A|_RA],[B|_RB],Trace,TraceR,Alts,NewAlts) :-
    \+(cl(A,_Body)),
    reverse([[]|Trace],TraceR),
    copy_term(B,Bcopy),copy_term(B,Bcopy2),
    findall(K,(cl(Bcopy,_),get_atom_label(Bcopy,K)),ListAllLabels),
    del_dump_label(Bcopy2,Bcopy2NoLabel),
    reverse([(Bcopy2NoLabel,ListAllLabels)|Alts],NewAlts).

change_label(Label,[_],[Label]) :- !.
change_label(Label,[X|R],[X|RR]) :- change_label(Label,R,RR).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% some pretty-printing utilities..
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic verbose/0.
:- dynamic very_verbose/0.

assert_verbose :- verbose -> true ; assertz(verbose).
assert_very_verbose :- very_verbose -> true ; assertz(very_verbose).
vprint(X) :- (verbose -> print(user,X) ; true).
vprintln(X) :- (verbose -> (print(user,X),nl(user)) ; true).
vprintln_atom(X) :- (verbose -> (copy_term(X,C),numbervars(C,0,_),print(user,C),nl(user)) ; true).
vvprint(X) :- (very_verbose -> print(user,X) ; true).
vvprintln(X) :- (very_verbose -> (print(user,X),nl(user)) ; true).
vvprintln_atom(X) :- (very_verbose -> (copy_term(X,C),numbervars(C,0,_),print(user,C),nl(user)) ; true).
println(X) :- print(user,X),nl(user).
print_atom(X) :- copy_term(X,C),numbervars(C,0,_),print(user,C).
println_atom(X) :- copy_term(X,C),numbervars(C,0,_),print(user,C),nl(user).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Z3's stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

matches_aux(Ctx,A,HNegs,HPos,VarsToBeGrounded) :-
	nl,%writeln(in-matches_aux(Ctx,A,HNegs,HPos,VarsToBeGrounded)),
	% checking the preconditions:
	preconds(A,HNegs,HPos,VarsToBeGrounded),
	%
	get_constraints(A,VarsToBeGrounded,HNegs,HPos,Consts),
	%
	( solve(Ctx,VarsToBeGrounded,Consts,Mod)
	 -> 
	    split_model(Mod,ValsMod),
	    z3_to_term_list(ValsMod,Terms),
        prefix(VarsToBeGrounded,Terms)
	).


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

mymember(X,[Y|_]) :- X == Y, !.
mymember(X,[_|R]) :- mymember(X,R).

mysubtract([],_,[]).
mysubtract([V|R],G,NG) :- mymember(V,G), mysubtract(R,G,NG).
mysubtract([V|R],G,[V|NG]) :- \+(mymember(V,G)), mysubtract(R,G,NG).

get_constraints(A,VarsToBeGrounded,HNegs,HPos,Constrs) :-
    term_variables(A,VarA),
    mysubtract(VarA,VarsToBeGrounded,VarsNotGrounded),
    get_pos_consts(A,VarsNotGrounded,HPos,PosConsts),
    get_neg_consts(A,VarsNotGrounded,HNegs,NegConsts),
    append(PosConsts,NegConsts,Constrs). 

get_pos_consts(_,_,[],[]).
get_pos_consts(A,VarsNotGrounded,[H|T],Constrs) :-
    copy_term(H,CArgs),
	term_variables(CArgs,VCArgs),
    exists_terms(VCArgs,A,VarsNotGrounded,CArgs,C1),
    get_pos_consts(A,VarsNotGrounded,T,C2),
    Constrs = [C1|C2].

exists_terms([],A,VarsNotGrounded,Args,Pred):- 
    Pred_ = (A = Args),
    exists_terms_atom(VarsNotGrounded,Pred_,Pred).
exists_terms([H|T],A,VarsNotGrounded,Args,Pred) :-
    exists_terms(T,A,VarsNotGrounded,Args,Pred1),
    Pred = exists(var(H),Pred1). 

exists_terms_atom([],Pred,Pred).
exists_terms_atom([V|Vars],Pred1,Pred3) :-
    exists_terms_atom(Vars,Pred1,Pred2),
    Pred3 = exists(var(V),Pred2).
 
get_neg_consts(_,_,[],[]).
get_neg_consts(A,VarsNotGrounded,[H|T],Constrs) :-
	copy_term(H,CArgs),
	term_variables(CArgs,VCArgs),
    forall_terms(VCArgs,A,VarsNotGrounded,CArgs,C1),
    get_neg_consts(A,VarsNotGrounded,T,C2),
    Constrs = [C1|C2].

forall_terms([],A,VarsNotGrounded,Args,Pred):- 
    Pred_ = (A \= Args),
    forall_terms_atom(VarsNotGrounded,Pred_,Pred).  
forall_terms([H|T],A,VarsNotGrounded,Args,Pred) :-
    forall_terms(T,A,VarsNotGrounded,Args,Pred1),
    Pred = forall(var(H),Pred1). 

forall_terms_atom([],Pred,Pred).
forall_terms_atom([V|Vars],Pred1,Pred3) :-
    forall_terms_atom(Vars,Pred1,Pred2),
    Pred3 = forall(var(V),Pred2).        
        
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Z3 solver
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Same context for each branch?
solve(N,VarsToBeGrounded,L,Model) :-  
    z3_push(N),
    copy_term(L,CL),  
/* Declaring constraints to solve*/

    %% To improve efficiency, we could only declare grouded variable, but it needs some C changes...
    %numbervars(VarsToBeGrounded),   
    %get_varnames(VarsToBeGrounded,VarsStr),
    
    z3_termconstr2smtlib(N,[],CL,VarsC,Csmtlib2), 
    (VarsC=[] -> true ; z3_mk_term_vars(N,VarsC)),
    z3_assert_term_string(N,Csmtlib2),
    writeln(Csmtlib2),
/* checking satisfiability */
    (z3_check(N) ->
        z3_print_model(N,Model),
        get_context_vars(N,VVS),
        get_model_varT_eval(N,VVS,Values),
        term_variables(CL,AllVars),
        z3_pop(N,VarsC),
        AllVars=Values;
        z3_pop(N,VarsC),
        false
    ).	
            
            
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Spliting a Z3 (string) model into Prolog terms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     
split_model(Model,Vals) :- 
    split_string(Model, "\n", "\s\t\n", L),
    split_affectation(L, Vals).    
  
split_affectation([H],[Affect]) :-
    split_string(H, "->", " ", [_,"",Affect]), !.         
split_affectation([H|T],Vals) :-
    split_affectation(T,Vals1),
    split_string(H, "->", " ", [_,"",Affect]),
    Vals = [Affect|Vals1]. 
    
       
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Transforming a list of strings representing a Z3 terms into a list 
%  of Prolog terms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
z3_to_term_list([],[]).
z3_to_term_list([T|Z3Terms],Terms) :-
    string_codes(T,L),
    pterm(L,_,Term),
    z3_to_term_list(Z3Terms,Terms_),
    Terms = [Term|Terms_].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% some benchmarks
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cex1 :- main(p(s(a)),[1],2,10,true,'examples/ex0.pl').
cex2 :- main(p(s(a)),[1],2,10,false,'examples/ex01.pl').

cex3 :- main(p(s(a),a),[1,2],2,10,false,'examples/ex02.pl').
cex4 :- main(p(s(a),a),[1],2,10,false,'examples/ex02.pl').
cex5 :- main(p(s(a),a),[],2,10,true,'examples/ex02.pl').
cex6 :- main(p(s(a),a),[2],2,10,true,'examples/ex02.pl').

cex7 :- main(nat(0),[1],2,10,true,'examples/ex03.pl').
cex8 :- main(nat(0),[],2,10,false,'examples/ex03.pl'). % non-termination

%%cex9 :- main(f(a,a),[1],1,10,false,'examples/g.pl').
cex9 :- main(generate(empty,_A,_B),[1],1,10,false,'examples/ex07.pl').

