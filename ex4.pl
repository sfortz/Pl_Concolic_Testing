:- use_module(swiplz3).

main :-
    in_to_out("in.pl",'out.pl').
    
in_to_out(NameIn,NameOut) :- 
    open(NameIn, read, File), 
    read_file(File, Terms, Vars), 
    close(File),
    get_model_str(Terms, Vars, Str),
    % redirection vers le fichier de sortie
    tell(NameOut),
	writeln(Str),
    told.

/* Reads a file containing terms and returns the list of terms and the name of the variables (in order of appearance). */	
read_file(File, Terms, Vars) :- 
    see(File),
    read_term(T,[variable_names(Vars)]),
    split_term(T, Terms). 
      
/* Splits a list containing terms.*/   
split_term(Term,L) :-  
    compound_name_arguments(Term, ',', [A,Args]),!,
    split_term(Args,L1),
    append([A],L1,L). 
split_term(Term,[Term]) :-  
    compound_name_arguments(Term, _, _). 

/* Takes a list of Terms (representing constraints) and a list of variable names. Returns a string representing the model solving these constraints.*/       
get_model_str(Terms, Vars, Str) :-
    solve(Terms,ModStr),nl,nl,
    split_model(ModStr,_,ValsMod),
    get_var_name(Vars,Names,_),
    %get_var_list(Names,Refs,VarList),
    %write_term(Terms,[variable_names(VarList)]),
    replace_var_model(Names,ValsMod,Str). 

/* Write a list in the current output, one element per line.*/
write_list([]) :- !.
write_list([L|Ls]):-
    writeln(L),
    write_list(Ls).
    
/* Splits a model (in String form) into two lists: one containing the "varriable-value" pairs, and the other with only the values.*/ 
split_model(Model,List,Vals) :- 
    split_string(Model, "\n", "\s\t\n", L),
    split_affectation(L, List, Vals).    

/* Splits a list of affectations (from a model) into two lists: one containing the "varriable-value" pairs, and the other with only the values.*/
split_affectation([],[],[]).      
split_affectation([H],L,[Affect]) :-
    split_string(H, "->", "", [Var,"",Affect]),
    L = [(Var,Affect)].         
split_affectation([H|T],L,Vals) :-
    split_affectation(T,L1,Vals1),
    split_string(H, "->", "", [Var,"",Affect]),
    append([(Var,Affect)],L1,L),
    append([Affect],Vals1,Vals).      
  
/* Takes a list of Strings containing the pattern "Var = Ref" and returns the list of the variable names and a list of their references.*/       
get_var_name([H],[Name],[Ref]) :- compound_name_arguments(H, _, [Name,Ref]).
get_var_name([H|Lst],Names,Refs) :- 
    get_var_name(Lst,Names1,Refs1),
    compound_name_arguments(H, _, [Name,Ref]),
    append([Name],Names1,Names),
    append([Ref],Refs1,Refs).

/* Takes a list of names and references, and associates them to each other.*/       
get_var_list([Name],[Ref],[Name = Ref]).
get_var_list([N|Name],[R|Ref],List) :- 
    get_var_list(Name,Ref,List1),
    append([N = R],List1,List).      

/* Takes a list of variable names and a list of values, and returns a string, representing a model where each variable is associate to a value.*/  
replace_var_model([Var],[Val],Str) :-
    string_concat(Var,'->', Str1),
    string_concat(Str1,Val,Str).
replace_var_model([Var|Vars],[Val|Vals],Str) :-
    string_concat(Var,"->", Str1),
    string_concat(Str1,Val,Str2),
    string_concat(Str2,'\n',Str3),
    replace_var_model(Vars,Vals,Str4),
    string_concat(Str3,Str4,Str).
    
solve([C1,C2,C3],Model) :- 
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
        z3_print_model(N,Model),
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
    z3_del_context(N).
