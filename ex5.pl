:- module(ex5, [in_to_out/2]).

:- use_module(swiplz3).


in_to_out(NameIn,NameOut) :- 
	open(NameIn, read, File), 
	read_file(File, Terms, Vars), 
	close(File),
	process(Terms, Vars, LstOut),
% redirection vers le fichier de sortie
tell(NameOut),
write_list(LstOut),
%writeList([Lst,Vars]),
told.
	
read_file(File, Terms, Eqs) :- 
    see(File),
    read_term(T,[variable_names(Eqs)]),
    split_term(T, Terms).
    

/* Write a list in the current output, one element per line.*/
write_list([]) :- !.
write_list([L|Ls]):-
    writeln(L),
    write_list(Ls).
     
process(Terms, Vars, LstOut) :-
    get_var_name(Vars,Names,Refs),
    append(Names,Refs,V),
    append(Terms,V,LstOut),
    get_var_list(Names,Refs,List),
    write_term(Terms,[variable_names(List)]). 
      
/* Splits a list containing terms.*/   
split_term(Term,L) :-  
    compound_name_arguments(Term, ',', [A,Args]),!,
    split_term(Args,L1),
    append([A],L1,L). 
split_term(Term,[Term]) :-  
    compound_name_arguments(Term, _, _). 
        
         
/* Splits a list of string with the Exp separator.*/    
split_list([],[]) :- !.
split_list([H|Lst],Exp,L) :-      
    split_string(H, Exp, "", L1),
    split_list(Lst,L2),
    select(L1,L,L2).
        
get_var_name([H],[Name],[Ref]) :- compound_name_arguments(H, _, [Name,Ref]).
get_var_name([H|Lst],Names,Refs) :- 
    get_var_name(Lst,Names1,Refs1),
    compound_name_arguments(H, _, [Name,Ref]),
    append([Name],Names1,Names),
    append([Ref],Refs1,Refs).

get_var_list([Name],[Ref],[Name = Ref]).
get_var_list([N|Name],[R|Ref],List) :- 
    get_var_list(Name,Ref,List1),
    append([N = R],List1,List).       
/*	write_term(-X^2,[variable_names(['X'=X])]).  */
















