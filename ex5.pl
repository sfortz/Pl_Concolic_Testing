:- use_module(library(apply)).
:- use_module(lambda).

write_eqs_term(T, Eqs) :-
   \+ \+ ( 
           maplist(\Eq^( Eq = (N='$VAR'(Chs)), N = Ch), Eqs),
           write_term(T,[numbervars(true),quoted(true)])
   ).

ttoa(T, Eqs, A) :-
   with_output_to(atom(A), write_eqs_term(T, Eqs) ).
  
main :- 
        read_term(T,[variable_names(Eqs)]),
        write_eqs_term(T, Eqs), nl, nl,
        trans(Eqs).

trans([H]):-
        print(H), nl.
trans([H|T]):-
        print(H), nl, trans(T).
        
        
        
/*	write_term(-X^2,[variable_names(['X'=X])]).  */
