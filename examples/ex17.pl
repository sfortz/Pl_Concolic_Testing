rev(L,R) :- rev(L,[],R).

rev([],A,A).
rev([H|T],Acc,Res) :-
        is_list_(Acc),
        rev(T,[H|Acc],Res).


is_list_([]).
is_list_([_H|T]) :- is_list_(T).

