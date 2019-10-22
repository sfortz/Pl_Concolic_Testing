qsort([], R, R).
qsort([X|L], R, R0) :-
        partition(L, X, L1, L2),
        qsort(L2, R1, R0),
        qsort(L1, R, [X|R1]).


partition([],_,[],[]).
partition([X|L],Y,[X|L1],L2) :-
        leq(X,Y),
        partition(L,Y,L1,L2).
partition([X|L],Y,L1,[X|L2]) :-
        g(X,Y),
        partition(L,Y,L1,L2).

leq(0,_).
leq(s(X),s(Y)) :- leq(X,Y).

g(s(_),0).
g(s(X),s(Y)) :- g(X,Y).

