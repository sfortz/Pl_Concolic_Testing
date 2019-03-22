incList([],_,[]).
incList([X|R],I,L) :- iList(X,R,I,L).

iList(X,R,I,[XI|RI]) :- nat(I),add(I,X,XI), incList(R,I,RI).

nat(0).
nat(s(X)) :- nat(X).

add(0,Y,Y).
add(s(X),Y,s(Z)) :- add(X,Y,Z).

