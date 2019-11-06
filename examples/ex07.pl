generate(empty,T,T).

%generate(char(X),[X|T],T).

generate(or(X,_Y),H,T) :- generate(X,H,T).
generate(or(_X,Y),H,T) :- generate(Y,H,T).

generate(cat(X,Y),H,T) :- generate(X,H,T1), generate(Y,T1,T).

generate(star(_X),T,T).
generate(star(X),H,T) :- generate(X,H,T1), generate(star(X),T1,T).
