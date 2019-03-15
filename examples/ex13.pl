start(0).
t(0,a,1).
t(0,b,2).
t(1,a,2).
t(1,b,1).
t(2,a,2).
t(2,b,2).
final(1).

accept(S) :- start(I), path(I,S).

path(K,[]) :- final(K).
path(K,[H|T]) :- t(K,H,N), path(N,T).

