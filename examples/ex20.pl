pre_order(T, L) :- pre_order_dl(T, L, []).

pre_order_dl(tree(X,L,R), [X|Xs], Zs) :-
  pre_order_dl(R, Ys, Zs),
  pre_order_dl(L, Xs, Ys).

pre_order_dl(void, Xs, Xs).
