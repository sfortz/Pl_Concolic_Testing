ackermann(0,N,s(N)).
ackermann(s(M), 0, X) :- ackermann(M, s(0), X).
ackermann(s(M), s(N), X) :- ackermann(s(M), N, X1), ackermann(M, X1, X).
