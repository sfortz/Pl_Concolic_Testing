fib(0, 0).
fib(s(0), s(0)).
fib(s(s(B)), NF) :-
    fib(s(B), AF), 
    fib(B, BF),
    sum(AF,BF,NF).

sum(0,Y,Y).
sum(s(X),Y,s(Z)) :- sum(X,Y,Z).

