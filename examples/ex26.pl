%% erroneous program

factorial(X,N) :- X=0,N=1.
factorial(X,N) :- X>0, X is Y-1, factorial(Y,M), N is X*M.
