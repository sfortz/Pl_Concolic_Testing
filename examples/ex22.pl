
factorial(X,N) :- X=0,!, N=1.
factorial(X,N) :- Y is X-1, factorial(Y,M), N is X*M.
