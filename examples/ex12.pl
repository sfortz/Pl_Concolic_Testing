hanoi(N) :- move(N,left,center,right).
 
move(0,_,_,_).
move(s(M),A,B,C) :-
    move(M,A,C,B),
    inform(A,B),
    move(M,C,B,A).
 
inform(_X,_Y). 
%% original: inform(X,Y) :- write([move,a,disk,from,the,X,pole,to,Y,pole]), nl.

