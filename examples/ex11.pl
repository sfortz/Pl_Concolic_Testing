mult(0,_X,0).
mult(s(X),Y,Z) :- mult(X,Y,W), add(W,Y,Z).

add(0,Y,Y).
add(s(X),Y,s(Z)) :- add(X,Y,Z).
