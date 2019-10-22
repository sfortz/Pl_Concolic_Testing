p(s(a),b).
p(s(X),a) :- q(X).
p(f(X),s(Y)) :- r(X,Y).

q(a).
q(b).

r(a,b).
r(c,b).
