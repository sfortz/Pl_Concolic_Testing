p(X) :- not(q(X)).
p(X) :- r(X).

q(a).
q(b) :- q(b).

r(b).

