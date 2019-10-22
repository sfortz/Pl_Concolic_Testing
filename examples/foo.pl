
foo(L,M) :- len(L,N), boh(N,M).

len([],0).
len([_X|T],s(N)) :- len(T,N).

boh(X,X).

%%%%%%%%%%%%%%%

p([Y|T]) :- q(Y,Z), r(Z,T).

q(a,[a]).
q(a,[b]).
q(a,[c]).

r(X,X).

%%%%%%%%%%%%%%%

w(X) :- w1(X,Y), w2(Y), w3(X).

w1(a,c).
w1(X,Y).

w2(b).

w3(b).

/* it is not true that given a derivation

   G0 -> G1 -> ... -> Gn

if we compute some alternatives for Gn and bind G0 with the resulting binding, the new derivation 
for G0 will actually follow the same steps of the previous derivation up to the point of Gn !!

This is what happens above starting with w(a), which produces w(b) and follows a different path.
Initial trace:

  {(w/1,1)}, {(w1/2,1),(w1/2,2)}, {}, backtracking, {(w1/2,2)}, {(w/2,1)}, {}  //failure

Computed alternative trace (out of many):

  {(w/1,1)}, {(w1/2,1),(w1/2,2)}, {}, backtracking, {(w1/2,2)}, {(w/2,1)}, {(w3/1,1)}

But the test case w(b) has the following associate trace:

  {(w/1,1)}, {(w1/2,2)}, {(w3/1,1)}


*/


dd(a,Y) :- eq(a,Y).
dd(b,Y) :- eq(b,Y).
dd(c,Y) :- eq(c,Y).

eq(X,X).
