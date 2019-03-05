
simple_example

DeMorgan
DeMorgan is valid

find_model_example1
model for: x xor y
sat
x -> true
y -> false


find_model_example2
model for: x < y + 1, x > 2
sat
x -> 3
y -> 3

model for: x < y + 1, x > 2, not(x = y)
sat
y -> 4
x -> 3


prove_example1
prove: x = y implies g(x) = g(y)
valid
disprove: x = y implies g(g(x)) = g(y)
invalid
counterexample:
y -> U!val!0
x -> U!val!0
g -> {
  U!val!1 -> U!val!2
  else -> U!val!1
}


prove_example2
prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0
valid
disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1
invalid
counterexample:
z -> (- 1)
y -> 1236
x -> 1236
g -> {
  0 -> 2
  (- 1) -> 3
  else -> 0
}


push_pop_example1
assert: x >= 'big number'
push
number of scopes: 1
assert: x <= 3
unsat
pop
number of scopes: 0
sat
x = 1000000000000000000000000000000000000000000000000000000:int
function interpretations:
assert: y > x
sat
y = 1000000000000000000000000000000000000000000000000000001:int
x = 1000000000000000000000000000000000000000000000000000000:int
function interpretations:

quantifier_example1
pattern: ((f (:var 0) (:var 1)))

assert axiom:
(forall ((x!1 Int) (x!2 Int))
  (! (= (inv!0 (f x!2 x!1)) x!1) :pattern ((f x!2 x!1))))
prove: f(x, y) = f(w, v) implies y = v
valid
disprove: f(x, y) = f(w, v) implies x = w
that is: not(f(x, y) = f(w, v) implies x = w) is satisfiable
unknown
potential model:
w = 2:int
v = 1:int
y = 1:int
x = 0:int
function interpretations:
f = {...}
reason for last failure: (incomplete quantifiers)

array_example1
prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))
(=> (= (store a1 i1 v1) (store a2 i2 v2))
    (or (= i1 i3) (= i2 i3) (= (select a1 i3) (select a2 i3))))
valid

array_example2
n = 2
(distinct k!0 k!1)
sat
#1 = (declare-fun const (Bool) (Array Bool Bool))[(declare-fun false () Bool)]
#0 = (declare-fun store ((Array Bool Bool) Bool Bool) (Array Bool Bool))[(declare-fun const (Bool) (Array Bool Bool))[(declare-fun false () Bool)], (declare-fun false () Bool), (declare-fun true () Bool)]
function interpretations:
n = 3
(distinct k!0 k!1 k!2)
sat
#0 = quantifier#unknown
#1 = quantifier#unknown
#2 = quantifier#unknown
function interpretations:
n = 4
(distinct k!0 k!1 k!2 k!3)
sat
#0 = quantifier#unknown
#1 = quantifier#unknown
#2 = quantifier#unknown
#3 = quantifier#unknown
function interpretations:
n = 5
(distinct k!0 k!1 k!2 k!3 k!4)
unsat

array_example3
domain: int
range:  bool

tuple_example1
tuple_sort: (real, real)
prove: get_x(mk_pair(x, y)) = 1 implies x = 1
valid
disprove: get_x(mk_pair(x, y)) = 1 implies y = 1
invalid
counterexample:
y -> 0.0
x -> 1.0

prove: get_x(p1) = get_x(p2) and get_y(p1) = get_y(p2) implies p1 = p2
valid
disprove: get_x(p1) = get_x(p2) implies p1 = p2
invalid
counterexample:
p1 -> (mk_pair 1.0 0.0)
p2 -> (mk_pair 1.0 2.0)

prove: p2 = update(p1, 0, 10) implies get_x(p2) = 10
valid
disprove: p2 = update(p1, 0, 10) implies get_y(p2) = 10
invalid
counterexample:
p2 -> (mk_pair 10.0 1.0)
p1 -> (mk_pair 0.0 1.0)


bitvector_example1
disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
invalid
counterexample:
x -> #x80000008


bitvector_example2
find values of x and y, such that x ^ y - 103 == x * y
sat
y -> #xc4f53687
x -> #x1b0035ae


eval_example1
MODEL:
x -> 3
y -> 4

evaluating x+y
result = 7:int

two_contexts_example1
k!0

error_code_example1
last call succeeded.
last call failed.

error_code_example2
before Z3_mk_iff
Z3 error: Sorts Int and Bool are incompatible.

parser_example2
formula: (ast-vector
  (> x y))
assert axiom:
(ast-vector
  (> x y))
sat
y -> 0
x -> 1


parser_example3
assert axiom:
(ast-vector
  (forall ((x Int) (y Int)) (= (g x y) (g y x))))
formula: (ast-vector
  (forall ((x Int) (y Int)) (=> (= x y) (= (g x 0) (g 0 y)))))
valid

parser_example5
Z3 error: (error "line 1 column 23: invalid command, '(' expected")
(error "line 1 column 62: unknown constant y")
.

numeral_example
Numerals n1:(/ 1.0 2.0) n2:(/ 1.0 2.0)
valid
Numerals n1:(- (/ 1.0 3.0)) n2:(- (/ 33333333333333333333333333333333333333333333333333.0
      100000000000000000000000000000000000000000000000000.0))
valid

ite_example
term: (ite false 1 0)

list_example
valid
valid
valid
valid
valid
valid
valid
Formula (=> ((_ is (cons (Int int_list) int_list)) u) (= u (cons (head u) (tail u))))
valid
invalid
counterexample:
u -> nil


tree_example
valid
valid
valid
valid
valid
Formula (=> ((_ is (cons (cell cell) cell)) u) (= u (cons (car u) (cdr u))))
valid
invalid
counterexample:
u -> nil


forest_example
valid
valid
valid
valid
valid
valid

binary_tree_example
valid
valid
valid
valid
valid

enum_example
(declare-fun apple () fruit)
(declare-fun banana () fruit)
(declare-fun orange () fruit)
(declare-fun is (fruit) Bool)
(declare-fun is (fruit) Bool)
(declare-fun is (fruit) Bool)
valid
valid
invalid
counterexample:

valid
valid

unsat_core_and_proof_example
unsat
proof: (unit-resolution (def-axiom (or (or (not PredA) PredB (not PredC)) (not PredB)))
                 (unit-resolution (def-axiom (or (or (not PredA)
                                                     (not PredB)
                                                     (not PredC))
                                                 PredB))
                                  (unit-resolution (mp (asserted (or (and PredA
                                                                          PredB
                                                                          PredC)
                                                                     P1))
                                                       (monotonicity (rewrite (= (and PredA
                                                                                      PredB
                                                                                      PredC)
                                                                                 (not (or (not PredA)
                                                                                          (not PredB)
                                                                                          (not PredC)))))
                                                                     (= (or (and PredA
                                                                                 PredB
                                                                                 PredC)
                                                                            P1)
                                                                        (or (not (or (not PredA)
                                                                                     (not PredB)
                                                                                     (not PredC)))
                                                                            P1)))
                                                       (or (not (or (not PredA)
                                                                    (not PredB)
                                                                    (not PredC)))
                                                           P1))
                                                   (asserted (not P1))
                                                   (not (or (not PredA)
                                                            (not PredB)
                                                            (not PredC))))
                                  PredB)
                 (unit-resolution (mp (asserted (or (and PredA
                                                         (not PredB)
                                                         PredC)
                                                    P2))
                                      (monotonicity (rewrite (= (and PredA
                                                                     (not PredB)
                                                                     PredC)
                                                                (not (or (not PredA)
                                                                         PredB
                                                                         (not PredC)))))
                                                    (= (or (and PredA
                                                                (not PredB)
                                                                PredC)
                                                           P2)
                                                       (or (not (or (not PredA)
                                                                    PredB
                                                                    (not PredC)))
                                                           P2)))
                                      (or (not (or (not PredA)
                                                   PredB
                                                   (not PredC)))
                                          P2))
                                  (asserted (not P2))
                                  (not (or (not PredA) PredB (not PredC))))
                 false)

core:
(not P1)
(not P2)


incremental_example1
unsat core: 0 2 3 
unsat
sat
unsat core: 0 2 3 
unsat
unsat core: 0 2 3 
unsat
sat

reference_counter_example
model for: x xor y
sat
x -> true
y -> false


smt2parser_example
formulas: (ast-vector
  (bvuge a #x10)
  (bvule a #xf0))

substitute_example
substitution result: (f (f a 0) 1)

substitute_vars_example
substitution result: (f (f a (g b)) a)

FPA-example
c4: (and (= x_plus_y (fp.add rm x y))
     (= x_plus_y (fp #b0 #b10000000100 #x5000000000000))
     (not (= rm roundTowardZero))
     (not (fp.isZero y))
     (not (fp.isNaN y))
     (not (fp.isInfinite y)))
sat
y -> (fp #b1 #b10000000111 #x3eb0e8f640000)
rm -> roundNearestTiesToEven
x -> (fp #b0 #b10000000111 #x68b0e8f640000)
x_plus_y -> (fp #b0 #b10000000100 #x5000000000000)

c5: (and (= (fp #b0 #b10000000001 #xc000000000000)
        ((_ to_fp 11 53) #x401c000000000000))
     (= (fp #b0 #b10000000001 #xc000000000000)
        ((_ to_fp 11 53) roundTowardZero 2 (/ 7.0 4.0)))
     (= (fp #b0 #b10000000001 #xc000000000000)
        ((_ to_fp 11 53) roundTowardZero 7.0)))
sat


mk_model_example
Model:
a -> 1
b -> 2
c -> (_ as-array !0)
!0 -> {
  0 -> 3
  1 -> 4
  else -> 0
}

Found interpretation for "(declare-fun a () Int)"
Found interpretation for "(declare-fun b () Int)"
Found interpretation for "(declare-fun c () (Array Int Int))"
Evaluated a + b = 3
Evaluated c[0] + c[1] + c[2] = 7

