(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-const one Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun qfac (Nat Nat) Nat)
(declare-fun fac (Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (= one (S Z)))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (z Nat)) (= (mult (S z) y) (plus y (mult z y)))))
(assert (forall ((y Nat)) (= (qfac Z y) y)))
(assert
  (forall ((y Nat) (z Nat))
    (= (qfac (S z) y) (qfac z (mult (S z) y)))))
(assert (= (fac Z) (S Z)))
(assert (forall ((y Nat)) (= (fac (S y)) (mult (S y) (fac y)))))
(assert-not (forall ((x Nat)) (= (fac x) (qfac x one))))
(check-sat)