(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun min2 (Nat Nat) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert (forall ((y Nat)) (= (min2 Z y) Z)))
(assert (forall ((z Nat)) (= (min2 (S z) Z) Z)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (min2 (S z) (S y2)) (S (min2 z y2)))))
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert-not
  (forall ((a Nat) (b Nat)) (= (equal (min2 a b) a) (le a b))))
(check-sat)
