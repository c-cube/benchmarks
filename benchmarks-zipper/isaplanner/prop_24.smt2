(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun max2 (Nat Nat) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert (forall ((y Nat)) (= (max2 Z y) y)))
(assert (forall ((z Nat)) (= (max2 (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (max2 (S z) (S x2)) (S (max2 z x2)))))
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
  (forall ((a Nat) (b Nat)) (= (equal (max2 a b) a) (le b a))))
(check-sat)
