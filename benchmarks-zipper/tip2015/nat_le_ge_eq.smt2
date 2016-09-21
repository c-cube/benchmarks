(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun le (Nat Nat) Bool)
(declare-fun ge (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert (forall ((x Nat)) (= (ge x Z) true)))
(assert (forall ((z Nat)) (= (ge Z (S z)) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (ge (S x2) (S z)) (ge x2 z))))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert-not
  (forall ((x Nat) (y Nat)) (=> (ge x y) (=> (le x y) (equal x y)))))
(check-sat)
