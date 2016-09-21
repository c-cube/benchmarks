(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun min2 (Nat Nat) Nat)
(declare-fun max2 (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (min2 Z y) Z)))
(assert (forall ((z Nat)) (= (min2 (S z) Z) Z)))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (min2 (S z) (S x2)) (S (min2 z x2)))))
(assert (forall ((y Nat)) (= (max2 Z y) y)))
(assert (forall ((z Nat)) (= (max2 (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (max2 (S z) (S x2)) (S (max2 z x2)))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (= (min2 x (max2 y z)) (max2 (min2 x y) (min2 x z)))))
(check-sat)
