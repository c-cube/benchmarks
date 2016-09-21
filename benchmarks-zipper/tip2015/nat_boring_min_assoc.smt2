(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun min2 (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (min2 Z y) Z)))
(assert (forall ((z Nat)) (= (min2 (S z) Z) Z)))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (min2 (S z) (S x2)) (S (min2 z x2)))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (= (min2 x (min2 y z)) (min2 (min2 x y) z))))
(check-sat)
