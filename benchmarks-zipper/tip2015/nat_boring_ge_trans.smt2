(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun ge (Nat Nat) Bool)
(assert (forall ((x Nat)) (= (ge x Z) true)))
(assert (forall ((z Nat)) (= (ge Z (S z)) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (ge (S x2) (S z)) (ge x2 z))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (=> (ge x y) (=> (ge y z) (ge x z)))))
(check-sat)
