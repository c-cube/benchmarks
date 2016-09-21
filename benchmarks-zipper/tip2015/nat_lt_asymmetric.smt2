(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun lt (Nat Nat) Bool)
(assert (forall ((x Nat)) (= (lt x Z) false)))
(assert (forall ((z Nat)) (= (lt Z (S z)) true)))
(assert (forall ((z Nat) (n Nat)) (= (lt (S n) (S z)) (lt n z))))
(assert-not
  (forall ((x Nat) (y Nat)) (=> (lt x y) (not (lt y x)))))
(check-sat)
