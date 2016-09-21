(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert-not (forall ((x Nat)) (= (plus x (S x)) (S (plus x x)))))
(check-sat)
