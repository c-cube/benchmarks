(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (forall ((x Nat)) (= (lt x Z) false)))
(assert (forall ((z Nat)) (= (lt Z (S z)) true)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (lt (S x2) (S z)) (lt x2 z))))
(assert-not (forall ((i Nat) (m Nat)) (lt i (S (plus i m)))))
(check-sat)
