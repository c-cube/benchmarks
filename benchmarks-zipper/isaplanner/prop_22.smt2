(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun max2 (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (max2 Z y) y)))
(assert (forall ((z Nat)) (= (max2 (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (max2 (S z) (S x2)) (S (max2 z x2)))))
(assert-not
  (forall ((a Nat) (b Nat) (c Nat))
    (= (max2 (max2 a b) c) (max2 a (max2 b c)))))
(check-sat)
