(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun min2 (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (min2 Z y) Z)))
(assert (forall ((z Nat)) (= (min2 (S z) Z) Z)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (min2 (S z) (S y2)) (S (min2 z y2)))))
(assert-not
  (forall ((a Nat) (b Nat) (c Nat))
    (= (min2 (min2 a b) c) (min2 a (min2 b c)))))
(check-sat)
