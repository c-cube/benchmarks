(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun gt (Nat Nat) Bool)
(assert (forall ((y Nat)) (= (gt Z y) false)))
(assert (forall ((z Nat)) (= (gt (S z) Z) true)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (gt (S z) (S x2)) (gt z x2))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (=> (gt x y) (=> (gt y z) (gt x z)))))
(check-sat)
