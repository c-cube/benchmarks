(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun le (Nat Nat) Bool)
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (=> (le x y) (=> (le y z) (le x z)))))
(check-sat)