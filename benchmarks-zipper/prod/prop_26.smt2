(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun half (Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (= (half Z) Z))
(assert (= (half (S Z)) Z))
(assert (forall ((z Nat)) (= (half (S (S z))) (S (half z)))))
(assert-not
  (forall ((x Nat) (y Nat)) (= (half (plus x y)) (half (plus y x)))))
(check-sat)
