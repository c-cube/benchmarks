(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun even (Nat) Bool)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (= (even Z) true))
(assert (= (even (S Z)) false))
(assert (forall ((z Nat)) (= (even (S (S z))) (even z))))
(assert-not
  (forall ((x Nat) (y Nat)) (= (even (plus x y)) (even (plus y x)))))
(check-sat)
