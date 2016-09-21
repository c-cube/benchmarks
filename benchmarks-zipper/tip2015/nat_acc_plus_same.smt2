(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun acc_plus (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (forall ((y Nat)) (= (acc_plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat))
    (= (acc_plus (S z) y) (acc_plus z (S y)))))
(assert-not
  (forall ((x Nat) (y Nat)) (= (plus x y) (acc_plus x y))))
(check-sat)
