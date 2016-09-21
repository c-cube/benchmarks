(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun acc_plus (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (acc_plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat))
    (= (acc_plus (S z) y) (acc_plus z (S y)))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (= (acc_plus x (acc_plus y z)) (acc_plus (acc_plus x y) z))))
(check-sat)
