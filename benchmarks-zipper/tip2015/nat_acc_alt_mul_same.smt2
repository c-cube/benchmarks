(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun acc_plus (Nat Nat) Nat)
(declare-fun acc_alt_mul (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (n Nat)) (= (mult (S n) y) (plus y (mult n y)))))
(assert (forall ((y Nat)) (= (acc_plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat))
    (= (acc_plus (S z) y) (acc_plus z (S y)))))
(assert (forall ((y Nat)) (= (acc_alt_mul Z y) Z)))
(assert (forall ((z Nat)) (= (acc_alt_mul (S z) Z) Z)))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (acc_alt_mul (S z) (S x2))
      (S (acc_plus z (acc_plus x2 (acc_alt_mul z x2)))))))
(assert-not
  (forall ((x Nat) (y Nat)) (= (acc_alt_mul x y) (mult x y))))
(check-sat)
