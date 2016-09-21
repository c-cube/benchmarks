(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-const ^1 Nat)
(declare-fun pow (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (n Nat)) (= (mult (S n) y) (plus y (mult n y)))))
(assert (= ^1 (S Z)))
(assert (forall ((x Nat)) (= (pow x Z) ^1)))
(assert
  (forall ((x Nat) (m Nat)) (= (pow x (S m)) (mult x (pow x m)))))
(assert-not
  (forall ((n Nat) (x Nat) (y Nat) (z Nat))
    (distinct
      (plus (pow (S x) (S (S (S n)))) (pow (S y) (S (S (S n)))))
      (pow (S z) (S (S (S n)))))))
(check-sat)
