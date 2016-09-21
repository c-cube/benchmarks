(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult2 (Nat Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (forall ((y Nat) (z Nat)) (= (mult2 Z y z) z)))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (mult2 (S x2) y z) (mult2 x2 y (plus y z)))))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (z Nat)) (= (mult (S z) y) (plus y (mult z y)))))
(assert-not
  (forall ((x Nat) (y Nat)) (= (mult x y) (mult2 x y Z))))
(check-sat)
