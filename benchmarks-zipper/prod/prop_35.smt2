(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-const one Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun qexp (Nat Nat Nat) Nat)
(declare-fun exp (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (= one (S Z)))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (z Nat)) (= (mult (S z) y) (plus y (mult z y)))))
(assert (forall ((x Nat) (z Nat)) (= (qexp x Z z) z)))
(assert
  (forall ((x Nat) (z Nat) (n Nat))
    (= (qexp x (S n) z) (qexp x n (mult x z)))))
(assert (forall ((x Nat)) (= (exp x Z) (S Z))))
(assert
  (forall ((x Nat) (n Nat)) (= (exp x (S n)) (mult x (exp x n)))))
(assert-not
  (forall ((x Nat) (y Nat)) (= (exp x y) (qexp x y one))))
(check-sat)
