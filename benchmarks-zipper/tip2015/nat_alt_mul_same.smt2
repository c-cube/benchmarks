(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun alt_mul (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (n Nat)) (= (mult (S n) y) (plus y (mult n y)))))
(assert (forall ((y Nat)) (= (alt_mul Z y) Z)))
(assert (forall ((z Nat)) (= (alt_mul (S z) Z) Z)))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (alt_mul (S z) (S x2)) (S (plus (plus (alt_mul z x2) z) x2)))))
(assert-not
  (forall ((x Nat) (y Nat)) (= (alt_mul x y) (mult x y))))
(check-sat)
