(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun add3 (Nat Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (forall ((z Nat)) (= (add3 Z Z z) z)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (add3 Z (S y2) z) (S (add3 Z y2 z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3 (S x2) y z) (S (add3 x2 y z)))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (= (add3 x y z) (plus x (plus y z)))))
(check-sat)
