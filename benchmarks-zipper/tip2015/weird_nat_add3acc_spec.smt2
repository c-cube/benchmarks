(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun add3acc (Nat Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (forall ((z Nat)) (= (add3acc Z Z z) z)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (add3acc Z (S y2) z) (add3acc Z y2 (S z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3acc (S x2) y z) (add3acc x2 (S y) z))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (= (add3acc x y z) (plus x (plus y z)))))
(check-sat)
