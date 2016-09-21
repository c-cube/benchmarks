(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun add3acc (Nat Nat Nat) Nat)
(declare-fun mul2 (Nat Nat) Nat)
(assert (forall ((z Nat)) (= (add3acc Z Z z) z)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (add3acc Z (S y2) z) (add3acc Z y2 (S z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3acc (S x2) y z) (add3acc x2 (S y) z))))
(assert (forall ((y Nat)) (= (mul2 Z y) Z)))
(assert (forall ((z Nat)) (= (mul2 (S z) Z) Z)))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (mul2 (S z) (S x2)) (S (add3acc z x2 (mul2 z x2))))))
(assert-not (forall ((x Nat) (y Nat)) (= (mul2 x y) (mul2 y x))))
(check-sat)
