(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun add3acc (Nat Nat Nat) Nat)
(assert (forall ((z Nat)) (= (add3acc Z Z z) z)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (add3acc Z (S y2) z) (add3acc Z y2 (S z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3acc (S x2) y z) (add3acc x2 (S y) z))))
(assert-not
  (forall ((x1 Nat) (x2 Nat) (x3 Nat) (x4 Nat) (x5 Nat))
    (= (add3acc (add3acc x1 x2 x3) x4 x5)
      (add3acc x1 (add3acc x2 x3 x4) x5))))
(check-sat)
