(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun add3acc (Nat Nat Nat) Nat)
(declare-fun mul3acc (Nat Nat Nat) Nat)
(assert (forall ((z Nat)) (= (add3acc Z Z z) z)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (add3acc Z (S y2) z) (add3acc Z y2 (S z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3acc (S x2) y z) (add3acc x2 (S y) z))))
(assert (forall ((y Nat) (z Nat)) (= (mul3acc Z y z) Z)))
(assert (forall ((z Nat) (x2 Nat)) (= (mul3acc (S x2) Z z) Z)))
(assert
  (forall ((x2 Nat) (x3 Nat)) (= (mul3acc (S x2) (S x3) Z) Z)))
(assert (= (mul3acc (S Z) (S Z) (S Z)) (S Z)))
(assert
  (forall ((x5 Nat))
    (= (mul3acc (S Z) (S Z) (S (S x5)))
      (S
        (add3acc (mul3acc Z Z (S x5))
          (add3acc (mul3acc (S Z) Z (S x5))
            (mul3acc Z (S Z) (S x5)) (mul3acc Z Z (S Z)))
          (add3acc Z Z (S x5)))))))
(assert
  (forall ((x4 Nat) (x6 Nat))
    (= (mul3acc (S Z) (S (S x6)) (S x4))
      (S
        (add3acc (mul3acc Z (S x6) x4)
          (add3acc (mul3acc (S Z) (S x6) x4)
            (mul3acc Z (S Z) x4) (mul3acc Z (S x6) (S Z)))
          (add3acc Z (S x6) x4))))))
(assert
  (forall ((x3 Nat) (x4 Nat) (x7 Nat))
    (= (mul3acc (S (S x7)) (S x3) (S x4))
      (S
        (add3acc (mul3acc (S x7) x3 x4)
          (add3acc (mul3acc (S Z) x3 x4)
            (mul3acc (S x7) (S Z) x4) (mul3acc (S x7) x3 (S Z)))
          (add3acc (S x7) x3 x4))))))
(assert-not
  (forall ((x1 Nat) (x2 Nat) (x3acc Nat) (x4 Nat) (x5 Nat))
    (= (mul3acc x1 (mul3acc x2 x3acc x4) x5)
      (mul3acc x1 x2 (mul3acc x3acc x4 x5)))))
(check-sat)
