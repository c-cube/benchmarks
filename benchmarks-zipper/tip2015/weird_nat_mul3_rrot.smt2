(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun add3 (Nat Nat Nat) Nat)
(declare-fun mul3 (Nat Nat Nat) Nat)
(assert (forall ((z Nat)) (= (add3 Z Z z) z)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (add3 Z (S y2) z) (S (add3 Z y2 z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3 (S x2) y z) (S (add3 x2 y z)))))
(assert (forall ((y Nat) (z Nat)) (= (mul3 Z y z) Z)))
(assert (forall ((z Nat) (x2 Nat)) (= (mul3 (S x2) Z z) Z)))
(assert (forall ((x2 Nat) (x3 Nat)) (= (mul3 (S x2) (S x3) Z) Z)))
(assert (= (mul3 (S Z) (S Z) (S Z)) (S Z)))
(assert
  (forall ((x5 Nat))
    (= (mul3 (S Z) (S Z) (S (S x5)))
      (S
        (add3 (mul3 Z Z (S x5))
          (add3 (mul3 (S Z) Z (S x5)) (mul3 Z (S Z) (S x5)) (mul3 Z Z (S Z)))
          (add3 Z Z (S x5)))))))
(assert
  (forall ((x4 Nat) (x6 Nat))
    (= (mul3 (S Z) (S (S x6)) (S x4))
      (S
        (add3 (mul3 Z (S x6) x4)
          (add3 (mul3 (S Z) (S x6) x4)
            (mul3 Z (S Z) x4) (mul3 Z (S x6) (S Z)))
          (add3 Z (S x6) x4))))))
(assert
  (forall ((x3 Nat) (x4 Nat) (x7 Nat))
    (= (mul3 (S (S x7)) (S x3) (S x4))
      (S
        (add3 (mul3 (S x7) x3 x4)
          (add3 (mul3 (S Z) x3 x4)
            (mul3 (S x7) (S Z) x4) (mul3 (S x7) x3 (S Z)))
          (add3 (S x7) x3 x4))))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 z x y))))
(check-sat)
