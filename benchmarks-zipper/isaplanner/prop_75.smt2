(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun equal (Nat Nat) Bool)
(declare-fun count (Nat list) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert (forall ((x Nat)) (= (count x nil) Z)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) true)
      (= (count x (cons z ys)) (S (count x ys))))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) false) (= (count x (cons z ys)) (count x ys)))))
(assert-not
  (forall ((n Nat) (m Nat) (xs list))
    (= (plus (count n xs) (count n (cons m nil)))
      (count n (cons m xs)))))
(check-sat)
