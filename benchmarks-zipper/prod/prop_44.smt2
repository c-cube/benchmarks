(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun intersect2 (list list) list)
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert (forall ((x Nat)) (= (elem x nil) false)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (= (elem x (cons z xs)) (or (equal x z) (elem x xs)))))
(assert (forall ((y list)) (= (intersect2 nil y) nil)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (=> (= (elem z y) true)
      (= (intersect2 (cons z xs) y) (cons z (intersect2 xs y))))))
(assert
  (forall ((y list) (z Nat) (xs list))
    (=> (= (elem z y) false)
      (= (intersect2 (cons z xs) y) (intersect2 xs y)))))
(assert-not
  (forall ((x Nat) (y list) (z list))
    (=> (elem x y) (=> (elem x z) (elem x (intersect2 y z))))))
(check-sat)
