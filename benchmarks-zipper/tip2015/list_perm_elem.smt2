(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun null (list) Bool)
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun delete (Nat list) list)
(declare-fun isPermutation (list list) Bool)
(assert (= (null nil) true))
(assert (forall ((y Nat) (z list)) (= (null (cons y z)) false)))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert (forall ((x Nat)) (= (elem x nil) false)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (= (elem x (cons z ys)) (or (equal x z) (elem x ys)))))
(assert (forall ((x Nat)) (= (delete x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true) (= (delete x (cons z xs)) xs))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false)
      (= (delete x (cons z xs)) (cons z (delete x xs))))))
(assert (forall ((y list)) (= (isPermutation nil y) (null y))))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (isPermutation (cons z xs) y)
      (and (elem z y) (isPermutation xs (delete z y))))))
(assert-not
  (forall ((x Nat) (xs list) (ys list))
    (=> (elem x xs) (=> (isPermutation xs ys) (elem x ys)))))
(check-sat)
