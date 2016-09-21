(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun deleteAll (Nat list) list)
(declare-fun nub (list) list)
(declare-fun count (Nat list) Nat)
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
(assert (forall ((x Nat)) (= (deleteAll x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true)
      (= (deleteAll x (cons z xs)) (deleteAll x xs)))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false)
      (= (deleteAll x (cons z xs)) (cons z (deleteAll x xs))))))
(assert (= (nub nil) nil))
(assert
  (forall ((y Nat) (xs list))
    (= (nub (cons y xs)) (cons y (deleteAll y (nub xs))))))
(assert (forall ((x Nat)) (= (count x nil) Z)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) true)
      (= (count x (cons z ys)) (S (count x ys))))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) false) (= (count x (cons z ys)) (count x ys)))))
(assert-not
  (forall ((x Nat) (xs list))
    (=> (elem x xs) (= (count x (nub xs)) (S Z)))))
(check-sat)
