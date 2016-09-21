(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun le (Nat Nat) Bool)
(declare-fun insert2 (Nat list) list)
(declare-fun isort (list) list)
(declare-fun equal (Nat Nat) Bool)
(declare-fun count (Nat list) Nat)
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert (forall ((x Nat)) (= (insert2 x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (le x z) true)
      (= (insert2 x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (le x z) false)
      (= (insert2 x (cons z xs)) (cons z (insert2 x xs))))))
(assert (= (isort nil) nil))
(assert
  (forall ((y Nat) (xs list))
    (= (isort (cons y xs)) (insert2 y (isort xs)))))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert (forall ((x Nat)) (= (count x nil) Z)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true)
      (= (count x (cons z xs)) (S (count x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false) (= (count x (cons z xs)) (count x xs)))))
(assert-not
  (forall ((x Nat) (y list)) (= (count x (isort y)) (count x y))))
(check-sat)
