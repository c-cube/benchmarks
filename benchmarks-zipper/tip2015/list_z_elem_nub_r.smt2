(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun zelem (Nat list) Bool)
(declare-fun zdeleteAll (Nat list) list)
(declare-fun znub (list) list)
(declare-fun equal (Nat Nat) Bool)
(assert (forall ((x Nat)) (= (zelem x nil) false)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (= (zelem x (cons z ys)) (or (equal x z) (zelem x ys)))))
(assert (forall ((x Nat)) (= (zdeleteAll x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true)
      (= (zdeleteAll x (cons z xs)) (zdeleteAll x xs)))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false)
      (= (zdeleteAll x (cons z xs)) (cons z (zdeleteAll x xs))))))
(assert (= (znub nil) nil))
(assert
  (forall ((y Nat) (xs list))
    (= (znub (cons y xs)) (cons y (zdeleteAll y (znub xs))))))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert-not
  (forall ((x Nat) (xs list)) (=> (zelem x (znub xs)) (zelem x xs))))
(check-sat)
