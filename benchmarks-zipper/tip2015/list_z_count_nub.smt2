(declare-datatypes () ((Nat2 (Z) (S (p Nat2)))))
(declare-datatypes () ((Nat (Z2) (S2 (q Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun zelem (Nat list) Bool)
(declare-fun zdeleteAll (Nat list) list)
(declare-fun znub (list) list)
(declare-fun zcount (Nat list) Nat2)
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
(assert (forall ((x Nat)) (= (zcount x nil) Z)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true)
      (= (zcount x (cons z xs)) (S (zcount x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false)
      (= (zcount x (cons z xs)) (zcount x xs)))))
(assert (= (equal Z2 Z2) true))
(assert (forall ((z Nat)) (= (equal Z2 (S2 z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S2 x2) Z2) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S2 x2) (S2 y2)) (equal x2 y2))))
(assert-not
  (forall ((x Nat) (xs list))
    (=> (zelem x xs) (= (zcount x (znub xs)) (S Z)))))
(check-sat)
