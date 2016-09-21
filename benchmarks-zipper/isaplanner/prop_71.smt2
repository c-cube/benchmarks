(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun ins (Nat list) list)
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(assert (forall ((x Nat)) (= (lt x Z) false)))
(assert (forall ((z Nat)) (= (lt Z (S z)) true)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (lt (S x2) (S z)) (lt x2 z))))
(assert (forall ((x Nat)) (= (ins x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (lt x z) true)
      (= (ins x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (lt x z) false)
      (= (ins x (cons z xs)) (cons z (ins x xs))))))
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
(assert-not
  (forall ((x Nat) (y Nat) (xs list))
    (=> (not (equal x y)) (= (elem x (ins y xs)) (elem x xs)))))
(check-sat)
