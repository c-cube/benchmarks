(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun len (list) Nat)
(declare-fun ins (Nat list) list)
(assert (forall ((x Nat)) (= (lt x Z) false)))
(assert (forall ((z Nat)) (= (lt Z (S z)) true)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (lt (S x2) (S z)) (lt x2 z))))
(assert (= (len nil) Z))
(assert
  (forall ((y Nat) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (forall ((x Nat)) (= (ins x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (lt x z) true)
      (= (ins x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (lt x z) false)
      (= (ins x (cons z xs)) (cons z (ins x xs))))))
(assert-not
  (forall ((x Nat) (xs list)) (= (len (ins x xs)) (S (len xs)))))
(check-sat)
