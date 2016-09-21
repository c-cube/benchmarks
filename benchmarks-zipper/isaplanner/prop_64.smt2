(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun last (list) Nat)
(declare-fun append (list list) list)
(assert (= (last nil) Z))
(assert (forall ((y Nat)) (= (last (cons y nil)) y)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (last (cons y (cons x2 x3))) (last (cons x2 x3)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert-not
  (forall ((x Nat) (xs list)) (= (last (append xs (cons x nil))) x)))
(check-sat)
