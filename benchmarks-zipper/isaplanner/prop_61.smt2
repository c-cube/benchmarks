(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun last (list) Nat)
(declare-fun lastOfTwo (list list) Nat)
(declare-fun append (list list) list)
(assert (= (last nil) Z))
(assert (forall ((y Nat)) (= (last (cons y nil)) y)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (last (cons y (cons x2 x3))) (last (cons x2 x3)))))
(assert (forall ((x list)) (= (lastOfTwo x nil) (last x))))
(assert
  (forall ((x list) (z Nat) (x2 list))
    (= (lastOfTwo x (cons z x2)) (last (cons z x2)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert-not
  (forall ((xs list) (ys list))
    (= (last (append xs ys)) (lastOfTwo xs ys))))
(check-sat)
