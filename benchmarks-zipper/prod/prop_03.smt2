(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun length (list) Nat)
(declare-fun append (list list) list)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (= (length nil) Z))
(assert
  (forall ((y sk) (xs list))
    (= (length (cons y xs)) (S (length xs)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert-not
  (forall ((x list) (y list))
    (= (length (append x y)) (plus (length y) (length x)))))
(check-sat)
