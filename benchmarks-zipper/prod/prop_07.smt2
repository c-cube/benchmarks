(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun qrev (list list) list)
(declare-fun plus (Nat Nat) Nat)
(declare-fun length (list) Nat)
(assert (forall ((y list)) (= (qrev nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (qrev (cons z xs) y) (qrev xs (cons z y)))))
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (S z) y) (S (plus z y)))))
(assert (= (length nil) Z))
(assert
  (forall ((y sk) (xs list))
    (= (length (cons y xs)) (S (length xs)))))
(assert-not
  (forall ((x list) (y list))
    (= (length (qrev x y)) (plus (length x) (length y)))))
(check-sat)
