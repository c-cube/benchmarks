(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun length (list) Nat)
(declare-fun append (list list) list)
(declare-fun rotate (Nat list) list)
(assert (= (length nil) Z))
(assert
  (forall ((y sk) (xs list))
    (= (length (cons y xs)) (S (length xs)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (forall ((y list)) (= (rotate Z y) y)))
(assert (forall ((z Nat)) (= (rotate (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (rotate (S z) (cons x2 x3))
      (rotate z (append x3 (cons x2 nil))))))
(assert-not
  (forall ((x list) (y list))
    (= (rotate (length x) (append x y)) (append y x))))
(check-sat)
