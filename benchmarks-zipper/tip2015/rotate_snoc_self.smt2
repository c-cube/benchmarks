(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun snoc (sk list) list)
(declare-fun rotate (Nat list) list)
(declare-fun append (list list) list)
(assert (forall ((x sk)) (= (snoc x nil) (cons x nil))))
(assert
  (forall ((x sk) (z sk) (ys list))
    (= (snoc x (cons z ys)) (cons z (snoc x ys)))))
(assert (forall ((y list)) (= (rotate Z y) y)))
(assert (forall ((z Nat)) (= (rotate (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (rotate (S z) (cons x2 x3)) (rotate z (snoc x2 x3)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert-not
  (forall ((n Nat) (xs list))
    (= (rotate n (append xs xs))
      (append (rotate n xs) (rotate n xs)))))
(check-sat)
