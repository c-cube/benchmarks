(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-fun qrev (list list) list)
(declare-fun append (list list) list)
(declare-fun rev (list) list)
(assert (forall ((y list)) (= (qrev nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (qrev (cons z xs) y) (qrev xs (cons z y)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (= (rev nil) nil))
(assert
  (forall ((y sk) (xs list))
    (= (rev (cons y xs)) (append (rev xs) (cons y nil)))))
(assert-not (forall ((x list)) (= (rev (qrev x nil)) x)))
(check-sat)
