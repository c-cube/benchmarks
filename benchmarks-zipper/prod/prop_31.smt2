(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-fun qrev (list list) list)
(assert (forall ((y list)) (= (qrev nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (qrev (cons z xs) y) (qrev xs (cons z y)))))
(assert-not (forall ((x list)) (= (qrev (qrev x nil) nil) x)))
(check-sat)
