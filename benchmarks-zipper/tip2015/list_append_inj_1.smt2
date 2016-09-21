(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-fun append (list list) list)
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert-not
  (forall ((xs list) (ys list) (zs list))
    (=> (= (append xs zs) (append ys zs)) (= xs ys))))
(check-sat)
