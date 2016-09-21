(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-fun butlast (list) list)
(declare-fun append (list list) list)
(declare-fun butlastConcat (list list) list)
(assert (= (butlast nil) nil))
(assert (forall ((y sk)) (= (butlast (cons y nil)) nil)))
(assert
  (forall ((y sk) (x2 sk) (x3 list))
    (= (butlast (cons y (cons x2 x3)))
      (cons y (butlast (cons x2 x3))))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (forall ((x list)) (= (butlastConcat x nil) (butlast x))))
(assert
  (forall ((x list) (z sk) (x2 list))
    (= (butlastConcat x (cons z x2))
      (append x (butlast (cons z x2))))))
(assert-not
  (forall ((xs list) (ys list))
    (= (butlast (append xs ys)) (butlastConcat xs ys))))
(check-sat)
