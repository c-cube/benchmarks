(declare-sort sk 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk) (tail2 list2)))))
(declare-datatypes () ((Pair (Pair2 (first sk) (second sk)))))
(declare-datatypes ()
  ((list (nil) (cons (head Pair) (tail list)))))
(declare-fun zip (list2 list2) list)
(declare-fun zipConcat (sk list2 list2) list)
(assert (forall ((y list2)) (= (zip nil2 y) nil)))
(assert
  (forall ((z sk) (x2 list2)) (= (zip (cons2 z x2) nil2) nil)))
(assert
  (forall ((z sk) (x2 list2) (x3 sk) (x4 list2))
    (= (zip (cons2 z x2) (cons2 x3 x4))
      (cons (Pair2 z x3) (zip x2 x4)))))
(assert (forall ((x sk) (y list2)) (= (zipConcat x y nil2) nil)))
(assert
  (forall ((x sk) (y list2) (y2 sk) (ys list2))
    (= (zipConcat x y (cons2 y2 ys)) (cons (Pair2 x y2) (zip y ys)))))
(assert-not
  (forall ((x sk) (xs list2) (ys list2))
    (= (zip (cons2 x xs) ys) (zipConcat x xs ys))))
(check-sat)
