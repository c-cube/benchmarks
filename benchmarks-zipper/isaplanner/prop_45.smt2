(declare-sort sk 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk) (tail2 list2)))))
(declare-datatypes () ((Pair (Pair2 (first sk) (second sk)))))
(declare-datatypes ()
  ((list (nil) (cons (head Pair) (tail list)))))
(declare-fun zip (list2 list2) list)
(assert (forall ((y list2)) (= (zip nil2 y) nil)))
(assert
  (forall ((z sk) (x2 list2)) (= (zip (cons2 z x2) nil2) nil)))
(assert
  (forall ((z sk) (x2 list2) (x3 sk) (x4 list2))
    (= (zip (cons2 z x2) (cons2 x3 x4))
      (cons (Pair2 z x3) (zip x2 x4)))))
(assert-not
  (forall ((x sk) (y sk) (xs list2) (ys list2))
    (= (zip (cons2 x xs) (cons2 y ys))
      (cons (Pair2 x y) (zip xs ys)))))
(check-sat)
