(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-fun append (list list) list)
(declare-fun rev (list) list)
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (= (rev nil) nil))
(assert
  (forall ((y sk) (xs list))
    (= (rev (cons y xs)) (append (rev xs) (cons y nil)))))
(assert-not
  (forall ((x list) (y list))
    (= (rev (rev (append x y))) (append (rev (rev x)) (rev (rev y))))))
(check-sat)
