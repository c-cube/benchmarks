(declare-sort sk 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk) (tail2 list2)))))
(declare-datatypes ()
  ((Tree (Node (Node_0 Tree) (Node_1 sk) (Node_2 Tree)) (Nil))))
(declare-datatypes ()
  ((list (nil) (cons (head Tree) (tail list)))))
(declare-fun flatten1 (list) list2)
(declare-fun append (list2 list2) list2)
(declare-fun flatten0 (Tree) list2)
(assert (= (flatten1 nil) nil2))
(assert
  (forall ((ps list) (x2 sk) (q Tree) (x3 Tree) (x4 sk) (x5 Tree))
    (= (flatten1 (cons (Node (Node x3 x4 x5) x2 q) ps))
      (flatten1 (cons (Node x3 x4 x5) (cons (Node Nil x2 q) ps))))))
(assert
  (forall ((ps list) (x2 sk) (q Tree))
    (= (flatten1 (cons (Node Nil x2 q) ps))
      (cons2 x2 (flatten1 (cons q ps))))))
(assert
  (forall ((ps list)) (= (flatten1 (cons Nil ps)) (flatten1 ps))))
(assert (forall ((y list2)) (= (append nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (append (cons2 z xs) y) (cons2 z (append xs y)))))
(assert
  (forall ((p Tree) (y sk) (q Tree))
    (= (flatten0 (Node p y q))
      (append (append (flatten0 p) (cons2 y nil2)) (flatten0 q)))))
(assert (= (flatten0 Nil) nil2))
(assert-not
  (forall ((p Tree)) (= (flatten1 (cons p nil)) (flatten0 p))))
(check-sat)