; Source: IsaPlanner test suite
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a b) ((Pair2 (Pair (first a) (second b)))))
(define-funs-rec
  ((par (a b) (zip ((x (list a)) (y (list b))) (list (Pair2 a b)))))
  ((match x
     (case nil (as nil (list (Pair2 a b))))
     (case (cons z x2)
       (match y
         (case nil (as nil (list (Pair2 a b))))
         (case (cons x3 x4)
           (cons (Pair z x3) (as (zip x2 x4) (list (Pair2 a b))))))))))
(assert-not
  (par (b a)
    (forall ((xs (list b)))
      (= (zip (as nil (list a)) xs) (as nil (list (Pair2 a b)))))))
(check-sat)
