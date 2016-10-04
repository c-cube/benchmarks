(declare-sort sk 0)
(declare-fun m (Int) Int)
(assert
  (forall ((x Int)) (=> (= (> x 100) true) (= (m x) (- x 10)))))
(assert
  (forall ((x Int))
    (=> (= (> x 100) false) (= (m x) (m (m (+ x 11)))))))
(assert-not (forall ((n Int)) (=> (>= n 101) (= (m n) (- n 10)))))
(check-sat)