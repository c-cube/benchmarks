; Selection sort, using a total minimum function
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(define-funs-rec
  ((ssort_minimum ((x Int) (y (list Int))) Int))
  ((match y
     (case nil x)
     (case (cons z ys)
       (ite (<= z x) (ssort_minimum z ys) (ssort_minimum x ys))))))
(define-funs-rec
  ((ordered ((x (list Int))) Bool))
  ((match x
     (case nil true)
     (case (cons y z)
       (match z
         (case nil true)
         (case (cons y2 xs) (and (<= y y2) (ordered z))))))))
(define-funs-rec
  ((delete ((x Int) (y (list Int))) (list Int)))
  ((match y
     (case nil (as nil (list Int)))
     (case (cons z ys) (ite (= x z) ys (cons z (delete x ys)))))))
(define-funs-rec
  ((ssort ((x (list Int))) (list Int)))
  ((match x
     (case nil (as nil (list Int)))
     (case (cons y ys)
       (let (((m Int) (ssort_minimum y ys)))
         (cons m (ssort (delete m x))))))))
(assert-not (forall ((x (list Int))) (ordered (ssort x))))
(check-sat)