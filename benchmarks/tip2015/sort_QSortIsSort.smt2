; QuickSort
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  insert2
    ((x Int) (y (list Int))) (list Int)
    (match y
      (case nil (cons x (as nil (list Int))))
      (case (cons z xs)
        (ite (<= x z) (cons x y) (cons z (insert2 x xs))))))
(define-fun-rec
  isort
    ((x (list Int))) (list Int)
    (match x
      (case nil (as nil (list Int)))
      (case (cons y xs) (insert2 y (isort xs)))))
(define-fun-rec
  (par (a)
    (filter
       ((x (=> a Bool)) (y (list a))) (list a)
       (match y
         (case nil (as nil (list a)))
         (case (cons z xs)
           (ite (@ x z) (cons z (filter x xs)) (filter x xs)))))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case nil y)
         (case (cons z xs) (cons z (append xs y)))))))
(define-fun-rec
  qsort
    ((x (list Int))) (list Int)
    (match x
      (case nil (as nil (list Int)))
      (case (cons y xs)
        (append
          (append (qsort (filter (lambda ((z Int)) (<= z y)) xs))
            (cons y (as nil (list Int))))
          (qsort (filter (lambda ((x2 Int)) (> x2 y)) xs))))))
(assert-not (forall ((x (list Int))) (= (qsort x) (isort x))))
(check-sat)
