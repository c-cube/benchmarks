; Stooge sort defined using reverse
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  (par (a)
    (ztake
       ((x Int) (y (list a))) (list a)
       (ite
         (= x 0) (as nil (list a))
         (match y
           (case nil (as nil (list a)))
           (case (cons z xs) (cons z (ztake (- x 1) xs))))))))
(define-fun-rec
  (par (a)
    (zlength
       ((x (list a))) Int
       (match x
         (case nil 0)
         (case (cons y xs) (+ 1 (zlength xs)))))))
(define-fun-rec
  (par (a)
    (zdrop
       ((x Int) (y (list a))) (list a)
       (ite
         (= x 0) y
         (match y
           (case nil (as nil (list a)))
           (case (cons z xs1) (zdrop (- x 1) xs1)))))))
(define-fun
  (par (a)
    (zsplitAt
       ((x Int) (y (list a))) (Pair (list a) (list a))
       (Pair2 (ztake x y) (zdrop x y)))))
(define-fun-rec
  zcount
    ((x Int) (y (list Int))) Nat
    (match y
      (case nil Z)
      (case (cons z xs) (ite (= x z) (S (zcount x xs)) (zcount x xs)))))
(define-fun
  sort2
    ((x Int) (y Int)) (list Int)
    (ite
      (<= x y) (cons x (cons y (as nil (list Int))))
      (cons y (cons x (as nil (list Int))))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case nil y)
         (case (cons z xs) (cons z (append xs y)))))))
(define-fun-rec
  (par (a)
    (reverse
       ((x (list a))) (list a)
       (match x
         (case nil (as nil (list a)))
         (case (cons y xs)
           (append (reverse xs) (cons y (as nil (list a)))))))))
(define-funs-rec
  ((stooge1sort2 ((x (list Int))) (list Int))
   (stoogesort ((x (list Int))) (list Int))
   (stooge1sort1 ((x (list Int))) (list Int)))
  ((match (zsplitAt (div (zlength x) 3) (reverse x))
     (case (Pair2 ys zs) (append (stoogesort zs) (reverse ys))))
   (match x
     (case nil (as nil (list Int)))
     (case (cons y z)
       (match z
         (case nil (cons y (as nil (list Int))))
         (case (cons y2 x2)
           (match x2
             (case nil (sort2 y y2))
             (case (cons x3 x4)
               (stooge1sort2 (stooge1sort1 (stooge1sort2 x)))))))))
   (match (zsplitAt (div (zlength x) 3) x)
     (case (Pair2 ys zs) (append ys (stoogesort zs))))))
(assert-not
  (forall ((x Int) (y (list Int)))
    (= (zcount x (stoogesort y)) (zcount x y))))
(check-sat)
