; Source: IsaPlanner test suite
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a b) ((Pair2 (Pair (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-funs-rec
  ((par (a b) (zip ((x (list a)) (y (list b))) (list (Pair2 a b)))))
  ((match x
     (case nil (as nil (list (Pair2 a b))))
     (case (cons z x2)
       (match y
         (case nil (as nil (list (Pair2 a b))))
         (case (cons x3 x4)
           (cons (Pair z x3) (as (zip x2 x4) (list (Pair2 a b))))))))))
(define-funs-rec
  ((par (a) (take ((x Nat) (y (list a))) (list a))))
  ((match x
     (case Z (as nil (list a)))
     (case (S z)
       (match y
         (case nil y)
         (case (cons x2 x3) (cons x2 (as (take z x3) (list a)))))))))
(define-funs-rec
  ((par (a) (len ((x (list a))) Nat)))
  ((match x
     (case nil Z)
     (case (cons y xs) (S (as (len xs) Nat))))))
(define-funs-rec
  ((par (a) (drop ((x Nat) (y (list a))) (list a))))
  ((match x
     (case Z y)
     (case (S z)
       (match y
         (case nil y)
         (case (cons x2 x3) (as (drop z x3) (list a))))))))
(define-funs-rec
  ((par (a) (append ((x (list a)) (y (list a))) (list a))))
  ((match x
     (case nil y)
     (case (cons z xs) (cons z (as (append xs y) (list a)))))))
(assert-not
  (par (a b)
    (forall ((xs (list a)) (ys (list a)) (zs (list b)))
      (= (zip (append xs ys) zs)
        (append (zip xs (take (len xs) zs))
          (zip ys (drop (len xs) zs)))))))
(check-sat)
