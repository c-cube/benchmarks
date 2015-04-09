; Source: Productive use of failure
(declare-datatypes
  (a) ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-funs-rec
  ((par (a2) (length ((x (list a2))) Nat)))
  ((match x
     (case nil Z)
     (case (cons ds xs) (S (as (length xs) Nat))))))
(define-funs-rec
  ((half ((x2 Nat)) Nat))
  ((match x2
     (case Z x2)
     (case
       (S ds2)
       (match ds2
         (case Z ds2)
         (case (S x3) (S (half x3))))))))
(define-funs-rec
  ((par (a3) (append ((x4 (list a3)) (x5 (list a3))) (list a3))))
  ((match x4
     (case nil x5)
     (case (cons x6 xs2) (cons x6 (as (append xs2 x5) (list a3)))))))
(declare-sort a4 0)
(assert
  (not
    (forall
      ((x7 (list a4)) (y (list a4)))
      (= (half (length (append x7 y))) (half (length (append y x7)))))))
(check-sat)