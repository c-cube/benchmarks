; Property from "Case-Analysis for Rippling and Inductive Proof",
; Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  (par (a b)
    (zip
       ((x (list a)) (y (list b))) (list (Pair a b))
       (match x
         (case nil (as nil (list (Pair a b))))
         (case (cons z x2)
           (match y
             (case nil (as nil (list (Pair a b))))
             (case (cons x3 x4) (cons (Pair2 z x3) (zip x2 x4)))))))))
(define-fun-rec
  (par (a)
    (drop
       ((x Nat) (y (list a))) (list a)
       (match x
         (case Z y)
         (case (S z)
           (match y
             (case nil (as nil (list a)))
             (case (cons x2 x3) (drop z x3))))))))
(assert-not
  (par (a b)
    (forall ((n Nat) (xs (list a)) (ys (list b)))
      (= (drop n (zip xs ys)) (zip (drop n xs) (drop n ys))))))
(check-sat)
