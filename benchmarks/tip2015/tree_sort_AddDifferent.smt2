; Tree sort
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a)
  ((Tree (Node (Node_0 (Tree a)) (Node_1 a) (Node_2 (Tree a)))
     (Nil))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-funs-rec
  ((le ((x Nat) (y Nat)) bool))
  ((match x
     (case Z true)
     (case (S z)
       (match y
         (case Z false)
         (case (S x2) (le z x2)))))))
(define-funs-rec
  ((par (a) (flatten ((x (Tree a)) (y (list a))) (list a))))
  ((match x
     (case (Node q z q2)
       (as (flatten q (cons z (as (flatten q2 y) (list a)))) (list a)))
     (case Nil y))))
(define-funs-rec
  ((equal ((x Nat) (y Nat)) bool))
  ((match x
     (case Z
       (match y
         (case Z true)
         (case (S z) false)))
     (case (S x2)
       (match y
         (case Z false)
         (case (S y2) (equal x2 y2)))))))
(define-funs-rec
  ((count ((x Nat) (y (list Nat))) Nat))
  ((match y
     (case nil Z)
     (case (cons z xs)
       (ite (equal x z) (S (count x xs)) (count x xs))))))
(define-funs-rec
  ((add ((x Nat) (y (Tree Nat))) (Tree Nat)))
  ((match y
     (case (Node q z q2)
       (ite (le x z) (Node (add x q) z q2) (Node q z (add x q2))))
     (case Nil (Node y x y)))))
(assert-not
  (forall ((x Nat) (y Nat) (t (Tree Nat)))
    (=> (not (equal x y))
      (= (count y (flatten (add x t) (as nil (list Nat))))
        (count y (flatten t (as nil (list Nat))))))))
(check-sat)
