; Tree sort
;
; Inserting an element preserves the counts of different elements.
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a)
  ((Tree (Node (Node_0 (Tree a)) (Node_1 a) (Node_2 (Tree a)))
     (Nil))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  le
    ((x Nat) (y Nat)) Bool
    (match x
      (case Z true)
      (case (S z)
        (match y
          (case Z false)
          (case (S x2) (le z x2))))))
(define-fun-rec
  (par (a)
    (flatten
       ((x (Tree a)) (y (list a))) (list a)
       (match x
         (case (Node q z q2) (flatten q (cons z (flatten q2 y))))
         (case Nil y)))))
(define-fun-rec
  equal
    ((x Nat) (y Nat)) Bool
    (match x
      (case Z
        (match y
          (case Z true)
          (case (S z) false)))
      (case (S x2)
        (match y
          (case Z false)
          (case (S y2) (equal x2 y2))))))
(define-fun-rec
  count
    ((x Nat) (y (list Nat))) Nat
    (match y
      (case nil Z)
      (case (cons z ys)
        (ite (equal x z) (S (count x ys)) (count x ys)))))
(define-fun-rec
  add
    ((x Nat) (y (Tree Nat))) (Tree Nat)
    (match y
      (case (Node q z q2)
        (ite (le x z) (Node (add x q) z q2) (Node q z (add x q2))))
      (case Nil (Node (as Nil (Tree Nat)) x (as Nil (Tree Nat))))))
(assert-not
  (forall ((x Nat) (y Nat) (t (Tree Nat)))
    (=> (not (equal x y))
      (= (count y (flatten (add x t) (as nil (list Nat))))
        (count y (flatten t (as nil (list Nat))))))))
(check-sat)
