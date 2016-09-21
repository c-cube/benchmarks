(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Tree (Node (Node_0 Tree) (Node_1 Nat) (Node_2 Tree)) (Nil))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun le (Nat Nat) Bool)
(declare-fun flatten (Tree list) list)
(declare-fun equal (Nat Nat) Bool)
(declare-fun count (Nat list) Nat)
(declare-fun add (Nat Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert
  (forall ((y list) (q Tree) (z Nat) (q2 Tree))
    (= (flatten (Node q z q2) y) (flatten q (cons z (flatten q2 y))))))
(assert (forall ((y list)) (= (flatten Nil y) y)))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert (forall ((x Nat)) (= (count x nil) Z)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) true)
      (= (count x (cons z ys)) (S (count x ys))))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) false) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x Nat) (q Tree) (z Nat) (q2 Tree))
    (=> (= (le x z) true)
      (= (add x (Node q z q2)) (Node (add x q) z q2)))))
(assert
  (forall ((x Nat) (q Tree) (z Nat) (q2 Tree))
    (=> (= (le x z) false)
      (= (add x (Node q z q2)) (Node q z (add x q2))))))
(assert (forall ((x Nat)) (= (add x Nil) (Node Nil x Nil))))
(assert (= (toTree nil) Nil))
(assert
  (forall ((y Nat) (xs list))
    (= (toTree (cons y xs)) (add y (toTree xs)))))
(assert (forall ((x list)) (= (tsort x) (flatten (toTree x) nil))))
(assert-not
  (forall ((x Nat) (y list)) (= (count x (tsort y)) (count x y))))
(check-sat)
