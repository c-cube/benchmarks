(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Tree (TNode (TNode_0 Tree) (TNode_1 Nat) (TNode_2 Tree))
     (TNil))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun zordered (list) Bool)
(declare-fun flatten (Tree list) list)
(declare-fun add (Nat Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(declare-fun le (Nat Nat) Bool)
(assert (= (zordered nil) true))
(assert (forall ((y Nat)) (= (zordered (cons y nil)) true)))
(assert
  (forall ((y Nat) (y2 Nat) (xs list))
    (= (zordered (cons y (cons y2 xs)))
      (and (le y y2) (zordered (cons y2 xs))))))
(assert
  (forall ((y list) (q Tree) (z Nat) (r Tree))
    (= (flatten (TNode q z r) y) (flatten q (cons z (flatten r y))))))
(assert (forall ((y list)) (= (flatten TNil y) y)))
(assert
  (forall ((x Nat) (q Tree) (z Nat) (r Tree))
    (=> (= (le x z) true)
      (= (add x (TNode q z r)) (TNode (add x q) z r)))))
(assert
  (forall ((x Nat) (q Tree) (z Nat) (r Tree))
    (=> (= (le x z) false)
      (= (add x (TNode q z r)) (TNode q z (add x r))))))
(assert (forall ((x Nat)) (= (add x TNil) (TNode TNil x TNil))))
(assert (= (toTree nil) TNil))
(assert
  (forall ((y Nat) (xs list))
    (= (toTree (cons y xs)) (add y (toTree xs)))))
(assert (forall ((x list)) (= (tsort x) (flatten (toTree x) nil))))
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert-not (forall ((x list)) (zordered (tsort x))))
(check-sat)