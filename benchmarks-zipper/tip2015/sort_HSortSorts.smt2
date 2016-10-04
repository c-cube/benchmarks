(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 Nat) (tail2 list2)))))
(declare-datatypes ()
  ((Heap (Node (Node_0 Heap) (Node_1 Nat) (Node_2 Heap)) (Nil))))
(declare-datatypes ()
  ((list (nil) (cons (head Heap) (tail list)))))
(declare-fun zordered (list2) Bool)
(declare-fun toHeap2 (list2) list)
(declare-fun hmerge (Heap Heap) Heap)
(declare-fun hpairwise (list) list)
(declare-fun hmerging (list) Heap)
(declare-fun toHeap (list2) Heap)
(declare-fun toList (Heap) list2)
(declare-fun hsort (list2) list2)
(declare-fun le (Nat Nat) Bool)
(assert (= (zordered nil2) true))
(assert (forall ((y Nat)) (= (zordered (cons2 y nil2)) true)))
(assert
  (forall ((y Nat) (y2 Nat) (xs list2))
    (= (zordered (cons2 y (cons2 y2 xs)))
      (and (le y y2) (zordered (cons2 y2 xs))))))
(assert (= (toHeap2 nil2) nil))
(assert
  (forall ((y Nat) (z list2))
    (= (toHeap2 (cons2 y z)) (cons (Node Nil y Nil) (toHeap2 z)))))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap) (x4 Heap) (x5 Nat) (x6 Heap))
    (=> (= (le x2 x5) true)
      (= (hmerge (Node z x2 x3) (Node x4 x5 x6))
        (Node (hmerge x3 (Node x4 x5 x6)) x2 z)))))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap) (x4 Heap) (x5 Nat) (x6 Heap))
    (=> (= (le x2 x5) false)
      (= (hmerge (Node z x2 x3) (Node x4 x5 x6))
        (Node (hmerge (Node z x2 x3) x6) x5 x4)))))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap))
    (= (hmerge (Node z x2 x3) Nil) (Node z x2 x3))))
(assert (forall ((y Heap)) (= (hmerge Nil y) y)))
(assert (= (hpairwise nil) nil))
(assert
  (forall ((q Heap)) (= (hpairwise (cons q nil)) (cons q nil))))
(assert
  (forall ((q Heap) (r Heap) (qs list))
    (= (hpairwise (cons q (cons r qs)))
      (cons (hmerge q r) (hpairwise qs)))))
(assert (= (hmerging nil) Nil))
(assert (forall ((q Heap)) (= (hmerging (cons q nil)) q)))
(assert
  (forall ((q Heap) (z Heap) (x2 list))
    (= (hmerging (cons q (cons z x2)))
      (hmerging (hpairwise (cons q (cons z x2)))))))
(assert (forall ((x list2)) (= (toHeap x) (hmerging (toHeap2 x)))))
(assert
  (forall ((q Heap) (y Nat) (r Heap))
    (= (toList (Node q y r)) (cons2 y (toList (hmerge q r))))))
(assert (= (toList Nil) nil2))
(assert (forall ((x list2)) (= (hsort x) (toList (toHeap x)))))
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert-not (forall ((x list2)) (zordered (hsort x))))
(check-sat)