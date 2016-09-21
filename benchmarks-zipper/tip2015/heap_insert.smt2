(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes ()
  ((Heap (Node (Node_0 Heap) (Node_1 Nat) (Node_2 Heap)) (Nil))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun listInsert (Nat list) list)
(declare-fun merge (Heap Heap) Heap)
(declare-fun toList (Nat Heap) list)
(declare-fun insert2 (Nat Heap) Heap)
(declare-fun heapSize (Heap) Nat)
(declare-fun toList2 (Heap) list)
(declare-fun heap1 (Nat Heap) Bool)
(declare-fun heap (Heap) Bool)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert (forall ((x Nat)) (= (listInsert x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (le x z) true)
      (= (listInsert x (cons z ys)) (cons x (cons z ys))))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (le x z) false)
      (= (listInsert x (cons z ys)) (cons z (listInsert x ys))))))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap) (x4 Heap) (x5 Nat) (x6 Heap))
    (=> (= (le x2 x5) true)
      (= (merge (Node z x2 x3) (Node x4 x5 x6))
        (Node (merge x3 (Node x4 x5 x6)) x2 z)))))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap) (x4 Heap) (x5 Nat) (x6 Heap))
    (=> (= (le x2 x5) false)
      (= (merge (Node z x2 x3) (Node x4 x5 x6))
        (Node (merge (Node z x2 x3) x6) x5 x4)))))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap))
    (= (merge (Node z x2 x3) Nil) (Node z x2 x3))))
(assert (forall ((y Heap)) (= (merge Nil y) y)))
(assert (forall ((y Heap)) (= (toList Z y) nil)))
(assert
  (forall ((z Nat) (x2 Heap) (x3 Nat) (x4 Heap))
    (= (toList (S z) (Node x2 x3 x4))
      (cons x3 (toList z (merge x2 x4))))))
(assert (forall ((z Nat)) (= (toList (S z) Nil) nil)))
(assert
  (forall ((x Nat) (y Heap))
    (= (insert2 x y) (merge (Node Nil x Nil) y))))
(assert
  (forall ((l Heap) (y Nat) (r Heap))
    (= (heapSize (Node l y r)) (S (plus (heapSize l) (heapSize r))))))
(assert (= (heapSize Nil) Z))
(assert
  (forall ((x Heap)) (= (toList2 x) (toList (heapSize x) x))))
(assert
  (forall ((x Nat) (l Heap) (z Nat) (r Heap))
    (= (heap1 x (Node l z r))
      (and (le x z) (and (heap1 z l) (heap1 z r))))))
(assert (forall ((x Nat)) (= (heap1 x Nil) true)))
(assert
  (forall ((l Heap) (y Nat) (r Heap))
    (= (heap (Node l y r)) (and (heap1 y l) (heap1 y r)))))
(assert (= (heap Nil) true))
(assert-not
  (forall ((x Nat) (h Heap))
    (=> (heap h)
      (= (toList2 (insert2 x h)) (listInsert x (toList2 h))))))
(check-sat)
