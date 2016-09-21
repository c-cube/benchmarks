(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes ()
  ((Heap (Node (Node_0 Heap) (Node_1 Nat) (Node_2 Heap)) (Nil))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun null (list) Bool)
(declare-fun le (Nat Nat) Bool)
(declare-fun merge (Heap Heap) Heap)
(declare-fun toList (Nat Heap) list)
(declare-fun insert2 (Nat Heap) Heap)
(declare-fun toHeap (list) Heap)
(declare-fun heapSize (Heap) Nat)
(declare-fun toList2 (Heap) list)
(declare-fun hsort (list) list)
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun delete (Nat list) list)
(declare-fun isPermutation (list list) Bool)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (= (null nil) true))
(assert (forall ((y Nat) (z list)) (= (null (cons y z)) false)))
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
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
(assert (= (toHeap nil) Nil))
(assert
  (forall ((y Nat) (xs list))
    (= (toHeap (cons y xs)) (insert2 y (toHeap xs)))))
(assert
  (forall ((l Heap) (y Nat) (r Heap))
    (= (heapSize (Node l y r)) (S (plus (heapSize l) (heapSize r))))))
(assert (= (heapSize Nil) Z))
(assert
  (forall ((x Heap)) (= (toList2 x) (toList (heapSize x) x))))
(assert (forall ((x list)) (= (hsort x) (toList2 (toHeap x)))))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert (forall ((x Nat)) (= (elem x nil) false)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (= (elem x (cons z ys)) (or (equal x z) (elem x ys)))))
(assert (forall ((x Nat)) (= (delete x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true) (= (delete x (cons z xs)) xs))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false)
      (= (delete x (cons z xs)) (cons z (delete x xs))))))
(assert (forall ((y list)) (= (isPermutation nil y) (null y))))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (isPermutation (cons z xs) y)
      (and (elem z y) (isPermutation xs (delete z y))))))
(assert-not (forall ((x list)) (isPermutation (hsort x) x)))
(check-sat)
