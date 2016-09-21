(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Tree (Node (Node_0 Tree) (Node_1 Nat) (Node_2 Tree)) (Nil))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun zelem (Nat list) Bool)
(declare-fun swap (Nat Nat Tree) Tree)
(declare-fun append (list list) list)
(declare-fun flatten0 (Tree) list)
(declare-fun equal (Nat Nat) Bool)
(assert (forall ((x Nat)) (= (zelem x nil) false)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (= (zelem x (cons z ys)) (or (equal x z) (zelem x ys)))))
(assert
  (forall ((x Nat) (y Nat) (q Tree) (x2 Nat) (r Tree))
    (=> (= (equal x2 x) true)
      (= (swap x y (Node q x2 r)) (Node (swap x y q) y (swap x y r))))))
(assert
  (forall ((x Nat) (y Nat) (q Tree) (x2 Nat) (r Tree))
    (=> (= (equal x2 x) false)
      (=> (= (equal x2 y) true)
        (= (swap x y (Node q x2 r)) (Node (swap x y q) x (swap x y r)))))))
(assert
  (forall ((x Nat) (y Nat) (q Tree) (x2 Nat) (r Tree))
    (=> (= (equal x2 x) false)
      (=> (= (equal x2 y) false)
        (= (swap x y (Node q x2 r))
          (Node (swap x y q) x2 (swap x y r)))))))
(assert (forall ((x Nat) (y Nat)) (= (swap x y Nil) Nil)))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert
  (forall ((q Tree) (y Nat) (r Tree))
    (= (flatten0 (Node q y r))
      (append (append (flatten0 q) (cons y nil)) (flatten0 r)))))
(assert (= (flatten0 Nil) nil))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert-not
  (forall ((q Tree) (a Nat) (b Nat))
    (=> (zelem a (flatten0 q))
      (=> (zelem b (flatten0 q))
        (and (zelem a (flatten0 (swap a b q)))
          (zelem b (flatten0 (swap a b q))))))))
(check-sat)
