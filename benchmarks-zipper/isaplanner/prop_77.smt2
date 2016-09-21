(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun le (Nat Nat) Bool)
(declare-fun sorted (list) Bool)
(declare-fun insort (Nat list) list)
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert (= (sorted nil) true))
(assert (forall ((y Nat)) (= (sorted (cons y nil)) true)))
(assert
  (forall ((y Nat) (y2 Nat) (ys list))
    (= (sorted (cons y (cons y2 ys)))
      (and (le y y2) (sorted (cons y2 ys))))))
(assert (forall ((x Nat)) (= (insort x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (le x z) true)
      (= (insort x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (le x z) false)
      (= (insort x (cons z xs)) (cons z (insort x xs))))))
(assert-not
  (forall ((x Nat) (xs list))
    (=> (sorted xs) (sorted (insort x xs)))))
(check-sat)
