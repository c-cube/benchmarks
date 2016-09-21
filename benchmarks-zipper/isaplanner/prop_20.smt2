(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun len (list) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun insort (Nat list) list)
(declare-fun sort (list) list)
(assert (= (len nil) Z))
(assert
  (forall ((y Nat) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert (forall ((x Nat)) (= (insort x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (le x z) true)
      (= (insort x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (le x z) false)
      (= (insort x (cons z xs)) (cons z (insort x xs))))))
(assert (= (sort nil) nil))
(assert
  (forall ((y Nat) (xs list))
    (= (sort (cons y xs)) (insort y (sort xs)))))
(assert-not (forall ((xs list)) (= (len (sort xs)) (len xs))))
(check-sat)
