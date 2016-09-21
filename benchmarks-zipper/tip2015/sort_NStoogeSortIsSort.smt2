(declare-datatypes () ((Nat2 (Z) (S (p Nat2)))))
(declare-datatypes () ((Nat (Z2) (S2 (q Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first list) (second list)))))
(declare-fun third (Nat2) Nat2)
(declare-fun take (Nat2 list) list)
(declare-fun sort2 (Nat Nat) list)
(declare-fun length (list) Nat2)
(declare-fun insert2 (Nat list) list)
(declare-fun isort (list) list)
(declare-fun drop (Nat2 list) list)
(declare-fun splitAt (Nat2 list) Pair)
(declare-fun append (list list) list)
(declare-fun reverse (list) list)
(declare-fun nstooge1sort2 (list) list)
(declare-fun nstoogesort (list) list)
(declare-fun nstooge1sort1 (list) list)
(declare-fun le (Nat Nat) Bool)
(assert (= (third Z) Z))
(assert (= (third (S Z)) Z))
(assert (= (third (S (S Z))) Z))
(assert
  (forall ((n Nat2)) (= (third (S (S (S n)))) (S (third n)))))
(assert (forall ((y list)) (= (take Z y) nil)))
(assert (forall ((z Nat2)) (= (take (S z) nil) nil)))
(assert
  (forall ((z Nat2) (x2 Nat) (x3 list))
    (= (take (S z) (cons x2 x3)) (cons x2 (take z x3)))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (= (le x y) true) (= (sort2 x y) (cons x (cons y nil))))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (= (le x y) false) (= (sort2 x y) (cons y (cons x nil))))))
(assert (= (length nil) Z))
(assert
  (forall ((y Nat) (xs list))
    (= (length (cons y xs)) (S (length xs)))))
(assert (forall ((x Nat)) (= (insert2 x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (le x z) true)
      (= (insert2 x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (le x z) false)
      (= (insert2 x (cons z xs)) (cons z (insert2 x xs))))))
(assert (= (isort nil) nil))
(assert
  (forall ((y Nat) (xs list))
    (= (isort (cons y xs)) (insert2 y (isort xs)))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat2)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat2) (x2 Nat) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert
  (forall ((x Nat2) (y list))
    (= (splitAt x y) (Pair2 (take x y) (drop x y)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (= (reverse nil) nil))
(assert
  (forall ((y Nat) (xs list))
    (= (reverse (cons y xs)) (append (reverse xs) (cons y nil)))))
(assert
  (forall ((x list) (ys list) (zs list))
    (=> (= (splitAt (third (length x)) (reverse x)) (Pair2 ys zs))
      (= (nstooge1sort2 x) (append (nstoogesort zs) (reverse ys))))))
(assert (= (nstoogesort nil) nil))
(assert
  (forall ((y Nat)) (= (nstoogesort (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat))
    (= (nstoogesort (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Nat) (y2 Nat) (x3 Nat) (x4 list))
    (= (nstoogesort (cons y (cons y2 (cons x3 x4))))
      (nstooge1sort2
        (nstooge1sort1 (nstooge1sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys list) (zs list))
    (=> (= (splitAt (third (length x)) x) (Pair2 ys zs))
      (= (nstooge1sort1 x) (append ys (nstoogesort zs))))))
(assert (forall ((y Nat)) (= (le Z2 y) true)))
(assert (forall ((z Nat)) (= (le (S2 z) Z2) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S2 z) (S2 x2)) (le z x2))))
(assert-not (forall ((x list)) (= (nstoogesort x) (isort x))))
(check-sat)
