(declare-datatypes () ((Nat2 (Z) (S (p Nat2)))))
(declare-datatypes () ((Nat (Z2) (S2 (q Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first list) (second list)))))
(declare-fun zelem (Nat list) Bool)
(declare-fun zdelete (Nat list) list)
(declare-fun twoThirds (Nat2) Nat2)
(declare-fun third (Nat2) Nat2)
(declare-fun take (Nat2 list) list)
(declare-fun sort2 (Nat Nat) list)
(declare-fun null (list) Bool)
(declare-fun zisPermutation (list list) Bool)
(declare-fun length (list) Nat2)
(declare-fun drop (Nat2 list) list)
(declare-fun splitAt (Nat2 list) Pair)
(declare-fun append (list list) list)
(declare-fun nstooge2sort2 (list) list)
(declare-fun nstoogesort2 (list) list)
(declare-fun nstooge2sort1 (list) list)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert (forall ((x Nat)) (= (zelem x nil) false)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (= (zelem x (cons z ys)) (or (equal x z) (zelem x ys)))))
(assert (forall ((x Nat)) (= (zdelete x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) true) (= (zdelete x (cons z ys)) ys))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) false)
      (= (zdelete x (cons z ys)) (cons z (zdelete x ys))))))
(assert (= (twoThirds Z) Z))
(assert (= (twoThirds (S Z)) (S Z)))
(assert (= (twoThirds (S (S Z))) (S Z)))
(assert
  (forall ((n Nat2))
    (= (twoThirds (S (S (S n)))) (S (S (twoThirds n))))))
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
(assert (= (null nil) true))
(assert (forall ((y Nat) (z list)) (= (null (cons y z)) false)))
(assert (forall ((y list)) (= (zisPermutation nil y) (null y))))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (zisPermutation (cons z xs) y)
      (and (zelem z y) (zisPermutation xs (zdelete z y))))))
(assert (= (length nil) Z))
(assert
  (forall ((y Nat) (xs list))
    (= (length (cons y xs)) (S (length xs)))))
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
(assert
  (forall ((x list) (ys list) (zs list))
    (=> (= (splitAt (twoThirds (length x)) x) (Pair2 ys zs))
      (= (nstooge2sort2 x) (append (nstoogesort2 ys) zs)))))
(assert (= (nstoogesort2 nil) nil))
(assert
  (forall ((y Nat)) (= (nstoogesort2 (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat))
    (= (nstoogesort2 (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Nat) (y2 Nat) (x3 Nat) (x4 list))
    (= (nstoogesort2 (cons y (cons y2 (cons x3 x4))))
      (nstooge2sort2
        (nstooge2sort1 (nstooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys list) (zs list))
    (=> (= (splitAt (third (length x)) x) (Pair2 ys zs))
      (= (nstooge2sort1 x) (append ys (nstoogesort2 zs))))))
(assert (forall ((y Nat)) (= (le Z2 y) true)))
(assert (forall ((z Nat)) (= (le (S2 z) Z2) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S2 z) (S2 x2)) (le z x2))))
(assert (= (equal Z2 Z2) true))
(assert (forall ((z Nat)) (= (equal Z2 (S2 z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S2 x2) Z2) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S2 x2) (S2 y2)) (equal x2 y2))))
(assert-not
  (forall ((x list)) (zisPermutation (nstoogesort2 x) x)))
(check-sat)
