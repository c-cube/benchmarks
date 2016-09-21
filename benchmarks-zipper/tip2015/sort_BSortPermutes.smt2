(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun zelem (Nat list) Bool)
(declare-fun zdelete (Nat list) list)
(declare-fun sort2 (Nat Nat) list)
(declare-fun null (list) Bool)
(declare-fun zisPermutation (list list) Bool)
(declare-fun evens (list) list)
(declare-fun odds (list) list)
(declare-fun append (list list) list)
(declare-fun pairs (list list) list)
(declare-fun stitch (list list) list)
(declare-fun bmerge (list list) list)
(declare-fun bsort (list) list)
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
(assert (= (evens nil) nil))
(assert
  (forall ((y Nat) (xs list))
    (= (evens (cons y xs)) (cons y (odds xs)))))
(assert (= (odds nil) nil))
(assert
  (forall ((y Nat) (xs list)) (= (odds (cons y xs)) (evens xs))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (forall ((y list)) (= (pairs nil y) y)))
(assert
  (forall ((z Nat) (x2 list))
    (= (pairs (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Nat) (x2 list) (x3 Nat) (x4 list))
    (= (pairs (cons z x2) (cons x3 x4))
      (append (sort2 z x3) (pairs x2 x4)))))
(assert (forall ((y list)) (= (stitch nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (stitch (cons z xs) y) (cons z (pairs xs y)))))
(assert (forall ((y list)) (= (bmerge nil y) nil)))
(assert
  (forall ((z Nat) (x2 list))
    (= (bmerge (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Nat) (x3 Nat))
    (= (bmerge (cons z nil) (cons x3 nil)) (sort2 z x3))))
(assert
  (forall ((z Nat) (x3 Nat) (x5 Nat) (x6 list))
    (= (bmerge (cons z nil) (cons x3 (cons x5 x6)))
      (stitch
        (bmerge (evens (cons z nil)) (evens (cons x3 (cons x5 x6))))
        (bmerge (odds (cons z nil)) (odds (cons x3 (cons x5 x6))))))))
(assert
  (forall ((z Nat) (x3 Nat) (x4 list) (x7 Nat) (x8 list))
    (= (bmerge (cons z (cons x7 x8)) (cons x3 x4))
      (stitch (bmerge (evens (cons z (cons x7 x8))) (evens (cons x3 x4)))
        (bmerge (odds (cons z (cons x7 x8))) (odds (cons x3 x4)))))))
(assert (= (bsort nil) nil))
(assert (forall ((y Nat)) (= (bsort (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (bsort (cons y (cons x2 x3)))
      (bmerge (bsort (evens (cons y (cons x2 x3))))
        (bsort (odds (cons y (cons x2 x3))))))))
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert (= (equal Z Z) true))
(assert (forall ((z Nat)) (= (equal Z (S z)) false)))
(assert (forall ((x2 Nat)) (= (equal (S x2) Z) false)))
(assert
  (forall ((x2 Nat) (y2 Nat))
    (= (equal (S x2) (S y2)) (equal x2 y2))))
(assert-not (forall ((x list)) (zisPermutation (bsort x) x)))
(check-sat)
