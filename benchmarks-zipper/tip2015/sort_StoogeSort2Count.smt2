(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first list) (second list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun ztake (Int list) list)
(declare-fun zlength (list) Int)
(declare-fun zdrop (Int list) list)
(declare-fun zsplitAt (Int list) Pair)
(declare-fun zcount (Int list) Nat)
(declare-fun sort2 (Int Int) list)
(declare-fun append (list list) list)
(declare-fun stooge2sort2 (list) list)
(declare-fun stoogesort2 (list) list)
(declare-fun stooge2sort1 (list) list)
(assert
  (forall ((x Int) (y list))
    (=> (= (= x 0) true) (= (ztake x y) nil))))
(assert
  (forall ((x Int)) (=> (= (= x 0) false) (= (ztake x nil) nil))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (=> (= (= x 0) false)
      (= (ztake x (cons z xs)) (cons z (ztake (- x 1) xs))))))
(assert (= (zlength nil) 0))
(assert
  (forall ((y Int) (xs list))
    (= (zlength (cons y xs)) (+ 1 (zlength xs)))))
(assert
  (forall ((x Int) (y list))
    (=> (= (= x 0) true) (= (zdrop x y) y))))
(assert
  (forall ((x Int)) (=> (= (= x 0) false) (= (zdrop x nil) nil))))
(assert
  (forall ((x Int) (z Int) (xs1 list))
    (=> (= (= x 0) false)
      (= (zdrop x (cons z xs1)) (zdrop (- x 1) xs1)))))
(assert
  (forall ((x Int) (y list))
    (= (zsplitAt x y) (Pair2 (ztake x y) (zdrop x y)))))
(assert (forall ((x Int)) (= (zcount x nil) Z)))
(assert
  (forall ((x Int) (z Int) (xs list))
    (=> (= (= x z) true)
      (= (zcount x (cons z xs)) (S (zcount x xs))))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (=> (= (= x z) false) (= (zcount x (cons z xs)) (zcount x xs)))))
(assert
  (forall ((x Int) (y Int))
    (=> (= (<= x y) true) (= (sort2 x y) (cons x (cons y nil))))))
(assert
  (forall ((x Int) (y Int))
    (=> (= (<= x y) false) (= (sort2 x y) (cons y (cons x nil))))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert
  (forall ((x list) (ys list) (zs list))
    (=> (= (zsplitAt (div (+ (* 2 (zlength x)) 1) 3) x) (Pair2 ys zs))
      (= (stooge2sort2 x) (append (stoogesort2 ys) zs)))))
(assert (= (stoogesort2 nil) nil))
(assert
  (forall ((y Int)) (= (stoogesort2 (cons y nil)) (cons y nil))))
(assert
  (forall ((y Int) (y2 Int))
    (= (stoogesort2 (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Int) (y2 Int) (x3 Int) (x4 list))
    (= (stoogesort2 (cons y (cons y2 (cons x3 x4))))
      (stooge2sort2
        (stooge2sort1 (stooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys list) (zs list))
    (=> (= (zsplitAt (div (zlength x) 3) x) (Pair2 ys zs))
      (= (stooge2sort1 x) (append ys (stoogesort2 zs))))))
(assert-not
  (forall ((x Int) (y list))
    (= (zcount x (stoogesort2 y)) (zcount x y))))
(check-sat)
