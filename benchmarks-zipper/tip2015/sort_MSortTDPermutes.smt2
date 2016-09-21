(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-fun ztake (Int list) list)
(declare-fun zlength (list) Int)
(declare-fun zelem (Int list) Bool)
(declare-fun zdrop (Int list) list)
(declare-fun zdelete (Int list) list)
(declare-fun null (list) Bool)
(declare-fun zisPermutation (list list) Bool)
(declare-fun lmerge (list list) list)
(declare-fun msorttd (list) list)
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
(assert (forall ((x Int)) (= (zelem x nil) false)))
(assert
  (forall ((x Int) (z Int) (ys list))
    (= (zelem x (cons z ys)) (or (= x z) (zelem x ys)))))
(assert
  (forall ((x Int) (y list))
    (=> (= (= x 0) true) (= (zdrop x y) y))))
(assert
  (forall ((x Int)) (=> (= (= x 0) false) (= (zdrop x nil) nil))))
(assert
  (forall ((x Int) (z Int) (xs1 list))
    (=> (= (= x 0) false)
      (= (zdrop x (cons z xs1)) (zdrop (- x 1) xs1)))))
(assert (forall ((x Int)) (= (zdelete x nil) nil)))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (= (= x z) true) (= (zdelete x (cons z ys)) ys))))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (= (= x z) false)
      (= (zdelete x (cons z ys)) (cons z (zdelete x ys))))))
(assert (= (null nil) true))
(assert (forall ((y Int) (z list)) (= (null (cons y z)) false)))
(assert (forall ((y list)) (= (zisPermutation nil y) (null y))))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (zisPermutation (cons z xs) y)
      (and (zelem z y) (zisPermutation xs (zdelete z y))))))
(assert (forall ((y list)) (= (lmerge nil y) y)))
(assert
  (forall ((z Int) (x2 list))
    (= (lmerge (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Int) (x2 list) (x3 Int) (x4 list))
    (=> (= (<= z x3) true)
      (= (lmerge (cons z x2) (cons x3 x4))
        (cons z (lmerge x2 (cons x3 x4)))))))
(assert
  (forall ((z Int) (x2 list) (x3 Int) (x4 list))
    (=> (= (<= z x3) false)
      (= (lmerge (cons z x2) (cons x3 x4))
        (cons x3 (lmerge (cons z x2) x4))))))
(assert (= (msorttd nil) nil))
(assert (forall ((y Int)) (= (msorttd (cons y nil)) (cons y nil))))
(assert
  (forall ((y Int) (x2 Int) (x3 list) (k Int))
    (=> (= k (div (zlength (cons y (cons x2 x3))) 2))
      (= (msorttd (cons y (cons x2 x3)))
        (lmerge (msorttd (ztake k (cons y (cons x2 x3))))
          (msorttd (zdrop k (cons y (cons x2 x3)))))))))
(assert-not (forall ((x list)) (zisPermutation (msorttd x) x)))
(check-sat)
