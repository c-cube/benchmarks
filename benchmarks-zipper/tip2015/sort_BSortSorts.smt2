(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun zordered (list) Bool)
(declare-fun sort2 (Nat Nat) list)
(declare-fun evens (list) list)
(declare-fun odds (list) list)
(declare-fun append (list list) list)
(declare-fun pairs (list list) list)
(declare-fun stitch (list list) list)
(declare-fun bmerge (list list) list)
(declare-fun bsort (list) list)
(declare-fun le (Nat Nat) Bool)
(assert (= (zordered nil) true))
(assert (forall ((y Nat)) (= (zordered (cons y nil)) true)))
(assert
  (forall ((y Nat) (y2 Nat) (xs list))
    (= (zordered (cons y (cons y2 xs)))
      (and (le y y2) (zordered (cons y2 xs))))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (= (le x y) true) (= (sort2 x y) (cons x (cons y nil))))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (= (le x y) false) (= (sort2 x y) (cons y (cons x nil))))))
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
(assert-not (forall ((x list)) (zordered (bsort x))))
(check-sat)
