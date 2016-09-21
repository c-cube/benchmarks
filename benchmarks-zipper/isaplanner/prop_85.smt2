(declare-sort sk 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk) (tail2 list2)))))
(declare-datatypes () ((Pair (Pair2 (first sk) (second sk)))))
(declare-datatypes ()
  ((list (nil) (cons (head Pair) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun zip (list2 list2) list)
(declare-fun len (list2) Nat)
(declare-fun append (list list) list)
(declare-fun append2 (list2 list2) list2)
(declare-fun rev (list) list)
(declare-fun rev2 (list2) list2)
(assert (forall ((y list2)) (= (zip nil2 y) nil)))
(assert
  (forall ((z sk) (x2 list2)) (= (zip (cons2 z x2) nil2) nil)))
(assert
  (forall ((z sk) (x2 list2) (x3 sk) (x4 list2))
    (= (zip (cons2 z x2) (cons2 x3 x4))
      (cons (Pair2 z x3) (zip x2 x4)))))
(assert (= (len nil2) Z))
(assert
  (forall ((y sk) (xs list2)) (= (len (cons2 y xs)) (S (len xs)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z Pair) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (forall ((y list2)) (= (append2 nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (append2 (cons2 z xs) y) (cons2 z (append2 xs y)))))
(assert (= (rev nil) nil))
(assert
  (forall ((y Pair) (xs list))
    (= (rev (cons y xs)) (append (rev xs) (cons y nil)))))
(assert (= (rev2 nil2) nil2))
(assert
  (forall ((y sk) (xs list2))
    (= (rev2 (cons2 y xs)) (append2 (rev2 xs) (cons2 y nil2)))))
(assert-not
  (forall ((xs list2) (ys list2))
    (=> (= (len xs) (len ys))
      (= (zip (rev2 xs) (rev2 ys)) (rev (zip xs ys))))))
(check-sat)
