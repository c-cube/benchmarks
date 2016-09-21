(declare-datatypes () ((Nat2 (Z) (S (p Nat2)))))
(declare-datatypes () ((Nat (Z2) (S2 (q Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first Bool) (second list)))))
(declare-fun zcount (Nat list) Nat2)
(declare-fun bubble (list) Pair)
(declare-fun bubsort (list) list)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert (forall ((x Nat)) (= (zcount x nil) Z)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true)
      (= (zcount x (cons z xs)) (S (zcount x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false)
      (= (zcount x (cons z xs)) (zcount x xs)))))
(assert (= (bubble nil) (Pair2 false nil)))
(assert
  (forall ((y Nat))
    (= (bubble (cons y nil)) (Pair2 false (cons y nil)))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list) (b2 Bool) (zs list))
    (=> (= (le y y2) true)
      (=> (= (bubble (cons y2 xs)) (Pair2 b2 zs))
        (= (bubble (cons y (cons y2 xs))) (Pair2 b2 (cons y zs)))))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list) (c Bool) (ys list))
    (=> (= (le y y2) false)
      (=> (= (bubble (cons y xs)) (Pair2 c ys))
        (= (bubble (cons y (cons y2 xs))) (Pair2 true (cons y2 ys)))))))
(assert
  (forall ((x list) (ys list))
    (=> (= (bubble x) (Pair2 true ys)) (= (bubsort x) (bubsort ys)))))
(assert
  (forall ((x list) (ys list))
    (=> (= (bubble x) (Pair2 false ys)) (= (bubsort x) x))))
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
  (forall ((x Nat) (y list))
    (= (zcount x (bubsort y)) (zcount x y))))
(check-sat)
