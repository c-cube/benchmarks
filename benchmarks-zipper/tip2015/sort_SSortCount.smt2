(declare-datatypes () ((Nat2 (Z) (S (p Nat2)))))
(declare-datatypes () ((Nat (Z2) (S2 (q Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun zdelete (Nat list) list)
(declare-fun zcount (Nat list) Nat2)
(declare-fun ssort_minimum (Nat list) Nat)
(declare-fun ssort (list) list)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert (forall ((x Nat)) (= (zdelete x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) true) (= (zdelete x (cons z ys)) ys))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) false)
      (= (zdelete x (cons z ys)) (cons z (zdelete x ys))))))
(assert (forall ((x Nat)) (= (zcount x nil) Z)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true)
      (= (zcount x (cons z xs)) (S (zcount x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false)
      (= (zcount x (cons z xs)) (zcount x xs)))))
(assert (forall ((x Nat)) (= (ssort_minimum x nil) x)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (le z x) true)
      (= (ssort_minimum x (cons z ys)) (ssort_minimum z ys)))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (le z x) false)
      (= (ssort_minimum x (cons z ys)) (ssort_minimum x ys)))))
(assert (= (ssort nil) nil))
(assert
  (forall ((y Nat) (ys list) (m Nat))
    (=> (= m (ssort_minimum y ys))
      (= (ssort (cons y ys)) (cons m (ssort (zdelete m (cons y ys))))))))
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
  (forall ((x Nat) (y list)) (= (zcount x (ssort y)) (zcount x y))))
(check-sat)
