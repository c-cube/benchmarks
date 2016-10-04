(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun zordered (list) Bool)
(declare-fun zdelete (Nat list) list)
(declare-fun ssort_minimum (Nat list) Nat)
(declare-fun ssort (list) list)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(assert (= (zordered nil) true))
(assert (forall ((y Nat)) (= (zordered (cons y nil)) true)))
(assert
  (forall ((y Nat) (y2 Nat) (xs list))
    (= (zordered (cons y (cons y2 xs)))
      (and (le y y2) (zordered (cons y2 xs))))))
(assert (forall ((x Nat)) (= (zdelete x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) true) (= (zdelete x (cons z ys)) ys))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= (equal x z) false)
      (= (zdelete x (cons z ys)) (cons z (zdelete x ys))))))
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
(assert-not (forall ((x list)) (zordered (ssort x))))
(check-sat)