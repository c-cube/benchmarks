(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first Bool) (second list)))))
(declare-fun zordered (list) Bool)
(declare-fun bubble (list) Pair)
(declare-fun bubsort (list) list)
(declare-fun le (Nat Nat) Bool)
(assert (= (zordered nil) true))
(assert (forall ((y Nat)) (= (zordered (cons y nil)) true)))
(assert
  (forall ((y Nat) (y2 Nat) (xs list))
    (= (zordered (cons y (cons y2 xs)))
      (and (le y y2) (zordered (cons y2 xs))))))
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
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert-not (forall ((x list)) (zordered (bubsort x))))
(check-sat)
