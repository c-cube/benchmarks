(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun minus (Nat Nat) Nat)
(declare-fun len (list) Nat)
(declare-fun butlast (list) list)
(assert (forall ((y Nat)) (= (minus Z y) Z)))
(assert (forall ((z Nat)) (= (minus (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (minus (S z) (S x2)) (minus z x2))))
(assert (= (len nil) Z))
(assert
  (forall ((y sk) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (= (butlast nil) nil))
(assert (forall ((y sk)) (= (butlast (cons y nil)) nil)))
(assert
  (forall ((y sk) (x2 sk) (x3 list))
    (= (butlast (cons y (cons x2 x3)))
      (cons y (butlast (cons x2 x3))))))
(assert-not
  (forall ((xs list)) (= (len (butlast xs)) (minus (len xs) (S Z)))))
(check-sat)
