(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun len (list) Nat)
(declare-fun last (list) Nat)
(declare-fun drop (Nat list) list)
(assert (forall ((x Nat)) (= (lt x Z) false)))
(assert (forall ((z Nat)) (= (lt Z (S z)) true)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (lt (S x2) (S z)) (lt x2 z))))
(assert (= (len nil) Z))
(assert
  (forall ((y Nat) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (= (last nil) Z))
(assert (forall ((y Nat)) (= (last (cons y nil)) y)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (last (cons y (cons x2 x3))) (last (cons x2 x3)))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 Nat) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert-not
  (forall ((n Nat) (xs list))
    (=> (lt n (len xs)) (= (last (drop n xs)) (last xs)))))
(check-sat)
