(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun minus (Nat Nat) Nat)
(declare-fun len (list) Nat)
(declare-fun drop (Nat list) list)
(assert (forall ((y Nat)) (= (minus Z y) Z)))
(assert (forall ((z Nat)) (= (minus (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (minus (S z) (S x2)) (minus z x2))))
(assert (= (len nil) Z))
(assert
  (forall ((y sk) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert-not
  (forall ((n Nat) (xs list))
    (= (len (drop n xs)) (minus (len xs) n))))
(check-sat)
