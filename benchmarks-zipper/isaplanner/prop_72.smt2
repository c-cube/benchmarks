(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun take (Nat list) list)
(declare-fun minus (Nat Nat) Nat)
(declare-fun len (list) Nat)
(declare-fun drop (Nat list) list)
(declare-fun append (list list) list)
(declare-fun rev (list) list)
(assert (forall ((y list)) (= (take Z y) nil)))
(assert (forall ((z Nat)) (= (take (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (take (S z) (cons x2 x3)) (cons x2 (take z x3)))))
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
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (= (rev nil) nil))
(assert
  (forall ((y sk) (xs list))
    (= (rev (cons y xs)) (append (rev xs) (cons y nil)))))
(assert-not
  (forall ((i Nat) (xs list))
    (= (rev (drop i xs)) (take (minus (len xs) i) (rev xs)))))
(check-sat)
