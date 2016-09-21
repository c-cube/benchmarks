(declare-sort fun1 2)
(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun (par (a b) (apply1 ((fun1 a b) a) b)))
(declare-fun len (list) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun filter ((fun1 sk Bool) list) list)
(assert (= (len nil) Z))
(assert
  (forall ((y sk) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (forall ((y Nat)) (= (le Z y) true)))
(assert (forall ((z Nat)) (= (le (S z) Z) false)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (le (S z) (S x2)) (le z x2))))
(assert (forall ((x (fun1 sk Bool))) (= (filter x nil) nil)))
(assert
  (forall ((x (fun1 sk Bool)) (z sk) (xs list))
    (=> (= (apply1 x z) true)
      (= (filter x (cons z xs)) (cons z (filter x xs))))))
(assert
  (forall ((x (fun1 sk Bool)) (z sk) (xs list))
    (=> (= (apply1 x z) false)
      (= (filter x (cons z xs)) (filter x xs)))))
(assert-not
  (forall ((q (fun1 sk Bool)) (xs list))
    (le (len (filter q xs)) (len xs))))
(check-sat)
