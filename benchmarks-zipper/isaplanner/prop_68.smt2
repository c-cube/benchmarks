(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun len (list) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun equal (Nat Nat) Bool)
(declare-fun delete (Nat list) list)
(assert (= (len nil) Z))
(assert
  (forall ((y Nat) (xs list)) (= (len (cons y xs)) (S (len xs)))))
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
(assert (forall ((x Nat)) (= (delete x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) true)
      (= (delete x (cons z xs)) (delete x xs)))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (= (equal x z) false)
      (= (delete x (cons z xs)) (cons z (delete x xs))))))
(assert-not
  (forall ((n Nat) (xs list)) (le (len (delete n xs)) (len xs))))
(check-sat)
