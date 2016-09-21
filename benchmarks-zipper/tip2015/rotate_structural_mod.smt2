(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun take (Nat list) list)
(declare-fun minus (Nat Nat) Nat)
(declare-fun length (list) Nat)
(declare-fun go (Nat Nat Nat) Nat)
(declare-fun mod_structural (Nat Nat) Nat)
(declare-fun drop (Nat list) list)
(declare-fun append (list list) list)
(declare-fun rotate (Nat list) list)
(assert (forall ((y list)) (= (take Z y) nil)))
(assert (forall ((z Nat)) (= (take (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (take (S z) (cons x2 x3)) (cons x2 (take z x3)))))
(assert (forall ((y Nat)) (= (minus Z y) Z)))
(assert (forall ((n Nat)) (= (minus (S n) Z) (S n))))
(assert
  (forall ((n Nat) (m Nat)) (= (minus (S n) (S m)) (minus n m))))
(assert (= (length nil) Z))
(assert
  (forall ((y sk) (xs list))
    (= (length (cons y xs)) (S (length xs)))))
(assert (forall ((x Nat) (y Nat)) (= (go x y Z) Z)))
(assert (forall ((x2 Nat)) (= (go Z Z (S x2)) Z)))
(assert
  (forall ((x2 Nat) (n Nat))
    (= (go Z (S n) (S x2)) (minus (S x2) (S n)))))
(assert
  (forall ((x2 Nat) (m Nat))
    (= (go (S m) Z (S x2)) (go m x2 (S x2)))))
(assert
  (forall ((x2 Nat) (m Nat) (k Nat))
    (= (go (S m) (S k) (S x2)) (go m k (S x2)))))
(assert
  (forall ((x Nat) (y Nat)) (= (mod_structural x y) (go x Z y))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (forall ((y list)) (= (rotate Z y) y)))
(assert (forall ((z Nat)) (= (rotate (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (rotate (S z) (cons x2 x3))
      (rotate z (append x3 (cons x2 nil))))))
(assert-not
  (forall ((n Nat) (xs list))
    (= (rotate n xs)
      (append (drop (mod_structural n (length xs)) xs)
        (take (mod_structural n (length xs)) xs)))))
(check-sat)
