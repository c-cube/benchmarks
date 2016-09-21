(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Bin (One) (ZeroAnd (ZeroAnd_0 Bin)) (OneAnd (OneAnd_0 Bin)))))
(declare-fun s (Bin) Bin)
(declare-fun plus2 (Nat Nat) Nat)
(declare-fun toNat (Bin) Nat)
(declare-fun plus (Bin Bin) Bin)
(declare-fun times (Bin Bin) Bin)
(declare-fun mult (Nat Nat) Nat)
(assert (= (s One) (ZeroAnd One)))
(assert (forall ((xs Bin)) (= (s (ZeroAnd xs)) (OneAnd xs))))
(assert (forall ((ys Bin)) (= (s (OneAnd ys)) (ZeroAnd (s ys)))))
(assert (forall ((y Nat)) (= (plus2 Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus2 (S n) y) (S (plus2 n y)))))
(assert (= (toNat One) (S Z)))
(assert
  (forall ((xs Bin))
    (= (toNat (ZeroAnd xs)) (plus2 (toNat xs) (toNat xs)))))
(assert
  (forall ((ys Bin))
    (= (toNat (OneAnd ys)) (S (plus2 (toNat ys) (toNat ys))))))
(assert (forall ((y Bin)) (= (plus One y) (s y))))
(assert
  (forall ((z Bin)) (= (plus (ZeroAnd z) One) (s (ZeroAnd z)))))
(assert
  (forall ((z Bin) (ys Bin))
    (= (plus (ZeroAnd z) (ZeroAnd ys)) (ZeroAnd (plus z ys)))))
(assert
  (forall ((z Bin) (xs Bin))
    (= (plus (ZeroAnd z) (OneAnd xs)) (OneAnd (plus z xs)))))
(assert
  (forall ((x2 Bin)) (= (plus (OneAnd x2) One) (s (OneAnd x2)))))
(assert
  (forall ((x2 Bin) (zs Bin))
    (= (plus (OneAnd x2) (ZeroAnd zs)) (OneAnd (plus x2 zs)))))
(assert
  (forall ((x2 Bin) (ys2 Bin))
    (= (plus (OneAnd x2) (OneAnd ys2)) (ZeroAnd (s (plus x2 ys2))))))
(assert (forall ((y Bin)) (= (times One y) y)))
(assert
  (forall ((y Bin) (xs Bin))
    (= (times (ZeroAnd xs) y) (ZeroAnd (times xs y)))))
(assert
  (forall ((y Bin) (ys Bin))
    (= (times (OneAnd ys) y) (plus (ZeroAnd (times ys y)) y))))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (n Nat)) (= (mult (S n) y) (plus2 y (mult n y)))))
(assert-not
  (forall ((x Bin) (y Bin))
    (= (toNat (times x y)) (mult (toNat x) (toNat y)))))
(check-sat)
