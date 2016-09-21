(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((Integer (P (P_0 Nat)) (N (N_0 Nat)))))
(declare-const zero Integer)
(declare-fun plus2 (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Integer)
(declare-fun plus (Integer Integer) Integer)
(assert (= zero (P Z)))
(assert (forall ((y Nat)) (= (plus2 Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus2 (S n) y) (S (plus2 n y)))))
(assert (= (minus Z Z) (P Z)))
(assert (forall ((n Nat)) (= (minus Z (S n)) (N n))))
(assert (forall ((m Nat)) (= (minus (S m) Z) (P (S m)))))
(assert
  (forall ((m Nat) (o Nat)) (= (minus (S m) (S o)) (minus m o))))
(assert
  (forall ((m Nat) (n Nat)) (= (plus (P m) (P n)) (P (plus2 m n)))))
(assert
  (forall ((m Nat) (o Nat)) (= (plus (P m) (N o)) (minus m (S o)))))
(assert
  (forall ((m2 Nat) (n2 Nat))
    (= (plus (N m2) (P n2)) (minus n2 (S m2)))))
(assert
  (forall ((m2 Nat) (n3 Nat))
    (= (plus (N m2) (N n3)) (N (S (plus2 m2 n3))))))
(assert-not (forall ((x Integer)) (= x (plus zero x))))
(check-sat)
