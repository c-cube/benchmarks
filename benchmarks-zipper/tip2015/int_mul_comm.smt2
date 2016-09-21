(declare-sort sk 0)
(declare-datatypes () ((Sign (Pos) (Neg))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((Integer (P (P_0 Nat)) (N (N_0 Nat)))))
(declare-fun toInteger (Sign Nat) Integer)
(declare-fun sign (Integer) Sign)
(declare-fun plus (Nat Nat) Nat)
(declare-fun opposite (Sign) Sign)
(declare-fun timesSign (Sign Sign) Sign)
(declare-fun mult (Nat Nat) Nat)
(declare-fun absVal (Integer) Nat)
(declare-fun times (Integer Integer) Integer)
(assert (forall ((y Nat)) (= (toInteger Pos y) (P y))))
(assert (= (toInteger Neg Z) (P Z)))
(assert (forall ((m Nat)) (= (toInteger Neg (S m)) (N m))))
(assert (forall ((y Nat)) (= (sign (P y)) Pos)))
(assert (forall ((z Nat)) (= (sign (N z)) Neg)))
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (= (opposite Pos) Neg))
(assert (= (opposite Neg) Pos))
(assert (forall ((y Sign)) (= (timesSign Pos y) y)))
(assert (forall ((y Sign)) (= (timesSign Neg y) (opposite y))))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (n Nat)) (= (mult (S n) y) (plus y (mult n y)))))
(assert (forall ((n Nat)) (= (absVal (P n)) n)))
(assert (forall ((m Nat)) (= (absVal (N m)) (S m))))
(assert
  (forall ((x Integer) (y Integer))
    (= (times x y)
      (toInteger (timesSign (sign x) (sign y))
        (mult (absVal x) (absVal y))))))
(assert-not
  (forall ((x Integer) (y Integer)) (= (times x y) (times y x))))
(check-sat)
