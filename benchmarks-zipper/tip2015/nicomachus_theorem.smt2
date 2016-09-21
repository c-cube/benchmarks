(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun sum (Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun cubes (Nat) Nat)
(assert (forall ((y Nat)) (= (plus Z y) y)))
(assert
  (forall ((y Nat) (n Nat)) (= (plus (S n) y) (S (plus n y)))))
(assert (= (sum Z) Z))
(assert (forall ((n Nat)) (= (sum (S n)) (plus (sum n) (S n)))))
(assert (forall ((y Nat)) (= (mult Z y) Z)))
(assert
  (forall ((y Nat) (n Nat)) (= (mult (S n) y) (plus y (mult n y)))))
(assert (= (cubes Z) Z))
(assert
  (forall ((n Nat))
    (= (cubes (S n))
      (plus (cubes n) (mult (mult (S n) (S n)) (S n))))))
(assert-not
  (forall ((n Nat)) (= (cubes n) (mult (sum n) (sum n)))))
(check-sat)
