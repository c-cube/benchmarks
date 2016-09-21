(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun minus (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (minus Z y) Z)))
(assert (forall ((z Nat)) (= (minus (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (minus (S z) (S x2)) (minus z x2))))
(assert-not
  (forall ((m Nat) (n Nat) (k Nat))
    (= (minus (minus (S m) n) (S k)) (minus (minus m n) k))))
(check-sat)
