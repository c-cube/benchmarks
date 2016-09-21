(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun op (Nat Nat Nat Nat) Nat)
(assert (forall ((y Nat) (x2 Nat)) (= (op Z y Z x2) x2)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 Nat))
    (= (op Z y (S x3) x2) (op Z y x3 (S x2)))))
(assert
  (forall ((y Nat) (x2 Nat) (x4 Nat))
    (= (op (S x4) y Z x2) (op x4 y y x2))))
(assert
  (forall ((y Nat) (x2 Nat) (x4 Nat) (c Nat))
    (= (op (S x4) y (S c) x2) (op (S x4) y c (S x2)))))
(assert-not
  (forall ((x Nat) (a Nat) (b Nat) (c Nat) (d Nat))
    (= (op (op x a a a) b c d) (op a (op b x b b) c d))))
(check-sat)
