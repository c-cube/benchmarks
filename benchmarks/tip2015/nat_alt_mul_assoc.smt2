; Property about an alternative multiplication function which exhibits an
; interesting recursion structure.
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  plus
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S n) (S (plus n y)))))
(define-fun-rec
  alt_mul
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z Z)
      (case (S z)
        (match y
          (case Z Z)
          (case (S x2) (S (plus (plus (alt_mul z x2) z) x2)))))))
(assert-not
  (forall ((x Nat) (y Nat) (z Nat))
    (= (alt_mul x (alt_mul y z)) (alt_mul (alt_mul x y) z))))
(check-sat)
