(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  min2
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z Z)
      (case (S z)
        (match y
          (case Z Z)
          (case (S x2) (S (min2 z x2)))))))
(assert-not (forall ((x Nat)) (= (min2 x x) x)))
(check-sat)
