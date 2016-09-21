(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun drop (Nat list) list)
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert-not
  (forall ((x Nat) (y Nat) (z list) (w Nat))
    (= (drop w (drop x (drop y z))) (drop y (drop x (drop w z))))))
(check-sat)
