(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun take (Nat list) list)
(declare-fun drop (Nat list) list)
(declare-fun append (list list) list)
(assert (forall ((y list)) (= (take Z y) nil)))
(assert (forall ((z Nat)) (= (take (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (take (S z) (cons x2 x3)) (cons x2 (take z x3)))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert-not
  (forall ((n Nat) (xs list))
    (= (append (take n xs) (drop n xs)) xs)))
(check-sat)
