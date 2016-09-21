(declare-sort sk 0)
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun minus (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(declare-fun mod2 (Nat Nat) Nat)
(declare-fun go (Nat Nat Nat) Nat)
(declare-fun mod_structural (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (minus Z y) Z)))
(assert (forall ((n Nat)) (= (minus (S n) Z) (S n))))
(assert
  (forall ((n Nat) (m Nat)) (= (minus (S n) (S m)) (minus n m))))
(assert (forall ((x Nat)) (= (lt x Z) false)))
(assert (forall ((z Nat)) (= (lt Z (S z)) true)))
(assert (forall ((z Nat) (n Nat)) (= (lt (S n) (S z)) (lt n z))))
(assert (forall ((x Nat)) (= (mod2 x Z) Z)))
(assert
  (forall ((x Nat) (z Nat))
    (=> (= (lt x (S z)) true) (= (mod2 x (S z)) x))))
(assert
  (forall ((x Nat) (z Nat))
    (=> (= (lt x (S z)) false)
      (= (mod2 x (S z)) (mod2 (minus x (S z)) (S z))))))
(assert (forall ((x Nat) (y Nat)) (= (go x y Z) Z)))
(assert (forall ((x2 Nat)) (= (go Z Z (S x2)) Z)))
(assert
  (forall ((x2 Nat) (n Nat))
    (= (go Z (S n) (S x2)) (minus (S x2) (S n)))))
(assert
  (forall ((x2 Nat) (m Nat))
    (= (go (S m) Z (S x2)) (go m x2 (S x2)))))
(assert
  (forall ((x2 Nat) (m Nat) (k Nat))
    (= (go (S m) (S k) (S x2)) (go m k (S x2)))))
(assert
  (forall ((x Nat) (y Nat)) (= (mod_structural x y) (go x Z y))))
(assert-not
  (forall ((m Nat) (n Nat)) (= (mod2 m n) (mod_structural m n))))
(check-sat)
