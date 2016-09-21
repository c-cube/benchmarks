(declare-datatypes () ((A (X) (Y))))
(declare-datatypes ()
  ((R (Nil)
     (Eps) (Atom (Atom_0 A)) (Plus (Plus_0 R) (Plus_1 R))
     (Seq (Seq_0 R) (Seq_1 R)) (Star (Star_0 R)))))
(declare-datatypes () ((list (nil) (cons (head A) (tail list)))))
(declare-fun seq (R R) R)
(declare-fun plus (R R) R)
(declare-fun eqA (A A) Bool)
(declare-fun eqList (list list) Bool)
(declare-fun eps (R) Bool)
(declare-fun epsR (R) R)
(declare-fun step (R A) R)
(declare-fun recognise (R list) Bool)
(assert
  (forall ((x R) (y R))
    (=> (distinct x Nil)
      (=> (distinct y Nil)
        (=> (distinct x Eps)
          (=> (distinct y Eps) (= (seq x y) (Seq x y))))))))
(assert
  (forall ((x R))
    (=> (distinct x Nil)
      (=> (distinct Eps Nil) (=> (distinct x Eps) (= (seq x Eps) x))))))
(assert
  (forall ((y R))
    (=> (distinct Eps Nil) (=> (distinct y Nil) (= (seq Eps y) y)))))
(assert (forall ((x R)) (=> (distinct x Nil) (= (seq x Nil) Nil))))
(assert (forall ((y R)) (= (seq Nil y) Nil)))
(assert
  (forall ((x R) (y R))
    (=> (distinct x Nil)
      (=> (distinct y Nil) (= (plus x y) (Plus x y))))))
(assert (forall ((x R)) (=> (distinct x Nil) (= (plus x Nil) x))))
(assert (forall ((y R)) (= (plus Nil y) y)))
(assert (= (eqA X X) true))
(assert (= (eqA X Y) false))
(assert (= (eqA Y X) false))
(assert (= (eqA Y Y) true))
(assert (= (eqList nil nil) true))
(assert
  (forall ((z A) (x2 list)) (= (eqList nil (cons z x2)) false)))
(assert
  (forall ((x3 A) (xs list)) (= (eqList (cons x3 xs) nil) false)))
(assert
  (forall ((x3 A) (xs list) (y2 A) (ys list))
    (= (eqList (cons x3 xs) (cons y2 ys))
      (and (eqA x3 y2) (eqList xs ys)))))
(assert
  (forall ((x R))
    (=> (distinct x Eps)
      (=> (distinct x (Plus (Plus_0 x) (Plus_1 x)))
        (=> (distinct x (Seq (Seq_0 x) (Seq_1 x)))
          (=> (distinct x (Star (Star_0 x))) (= (eps x) false)))))))
(assert (= (eps Eps) true))
(assert
  (forall ((p R) (q R)) (= (eps (Plus p q)) (or (eps p) (eps q)))))
(assert
  (forall ((p2 R) (q2 R))
    (= (eps (Seq p2 q2)) (and (eps p2) (eps q2)))))
(assert (forall ((y R)) (= (eps (Star y)) true)))
(assert (forall ((x R)) (=> (= (eps x) true) (= (epsR x) Eps))))
(assert (forall ((x R)) (=> (= (eps x) false) (= (epsR x) Nil))))
(assert
  (forall ((x R) (y A))
    (=> (distinct x (Atom (Atom_0 x)))
      (=> (distinct x (Plus (Plus_0 x) (Plus_1 x)))
        (=> (distinct x (Seq (Seq_0 x) (Seq_1 x)))
          (=> (distinct x (Star (Star_0 x))) (= (step x y) Nil)))))))
(assert
  (forall ((y A) (a A))
    (=> (= (eqA a y) true) (= (step (Atom a) y) Eps))))
(assert
  (forall ((y A) (a A))
    (=> (= (eqA a y) false) (= (step (Atom a) y) Nil))))
(assert
  (forall ((y A) (p R) (q R))
    (= (step (Plus p q) y) (plus (step p y) (step q y)))))
(assert
  (forall ((y A) (p2 R) (q2 R))
    (= (step (Seq p2 q2) y)
      (plus (seq (step p2 y) q2) (seq (epsR p2) (step q2 y))))))
(assert
  (forall ((y A) (p3 R))
    (= (step (Star p3) y) (seq (step p3 y) (Star p3)))))
(assert (forall ((x R)) (= (recognise x nil) (eps x))))
(assert
  (forall ((x R) (z A) (xs list))
    (= (recognise x (cons z xs)) (recognise (step x z) xs))))
(assert-not
  (forall ((a A) (s list))
    (= (recognise (Atom a) s) (eqList s (cons a nil)))))
(check-sat)
