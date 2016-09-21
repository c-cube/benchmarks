(declare-datatypes () ((It (A) (B) (C))))
(declare-datatypes () ((list (nil) (cons (head It) (tail list)))))
(declare-fun eq (It It) Bool)
(declare-fun isPrefix (list list) Bool)
(declare-fun isRelaxedPrefix (list list) Bool)
(declare-fun append (list list) list)
(assert (forall ((y It)) (=> (distinct y A) (= (eq A y) false))))
(assert (= (eq A A) true))
(assert (forall ((y It)) (=> (distinct y B) (= (eq B y) false))))
(assert (= (eq B B) true))
(assert (forall ((y It)) (=> (distinct y C) (= (eq C y) false))))
(assert (= (eq C C) true))
(assert (forall ((y list)) (= (isPrefix nil y) true)))
(assert
  (forall ((z It) (x2 list)) (= (isPrefix (cons z x2) nil) false)))
(assert
  (forall ((z It) (x2 list) (x3 It) (x4 list))
    (= (isPrefix (cons z x2) (cons x3 x4))
      (and (eq z x3) (isPrefix x2 x4)))))
(assert (forall ((y list)) (= (isRelaxedPrefix nil y) true)))
(assert
  (forall ((y list) (z It))
    (= (isRelaxedPrefix (cons z nil) y) true)))
(assert
  (forall ((z It) (x3 It) (x4 list))
    (= (isRelaxedPrefix (cons z (cons x3 x4)) nil) false)))
(assert
  (forall ((z It) (x3 It) (x4 list) (x5 It) (x6 list))
    (=> (= (eq z x5) true)
      (= (isRelaxedPrefix (cons z (cons x3 x4)) (cons x5 x6))
        (isRelaxedPrefix (cons x3 x4) x6)))))
(assert
  (forall ((z It) (x3 It) (x4 list) (x5 It) (x6 list))
    (=> (= (eq z x5) false)
      (= (isRelaxedPrefix (cons z (cons x3 x4)) (cons x5 x6))
        (isPrefix (cons x3 x4) (cons x5 x6))))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z It) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert-not
  (forall ((x It) (xs list) (ys list))
    (isRelaxedPrefix (cons x xs) (append xs ys))))
(check-sat)
