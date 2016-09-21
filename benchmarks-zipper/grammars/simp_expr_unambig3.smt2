(declare-datatypes () ((Tok (C) (D) (X) (Y) (Pl))))
(declare-datatypes () ((list (nil) (cons (head Tok) (tail list)))))
(declare-datatypes () ((E (Plus (Plus_0 E) (Plus_1 E)) (EX) (EY))))
(declare-fun append (list list) list)
(declare-fun lin (E) list)
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z Tok) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert
  (forall ((a E) (b E))
    (= (lin (Plus a b))
      (append
        (append (append (cons C nil) (lin a)) (cons D (cons Pl nil)))
        (lin b)))))
(assert (= (lin EX) (cons X nil)))
(assert (= (lin EY) (cons Y nil)))
(assert-not
  (forall ((u E) (v E)) (=> (= (lin u) (lin v)) (= u v))))
(check-sat)
