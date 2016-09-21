(declare-sort fun1 2)
(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-fun (par (a b) (apply1 ((fun1 a b) a) b)))
(declare-fun filter ((fun1 sk Bool) list) list)
(declare-fun append (list list) list)
(declare-fun rev (list) list)
(assert (forall ((x (fun1 sk Bool))) (= (filter x nil) nil)))
(assert
  (forall ((x (fun1 sk Bool)) (z sk) (xs list))
    (=> (= (apply1 x z) true)
      (= (filter x (cons z xs)) (cons z (filter x xs))))))
(assert
  (forall ((x (fun1 sk Bool)) (z sk) (xs list))
    (=> (= (apply1 x z) false)
      (= (filter x (cons z xs)) (filter x xs)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert (= (rev nil) nil))
(assert
  (forall ((y sk) (xs list))
    (= (rev (cons y xs)) (append (rev xs) (cons y nil)))))
(assert-not
  (forall ((p (fun1 sk Bool)) (xs list))
    (= (rev (filter p xs)) (filter p (rev xs)))))
(check-sat)
