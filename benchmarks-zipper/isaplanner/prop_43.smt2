(declare-sort fun1 2)
(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(declare-fun (par (a b) (apply1 ((fun1 a b) a) b)))
(declare-fun takeWhile ((fun1 sk Bool) list) list)
(declare-fun dropWhile ((fun1 sk Bool) list) list)
(declare-fun append (list list) list)
(assert (forall ((x (fun1 sk Bool))) (= (takeWhile x nil) nil)))
(assert
  (forall ((x (fun1 sk Bool)) (z sk) (xs list))
    (=> (= (apply1 x z) true)
      (= (takeWhile x (cons z xs)) (cons z (takeWhile x xs))))))
(assert
  (forall ((x (fun1 sk Bool)) (z sk) (xs list))
    (=> (= (apply1 x z) false) (= (takeWhile x (cons z xs)) nil))))
(assert (forall ((x (fun1 sk Bool))) (= (dropWhile x nil) nil)))
(assert
  (forall ((x (fun1 sk Bool)) (z sk) (xs list))
    (=> (= (apply1 x z) true)
      (= (dropWhile x (cons z xs)) (dropWhile x xs)))))
(assert
  (forall ((x (fun1 sk Bool)) (z sk) (xs list))
    (=> (= (apply1 x z) false)
      (= (dropWhile x (cons z xs)) (cons z xs)))))
(assert (forall ((y list)) (= (append nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (append (cons z xs) y) (cons z (append xs y)))))
(assert-not
  (forall ((p (fun1 sk Bool)) (xs list))
    (= (append (takeWhile p xs) (dropWhile p xs)) xs)))
(check-sat)
