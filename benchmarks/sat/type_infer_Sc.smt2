(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes ()
  ((Ty (Arr (Arr_0 Ty) (Arr_1 Ty)) (A) (B) (C))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes (a) ((Maybe (Nothing) (Just (Just_0 a)))))
(declare-datatypes ()
  ((Expr (App (App_0 Expr) (App_1 Expr) (App_2 Ty))
     (Lam (Lam_0 Expr)) (Var (Var_0 Nat)))))
(define-fun y () Expr (Var (S Z)))
(define-fun-rec
  (par (a)
    (index
       ((x (list a)) (z Nat)) (Maybe a)
       (match x
         (case nil (as Nothing (Maybe a)))
         (case (cons x2 xs)
           (match z
             (case Z (Just x2))
             (case (S n) (index xs n))))))))
(define-fun-rec
  eqType
    ((x Ty) (z Ty)) Bool
    (match x
      (case (Arr a x2)
        (match z
          (case default false)
          (case (Arr b y2) (and (eqType a b) (eqType x2 y2)))))
      (case A
        (match z
          (case default false)
          (case A true)))
      (case B
        (match z
          (case default false)
          (case B true)))
      (case C
        (match z
          (case default false)
          (case C true)))))
(define-fun-rec
  tc
    ((x (list Ty)) (z Expr) (x2 Ty)) Bool
    (match z
      (case (App f x3 tx) (and (tc x f (Arr tx x2)) (tc x x3 tx)))
      (case (Lam e)
        (match x2
          (case default false)
          (case (Arr tx2 t) (tc (cons tx2 x) e t))))
      (case (Var x4)
        (match (index x x4)
          (case Nothing false)
          (case (Just tx3) (eqType tx3 x2))))))
(assert-not
  (forall ((t Ty)) (not (tc (as nil (list Ty)) (Lam (Lam y)) t))))
(check-sat)