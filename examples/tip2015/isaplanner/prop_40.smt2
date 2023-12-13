((declare-sort sk 0)
(declare-datatypes ((list 0))
  (((nil) (cons (head sk) (tail list)))))
(declare-datatypes ((Nat 0)) (((Z) (S (proj1-S Nat)))))
(define-fun-rec
  take
  ((x Nat) (y list)) list
  (match x
    ((Z nil)
     ((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (cons x2 (take z x3)))))))))
(assert (not (forall ((xs list)) (= (take Z xs) nil))))
(check-sat)
)