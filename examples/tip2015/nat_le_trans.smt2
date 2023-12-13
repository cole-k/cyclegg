((declare-datatypes ((Nat 0)) (((zero) (succ (p Nat)))))
(define-fun-rec
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (=> (leq x y) (=> (leq y z) (leq x z))))))
(check-sat)
)