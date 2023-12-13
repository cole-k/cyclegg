((declare-datatypes ((Nat 0)) (((zero) (succ (p Nat)))))
(define-fun-rec
  lt
  ((x Nat) (y Nat)) Bool
  (match y
    ((zero false)
     ((succ z)
      (match x
        ((zero true)
         ((succ n) (lt n z))))))))
(assert
  (not (forall ((x Nat) (y Nat)) (=> (lt x y) (not (lt y x))))))
(check-sat)
)