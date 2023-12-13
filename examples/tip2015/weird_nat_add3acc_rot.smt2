((declare-datatypes ((Nat 0)) (((zero) (succ (p Nat)))))
(define-fun-rec
  add3acc
  ((x Nat) (y Nat) (z Nat)) Nat
  (match x
    ((zero
      (match y
        ((zero z)
         ((succ x2) (add3acc zero x2 (succ z))))))
     ((succ x3) (add3acc x3 (succ y) z)))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (= (add3acc x y z) (add3acc y x z)))))
(check-sat)
)