((declare-datatypes ((Nat 0)) (((zero) (succ (p Nat)))))
(define-fun-rec
  minus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero zero)
     ((succ z)
      (match y
        (((succ y2) (minus z y2))
         (zero (succ z))))))))
(define-fun-rec
  lt
  ((x Nat) (y Nat)) Bool
  (match y
    ((zero false)
     ((succ z)
      (match x
        ((zero true)
         ((succ n) (lt n z))))))))
(define-fun-rec
  mod2
  ((x Nat) (y Nat)) Nat
  (match y
    ((zero zero)
     ((succ z)
      (ite (lt x (succ z)) x (mod2 (minus x (succ z)) (succ z)))))))
(define-fun-rec
  go
  ((x Nat) (y Nat) (z Nat)) Nat
  (match z
    ((zero zero)
     ((succ x2)
      (match x
        ((zero
          (match y
            ((zero zero)
             ((succ x3) (minus (succ x2) (succ x3))))))
         ((succ x4)
          (match y
            ((zero (go x4 x2 (succ x2)))
             ((succ x5) (go x4 x5 (succ x2))))))))))))
(define-fun
  mod_structural
  ((x Nat) (y Nat)) Nat (go x zero y))
(assert
  (not
    (forall ((m Nat) (n Nat)) (= (mod2 m n) (mod_structural m n)))))
(check-sat)
)