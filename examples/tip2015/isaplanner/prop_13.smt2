((declare-sort sk 0)
(declare-datatypes ((list 0))
  (((nil) (cons (head sk) (tail list)))))
(declare-datatypes ((Nat 0)) (((Z) (S (proj1-S Nat)))))
(define-fun-rec
  drop
  ((x Nat) (y list)) list
  (match x
    ((Z y)
     ((S z)
      (match y
        ((nil nil)
         ((cons x2 x3) (drop z x3))))))))
(assert
  (not
    (forall ((n Nat) (x sk) (xs list))
      (= (drop (S n) (cons x xs)) (drop n xs)))))
(check-sat)
)