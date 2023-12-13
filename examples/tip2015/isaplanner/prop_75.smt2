((declare-datatypes ((Nat 0)) (((Z) (S (proj1-S Nat)))))
(declare-datatypes ((list 0))
  (((nil) (cons (head Nat) (tail list)))))
(define-fun-rec
  ==
  ((x Nat) (y Nat)) Bool
  (match x
    ((Z
      (match y
        ((Z true)
         ((S z) false))))
     ((S x2)
      (match y
        ((Z false)
         ((S y2) (== x2 y2))))))))
(define-fun-rec
  count
  ((x Nat) (y list)) Nat
  (match y
    ((nil Z)
     ((cons z ys) (ite (== x z) (S (count x ys)) (count x ys))))))
(define-fun-rec
  +2
  ((x Nat) (y Nat)) Nat
  (match x
    ((Z y)
     ((S z) (S (+2 z y))))))
(assert
  (not
    (forall ((n Nat) (m Nat) (xs list))
      (= (+2 (count n xs) (count n (cons m nil)))
        (count n (cons m xs))))))
(check-sat)
)