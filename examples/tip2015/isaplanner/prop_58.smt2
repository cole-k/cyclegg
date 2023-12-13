((declare-sort sk 0)
(declare-datatypes ((pair 0))
  (((pair2 (proj1-pair sk) (proj2-pair sk)))))
(declare-datatypes ((list2 0))
  (((nil2) (cons2 (head2 sk) (tail2 list2)))))
(declare-datatypes ((list 0))
  (((nil) (cons (head pair) (tail list)))))
(declare-datatypes ((Nat 0)) (((Z) (S (proj1-S Nat)))))
(define-fun-rec
  zip
  ((x list2) (y list2)) list
  (match x
    ((nil2 nil)
     ((cons2 z x2)
      (match y
        ((nil2 nil)
         ((cons2 x3 x4) (cons (pair2 z x3) (zip x2 x4)))))))))
(define-fun-rec
  drop2
  ((x Nat) (y list2)) list2
  (match x
    ((Z y)
     ((S z)
      (match y
        ((nil2 nil2)
         ((cons2 x2 x3) (drop2 z x3))))))))
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
    (forall ((n Nat) (xs list2) (ys list2))
      (= (drop n (zip xs ys)) (zip (drop2 n xs) (drop2 n ys))))))
(check-sat)
)