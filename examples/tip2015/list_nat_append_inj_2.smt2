((declare-sort sk 0)
(declare-datatypes ((list 0))
  (((nil) (cons (head sk) (tail list)))))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(assert
  (not
    (forall ((xs list) (ys list) (zs list))
      (=> (= (++ xs ys) (++ xs zs)) (= ys zs)))))
(check-sat)
)