((declare-datatypes ((Nat 0)) (((zero) (succ (p Nat)))))
(declare-datatypes ((list2 0))
  (((nil2) (cons2 (head2 Nat) (tail2 list2)))))
(declare-datatypes ((list 0))
  (((nil) (cons (head list2) (tail list)))))
(define-fun-rec
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(define-fun-rec
  lmerge
  ((x list2) (y list2)) list2
  (match x
    ((nil2 y)
     ((cons2 z x2)
      (match y
        ((nil2 (cons2 z x2))
         ((cons2 x3 x4)
          (ite
            (leq z x3) (cons2 z (lmerge x2 (cons2 x3 x4)))
            (cons2 x3 (lmerge (cons2 z x2) x4))))))))))
(define-fun-rec
  pairwise
  ((x list)) list
  (match x
    ((nil nil)
     ((cons xs y)
      (match y
        ((nil (cons xs nil))
         ((cons ys xss) (cons (lmerge xs ys) (pairwise xss)))))))))
(define-fun-rec
  mergingbu2
  ((x list)) list2
  (match x
    ((nil nil2)
     ((cons xs y)
      (match y
        ((nil xs)
         ((cons z x2) (mergingbu2 (pairwise (cons xs (cons z x2)))))))))))
(define-fun-rec
  ordered
  ((x list2)) Bool
  (match x
    ((nil2 true)
     ((cons2 y z)
      (match z
        ((nil2 true)
         ((cons2 y2 xs) (and (leq y y2) (ordered (cons2 y2 xs))))))))))
(define-fun-rec
  risers
  ((x list2)) list
  (match x
    ((nil2 nil)
     ((cons2 y z)
      (match z
        ((nil2 (cons (cons2 y nil2) nil))
         ((cons2 y2 xs)
          (ite
            (leq y y2)
            (match (risers (cons2 y2 xs))
              ((nil nil)
               ((cons ys yss) (cons (cons2 y ys) yss))))
            (cons (cons2 y nil2) (risers (cons2 y2 xs)))))))))))
(define-fun
  msortbu2
  ((x list2)) list2 (mergingbu2 (risers x)))
(assert (not (forall ((xs list2)) (ordered (msortbu2 xs)))))
(check-sat)
)