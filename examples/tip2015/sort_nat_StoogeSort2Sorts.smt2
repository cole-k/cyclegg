((declare-datatypes ((Nat 0)) (((zero) (succ (p Nat)))))
(declare-datatypes ((list 0))
  (((nil) (cons (head Nat) (tail list)))))
(declare-datatypes ((pair 0))
  (((pair2 (proj1-pair list) (proj2-pair list)))))
(define-fun-rec
  take
  ((x Nat) (y list)) list
  (match x
    ((zero nil)
     ((succ z)
      (match y
        ((nil nil)
         ((cons z2 xs) (cons z2 (take z xs)))))))))
(define-fun-rec
  plus
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero y)
     ((succ z) (succ (plus z y))))))
(define-fun-rec
  times
  ((x Nat) (y Nat)) Nat
  (match x
    ((zero zero)
     ((succ z) (plus y (times z y))))))
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
  leq
  ((x Nat) (y Nat)) Bool
  (match x
    ((zero true)
     ((succ z)
      (match y
        ((zero false)
         ((succ x2) (leq z x2))))))))
(define-fun-rec
  ordered
  ((x list)) Bool
  (match x
    ((nil true)
     ((cons y z)
      (match z
        ((nil true)
         ((cons y2 xs) (and (leq y y2) (ordered (cons y2 xs))))))))))
(define-fun
  sort2
  ((x Nat) (y Nat)) list
  (ite (leq x y) (cons x (cons y nil)) (cons y (cons x nil))))
(define-fun-rec
  length
  ((x list)) Nat
  (match x
    ((nil zero)
     ((cons y l) (plus (succ zero) (length l))))))
(define-fun-rec
  idiv
  ((x Nat) (y Nat)) Nat
  (ite (lt x y) zero (succ (idiv (minus x y) y))))
(define-fun-rec
  drop
  ((x Nat) (y list)) list
  (match x
    ((zero y)
     ((succ z)
      (match y
        ((nil nil)
         ((cons z2 xs1) (drop z xs1))))))))
(define-fun
  splitAt
  ((x Nat) (y list)) pair (pair2 (take x y) (drop x y)))
(define-fun-rec
  ++
  ((x list) (y list)) list
  (match x
    ((nil y)
     ((cons z xs) (cons z (++ xs y))))))
(define-funs-rec
  ((stooge2sort2
    ((x list)) list)
   (stoogesort2
    ((x list)) list)
   (stooge2sort1
    ((x list)) list))
  ((match
     (splitAt
       (idiv (succ (times (succ (succ zero)) (length x)))
         (succ (succ (succ zero))))
       x)
     (((pair2 ys1 zs) (++ (stoogesort2 ys1) zs))))
   (match x
     ((nil nil)
      ((cons y z)
       (match z
         ((nil (cons y nil))
          ((cons y2 x2)
           (match x2
             ((nil (sort2 y y2))
              ((cons x3 x4)
               (stooge2sort2
                 (stooge2sort1
                   (stooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))))))))
   (match (splitAt (idiv (length x) (succ (succ (succ zero)))) x)
     (((pair2 ys1 zs) (++ ys1 (stoogesort2 zs)))))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times x (times y z)) (times (times x y) z))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (times x y) (times y x))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times x (plus y z)) (plus (times x y) (times x z)))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times (plus x y) z) (plus (times x z) (times y z)))))
(assert (forall ((x Nat)) (= (times x (succ zero)) x)))
(assert (forall ((x Nat)) (= (times (succ zero) x) x)))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (forall ((x Nat)) (= (times x zero) zero)))
(assert (forall ((x Nat)) (= (times zero x) zero)))
(assert (not (forall ((xs list)) (ordered (stoogesort2 xs)))))
(check-sat)
)