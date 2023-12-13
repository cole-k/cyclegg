((declare-datatypes ((Token 0))
  (((A) (B) (C) (D) (ESC) (P) (Q) (R))))
(declare-datatypes ((list 0))
  (((nil) (cons (head Token) (tail list)))))
(define-fun
  isSpecial
  ((x Token)) Bool
  (match x
    ((ESC true)
     (P true)
     (Q true)
     (R true)
     (_ false))))
(define-fun
  code
  ((x Token)) Token
  (match x
    ((ESC ESC)
     (P A)
     (Q B)
     (R C)
     (_ x))))
(define-fun-rec
  escape
  ((x list)) list
  (match x
    ((nil nil)
     ((cons y xs)
      (ite
        (isSpecial y) (cons ESC (cons (code y) (escape xs)))
        (cons y (escape xs)))))))
(assert
  (not
    (forall ((xs list) (ys list))
      (=> (= (escape xs) (escape ys)) (= xs ys)))))
(check-sat)
)