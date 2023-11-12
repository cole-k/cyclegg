{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_77: (cyclegg_count cyclegg_n (cyclegg_append cyclegg_xs (Cyclegg_Cons cyclegg_m Cyclegg_Nil))) = (cyclegg_count cyclegg_n cyclegg_xs)
module Goal77 where
import Language.Haskell.Liquid.Equational

{-@ autosize Cyclegg_List @-}
data Cyclegg_List cyclegg_a where
  Cyclegg_Nil :: (Cyclegg_List cyclegg_a)
  Cyclegg_Cons :: (cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))

{-@ autosize Cyclegg_Tree @-}
data Cyclegg_Tree cyclegg_a where
  Cyclegg_Leaf :: (Cyclegg_Tree cyclegg_a)
  Cyclegg_Node :: ((Cyclegg_Tree cyclegg_a) -> cyclegg_a -> (Cyclegg_Tree cyclegg_a) -> (Cyclegg_Tree cyclegg_a))

{-@ autosize Cyclegg_Bool @-}
data Cyclegg_Bool where
  Cyclegg_True :: Cyclegg_Bool
  Cyclegg_False :: Cyclegg_Bool

{-@ autosize Cyclegg_Tm @-}
data Cyclegg_Tm cyclegg_a where
  Cyclegg_Var :: (cyclegg_a -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_Cst :: (Cyclegg_Nat -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_App :: ((Cyclegg_Expr cyclegg_a) -> (Cyclegg_Expr cyclegg_a) -> (Cyclegg_Tm cyclegg_a))

{-@ autosize Cyclegg_Pair @-}
data Cyclegg_Pair cyclegg_a cyclegg_b where
  Cyclegg_Pair :: (cyclegg_a -> cyclegg_b -> (Cyclegg_Pair cyclegg_a cyclegg_b))

{-@ autosize Cyclegg_Expr @-}
data Cyclegg_Expr cyclegg_a where
  Cyclegg_MkExpr :: ((Cyclegg_Tm cyclegg_a) -> Cyclegg_Nat -> (Cyclegg_Expr cyclegg_a))

{-@ autosize Cyclegg_Nat @-}
data Cyclegg_Nat where
  Cyclegg_Z :: Cyclegg_Nat
  Cyclegg_S :: (Cyclegg_Nat -> Cyclegg_Nat)

{-@ unreachable :: {v: a | false} -> b @-}
unreachable :: a -> b
unreachable x = error "unreachable"

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ goal_77 :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_count cyclegg_n (cyclegg_append cyclegg_xs (Cyclegg_Cons cyclegg_m Cyclegg_Nil))) = (cyclegg_count cyclegg_n cyclegg_xs) } @-}
goal_77 :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
goal_77 cyclegg_n cyclegg_m cyclegg_xs =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_100) ->
      case cyclegg_m of
        (Cyclegg_S cyclegg_m_150) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) ->
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150) =>
              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150)
              goal_77 (cyclegg_n) (cyclegg_m) (cyclegg_xs_231)
              -- goal_77-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n ?cyclegg_xs) =>
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150)
              ? goal_77 (cyclegg_n) (cyclegg_m) (cyclegg_xs_231)
              -- goal_77-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n ?cyclegg_xs) =>
              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231)
            (Cyclegg_Nil ) ->
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_append Cyclegg_Nil ?ys) =>
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil
              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100) =>
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150) =>
              -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_count ?x Cyclegg_Nil) =>
              -- <= (cyclegg_count ?x Cyclegg_Nil)
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_count ?x Cyclegg_Nil) =>
              -- <= (cyclegg_count ?x Cyclegg_Nil)
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil
              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil =>
              -- <= (cyclegg_append Cyclegg_Nil ?ys)
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil
              goal_77 (cyclegg_n_100) (cyclegg_m_150) (cyclegg_xs)
              -- goal_77-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n ?cyclegg_xs) =>
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_count ?x Cyclegg_Nil) =>
              -- <= (cyclegg_count ?x Cyclegg_Nil)
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=(Cyclegg_S cyclegg_m_150):cyclegg_xs=Cyclegg_Nil
        (Cyclegg_Z ) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161) ->
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z =>
              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z
              goal_77 (cyclegg_n) (cyclegg_m) (cyclegg_xs_161)
              -- goal_77-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n ?cyclegg_xs) =>
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z
              ? goal_77 (cyclegg_n) (cyclegg_m) (cyclegg_xs_161)
              -- goal_77-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n ?cyclegg_xs) =>
              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161)
            (Cyclegg_Nil ) ->
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_append Cyclegg_Nil ?ys) =>
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_count ?x Cyclegg_Nil) =>
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_count ?x Cyclegg_Nil) =>
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z
              -- premise (cyclegg_eq cyclegg_n cyclegg_m)=Cyclegg_False =>
              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
              -- case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z =>
              -- <= (cyclegg_count ?x Cyclegg_Nil)
              -- <= case-split:goal_77:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
              ()
    (Cyclegg_Z ) ->
      case cyclegg_m of
        (Cyclegg_S cyclegg_m_110) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171) ->
              -- case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110) =>
              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
              -- <= case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110)
              goal_77 (cyclegg_n) (cyclegg_m) (cyclegg_xs_171)
              -- goal_77-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n ?cyclegg_xs) =>
              -- <= case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110)
              ? goal_77 (cyclegg_n) (cyclegg_m) (cyclegg_xs_171)
              -- goal_77-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n ?cyclegg_xs) =>
              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
              -- <= case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171)
            (Cyclegg_Nil ) ->
              -- case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_append Cyclegg_Nil ?ys) =>
              -- <= case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110):cyclegg_xs=Cyclegg_Nil
              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
              -- case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_count ?x Cyclegg_Nil) =>
              -- <= case-split:goal_77:cyclegg_n=Cyclegg_Z
              -- case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_count ?x Cyclegg_Nil) =>
              -- <= case-split:goal_77:cyclegg_n=Cyclegg_Z
              -- premise (cyclegg_eq cyclegg_n cyclegg_m)=Cyclegg_False =>
              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
              -- case-split:goal_77:cyclegg_n=Cyclegg_Z =>
              -- <= (cyclegg_count ?x Cyclegg_Nil)
              -- <= case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_110):cyclegg_xs=Cyclegg_Nil
              ()
        (Cyclegg_Z ) ->
          unreachable (
            -- <= premise (cyclegg_eq cyclegg_n cyclegg_m)=Cyclegg_False
            -- case-split:goal_77:cyclegg_n=Cyclegg_Z =>
            -- case-split:goal_77:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z =>
            -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
            ()
          )



