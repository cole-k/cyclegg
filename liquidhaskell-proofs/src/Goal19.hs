{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_19: (cyclegg_len (cyclegg_drop cyclegg_n cyclegg_xs)) = (cyclegg_sub (cyclegg_len cyclegg_xs) cyclegg_n)
module Goal19 where
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

{-@ reflect cyclegg_sub @-}
cyclegg_sub :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_sub x Cyclegg_Z = x
cyclegg_sub Cyclegg_Z y = Cyclegg_Z
cyclegg_sub (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_sub x y)

{-@ reflect cyclegg_drop @-}
cyclegg_drop :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_drop Cyclegg_Z xs = xs
cyclegg_drop (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_drop (Cyclegg_S n) (Cyclegg_Cons x xs) = (cyclegg_drop n xs)

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ goal_19 :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_len (cyclegg_drop cyclegg_n cyclegg_xs)) = (cyclegg_sub (cyclegg_len cyclegg_xs) cyclegg_n) } @-}
goal_19 :: Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> Proof
goal_19 cyclegg_n cyclegg_xs =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_60) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) ->
          -- case-split:goal_19:cyclegg_n=(Cyclegg_S cyclegg_n_60) =>
          -- case-split:goal_19:cyclegg_n=(Cyclegg_S cyclegg_n_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
          goal_19 (cyclegg_n_60) (cyclegg_xs_111)
          -- <= goal_19-(cyclegg_sub (cyclegg_len ?cyclegg_xs) ?cyclegg_n)=(cyclegg_len (cyclegg_drop ?cyclegg_n ?cyclegg_xs))
          -- <= (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= case-split:goal_19:cyclegg_n=(Cyclegg_S cyclegg_n_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111)
          -- <= case-split:goal_19:cyclegg_n=(Cyclegg_S cyclegg_n_60)
        (Cyclegg_Nil ) ->
          -- case-split:goal_19:cyclegg_n=(Cyclegg_S cyclegg_n_60) =>
          -- case-split:goal_19:cyclegg_n=(Cyclegg_S cyclegg_n_60):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
          -- (cyclegg_len Cyclegg_Nil) =>
          -- <= (cyclegg_sub Cyclegg_Z ?y)
          -- <= (cyclegg_len Cyclegg_Nil)
          -- <= case-split:goal_19:cyclegg_n=(Cyclegg_S cyclegg_n_60):cyclegg_xs=Cyclegg_Nil
          ()
    (Cyclegg_Z ) ->
      -- case-split:goal_19:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_drop Cyclegg_Z ?xs) =>
      -- <= (cyclegg_sub ?x Cyclegg_Z)
      -- <= case-split:goal_19:cyclegg_n=Cyclegg_Z
      ()


