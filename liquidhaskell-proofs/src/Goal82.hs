{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_82: (cyclegg_append (cyclegg_take cyclegg_n cyclegg_xs) (cyclegg_take (cyclegg_sub cyclegg_n (cyclegg_len cyclegg_xs)) cyclegg_ys)) = (cyclegg_take cyclegg_n (cyclegg_append cyclegg_xs cyclegg_ys))
module Goal82 where
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

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_take @-}
cyclegg_take :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_take Cyclegg_Z xs = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) (Cyclegg_Cons x xs) = (Cyclegg_Cons x (cyclegg_take n xs))

{-@ reflect cyclegg_sub @-}
cyclegg_sub :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_sub x Cyclegg_Z = x
cyclegg_sub Cyclegg_Z y = Cyclegg_Z
cyclegg_sub (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_sub x y)

{-@ goal_82 :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> cyclegg_ys: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_take cyclegg_n cyclegg_xs) (cyclegg_take (cyclegg_sub cyclegg_n (cyclegg_len cyclegg_xs)) cyclegg_ys)) = (cyclegg_take cyclegg_n (cyclegg_append cyclegg_xs cyclegg_ys)) } @-}
goal_82 :: Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
goal_82 cyclegg_n cyclegg_xs cyclegg_ys =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_100) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171) ->
          -- case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100) =>
          -- case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171) =>
          -- (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100) =>
          -- case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          -- (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          goal_82 (cyclegg_n_100) (cyclegg_xs_171) (cyclegg_ys)
          -- <= goal_82-(cyclegg_take ?cyclegg_n (cyclegg_append ?cyclegg_xs ?cyclegg_ys))=(cyclegg_append (cyclegg_take ?cyclegg_n ?cyclegg_xs) (cyclegg_take (cyclegg_sub ?cyclegg_n (cyclegg_len ?cyclegg_xs)) ?cyclegg_ys))
          -- <= (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
          -- <= case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100)
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          -- <= case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171)
        (Cyclegg_Nil ) ->
          -- case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100) =>
          -- case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil) =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_len Cyclegg_Nil) =>
          -- (cyclegg_sub ?x Cyclegg_Z) =>
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          -- <= case-split:goal_82:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil
          ()
    (Cyclegg_Z ) ->
      -- case-split:goal_82:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_take Cyclegg_Z ?xs) =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- case-split:goal_82:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_sub Cyclegg_Z ?y) =>
      -- (cyclegg_take Cyclegg_Z ?xs) =>
      -- <= (cyclegg_take Cyclegg_Z ?xs)
      -- <= case-split:goal_82:cyclegg_n=Cyclegg_Z
      ()


