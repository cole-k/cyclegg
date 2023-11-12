{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_19: (cyclegg_append (cyclegg_rev (cyclegg_rev cyclegg_x)) cyclegg_y) = (cyclegg_rev (cyclegg_rev (cyclegg_append cyclegg_x cyclegg_y)))
module Clam19 where
import Language.Haskell.Liquid.Equational

{-@ autosize Cyclegg_Expr @-}
data Cyclegg_Expr cyclegg_a where
  Cyclegg_MkExpr :: ((Cyclegg_Tm cyclegg_a) -> Cyclegg_Nat -> (Cyclegg_Expr cyclegg_a))

{-@ autosize Cyclegg_Bool @-}
data Cyclegg_Bool where
  Cyclegg_True :: Cyclegg_Bool
  Cyclegg_False :: Cyclegg_Bool

{-@ autosize Cyclegg_List @-}
data Cyclegg_List cyclegg_a where
  Cyclegg_Nil :: (Cyclegg_List cyclegg_a)
  Cyclegg_Cons :: (cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))

{-@ autosize Cyclegg_Tree @-}
data Cyclegg_Tree cyclegg_a where
  Cyclegg_Leaf :: (Cyclegg_Tree cyclegg_a)
  Cyclegg_Node :: ((Cyclegg_Tree cyclegg_a) -> cyclegg_a -> (Cyclegg_Tree cyclegg_a) -> (Cyclegg_Tree cyclegg_a))

{-@ autosize Cyclegg_Nat @-}
data Cyclegg_Nat where
  Cyclegg_Z :: Cyclegg_Nat
  Cyclegg_S :: (Cyclegg_Nat -> Cyclegg_Nat)

{-@ autosize Cyclegg_Pair @-}
data Cyclegg_Pair cyclegg_a cyclegg_b where
  Cyclegg_Pair :: (cyclegg_a -> cyclegg_b -> (Cyclegg_Pair cyclegg_a cyclegg_b))

{-@ autosize Cyclegg_Tm @-}
data Cyclegg_Tm cyclegg_a where
  Cyclegg_Var :: (cyclegg_a -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_Cst :: (Cyclegg_Nat -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_App :: ((Cyclegg_Expr cyclegg_a) -> (Cyclegg_Expr cyclegg_a) -> (Cyclegg_Tm cyclegg_a))

{-@ unreachable :: {v: a | false} -> b @-}
unreachable :: a -> b
unreachable x = error "unreachable"

{-@ reflect cyclegg_rev @-}
cyclegg_rev :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_rev Cyclegg_Nil = Cyclegg_Nil
cyclegg_rev (Cyclegg_Cons x xs) = (cyclegg_append (cyclegg_rev xs) (Cyclegg_Cons x Cyclegg_Nil))

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ clam_19 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_rev (cyclegg_rev cyclegg_x)) cyclegg_y) = (cyclegg_rev (cyclegg_rev (cyclegg_append cyclegg_x cyclegg_y))) } @-}
clam_19 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
clam_19 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_80 cyclegg_x_81) ->
      lemma_9 (cyclegg_x)
      -- <= lemma_9-?cyclegg_x=(cyclegg_rev (cyclegg_rev ?cyclegg_x))
      ? lemma_9 ((cyclegg_append cyclegg_x cyclegg_y))
      -- lemma_9-?cyclegg_x=(cyclegg_rev (cyclegg_rev ?cyclegg_x)) =>
    (Cyclegg_Nil ) ->
      lemma_9 ((cyclegg_append (cyclegg_rev (cyclegg_rev cyclegg_x)) cyclegg_y))
      -- lemma_9-?cyclegg_x=(cyclegg_rev (cyclegg_rev ?cyclegg_x)) =>
      ? lemma_9 (cyclegg_x)
      -- lemma_9-(cyclegg_rev (cyclegg_rev ?cyclegg_x))=?cyclegg_x =>


{-@ lemma_10 :: fresh_13: (Cyclegg_List cyclegg_a) -> cyclegg_x_30: cyclegg_a -> { (Cyclegg_Cons cyclegg_x_30 (cyclegg_rev fresh_13)) = (cyclegg_rev (cyclegg_append fresh_13 (Cyclegg_Cons cyclegg_x_30 Cyclegg_Nil))) } @-}
lemma_10 :: (Cyclegg_List cyclegg_a) -> cyclegg_a -> Proof
lemma_10 fresh_13 cyclegg_x_30 =
  case fresh_13 of
    (Cyclegg_Cons fresh_13_80 fresh_13_81) ->
      -- case-split:lemma_10:fresh_13=(Cyclegg_Cons fresh_13_80 fresh_13_81) =>
      -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      lemma_10 (fresh_13_81) (cyclegg_x_30)
      -- lemma_10-(Cyclegg_Cons ?cyclegg_x_30 (cyclegg_rev ?fresh_13))=(cyclegg_rev (cyclegg_append ?fresh_13 (Cyclegg_Cons ?cyclegg_x_30 Cyclegg_Nil))) =>
      -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      -- <= case-split:lemma_10:fresh_13=(Cyclegg_Cons fresh_13_80 fresh_13_81)
    (Cyclegg_Nil ) ->
      -- case-split:lemma_10:fresh_13=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= (cyclegg_rev Cyclegg_Nil)
      -- <= case-split:lemma_10:fresh_13=Cyclegg_Nil
      -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
      -- case-split:lemma_10:fresh_13=Cyclegg_Nil =>
      -- <= (cyclegg_rev Cyclegg_Nil)
      -- <= case-split:lemma_10:fresh_13=Cyclegg_Nil
      -- case-split:lemma_10:fresh_13=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:lemma_10:fresh_13=Cyclegg_Nil
      ()


{-@ lemma_9 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> { (cyclegg_rev (cyclegg_rev cyclegg_x)) = cyclegg_x } @-}
lemma_9 :: (Cyclegg_List cyclegg_a) -> Proof
lemma_9 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_30 cyclegg_x_31) ->
      -- case-split:lemma_9:cyclegg_x=(Cyclegg_Cons cyclegg_x_30 cyclegg_x_31) =>
      -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
      lemma_10 ((cyclegg_rev cyclegg_x_31)) (cyclegg_x_30)
      -- <= lemma_10-(Cyclegg_Cons ?cyclegg_x_30 (cyclegg_rev ?fresh_13))=(cyclegg_rev (cyclegg_append ?fresh_13 (Cyclegg_Cons ?cyclegg_x_30 Cyclegg_Nil)))
      ? lemma_9 (cyclegg_x_31)
      -- <= lemma_9-?cyclegg_x=(cyclegg_rev (cyclegg_rev ?cyclegg_x))
      -- <= case-split:lemma_9:cyclegg_x=(Cyclegg_Cons cyclegg_x_30 cyclegg_x_31)
    (Cyclegg_Nil ) ->
      -- case-split:lemma_9:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- <= case-split:lemma_9:cyclegg_x=Cyclegg_Nil
      ()


