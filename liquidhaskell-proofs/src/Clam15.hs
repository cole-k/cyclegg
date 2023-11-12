{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_15: (Cyclegg_S (cyclegg_plus cyclegg_x cyclegg_x)) = (cyclegg_plus cyclegg_x (Cyclegg_S cyclegg_x))
module Clam15 where
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

{-@ reflect cyclegg_plus @-}
cyclegg_plus :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_plus Cyclegg_Z y = y
cyclegg_plus (Cyclegg_S x) y = (Cyclegg_S (cyclegg_plus x y))

{-@ clam_15 :: cyclegg_x: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_plus cyclegg_x cyclegg_x)) = (cyclegg_plus cyclegg_x (Cyclegg_S cyclegg_x)) } @-}
clam_15 :: Cyclegg_Nat -> Proof
clam_15 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_50) ->
      -- case-split:clam_15:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
      -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
      lemma_2 (cyclegg_x_50) (cyclegg_x)
      -- <= lemma_2-(cyclegg_plus ?cyclegg_x_50 (Cyclegg_S ?fresh_14))=(Cyclegg_S (cyclegg_plus ?cyclegg_x_50 ?fresh_14))
      -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
      -- <= case-split:clam_15:cyclegg_x=(Cyclegg_S cyclegg_x_50)
    (Cyclegg_Z ) ->
      lemma_2 (cyclegg_x) (cyclegg_x)
      -- <= lemma_2-(cyclegg_plus ?cyclegg_x_50 (Cyclegg_S ?fresh_14))=(Cyclegg_S (cyclegg_plus ?cyclegg_x_50 ?fresh_14))


{-@ lemma_2 :: cyclegg_x_50: Cyclegg_Nat -> fresh_14: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_plus cyclegg_x_50 fresh_14)) = (cyclegg_plus cyclegg_x_50 (Cyclegg_S fresh_14)) } @-}
lemma_2 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_2 cyclegg_x_50 fresh_14 =
  case cyclegg_x_50 of
    (Cyclegg_S cyclegg_x_50_60) ->
      -- case-split:lemma_2:cyclegg_x_50=(Cyclegg_S cyclegg_x_50_60) =>
      -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
      lemma_2 (cyclegg_x_50_60) (fresh_14)
      -- lemma_2-(Cyclegg_S (cyclegg_plus ?cyclegg_x_50 ?fresh_14))=(cyclegg_plus ?cyclegg_x_50 (Cyclegg_S ?fresh_14)) =>
      -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
      -- <= case-split:lemma_2:cyclegg_x_50=(Cyclegg_S cyclegg_x_50_60)
    (Cyclegg_Z ) ->
      -- case-split:lemma_2:cyclegg_x_50=Cyclegg_Z =>
      -- (cyclegg_plus Cyclegg_Z ?y) =>
      -- <= (cyclegg_plus Cyclegg_Z ?y)
      -- <= case-split:lemma_2:cyclegg_x_50=Cyclegg_Z
      ()


