{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_26: (cyclegg_half (cyclegg_plus cyclegg_x cyclegg_y)) = (cyclegg_half (cyclegg_plus cyclegg_y cyclegg_x))
module Clam26 where
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

{-@ reflect cyclegg_half @-}
cyclegg_half :: (Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_half Cyclegg_Z = Cyclegg_Z
cyclegg_half (Cyclegg_S Cyclegg_Z) = Cyclegg_Z
cyclegg_half (Cyclegg_S (Cyclegg_S n)) = (Cyclegg_S (cyclegg_half n))

{-@ reflect cyclegg_plus @-}
cyclegg_plus :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_plus Cyclegg_Z y = y
cyclegg_plus (Cyclegg_S x) y = (Cyclegg_S (cyclegg_plus x y))

{-@ clam_26 :: cyclegg_x: Cyclegg_Nat -> cyclegg_y: Cyclegg_Nat -> { (cyclegg_half (cyclegg_plus cyclegg_x cyclegg_y)) = (cyclegg_half (cyclegg_plus cyclegg_y cyclegg_x)) } @-}
clam_26 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
clam_26 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_60) ->
      case cyclegg_y of
        (Cyclegg_S cyclegg_y_130) ->
          -- case-split:clam_26:cyclegg_x=(Cyclegg_S cyclegg_x_60) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          lemma_14 (cyclegg_y) (cyclegg_x_60)
          -- lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y) =>
          -- case-split:clam_26:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          ? lemma_14 (cyclegg_y_130) (cyclegg_x_60)
          -- <= lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y)
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= case-split:clam_26:cyclegg_x=(Cyclegg_S cyclegg_x_60)
          ? lemma_14 (cyclegg_x) (cyclegg_y_130)
          -- <= lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y)
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= case-split:clam_26:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_y=(Cyclegg_S cyclegg_y_130)
        (Cyclegg_Z ) ->
          lemma_14 (cyclegg_x) (cyclegg_y)
          -- <= lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y)
    (Cyclegg_Z ) ->
      case cyclegg_y of
        (Cyclegg_S cyclegg_y_80) ->
          lemma_14 (cyclegg_x) (cyclegg_y)
          -- <= lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y)
        (Cyclegg_Z ) ->
          -- case-split:clam_26:cyclegg_x=Cyclegg_Z =>
          -- <= case-split:clam_26:cyclegg_x=Cyclegg_Z:cyclegg_y=Cyclegg_Z
          -- case-split:clam_26:cyclegg_x=Cyclegg_Z:cyclegg_y=Cyclegg_Z =>
          -- <= case-split:clam_26:cyclegg_x=Cyclegg_Z
          ()


{-@ lemma_14 :: cyclegg_x: Cyclegg_Nat -> cyclegg_y: Cyclegg_Nat -> { (cyclegg_plus cyclegg_x cyclegg_y) = (cyclegg_plus cyclegg_y cyclegg_x) } @-}
lemma_14 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_14 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_40) ->
      case cyclegg_y of
        (Cyclegg_S cyclegg_y_90) ->
          -- case-split:lemma_14:cyclegg_x=(Cyclegg_S cyclegg_x_40) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          lemma_14 (cyclegg_x_40) (cyclegg_y)
          -- <= lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y)
          -- case-split:lemma_14:cyclegg_x=(Cyclegg_S cyclegg_x_40):cyclegg_y=(Cyclegg_S cyclegg_y_90) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          ? lemma_14 (cyclegg_x_40) (cyclegg_y_90)
          -- lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y) =>
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= case-split:lemma_14:cyclegg_x=(Cyclegg_S cyclegg_x_40)
          ? lemma_14 (cyclegg_x) (cyclegg_y_90)
          -- <= lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y)
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= case-split:lemma_14:cyclegg_x=(Cyclegg_S cyclegg_x_40):cyclegg_y=(Cyclegg_S cyclegg_y_90)
        (Cyclegg_Z ) ->
          -- case-split:lemma_14:cyclegg_x=(Cyclegg_S cyclegg_x_40) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          lemma_14 (cyclegg_x_40) (cyclegg_y)
          -- <= lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y)
          -- case-split:lemma_14:cyclegg_x=(Cyclegg_S cyclegg_x_40):cyclegg_y=Cyclegg_Z =>
          -- (cyclegg_plus Cyclegg_Z ?y) =>
          -- <= case-split:lemma_14:cyclegg_x=(Cyclegg_S cyclegg_x_40)
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= case-split:lemma_14:cyclegg_x=(Cyclegg_S cyclegg_x_40):cyclegg_y=Cyclegg_Z
    (Cyclegg_Z ) ->
      case cyclegg_y of
        (Cyclegg_S cyclegg_y_50) ->
          -- case-split:lemma_14:cyclegg_x=Cyclegg_Z =>
          -- (cyclegg_plus Cyclegg_Z ?y) =>
          -- case-split:lemma_14:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_50) =>
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= case-split:lemma_14:cyclegg_x=Cyclegg_Z
          lemma_14 (cyclegg_x) (cyclegg_y_50)
          -- <= lemma_14-(cyclegg_plus ?cyclegg_y ?cyclegg_x)=(cyclegg_plus ?cyclegg_x ?cyclegg_y)
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= case-split:lemma_14:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_50)
        (Cyclegg_Z ) ->
          -- case-split:lemma_14:cyclegg_x=Cyclegg_Z =>
          -- <= case-split:lemma_14:cyclegg_x=Cyclegg_Z:cyclegg_y=Cyclegg_Z
          -- case-split:lemma_14:cyclegg_x=Cyclegg_Z:cyclegg_y=Cyclegg_Z =>
          -- <= case-split:lemma_14:cyclegg_x=Cyclegg_Z
          ()


