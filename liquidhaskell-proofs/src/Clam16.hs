{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_16: (cyclegg_even (cyclegg_plus cyclegg_x cyclegg_x)) = Cyclegg_True
module Clam16 where
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

{-@ reflect cyclegg_not @-}
cyclegg_not :: (Cyclegg_Bool -> Cyclegg_Bool)
cyclegg_not Cyclegg_True = Cyclegg_False
cyclegg_not Cyclegg_False = Cyclegg_True

{-@ reflect cyclegg_plus @-}
cyclegg_plus :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_plus Cyclegg_Z y = y
cyclegg_plus (Cyclegg_S x) y = (Cyclegg_S (cyclegg_plus x y))

{-@ reflect cyclegg_even @-}
cyclegg_even :: (Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_even Cyclegg_Z = Cyclegg_True
cyclegg_even (Cyclegg_S n) = (cyclegg_not (cyclegg_even n))

{-@ clam_16 :: cyclegg_x: Cyclegg_Nat -> { (cyclegg_even (cyclegg_plus cyclegg_x cyclegg_x)) = Cyclegg_True } @-}
clam_16 :: Cyclegg_Nat -> Proof
clam_16 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_40) ->
      case cyclegg_x_40 of
        (Cyclegg_S cyclegg_x_40_120) ->
          -- case-split:clam_16:cyclegg_x=(Cyclegg_S cyclegg_x_40) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          -- (cyclegg_even (Cyclegg_S ?n)) =>
          -- case-split:clam_16:cyclegg_x=(Cyclegg_S cyclegg_x_40):cyclegg_x_40=(Cyclegg_S cyclegg_x_40_120) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          -- (cyclegg_even (Cyclegg_S ?n)) =>
          -- case-split:clam_16:cyclegg_x=(Cyclegg_S cyclegg_x_40) =>
          lemma_6 (cyclegg_x_40_120) (cyclegg_x_40)
          -- <= lemma_6-(cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 ?fresh_26))=(cyclegg_not (cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 (Cyclegg_S ?fresh_26))))
          -- case-split:clam_16:cyclegg_x=(Cyclegg_S cyclegg_x_40):cyclegg_x_40=(Cyclegg_S cyclegg_x_40_120) =>
          ? lemma_6 (cyclegg_x_40_120) (cyclegg_x_40_120)
          -- <= lemma_6-(cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 ?fresh_26))=(cyclegg_not (cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 (Cyclegg_S ?fresh_26))))
          ? clam_16 (cyclegg_x_40_120)
          -- clam_16-(cyclegg_even (cyclegg_plus ?cyclegg_x ?cyclegg_x))=Cyclegg_True =>
        (Cyclegg_Z ) ->
          -- case-split:clam_16:cyclegg_x=(Cyclegg_S cyclegg_x_40) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          -- (cyclegg_even (Cyclegg_S ?n)) =>
          -- case-split:clam_16:cyclegg_x=(Cyclegg_S cyclegg_x_40) =>
          lemma_6 (cyclegg_x_40) (cyclegg_x_40)
          -- <= lemma_6-(cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 ?fresh_26))=(cyclegg_not (cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 (Cyclegg_S ?fresh_26))))
          ? clam_16 (cyclegg_x_40)
          -- clam_16-(cyclegg_even (cyclegg_plus ?cyclegg_x ?cyclegg_x))=Cyclegg_True =>
    (Cyclegg_Z ) ->
      -- case-split:clam_16:cyclegg_x=Cyclegg_Z =>
      -- (cyclegg_plus Cyclegg_Z ?y) =>
      -- case-split:clam_16:cyclegg_x=Cyclegg_Z =>
      -- (cyclegg_even Cyclegg_Z) =>
      ()


{-@ lemma_6 :: cyclegg_x_40_120: Cyclegg_Nat -> fresh_26: Cyclegg_Nat -> { (cyclegg_even (cyclegg_plus cyclegg_x_40_120 fresh_26)) = (cyclegg_not (cyclegg_even (cyclegg_plus cyclegg_x_40_120 (Cyclegg_S fresh_26)))) } @-}
lemma_6 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_6 cyclegg_x_40_120 fresh_26 =
  case cyclegg_x_40_120 of
    (Cyclegg_S cyclegg_x_40_120_80) ->
      -- case-split:lemma_6:cyclegg_x_40_120=(Cyclegg_S cyclegg_x_40_120_80) =>
      -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
      -- (cyclegg_even (Cyclegg_S ?n)) =>
      lemma_6 (cyclegg_x_40_120_80) (fresh_26)
      -- lemma_6-(cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 ?fresh_26))=(cyclegg_not (cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 (Cyclegg_S ?fresh_26)))) =>
      -- <= (cyclegg_even (Cyclegg_S ?n))
      -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
      -- <= case-split:lemma_6:cyclegg_x_40_120=(Cyclegg_S cyclegg_x_40_120_80)
    (Cyclegg_Z ) ->
      case fresh_26 of
        (Cyclegg_S fresh_26_120) ->
          -- case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z =>
          -- (cyclegg_plus Cyclegg_Z ?y) =>
          -- case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z:fresh_26=(Cyclegg_S fresh_26_120) =>
          -- (cyclegg_even (Cyclegg_S ?n)) =>
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z
          lemma_6 (cyclegg_x_40_120) (fresh_26_120)
          -- lemma_6-(cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 ?fresh_26))=(cyclegg_not (cyclegg_even (cyclegg_plus ?cyclegg_x_40_120 (Cyclegg_S ?fresh_26)))) =>
          -- case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z =>
          -- <= case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z
          -- <= case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z:fresh_26=(Cyclegg_S fresh_26_120)
          -- case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z =>
          -- (cyclegg_plus Cyclegg_Z ?y) =>
          -- <= (cyclegg_even (Cyclegg_S ?n))
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z
        (Cyclegg_Z ) ->
          -- case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z =>
          -- (cyclegg_plus Cyclegg_Z ?y) =>
          -- case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z:fresh_26=Cyclegg_Z =>
          -- (cyclegg_even Cyclegg_Z) =>
          -- <= (cyclegg_not Cyclegg_False)
          -- <= (cyclegg_not Cyclegg_True)
          -- <= (cyclegg_even Cyclegg_Z)
          -- <= case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z:fresh_26=Cyclegg_Z
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z
          -- case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z =>
          -- (cyclegg_plus Cyclegg_Z ?y) =>
          -- <= (cyclegg_even (Cyclegg_S ?n))
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= case-split:lemma_6:cyclegg_x_40_120=Cyclegg_Z
          ()


