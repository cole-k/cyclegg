{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_13: (cyclegg_half (cyclegg_plus cyclegg_x cyclegg_x)) = cyclegg_x
module Clam13 where
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

{-@ clam_13 :: cyclegg_x: Cyclegg_Nat -> { (cyclegg_half (cyclegg_plus cyclegg_x cyclegg_x)) = cyclegg_x } @-}
clam_13 :: Cyclegg_Nat -> Proof
clam_13 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_30) ->
      -- case-split:clam_13:cyclegg_x=(Cyclegg_S cyclegg_x_30) =>
      -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
      clam_13 (cyclegg_x_30)
      -- <= clam_13-(cyclegg_half (cyclegg_plus ?cyclegg_x ?cyclegg_x))=?cyclegg_x
      -- case-split:clam_13:cyclegg_x=(Cyclegg_S cyclegg_x_30) =>
      ? clam_13 (cyclegg_x_30)
      -- <= clam_13-(cyclegg_half (cyclegg_plus ?cyclegg_x ?cyclegg_x))=?cyclegg_x
      ? lemma_0 ((cyclegg_plus cyclegg_x_30 cyclegg_x_30))
      -- lemma_0-(cyclegg_half (Cyclegg_S (cyclegg_plus (cyclegg_half ?fresh_9) (Cyclegg_S (cyclegg_half ?fresh_9)))))=(Cyclegg_S (cyclegg_half ?fresh_9)) =>
      ? clam_13 (cyclegg_x_30)
      -- clam_13-(cyclegg_half (cyclegg_plus ?cyclegg_x ?cyclegg_x))=?cyclegg_x =>
      -- <= case-split:clam_13:cyclegg_x=(Cyclegg_S cyclegg_x_30)
    (Cyclegg_Z ) ->
      -- case-split:clam_13:cyclegg_x=Cyclegg_Z =>
      -- (cyclegg_plus Cyclegg_Z ?y) =>
      -- case-split:clam_13:cyclegg_x=Cyclegg_Z =>
      -- (cyclegg_half Cyclegg_Z) =>
      -- <= case-split:clam_13:cyclegg_x=Cyclegg_Z
      ()


{-@ lemma_24 :: fresh_9_60_130: Cyclegg_Nat -> fresh_33: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_plus (cyclegg_half fresh_9_60_130) fresh_33)) = (cyclegg_plus (cyclegg_half fresh_9_60_130) (Cyclegg_S fresh_33)) } @-}
lemma_24 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_24 fresh_9_60_130 fresh_33 =
  case fresh_9_60_130 of
    (Cyclegg_S fresh_9_60_130_70) ->
      case fresh_9_60_130_70 of
        (Cyclegg_S fresh_9_60_130_70_130) ->
          -- case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70) =>
          -- case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70):fresh_9_60_130_70=(Cyclegg_S fresh_9_60_130_70_130) =>
          -- (cyclegg_half (Cyclegg_S (Cyclegg_S ?n))) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          lemma_24 (fresh_9_60_130_70_130) (fresh_33)
          -- lemma_24-(Cyclegg_S (cyclegg_plus (cyclegg_half ?fresh_9_60_130) ?fresh_33))=(cyclegg_plus (cyclegg_half ?fresh_9_60_130) (Cyclegg_S ?fresh_33)) =>
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= (cyclegg_half (Cyclegg_S (Cyclegg_S ?n)))
          -- <= case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70):fresh_9_60_130_70=(Cyclegg_S fresh_9_60_130_70_130)
          -- <= case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70)
        (Cyclegg_Z ) ->
          -- case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70) =>
          -- case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70):fresh_9_60_130_70=Cyclegg_Z =>
          -- (cyclegg_half (Cyclegg_S Cyclegg_Z)) =>
          -- <= (cyclegg_half Cyclegg_Z)
          -- <= case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70):fresh_9_60_130_70=Cyclegg_Z
          lemma_24 (fresh_9_60_130_70) (fresh_33)
          -- lemma_24-(Cyclegg_S (cyclegg_plus (cyclegg_half ?fresh_9_60_130) ?fresh_33))=(cyclegg_plus (cyclegg_half ?fresh_9_60_130) (Cyclegg_S ?fresh_33)) =>
          -- case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70):fresh_9_60_130_70=Cyclegg_Z =>
          -- (cyclegg_half Cyclegg_Z) =>
          -- <= (cyclegg_half (Cyclegg_S Cyclegg_Z))
          -- <= case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70):fresh_9_60_130_70=Cyclegg_Z
          -- <= case-split:lemma_24:fresh_9_60_130=(Cyclegg_S fresh_9_60_130_70)
    (Cyclegg_Z ) ->
      -- case-split:lemma_24:fresh_9_60_130=Cyclegg_Z =>
      -- (cyclegg_half Cyclegg_Z) =>
      -- (cyclegg_plus Cyclegg_Z ?y) =>
      -- <= (cyclegg_plus Cyclegg_Z ?y)
      -- <= (cyclegg_half Cyclegg_Z)
      -- <= case-split:lemma_24:fresh_9_60_130=Cyclegg_Z
      ()


{-@ lemma_0 :: fresh_9: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_half fresh_9)) = (cyclegg_half (Cyclegg_S (cyclegg_plus (cyclegg_half fresh_9) (Cyclegg_S (cyclegg_half fresh_9))))) } @-}
lemma_0 :: Cyclegg_Nat -> Proof
lemma_0 fresh_9 =
  case fresh_9 of
    (Cyclegg_S fresh_9_60) ->
      case fresh_9_60 of
        (Cyclegg_S fresh_9_60_130) ->
          -- case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60) =>
          -- case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60):fresh_9_60=(Cyclegg_S fresh_9_60_130) =>
          -- (cyclegg_half (Cyclegg_S (Cyclegg_S ?n))) =>
          lemma_0 (fresh_9_60_130)
          -- <= lemma_0-(cyclegg_half (Cyclegg_S (cyclegg_plus (cyclegg_half ?fresh_9) (Cyclegg_S (cyclegg_half ?fresh_9)))))=(Cyclegg_S (cyclegg_half ?fresh_9))
          -- <= (cyclegg_half (Cyclegg_S (Cyclegg_S ?n)))
          -- <= case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60):fresh_9_60=(Cyclegg_S fresh_9_60_130)
          -- <= case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60)
          ? lemma_24 (fresh_9_60_130) ((cyclegg_half fresh_9))
          -- <= lemma_24-(cyclegg_plus (cyclegg_half ?fresh_9_60_130) (Cyclegg_S ?fresh_33))=(Cyclegg_S (cyclegg_plus (cyclegg_half ?fresh_9_60_130) ?fresh_33))
          -- <= (cyclegg_half (Cyclegg_S (Cyclegg_S ?n)))
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= (cyclegg_half (Cyclegg_S (Cyclegg_S ?n)))
          -- <= case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60):fresh_9_60=(Cyclegg_S fresh_9_60_130)
          -- <= case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60)
        (Cyclegg_Z ) ->
          -- case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60) =>
          -- case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60):fresh_9_60=Cyclegg_Z =>
          -- (cyclegg_half (Cyclegg_S Cyclegg_Z)) =>
          -- <= (cyclegg_half Cyclegg_Z)
          -- <= case-split:lemma_0:fresh_9=(Cyclegg_S fresh_9_60):fresh_9_60=Cyclegg_Z
          lemma_0 (fresh_9_60)
          -- <= lemma_0-(cyclegg_half (Cyclegg_S (cyclegg_plus (cyclegg_half ?fresh_9) (Cyclegg_S (cyclegg_half ?fresh_9)))))=(Cyclegg_S (cyclegg_half ?fresh_9))
          -- <= constructor-injective (Cyclegg_S (cyclegg_plus Cyclegg_Z (Cyclegg_S Cyclegg_Z))) = (Cyclegg_S (cyclegg_plus Cyclegg_Z (Cyclegg_S Cyclegg_Z)))
          ? lemma_24 ((cyclegg_half fresh_9_60)) ((cyclegg_half fresh_9_60))
          -- lemma_24-(cyclegg_plus (cyclegg_half ?fresh_9_60_130) (Cyclegg_S ?fresh_33))=(Cyclegg_S (cyclegg_plus (cyclegg_half ?fresh_9_60_130) ?fresh_33)) =>
          -- <= constructor-injective (Cyclegg_S (cyclegg_plus Cyclegg_Z Cyclegg_Z)) = (Cyclegg_S (cyclegg_plus Cyclegg_Z Cyclegg_Z))
          ? lemma_24 (fresh_9) ((cyclegg_half fresh_9))
          -- <= lemma_24-(cyclegg_plus (cyclegg_half ?fresh_9_60_130) (Cyclegg_S ?fresh_33))=(Cyclegg_S (cyclegg_plus (cyclegg_half ?fresh_9_60_130) ?fresh_33))
    (Cyclegg_Z ) ->
      -- case-split:lemma_0:fresh_9=Cyclegg_Z =>
      -- <= (cyclegg_half Cyclegg_Z)
      -- <= case-split:lemma_0:fresh_9=Cyclegg_Z
      -- <= (cyclegg_half (Cyclegg_S (Cyclegg_S ?n)))
      -- <= (cyclegg_plus Cyclegg_Z ?y)
      -- <= (cyclegg_half Cyclegg_Z)
      -- <= case-split:lemma_0:fresh_9=Cyclegg_Z
      ()


