{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_85: (cyclegg_plus (cyclegg_mult cyclegg_x cyclegg_y) cyclegg_z) = (cyclegg_qmult cyclegg_x cyclegg_y cyclegg_z)
module Clam85 where
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

{-@ reflect cyclegg_qmult @-}
cyclegg_qmult :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_qmult Cyclegg_Z n acc = acc
cyclegg_qmult (Cyclegg_S m) n acc = (cyclegg_qmult m n (cyclegg_plus acc n))

{-@ reflect cyclegg_mult @-}
cyclegg_mult :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_mult Cyclegg_Z n = (Cyclegg_Z)
cyclegg_mult (Cyclegg_S m) n = (cyclegg_plus (cyclegg_mult m n) n)

{-@ clam_85 :: cyclegg_x: Cyclegg_Nat -> cyclegg_y: Cyclegg_Nat -> cyclegg_z: Cyclegg_Nat -> { (cyclegg_plus (cyclegg_mult cyclegg_x cyclegg_y) cyclegg_z) = (cyclegg_qmult cyclegg_x cyclegg_y cyclegg_z) } @-}
clam_85 :: Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat -> Proof
clam_85 cyclegg_x cyclegg_y cyclegg_z =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_60) ->
      case cyclegg_z of
        (Cyclegg_S cyclegg_z_160) ->
          -- case-split:clam_85:cyclegg_x=(Cyclegg_S cyclegg_x_60) =>
          -- (cyclegg_mult (Cyclegg_S ?m) ?n) =>
          lemma_0 (cyclegg_z) ((cyclegg_mult cyclegg_x_60 cyclegg_y)) (cyclegg_y)
          -- lemma_0-(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z)=(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y)) =>
          ? clam_85 (cyclegg_x_60) (cyclegg_y) ((cyclegg_plus cyclegg_z cyclegg_y))
          -- <= clam_85-(cyclegg_qmult ?cyclegg_x ?cyclegg_y ?cyclegg_z)=(cyclegg_plus (cyclegg_mult ?cyclegg_x ?cyclegg_y) ?cyclegg_z)
          -- <= (cyclegg_qmult (Cyclegg_S ?m) ?n ?acc)
          -- <= case-split:clam_85:cyclegg_x=(Cyclegg_S cyclegg_x_60)
        (Cyclegg_Z ) ->
          -- case-split:clam_85:cyclegg_x=(Cyclegg_S cyclegg_x_60) =>
          -- (cyclegg_mult (Cyclegg_S ?m) ?n) =>
          lemma_0 (cyclegg_z) ((cyclegg_mult cyclegg_x_60 cyclegg_y)) (cyclegg_y)
          -- lemma_0-(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z)=(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y)) =>
          ? clam_85 (cyclegg_x_60) (cyclegg_y) ((cyclegg_plus cyclegg_z cyclegg_y))
          -- <= clam_85-(cyclegg_qmult ?cyclegg_x ?cyclegg_y ?cyclegg_z)=(cyclegg_plus (cyclegg_mult ?cyclegg_x ?cyclegg_y) ?cyclegg_z)
          -- <= (cyclegg_qmult (Cyclegg_S ?m) ?n ?acc)
          -- <= case-split:clam_85:cyclegg_x=(Cyclegg_S cyclegg_x_60)
    (Cyclegg_Z ) ->
      -- case-split:clam_85:cyclegg_x=Cyclegg_Z =>
      -- (cyclegg_mult Cyclegg_Z ?n) =>
      -- (cyclegg_plus Cyclegg_Z ?y) =>
      -- <= (cyclegg_qmult Cyclegg_Z ?n ?acc)
      -- <= case-split:clam_85:cyclegg_x=Cyclegg_Z
      ()


{-@ lemma_0 :: cyclegg_z: Cyclegg_Nat -> fresh_16: Cyclegg_Nat -> cyclegg_y: Cyclegg_Nat -> { (cyclegg_plus (cyclegg_plus fresh_16 cyclegg_y) cyclegg_z) = (cyclegg_plus fresh_16 (cyclegg_plus cyclegg_z cyclegg_y)) } @-}
lemma_0 :: Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_0 cyclegg_z fresh_16 cyclegg_y =
  case cyclegg_z of
    (Cyclegg_S cyclegg_z_70) ->
      case fresh_16 of
        (Cyclegg_S fresh_16_130) ->
          -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=(Cyclegg_S fresh_16_130) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          lemma_0 (cyclegg_z) (fresh_16_130) (cyclegg_y)
          -- lemma_0-(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z)=(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y)) =>
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=(Cyclegg_S fresh_16_130)
        (Cyclegg_Z ) ->
          case cyclegg_y of
            (Cyclegg_S cyclegg_y_160) ->
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_160) =>
              -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z
              lemma_0 (cyclegg_z) (fresh_16) (cyclegg_y_160)
              -- <= lemma_0-(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y))=(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z)
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z =>
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70) =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z
              ? lemma_0 (cyclegg_z_70) (fresh_16) (cyclegg_y_160)
              -- lemma_0-(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y))=(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z) =>
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_160)
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z
              ? lemma_0 (cyclegg_z_70) (fresh_16) (cyclegg_y)
              -- <= lemma_0-(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y))=(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z)
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70)
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z
            (Cyclegg_Z ) ->
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z:cyclegg_y=Cyclegg_Z =>
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70) =>
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z:cyclegg_y=Cyclegg_Z
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z
              lemma_0 (cyclegg_z_70) (fresh_16) (cyclegg_y)
              -- <= lemma_0-(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y))=(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z)
              -- case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70):fresh_16=Cyclegg_Z =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
              -- <= case-split:lemma_0:cyclegg_z=(Cyclegg_S cyclegg_z_70)
    (Cyclegg_Z ) ->
      case fresh_16 of
        (Cyclegg_S fresh_16_80) ->
          -- case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=(Cyclegg_S fresh_16_80) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
          lemma_0 (cyclegg_z) (fresh_16_80) (cyclegg_y)
          -- lemma_0-(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z)=(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y)) =>
          -- case-split:lemma_0:cyclegg_z=Cyclegg_Z =>
          -- (cyclegg_plus Cyclegg_Z ?y) =>
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=(Cyclegg_S fresh_16_80)
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z
        (Cyclegg_Z ) ->
          case cyclegg_y of
            (Cyclegg_S cyclegg_y_90) ->
              -- case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90) =>
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- case-split:lemma_0:cyclegg_z=Cyclegg_Z =>
              -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z
              -- (cyclegg_plus (Cyclegg_S ?x) ?y) =>
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z
              lemma_0 (fresh_16) (fresh_16) ((cyclegg_plus Cyclegg_Z cyclegg_y_90))
              -- <= lemma_0-(cyclegg_plus ?fresh_16 (cyclegg_plus ?cyclegg_z ?cyclegg_y))=(cyclegg_plus (cyclegg_plus ?fresh_16 ?cyclegg_y) ?cyclegg_z)
              -- case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z =>
              -- case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90)
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z
            (Cyclegg_Z ) ->
              -- case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z =>
              -- (cyclegg_plus Cyclegg_Z ?y) =>
              -- case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z:cyclegg_y=Cyclegg_Z =>
              -- case-split:lemma_0:cyclegg_z=Cyclegg_Z =>
              -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z:cyclegg_y=Cyclegg_Z
              -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z:fresh_16=Cyclegg_Z
              -- <= (cyclegg_plus Cyclegg_Z ?y)
              -- <= case-split:lemma_0:cyclegg_z=Cyclegg_Z
              ()


