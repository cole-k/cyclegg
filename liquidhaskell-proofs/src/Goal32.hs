{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_32: (cyclegg_min cyclegg_a cyclegg_b) = (cyclegg_min cyclegg_b cyclegg_a)
module Goal32 where
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

{-@ reflect cyclegg_min @-}
cyclegg_min :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_min Cyclegg_Z y = Cyclegg_Z
cyclegg_min x Cyclegg_Z = Cyclegg_Z
cyclegg_min (Cyclegg_S x) (Cyclegg_S y) = (Cyclegg_S (cyclegg_min x y))

{-@ goal_32 :: cyclegg_a: Cyclegg_Nat -> cyclegg_b: Cyclegg_Nat -> { (cyclegg_min cyclegg_a cyclegg_b) = (cyclegg_min cyclegg_b cyclegg_a) } @-}
goal_32 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
goal_32 cyclegg_a cyclegg_b =
  case cyclegg_a of
    (Cyclegg_S cyclegg_a_40) ->
      case cyclegg_b of
        (Cyclegg_S cyclegg_b_80) ->
          -- case-split:goal_32:cyclegg_a=(Cyclegg_S cyclegg_a_40) =>
          -- case-split:goal_32:cyclegg_a=(Cyclegg_S cyclegg_a_40):cyclegg_b=(Cyclegg_S cyclegg_b_80) =>
          -- (cyclegg_min (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          goal_32 (cyclegg_a_40) (cyclegg_b_80)
          -- goal_32-(cyclegg_min ?cyclegg_a ?cyclegg_b)=(cyclegg_min ?cyclegg_b ?cyclegg_a) =>
          -- <= (cyclegg_min (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= case-split:goal_32:cyclegg_a=(Cyclegg_S cyclegg_a_40):cyclegg_b=(Cyclegg_S cyclegg_b_80)
          -- <= case-split:goal_32:cyclegg_a=(Cyclegg_S cyclegg_a_40)
        (Cyclegg_Z ) ->
          -- case-split:goal_32:cyclegg_a=(Cyclegg_S cyclegg_a_40):cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_min ?x Cyclegg_Z) =>
          -- <= (cyclegg_min Cyclegg_Z ?y)
          -- <= case-split:goal_32:cyclegg_a=(Cyclegg_S cyclegg_a_40):cyclegg_b=Cyclegg_Z
          ()
    (Cyclegg_Z ) ->
      -- case-split:goal_32:cyclegg_a=Cyclegg_Z =>
      -- (cyclegg_min Cyclegg_Z ?y) =>
      -- <= (cyclegg_min ?x Cyclegg_Z)
      -- <= case-split:goal_32:cyclegg_a=Cyclegg_Z
      ()


