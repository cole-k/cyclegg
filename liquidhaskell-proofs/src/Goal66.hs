{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_66: (cyclegg_lt cyclegg_i (Cyclegg_S (cyclegg_add cyclegg_m cyclegg_i))) = Cyclegg_True
module Goal66 where
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

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

{-@ reflect cyclegg_lt @-}
cyclegg_lt :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_lt x Cyclegg_Z = Cyclegg_False
cyclegg_lt Cyclegg_Z (Cyclegg_S y) = Cyclegg_True
cyclegg_lt (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_lt x y)

{-@ goal_66 :: cyclegg_i: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> { (cyclegg_lt cyclegg_i (Cyclegg_S (cyclegg_add cyclegg_m cyclegg_i))) = Cyclegg_True } @-}
goal_66 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
goal_66 cyclegg_i cyclegg_m =
  case cyclegg_i of
    (Cyclegg_S cyclegg_i_60) ->
      case cyclegg_m of
        (Cyclegg_S cyclegg_m_120) ->
          -- case-split:goal_66:cyclegg_i=(Cyclegg_S cyclegg_i_60) =>
          -- (cyclegg_lt (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- case-split:goal_66:cyclegg_i=(Cyclegg_S cyclegg_i_60):cyclegg_m=(Cyclegg_S cyclegg_m_120) =>
          -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
          -- case-split:goal_66:cyclegg_i=(Cyclegg_S cyclegg_i_60) =>
          lemma_2 (cyclegg_m_120) (cyclegg_i_60)
          -- <= lemma_2-(Cyclegg_S (cyclegg_add ?cyclegg_m ?cyclegg_i_60))=(cyclegg_add ?cyclegg_m (Cyclegg_S ?cyclegg_i_60))
          -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
          -- <= case-split:goal_66:cyclegg_i=(Cyclegg_S cyclegg_i_60):cyclegg_m=(Cyclegg_S cyclegg_m_120)
          ? goal_66 (cyclegg_i_60) (cyclegg_m)
          -- goal_66-(cyclegg_lt ?cyclegg_i (Cyclegg_S (cyclegg_add ?cyclegg_m ?cyclegg_i)))=Cyclegg_True =>
        (Cyclegg_Z ) ->
          -- case-split:goal_66:cyclegg_i=(Cyclegg_S cyclegg_i_60) =>
          -- (cyclegg_lt (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- case-split:goal_66:cyclegg_i=(Cyclegg_S cyclegg_i_60) =>
          lemma_2 (cyclegg_m) (cyclegg_i_60)
          -- <= lemma_2-(Cyclegg_S (cyclegg_add ?cyclegg_m ?cyclegg_i_60))=(cyclegg_add ?cyclegg_m (Cyclegg_S ?cyclegg_i_60))
          ? goal_66 (cyclegg_i_60) (cyclegg_m)
          -- goal_66-(cyclegg_lt ?cyclegg_i (Cyclegg_S (cyclegg_add ?cyclegg_m ?cyclegg_i)))=Cyclegg_True =>
    (Cyclegg_Z ) ->
      -- case-split:goal_66:cyclegg_i=Cyclegg_Z =>
      -- (cyclegg_lt Cyclegg_Z (Cyclegg_S ?y)) =>
      ()


{-@ lemma_2 :: cyclegg_m: Cyclegg_Nat -> cyclegg_i_60: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_add cyclegg_m cyclegg_i_60)) = (cyclegg_add cyclegg_m (Cyclegg_S cyclegg_i_60)) } @-}
lemma_2 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_2 cyclegg_m cyclegg_i_60 =
  case cyclegg_m of
    (Cyclegg_S cyclegg_m_60) ->
      -- case-split:lemma_2:cyclegg_m=(Cyclegg_S cyclegg_m_60) =>
      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
      lemma_2 (cyclegg_m_60) (cyclegg_i_60)
      -- lemma_2-(Cyclegg_S (cyclegg_add ?cyclegg_m ?cyclegg_i_60))=(cyclegg_add ?cyclegg_m (Cyclegg_S ?cyclegg_i_60)) =>
      -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
      -- <= case-split:lemma_2:cyclegg_m=(Cyclegg_S cyclegg_m_60)
    (Cyclegg_Z ) ->
      -- case-split:lemma_2:cyclegg_m=Cyclegg_Z =>
      -- (cyclegg_add Cyclegg_Z ?y) =>
      -- <= (cyclegg_add Cyclegg_Z ?y)
      -- <= case-split:lemma_2:cyclegg_m=Cyclegg_Z
      ()


