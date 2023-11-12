{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_70: (cyclegg_leq cyclegg_n (cyclegg_add cyclegg_m cyclegg_n)) = Cyclegg_True
module Goal70 where
import Language.Haskell.Liquid.Equational

{-@ autosize Cyclegg_Tm @-}
data Cyclegg_Tm cyclegg_a where
  Cyclegg_Var :: (cyclegg_a -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_Cst :: (Cyclegg_Nat -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_App :: ((Cyclegg_Expr cyclegg_a) -> (Cyclegg_Expr cyclegg_a) -> (Cyclegg_Tm cyclegg_a))

{-@ autosize Cyclegg_Nat @-}
data Cyclegg_Nat where
  Cyclegg_Z :: Cyclegg_Nat
  Cyclegg_S :: (Cyclegg_Nat -> Cyclegg_Nat)

{-@ autosize Cyclegg_Expr @-}
data Cyclegg_Expr cyclegg_a where
  Cyclegg_MkExpr :: ((Cyclegg_Tm cyclegg_a) -> Cyclegg_Nat -> (Cyclegg_Expr cyclegg_a))

{-@ autosize Cyclegg_Pair @-}
data Cyclegg_Pair cyclegg_a cyclegg_b where
  Cyclegg_Pair :: (cyclegg_a -> cyclegg_b -> (Cyclegg_Pair cyclegg_a cyclegg_b))

{-@ autosize Cyclegg_Tree @-}
data Cyclegg_Tree cyclegg_a where
  Cyclegg_Leaf :: (Cyclegg_Tree cyclegg_a)
  Cyclegg_Node :: ((Cyclegg_Tree cyclegg_a) -> cyclegg_a -> (Cyclegg_Tree cyclegg_a) -> (Cyclegg_Tree cyclegg_a))

{-@ autosize Cyclegg_Bool @-}
data Cyclegg_Bool where
  Cyclegg_True :: Cyclegg_Bool
  Cyclegg_False :: Cyclegg_Bool

{-@ autosize Cyclegg_List @-}
data Cyclegg_List cyclegg_a where
  Cyclegg_Nil :: (Cyclegg_List cyclegg_a)
  Cyclegg_Cons :: (cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))

{-@ unreachable :: {v:a | false} -> b @-}
unreachable :: a -> b
unreachable x = unreachable x

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

{-@ reflect cyclegg_leq @-}
cyclegg_leq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_leq Cyclegg_Z y = Cyclegg_True
cyclegg_leq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_leq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_leq x y)

{-@ goal_70 :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> { (cyclegg_leq cyclegg_n (cyclegg_add cyclegg_m cyclegg_n)) = Cyclegg_True } @-}
goal_70 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
goal_70 cyclegg_n cyclegg_m =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_50) ->
      case cyclegg_m of
        (Cyclegg_S cyclegg_m_90) ->
          -- case-split:goal_70:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
          -- case-split:goal_70:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_m=(Cyclegg_S cyclegg_m_90) =>
          -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
          -- case-split:goal_70:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
          -- (cyclegg_leq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          lemma_1 (cyclegg_n_50) (cyclegg_m_90)
          -- <= lemma_1-(Cyclegg_S (cyclegg_add ?cyclegg_m_90 ?cyclegg_n_50))=(cyclegg_add ?cyclegg_m_90 (Cyclegg_S ?cyclegg_n_50))
          -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
          -- <= case-split:goal_70:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_m=(Cyclegg_S cyclegg_m_90)
          ? goal_70 (cyclegg_n_50) (cyclegg_m)
          -- goal_70-(cyclegg_leq ?cyclegg_n (cyclegg_add ?cyclegg_m ?cyclegg_n))=Cyclegg_True =>
        (Cyclegg_Z ) ->
          -- case-split:goal_70:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
          -- case-split:goal_70:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_m=Cyclegg_Z =>
          -- (cyclegg_add Cyclegg_Z ?y) =>
          -- case-split:goal_70:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
          -- (cyclegg_leq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- <= (cyclegg_add Cyclegg_Z ?y)
          -- <= case-split:goal_70:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_m=Cyclegg_Z
          goal_70 (cyclegg_n_50) (cyclegg_m)
          -- goal_70-(cyclegg_leq ?cyclegg_n (cyclegg_add ?cyclegg_m ?cyclegg_n))=Cyclegg_True =>
    (Cyclegg_Z ) ->
      -- case-split:goal_70:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_leq Cyclegg_Z ?y) =>
      ()


{-@ lemma_1 :: cyclegg_n_50: Cyclegg_Nat -> cyclegg_m_90: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_add cyclegg_m_90 cyclegg_n_50)) = (cyclegg_add cyclegg_m_90 (Cyclegg_S cyclegg_n_50)) } @-}
lemma_1 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_1 cyclegg_n_50 cyclegg_m_90 =
  case cyclegg_m_90 of
    (Cyclegg_S cyclegg_m_90_60) ->
      -- case-split:lemma_1:cyclegg_m_90=(Cyclegg_S cyclegg_m_90_60) =>
      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
      lemma_1 (cyclegg_n_50) (cyclegg_m_90_60)
      -- lemma_1-(Cyclegg_S (cyclegg_add ?cyclegg_m_90 ?cyclegg_n_50))=(cyclegg_add ?cyclegg_m_90 (Cyclegg_S ?cyclegg_n_50)) =>
      -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
      -- <= case-split:lemma_1:cyclegg_m_90=(Cyclegg_S cyclegg_m_90_60)
    (Cyclegg_Z ) ->
      -- case-split:lemma_1:cyclegg_m_90=Cyclegg_Z =>
      -- (cyclegg_add Cyclegg_Z ?y) =>
      -- <= (cyclegg_add Cyclegg_Z ?y)
      -- <= case-split:lemma_1:cyclegg_m_90=Cyclegg_Z
      ()


