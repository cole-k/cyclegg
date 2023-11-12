{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_71: (cyclegg_leq cyclegg_m (Cyclegg_S cyclegg_n)) = Cyclegg_True
module Goal71 where
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

{-@ reflect cyclegg_leq @-}
cyclegg_leq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_leq Cyclegg_Z y = Cyclegg_True
cyclegg_leq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_leq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_leq x y)

{-@ goal_71 :: cyclegg_m: Cyclegg_Nat -> cyclegg_n: Cyclegg_Nat -> { (cyclegg_leq cyclegg_m (Cyclegg_S cyclegg_n)) = Cyclegg_True } @-}
goal_71 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
goal_71 cyclegg_m cyclegg_n =
  case cyclegg_m of
    (Cyclegg_S cyclegg_m_60) ->
      case cyclegg_n of
        (Cyclegg_S cyclegg_n_100) ->
          -- case-split:goal_71:cyclegg_m=(Cyclegg_S cyclegg_m_60) =>
          -- (cyclegg_leq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- case-split:goal_71:cyclegg_m=(Cyclegg_S cyclegg_m_60):cyclegg_n=(Cyclegg_S cyclegg_n_100) =>
          goal_71 (cyclegg_m_60) (cyclegg_n_100)
          -- goal_71-(cyclegg_leq ?cyclegg_m (Cyclegg_S ?cyclegg_n))=Cyclegg_True =>
        (Cyclegg_Z ) ->
          unreachable (
            -- <= premise (cyclegg_leq cyclegg_m cyclegg_n)=Cyclegg_True
            -- case-split:goal_71:cyclegg_m=(Cyclegg_S cyclegg_m_60) =>
            -- case-split:goal_71:cyclegg_m=(Cyclegg_S cyclegg_m_60):cyclegg_n=Cyclegg_Z =>
            -- (cyclegg_leq (Cyclegg_S ?x) Cyclegg_Z) =>
            ()
          )

    (Cyclegg_Z ) ->
      -- case-split:goal_71:cyclegg_m=Cyclegg_Z =>
      -- (cyclegg_leq Cyclegg_Z ?y) =>
      ()


