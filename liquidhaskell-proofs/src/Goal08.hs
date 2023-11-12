{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_08: (cyclegg_sub (cyclegg_add cyclegg_k cyclegg_m) (cyclegg_add cyclegg_k cyclegg_n)) = (cyclegg_sub cyclegg_m cyclegg_n)
module Goal08 where
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

{-@ reflect cyclegg_sub @-}
cyclegg_sub :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_sub x Cyclegg_Z = x
cyclegg_sub Cyclegg_Z y = Cyclegg_Z
cyclegg_sub (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_sub x y)

{-@ goal_08 :: cyclegg_k: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> cyclegg_n: Cyclegg_Nat -> { (cyclegg_sub (cyclegg_add cyclegg_k cyclegg_m) (cyclegg_add cyclegg_k cyclegg_n)) = (cyclegg_sub cyclegg_m cyclegg_n) } @-}
goal_08 :: Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat -> Proof
goal_08 cyclegg_k cyclegg_m cyclegg_n =
  case cyclegg_k of
    (Cyclegg_S cyclegg_k_70) ->
      -- case-split:goal_08:cyclegg_k=(Cyclegg_S cyclegg_k_70) =>
      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
      -- case-split:goal_08:cyclegg_k=(Cyclegg_S cyclegg_k_70) =>
      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
      -- (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
      goal_08 (cyclegg_k_70) (cyclegg_m) (cyclegg_n)
      -- goal_08-(cyclegg_sub (cyclegg_add ?cyclegg_k ?cyclegg_m) (cyclegg_add ?cyclegg_k ?cyclegg_n))=(cyclegg_sub ?cyclegg_m ?cyclegg_n) =>
    (Cyclegg_Z ) ->
      -- case-split:goal_08:cyclegg_k=Cyclegg_Z =>
      -- (cyclegg_add Cyclegg_Z ?y) =>
      -- case-split:goal_08:cyclegg_k=Cyclegg_Z =>
      -- (cyclegg_add Cyclegg_Z ?y) =>
      ()


