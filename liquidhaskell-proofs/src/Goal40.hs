{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_40: (cyclegg_take Cyclegg_Z cyclegg_xs) = Cyclegg_Nil
module Goal40 where
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

{-@ reflect cyclegg_take @-}
cyclegg_take :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_take Cyclegg_Z xs = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) (Cyclegg_Cons x xs) = (Cyclegg_Cons x (cyclegg_take n xs))

{-@ goal_40 :: cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_take Cyclegg_Z cyclegg_xs) = Cyclegg_Nil } @-}
goal_40 :: (Cyclegg_List cyclegg_a) -> Proof
goal_40 cyclegg_xs =
  -- (cyclegg_take Cyclegg_Z ?xs) =>
  ()


