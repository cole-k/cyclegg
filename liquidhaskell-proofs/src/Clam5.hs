{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_5: (cyclegg_len (cyclegg_rev cyclegg_x)) = (cyclegg_len cyclegg_x)
module Clam5 where
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

{-@ reflect cyclegg_rev @-}
cyclegg_rev :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_rev Cyclegg_Nil = Cyclegg_Nil
cyclegg_rev (Cyclegg_Cons x xs) = (cyclegg_append (cyclegg_rev xs) (Cyclegg_Cons x Cyclegg_Nil))

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ clam_5 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> { (cyclegg_len (cyclegg_rev cyclegg_x)) = (cyclegg_len cyclegg_x) } @-}
clam_5 :: (Cyclegg_List cyclegg_a) -> Proof
clam_5 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_40 cyclegg_x_41) ->
      -- case-split:clam_5:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41) =>
      -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
      lemma_0 ((cyclegg_rev cyclegg_x_41)) (cyclegg_x_40)
      -- lemma_0-(cyclegg_len (cyclegg_append ?fresh_14 (Cyclegg_Cons ?cyclegg_x_40 Cyclegg_Nil)))=(Cyclegg_S (cyclegg_len ?fresh_14)) =>
      ? clam_5 (cyclegg_x_41)
      -- <= clam_5-(cyclegg_len ?cyclegg_x)=(cyclegg_len (cyclegg_rev ?cyclegg_x))
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- <= case-split:clam_5:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41)
    (Cyclegg_Nil ) ->
      -- case-split:clam_5:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- <= case-split:clam_5:cyclegg_x=Cyclegg_Nil
      ()


{-@ lemma_0 :: fresh_14: (Cyclegg_List cyclegg_a) -> cyclegg_x_40: cyclegg_a -> { (Cyclegg_S (cyclegg_len fresh_14)) = (cyclegg_len (cyclegg_append fresh_14 (Cyclegg_Cons cyclegg_x_40 Cyclegg_Nil))) } @-}
lemma_0 :: (Cyclegg_List cyclegg_a) -> cyclegg_a -> Proof
lemma_0 fresh_14 cyclegg_x_40 =
  case fresh_14 of
    (Cyclegg_Cons fresh_14_80 fresh_14_81) ->
      -- case-split:lemma_0:fresh_14=(Cyclegg_Cons fresh_14_80 fresh_14_81) =>
      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
      lemma_0 (fresh_14_81) (cyclegg_x_40)
      -- <= lemma_0-(cyclegg_len (cyclegg_append ?fresh_14 (Cyclegg_Cons ?cyclegg_x_40 Cyclegg_Nil)))=(Cyclegg_S (cyclegg_len ?fresh_14))
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      -- <= case-split:lemma_0:fresh_14=(Cyclegg_Cons fresh_14_80 fresh_14_81)
    (Cyclegg_Nil ) ->
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- case-split:lemma_0:fresh_14=Cyclegg_Nil =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:lemma_0:fresh_14=Cyclegg_Nil
      ()


