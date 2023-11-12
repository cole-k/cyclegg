{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_75: (cyclegg_append (cyclegg_rev cyclegg_x) cyclegg_y) = (cyclegg_qreva cyclegg_x cyclegg_y)
module Clam75 where
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

{-@ reflect cyclegg_qreva @-}
cyclegg_qreva :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_qreva Cyclegg_Nil acc = acc
cyclegg_qreva (Cyclegg_Cons x xs) acc = (cyclegg_qreva xs (Cyclegg_Cons x acc))

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ clam_75 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_rev cyclegg_x) cyclegg_y) = (cyclegg_qreva cyclegg_x cyclegg_y) } @-}
clam_75 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
clam_75 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) ->
      -- case-split:clam_75:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) =>
      -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
      lemma_0 (cyclegg_x_50) (cyclegg_y) ((cyclegg_rev cyclegg_x_51))
      -- <= lemma_0-(cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_50 ?cyclegg_y))=(cyclegg_append (cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_50 Cyclegg_Nil)) ?cyclegg_y)
      ? clam_75 (cyclegg_x_51) ((Cyclegg_Cons cyclegg_x_50 cyclegg_y))
      -- <= clam_75-(cyclegg_qreva ?cyclegg_x ?cyclegg_y)=(cyclegg_append (cyclegg_rev ?cyclegg_x) ?cyclegg_y)
      -- <= (cyclegg_qreva (Cyclegg_Cons ?x ?xs) ?acc)
      -- <= case-split:clam_75:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51)
    (Cyclegg_Nil ) ->
      -- case-split:clam_75:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= (cyclegg_qreva Cyclegg_Nil ?acc)
      -- <= case-split:clam_75:cyclegg_x=Cyclegg_Nil
      ()


{-@ lemma_0 :: cyclegg_x_50: cyclegg_a -> cyclegg_y: (Cyclegg_List cyclegg_a) -> fresh_18: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_append fresh_18 (Cyclegg_Cons cyclegg_x_50 Cyclegg_Nil)) cyclegg_y) = (cyclegg_append fresh_18 (Cyclegg_Cons cyclegg_x_50 cyclegg_y)) } @-}
lemma_0 :: cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
lemma_0 cyclegg_x_50 cyclegg_y fresh_18 =
  case fresh_18 of
    (Cyclegg_Cons fresh_18_90 fresh_18_91) ->
      -- case-split:lemma_0:fresh_18=(Cyclegg_Cons fresh_18_90 fresh_18_91) =>
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      lemma_0 (cyclegg_x_50) (cyclegg_y) (fresh_18_91)
      -- lemma_0-(cyclegg_append (cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_50 Cyclegg_Nil)) ?cyclegg_y)=(cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_50 ?cyclegg_y)) =>
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      -- <= case-split:lemma_0:fresh_18=(Cyclegg_Cons fresh_18_90 fresh_18_91)
    (Cyclegg_Nil ) ->
      -- case-split:lemma_0:fresh_18=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= case-split:lemma_0:fresh_18=Cyclegg_Nil
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      -- case-split:lemma_0:fresh_18=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:lemma_0:fresh_18=Cyclegg_Nil
      ()


