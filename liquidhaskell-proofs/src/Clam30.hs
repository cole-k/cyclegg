{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_30: (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) Cyclegg_Nil)) = cyclegg_x
module Clam30 where
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

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_rev @-}
cyclegg_rev :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_rev Cyclegg_Nil = Cyclegg_Nil
cyclegg_rev (Cyclegg_Cons x xs) = (cyclegg_append (cyclegg_rev xs) (Cyclegg_Cons x Cyclegg_Nil))

{-@ clam_30 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> { (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) Cyclegg_Nil)) = cyclegg_x } @-}
clam_30 :: (Cyclegg_List cyclegg_a) -> Proof
clam_30 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) ->
      -- case-split:clam_30:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) =>
      -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
      lemma_3 ((cyclegg_rev cyclegg_x_51)) (cyclegg_x_50)
      -- <= lemma_3-(Cyclegg_Cons ?cyclegg_x_50 (cyclegg_rev (cyclegg_append ?fresh_16 Cyclegg_Nil)))=(cyclegg_rev (cyclegg_append (cyclegg_append ?fresh_16 (Cyclegg_Cons ?cyclegg_x_50 Cyclegg_Nil)) Cyclegg_Nil))
      ? clam_30 (cyclegg_x_51)
      -- <= clam_30-?cyclegg_x=(cyclegg_rev (cyclegg_append (cyclegg_rev ?cyclegg_x) Cyclegg_Nil))
      -- <= case-split:clam_30:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51)
    (Cyclegg_Nil ) ->
      -- case-split:clam_30:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- <= case-split:clam_30:cyclegg_x=Cyclegg_Nil
      lemma_2 (cyclegg_x)
      -- lemma_2-(cyclegg_append ?fresh_5 Cyclegg_Nil)=?fresh_5 =>
      -- case-split:clam_30:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- <= case-split:clam_30:cyclegg_x=Cyclegg_Nil


{-@ lemma_2 :: fresh_5: (Cyclegg_List cyclegg_a) -> { (cyclegg_append fresh_5 Cyclegg_Nil) = fresh_5 } @-}
lemma_2 :: (Cyclegg_List cyclegg_a) -> Proof
lemma_2 fresh_5 =
  case fresh_5 of
    (Cyclegg_Cons fresh_5_30 fresh_5_31) ->
      -- case-split:lemma_2:fresh_5=(Cyclegg_Cons fresh_5_30 fresh_5_31) =>
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      lemma_2 (fresh_5_31)
      -- <= lemma_2-?fresh_5=(cyclegg_append ?fresh_5 Cyclegg_Nil)
      -- <= case-split:lemma_2:fresh_5=(Cyclegg_Cons fresh_5_30 fresh_5_31)
    (Cyclegg_Nil ) ->
      -- case-split:lemma_2:fresh_5=Cyclegg_Nil =>
      -- <= case-split:lemma_2:fresh_5=Cyclegg_Nil
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      ()


{-@ lemma_3 :: fresh_16: (Cyclegg_List cyclegg_a) -> cyclegg_x_50: cyclegg_a -> { (Cyclegg_Cons cyclegg_x_50 (cyclegg_rev (cyclegg_append fresh_16 Cyclegg_Nil))) = (cyclegg_rev (cyclegg_append (cyclegg_append fresh_16 (Cyclegg_Cons cyclegg_x_50 Cyclegg_Nil)) Cyclegg_Nil)) } @-}
lemma_3 :: (Cyclegg_List cyclegg_a) -> cyclegg_a -> Proof
lemma_3 fresh_16 cyclegg_x_50 =
  case fresh_16 of
    (Cyclegg_Cons fresh_16_180 fresh_16_181) ->
      lemma_2 (fresh_16)
      -- lemma_2-(cyclegg_append ?fresh_5 Cyclegg_Nil)=?fresh_5 =>
      -- case-split:lemma_3:fresh_16=(Cyclegg_Cons fresh_16_180 fresh_16_181) =>
      -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
      -- <= constructor-injective (Cyclegg_Cons fresh_16_180 (cyclegg_append fresh_16_181 Cyclegg_Nil)) = (Cyclegg_Cons fresh_16_180 fresh_16_181)
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      ? lemma_3 (fresh_16_181) (cyclegg_x_50)
      -- lemma_3-(Cyclegg_Cons ?cyclegg_x_50 (cyclegg_rev (cyclegg_append ?fresh_16 Cyclegg_Nil)))=(cyclegg_rev (cyclegg_append (cyclegg_append ?fresh_16 (Cyclegg_Cons ?cyclegg_x_50 Cyclegg_Nil)) Cyclegg_Nil)) =>
      ? lemma_2 ((cyclegg_append fresh_16_181 (Cyclegg_Cons cyclegg_x_50 Cyclegg_Nil)))
      -- lemma_2-(cyclegg_append ?fresh_5 Cyclegg_Nil)=?fresh_5 =>
      -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      -- <= case-split:lemma_3:fresh_16=(Cyclegg_Cons fresh_16_180 fresh_16_181)
      ? lemma_2 ((cyclegg_append fresh_16 (Cyclegg_Cons cyclegg_x_50 Cyclegg_Nil)))
      -- <= lemma_2-(cyclegg_append ?fresh_5 Cyclegg_Nil)=?fresh_5
    (Cyclegg_Nil ) ->
      lemma_2 (fresh_16)
      -- lemma_2-(cyclegg_append ?fresh_5 Cyclegg_Nil)=?fresh_5 =>
      -- case-split:lemma_3:fresh_16=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= (cyclegg_rev Cyclegg_Nil)
      -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:lemma_3:fresh_16=Cyclegg_Nil
      ? lemma_2 ((cyclegg_append fresh_16 (Cyclegg_Cons cyclegg_x_50 Cyclegg_Nil)))
      -- <= lemma_2-(cyclegg_append ?fresh_5 Cyclegg_Nil)=?fresh_5


