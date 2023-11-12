{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_20: (cyclegg_even (cyclegg_len (cyclegg_append cyclegg_x cyclegg_x))) = Cyclegg_True
module Clam20 where
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

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_even @-}
cyclegg_even :: (Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_even Cyclegg_Z = Cyclegg_True
cyclegg_even (Cyclegg_S n) = (cyclegg_not (cyclegg_even n))

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_not @-}
cyclegg_not :: (Cyclegg_Bool -> Cyclegg_Bool)
cyclegg_not Cyclegg_True = Cyclegg_False
cyclegg_not Cyclegg_False = Cyclegg_True

{-@ clam_20 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> { (cyclegg_even (cyclegg_len (cyclegg_append cyclegg_x cyclegg_x))) = Cyclegg_True } @-}
clam_20 :: (Cyclegg_List cyclegg_a) -> Proof
clam_20 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) ->
      case cyclegg_x_51 of
        (Cyclegg_Cons cyclegg_x_51_170 cyclegg_x_51_171) ->
          -- case-split:clam_20:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          -- (cyclegg_even (Cyclegg_S ?n)) =>
          -- case-split:clam_20:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51):cyclegg_x_51=(Cyclegg_Cons cyclegg_x_51_170 cyclegg_x_51_171) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          -- (cyclegg_even (Cyclegg_S ?n)) =>
          -- case-split:clam_20:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) =>
          lemma_15 (cyclegg_x_50) (cyclegg_x_51_171) (cyclegg_x_51)
          -- lemma_15-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x_51_171 (Cyclegg_Cons ?cyclegg_x_50 ?fresh_45))))=(cyclegg_not (cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x_51_171 ?fresh_45)))) =>
          -- <= (cyclegg_even (Cyclegg_S ?n))
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          -- <= case-split:clam_20:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51):cyclegg_x_51=(Cyclegg_Cons cyclegg_x_51_170 cyclegg_x_51_171)
          ? clam_20 (cyclegg_x_51)
          -- clam_20-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_x)))=Cyclegg_True =>
          ? clam_20 (cyclegg_x_51_171)
          -- <= clam_20-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_x)))=Cyclegg_True
          ? lemma_15 (cyclegg_x_51_170) (cyclegg_x_51_171) (cyclegg_x_51_171)
          -- <= lemma_15-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x_51_171 (Cyclegg_Cons ?cyclegg_x_50 ?fresh_45))))=(cyclegg_not (cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x_51_171 ?fresh_45))))
          -- <= case-split:clam_20:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51):cyclegg_x_51=(Cyclegg_Cons cyclegg_x_51_170 cyclegg_x_51_171)
          -- <= (cyclegg_even (Cyclegg_S ?n))
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          -- <= case-split:clam_20:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51):cyclegg_x_51=(Cyclegg_Cons cyclegg_x_51_170 cyclegg_x_51_171)
          ? clam_20 (cyclegg_x_51)
          -- clam_20-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_x)))=Cyclegg_True =>
        (Cyclegg_Nil ) ->
          -- case-split:clam_20:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          -- (cyclegg_even (Cyclegg_S ?n)) =>
          -- case-split:clam_20:cyclegg_x=(Cyclegg_Cons cyclegg_x_50 cyclegg_x_51) =>
          lemma_15 (cyclegg_x_50) (cyclegg_x_51) (cyclegg_x_51)
          -- lemma_15-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x_51_171 (Cyclegg_Cons ?cyclegg_x_50 ?fresh_45))))=(cyclegg_not (cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x_51_171 ?fresh_45)))) =>
          ? clam_20 (cyclegg_x_51)
          -- clam_20-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_x)))=Cyclegg_True =>
          -- (cyclegg_not Cyclegg_True) =>
          -- (cyclegg_not Cyclegg_False) =>
    (Cyclegg_Nil ) ->
      -- case-split:clam_20:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- case-split:clam_20:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_len Cyclegg_Nil) =>
      -- (cyclegg_even Cyclegg_Z) =>
      ()


{-@ lemma_15 :: cyclegg_x_50: cyclegg_a -> cyclegg_x_51_171: (Cyclegg_List cyclegg_a) -> fresh_45: (Cyclegg_List cyclegg_a) -> { (cyclegg_even (cyclegg_len (cyclegg_append cyclegg_x_51_171 (Cyclegg_Cons cyclegg_x_50 fresh_45)))) = (cyclegg_not (cyclegg_even (cyclegg_len (cyclegg_append cyclegg_x_51_171 fresh_45)))) } @-}
lemma_15 :: cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
lemma_15 cyclegg_x_50 cyclegg_x_51_171 fresh_45 =
  case cyclegg_x_51_171 of
    (Cyclegg_Cons cyclegg_x_51_171_110 cyclegg_x_51_171_111) ->
      -- case-split:lemma_15:cyclegg_x_51_171=(Cyclegg_Cons cyclegg_x_51_171_110 cyclegg_x_51_171_111) =>
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
      -- (cyclegg_even (Cyclegg_S ?n)) =>
      lemma_15 (cyclegg_x_50) (cyclegg_x_51_171_111) (fresh_45)
      -- lemma_15-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x_51_171 (Cyclegg_Cons ?cyclegg_x_50 ?fresh_45))))=(cyclegg_not (cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x_51_171 ?fresh_45)))) =>
      -- <= (cyclegg_even (Cyclegg_S ?n))
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      -- <= case-split:lemma_15:cyclegg_x_51_171=(Cyclegg_Cons cyclegg_x_51_171_110 cyclegg_x_51_171_111)
    (Cyclegg_Nil ) ->
      -- case-split:lemma_15:cyclegg_x_51_171=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:lemma_15:cyclegg_x_51_171=Cyclegg_Nil
      -- (cyclegg_even (Cyclegg_S ?n)) =>
      ()


