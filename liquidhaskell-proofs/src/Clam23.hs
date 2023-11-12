{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_23: (cyclegg_half (cyclegg_len (cyclegg_append cyclegg_x cyclegg_y))) = (cyclegg_half (cyclegg_len (cyclegg_append cyclegg_y cyclegg_x)))
module Clam23 where
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

{-@ reflect cyclegg_half @-}
cyclegg_half :: (Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_half Cyclegg_Z = Cyclegg_Z
cyclegg_half (Cyclegg_S Cyclegg_Z) = Cyclegg_Z
cyclegg_half (Cyclegg_S (Cyclegg_S n)) = (Cyclegg_S (cyclegg_half n))

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ clam_23 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_half (cyclegg_len (cyclegg_append cyclegg_x cyclegg_y))) = (cyclegg_half (cyclegg_len (cyclegg_append cyclegg_y cyclegg_x))) } @-}
clam_23 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
clam_23 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_80 cyclegg_x_81) ->
      case cyclegg_y of
        (Cyclegg_Cons cyclegg_y_190 cyclegg_y_191) ->
          -- case-split:clam_23:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          lemma_15 (cyclegg_y) (cyclegg_x_81)
          -- lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y)) =>
          -- case-split:clam_23:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81):cyclegg_y=(Cyclegg_Cons cyclegg_y_190 cyclegg_y_191) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          ? lemma_15 (cyclegg_x_81) (cyclegg_y_191)
          -- lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y)) =>
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          -- <= case-split:clam_23:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81)
          ? lemma_15 (cyclegg_x) (cyclegg_y_191)
          -- <= lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y))
          -- case-split:clam_23:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81) =>
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= case-split:clam_23:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81)
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          -- <= case-split:clam_23:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81):cyclegg_y=(Cyclegg_Cons cyclegg_y_190 cyclegg_y_191)
        (Cyclegg_Nil ) ->
          lemma_15 (cyclegg_x) (cyclegg_y)
          -- <= lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y))
    (Cyclegg_Nil ) ->
      case cyclegg_y of
        (Cyclegg_Cons cyclegg_y_100 cyclegg_y_101) ->
          lemma_15 (cyclegg_x) (cyclegg_y)
          -- <= lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y))
        (Cyclegg_Nil ) ->
          -- case-split:clam_23:cyclegg_x=Cyclegg_Nil =>
          -- <= case-split:clam_23:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil
          -- case-split:clam_23:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil =>
          -- <= case-split:clam_23:cyclegg_x=Cyclegg_Nil
          ()


{-@ lemma_15 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_len (cyclegg_append cyclegg_x cyclegg_y)) = (cyclegg_len (cyclegg_append cyclegg_y cyclegg_x)) } @-}
lemma_15 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
lemma_15 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_60 cyclegg_x_61) ->
      case cyclegg_y of
        (Cyclegg_Cons cyclegg_y_150 cyclegg_y_151) ->
          -- case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          lemma_15 (cyclegg_x_61) (cyclegg_y)
          -- <= lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y))
          -- case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61):cyclegg_y=(Cyclegg_Cons cyclegg_y_150 cyclegg_y_151) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          ? lemma_15 (cyclegg_x_61) (cyclegg_y_151)
          -- lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y)) =>
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          -- <= case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61)
          ? lemma_15 (cyclegg_x) (cyclegg_y_151)
          -- <= lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y))
          -- case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61) =>
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61)
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          -- <= case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61):cyclegg_y=(Cyclegg_Cons cyclegg_y_150 cyclegg_y_151)
        (Cyclegg_Nil ) ->
          -- case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          lemma_15 (cyclegg_x_61) (cyclegg_y)
          -- <= lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y))
          -- case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61):cyclegg_y=Cyclegg_Nil =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61)
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          -- <= case-split:lemma_15:cyclegg_x=(Cyclegg_Cons cyclegg_x_60 cyclegg_x_61):cyclegg_y=Cyclegg_Nil
    (Cyclegg_Nil ) ->
      case cyclegg_y of
        (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81) ->
          -- case-split:lemma_15:cyclegg_x=Cyclegg_Nil =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- case-split:lemma_15:cyclegg_x=Cyclegg_Nil:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          -- <= case-split:lemma_15:cyclegg_x=Cyclegg_Nil
          lemma_15 (cyclegg_x) (cyclegg_y_81)
          -- <= lemma_15-(cyclegg_len (cyclegg_append ?cyclegg_y ?cyclegg_x))=(cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y))
          -- case-split:lemma_15:cyclegg_x=Cyclegg_Nil =>
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= case-split:lemma_15:cyclegg_x=Cyclegg_Nil
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          -- <= case-split:lemma_15:cyclegg_x=Cyclegg_Nil:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)
        (Cyclegg_Nil ) ->
          -- case-split:lemma_15:cyclegg_x=Cyclegg_Nil =>
          -- <= case-split:lemma_15:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil
          -- case-split:lemma_15:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil =>
          -- <= case-split:lemma_15:cyclegg_x=Cyclegg_Nil
          ()


