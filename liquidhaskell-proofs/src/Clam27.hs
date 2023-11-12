{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_27: (cyclegg_qreva cyclegg_x Cyclegg_Nil) = (cyclegg_rev cyclegg_x)
module Clam27 where
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

{-@ reflect cyclegg_qreva @-}
cyclegg_qreva :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_qreva Cyclegg_Nil acc = acc
cyclegg_qreva (Cyclegg_Cons x xs) acc = (cyclegg_qreva xs (Cyclegg_Cons x acc))

{-@ clam_27 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> { (cyclegg_qreva cyclegg_x Cyclegg_Nil) = (cyclegg_rev cyclegg_x) } @-}
clam_27 :: (Cyclegg_List cyclegg_a) -> Proof
clam_27 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_40 cyclegg_x_41) ->
      case cyclegg_x_41 of
        (Cyclegg_Cons cyclegg_x_41_120 cyclegg_x_41_121) ->
          -- case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41) =>
          -- (cyclegg_qreva (Cyclegg_Cons ?x ?xs) ?acc) =>
          -- case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41):cyclegg_x_41=(Cyclegg_Cons cyclegg_x_41_120 cyclegg_x_41_121) =>
          -- (cyclegg_qreva (Cyclegg_Cons ?x ?xs) ?acc) =>
          lemma_2 (cyclegg_x_41_121) ((Cyclegg_Cons cyclegg_x_41_120 (Cyclegg_Cons cyclegg_x_40 Cyclegg_Nil)))
          -- lemma_2-(cyclegg_qreva ?cyclegg_x_41_121 ?fresh_27)=(cyclegg_append (cyclegg_rev ?cyclegg_x_41_121) ?fresh_27) =>
          ? lemma_3 ((cyclegg_rev cyclegg_x_41_121)) (cyclegg_x_41_120) ((Cyclegg_Cons cyclegg_x_40 Cyclegg_Nil))
          -- <= lemma_3-(cyclegg_append (cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_41_121_50 Cyclegg_Nil)) ?fresh_27)=(cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_41_121_50 ?fresh_27))
          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
          -- <= case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41):cyclegg_x_41=(Cyclegg_Cons cyclegg_x_41_120 cyclegg_x_41_121)
          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
          -- <= case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41)
        (Cyclegg_Nil ) ->
          -- case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41) =>
          -- (cyclegg_qreva (Cyclegg_Cons ?x ?xs) ?acc) =>
          -- <= case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41):cyclegg_x_41=Cyclegg_Nil
          -- <= case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41)
          lemma_2 (cyclegg_x_41) (cyclegg_x)
          -- lemma_2-(cyclegg_qreva ?cyclegg_x_41_121 ?fresh_27)=(cyclegg_append (cyclegg_rev ?cyclegg_x_41_121) ?fresh_27) =>
          -- case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41) =>
          -- case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41):cyclegg_x_41=Cyclegg_Nil =>
          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
          -- <= case-split:clam_27:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41)
    (Cyclegg_Nil ) ->
      -- case-split:clam_27:cyclegg_x=Cyclegg_Nil =>
      -- <= case-split:clam_27:cyclegg_x=Cyclegg_Nil
      -- (cyclegg_qreva Cyclegg_Nil ?acc) =>
      -- case-split:clam_27:cyclegg_x=Cyclegg_Nil =>
      -- <= (cyclegg_rev Cyclegg_Nil)
      -- <= case-split:clam_27:cyclegg_x=Cyclegg_Nil
      ()


{-@ lemma_3 :: fresh_18: (Cyclegg_List cyclegg_a) -> cyclegg_x_41_121_50: cyclegg_a -> fresh_27: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_append fresh_18 (Cyclegg_Cons cyclegg_x_41_121_50 Cyclegg_Nil)) fresh_27) = (cyclegg_append fresh_18 (Cyclegg_Cons cyclegg_x_41_121_50 fresh_27)) } @-}
lemma_3 :: (Cyclegg_List cyclegg_a) -> cyclegg_a -> (Cyclegg_List cyclegg_a) -> Proof
lemma_3 fresh_18 cyclegg_x_41_121_50 fresh_27 =
  case fresh_18 of
    (Cyclegg_Cons fresh_18_90 fresh_18_91) ->
      -- case-split:lemma_3:fresh_18=(Cyclegg_Cons fresh_18_90 fresh_18_91) =>
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      lemma_3 (fresh_18_91) (cyclegg_x_41_121_50) (fresh_27)
      -- <= lemma_3-(cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_41_121_50 ?fresh_27))=(cyclegg_append (cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_41_121_50 Cyclegg_Nil)) ?fresh_27)
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      -- <= case-split:lemma_3:fresh_18=(Cyclegg_Cons fresh_18_90 fresh_18_91)
    (Cyclegg_Nil ) ->
      -- case-split:lemma_3:fresh_18=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= case-split:lemma_3:fresh_18=Cyclegg_Nil
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      -- case-split:lemma_3:fresh_18=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:lemma_3:fresh_18=Cyclegg_Nil
      ()


{-@ lemma_2 :: cyclegg_x_41_121: (Cyclegg_List cyclegg_a) -> fresh_27: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_rev cyclegg_x_41_121) fresh_27) = (cyclegg_qreva cyclegg_x_41_121 fresh_27) } @-}
lemma_2 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
lemma_2 cyclegg_x_41_121 fresh_27 =
  case cyclegg_x_41_121 of
    (Cyclegg_Cons cyclegg_x_41_121_50 cyclegg_x_41_121_51) ->
      -- case-split:lemma_2:cyclegg_x_41_121=(Cyclegg_Cons cyclegg_x_41_121_50 cyclegg_x_41_121_51) =>
      -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
      lemma_3 ((cyclegg_rev cyclegg_x_41_121_51)) (cyclegg_x_41_121_50) (fresh_27)
      -- lemma_3-(cyclegg_append (cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_41_121_50 Cyclegg_Nil)) ?fresh_27)=(cyclegg_append ?fresh_18 (Cyclegg_Cons ?cyclegg_x_41_121_50 ?fresh_27)) =>
      ? lemma_2 (cyclegg_x_41_121_51) ((Cyclegg_Cons cyclegg_x_41_121_50 fresh_27))
      -- <= lemma_2-(cyclegg_qreva ?cyclegg_x_41_121 ?fresh_27)=(cyclegg_append (cyclegg_rev ?cyclegg_x_41_121) ?fresh_27)
      -- <= (cyclegg_qreva (Cyclegg_Cons ?x ?xs) ?acc)
      -- <= case-split:lemma_2:cyclegg_x_41_121=(Cyclegg_Cons cyclegg_x_41_121_50 cyclegg_x_41_121_51)
    (Cyclegg_Nil ) ->
      -- case-split:lemma_2:cyclegg_x_41_121=Cyclegg_Nil =>
      -- (cyclegg_rev Cyclegg_Nil) =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= (cyclegg_qreva Cyclegg_Nil ?acc)
      -- <= case-split:lemma_2:cyclegg_x_41_121=Cyclegg_Nil
      ()


