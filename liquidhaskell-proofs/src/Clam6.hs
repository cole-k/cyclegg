{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_6: (cyclegg_len (cyclegg_rev (cyclegg_append cyclegg_x cyclegg_y))) = (cyclegg_plus (cyclegg_len cyclegg_x) (cyclegg_len cyclegg_y))
module Clam6 where
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

{-@ reflect cyclegg_plus @-}
cyclegg_plus :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_plus Cyclegg_Z y = y
cyclegg_plus (Cyclegg_S x) y = (Cyclegg_S (cyclegg_plus x y))

{-@ clam_6 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_len (cyclegg_rev (cyclegg_append cyclegg_x cyclegg_y))) = (cyclegg_plus (cyclegg_len cyclegg_x) (cyclegg_len cyclegg_y)) } @-}
clam_6 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
clam_6 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_80 cyclegg_x_81) ->
      case cyclegg_y of
        (Cyclegg_Cons cyclegg_y_220 cyclegg_y_221) ->
          -- case-split:clam_6:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
          lemma_6 ((cyclegg_rev (cyclegg_append cyclegg_x_81 cyclegg_y))) (cyclegg_x_80)
          -- lemma_6-(cyclegg_len (cyclegg_append ?fresh_22 (Cyclegg_Cons ?cyclegg_x_80 Cyclegg_Nil)))=(Cyclegg_S (cyclegg_len ?fresh_22)) =>
          ? clam_6 (cyclegg_x_81) (cyclegg_y)
          -- clam_6-(cyclegg_len (cyclegg_rev (cyclegg_append ?cyclegg_x ?cyclegg_y)))=(cyclegg_plus (cyclegg_len ?cyclegg_x) (cyclegg_len ?cyclegg_y)) =>
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= case-split:clam_6:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81)
        (Cyclegg_Nil ) ->
          -- case-split:clam_6:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81) =>
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
          lemma_6 ((cyclegg_rev (cyclegg_append cyclegg_x_81 cyclegg_y))) (cyclegg_x_80)
          -- lemma_6-(cyclegg_len (cyclegg_append ?fresh_22 (Cyclegg_Cons ?cyclegg_x_80 Cyclegg_Nil)))=(Cyclegg_S (cyclegg_len ?fresh_22)) =>
          ? clam_6 (cyclegg_x_81) (cyclegg_y)
          -- clam_6-(cyclegg_len (cyclegg_rev (cyclegg_append ?cyclegg_x ?cyclegg_y)))=(cyclegg_plus (cyclegg_len ?cyclegg_x) (cyclegg_len ?cyclegg_y)) =>
          -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= case-split:clam_6:cyclegg_x=(Cyclegg_Cons cyclegg_x_80 cyclegg_x_81)
    (Cyclegg_Nil ) ->
      case cyclegg_y of
        (Cyclegg_Cons cyclegg_y_110 cyclegg_y_111) ->
          -- case-split:clam_6:cyclegg_x=Cyclegg_Nil =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- case-split:clam_6:cyclegg_x=Cyclegg_Nil:cyclegg_y=(Cyclegg_Cons cyclegg_y_110 cyclegg_y_111) =>
          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
          lemma_6 ((cyclegg_rev cyclegg_y_111)) (cyclegg_y_110)
          -- lemma_6-(cyclegg_len (cyclegg_append ?fresh_22 (Cyclegg_Cons ?cyclegg_x_80 Cyclegg_Nil)))=(Cyclegg_S (cyclegg_len ?fresh_22)) =>
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          -- <= case-split:clam_6:cyclegg_x=Cyclegg_Nil
          ? clam_6 (cyclegg_x) (cyclegg_y_111)
          -- clam_6-(cyclegg_len (cyclegg_rev (cyclegg_append ?cyclegg_x ?cyclegg_y)))=(cyclegg_plus (cyclegg_len ?cyclegg_x) (cyclegg_len ?cyclegg_y)) =>
          -- case-split:clam_6:cyclegg_x=Cyclegg_Nil =>
          -- (cyclegg_len Cyclegg_Nil) =>
          -- (cyclegg_plus Cyclegg_Z ?y) =>
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= case-split:clam_6:cyclegg_x=Cyclegg_Nil:cyclegg_y=(Cyclegg_Cons cyclegg_y_110 cyclegg_y_111)
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= (cyclegg_len Cyclegg_Nil)
          -- <= case-split:clam_6:cyclegg_x=Cyclegg_Nil
        (Cyclegg_Nil ) ->
          -- case-split:clam_6:cyclegg_x=Cyclegg_Nil =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- case-split:clam_6:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil =>
          -- (cyclegg_rev Cyclegg_Nil) =>
          -- <= case-split:clam_6:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil
          -- <= (cyclegg_plus Cyclegg_Z ?y)
          -- <= (cyclegg_len Cyclegg_Nil)
          -- <= case-split:clam_6:cyclegg_x=Cyclegg_Nil
          ()


{-@ lemma_6 :: fresh_22: (Cyclegg_List cyclegg_a) -> cyclegg_x_80: cyclegg_a -> { (Cyclegg_S (cyclegg_len fresh_22)) = (cyclegg_len (cyclegg_append fresh_22 (Cyclegg_Cons cyclegg_x_80 Cyclegg_Nil))) } @-}
lemma_6 :: (Cyclegg_List cyclegg_a) -> cyclegg_a -> Proof
lemma_6 fresh_22 cyclegg_x_80 =
  case fresh_22 of
    (Cyclegg_Cons fresh_22_80 fresh_22_81) ->
      -- case-split:lemma_6:fresh_22=(Cyclegg_Cons fresh_22_80 fresh_22_81) =>
      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
      lemma_6 (fresh_22_81) (cyclegg_x_80)
      -- <= lemma_6-(cyclegg_len (cyclegg_append ?fresh_22 (Cyclegg_Cons ?cyclegg_x_80 Cyclegg_Nil)))=(Cyclegg_S (cyclegg_len ?fresh_22))
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
      -- <= case-split:lemma_6:fresh_22=(Cyclegg_Cons fresh_22_80 fresh_22_81)
    (Cyclegg_Nil ) ->
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- case-split:lemma_6:fresh_22=Cyclegg_Nil =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:lemma_6:fresh_22=Cyclegg_Nil
      ()


