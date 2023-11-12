{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_48: (cyclegg_len (cyclegg_sort cyclegg_x)) = (cyclegg_len cyclegg_x)
module Clam48 where
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

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_sort @-}
cyclegg_sort :: ((Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_sort Cyclegg_Nil = Cyclegg_Nil
cyclegg_sort (Cyclegg_Cons x xs) = (cyclegg_insort x (cyclegg_sort xs))

{-@ reflect cyclegg_insort @-}
cyclegg_insort :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_insort n Cyclegg_Nil = (Cyclegg_Cons n Cyclegg_Nil)
cyclegg_insort n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_lt n x) (Cyclegg_Cons n (Cyclegg_Cons x xs)) (Cyclegg_Cons x (cyclegg_insort n xs)))

{-@ reflect cyclegg_lt @-}
cyclegg_lt :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_lt x Cyclegg_Z = Cyclegg_False
cyclegg_lt Cyclegg_Z (Cyclegg_S y) = Cyclegg_True
cyclegg_lt (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_lt x y)

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ clam_48 :: cyclegg_x: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_len (cyclegg_sort cyclegg_x)) = (cyclegg_len cyclegg_x) } @-}
clam_48 :: (Cyclegg_List Cyclegg_Nat) -> Proof
clam_48 cyclegg_x =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_40 cyclegg_x_41) ->
      -- case-split:clam_48:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41) =>
      -- (cyclegg_sort (Cyclegg_Cons ?x ?xs)) =>
      lemma_0 (cyclegg_x_40) ((cyclegg_sort cyclegg_x_41))
      -- lemma_0-(cyclegg_len (cyclegg_insort ?cyclegg_x_40 ?fresh_12))=(Cyclegg_S (cyclegg_len ?fresh_12)) =>
      ? clam_48 (cyclegg_x_41)
      -- clam_48-(cyclegg_len (cyclegg_sort ?cyclegg_x))=(cyclegg_len ?cyclegg_x) =>
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- <= case-split:clam_48:cyclegg_x=(Cyclegg_Cons cyclegg_x_40 cyclegg_x_41)
    (Cyclegg_Nil ) ->
      -- case-split:clam_48:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_sort Cyclegg_Nil) =>
      -- <= case-split:clam_48:cyclegg_x=Cyclegg_Nil
      ()


{-@ lemma_0 :: cyclegg_x_40: Cyclegg_Nat -> fresh_12: (Cyclegg_List Cyclegg_Nat) -> { (Cyclegg_S (cyclegg_len fresh_12)) = (cyclegg_len (cyclegg_insort cyclegg_x_40 fresh_12)) } @-}
lemma_0 :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
lemma_0 cyclegg_x_40 fresh_12 =
  case fresh_12 of
    (Cyclegg_Cons fresh_12_60 fresh_12_61) ->
      let g_14 = (cyclegg_lt cyclegg_x_40 fresh_12_60) in
        case g_14 of
          (Cyclegg_False ) ->
            -- case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61) =>
            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
            lemma_0 (cyclegg_x_40) (fresh_12_61)
            -- <= lemma_0-(cyclegg_len (cyclegg_insort ?cyclegg_x_40 ?fresh_12))=(Cyclegg_S (cyclegg_len ?fresh_12))
            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
            -- <= case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61):g_14=Cyclegg_False
            -- <= adding scrutinee g_14 to split condition (cyclegg_lt cyclegg_x_40 fresh_12_60)
            -- case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61) =>
            -- <= (cyclegg_insort ?n (Cyclegg_Cons ?x ?xs))
            -- <= case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61)
          (Cyclegg_True ) ->
            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
            -- <= case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61):g_14=Cyclegg_True
            -- <= adding scrutinee g_14 to split condition (cyclegg_lt cyclegg_x_40 fresh_12_60)
            -- case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61) =>
            -- <= (cyclegg_insort ?n (Cyclegg_Cons ?x ?xs))
            -- <= case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61)
            ()
    (Cyclegg_Nil ) ->
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- case-split:lemma_0:fresh_12=Cyclegg_Nil =>
      -- <= (cyclegg_insort ?n Cyclegg_Nil)
      -- <= case-split:lemma_0:fresh_12=Cyclegg_Nil
      ()


