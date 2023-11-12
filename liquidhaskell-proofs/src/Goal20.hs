{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_20: (cyclegg_len (cyclegg_sort cyclegg_xs)) = (cyclegg_len cyclegg_xs)
module Goal20 where
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

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_sort @-}
cyclegg_sort :: ((Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_sort Cyclegg_Nil = Cyclegg_Nil
cyclegg_sort (Cyclegg_Cons x xs) = (cyclegg_insort x (cyclegg_sort xs))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_leq @-}
cyclegg_leq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_leq Cyclegg_Z y = Cyclegg_True
cyclegg_leq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_leq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_leq x y)

{-@ reflect cyclegg_insort @-}
cyclegg_insort :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_insort n Cyclegg_Nil = (Cyclegg_Cons n Cyclegg_Nil)
cyclegg_insort n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_leq n x) (Cyclegg_Cons n (Cyclegg_Cons x xs)) (Cyclegg_Cons x (cyclegg_insort n xs)))

{-@ goal_20 :: cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_len (cyclegg_sort cyclegg_xs)) = (cyclegg_len cyclegg_xs) } @-}
goal_20 :: (Cyclegg_List Cyclegg_Nat) -> Proof
goal_20 cyclegg_xs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_40 cyclegg_xs_41) ->
      -- case-split:goal_20:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_40 cyclegg_xs_41) =>
      -- (cyclegg_sort (Cyclegg_Cons ?x ?xs)) =>
      lemma_0 ((cyclegg_sort cyclegg_xs_41)) (cyclegg_xs_40)
      -- lemma_0-(cyclegg_len (cyclegg_insort ?cyclegg_xs_40 ?fresh_12))=(Cyclegg_S (cyclegg_len ?fresh_12)) =>
      ? goal_20 (cyclegg_xs_41)
      -- goal_20-(cyclegg_len (cyclegg_sort ?cyclegg_xs))=(cyclegg_len ?cyclegg_xs) =>
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- <= case-split:goal_20:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_40 cyclegg_xs_41)
    (Cyclegg_Nil ) ->
      -- case-split:goal_20:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_sort Cyclegg_Nil) =>
      -- <= case-split:goal_20:cyclegg_xs=Cyclegg_Nil
      ()


{-@ lemma_0 :: fresh_12: (Cyclegg_List Cyclegg_Nat) -> cyclegg_xs_40: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_len fresh_12)) = (cyclegg_len (cyclegg_insort cyclegg_xs_40 fresh_12)) } @-}
lemma_0 :: (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat -> Proof
lemma_0 fresh_12 cyclegg_xs_40 =
  case fresh_12 of
    (Cyclegg_Cons fresh_12_60 fresh_12_61) ->
      let g_14 = (cyclegg_leq cyclegg_xs_40 fresh_12_60) in
        case g_14 of
          (Cyclegg_False ) ->
            -- case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61) =>
            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
            lemma_0 (fresh_12_61) (cyclegg_xs_40)
            -- <= lemma_0-(cyclegg_len (cyclegg_insort ?cyclegg_xs_40 ?fresh_12))=(Cyclegg_S (cyclegg_len ?fresh_12))
            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
            -- <= case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61):g_14=Cyclegg_False
            -- <= adding scrutinee g_14 to split condition (cyclegg_leq cyclegg_xs_40 fresh_12_60)
            -- case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61) =>
            -- <= (cyclegg_insort ?n (Cyclegg_Cons ?x ?xs))
            -- <= case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61)
          (Cyclegg_True ) ->
            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
            -- <= case-split:lemma_0:fresh_12=(Cyclegg_Cons fresh_12_60 fresh_12_61):g_14=Cyclegg_True
            -- <= adding scrutinee g_14 to split condition (cyclegg_leq cyclegg_xs_40 fresh_12_60)
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


