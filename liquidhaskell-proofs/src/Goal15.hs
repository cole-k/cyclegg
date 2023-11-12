{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_15: (Cyclegg_S (cyclegg_len cyclegg_xs)) = (cyclegg_len (cyclegg_ins cyclegg_x cyclegg_xs))
module Goal15 where
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

{-@ reflect cyclegg_lt @-}
cyclegg_lt :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_lt x Cyclegg_Z = Cyclegg_False
cyclegg_lt Cyclegg_Z (Cyclegg_S y) = Cyclegg_True
cyclegg_lt (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_lt x y)

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_ins @-}
cyclegg_ins :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_ins n Cyclegg_Nil = (Cyclegg_Cons n Cyclegg_Nil)
cyclegg_ins n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_lt n x) (Cyclegg_Cons n (Cyclegg_Cons x xs)) (Cyclegg_Cons x (cyclegg_ins n xs)))

{-@ goal_15 :: cyclegg_x: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (Cyclegg_S (cyclegg_len cyclegg_xs)) = (cyclegg_len (cyclegg_ins cyclegg_x cyclegg_xs)) } @-}
goal_15 :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
goal_15 cyclegg_x cyclegg_xs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) ->
      let g_13 = (cyclegg_lt cyclegg_x cyclegg_xs_60) in
        case g_13 of
          (Cyclegg_False ) ->
            -- case-split:goal_15:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
            -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
            goal_15 (cyclegg_x) (cyclegg_xs_61)
            -- <= goal_15-(cyclegg_len (cyclegg_ins ?cyclegg_x ?cyclegg_xs))=(Cyclegg_S (cyclegg_len ?cyclegg_xs))
            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
            -- <= case-split:goal_15:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_13=Cyclegg_False
            -- <= adding scrutinee g_13 to split condition (cyclegg_lt cyclegg_x cyclegg_xs_60)
            -- case-split:goal_15:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
            -- <= (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs))
            -- <= case-split:goal_15:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
          (Cyclegg_True ) ->
            -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
            -- <= case-split:goal_15:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_13=Cyclegg_True
            -- <= adding scrutinee g_13 to split condition (cyclegg_lt cyclegg_x cyclegg_xs_60)
            -- case-split:goal_15:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
            -- <= (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs))
            -- <= case-split:goal_15:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
            ()
    (Cyclegg_Nil ) ->
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- case-split:goal_15:cyclegg_xs=Cyclegg_Nil =>
      -- <= (cyclegg_ins ?n Cyclegg_Nil)
      -- <= case-split:goal_15:cyclegg_xs=Cyclegg_Nil
      ()


