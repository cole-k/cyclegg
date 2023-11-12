{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_02: (cyclegg_add (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n cyclegg_ys)) = (cyclegg_count cyclegg_n (cyclegg_append cyclegg_xs cyclegg_ys))
module Goal02 where
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

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ goal_02 :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> cyclegg_ys: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_add (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n cyclegg_ys)) = (cyclegg_count cyclegg_n (cyclegg_append cyclegg_xs cyclegg_ys)) } @-}
goal_02 :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat) -> Proof
goal_02 cyclegg_n cyclegg_xs cyclegg_ys =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) ->
      let g_17 = (cyclegg_eq cyclegg_n cyclegg_xs_80) in
        case g_17 of
          (Cyclegg_False ) ->
            -- case-split:goal_02:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) =>
            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
            -- adding scrutinee g_17 to split condition (cyclegg_eq cyclegg_n cyclegg_xs_80) =>
            -- case-split:goal_02:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_17=Cyclegg_False =>
            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
            goal_02 (cyclegg_n) (cyclegg_xs_81) (cyclegg_ys)
            -- <= goal_02-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs ?cyclegg_ys))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n ?cyclegg_ys))
            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
            -- <= case-split:goal_02:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_17=Cyclegg_False
            -- <= adding scrutinee g_17 to split condition (cyclegg_eq cyclegg_n cyclegg_xs_80)
            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
            -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
            -- <= case-split:goal_02:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81)
          (Cyclegg_True ) ->
            -- case-split:goal_02:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) =>
            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
            -- adding scrutinee g_17 to split condition (cyclegg_eq cyclegg_n cyclegg_xs_80) =>
            -- case-split:goal_02:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_17=Cyclegg_True =>
            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
            -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
            goal_02 (cyclegg_n) (cyclegg_xs_81) (cyclegg_ys)
            -- <= goal_02-(cyclegg_count ?cyclegg_n (cyclegg_append ?cyclegg_xs ?cyclegg_ys))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n ?cyclegg_ys))
            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
            -- <= case-split:goal_02:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_17=Cyclegg_True
            -- <= adding scrutinee g_17 to split condition (cyclegg_eq cyclegg_n cyclegg_xs_80)
            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
            -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
            -- <= case-split:goal_02:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81)
    (Cyclegg_Nil ) ->
      -- case-split:goal_02:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_count ?x Cyclegg_Nil) =>
      -- (cyclegg_add Cyclegg_Z ?y) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:goal_02:cyclegg_xs=Cyclegg_Nil
      ()


