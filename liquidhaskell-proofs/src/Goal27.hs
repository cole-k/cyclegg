{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_27: (cyclegg_elem cyclegg_x (cyclegg_append cyclegg_xs cyclegg_ys)) = Cyclegg_True
module Goal27 where
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

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_elem @-}
cyclegg_elem :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Bool)
cyclegg_elem n Cyclegg_Nil = Cyclegg_False
cyclegg_elem n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) Cyclegg_True (cyclegg_elem n xs))

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ goal_27 :: cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> cyclegg_ys: (Cyclegg_List Cyclegg_Nat) -> cyclegg_x: Cyclegg_Nat -> { (cyclegg_elem cyclegg_x (cyclegg_append cyclegg_xs cyclegg_ys)) = Cyclegg_True } @-}
goal_27 :: (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat -> Proof
goal_27 cyclegg_xs cyclegg_ys cyclegg_x =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) ->
      let g_14 = (cyclegg_eq cyclegg_x cyclegg_xs_70) in
        case g_14 of
          (Cyclegg_False ) ->
            -- case-split:goal_27:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
            -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
            goal_27 (cyclegg_xs_71) (cyclegg_ys) (cyclegg_x)
            -- <= goal_27-(cyclegg_elem ?cyclegg_x (cyclegg_append ?cyclegg_xs ?cyclegg_ys))=Cyclegg_True
            -- adding scrutinee g_14 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_70) =>
            -- case-split:goal_27:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_14=Cyclegg_False =>
            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
            ? goal_27 (cyclegg_xs_71) (cyclegg_ys) (cyclegg_x)
            -- goal_27-(cyclegg_elem ?cyclegg_x (cyclegg_append ?cyclegg_xs ?cyclegg_ys))=Cyclegg_True =>
          (Cyclegg_True ) ->
            -- case-split:goal_27:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
            -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
            goal_27 (cyclegg_xs_71) (cyclegg_ys) (cyclegg_x)
            -- <= goal_27-(cyclegg_elem ?cyclegg_x (cyclegg_append ?cyclegg_xs ?cyclegg_ys))=Cyclegg_True
            -- adding scrutinee g_14 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_70) =>
            -- case-split:goal_27:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_14=Cyclegg_True =>
            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
            ? goal_27 (cyclegg_xs_71) (cyclegg_ys) (cyclegg_x)
            -- goal_27-(cyclegg_elem ?cyclegg_x (cyclegg_append ?cyclegg_xs ?cyclegg_ys))=Cyclegg_True =>
    (Cyclegg_Nil ) ->
      -- case-split:goal_27:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- premise (cyclegg_elem cyclegg_x cyclegg_ys)=Cyclegg_True =>
      ()


