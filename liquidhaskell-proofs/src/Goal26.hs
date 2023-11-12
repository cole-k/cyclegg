{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_26: (cyclegg_elem cyclegg_x (cyclegg_append cyclegg_xs cyclegg_ys)) = Cyclegg_True
module Goal26 where
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

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_elem @-}
cyclegg_elem :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Bool)
cyclegg_elem n Cyclegg_Nil = Cyclegg_False
cyclegg_elem n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) Cyclegg_True (cyclegg_elem n xs))

{-@ goal_26 :: cyclegg_x: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> cyclegg_ys: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_elem cyclegg_x (cyclegg_append cyclegg_xs cyclegg_ys)) = Cyclegg_True } @-}
goal_26 :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat) -> Proof
goal_26 cyclegg_x cyclegg_xs cyclegg_ys =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) ->
      let g_13 = (cyclegg_eq cyclegg_x cyclegg_xs_70) in
        case g_13 of
          (Cyclegg_False ) ->
            -- case-split:goal_26:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
            -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
            -- <= premise (cyclegg_elem cyclegg_x cyclegg_xs)=Cyclegg_True
            -- adding scrutinee g_13 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_70) =>
            -- case-split:goal_26:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_13=Cyclegg_False =>
            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
            goal_26 (cyclegg_x) (cyclegg_xs_71) (cyclegg_ys)
            -- goal_26-(cyclegg_elem ?cyclegg_x (cyclegg_append ?cyclegg_xs ?cyclegg_ys))=Cyclegg_True =>
          (Cyclegg_True ) ->
            -- case-split:goal_26:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
            -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
            -- adding scrutinee g_13 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_70) =>
            -- case-split:goal_26:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_13=Cyclegg_True =>
            -- <= case-split:goal_26:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_13=Cyclegg_True
            -- <= adding scrutinee g_13 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_70)
            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
            -- adding scrutinee g_13 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_70) =>
            -- case-split:goal_26:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_13=Cyclegg_True =>
            ()
    (Cyclegg_Nil ) ->
      unreachable (
        -- <= premise (cyclegg_elem cyclegg_x cyclegg_xs)=Cyclegg_True
        -- case-split:goal_26:cyclegg_xs=Cyclegg_Nil =>
        -- (cyclegg_elem ?n Cyclegg_Nil) =>
        ()
      )



