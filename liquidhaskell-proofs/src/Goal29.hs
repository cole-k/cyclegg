{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_29: (cyclegg_elem cyclegg_x (cyclegg_ins1 cyclegg_x cyclegg_xs)) = Cyclegg_True
module Goal29 where
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

{-@ reflect cyclegg_ins1 @-}
cyclegg_ins1 :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_ins1 n Cyclegg_Nil = (Cyclegg_Cons n Cyclegg_Nil)
cyclegg_ins1 n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) (Cyclegg_Cons n (Cyclegg_Cons x xs)) (Cyclegg_Cons x (cyclegg_ins1 n xs)))

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

{-@ reflect cyclegg_elem @-}
cyclegg_elem :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Bool)
cyclegg_elem n Cyclegg_Nil = Cyclegg_False
cyclegg_elem n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) Cyclegg_True (cyclegg_elem n xs))

{-@ goal_29 :: cyclegg_x: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_elem cyclegg_x (cyclegg_ins1 cyclegg_x cyclegg_xs)) = Cyclegg_True } @-}
goal_29 :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
goal_29 cyclegg_x cyclegg_xs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) ->
      let g_10 = (cyclegg_eq cyclegg_x cyclegg_xs_50) in
        case g_10 of
          (Cyclegg_False ) ->
            -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
            -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
            -- <= case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50) =>
            -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_False =>
            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
            goal_29 (cyclegg_x) (cyclegg_xs_51)
            -- <= goal_29-(cyclegg_elem ?cyclegg_x (cyclegg_ins1 ?cyclegg_x ?cyclegg_xs))=Cyclegg_True
            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50) =>
            -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_False =>
            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
            ? goal_29 (cyclegg_x) (cyclegg_xs_51)
            -- goal_29-(cyclegg_elem ?cyclegg_x (cyclegg_ins1 ?cyclegg_x ?cyclegg_xs))=Cyclegg_True =>
          (Cyclegg_True ) ->
            let g_19 = (cyclegg_eq cyclegg_x cyclegg_x) in
              case g_19 of
                (Cyclegg_False ) ->
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                  -- <= case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
                  -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50) =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True =>
                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                  -- <= case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True
                  -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50)
                  -- adding scrutinee g_19 to split condition (cyclegg_eq cyclegg_x cyclegg_x) =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True:g_19=Cyclegg_False =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                  -- <= case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True
                  -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50)
                  -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50) =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True =>
                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                  -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50) =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True =>
                  ()
                (Cyclegg_True ) ->
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                  -- <= case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
                  -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50) =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True =>
                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                  -- <= case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True
                  -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50)
                  -- adding scrutinee g_19 to split condition (cyclegg_eq cyclegg_x cyclegg_x) =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True:g_19=Cyclegg_True =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                  -- <= case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True
                  -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50)
                  -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50) =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True =>
                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                  -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_x cyclegg_xs_50) =>
                  -- case-split:goal_29:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_10=Cyclegg_True =>
                  ()
    (Cyclegg_Nil ) ->
      let g_9 = (cyclegg_eq cyclegg_x cyclegg_x) in
        case g_9 of
          (Cyclegg_False ) ->
            case cyclegg_x of
              (Cyclegg_S cyclegg_x_130) ->
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_ins1 ?n Cyclegg_Nil) =>
                -- <= case-split:goal_29:cyclegg_xs=Cyclegg_Nil
                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_elem ?n Cyclegg_Nil) =>
                -- <= (cyclegg_elem ?n Cyclegg_Nil)
                -- <= case-split:goal_29:cyclegg_xs=Cyclegg_Nil
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_False:cyclegg_x=(Cyclegg_S cyclegg_x_130) =>
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_False:cyclegg_x=(Cyclegg_S cyclegg_x_130) =>
                -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil =>
                -- <= (cyclegg_ins1 ?n Cyclegg_Nil)
                -- <= case-split:goal_29:cyclegg_xs=Cyclegg_Nil
                goal_29 (cyclegg_x_130) (cyclegg_xs)
                -- goal_29-(cyclegg_elem ?cyclegg_x (cyclegg_ins1 ?cyclegg_x ?cyclegg_xs))=Cyclegg_True =>
              (Cyclegg_Z ) ->
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_ins1 ?n Cyclegg_Nil) =>
                -- <= case-split:goal_29:cyclegg_xs=Cyclegg_Nil
                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                -- adding scrutinee g_9 to split condition (cyclegg_eq cyclegg_x cyclegg_x) =>
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_False =>
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_elem ?n Cyclegg_Nil) =>
                -- <= case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_False
                -- <= adding scrutinee g_9 to split condition (cyclegg_eq cyclegg_x cyclegg_x)
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_False:cyclegg_x=Cyclegg_Z =>
                -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_False:cyclegg_x=Cyclegg_Z =>
                -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                ()
          (Cyclegg_True ) ->
            -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil =>
            -- (cyclegg_ins1 ?n Cyclegg_Nil) =>
            -- <= case-split:goal_29:cyclegg_xs=Cyclegg_Nil
            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
            -- adding scrutinee g_9 to split condition (cyclegg_eq cyclegg_x cyclegg_x) =>
            -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_True =>
            -- <= case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_True
            -- <= adding scrutinee g_9 to split condition (cyclegg_eq cyclegg_x cyclegg_x)
            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
            -- adding scrutinee g_9 to split condition (cyclegg_eq cyclegg_x cyclegg_x) =>
            -- case-split:goal_29:cyclegg_xs=Cyclegg_Nil:g_9=Cyclegg_True =>
            ()


