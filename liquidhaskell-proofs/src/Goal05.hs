{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_05: (cyclegg_add (Cyclegg_S Cyclegg_Z) (cyclegg_count cyclegg_n cyclegg_xs)) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_x cyclegg_xs))
module Goal05 where
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

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ goal_05 :: cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> cyclegg_n: Cyclegg_Nat -> cyclegg_x: Cyclegg_Nat -> { (cyclegg_add (Cyclegg_S Cyclegg_Z) (cyclegg_count cyclegg_n cyclegg_xs)) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_x cyclegg_xs)) } @-}
goal_05 :: (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat -> Cyclegg_Nat -> Proof
goal_05 cyclegg_xs cyclegg_n cyclegg_x =
  let g_11 = (cyclegg_eq cyclegg_n cyclegg_n) in
    case g_11 of
      (Cyclegg_False ) ->
        case cyclegg_xs of
          (Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171) ->
            let g_28 = (cyclegg_eq cyclegg_n cyclegg_xs_170) in
              case g_28 of
                (Cyclegg_False ) ->
                  -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171) =>
                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                  -- adding scrutinee g_28 to split condition (cyclegg_eq cyclegg_n cyclegg_xs_170) =>
                  -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171):g_28=Cyclegg_False =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                  -- <= premise cyclegg_n=cyclegg_x
                  goal_05 (cyclegg_xs_171) (cyclegg_n) (cyclegg_n)
                  -- <= goal_05-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_x ?cyclegg_xs))=(cyclegg_add (Cyclegg_S Cyclegg_Z) (cyclegg_count ?cyclegg_n ?cyclegg_xs))
                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                  -- adding scrutinee g_11 to split condition (cyclegg_eq cyclegg_n cyclegg_n) =>
                  -- case-split:goal_05:g_11=Cyclegg_False =>
                  -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171):g_28=Cyclegg_False
                  -- <= adding scrutinee g_28 to split condition (cyclegg_eq cyclegg_n cyclegg_xs_170)
                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                  -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171)
                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                  -- <= case-split:goal_05:g_11=Cyclegg_False
                  -- <= adding scrutinee g_11 to split condition (cyclegg_eq cyclegg_n cyclegg_n)
                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                  -- premise cyclegg_n=cyclegg_x =>
                (Cyclegg_True ) ->
                  -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171) =>
                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- adding scrutinee g_28 to split condition (cyclegg_eq cyclegg_n cyclegg_xs_170) =>
                  -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171):g_28=Cyclegg_True =>
                  -- <= (cyclegg_add Cyclegg_Z ?y)
                  -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
                  -- <= premise cyclegg_n=cyclegg_x
                  goal_05 (cyclegg_xs_171) (cyclegg_n) (cyclegg_n)
                  -- <= goal_05-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_x ?cyclegg_xs))=(cyclegg_add (Cyclegg_S Cyclegg_Z) (cyclegg_count ?cyclegg_n ?cyclegg_xs))
                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- adding scrutinee g_11 to split condition (cyclegg_eq cyclegg_n cyclegg_n) =>
                  -- case-split:goal_05:g_11=Cyclegg_False =>
                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                  -- <= premise cyclegg_n=cyclegg_x
                  ? goal_05 (cyclegg_xs_171) (cyclegg_n) (cyclegg_n)
                  -- <= goal_05-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_x ?cyclegg_xs))=(cyclegg_add (Cyclegg_S Cyclegg_Z) (cyclegg_count ?cyclegg_n ?cyclegg_xs))
                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                  -- adding scrutinee g_11 to split condition (cyclegg_eq cyclegg_n cyclegg_n) =>
                  -- case-split:goal_05:g_11=Cyclegg_False =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                  -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                  -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171):g_28=Cyclegg_True
                  -- <= adding scrutinee g_28 to split condition (cyclegg_eq cyclegg_n cyclegg_xs_170)
                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                  -- <= case-split:goal_05:g_11=Cyclegg_False
                  -- <= adding scrutinee g_11 to split condition (cyclegg_eq cyclegg_n cyclegg_n)
                  -- <= premise cyclegg_n=cyclegg_x
                  -- <= premise cyclegg_n=cyclegg_x
                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                  ? goal_05 (cyclegg_xs_171) (cyclegg_n) (cyclegg_n)
                  -- goal_05-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_x ?cyclegg_xs))=(cyclegg_add (Cyclegg_S Cyclegg_Z) (cyclegg_count ?cyclegg_n ?cyclegg_xs)) =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                  -- (cyclegg_add Cyclegg_Z ?y) =>
                  -- <= premise cyclegg_n=cyclegg_x
                  -- <= premise cyclegg_n=cyclegg_x
                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                  -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_170 cyclegg_xs_171)
                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                  -- <= case-split:goal_05:g_11=Cyclegg_False
                  -- <= adding scrutinee g_11 to split condition (cyclegg_eq cyclegg_n cyclegg_n)
                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                  -- premise cyclegg_n=cyclegg_x =>
          (Cyclegg_Nil ) ->
            case cyclegg_x of
              (Cyclegg_S cyclegg_x_200) ->
                -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_count ?x Cyclegg_Nil) =>
                -- <= (cyclegg_count ?x Cyclegg_Nil)
                -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil
                goal_05 (cyclegg_xs) (cyclegg_x_200) (cyclegg_x_200)
                -- <= goal_05-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_x ?cyclegg_xs))=(cyclegg_add (Cyclegg_S Cyclegg_Z) (cyclegg_count ?cyclegg_n ?cyclegg_xs))
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_count ?x Cyclegg_Nil) =>
                -- <= (cyclegg_count ?x Cyclegg_Nil)
                -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil
                -- <= (cyclegg_add Cyclegg_Z ?y)
                -- (cyclegg_add Cyclegg_Z ?y) =>
                -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_count ?x Cyclegg_Nil) =>
                -- <= (cyclegg_count ?x Cyclegg_Nil)
                -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil
                -- <= (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y))
                -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil:cyclegg_x=(Cyclegg_S cyclegg_x_200)
                -- <= premise cyclegg_n=cyclegg_x
                -- <= case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil:cyclegg_x=(Cyclegg_S cyclegg_x_200)
                -- <= premise cyclegg_n=cyclegg_x
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                -- premise cyclegg_n=cyclegg_x =>
              (Cyclegg_Z ) ->
                unreachable (
                  -- <= case-split:goal_05:g_11=Cyclegg_False
                  -- <= adding scrutinee g_11 to split condition (cyclegg_eq cyclegg_n cyclegg_n)
                  -- premise cyclegg_n=cyclegg_x =>
                  -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil:cyclegg_x=Cyclegg_Z =>
                  -- premise cyclegg_n=cyclegg_x =>
                  -- case-split:goal_05:g_11=Cyclegg_False:cyclegg_xs=Cyclegg_Nil:cyclegg_x=Cyclegg_Z =>
                  -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                  ()
                )

      (Cyclegg_True ) ->
        -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
        -- (cyclegg_add Cyclegg_Z ?y) =>
        -- <= (cyclegg_ite Cyclegg_True ?x ?y)
        -- <= case-split:goal_05:g_11=Cyclegg_True
        -- <= adding scrutinee g_11 to split condition (cyclegg_eq cyclegg_n cyclegg_n)
        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
        -- premise cyclegg_n=cyclegg_x =>
        ()


