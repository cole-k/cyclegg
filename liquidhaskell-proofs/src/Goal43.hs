{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_43: (cyclegg_append (cyclegg_takeWhile cyclegg_p cyclegg_xs) (cyclegg_dropWhile cyclegg_p cyclegg_xs)) = cyclegg_xs
module Goal43 where
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

{-@ reflect cyclegg_dropWhile @-}
cyclegg_dropWhile :: ((cyclegg_a -> Cyclegg_Bool) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_dropWhile p Cyclegg_Nil = Cyclegg_Nil
cyclegg_dropWhile p (Cyclegg_Cons x xs) = (cyclegg_ite (($) p x) (cyclegg_dropWhile p xs) (Cyclegg_Cons x xs))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_takeWhile @-}
cyclegg_takeWhile :: ((cyclegg_a -> Cyclegg_Bool) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_takeWhile p Cyclegg_Nil = Cyclegg_Nil
cyclegg_takeWhile p (Cyclegg_Cons x xs) = (cyclegg_ite (($) p x) (Cyclegg_Cons x (cyclegg_takeWhile p xs)) Cyclegg_Nil)

{-@ goal_43 :: cyclegg_p: (cyclegg_a -> Cyclegg_Bool) -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_takeWhile cyclegg_p cyclegg_xs) (cyclegg_dropWhile cyclegg_p cyclegg_xs)) = cyclegg_xs } @-}
goal_43 :: (cyclegg_a -> Cyclegg_Bool) -> (Cyclegg_List cyclegg_a) -> Proof
goal_43 cyclegg_p cyclegg_xs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) ->
      let g_11 = ($ cyclegg_p cyclegg_xs_50) in
        case g_11 of
          (Cyclegg_False ) ->
            -- case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
            -- (cyclegg_takeWhile ?p (Cyclegg_Cons ?x ?xs)) =>
            -- adding scrutinee g_11 to split condition ($ cyclegg_p cyclegg_xs_50) =>
            -- case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_11=Cyclegg_False =>
            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
            -- case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
            -- (cyclegg_dropWhile ?p (Cyclegg_Cons ?x ?xs)) =>
            -- <= case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
            -- adding scrutinee g_11 to split condition ($ cyclegg_p cyclegg_xs_50) =>
            -- case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_11=Cyclegg_False =>
            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
            -- (cyclegg_append Cyclegg_Nil ?ys) =>
            ()
          (Cyclegg_True ) ->
            -- case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
            -- (cyclegg_takeWhile ?p (Cyclegg_Cons ?x ?xs)) =>
            -- adding scrutinee g_11 to split condition ($ cyclegg_p cyclegg_xs_50) =>
            -- case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_11=Cyclegg_True =>
            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
            -- case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
            -- (cyclegg_dropWhile ?p (Cyclegg_Cons ?x ?xs)) =>
            -- <= case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
            -- adding scrutinee g_11 to split condition ($ cyclegg_p cyclegg_xs_50) =>
            -- case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_11=Cyclegg_True =>
            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
            -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
            goal_43 (cyclegg_p) (cyclegg_xs_51)
            -- goal_43-(cyclegg_append (cyclegg_takeWhile ?cyclegg_p ?cyclegg_xs) (cyclegg_dropWhile ?cyclegg_p ?cyclegg_xs))=?cyclegg_xs =>
            -- <= case-split:goal_43:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
    (Cyclegg_Nil ) ->
      -- case-split:goal_43:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_takeWhile ?p Cyclegg_Nil) =>
      -- case-split:goal_43:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_dropWhile ?p Cyclegg_Nil) =>
      -- <= case-split:goal_43:cyclegg_xs=Cyclegg_Nil
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      ()


