{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_48: (cyclegg_append (cyclegg_butlast cyclegg_xs) (Cyclegg_Cons (cyclegg_last cyclegg_xs) Cyclegg_Nil)) = cyclegg_xs
module Goal48 where
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

{-@ reflect cyclegg_last @-}
cyclegg_last :: ((Cyclegg_List cyclegg_a) -> cyclegg_a)
cyclegg_last (Cyclegg_Cons x Cyclegg_Nil) = x
cyclegg_last (Cyclegg_Cons x (Cyclegg_Cons y ys)) = (cyclegg_last (Cyclegg_Cons y ys))

{-@ reflect cyclegg_butlast @-}
cyclegg_butlast :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_butlast Cyclegg_Nil = Cyclegg_Nil
cyclegg_butlast (Cyclegg_Cons x Cyclegg_Nil) = Cyclegg_Nil
cyclegg_butlast (Cyclegg_Cons x (Cyclegg_Cons y ys)) = (Cyclegg_Cons x (cyclegg_butlast (Cyclegg_Cons y ys)))

{-@ reflect cyclegg_null @-}
cyclegg_null :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Bool)
cyclegg_null Cyclegg_Nil = Cyclegg_True
cyclegg_null (Cyclegg_Cons x xs) = Cyclegg_False

{-@ reflect cyclegg_not @-}
cyclegg_not :: (Cyclegg_Bool -> Cyclegg_Bool)
cyclegg_not Cyclegg_True = Cyclegg_False
cyclegg_not Cyclegg_False = Cyclegg_True

{-@ goal_48 :: cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_butlast cyclegg_xs) (Cyclegg_Cons (cyclegg_last cyclegg_xs) Cyclegg_Nil)) = cyclegg_xs } @-}
goal_48 :: (Cyclegg_List cyclegg_a) -> Proof
goal_48 cyclegg_xs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) ->
      case cyclegg_xs_91 of
        (Cyclegg_Cons cyclegg_xs_91_190 cyclegg_xs_91_191) ->
          -- case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
          -- case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_190 cyclegg_xs_91_191) =>
          -- (cyclegg_butlast (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys))) =>
          -- <= case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_190 cyclegg_xs_91_191)
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          -- case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
          -- case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_190 cyclegg_xs_91_191) =>
          -- (cyclegg_last (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys))) =>
          -- <= case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_190 cyclegg_xs_91_191)
          goal_48 (cyclegg_xs_91)
          -- <= goal_48-?cyclegg_xs=(cyclegg_append (cyclegg_butlast ?cyclegg_xs) (Cyclegg_Cons (cyclegg_last ?cyclegg_xs) Cyclegg_Nil))
          -- <= case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
        (Cyclegg_Nil ) ->
          -- case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
          -- <= (cyclegg_last (Cyclegg_Cons ?x Cyclegg_Nil))
          -- <= case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):cyclegg_xs_91=Cyclegg_Nil
          -- <= case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
          -- case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):cyclegg_xs_91=Cyclegg_Nil =>
          -- (cyclegg_butlast (Cyclegg_Cons ?x Cyclegg_Nil)) =>
          -- case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
          -- case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):cyclegg_xs_91=Cyclegg_Nil =>
          -- (cyclegg_last (Cyclegg_Cons ?x Cyclegg_Nil)) =>
          -- <= case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):cyclegg_xs_91=Cyclegg_Nil
          -- <= case-split:goal_48:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          ()
    (Cyclegg_Nil ) ->
      unreachable (
        -- <= premise (cyclegg_not (cyclegg_null cyclegg_xs))=Cyclegg_True
        -- case-split:goal_48:cyclegg_xs=Cyclegg_Nil =>
        -- (cyclegg_null Cyclegg_Nil) =>
        -- (cyclegg_not Cyclegg_True) =>
        ()
      )



