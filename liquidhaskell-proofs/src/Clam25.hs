{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_25: (cyclegg_even (cyclegg_len (cyclegg_append cyclegg_x cyclegg_y))) = (cyclegg_even (cyclegg_plus (cyclegg_len cyclegg_x) (cyclegg_len cyclegg_y)))
module Clam25 where
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

{-@ reflect cyclegg_plus @-}
cyclegg_plus :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_plus Cyclegg_Z y = y
cyclegg_plus (Cyclegg_S x) y = (Cyclegg_S (cyclegg_plus x y))

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_not @-}
cyclegg_not :: (Cyclegg_Bool -> Cyclegg_Bool)
cyclegg_not Cyclegg_True = Cyclegg_False
cyclegg_not Cyclegg_False = Cyclegg_True

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_even @-}
cyclegg_even :: (Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_even Cyclegg_Z = Cyclegg_True
cyclegg_even (Cyclegg_S n) = (cyclegg_not (cyclegg_even n))

{-@ clam_25 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_even (cyclegg_len (cyclegg_append cyclegg_x cyclegg_y))) = (cyclegg_even (cyclegg_plus (cyclegg_len cyclegg_x) (cyclegg_len cyclegg_y))) } @-}
clam_25 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
clam_25 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_90 cyclegg_x_91) ->
      -- case-split:clam_25:cyclegg_x=(Cyclegg_Cons cyclegg_x_90 cyclegg_x_91) =>
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
      -- (cyclegg_even (Cyclegg_S ?n)) =>
      clam_25 (cyclegg_x_91) (cyclegg_y)
      -- clam_25-(cyclegg_even (cyclegg_len (cyclegg_append ?cyclegg_x ?cyclegg_y)))=(cyclegg_even (cyclegg_plus (cyclegg_len ?cyclegg_x) (cyclegg_len ?cyclegg_y))) =>
      -- <= (cyclegg_even (Cyclegg_S ?n))
      -- <= (cyclegg_plus (Cyclegg_S ?x) ?y)
      -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
      -- <= case-split:clam_25:cyclegg_x=(Cyclegg_Cons cyclegg_x_90 cyclegg_x_91)
    (Cyclegg_Nil ) ->
      -- case-split:clam_25:cyclegg_x=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= (cyclegg_plus Cyclegg_Z ?y)
      -- <= (cyclegg_len Cyclegg_Nil)
      -- <= case-split:clam_25:cyclegg_x=Cyclegg_Nil
      ()


