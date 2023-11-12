{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_34: (cyclegg_eq (cyclegg_min cyclegg_a cyclegg_b) cyclegg_b) = (cyclegg_leq cyclegg_b cyclegg_a)
module Goal34 where
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

{-@ reflect cyclegg_leq @-}
cyclegg_leq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_leq Cyclegg_Z y = Cyclegg_True
cyclegg_leq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_leq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_leq x y)

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ reflect cyclegg_min @-}
cyclegg_min :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_min Cyclegg_Z y = Cyclegg_Z
cyclegg_min x Cyclegg_Z = Cyclegg_Z
cyclegg_min (Cyclegg_S x) (Cyclegg_S y) = (Cyclegg_S (cyclegg_min x y))

{-@ goal_34 :: cyclegg_a: Cyclegg_Nat -> cyclegg_b: Cyclegg_Nat -> { (cyclegg_eq (cyclegg_min cyclegg_a cyclegg_b) cyclegg_b) = (cyclegg_leq cyclegg_b cyclegg_a) } @-}
goal_34 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
goal_34 cyclegg_a cyclegg_b =
  case cyclegg_a of
    (Cyclegg_S cyclegg_a_50) ->
      case cyclegg_b of
        (Cyclegg_S cyclegg_b_100) ->
          -- case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50) =>
          -- case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=(Cyclegg_S cyclegg_b_100) =>
          -- (cyclegg_min (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=(Cyclegg_S cyclegg_b_100) =>
          -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          goal_34 (cyclegg_a_50) (cyclegg_b_100)
          -- <= goal_34-(cyclegg_leq ?cyclegg_b ?cyclegg_a)=(cyclegg_eq (cyclegg_min ?cyclegg_a ?cyclegg_b) ?cyclegg_b)
          -- <= (cyclegg_leq (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=(Cyclegg_S cyclegg_b_100)
          -- <= case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50)
        (Cyclegg_Z ) ->
          -- case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_min ?x Cyclegg_Z) =>
          -- <= (cyclegg_min ?x Cyclegg_Z)
          -- <= case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=Cyclegg_Z
          goal_34 (cyclegg_a_50) (cyclegg_b)
          -- <= goal_34-(cyclegg_leq ?cyclegg_b ?cyclegg_a)=(cyclegg_eq (cyclegg_min ?cyclegg_a ?cyclegg_b) ?cyclegg_b)
          -- case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_leq Cyclegg_Z ?y) =>
          -- <= (cyclegg_leq Cyclegg_Z ?y)
          -- <= case-split:goal_34:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=Cyclegg_Z
    (Cyclegg_Z ) ->
      case cyclegg_b of
        (Cyclegg_S cyclegg_b_70) ->
          -- case-split:goal_34:cyclegg_a=Cyclegg_Z =>
          -- (cyclegg_min Cyclegg_Z ?y) =>
          -- case-split:goal_34:cyclegg_a=Cyclegg_Z:cyclegg_b=(Cyclegg_S cyclegg_b_70) =>
          -- (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y)) =>
          -- <= (cyclegg_leq (Cyclegg_S ?x) Cyclegg_Z)
          -- <= case-split:goal_34:cyclegg_a=Cyclegg_Z:cyclegg_b=(Cyclegg_S cyclegg_b_70)
          -- <= case-split:goal_34:cyclegg_a=Cyclegg_Z
          ()
        (Cyclegg_Z ) ->
          -- case-split:goal_34:cyclegg_a=Cyclegg_Z =>
          -- (cyclegg_min Cyclegg_Z ?y) =>
          -- case-split:goal_34:cyclegg_a=Cyclegg_Z:cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
          -- <= (cyclegg_leq Cyclegg_Z ?y)
          -- <= case-split:goal_34:cyclegg_a=Cyclegg_Z:cyclegg_b=Cyclegg_Z
          -- case-split:goal_34:cyclegg_a=Cyclegg_Z:cyclegg_b=Cyclegg_Z =>
          -- <= case-split:goal_34:cyclegg_a=Cyclegg_Z
          ()


