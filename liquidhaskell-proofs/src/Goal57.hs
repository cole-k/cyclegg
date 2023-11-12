{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_57: (cyclegg_drop (cyclegg_add cyclegg_n cyclegg_m) cyclegg_xs) = (cyclegg_drop cyclegg_n (cyclegg_drop cyclegg_m cyclegg_xs))
module Goal57 where
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

{-@ reflect cyclegg_drop @-}
cyclegg_drop :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_drop Cyclegg_Z xs = xs
cyclegg_drop (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_drop (Cyclegg_S n) (Cyclegg_Cons x xs) = (cyclegg_drop n xs)

{-@ goal_57 :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_drop (cyclegg_add cyclegg_n cyclegg_m) cyclegg_xs) = (cyclegg_drop cyclegg_n (cyclegg_drop cyclegg_m cyclegg_xs)) } @-}
goal_57 :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> Proof
goal_57 cyclegg_n cyclegg_m cyclegg_xs =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_70) ->
      case cyclegg_m of
        (Cyclegg_S cyclegg_m_130) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) ->
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
              -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130) =>
              lemma_7 (cyclegg_n_70) (cyclegg_m_130)
              -- <= lemma_7-(Cyclegg_S (cyclegg_add ?cyclegg_n_70 ?cyclegg_m_130))=(cyclegg_add ?cyclegg_n_70 (Cyclegg_S ?cyclegg_m_130))
              -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70)
              ? goal_57 (cyclegg_n) (cyclegg_m_130) (cyclegg_xs_231)
              -- <= goal_57-(cyclegg_drop ?cyclegg_n (cyclegg_drop ?cyclegg_m ?cyclegg_xs))=(cyclegg_drop (cyclegg_add ?cyclegg_n ?cyclegg_m) ?cyclegg_xs)
              -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_230 cyclegg_xs_231)
            (Cyclegg_Nil ) ->
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
              -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70)
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=(Cyclegg_S cyclegg_m_130):cyclegg_xs=Cyclegg_Nil
              ()
        (Cyclegg_Z ) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161) ->
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
              -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              goal_57 (cyclegg_n_70) (cyclegg_m) (cyclegg_xs_161)
              -- <= goal_57-(cyclegg_drop ?cyclegg_n (cyclegg_drop ?cyclegg_m ?cyclegg_xs))=(cyclegg_drop (cyclegg_add ?cyclegg_n ?cyclegg_m) ?cyclegg_xs)
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z =>
              -- (cyclegg_drop Cyclegg_Z ?xs) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_160 cyclegg_xs_161)
              -- <= (cyclegg_drop Cyclegg_Z ?xs)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z
            (Cyclegg_Nil ) ->
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70) =>
              -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
              -- case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
              -- <= (cyclegg_drop Cyclegg_Z ?xs)
              -- <= case-split:goal_57:cyclegg_n=(Cyclegg_S cyclegg_n_70):cyclegg_m=Cyclegg_Z
              ()
    (Cyclegg_Z ) ->
      -- case-split:goal_57:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_add Cyclegg_Z ?y) =>
      -- <= (cyclegg_drop Cyclegg_Z ?xs)
      -- <= case-split:goal_57:cyclegg_n=Cyclegg_Z
      ()


{-@ lemma_7 :: cyclegg_n_70: Cyclegg_Nat -> cyclegg_m_130: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_add cyclegg_n_70 cyclegg_m_130)) = (cyclegg_add cyclegg_n_70 (Cyclegg_S cyclegg_m_130)) } @-}
lemma_7 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_7 cyclegg_n_70 cyclegg_m_130 =
  case cyclegg_n_70 of
    (Cyclegg_S cyclegg_n_70_60) ->
      -- case-split:lemma_7:cyclegg_n_70=(Cyclegg_S cyclegg_n_70_60) =>
      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
      lemma_7 (cyclegg_n_70_60) (cyclegg_m_130)
      -- <= lemma_7-(cyclegg_add ?cyclegg_n_70 (Cyclegg_S ?cyclegg_m_130))=(Cyclegg_S (cyclegg_add ?cyclegg_n_70 ?cyclegg_m_130))
      -- <= (cyclegg_add (Cyclegg_S ?x) ?y)
      -- <= case-split:lemma_7:cyclegg_n_70=(Cyclegg_S cyclegg_n_70_60)
    (Cyclegg_Z ) ->
      -- case-split:lemma_7:cyclegg_n_70=Cyclegg_Z =>
      -- (cyclegg_add Cyclegg_Z ?y) =>
      -- <= (cyclegg_add Cyclegg_Z ?y)
      -- <= case-split:lemma_7:cyclegg_n_70=Cyclegg_Z
      ()


