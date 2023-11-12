{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_58: (cyclegg_drop cyclegg_n (cyclegg_take cyclegg_m cyclegg_xs)) = (cyclegg_take (cyclegg_sub cyclegg_m cyclegg_n) (cyclegg_drop cyclegg_n cyclegg_xs))
module Goal58 where
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

{-@ reflect cyclegg_drop @-}
cyclegg_drop :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_drop Cyclegg_Z xs = xs
cyclegg_drop (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_drop (Cyclegg_S n) (Cyclegg_Cons x xs) = (cyclegg_drop n xs)

{-@ reflect cyclegg_sub @-}
cyclegg_sub :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_sub x Cyclegg_Z = x
cyclegg_sub Cyclegg_Z y = Cyclegg_Z
cyclegg_sub (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_sub x y)

{-@ reflect cyclegg_take @-}
cyclegg_take :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_take Cyclegg_Z xs = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) (Cyclegg_Cons x xs) = (Cyclegg_Cons x (cyclegg_take n xs))

{-@ goal_58 :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_drop cyclegg_n (cyclegg_take cyclegg_m cyclegg_xs)) = (cyclegg_take (cyclegg_sub cyclegg_m cyclegg_n) (cyclegg_drop cyclegg_n cyclegg_xs)) } @-}
goal_58 :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> Proof
goal_58 cyclegg_n cyclegg_m cyclegg_xs =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_80) ->
      case cyclegg_m of
        (Cyclegg_S cyclegg_m_140) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_240 cyclegg_xs_241) ->
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140) =>
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_240 cyclegg_xs_241) =>
              -- (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              goal_58 (cyclegg_n_80) (cyclegg_m_140) (cyclegg_xs_241)
              -- goal_58-(cyclegg_drop ?cyclegg_n (cyclegg_take ?cyclegg_m ?cyclegg_xs))=(cyclegg_take (cyclegg_sub ?cyclegg_m ?cyclegg_n) (cyclegg_drop ?cyclegg_n ?cyclegg_xs)) =>
              -- <= (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y))
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80)
              -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_240 cyclegg_xs_241)
            (Cyclegg_Nil ) ->
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140) =>
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              lemma_25 (cyclegg_n_80) (cyclegg_m_140)
              -- <= lemma_25-(cyclegg_take (cyclegg_sub ?cyclegg_m_140 ?cyclegg_n_80) (cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil))=Cyclegg_Nil
              -- <= (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y))
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80)
              -- <= (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140):cyclegg_xs=Cyclegg_Nil
              ? goal_58 (cyclegg_n_80) (cyclegg_m) (cyclegg_xs)
              -- goal_58-(cyclegg_drop ?cyclegg_n (cyclegg_take ?cyclegg_m ?cyclegg_xs))=(cyclegg_take (cyclegg_sub ?cyclegg_m ?cyclegg_n) (cyclegg_drop ?cyclegg_n ?cyclegg_xs)) =>
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140):cyclegg_xs=Cyclegg_Nil =>
              -- <= (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140):cyclegg_xs=Cyclegg_Nil
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140) =>
              -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil) =>
              ? lemma_25 (cyclegg_n_80) (cyclegg_m)
              -- lemma_25-(cyclegg_take (cyclegg_sub ?cyclegg_m_140 ?cyclegg_n_80) (cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil))=Cyclegg_Nil =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80)
              -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=(Cyclegg_S cyclegg_m_140):cyclegg_xs=Cyclegg_Nil
        (Cyclegg_Z ) ->
          -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
          -- case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=Cyclegg_Z =>
          -- (cyclegg_take Cyclegg_Z ?xs) =>
          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
          -- <= (cyclegg_take Cyclegg_Z ?xs)
          -- <= (cyclegg_sub Cyclegg_Z ?y)
          -- <= case-split:goal_58:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_m=Cyclegg_Z
          ()
    (Cyclegg_Z ) ->
      -- case-split:goal_58:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_drop Cyclegg_Z ?xs) =>
      -- <= (cyclegg_sub ?x Cyclegg_Z)
      -- <= case-split:goal_58:cyclegg_n=Cyclegg_Z
      -- <= (cyclegg_drop Cyclegg_Z ?xs)
      -- <= case-split:goal_58:cyclegg_n=Cyclegg_Z
      ()


{-@ lemma_28 :: cyclegg_n_80: Cyclegg_Nat -> cyclegg_m_140: Cyclegg_Nat -> { (cyclegg_drop cyclegg_n_80 Cyclegg_Nil) = (cyclegg_take (cyclegg_sub cyclegg_m_140 cyclegg_n_80) (cyclegg_drop cyclegg_n_80 Cyclegg_Nil)) } @-}
lemma_28 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_28 cyclegg_n_80 cyclegg_m_140 =
  case cyclegg_n_80 of
    (Cyclegg_S cyclegg_n_80_60) ->
      case cyclegg_m_140 of
        (Cyclegg_S cyclegg_m_140_120) ->
          case cyclegg_n_80_60 of
            (Cyclegg_S cyclegg_n_80_60_190) ->
              -- case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60) =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60):cyclegg_m_140=(Cyclegg_S cyclegg_m_140_120):cyclegg_n_80_60=(Cyclegg_S cyclegg_n_80_60_190)
              lemma_28 (cyclegg_n_80_60) (cyclegg_m_140_120)
              -- <= lemma_28-(cyclegg_take (cyclegg_sub ?cyclegg_m_140 ?cyclegg_n_80) (cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil))=(cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil)
              -- <= (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y))
              -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60):cyclegg_m_140=(Cyclegg_S cyclegg_m_140_120)
              -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60)
              -- case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60):cyclegg_m_140=(Cyclegg_S cyclegg_m_140_120):cyclegg_n_80_60=(Cyclegg_S cyclegg_n_80_60_190) =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60)
            (Cyclegg_Z ) ->
              -- case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60) =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop Cyclegg_Z ?xs)
              -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60):cyclegg_m_140=(Cyclegg_S cyclegg_m_140_120):cyclegg_n_80_60=Cyclegg_Z
              lemma_28 (cyclegg_n_80_60) (cyclegg_m_140_120)
              -- <= lemma_28-(cyclegg_take (cyclegg_sub ?cyclegg_m_140 ?cyclegg_n_80) (cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil))=(cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil)
              -- <= (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y))
              -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60):cyclegg_m_140=(Cyclegg_S cyclegg_m_140_120)
              -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60)
              -- case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60):cyclegg_m_140=(Cyclegg_S cyclegg_m_140_120):cyclegg_n_80_60=Cyclegg_Z =>
              -- (cyclegg_drop Cyclegg_Z ?xs) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60)
        (Cyclegg_Z ) ->
          -- case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60) =>
          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
          -- <= (cyclegg_take Cyclegg_Z ?xs)
          -- <= (cyclegg_sub Cyclegg_Z ?y)
          -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60):cyclegg_m_140=Cyclegg_Z
          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
          -- <= case-split:lemma_28:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60)
          ()
    (Cyclegg_Z ) ->
      case cyclegg_m_140 of
        (Cyclegg_S cyclegg_m_140_90) ->
          -- case-split:lemma_28:cyclegg_n_80=Cyclegg_Z =>
          -- (cyclegg_drop Cyclegg_Z ?xs) =>
          -- <= (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil)
          -- <= case-split:lemma_28:cyclegg_n_80=Cyclegg_Z:cyclegg_m_140=(Cyclegg_S cyclegg_m_140_90)
          -- <= (cyclegg_sub ?x Cyclegg_Z)
          -- <= case-split:lemma_28:cyclegg_n_80=Cyclegg_Z
          -- <= (cyclegg_drop Cyclegg_Z ?xs)
          -- <= case-split:lemma_28:cyclegg_n_80=Cyclegg_Z
          ()
        (Cyclegg_Z ) ->
          -- case-split:lemma_28:cyclegg_n_80=Cyclegg_Z =>
          -- (cyclegg_drop Cyclegg_Z ?xs) =>
          -- <= (cyclegg_take Cyclegg_Z ?xs)
          -- <= case-split:lemma_28:cyclegg_n_80=Cyclegg_Z:cyclegg_m_140=Cyclegg_Z
          -- <= (cyclegg_sub ?x Cyclegg_Z)
          -- <= case-split:lemma_28:cyclegg_n_80=Cyclegg_Z
          ()


{-@ lemma_25 :: cyclegg_n_80: Cyclegg_Nat -> cyclegg_m_140: Cyclegg_Nat -> { (cyclegg_take (cyclegg_sub cyclegg_m_140 cyclegg_n_80) (cyclegg_drop cyclegg_n_80 Cyclegg_Nil)) = Cyclegg_Nil } @-}
lemma_25 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_25 cyclegg_n_80 cyclegg_m_140 =
  case cyclegg_n_80 of
    (Cyclegg_S cyclegg_n_80_60) ->
      case cyclegg_m_140 of
        (Cyclegg_S cyclegg_m_140_120) ->
          -- case-split:lemma_25:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60):cyclegg_m_140=(Cyclegg_S cyclegg_m_140_120) =>
          -- case-split:lemma_25:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60) =>
          -- (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- case-split:lemma_25:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60) =>
          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
          lemma_25 (cyclegg_n_80_60) (cyclegg_m_140_120)
          -- <= lemma_25-(cyclegg_take (cyclegg_sub ?cyclegg_m_140 ?cyclegg_n_80) (cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil))=Cyclegg_Nil
          ? lemma_28 (cyclegg_n_80_60) (cyclegg_m_140_120)
          -- lemma_28-(cyclegg_take (cyclegg_sub ?cyclegg_m_140 ?cyclegg_n_80) (cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil))=(cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil) =>
          ? lemma_25 (cyclegg_n_80_60) (cyclegg_m_140_120)
          -- lemma_25-(cyclegg_take (cyclegg_sub ?cyclegg_m_140 ?cyclegg_n_80) (cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil))=Cyclegg_Nil =>
        (Cyclegg_Z ) ->
          lemma_28 (cyclegg_n_80) (cyclegg_m_140)
          -- lemma_28-(cyclegg_take (cyclegg_sub ?cyclegg_m_140 ?cyclegg_n_80) (cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil))=(cyclegg_drop ?cyclegg_n_80 Cyclegg_Nil) =>
          -- case-split:lemma_25:cyclegg_n_80=(Cyclegg_S cyclegg_n_80_60) =>
          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
    (Cyclegg_Z ) ->
      case cyclegg_m_140 of
        (Cyclegg_S cyclegg_m_140_90) ->
          -- case-split:lemma_25:cyclegg_n_80=Cyclegg_Z =>
          -- (cyclegg_sub ?x Cyclegg_Z) =>
          -- case-split:lemma_25:cyclegg_n_80=Cyclegg_Z:cyclegg_m_140=(Cyclegg_S cyclegg_m_140_90) =>
          -- case-split:lemma_25:cyclegg_n_80=Cyclegg_Z =>
          -- (cyclegg_drop Cyclegg_Z ?xs) =>
          -- (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil) =>
          ()
        (Cyclegg_Z ) ->
          -- case-split:lemma_25:cyclegg_n_80=Cyclegg_Z =>
          -- (cyclegg_sub ?x Cyclegg_Z) =>
          -- case-split:lemma_25:cyclegg_n_80=Cyclegg_Z:cyclegg_m_140=Cyclegg_Z =>
          -- (cyclegg_take Cyclegg_Z ?xs) =>
          ()


