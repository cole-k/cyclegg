{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_64: (cyclegg_last (cyclegg_drop cyclegg_n cyclegg_xs)) = (cyclegg_last cyclegg_xs)
module Goal64 where
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

{-@ reflect cyclegg_last @-}
cyclegg_last :: ((Cyclegg_List cyclegg_a) -> cyclegg_a)
cyclegg_last (Cyclegg_Cons x Cyclegg_Nil) = x
cyclegg_last (Cyclegg_Cons x (Cyclegg_Cons y ys)) = (cyclegg_last (Cyclegg_Cons y ys))

{-@ reflect cyclegg_lt @-}
cyclegg_lt :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_lt x Cyclegg_Z = Cyclegg_False
cyclegg_lt Cyclegg_Z (Cyclegg_S y) = Cyclegg_True
cyclegg_lt (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_lt x y)

{-@ reflect cyclegg_drop @-}
cyclegg_drop :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_drop Cyclegg_Z xs = xs
cyclegg_drop (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_drop (Cyclegg_S n) (Cyclegg_Cons x xs) = (cyclegg_drop n xs)

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ goal_64 :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_last (cyclegg_drop cyclegg_n cyclegg_xs)) = (cyclegg_last cyclegg_xs) } @-}
goal_64 :: Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> Proof
goal_64 cyclegg_n cyclegg_xs =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_80) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) ->
          case cyclegg_n_80 of
            (Cyclegg_S cyclegg_n_80_250) ->
              case cyclegg_xs_131 of
                (Cyclegg_Cons cyclegg_xs_131_390 cyclegg_xs_131_391) ->
                  -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
                  -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                  goal_64 (cyclegg_n_80) (cyclegg_xs_131)
                  -- goal_64-(cyclegg_last (cyclegg_drop ?cyclegg_n ?cyclegg_xs))=(cyclegg_last ?cyclegg_xs) =>
                  -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):cyclegg_n_80=(Cyclegg_S cyclegg_n_80_250):cyclegg_xs_131=(Cyclegg_Cons cyclegg_xs_131_390 cyclegg_xs_131_391) =>
                  -- <= (cyclegg_last (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys)))
                  -- <= case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):cyclegg_n_80=(Cyclegg_S cyclegg_n_80_250):cyclegg_xs_131=(Cyclegg_Cons cyclegg_xs_131_390 cyclegg_xs_131_391)
                  -- <= case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131)
                (Cyclegg_Nil ) ->
                  unreachable (
                    -- <= premise (cyclegg_lt cyclegg_n (cyclegg_len cyclegg_xs))=Cyclegg_True
                    -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
                    -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                    -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                    -- (cyclegg_lt (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                    -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):cyclegg_n_80=(Cyclegg_S cyclegg_n_80_250):cyclegg_xs_131=Cyclegg_Nil =>
                    -- (cyclegg_len Cyclegg_Nil) =>
                    -- (cyclegg_lt ?x Cyclegg_Z) =>
                    ()
                  )

            (Cyclegg_Z ) ->
              case cyclegg_xs_131 of
                (Cyclegg_Cons cyclegg_xs_131_260 cyclegg_xs_131_261) ->
                  -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
                  -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                  goal_64 (cyclegg_n_80) (cyclegg_xs_131)
                  -- goal_64-(cyclegg_last (cyclegg_drop ?cyclegg_n ?cyclegg_xs))=(cyclegg_last ?cyclegg_xs) =>
                  -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):cyclegg_n_80=Cyclegg_Z:cyclegg_xs_131=(Cyclegg_Cons cyclegg_xs_131_260 cyclegg_xs_131_261) =>
                  -- <= (cyclegg_last (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys)))
                  -- <= case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):cyclegg_n_80=Cyclegg_Z:cyclegg_xs_131=(Cyclegg_Cons cyclegg_xs_131_260 cyclegg_xs_131_261)
                  -- <= case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131)
                (Cyclegg_Nil ) ->
                  unreachable (
                    -- <= premise (cyclegg_lt cyclegg_n (cyclegg_len cyclegg_xs))=Cyclegg_True
                    -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
                    -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131) =>
                    -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
                    -- (cyclegg_lt (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                    -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_130 cyclegg_xs_131):cyclegg_n_80=Cyclegg_Z:cyclegg_xs_131=Cyclegg_Nil =>
                    -- (cyclegg_len Cyclegg_Nil) =>
                    -- (cyclegg_lt ?x Cyclegg_Z) =>
                    ()
                  )

        (Cyclegg_Nil ) ->
          -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
          -- case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
          -- <= case-split:goal_64:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=Cyclegg_Nil
          ()
    (Cyclegg_Z ) ->
      -- case-split:goal_64:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_drop Cyclegg_Z ?xs) =>
      ()


