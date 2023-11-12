{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_9: (cyclegg_drop cyclegg_w (cyclegg_drop cyclegg_x (cyclegg_drop cyclegg_y cyclegg_z))) = (cyclegg_drop cyclegg_y (cyclegg_drop cyclegg_x (cyclegg_drop cyclegg_w cyclegg_z)))
module Clam9 where
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

{-@ reflect cyclegg_drop @-}
cyclegg_drop :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_drop Cyclegg_Z xs = xs
cyclegg_drop (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_drop (Cyclegg_S n) (Cyclegg_Cons x xs) = (cyclegg_drop n xs)

{-@ clam_9 :: cyclegg_w: Cyclegg_Nat -> cyclegg_x: Cyclegg_Nat -> cyclegg_y: Cyclegg_Nat -> cyclegg_z: (Cyclegg_List cyclegg_a) -> { (cyclegg_drop cyclegg_w (cyclegg_drop cyclegg_x (cyclegg_drop cyclegg_y cyclegg_z))) = (cyclegg_drop cyclegg_y (cyclegg_drop cyclegg_x (cyclegg_drop cyclegg_w cyclegg_z))) } @-}
clam_9 :: Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> Proof
clam_9 cyclegg_w cyclegg_x cyclegg_y cyclegg_z =
  case cyclegg_w of
    (Cyclegg_S cyclegg_w_100) ->
      case cyclegg_x of
        (Cyclegg_S cyclegg_x_160) ->
          case cyclegg_y of
            (Cyclegg_S cyclegg_y_250) ->
              case cyclegg_z of
                (Cyclegg_Cons cyclegg_z_380 cyclegg_z_381) ->
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100) =>
                  lemma_103 (cyclegg_w_100) (cyclegg_x) ((cyclegg_drop cyclegg_y cyclegg_z))
                  -- lemma_103-(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25))=(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25)) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250):cyclegg_z=(Cyclegg_Cons cyclegg_z_380 cyclegg_z_381) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                  ? lemma_103 (cyclegg_x) (cyclegg_y_250) (cyclegg_z_381)
                  -- <= lemma_103-(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25))=(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25))
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160) =>
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250)
                  ? clam_9 (cyclegg_w_100) (cyclegg_x) (cyclegg_y) (cyclegg_z_381)
                  -- clam_9-(cyclegg_drop ?cyclegg_w (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z)))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_w ?cyclegg_z))) =>
                  -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250):cyclegg_z=(Cyclegg_Cons cyclegg_z_380 cyclegg_z_381)
                (Cyclegg_Nil ) ->
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160) =>
                  lemma_103 (cyclegg_x_160) (cyclegg_y) (cyclegg_z)
                  -- lemma_103-(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25))=(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25)) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250):cyclegg_z=Cyclegg_Nil =>
                  -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                  -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250):cyclegg_z=Cyclegg_Nil
                  ? clam_9 (cyclegg_w) (cyclegg_x_160) (cyclegg_y) (cyclegg_z)
                  -- clam_9-(cyclegg_drop ?cyclegg_w (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z)))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_w ?cyclegg_z))) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100) =>
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100)
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250):cyclegg_z=Cyclegg_Nil =>
                  -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                  -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=(Cyclegg_S cyclegg_y_250):cyclegg_z=Cyclegg_Nil
                  ? lemma_103 (cyclegg_x_160) (cyclegg_w) (cyclegg_z)
                  -- <= lemma_103-(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25))=(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25))
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160)
            (Cyclegg_Z ) ->
              case cyclegg_z of
                (Cyclegg_Cons cyclegg_z_310 cyclegg_z_311) ->
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=Cyclegg_Z =>
                  -- (cyclegg_drop Cyclegg_Z ?xs) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=Cyclegg_Z:cyclegg_z=(Cyclegg_Cons cyclegg_z_310 cyclegg_z_311) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                  lemma_103 (cyclegg_w_100) (cyclegg_x_160) (cyclegg_z_311)
                  -- <= lemma_103-(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25))=(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25))
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160)
                  -- <= (cyclegg_drop Cyclegg_Z ?xs)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=Cyclegg_Z
                  ? clam_9 (cyclegg_w_100) (cyclegg_x) (cyclegg_y) (cyclegg_z_311)
                  -- clam_9-(cyclegg_drop ?cyclegg_w (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z)))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_w ?cyclegg_z))) =>
                  -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=Cyclegg_Z:cyclegg_z=(Cyclegg_Cons cyclegg_z_310 cyclegg_z_311)
                (Cyclegg_Nil ) ->
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=Cyclegg_Z =>
                  -- (cyclegg_drop Cyclegg_Z ?xs) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=Cyclegg_Z:cyclegg_z=Cyclegg_Nil =>
                  -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                  -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                  -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=Cyclegg_Z:cyclegg_z=Cyclegg_Nil
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160)
                  -- <= (cyclegg_drop Cyclegg_Z ?xs)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=(Cyclegg_S cyclegg_x_160):cyclegg_y=Cyclegg_Z
                  ()
        (Cyclegg_Z ) ->
          case cyclegg_y of
            (Cyclegg_S cyclegg_y_220) ->
              case cyclegg_z of
                (Cyclegg_Cons cyclegg_z_330 cyclegg_z_331) ->
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_220) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_220):cyclegg_z=(Cyclegg_Cons cyclegg_z_330 cyclegg_z_331) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                  clam_9 (cyclegg_w) (cyclegg_x) (cyclegg_y_220) (cyclegg_z_331)
                  -- clam_9-(cyclegg_drop ?cyclegg_w (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z)))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_w ?cyclegg_z))) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100) =>
                  ? lemma_103 (cyclegg_x) (cyclegg_w_100) (cyclegg_z_331)
                  -- lemma_103-(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25))=(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25)) =>
                  -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_220):cyclegg_z=(Cyclegg_Cons cyclegg_z_330 cyclegg_z_331)
                  -- <= (cyclegg_drop Cyclegg_Z ?xs)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z
                  ? lemma_103 (cyclegg_y_220) (cyclegg_x) ((cyclegg_drop cyclegg_x (cyclegg_drop cyclegg_w cyclegg_z)))
                  -- <= lemma_103-(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25))=(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25))
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_220)
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z =>
                  -- (cyclegg_drop Cyclegg_Z ?xs) =>
                (Cyclegg_Nil ) ->
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z =>
                  -- (cyclegg_drop Cyclegg_Z ?xs) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_220) =>
                  -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_220):cyclegg_z=Cyclegg_Nil =>
                  -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                  -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_220)
                  -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_220):cyclegg_z=Cyclegg_Nil
                  -- <= (cyclegg_drop Cyclegg_Z ?xs)
                  -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z
                  ()
            (Cyclegg_Z ) ->
              -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z =>
              -- (cyclegg_drop Cyclegg_Z ?xs) =>
              -- case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=Cyclegg_Z =>
              -- (cyclegg_drop Cyclegg_Z ?xs) =>
              -- <= (cyclegg_drop Cyclegg_Z ?xs)
              -- <= (cyclegg_drop Cyclegg_Z ?xs)
              -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z
              -- <= case-split:clam_9:cyclegg_w=(Cyclegg_S cyclegg_w_100):cyclegg_x=Cyclegg_Z:cyclegg_y=Cyclegg_Z
              ()
    (Cyclegg_Z ) ->
      case cyclegg_x of
        (Cyclegg_S cyclegg_x_120) ->
          case cyclegg_y of
            (Cyclegg_S cyclegg_y_180) ->
              case cyclegg_z of
                (Cyclegg_Cons cyclegg_z_270 cyclegg_z_271) ->
                  -- case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=(Cyclegg_S cyclegg_y_180) =>
                  -- case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=(Cyclegg_S cyclegg_y_180):cyclegg_z=(Cyclegg_Cons cyclegg_z_270 cyclegg_z_271) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                  clam_9 (cyclegg_w) (cyclegg_x) (cyclegg_y_180) (cyclegg_z_271)
                  -- clam_9-(cyclegg_drop ?cyclegg_w (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z)))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_w ?cyclegg_z))) =>
                  -- case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120) =>
                  -- case-split:clam_9:cyclegg_w=Cyclegg_Z =>
                  -- (cyclegg_drop Cyclegg_Z ?xs) =>
                  ? lemma_103 (cyclegg_y_180) (cyclegg_x_120) (cyclegg_z_271)
                  -- lemma_103-(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25))=(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25)) =>
                  -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=(Cyclegg_S cyclegg_y_180)
                  -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                  -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120)
                  -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=(Cyclegg_S cyclegg_y_180):cyclegg_z=(Cyclegg_Cons cyclegg_z_270 cyclegg_z_271)
                  -- <= (cyclegg_drop Cyclegg_Z ?xs)
                  -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z
                (Cyclegg_Nil ) ->
                  -- case-split:clam_9:cyclegg_w=Cyclegg_Z =>
                  -- (cyclegg_drop Cyclegg_Z ?xs) =>
                  -- case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120) =>
                  -- case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=(Cyclegg_S cyclegg_y_180) =>
                  -- case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=(Cyclegg_S cyclegg_y_180):cyclegg_z=Cyclegg_Nil =>
                  -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                  -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                  -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                  -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=(Cyclegg_S cyclegg_y_180)
                  -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                  -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120)
                  -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=(Cyclegg_S cyclegg_y_180):cyclegg_z=Cyclegg_Nil
                  -- <= (cyclegg_drop Cyclegg_Z ?xs)
                  -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z
                  ()
            (Cyclegg_Z ) ->
              -- case-split:clam_9:cyclegg_w=Cyclegg_Z =>
              -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=Cyclegg_Z
              -- case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=(Cyclegg_S cyclegg_x_120):cyclegg_y=Cyclegg_Z =>
              -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z
              ()
        (Cyclegg_Z ) ->
          -- case-split:clam_9:cyclegg_w=Cyclegg_Z =>
          -- (cyclegg_drop Cyclegg_Z ?xs) =>
          -- case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=Cyclegg_Z =>
          -- (cyclegg_drop Cyclegg_Z ?xs) =>
          -- <= (cyclegg_drop Cyclegg_Z ?xs)
          -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z
          -- case-split:clam_9:cyclegg_w=Cyclegg_Z =>
          -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z:cyclegg_x=Cyclegg_Z
          -- <= (cyclegg_drop Cyclegg_Z ?xs)
          -- <= case-split:clam_9:cyclegg_w=Cyclegg_Z
          ()


{-@ lemma_103 :: cyclegg_w_100: Cyclegg_Nat -> cyclegg_x_160: Cyclegg_Nat -> fresh_25: (Cyclegg_List cyclegg_a) -> { (cyclegg_drop (Cyclegg_S cyclegg_w_100) (cyclegg_drop cyclegg_x_160 fresh_25)) = (cyclegg_drop cyclegg_w_100 (cyclegg_drop (Cyclegg_S cyclegg_x_160) fresh_25)) } @-}
lemma_103 :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> Proof
lemma_103 cyclegg_w_100 cyclegg_x_160 fresh_25 =
  case cyclegg_w_100 of
    (Cyclegg_S cyclegg_w_100_90) ->
      case cyclegg_x_160 of
        (Cyclegg_S cyclegg_x_160_140) ->
          case fresh_25 of
            (Cyclegg_Cons fresh_25_230 fresh_25_231) ->
              -- case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=(Cyclegg_S cyclegg_x_160_140) =>
              -- case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=(Cyclegg_S cyclegg_x_160_140):fresh_25=(Cyclegg_Cons fresh_25_230 fresh_25_231) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              lemma_103 (cyclegg_w_100) (cyclegg_x_160_140) (fresh_25_231)
              -- <= lemma_103-(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25))=(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25))
              -- <= case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=(Cyclegg_S cyclegg_x_160_140)
              -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=(Cyclegg_S cyclegg_x_160_140):fresh_25=(Cyclegg_Cons fresh_25_230 fresh_25_231)
            (Cyclegg_Nil ) ->
              -- case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=(Cyclegg_S cyclegg_x_160_140) =>
              -- case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=(Cyclegg_S cyclegg_x_160_140):fresh_25=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90)
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=(Cyclegg_S cyclegg_x_160_140):fresh_25=Cyclegg_Nil
              ()
        (Cyclegg_Z ) ->
          case fresh_25 of
            (Cyclegg_Cons fresh_25_190 fresh_25_191) ->
              -- case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=Cyclegg_Z =>
              -- (cyclegg_drop Cyclegg_Z ?xs) =>
              -- case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=Cyclegg_Z:fresh_25=(Cyclegg_Cons fresh_25_190 fresh_25_191) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              -- <= (cyclegg_drop Cyclegg_Z ?xs)
              -- <= case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=Cyclegg_Z
              -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=Cyclegg_Z:fresh_25=(Cyclegg_Cons fresh_25_190 fresh_25_191)
              ()
            (Cyclegg_Nil ) ->
              -- case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=Cyclegg_Z =>
              -- (cyclegg_drop Cyclegg_Z ?xs) =>
              -- case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=Cyclegg_Z:fresh_25=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90)
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:lemma_103:cyclegg_w_100=(Cyclegg_S cyclegg_w_100_90):cyclegg_x_160=Cyclegg_Z:fresh_25=Cyclegg_Nil
              ()
    (Cyclegg_Z ) ->
      case cyclegg_x_160 of
        (Cyclegg_S cyclegg_x_160_100) ->
          case fresh_25 of
            (Cyclegg_Cons fresh_25_170 fresh_25_171) ->
              -- case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=(Cyclegg_S cyclegg_x_160_100) =>
              -- case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=(Cyclegg_S cyclegg_x_160_100):fresh_25=(Cyclegg_Cons fresh_25_170 fresh_25_171) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              lemma_103 (cyclegg_w_100) (cyclegg_x_160_100) (fresh_25_171)
              -- <= lemma_103-(cyclegg_drop ?cyclegg_w_100 (cyclegg_drop (Cyclegg_S ?cyclegg_x_160) ?fresh_25))=(cyclegg_drop (Cyclegg_S ?cyclegg_w_100) (cyclegg_drop ?cyclegg_x_160 ?fresh_25))
              -- <= case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=(Cyclegg_S cyclegg_x_160_100)
              -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=(Cyclegg_S cyclegg_x_160_100):fresh_25=(Cyclegg_Cons fresh_25_170 fresh_25_171)
            (Cyclegg_Nil ) ->
              -- case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=(Cyclegg_S cyclegg_x_160_100) =>
              -- case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=(Cyclegg_S cyclegg_x_160_100):fresh_25=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=(Cyclegg_S cyclegg_x_160_100):fresh_25=Cyclegg_Nil
              -- <= (cyclegg_drop Cyclegg_Z ?xs)
              -- <= case-split:lemma_103:cyclegg_w_100=Cyclegg_Z
              ()
        (Cyclegg_Z ) ->
          -- case-split:lemma_103:cyclegg_w_100=Cyclegg_Z =>
          -- <= case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=Cyclegg_Z
          -- case-split:lemma_103:cyclegg_w_100=Cyclegg_Z:cyclegg_x_160=Cyclegg_Z =>
          -- (cyclegg_drop Cyclegg_Z ?xs) =>
          -- <= (cyclegg_drop Cyclegg_Z ?xs)
          -- <= case-split:lemma_103:cyclegg_w_100=Cyclegg_Z
          ()


