{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_8: (cyclegg_drop cyclegg_x (cyclegg_drop cyclegg_y cyclegg_z)) = (cyclegg_drop cyclegg_y (cyclegg_drop cyclegg_x cyclegg_z))
module Clam8 where
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

{-@ clam_8 :: cyclegg_x: Cyclegg_Nat -> cyclegg_y: Cyclegg_Nat -> cyclegg_z: (Cyclegg_List cyclegg_a) -> { (cyclegg_drop cyclegg_x (cyclegg_drop cyclegg_y cyclegg_z)) = (cyclegg_drop cyclegg_y (cyclegg_drop cyclegg_x cyclegg_z)) } @-}
clam_8 :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> Proof
clam_8 cyclegg_x cyclegg_y cyclegg_z =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_70) ->
      case cyclegg_y of
        (Cyclegg_S cyclegg_y_120) ->
          case cyclegg_z of
            (Cyclegg_Cons cyclegg_z_190 cyclegg_z_191) ->
              case cyclegg_x_70 of
                (Cyclegg_S cyclegg_x_70_340) ->
                  case cyclegg_y_120 of
                    (Cyclegg_S cyclegg_y_120_540) ->
                      case cyclegg_z_191 of
                        (Cyclegg_Cons cyclegg_z_191_800 cyclegg_z_191_801) ->
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          clam_8 (cyclegg_x) (cyclegg_y_120) (cyclegg_z_191)
                          -- clam_8-(cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x ?cyclegg_z)) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=(Cyclegg_S cyclegg_y_120_540):cyclegg_z_191=(Cyclegg_Cons cyclegg_z_191_800 cyclegg_z_191_801) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          ? clam_8 (cyclegg_x_70) (cyclegg_y_120) (cyclegg_z_191_801)
                          -- <= clam_8-(cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x ?cyclegg_z))
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=(Cyclegg_S cyclegg_y_120_540):cyclegg_z_191=(Cyclegg_Cons cyclegg_z_191_800 cyclegg_z_191_801)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120)
                          ? clam_8 (cyclegg_x_70) (cyclegg_y) (cyclegg_z_191)
                          -- clam_8-(cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x ?cyclegg_z)) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191)
                        (Cyclegg_Nil ) ->
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=(Cyclegg_S cyclegg_y_120_540) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=(Cyclegg_S cyclegg_y_120_540):cyclegg_z_191=Cyclegg_Nil =>
                          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=(Cyclegg_S cyclegg_y_120_540):cyclegg_z_191=Cyclegg_Nil
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120)
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191)
                          ()
                    (Cyclegg_Z ) ->
                      case cyclegg_z_191 of
                        (Cyclegg_Cons cyclegg_z_191_550 cyclegg_z_191_551) ->
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=Cyclegg_Z =>
                          -- (cyclegg_drop Cyclegg_Z ?xs) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=Cyclegg_Z:cyclegg_z_191=(Cyclegg_Cons cyclegg_z_191_550 cyclegg_z_191_551) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          -- <= (cyclegg_drop Cyclegg_Z ?xs)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=Cyclegg_Z
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=Cyclegg_Z:cyclegg_z_191=(Cyclegg_Cons cyclegg_z_191_550 cyclegg_z_191_551)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120)
                          clam_8 (cyclegg_x_70) (cyclegg_y) (cyclegg_z_191)
                          -- clam_8-(cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x ?cyclegg_z)) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191)
                        (Cyclegg_Nil ) ->
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=Cyclegg_Z =>
                          -- (cyclegg_drop Cyclegg_Z ?xs) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=Cyclegg_Z:cyclegg_z_191=Cyclegg_Nil =>
                          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340)
                          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=(Cyclegg_S cyclegg_x_70_340):cyclegg_y_120=Cyclegg_Z:cyclegg_z_191=Cyclegg_Nil
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120)
                          clam_8 (cyclegg_x_70) (cyclegg_y) (cyclegg_z_191)
                          -- clam_8-(cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x ?cyclegg_z)) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191)
                (Cyclegg_Z ) ->
                  case cyclegg_y_120 of
                    (Cyclegg_S cyclegg_y_120_350) ->
                      case cyclegg_z_191 of
                        (Cyclegg_Cons cyclegg_z_191_510 cyclegg_z_191_511) ->
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          clam_8 (cyclegg_x) (cyclegg_y_120) (cyclegg_z_191)
                          -- clam_8-(cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x ?cyclegg_z)) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z:cyclegg_y_120=(Cyclegg_S cyclegg_y_120_350):cyclegg_z_191=(Cyclegg_Cons cyclegg_z_191_510 cyclegg_z_191_511) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z =>
                          -- (cyclegg_drop Cyclegg_Z ?xs) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z:cyclegg_y_120=(Cyclegg_S cyclegg_y_120_350):cyclegg_z_191=(Cyclegg_Cons cyclegg_z_191_510 cyclegg_z_191_511)
                          -- <= (cyclegg_drop Cyclegg_Z ?xs)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191)
                        (Cyclegg_Nil ) ->
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                          clam_8 (cyclegg_x) (cyclegg_y_120) (cyclegg_z_191)
                          -- clam_8-(cyclegg_drop ?cyclegg_x (cyclegg_drop ?cyclegg_y ?cyclegg_z))=(cyclegg_drop ?cyclegg_y (cyclegg_drop ?cyclegg_x ?cyclegg_z)) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z:cyclegg_y_120=(Cyclegg_S cyclegg_y_120_350) =>
                          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z:cyclegg_y_120=(Cyclegg_S cyclegg_y_120_350):cyclegg_z_191=Cyclegg_Nil =>
                          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                          -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
                          -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z:cyclegg_y_120=(Cyclegg_S cyclegg_y_120_350):cyclegg_z_191=Cyclegg_Nil
                          -- <= (cyclegg_drop Cyclegg_Z ?xs)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z
                          -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70)
                          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191)
                    (Cyclegg_Z ) ->
                      -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
                      -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z =>
                      -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z:cyclegg_y_120=Cyclegg_Z
                      -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120)
                      -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120) =>
                      -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z:cyclegg_y_120=Cyclegg_Z =>
                      -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191):cyclegg_x_70=Cyclegg_Z
                      -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191) =>
                      -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
                      -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
                      -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70)
                      -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=(Cyclegg_Cons cyclegg_z_190 cyclegg_z_191)
                      ()
            (Cyclegg_Nil ) ->
              -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70) =>
              -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120) =>
              -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120)
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70)
              -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=(Cyclegg_S cyclegg_y_120):cyclegg_z=Cyclegg_Nil
              ()
        (Cyclegg_Z ) ->
          -- case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=Cyclegg_Z =>
          -- (cyclegg_drop Cyclegg_Z ?xs) =>
          -- <= (cyclegg_drop Cyclegg_Z ?xs)
          -- <= case-split:clam_8:cyclegg_x=(Cyclegg_S cyclegg_x_70):cyclegg_y=Cyclegg_Z
          ()
    (Cyclegg_Z ) ->
      -- case-split:clam_8:cyclegg_x=Cyclegg_Z =>
      -- (cyclegg_drop Cyclegg_Z ?xs) =>
      -- <= (cyclegg_drop Cyclegg_Z ?xs)
      -- <= case-split:clam_8:cyclegg_x=Cyclegg_Z
      ()


