{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- rev1_count_no_cyclic: (cyclegg_count cyclegg_n cyclegg_xs) = (cyclegg_count cyclegg_n (cyclegg_rev1 cyclegg_xs))
module Rev1CountNoCyclic where
import Language.Haskell.Liquid.Equational

{-@ autosize Cyclegg_Nat @-}
data Cyclegg_Nat where
  Cyclegg_Z :: Cyclegg_Nat
  Cyclegg_S :: (Cyclegg_Nat -> Cyclegg_Nat)

{-@ autosize Cyclegg_Bool @-}
data Cyclegg_Bool where
  Cyclegg_True :: Cyclegg_Bool
  Cyclegg_False :: Cyclegg_Bool

{-@ autosize Cyclegg_List @-}
data Cyclegg_List cyclegg_a where
  Cyclegg_Nil :: (Cyclegg_List cyclegg_a)
  Cyclegg_Cons :: (cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))

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

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_rev1 @-}
cyclegg_rev1 :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_rev1 Cyclegg_Nil = Cyclegg_Nil
cyclegg_rev1 (Cyclegg_Cons x xs) = (cyclegg_append xs (Cyclegg_Cons x Cyclegg_Nil))

{-@ type Pos = {v: Int | v >= 1 } @-}

{-@ measure natSize @-}
{-@ natSize :: Cyclegg_Nat -> Pos @-}
natSize :: Cyclegg_Nat -> Int
natSize Cyclegg_Z = 1
natSize (Cyclegg_S n) = 1 + natSize n

{-@ measure listSum @-}
{-@ listSum :: Cyclegg_List Cyclegg_Nat -> Pos @-}
listSum :: Cyclegg_List Cyclegg_Nat -> Int
listSum Cyclegg_Nil = 1
listSum (Cyclegg_Cons n xs) = 1 + natSize n + listSum xs

{-@ rev1_count_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_count cyclegg_n cyclegg_xs) = (cyclegg_count cyclegg_n (cyclegg_rev1 cyclegg_xs)) } / [listSum cyclegg_xs] @-}
rev1_count_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
rev1_count_no_cyclic cyclegg_n cyclegg_xs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) ->
      let g_16 = (cyclegg_eq cyclegg_n cyclegg_xs_50) in
        case g_16 of
          (Cyclegg_False ) ->
            case cyclegg_xs_51 of
              (Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191) ->
                -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_False =>
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_False:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_False
                -- <= add guard scrutinee
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                rev1_count_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191)
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191) =>
                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_False
                -- <= add guard scrutinee
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                ? rev1_count_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191)
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191) =>
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                -- (cyclegg_rev1 (Cyclegg_Cons ?x ?xs)) =>
                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_False:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191)
                -- <= (cyclegg_rev1 (Cyclegg_Cons ?x ?xs))
                -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
              (Cyclegg_Nil ) ->
                -- <= (cyclegg_append Cyclegg_Nil ?ys)
                -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_False:cyclegg_xs_51=Cyclegg_Nil
                -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_False:cyclegg_xs_51=Cyclegg_Nil =>
                -- <= (cyclegg_rev1 (Cyclegg_Cons ?x ?xs))
                -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
                ()
          (Cyclegg_True ) ->
            case cyclegg_xs_51 of
              (Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191) ->
                let g_41 = (cyclegg_eq cyclegg_n cyclegg_xs_51_190) in
                  case g_41 of
                    (Cyclegg_False ) ->
                      -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191):g_41=Cyclegg_False =>
                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191):g_41=Cyclegg_False
                      -- <= add guard scrutinee
                      rev1_count_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191)
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191) =>
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      -- (cyclegg_rev1 (Cyclegg_Cons ?x ?xs)) =>
                      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191)
                      -- <= (cyclegg_rev1 (Cyclegg_Cons ?x ?xs))
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
                    (Cyclegg_True ) ->
                      -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191):g_41=Cyclegg_True =>
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      rev1_count_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191)
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191) =>
                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191):g_41=Cyclegg_True
                      -- <= add guard scrutinee
                      ? rev1_count_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191)
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51_191) =>
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      -- (cyclegg_rev1 (Cyclegg_Cons ?x ?xs)) =>
                      -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_190 cyclegg_xs_51_191)
                      -- <= (cyclegg_rev1 (Cyclegg_Cons ?x ?xs))
                      -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
              (Cyclegg_Nil ) ->
                -- <= (cyclegg_append Cyclegg_Nil ?ys)
                -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=Cyclegg_Nil
                -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
                -- rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):g_16=Cyclegg_True:cyclegg_xs_51=Cyclegg_Nil =>
                -- <= (cyclegg_rev1 (Cyclegg_Cons ?x ?xs))
                -- <= rev1_count_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
                ()
    (Cyclegg_Nil ) ->
      -- rev1_count_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
      -- <= (cyclegg_rev1 Cyclegg_Nil)
      -- <= rev1_count_no_cyclic:cyclegg_xs=Cyclegg_Nil
      ()

