{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_85: (cyclegg_append (cyclegg_zip cyclegg_xs (cyclegg_take (cyclegg_len cyclegg_xs) cyclegg_zs)) (cyclegg_zip cyclegg_ys (cyclegg_drop (cyclegg_len cyclegg_xs) cyclegg_zs))) = (cyclegg_zip (cyclegg_append cyclegg_xs cyclegg_ys) cyclegg_zs)
module Goal85 where
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

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_take @-}
cyclegg_take :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_take Cyclegg_Z xs = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) (Cyclegg_Cons x xs) = (Cyclegg_Cons x (cyclegg_take n xs))

{-@ reflect cyclegg_zip @-}
cyclegg_zip :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_b) -> (Cyclegg_List (Cyclegg_Pair cyclegg_a cyclegg_b)))
cyclegg_zip Cyclegg_Nil ys = Cyclegg_Nil
cyclegg_zip xs Cyclegg_Nil = Cyclegg_Nil
cyclegg_zip (Cyclegg_Cons x xs) (Cyclegg_Cons y ys) = (Cyclegg_Cons (Cyclegg_Pair x y) (cyclegg_zip xs ys))

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ goal_85 :: cyclegg_xs: (Cyclegg_List cyclegg_a) -> cyclegg_ys: (Cyclegg_List cyclegg_a) -> cyclegg_zs: (Cyclegg_List cyclegg_a) -> { (cyclegg_append (cyclegg_zip cyclegg_xs (cyclegg_take (cyclegg_len cyclegg_xs) cyclegg_zs)) (cyclegg_zip cyclegg_ys (cyclegg_drop (cyclegg_len cyclegg_xs) cyclegg_zs))) = (cyclegg_zip (cyclegg_append cyclegg_xs cyclegg_ys) cyclegg_zs) } @-}
goal_85 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
goal_85 cyclegg_xs cyclegg_ys cyclegg_zs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) ->
      case cyclegg_ys of
        (Cyclegg_Cons cyclegg_ys_240 cyclegg_ys_241) ->
          case cyclegg_zs of
            (Cyclegg_Cons cyclegg_zs_360 cyclegg_zs_361) ->
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_240 cyclegg_ys_241):cyclegg_zs=(Cyclegg_Cons cyclegg_zs_360 cyclegg_zs_361) =>
              -- (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              -- (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys)) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_240 cyclegg_ys_241):cyclegg_zs=(Cyclegg_Cons cyclegg_zs_360 cyclegg_zs_361) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              goal_85 (cyclegg_xs_111) (cyclegg_ys) (cyclegg_zs_361)
              -- <= goal_85-(cyclegg_zip (cyclegg_append ?cyclegg_xs ?cyclegg_ys) ?cyclegg_zs)=(cyclegg_append (cyclegg_zip ?cyclegg_xs (cyclegg_take (cyclegg_len ?cyclegg_xs) ?cyclegg_zs)) (cyclegg_zip ?cyclegg_ys (cyclegg_drop (cyclegg_len ?cyclegg_xs) ?cyclegg_zs)))
              -- <= (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys))
              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111)
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_240 cyclegg_ys_241):cyclegg_zs=(Cyclegg_Cons cyclegg_zs_360 cyclegg_zs_361)
            (Cyclegg_Nil ) ->
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_240 cyclegg_ys_241):cyclegg_zs=Cyclegg_Nil =>
              -- (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- (cyclegg_zip ?xs Cyclegg_Nil) =>
              -- <= (cyclegg_zip ?xs Cyclegg_Nil)
              -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111)
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_240 cyclegg_ys_241):cyclegg_zs=Cyclegg_Nil
              goal_85 (cyclegg_xs) (cyclegg_ys_241) (cyclegg_zs)
              -- <= goal_85-(cyclegg_zip (cyclegg_append ?cyclegg_xs ?cyclegg_ys) ?cyclegg_zs)=(cyclegg_append (cyclegg_zip ?cyclegg_xs (cyclegg_take (cyclegg_len ?cyclegg_xs) ?cyclegg_zs)) (cyclegg_zip ?cyclegg_ys (cyclegg_drop (cyclegg_len ?cyclegg_xs) ?cyclegg_zs)))
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_240 cyclegg_ys_241):cyclegg_zs=Cyclegg_Nil =>
              -- (cyclegg_zip ?xs Cyclegg_Nil) =>
              -- <= (cyclegg_zip ?xs Cyclegg_Nil)
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_240 cyclegg_ys_241):cyclegg_zs=Cyclegg_Nil
        (Cyclegg_Nil ) ->
          case cyclegg_zs of
            (Cyclegg_Cons cyclegg_zs_270 cyclegg_zs_271) ->
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil:cyclegg_zs=(Cyclegg_Cons cyclegg_zs_270 cyclegg_zs_271) =>
              -- (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              -- (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys)) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil =>
              -- (cyclegg_zip Cyclegg_Nil ?ys) =>
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil =>
              -- <= (cyclegg_zip Cyclegg_Nil ?ys)
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil:cyclegg_zs=(Cyclegg_Cons cyclegg_zs_270 cyclegg_zs_271) =>
              -- (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              goal_85 (cyclegg_xs_111) (cyclegg_ys) (cyclegg_zs_271)
              -- <= goal_85-(cyclegg_zip (cyclegg_append ?cyclegg_xs ?cyclegg_ys) ?cyclegg_zs)=(cyclegg_append (cyclegg_zip ?cyclegg_xs (cyclegg_take (cyclegg_len ?cyclegg_xs) ?cyclegg_zs)) (cyclegg_zip ?cyclegg_ys (cyclegg_drop (cyclegg_len ?cyclegg_xs) ?cyclegg_zs)))
              -- <= (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys))
              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111)
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil:cyclegg_zs=(Cyclegg_Cons cyclegg_zs_270 cyclegg_zs_271)
            (Cyclegg_Nil ) ->
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
              -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil:cyclegg_zs=Cyclegg_Nil =>
              -- (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- (cyclegg_zip ?xs Cyclegg_Nil) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil =>
              -- (cyclegg_zip Cyclegg_Nil ?ys) =>
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil
              -- (cyclegg_append Cyclegg_Nil ?ys) =>
              -- case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil =>
              -- <= (cyclegg_zip ?xs Cyclegg_Nil)
              -- <= case-split:goal_85:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil:cyclegg_zs=Cyclegg_Nil
              ()
    (Cyclegg_Nil ) ->
      -- case-split:goal_85:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_zip Cyclegg_Nil ?ys) =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= case-split:goal_85:cyclegg_xs=Cyclegg_Nil
      -- case-split:goal_85:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_len Cyclegg_Nil) =>
      -- (cyclegg_drop Cyclegg_Z ?xs) =>
      ()


