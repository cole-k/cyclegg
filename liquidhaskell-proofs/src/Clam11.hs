{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- clam_11: (cyclegg_append cyclegg_y cyclegg_x) = (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev cyclegg_y)))
module Clam11 where
import Language.Haskell.Liquid.Equational

{-@ autosize Cyclegg_Pair @-}
data Cyclegg_Pair cyclegg_a cyclegg_b where
  Cyclegg_Pair :: (cyclegg_a -> cyclegg_b -> (Cyclegg_Pair cyclegg_a cyclegg_b))

{-@ autosize Cyclegg_Bool @-}
data Cyclegg_Bool where
  Cyclegg_True :: Cyclegg_Bool
  Cyclegg_False :: Cyclegg_Bool

{-@ autosize Cyclegg_Expr @-}
data Cyclegg_Expr cyclegg_a where
  Cyclegg_MkExpr :: ((Cyclegg_Tm cyclegg_a) -> Cyclegg_Nat -> (Cyclegg_Expr cyclegg_a))

{-@ autosize Cyclegg_Tm @-}
data Cyclegg_Tm cyclegg_a where
  Cyclegg_Var :: (cyclegg_a -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_Cst :: (Cyclegg_Nat -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_App :: ((Cyclegg_Expr cyclegg_a) -> (Cyclegg_Expr cyclegg_a) -> (Cyclegg_Tm cyclegg_a))

{-@ autosize Cyclegg_Nat @-}
data Cyclegg_Nat where
  Cyclegg_Z :: Cyclegg_Nat
  Cyclegg_S :: (Cyclegg_Nat -> Cyclegg_Nat)

{-@ autosize Cyclegg_List @-}
data Cyclegg_List cyclegg_a where
  Cyclegg_Nil :: (Cyclegg_List cyclegg_a)
  Cyclegg_Cons :: (cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))

{-@ autosize Cyclegg_Tree @-}
data Cyclegg_Tree cyclegg_a where
  Cyclegg_Leaf :: (Cyclegg_Tree cyclegg_a)
  Cyclegg_Node :: ((Cyclegg_Tree cyclegg_a) -> cyclegg_a -> (Cyclegg_Tree cyclegg_a) -> (Cyclegg_Tree cyclegg_a))

{-@ unreachable :: {v: a | false} -> b @-}
unreachable :: a -> b
unreachable x = error "unreachable"

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_rev @-}
cyclegg_rev :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_rev Cyclegg_Nil = Cyclegg_Nil
cyclegg_rev (Cyclegg_Cons x xs) = (cyclegg_append (cyclegg_rev xs) (Cyclegg_Cons x Cyclegg_Nil))

{-@ clam_11 :: cyclegg_x: (Cyclegg_List cyclegg_a) -> cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_append cyclegg_y cyclegg_x) = (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev cyclegg_y))) } @-}
clam_11 :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
clam_11 cyclegg_x cyclegg_y =
  case cyclegg_x of
    (Cyclegg_Cons cyclegg_x_70 cyclegg_x_71) ->
      case cyclegg_y of
        (Cyclegg_Cons cyclegg_y_170 cyclegg_y_171) ->
          (cyclegg_append cyclegg_y cyclegg_x)
          -- case-split:clam_11:cyclegg_x=(Cyclegg_Cons cyclegg_x_70 cyclegg_x_71):cyclegg_y=(Cyclegg_Cons cyclegg_y_170 cyclegg_y_171) =>
          ==. (cyclegg_append (Cyclegg_Cons cyclegg_y_170 cyclegg_y_171) cyclegg_x)
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          ==. (Cyclegg_Cons cyclegg_y_170 (cyclegg_append cyclegg_y_171 cyclegg_x))
          ? clam_11 (cyclegg_x) (cyclegg_y_171)
          -- clam_11-(cyclegg_append ?cyclegg_y ?cyclegg_x)=(cyclegg_rev (cyclegg_append (cyclegg_rev ?cyclegg_x) (cyclegg_rev ?cyclegg_y))) =>
          ==. (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev cyclegg_y_171))))
          ? lemma_24 (cyclegg_y_170) (cyclegg_y_171) ((cyclegg_rev cyclegg_x))
          -- lemma_24-(Cyclegg_Cons ?cyclegg_y_170 (cyclegg_rev (cyclegg_append ?fresh_31 (cyclegg_rev ?cyclegg_y_171))))=(cyclegg_rev (cyclegg_append ?fresh_31 (cyclegg_append (cyclegg_rev ?cyclegg_y_171) (Cyclegg_Cons ?cyclegg_y_170 Cyclegg_Nil)))) =>
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))))
          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev (Cyclegg_Cons cyclegg_y_170 cyclegg_y_171))))
          -- <= case-split:clam_11:cyclegg_x=(Cyclegg_Cons cyclegg_x_70 cyclegg_x_71):cyclegg_y=(Cyclegg_Cons cyclegg_y_170 cyclegg_y_171)
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev cyclegg_y)))
          ***
          QED
        (Cyclegg_Nil ) ->
          (cyclegg_append cyclegg_y cyclegg_x)
          -- case-split:clam_11:cyclegg_x=(Cyclegg_Cons cyclegg_x_70 cyclegg_x_71):cyclegg_y=Cyclegg_Nil =>
          ==. (cyclegg_append Cyclegg_Nil cyclegg_x)
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          ==. cyclegg_x
          ? lemma_3 (cyclegg_x)
          -- lemma_3-?cyclegg_y=(cyclegg_rev (cyclegg_rev ?cyclegg_y)) =>
          ==. (cyclegg_rev (cyclegg_rev cyclegg_x))
          ? lemma_2 ((cyclegg_rev cyclegg_x))
          -- lemma_2-?cyclegg_y=(cyclegg_append ?cyclegg_y Cyclegg_Nil) =>
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) Cyclegg_Nil))
          -- <= (cyclegg_rev Cyclegg_Nil)
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev Cyclegg_Nil)))
          -- <= case-split:clam_11:cyclegg_x=(Cyclegg_Cons cyclegg_x_70 cyclegg_x_71):cyclegg_y=Cyclegg_Nil
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev cyclegg_y)))
          ***
          QED
    (Cyclegg_Nil ) ->
      case cyclegg_y of
        (Cyclegg_Cons cyclegg_y_100 cyclegg_y_101) ->
          (cyclegg_append cyclegg_y cyclegg_x)
          -- case-split:clam_11:cyclegg_x=Cyclegg_Nil =>
          ==. (cyclegg_append cyclegg_y Cyclegg_Nil)
          ? lemma_2 (cyclegg_y)
          -- lemma_2-(cyclegg_append ?cyclegg_y Cyclegg_Nil)=?cyclegg_y =>
          ==. cyclegg_y
          ? lemma_3 (cyclegg_y)
          -- lemma_3-?cyclegg_y=(cyclegg_rev (cyclegg_rev ?cyclegg_y)) =>
          ==. (cyclegg_rev (cyclegg_rev cyclegg_y))
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          ==. (cyclegg_rev (cyclegg_append Cyclegg_Nil (cyclegg_rev cyclegg_y)))
          -- <= (cyclegg_rev Cyclegg_Nil)
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev Cyclegg_Nil) (cyclegg_rev cyclegg_y)))
          -- <= case-split:clam_11:cyclegg_x=Cyclegg_Nil
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev cyclegg_y)))
          ***
          QED
        (Cyclegg_Nil ) ->
          (cyclegg_append cyclegg_y cyclegg_x)
          -- case-split:clam_11:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil =>
          ==. (cyclegg_append Cyclegg_Nil cyclegg_x)
          -- case-split:clam_11:cyclegg_x=Cyclegg_Nil =>
          ==. (cyclegg_append Cyclegg_Nil Cyclegg_Nil)
          -- <= (cyclegg_rev Cyclegg_Nil)
          ==. (cyclegg_append Cyclegg_Nil (cyclegg_rev Cyclegg_Nil))
          -- <= case-split:clam_11:cyclegg_x=Cyclegg_Nil
          ==. (cyclegg_append Cyclegg_Nil (cyclegg_rev cyclegg_x))
          -- case-split:clam_11:cyclegg_x=Cyclegg_Nil =>
          ==. (cyclegg_append Cyclegg_Nil (cyclegg_rev Cyclegg_Nil))
          -- <= case-split:clam_11:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil
          ==. (cyclegg_append Cyclegg_Nil (cyclegg_rev cyclegg_y))
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          ==. (cyclegg_rev cyclegg_y)
          -- case-split:clam_11:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil =>
          ==. (cyclegg_rev Cyclegg_Nil)
          -- <= (cyclegg_rev Cyclegg_Nil)
          ==. (cyclegg_rev (cyclegg_rev Cyclegg_Nil))
          -- <= case-split:clam_11:cyclegg_x=Cyclegg_Nil
          ==. (cyclegg_rev (cyclegg_rev cyclegg_x))
          -- case-split:clam_11:cyclegg_x=Cyclegg_Nil =>
          ==. (cyclegg_rev (cyclegg_rev Cyclegg_Nil))
          -- <= case-split:clam_11:cyclegg_x=Cyclegg_Nil:cyclegg_y=Cyclegg_Nil
          ==. (cyclegg_rev (cyclegg_rev cyclegg_y))
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          ==. (cyclegg_rev (cyclegg_append Cyclegg_Nil (cyclegg_rev cyclegg_y)))
          -- <= (cyclegg_rev Cyclegg_Nil)
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev Cyclegg_Nil) (cyclegg_rev cyclegg_y)))
          -- <= case-split:clam_11:cyclegg_x=Cyclegg_Nil
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_x) (cyclegg_rev cyclegg_y)))
          ***
          QED


{-@ lemma_2 :: cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_append cyclegg_y Cyclegg_Nil) = cyclegg_y } @-}
lemma_2 :: (Cyclegg_List cyclegg_a) -> Proof
lemma_2 cyclegg_y =
  case cyclegg_y of
    (Cyclegg_Cons cyclegg_y_30 cyclegg_y_31) ->
      (cyclegg_append cyclegg_y Cyclegg_Nil)
      -- case-split:lemma_2:cyclegg_y=(Cyclegg_Cons cyclegg_y_30 cyclegg_y_31) =>
      ==. (cyclegg_append (Cyclegg_Cons cyclegg_y_30 cyclegg_y_31) Cyclegg_Nil)
      -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
      ==. (Cyclegg_Cons cyclegg_y_30 (cyclegg_append cyclegg_y_31 Cyclegg_Nil))
      ? lemma_2 (cyclegg_y_31)
      -- <= lemma_2-?cyclegg_y=(cyclegg_append ?cyclegg_y Cyclegg_Nil)
      ==. (Cyclegg_Cons cyclegg_y_30 cyclegg_y_31)
      -- <= case-split:lemma_2:cyclegg_y=(Cyclegg_Cons cyclegg_y_30 cyclegg_y_31)
      ==. cyclegg_y
      ***
      QED
    (Cyclegg_Nil ) ->
      (cyclegg_append cyclegg_y Cyclegg_Nil)
      -- case-split:lemma_2:cyclegg_y=Cyclegg_Nil =>
      ==. (cyclegg_append Cyclegg_Nil Cyclegg_Nil)
      -- <= case-split:lemma_2:cyclegg_y=Cyclegg_Nil
      ==. (cyclegg_append Cyclegg_Nil cyclegg_y)
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      ==. cyclegg_y
      ***
      QED


{-@ lemma_3 :: cyclegg_y: (Cyclegg_List cyclegg_a) -> { (cyclegg_rev (cyclegg_rev cyclegg_y)) = cyclegg_y } @-}
lemma_3 :: (Cyclegg_List cyclegg_a) -> Proof
lemma_3 cyclegg_y =
  case cyclegg_y of
    (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81) ->
      case cyclegg_y_81 of
        (Cyclegg_Cons cyclegg_y_81_230 cyclegg_y_81_231) ->
          case cyclegg_y_81_231 of
            (Cyclegg_Cons cyclegg_y_81_231_450 cyclegg_y_81_231_451) ->
              (cyclegg_rev (cyclegg_rev cyclegg_y))
              -- case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81) =>
              ==. (cyclegg_rev (cyclegg_rev (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)))
              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
              ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_y_81) (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil)))
              -- <= lemma_23-(Cyclegg_Cons ?cyclegg_y_80 (cyclegg_rev ?fresh_81))=(cyclegg_rev (cyclegg_append ?fresh_81 (Cyclegg_Cons ?cyclegg_y_80 Cyclegg_Nil)))
              ==. (Cyclegg_Cons cyclegg_y_80 (cyclegg_rev (cyclegg_rev cyclegg_y_81)))
              ? lemma_3 (cyclegg_y_81)
              -- <= lemma_3-?cyclegg_y=(cyclegg_rev (cyclegg_rev ?cyclegg_y))
              ==. (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)
              -- <= case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)
              ==. cyclegg_y
              ***
              QED
            (Cyclegg_Nil ) ->
              (cyclegg_rev (cyclegg_rev cyclegg_y))
              -- case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81) =>
              ==. (cyclegg_rev (cyclegg_rev (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)))
              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
              ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_y_81) (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil)))
              -- <= lemma_23-(Cyclegg_Cons ?cyclegg_y_80 (cyclegg_rev ?fresh_81))=(cyclegg_rev (cyclegg_append ?fresh_81 (Cyclegg_Cons ?cyclegg_y_80 Cyclegg_Nil)))
              ==. (Cyclegg_Cons cyclegg_y_80 (cyclegg_rev (cyclegg_rev cyclegg_y_81)))
              ? lemma_3 (cyclegg_y_81)
              -- <= lemma_3-?cyclegg_y=(cyclegg_rev (cyclegg_rev ?cyclegg_y))
              ==. (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)
              -- <= case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)
              ==. cyclegg_y
              ***
              QED
        (Cyclegg_Nil ) ->
          (cyclegg_rev (cyclegg_rev cyclegg_y))
          -- case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81) =>
          ==. (cyclegg_rev (cyclegg_rev (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)))
          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev cyclegg_y_81) (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil)))
          -- case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81):cyclegg_y_81=Cyclegg_Nil =>
          ==. (cyclegg_rev (cyclegg_append (cyclegg_rev Cyclegg_Nil) (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil)))
          -- (cyclegg_rev Cyclegg_Nil) =>
          ==. (cyclegg_rev (cyclegg_append Cyclegg_Nil (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil)))
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          ==. (cyclegg_rev (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil))
          -- <= case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81):cyclegg_y_81=Cyclegg_Nil
          ==. (cyclegg_rev (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81))
          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
          ==. (cyclegg_append (cyclegg_rev cyclegg_y_81) (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil))
          -- case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81):cyclegg_y_81=Cyclegg_Nil =>
          ==. (cyclegg_append (cyclegg_rev Cyclegg_Nil) (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil))
          -- (cyclegg_rev Cyclegg_Nil) =>
          ==. (cyclegg_append Cyclegg_Nil (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil))
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          ==. (Cyclegg_Cons cyclegg_y_80 Cyclegg_Nil)
          -- <= case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81):cyclegg_y_81=Cyclegg_Nil
          ==. (Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)
          -- <= case-split:lemma_3:cyclegg_y=(Cyclegg_Cons cyclegg_y_80 cyclegg_y_81)
          ==. cyclegg_y
          ***
          QED
    (Cyclegg_Nil ) ->
      (cyclegg_rev (cyclegg_rev cyclegg_y))
      -- case-split:lemma_3:cyclegg_y=Cyclegg_Nil =>
      ==. (cyclegg_rev (cyclegg_rev Cyclegg_Nil))
      -- (cyclegg_rev Cyclegg_Nil) =>
      ==. (cyclegg_rev Cyclegg_Nil)
      -- (cyclegg_rev Cyclegg_Nil) =>
      ==. Cyclegg_Nil
      -- <= case-split:lemma_3:cyclegg_y=Cyclegg_Nil
      ==. cyclegg_y
      ***
      QED


{-@ lemma_24 :: cyclegg_y_170: cyclegg_a -> cyclegg_y_171: (Cyclegg_List cyclegg_a) -> fresh_31: (Cyclegg_List cyclegg_a) -> { (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_rev cyclegg_y_171)))) = (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))) } @-}
lemma_24 :: cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
lemma_24 cyclegg_y_170 cyclegg_y_171 fresh_31 =
  case cyclegg_y_171 of
    (Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481) ->
      case fresh_31 of
        (Cyclegg_Cons fresh_31_870 fresh_31_871) ->
          (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_rev cyclegg_y_171))))
          -- case-split:lemma_24:cyclegg_y_171=(Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481):fresh_31=(Cyclegg_Cons fresh_31_870 fresh_31_871) =>
          ==. (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (cyclegg_append (Cyclegg_Cons fresh_31_870 fresh_31_871) (cyclegg_rev cyclegg_y_171))))
          -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
          ==. (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (Cyclegg_Cons fresh_31_870 (cyclegg_append fresh_31_871 (cyclegg_rev cyclegg_y_171)))))
          -- case-split:lemma_24:cyclegg_y_171=(Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481) =>
          ==. (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (Cyclegg_Cons fresh_31_870 (cyclegg_append fresh_31_871 (cyclegg_rev (Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481))))))
          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
          ==. (Cyclegg_Cons cyclegg_y_170 (cyclegg_append (cyclegg_rev (cyclegg_append fresh_31_871 (cyclegg_rev (Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481)))) (Cyclegg_Cons fresh_31_870 Cyclegg_Nil)))
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          ==. (cyclegg_append (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (cyclegg_append fresh_31_871 (cyclegg_rev (Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481))))) (Cyclegg_Cons fresh_31_870 Cyclegg_Nil))
          -- lemma_23-(Cyclegg_Cons ?cyclegg_y_80 (cyclegg_rev ?fresh_81))=(cyclegg_rev (cyclegg_append ?fresh_81 (Cyclegg_Cons ?cyclegg_y_80 Cyclegg_Nil))) =>
          ==. (cyclegg_append (cyclegg_rev (cyclegg_append (cyclegg_append fresh_31_871 (cyclegg_rev (Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481))) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))) (Cyclegg_Cons fresh_31_870 Cyclegg_Nil))
          -- <= case-split:lemma_24:cyclegg_y_171=(Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481)
          ==. (cyclegg_append (cyclegg_rev (cyclegg_append (cyclegg_append fresh_31_871 (cyclegg_rev cyclegg_y_171)) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))) (Cyclegg_Cons fresh_31_870 Cyclegg_Nil))
          -- lemma_29-(cyclegg_append (cyclegg_append ?fresh_31 ?fresh_48) (Cyclegg_Cons ?cyclegg_y_170 Cyclegg_Nil))=(cyclegg_append ?fresh_31 (cyclegg_append ?fresh_48 (Cyclegg_Cons ?cyclegg_y_170 Cyclegg_Nil))) =>
          ==. (cyclegg_append (cyclegg_rev (cyclegg_append fresh_31_871 (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))) (Cyclegg_Cons fresh_31_870 Cyclegg_Nil))
          -- case-split:lemma_24:cyclegg_y_171=(Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481) =>
          ==. (cyclegg_append (cyclegg_rev (cyclegg_append fresh_31_871 (cyclegg_append (cyclegg_rev (Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481)) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))) (Cyclegg_Cons fresh_31_870 Cyclegg_Nil))
          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
          ==. (cyclegg_rev (Cyclegg_Cons fresh_31_870 (cyclegg_append fresh_31_871 (cyclegg_append (cyclegg_rev (Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481)) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))))
          -- <= case-split:lemma_24:cyclegg_y_171=(Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481)
          ==. (cyclegg_rev (Cyclegg_Cons fresh_31_870 (cyclegg_append fresh_31_871 (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))))
          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
          ==. (cyclegg_rev (cyclegg_append (Cyclegg_Cons fresh_31_870 fresh_31_871) (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))))
          -- <= case-split:lemma_24:cyclegg_y_171=(Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481):fresh_31=(Cyclegg_Cons fresh_31_870 fresh_31_871)
          ==. (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))))
          ***
          QED
        (Cyclegg_Nil ) ->
          (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_rev cyclegg_y_171))))
          -- lemma_23-(Cyclegg_Cons ?cyclegg_y_80 (cyclegg_rev ?fresh_81))=(cyclegg_rev (cyclegg_append ?fresh_81 (Cyclegg_Cons ?cyclegg_y_80 Cyclegg_Nil))) =>
          ==. (cyclegg_rev (cyclegg_append (cyclegg_append fresh_31 (cyclegg_rev cyclegg_y_171)) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))
          -- case-split:lemma_24:cyclegg_y_171=(Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481):fresh_31=Cyclegg_Nil =>
          ==. (cyclegg_rev (cyclegg_append (cyclegg_append Cyclegg_Nil (cyclegg_rev cyclegg_y_171)) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))
          -- lemma_29-(cyclegg_append (cyclegg_append ?fresh_31 ?fresh_48) (Cyclegg_Cons ?cyclegg_y_170 Cyclegg_Nil))=(cyclegg_append ?fresh_31 (cyclegg_append ?fresh_48 (Cyclegg_Cons ?cyclegg_y_170 Cyclegg_Nil))) =>
          ==. (cyclegg_rev (cyclegg_append Cyclegg_Nil (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))))
          -- <= case-split:lemma_24:cyclegg_y_171=(Cyclegg_Cons cyclegg_y_171_480 cyclegg_y_171_481):fresh_31=Cyclegg_Nil
          ==. (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))))
          ***
          QED
    (Cyclegg_Nil ) ->
      (Cyclegg_Cons cyclegg_y_170 (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_rev cyclegg_y_171))))
      -- lemma_23-(Cyclegg_Cons ?cyclegg_y_80 (cyclegg_rev ?fresh_81))=(cyclegg_rev (cyclegg_append ?fresh_81 (Cyclegg_Cons ?cyclegg_y_80 Cyclegg_Nil))) =>
      ==. (cyclegg_rev (cyclegg_append (cyclegg_append fresh_31 (cyclegg_rev cyclegg_y_171)) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))
      -- case-split:lemma_24:cyclegg_y_171=Cyclegg_Nil =>
      ==. (cyclegg_rev (cyclegg_append (cyclegg_append fresh_31 (cyclegg_rev Cyclegg_Nil)) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))
      -- (cyclegg_rev Cyclegg_Nil) =>
      ==. (cyclegg_rev (cyclegg_append (cyclegg_append fresh_31 Cyclegg_Nil) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))
      ? lemma_2 (fresh_31)
      -- <= lemma_2-?cyclegg_y=(cyclegg_append ?cyclegg_y Cyclegg_Nil)
      ==. (cyclegg_rev (cyclegg_append fresh_31 (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil)))
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      ==. (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_append Cyclegg_Nil (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))))
      -- <= (cyclegg_rev Cyclegg_Nil)
      ==. (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_append (cyclegg_rev Cyclegg_Nil) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))))
      -- <= case-split:lemma_24:cyclegg_y_171=Cyclegg_Nil
      ==. (cyclegg_rev (cyclegg_append fresh_31 (cyclegg_append (cyclegg_rev cyclegg_y_171) (Cyclegg_Cons cyclegg_y_170 Cyclegg_Nil))))
      ***
      QED


