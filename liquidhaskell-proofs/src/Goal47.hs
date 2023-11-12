{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_47: (cyclegg_height (cyclegg_mirror cyclegg_t)) = (cyclegg_height cyclegg_t)
module Goal47 where
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

{-@ reflect cyclegg_mirror @-}
cyclegg_mirror :: ((Cyclegg_Tree cyclegg_a) -> (Cyclegg_Tree cyclegg_a))
cyclegg_mirror Cyclegg_Leaf = Cyclegg_Leaf
cyclegg_mirror (Cyclegg_Node l x r) = (Cyclegg_Node (cyclegg_mirror r) x (cyclegg_mirror l))

{-@ reflect cyclegg_height @-}
cyclegg_height :: ((Cyclegg_Tree cyclegg_a) -> Cyclegg_Nat)
cyclegg_height Cyclegg_Leaf = Cyclegg_Z
cyclegg_height (Cyclegg_Node l x r) = (Cyclegg_S (cyclegg_max (cyclegg_height l) (cyclegg_height r)))

{-@ reflect cyclegg_max @-}
cyclegg_max :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_max Cyclegg_Z y = y
cyclegg_max x Cyclegg_Z = x
cyclegg_max (Cyclegg_S x) (Cyclegg_S y) = (Cyclegg_S (cyclegg_max x y))

{-@ goal_47 :: cyclegg_t: (Cyclegg_Tree cyclegg_a) -> { (cyclegg_height (cyclegg_mirror cyclegg_t)) = (cyclegg_height cyclegg_t) } @-}
goal_47 :: (Cyclegg_Tree cyclegg_a) -> Proof
goal_47 cyclegg_t =
  case cyclegg_t of
    (Cyclegg_Node cyclegg_t_40 cyclegg_t_41 cyclegg_t_42) ->
      -- case-split:goal_47:cyclegg_t=(Cyclegg_Node cyclegg_t_40 cyclegg_t_41 cyclegg_t_42) =>
      -- (cyclegg_mirror (Cyclegg_Node ?l ?x ?r)) =>
      -- (cyclegg_height (Cyclegg_Node ?l ?x ?r)) =>
      goal_47 (cyclegg_t_42)
      -- <= goal_47-(cyclegg_height ?cyclegg_t)=(cyclegg_height (cyclegg_mirror ?cyclegg_t))
      ? goal_47 (cyclegg_t_40)
      -- <= goal_47-(cyclegg_height ?cyclegg_t)=(cyclegg_height (cyclegg_mirror ?cyclegg_t))
      ? lemma_20 ((cyclegg_height cyclegg_t_40)) ((cyclegg_height cyclegg_t_42))
      -- <= lemma_20-(Cyclegg_S (cyclegg_max ?fresh_19 ?fresh_7))=(Cyclegg_S (cyclegg_max ?fresh_7 ?fresh_19))
      -- <= (cyclegg_height (Cyclegg_Node ?l ?x ?r))
      -- <= case-split:goal_47:cyclegg_t=(Cyclegg_Node cyclegg_t_40 cyclegg_t_41 cyclegg_t_42)
    (Cyclegg_Leaf ) ->
      -- case-split:goal_47:cyclegg_t=Cyclegg_Leaf =>
      -- (cyclegg_mirror Cyclegg_Leaf) =>
      -- <= case-split:goal_47:cyclegg_t=Cyclegg_Leaf
      ()


{-@ lemma_20 :: fresh_19: Cyclegg_Nat -> fresh_7: Cyclegg_Nat -> { (Cyclegg_S (cyclegg_max fresh_19 fresh_7)) = (Cyclegg_S (cyclegg_max fresh_7 fresh_19)) } @-}
lemma_20 :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
lemma_20 fresh_19 fresh_7 =
  case fresh_19 of
    (Cyclegg_S fresh_19_60) ->
      case fresh_7 of
        (Cyclegg_S fresh_7_120) ->
          -- case-split:lemma_20:fresh_19=(Cyclegg_S fresh_19_60) =>
          -- case-split:lemma_20:fresh_19=(Cyclegg_S fresh_19_60):fresh_7=(Cyclegg_S fresh_7_120) =>
          -- (cyclegg_max (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          lemma_20 (fresh_19_60) (fresh_7_120)
          -- lemma_20-(Cyclegg_S (cyclegg_max ?fresh_19 ?fresh_7))=(Cyclegg_S (cyclegg_max ?fresh_7 ?fresh_19)) =>
          -- <= (cyclegg_max (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= case-split:lemma_20:fresh_19=(Cyclegg_S fresh_19_60):fresh_7=(Cyclegg_S fresh_7_120)
          -- <= case-split:lemma_20:fresh_19=(Cyclegg_S fresh_19_60)
        (Cyclegg_Z ) ->
          -- case-split:lemma_20:fresh_19=(Cyclegg_S fresh_19_60):fresh_7=Cyclegg_Z =>
          -- (cyclegg_max ?x Cyclegg_Z) =>
          -- <= (cyclegg_max Cyclegg_Z ?y)
          -- <= case-split:lemma_20:fresh_19=(Cyclegg_S fresh_19_60):fresh_7=Cyclegg_Z
          ()
    (Cyclegg_Z ) ->
      -- case-split:lemma_20:fresh_19=Cyclegg_Z =>
      -- (cyclegg_max Cyclegg_Z ?y) =>
      -- <= (cyclegg_max ?x Cyclegg_Z)
      -- <= case-split:lemma_20:fresh_19=Cyclegg_Z
      ()


{-@ lemma_16 :: fresh_19: Cyclegg_Nat -> cyclegg_t_42: (Cyclegg_Tree cyclegg_a) -> { (Cyclegg_S (cyclegg_max (cyclegg_height cyclegg_t_42) fresh_19)) = (Cyclegg_S (cyclegg_max fresh_19 (cyclegg_height cyclegg_t_42))) } @-}
lemma_16 :: Cyclegg_Nat -> (Cyclegg_Tree cyclegg_a) -> Proof
lemma_16 fresh_19 cyclegg_t_42 =
  case fresh_19 of
    (Cyclegg_S fresh_19_70) ->
      case cyclegg_t_42 of
        (Cyclegg_Node cyclegg_t_42_130 cyclegg_t_42_131 cyclegg_t_42_132) ->
          -- case-split:lemma_16:fresh_19=(Cyclegg_S fresh_19_70):cyclegg_t_42=(Cyclegg_Node cyclegg_t_42_130 cyclegg_t_42_131 cyclegg_t_42_132) =>
          -- (cyclegg_height (Cyclegg_Node ?l ?x ?r)) =>
          -- case-split:lemma_16:fresh_19=(Cyclegg_S fresh_19_70) =>
          -- (cyclegg_max (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          lemma_20 (fresh_19_70) ((cyclegg_max (cyclegg_height cyclegg_t_42_130) (cyclegg_height cyclegg_t_42_132)))
          -- <= lemma_20-(Cyclegg_S (cyclegg_max ?fresh_19 ?fresh_7))=(Cyclegg_S (cyclegg_max ?fresh_7 ?fresh_19))
          -- <= (cyclegg_max (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= case-split:lemma_16:fresh_19=(Cyclegg_S fresh_19_70)
          -- <= (cyclegg_height (Cyclegg_Node ?l ?x ?r))
          -- <= case-split:lemma_16:fresh_19=(Cyclegg_S fresh_19_70):cyclegg_t_42=(Cyclegg_Node cyclegg_t_42_130 cyclegg_t_42_131 cyclegg_t_42_132)
        (Cyclegg_Leaf ) ->
          lemma_20 ((cyclegg_height cyclegg_t_42)) (fresh_19)
          -- lemma_20-(Cyclegg_S (cyclegg_max ?fresh_19 ?fresh_7))=(Cyclegg_S (cyclegg_max ?fresh_7 ?fresh_19)) =>
    (Cyclegg_Z ) ->
      -- case-split:lemma_16:fresh_19=Cyclegg_Z =>
      -- (cyclegg_max ?x Cyclegg_Z) =>
      -- <= (cyclegg_max Cyclegg_Z ?y)
      -- <= case-split:lemma_16:fresh_19=Cyclegg_Z
      ()


