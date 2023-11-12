{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_78: (cyclegg_add (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_m Cyclegg_Nil))) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_m cyclegg_xs))
module Goal78 where
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

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ goal_78 :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_add (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_m Cyclegg_Nil))) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_m cyclegg_xs)) } @-}
goal_78 :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
goal_78 cyclegg_n cyclegg_m cyclegg_xs =
  let g_10 = (cyclegg_eq cyclegg_n cyclegg_m) in
    case g_10 of
      (Cyclegg_False ) ->
        case cyclegg_n of
          (Cyclegg_S cyclegg_n_200) ->
            let g_27 = (cyclegg_eq cyclegg_n_200 cyclegg_m) in
              case g_27 of
                (Cyclegg_False ) ->
                  case cyclegg_m of
                    (Cyclegg_S cyclegg_m_370) ->
                      let g_50 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) in
                        case g_50 of
                          (Cyclegg_False ) ->
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                            -- case-split:goal_78:g_10=Cyclegg_False =>
                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False
                            -- <= adding scrutinee g_50 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370)
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                            goal_78 (cyclegg_n) (cyclegg_m_370) (cyclegg_xs)
                            -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- adding scrutinee g_50 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) =>
                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False =>
                            -- <= case-split:goal_78:g_10=Cyclegg_False
                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          (Cyclegg_True ) ->
                            case cyclegg_xs of
                              (Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) ->
                                let g_79 = (cyclegg_eq cyclegg_n_200 cyclegg_xs_560) in
                                  case g_79 of
                                    (Cyclegg_False ) ->
                                      let g_92 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) in
                                        case g_92 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- adding scrutinee g_92 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_79=Cyclegg_False:g_92=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                            goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_561)
                                            -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False =>
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_79=Cyclegg_False:g_92=Cyclegg_False
                                            -- <= adding scrutinee g_92 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False
                                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- adding scrutinee g_92 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_79=Cyclegg_False:g_92=Cyclegg_True =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False
                                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_561)
                                            -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_79=Cyclegg_False:g_92=Cyclegg_True
                                            -- <= adding scrutinee g_92 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False
                                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      let g_92 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) in
                                        case g_92 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- adding scrutinee g_92 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_79=Cyclegg_True:g_92=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                            goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_561)
                                            -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False =>
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_79=Cyclegg_True:g_92=Cyclegg_False
                                            -- <= adding scrutinee g_92 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False
                                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- adding scrutinee g_92 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_79=Cyclegg_True:g_92=Cyclegg_True =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False
                                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_561)
                                            -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_79=Cyclegg_True:g_92=Cyclegg_True
                                            -- <= adding scrutinee g_92 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= case-split:goal_78:g_10=Cyclegg_False
                                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_Nil ) ->
                                -- <= constructor-injective (Cyclegg_S Cyclegg_Z) = (Cyclegg_S (cyclegg_count (Cyclegg_S cyclegg_n_200) Cyclegg_Nil))
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=Cyclegg_Nil
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370) =>
                                -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                goal_78 (cyclegg_n_200) (cyclegg_m_370) (cyclegg_xs)
                                -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- <= (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True:cyclegg_xs=Cyclegg_Nil
                    (Cyclegg_Z ) ->
                      case cyclegg_xs of
                        (Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) ->
                          let g_49 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) in
                            case g_49 of
                              (Cyclegg_False ) ->
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- adding scrutinee g_49 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_49=Cyclegg_False =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                goal_78 (cyclegg_n) ((cyclegg_count cyclegg_n Cyclegg_Nil)) (cyclegg_xs_411)
                                -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_49=Cyclegg_False
                                -- <= adding scrutinee g_49 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_True ) ->
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- adding scrutinee g_49 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_49=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                goal_78 (cyclegg_n) ((cyclegg_count cyclegg_n Cyclegg_Nil)) (cyclegg_xs_411)
                                -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z
                                -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_False =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_49=Cyclegg_True
                                -- <= adding scrutinee g_49 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_Nil ) ->
                          -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                          -- case-split:goal_78:g_10=Cyclegg_False =>
                          -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False
                          -- <= adding scrutinee g_27 to split condition (cyclegg_eq cyclegg_n_200 cyclegg_m)
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          goal_78 (cyclegg_n_200) (cyclegg_m) (cyclegg_xs)
                          -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- adding scrutinee g_27 to split condition (cyclegg_eq cyclegg_n_200 cyclegg_m) =>
                          -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= case-split:goal_78:g_10=Cyclegg_False
                          -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                (Cyclegg_True ) ->
                  case cyclegg_m of
                    (Cyclegg_S cyclegg_m_370) ->
                      let g_48 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) in
                        case g_48 of
                          (Cyclegg_False ) ->
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                            -- case-split:goal_78:g_10=Cyclegg_False =>
                            -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_False
                            -- <= adding scrutinee g_48 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370)
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                            goal_78 (cyclegg_n) (cyclegg_m_370) (cyclegg_xs)
                            -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- adding scrutinee g_48 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) =>
                            -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_False =>
                            -- <= case-split:goal_78:g_10=Cyclegg_False
                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          (Cyclegg_True ) ->
                            case cyclegg_xs of
                              (Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) ->
                                let g_84 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580) in
                                  case g_84 of
                                    (Cyclegg_False ) ->
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- adding scrutinee g_84 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_84=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_581)
                                      -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_84=Cyclegg_False
                                      -- <= adding scrutinee g_84 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_False
                                      -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_84 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_84=Cyclegg_True =>
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_False
                                      -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_581)
                                      -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False =>
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_84=Cyclegg_True
                                      -- <= adding scrutinee g_84 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580)
                                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_False
                                      -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_Nil ) ->
                                -- <= constructor-injective (Cyclegg_S Cyclegg_Z) = (Cyclegg_S (cyclegg_count (Cyclegg_S cyclegg_n_200) Cyclegg_Nil))
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=Cyclegg_Nil
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370) =>
                                -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                goal_78 (cyclegg_n_200) (cyclegg_m_370) (cyclegg_xs)
                                -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_48=Cyclegg_True:cyclegg_xs=Cyclegg_Nil
                    (Cyclegg_Z ) ->
                      case cyclegg_xs of
                        (Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) ->
                          let g_57 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) in
                            case g_57 of
                              (Cyclegg_False ) ->
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- adding scrutinee g_57 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_57=Cyclegg_False =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                goal_78 (cyclegg_n) ((cyclegg_count cyclegg_n Cyclegg_Nil)) (cyclegg_xs_411)
                                -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_57=Cyclegg_False
                                -- <= adding scrutinee g_57 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_True ) ->
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- adding scrutinee g_57 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_57=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                goal_78 (cyclegg_n) ((cyclegg_count cyclegg_n Cyclegg_Nil)) (cyclegg_xs_411)
                                -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z
                                -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_False =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_57=Cyclegg_True
                                -- <= adding scrutinee g_57 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_Nil ) ->
                          -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                          -- case-split:goal_78:g_10=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          -- (cyclegg_add Cyclegg_Z ?y) =>
                          -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= case-split:goal_78:g_10=Cyclegg_False
                          -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          ()
          (Cyclegg_Z ) ->
            case cyclegg_m of
              (Cyclegg_S cyclegg_m_230) ->
                let g_29 = (cyclegg_eq Cyclegg_Z cyclegg_m_230) in
                  case g_29 of
                    (Cyclegg_False ) ->
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                      -- case-split:goal_78:g_10=Cyclegg_False =>
                      -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_False
                      -- <= adding scrutinee g_29 to split condition (cyclegg_eq Cyclegg_Z cyclegg_m_230)
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      goal_78 (cyclegg_n) (cyclegg_m_230) (cyclegg_xs)
                      -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- adding scrutinee g_29 to split condition (cyclegg_eq Cyclegg_Z cyclegg_m_230) =>
                      -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_False =>
                      -- <= case-split:goal_78:g_10=Cyclegg_False
                      -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                    (Cyclegg_True ) ->
                      case cyclegg_xs of
                        (Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361) ->
                          let g_64 = (cyclegg_eq Cyclegg_Z cyclegg_xs_360) in
                            case g_64 of
                              (Cyclegg_False ) ->
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                                -- adding scrutinee g_64 to split condition (cyclegg_eq Cyclegg_Z cyclegg_xs_360) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361):g_64=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                                goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_361)
                                -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_False =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361):g_64=Cyclegg_False
                                -- <= adding scrutinee g_64 to split condition (cyclegg_eq Cyclegg_Z cyclegg_xs_360)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_True ) ->
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                                -- adding scrutinee g_64 to split condition (cyclegg_eq Cyclegg_Z cyclegg_xs_360) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361):g_64=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                                -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_361)
                                -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                                -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                                -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361):g_64=Cyclegg_True
                                -- <= adding scrutinee g_64 to split condition (cyclegg_eq Cyclegg_Z cyclegg_xs_360)
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_29=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_False
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_Nil ) ->
                          -- <= constructor-injective (Cyclegg_S Cyclegg_Z) = (Cyclegg_S (cyclegg_count Cyclegg_Z Cyclegg_Nil))
                          -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                          -- case-split:goal_78:g_10=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                          -- (cyclegg_add Cyclegg_Z ?y) =>
                          -- constructor-injective (Cyclegg_S Cyclegg_Z) = (Cyclegg_S (cyclegg_count Cyclegg_Z Cyclegg_Nil)) =>
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= case-split:goal_78:g_10=Cyclegg_False
                          -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          ()
              (Cyclegg_Z ) ->
                unreachable (
                  -- <= case-split:goal_78:g_10=Cyclegg_False
                  -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                  -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                  -- case-split:goal_78:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z =>
                  -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                  ()
                )

      (Cyclegg_True ) ->
        case cyclegg_n of
          (Cyclegg_S cyclegg_n_200) ->
            let g_27 = (cyclegg_eq cyclegg_n_200 cyclegg_m) in
              case g_27 of
                (Cyclegg_False ) ->
                  case cyclegg_m of
                    (Cyclegg_S cyclegg_m_370) ->
                      let g_50 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) in
                        case g_50 of
                          (Cyclegg_False ) ->
                            case cyclegg_xs of
                              (Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) ->
                                let g_98 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580) in
                                  case g_98 of
                                    (Cyclegg_False ) ->
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_98 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_98=Cyclegg_False =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_581)
                                      -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_98=Cyclegg_False
                                      -- <= adding scrutinee g_98 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581)
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True
                                      -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_98 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_98=Cyclegg_True =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_581)
                                      -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_98=Cyclegg_True
                                      -- <= adding scrutinee g_98 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581)
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True
                                      -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_Nil ) ->
                                -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- constructor-injective (Cyclegg_S Cyclegg_Z) = (Cyclegg_S (cyclegg_count cyclegg_n_200 Cyclegg_Nil)) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370) =>
                                -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                goal_78 (cyclegg_n_200) (cyclegg_m_370) (cyclegg_xs)
                                -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                                -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- <= (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y))
                                -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_False:cyclegg_xs=Cyclegg_Nil
                          (Cyclegg_True ) ->
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                            -- case-split:goal_78:g_10=Cyclegg_True =>
                            -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True
                            -- <= adding scrutinee g_50 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370)
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                            goal_78 (cyclegg_n) (cyclegg_m_370) (cyclegg_xs)
                            -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- adding scrutinee g_50 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) =>
                            -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_50=Cyclegg_True =>
                            -- <= case-split:goal_78:g_10=Cyclegg_True
                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                    (Cyclegg_Z ) ->
                      unreachable (
                        -- <= (cyclegg_count ?x Cyclegg_Nil)
                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                        -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                        -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z
                        -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                        -- case-split:goal_78:g_10=Cyclegg_True =>
                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                        -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                        -- case-split:goal_78:g_10=Cyclegg_True =>
                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                        -- (cyclegg_count ?x Cyclegg_Nil) =>
                        -- <= (cyclegg_count ?x Cyclegg_Nil)
                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                        -- (cyclegg_count ?x Cyclegg_Nil) =>
                        ()
                      )

                (Cyclegg_True ) ->
                  case cyclegg_m of
                    (Cyclegg_S cyclegg_m_370) ->
                      let g_51 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) in
                        case g_51 of
                          (Cyclegg_False ) ->
                            case cyclegg_xs of
                              (Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) ->
                                let g_94 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) in
                                  case g_94 of
                                    (Cyclegg_False ) ->
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_94 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_94=Cyclegg_False =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_561)
                                      -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_94=Cyclegg_False
                                      -- <= adding scrutinee g_94 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True
                                      -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- adding scrutinee g_94 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_94=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      goal_78 (cyclegg_n) (cyclegg_m) (cyclegg_xs_561)
                                      -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                      -- case-split:goal_78:g_10=Cyclegg_True =>
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_94=Cyclegg_True
                                      -- <= adding scrutinee g_94 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= case-split:goal_78:g_10=Cyclegg_True
                                      -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_Nil ) ->
                                -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- constructor-injective (Cyclegg_S Cyclegg_Z) = (Cyclegg_S (cyclegg_count cyclegg_n_200 Cyclegg_Nil)) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_True =>
                                -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True
                                -- <= adding scrutinee g_27 to split condition (cyclegg_eq cyclegg_n_200 cyclegg_m)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                goal_78 (cyclegg_n_200) (cyclegg_m) (cyclegg_xs)
                                -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                                -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- adding scrutinee g_27 to split condition (cyclegg_eq cyclegg_n_200 cyclegg_m) =>
                                -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                -- <= case-split:goal_78:g_10=Cyclegg_True
                                -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False:cyclegg_xs=Cyclegg_Nil
                          (Cyclegg_True ) ->
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                            -- case-split:goal_78:g_10=Cyclegg_True =>
                            -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True
                            -- <= adding scrutinee g_51 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370)
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                            goal_78 (cyclegg_n) (cyclegg_m_370) (cyclegg_xs)
                            -- goal_78-(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))=(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs)) =>
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- adding scrutinee g_51 to split condition (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) =>
                            -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True =>
                            -- <= case-split:goal_78:g_10=Cyclegg_True
                            -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                    (Cyclegg_Z ) ->
                      unreachable (
                        -- <= case-split:goal_78:g_10=Cyclegg_True
                        -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                        -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                        -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                        -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                        ()
                      )

          (Cyclegg_Z ) ->
            case cyclegg_m of
              (Cyclegg_S cyclegg_m_220) ->
                unreachable (
                  -- <= case-split:goal_78:g_10=Cyclegg_True
                  -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                  -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                  -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_220) =>
                  -- (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y)) =>
                  ()
                )

              (Cyclegg_Z ) ->
                case cyclegg_xs of
                  (Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251) ->
                    let g_39 = (cyclegg_eq Cyclegg_Z cyclegg_xs_250) in
                      case g_39 of
                        (Cyclegg_False ) ->
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- adding scrutinee g_39 to split condition (cyclegg_eq Cyclegg_Z cyclegg_xs_250) =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_39=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z =>
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                          goal_78 (cyclegg_n) (cyclegg_n) (cyclegg_xs_251)
                          -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_39=Cyclegg_False
                          -- <= adding scrutinee g_39 to split condition (cyclegg_eq Cyclegg_Z cyclegg_xs_250)
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251)
                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                          -- <= case-split:goal_78:g_10=Cyclegg_True
                          -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_True ) ->
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- adding scrutinee g_39 to split condition (cyclegg_eq Cyclegg_Z cyclegg_xs_250) =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_39=Cyclegg_True =>
                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                          -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z =>
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                          goal_78 (cyclegg_n) (cyclegg_n) (cyclegg_xs_251)
                          -- <= goal_78-(cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m ?cyclegg_xs))=(cyclegg_add (cyclegg_count ?cyclegg_n ?cyclegg_xs) (cyclegg_count ?cyclegg_n (Cyclegg_Cons ?cyclegg_m Cyclegg_Nil)))
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z
                          -- adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m) =>
                          -- case-split:goal_78:g_10=Cyclegg_True =>
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_39=Cyclegg_True
                          -- <= adding scrutinee g_39 to split condition (cyclegg_eq Cyclegg_Z cyclegg_xs_250)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251)
                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                          -- <= case-split:goal_78:g_10=Cyclegg_True
                          -- <= adding scrutinee g_10 to split condition (cyclegg_eq cyclegg_n cyclegg_m)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                  (Cyclegg_Nil ) ->
                    -- case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                    -- (cyclegg_count ?x Cyclegg_Nil) =>
                    -- (cyclegg_add Cyclegg_Z ?y) =>
                    -- <= case-split:goal_78:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                    ()


