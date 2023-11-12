{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- goal_73: (cyclegg_elem cyclegg_x (cyclegg_ins cyclegg_y cyclegg_xs)) = (cyclegg_elem cyclegg_x cyclegg_xs)
module Goal73 where
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

{-@ reflect cyclegg_ins @-}
cyclegg_ins :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_ins n Cyclegg_Nil = (Cyclegg_Cons n Cyclegg_Nil)
cyclegg_ins n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_lt n x) (Cyclegg_Cons n (Cyclegg_Cons x xs)) (Cyclegg_Cons x (cyclegg_ins n xs)))

{-@ reflect cyclegg_lt @-}
cyclegg_lt :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_lt x Cyclegg_Z = Cyclegg_False
cyclegg_lt Cyclegg_Z (Cyclegg_S y) = Cyclegg_True
cyclegg_lt (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_lt x y)

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_elem @-}
cyclegg_elem :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Bool)
cyclegg_elem n Cyclegg_Nil = Cyclegg_False
cyclegg_elem n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) Cyclegg_True (cyclegg_elem n xs))

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ goal_73 :: cyclegg_x: Cyclegg_Nat -> cyclegg_y: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_elem cyclegg_x (cyclegg_ins cyclegg_y cyclegg_xs)) = (cyclegg_elem cyclegg_x cyclegg_xs) } @-}
goal_73 :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
goal_73 cyclegg_x cyclegg_y cyclegg_xs =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_80) ->
      case cyclegg_y of
        (Cyclegg_S cyclegg_y_130) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) ->
              let g_43 = (cyclegg_lt cyclegg_y_130 cyclegg_xs_200) in
                case g_43 of
                  (Cyclegg_False ) ->
                    let g_34 = (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) in
                      case g_34 of
                        (Cyclegg_False ) ->
                          let g_40 = (cyclegg_eq cyclegg_x_80 cyclegg_xs_200) in
                            case g_40 of
                              (Cyclegg_False ) ->
                                let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                  case g_50 of
                                    (Cyclegg_False ) ->
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                      -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_False:g_40=Cyclegg_False:g_50=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                      goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                      -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                      -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                    (Cyclegg_True ) ->
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                      -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_False:g_40=Cyclegg_False:g_50=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_False
                                      -- <= adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                      -- adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                      -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      ()
                              (Cyclegg_True ) ->
                                let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                  case g_50 of
                                    (Cyclegg_False ) ->
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                      -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_False:g_40=Cyclegg_True:g_50=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                      goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                      -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                      -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                    (Cyclegg_True ) ->
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                      -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_False:g_40=Cyclegg_True:g_50=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_False
                                      -- <= adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                      -- adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                      -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      ()
                        (Cyclegg_True ) ->
                          let g_40 = (cyclegg_eq cyclegg_x_80 cyclegg_xs_200) in
                            case g_40 of
                              (Cyclegg_False ) ->
                                let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                  case g_50 of
                                    (Cyclegg_False ) ->
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                      -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_True:g_40=Cyclegg_False:g_50=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                      goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                      -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                      -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                    (Cyclegg_True ) ->
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                      -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_True:g_40=Cyclegg_False:g_50=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                      -- adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_True
                                      -- <= adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200)
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                      -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      ()
                              (Cyclegg_True ) ->
                                let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                  case g_50 of
                                    (Cyclegg_False ) ->
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                      -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_True:g_40=Cyclegg_True:g_50=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                      goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                      -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                      -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                    (Cyclegg_True ) ->
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                      -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_True:g_40=Cyclegg_True:g_50=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                      -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                      -- adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) =>
                                      -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_False:g_34=Cyclegg_True
                                      -- <= adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200)
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                      -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                      -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                      ()
                  (Cyclegg_True ) ->
                    let g_17 = (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_y_130) in
                      case g_17 of
                        (Cyclegg_False ) ->
                          let g_34 = (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) in
                            case g_34 of
                              (Cyclegg_False ) ->
                                let g_40 = (cyclegg_eq cyclegg_x_80 cyclegg_xs_200) in
                                  case g_40 of
                                    (Cyclegg_False ) ->
                                      let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                        case g_50 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_False:g_34=Cyclegg_False:g_40=Cyclegg_False:g_50=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                            goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_False:g_34=Cyclegg_False:g_40=Cyclegg_False:g_50=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            ()
                                    (Cyclegg_True ) ->
                                      let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                        case g_50 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_False:g_34=Cyclegg_False:g_40=Cyclegg_True:g_50=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                            goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_False:g_34=Cyclegg_False:g_40=Cyclegg_True:g_50=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            ()
                              (Cyclegg_True ) ->
                                let g_40 = (cyclegg_eq cyclegg_x_80 cyclegg_xs_200) in
                                  case g_40 of
                                    (Cyclegg_False ) ->
                                      let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                        case g_50 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_False:g_34=Cyclegg_True:g_40=Cyclegg_False:g_50=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                            goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_False:g_34=Cyclegg_True:g_40=Cyclegg_False:g_50=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            ()
                                    (Cyclegg_True ) ->
                                      let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                        case g_50 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_False:g_34=Cyclegg_True:g_40=Cyclegg_True:g_50=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                            goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_False:g_34=Cyclegg_True:g_40=Cyclegg_True:g_50=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            ()
                        (Cyclegg_True ) ->
                          let g_34 = (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) in
                            case g_34 of
                              (Cyclegg_False ) ->
                                let g_40 = (cyclegg_eq cyclegg_x_80 cyclegg_xs_200) in
                                  case g_40 of
                                    (Cyclegg_False ) ->
                                      let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                        case g_50 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_False:g_40=Cyclegg_False:g_50=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                            goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_False:g_40=Cyclegg_False:g_50=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_False
                                            -- <= adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                            -- adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            ()
                                    (Cyclegg_True ) ->
                                      let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                        case g_50 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_False:g_40=Cyclegg_True:g_50=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                            goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_False:g_40=Cyclegg_True:g_50=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_False
                                            -- <= adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                            -- adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            ()
                              (Cyclegg_True ) ->
                                let g_40 = (cyclegg_eq cyclegg_x_80 cyclegg_xs_200) in
                                  case g_40 of
                                    (Cyclegg_False ) ->
                                      let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                        case g_50 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True:g_40=Cyclegg_False:g_50=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                            goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True:g_40=Cyclegg_False:g_50=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                            -- adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True
                                            -- <= adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200)
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            ()
                                    (Cyclegg_True ) ->
                                      let g_50 = (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) in
                                        case g_50 of
                                          (Cyclegg_False ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True:g_40=Cyclegg_True:g_50=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130)
                                            goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_201)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                          (Cyclegg_True ) ->
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
                                            -- adding scrutinee g_50 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_130) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True:g_40=Cyclegg_True:g_50=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                            -- adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True:g_40=Cyclegg_True
                                            -- <= adding scrutinee g_40 to split condition (cyclegg_eq cyclegg_x_80 cyclegg_xs_200)
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                                            goal_73 (cyclegg_x_80) (cyclegg_y_130) (cyclegg_xs)
                                            -- <= goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs)
                                            -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            ? goal_73 (cyclegg_x_80) (cyclegg_y_130) (cyclegg_xs)
                                            -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                            -- adding scrutinee g_40 to split condition (cyclegg_eq cyclegg_x_80 cyclegg_xs_200) =>
                                            -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True:g_40=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_43=Cyclegg_True:g_17=Cyclegg_True:g_34=Cyclegg_True
                                            -- <= adding scrutinee g_34 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_200)
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                            -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                            -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
            (Cyclegg_Nil ) ->
              -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_ins ?n Cyclegg_Nil) =>
              -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=Cyclegg_Nil
              -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
              -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
              -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130) =>
              -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
              -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_elem ?n Cyclegg_Nil) =>
              -- <= (cyclegg_elem ?n Cyclegg_Nil)
              -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=Cyclegg_Nil
              -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
              -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=Cyclegg_Nil =>
              -- <= (cyclegg_ins ?n Cyclegg_Nil)
              -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=Cyclegg_Nil
              goal_73 (cyclegg_x_80) (cyclegg_y_130) (cyclegg_xs)
              -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
              -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_elem ?n Cyclegg_Nil) =>
              -- <= (cyclegg_elem ?n Cyclegg_Nil)
              -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=(Cyclegg_S cyclegg_y_130):cyclegg_xs=Cyclegg_Nil
        (Cyclegg_Z ) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) ->
              let g_24 = (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140) in
                case g_24 of
                  (Cyclegg_False ) ->
                    let g_30 = (cyclegg_eq cyclegg_x_80 cyclegg_xs_140) in
                      case g_30 of
                        (Cyclegg_False ) ->
                          let g_33 = (cyclegg_lt Cyclegg_Z cyclegg_xs_140) in
                            case g_33 of
                              (Cyclegg_False ) ->
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z =>
                                -- adding scrutinee g_33 to split condition (cyclegg_lt Cyclegg_Z cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_False:g_30=Cyclegg_False:g_33=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z
                                goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_141)
                                -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                              (Cyclegg_True ) ->
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z =>
                                -- adding scrutinee g_33 to split condition (cyclegg_lt Cyclegg_Z cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_False:g_30=Cyclegg_False:g_33=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_False
                                -- <= adding scrutinee g_24 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                -- adding scrutinee g_24 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                ()
                        (Cyclegg_True ) ->
                          let g_33 = (cyclegg_lt Cyclegg_Z cyclegg_xs_140) in
                            case g_33 of
                              (Cyclegg_False ) ->
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z =>
                                -- adding scrutinee g_33 to split condition (cyclegg_lt Cyclegg_Z cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_False:g_30=Cyclegg_True:g_33=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z
                                goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_141)
                                -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                              (Cyclegg_True ) ->
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z =>
                                -- adding scrutinee g_33 to split condition (cyclegg_lt Cyclegg_Z cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_False:g_30=Cyclegg_True:g_33=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_False
                                -- <= adding scrutinee g_24 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                -- adding scrutinee g_24 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                ()
                  (Cyclegg_True ) ->
                    let g_30 = (cyclegg_eq cyclegg_x_80 cyclegg_xs_140) in
                      case g_30 of
                        (Cyclegg_False ) ->
                          let g_33 = (cyclegg_lt Cyclegg_Z cyclegg_xs_140) in
                            case g_33 of
                              (Cyclegg_False ) ->
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z =>
                                -- adding scrutinee g_33 to split condition (cyclegg_lt Cyclegg_Z cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_True:g_30=Cyclegg_False:g_33=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z
                                goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_141)
                                -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                              (Cyclegg_True ) ->
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z =>
                                -- adding scrutinee g_33 to split condition (cyclegg_lt Cyclegg_Z cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_True:g_30=Cyclegg_False:g_33=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                -- adding scrutinee g_24 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_True
                                -- <= adding scrutinee g_24 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140)
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                ()
                        (Cyclegg_True ) ->
                          let g_33 = (cyclegg_lt Cyclegg_Z cyclegg_xs_140) in
                            case g_33 of
                              (Cyclegg_False ) ->
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z =>
                                -- adding scrutinee g_33 to split condition (cyclegg_lt Cyclegg_Z cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_True:g_30=Cyclegg_True:g_33=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z
                                goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_141)
                                -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                              (Cyclegg_True ) ->
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z =>
                                -- adding scrutinee g_33 to split condition (cyclegg_lt Cyclegg_Z cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_True:g_30=Cyclegg_True:g_33=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80) =>
                                -- adding scrutinee g_24 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140) =>
                                -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_24=Cyclegg_True
                                -- <= adding scrutinee g_24 to split condition (cyclegg_eq (Cyclegg_S cyclegg_x_80) cyclegg_xs_140)
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80)
                                -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                                -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                                ()
            (Cyclegg_Nil ) ->
              -- case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_ins ?n Cyclegg_Nil) =>
              -- <= case-split:goal_73:cyclegg_x=(Cyclegg_S cyclegg_x_80):cyclegg_y=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
              -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
              -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
              ()
    (Cyclegg_Z ) ->
      case cyclegg_y of
        (Cyclegg_S cyclegg_y_90) ->
          case cyclegg_xs of
            (Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) ->
              let g_37 = (cyclegg_lt (Cyclegg_S cyclegg_y_90) cyclegg_xs_140) in
                case g_37 of
                  (Cyclegg_False ) ->
                    -- case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                    -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                    -- <= case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                    -- case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90) =>
                    -- adding scrutinee g_37 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_90) cyclegg_xs_140) =>
                    -- case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_37=Cyclegg_False =>
                    -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                    -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                    -- <= case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90)
                    goal_73 (cyclegg_x) (cyclegg_y) (cyclegg_xs_141)
                    -- goal_73-(cyclegg_elem ?cyclegg_x (cyclegg_ins ?cyclegg_y ?cyclegg_xs))=(cyclegg_elem ?cyclegg_x ?cyclegg_xs) =>
                    -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
                    -- <= case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                  (Cyclegg_True ) ->
                    -- case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
                    -- (cyclegg_ins ?n (Cyclegg_Cons ?x ?xs)) =>
                    -- <= case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
                    -- case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90) =>
                    -- adding scrutinee g_37 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_90) cyclegg_xs_140) =>
                    -- case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_37=Cyclegg_True =>
                    -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                    -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                    -- <= case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):g_37=Cyclegg_True
                    -- <= adding scrutinee g_37 to split condition (cyclegg_lt (Cyclegg_S cyclegg_y_90) cyclegg_xs_140)
                    -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
                    -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                    ()
            (Cyclegg_Nil ) ->
              -- case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=Cyclegg_Nil =>
              -- (cyclegg_ins ?n Cyclegg_Nil) =>
              -- <= case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=(Cyclegg_S cyclegg_y_90):cyclegg_xs=Cyclegg_Nil
              -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
              -- premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False =>
              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
              ()
        (Cyclegg_Z ) ->
          unreachable (
            -- <= premise (cyclegg_eq cyclegg_x cyclegg_y)=Cyclegg_False
            -- case-split:goal_73:cyclegg_x=Cyclegg_Z =>
            -- case-split:goal_73:cyclegg_x=Cyclegg_Z:cyclegg_y=Cyclegg_Z =>
            -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
            ()
          )



