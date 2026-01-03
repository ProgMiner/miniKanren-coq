{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Rational_unification where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
proj1_sig :: a1 -> a1
proj1_sig e =
  e

data Sumbool =
   Left
 | Right

data Sumor a =
   Inleft a
 | Inright

acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
acc_rect f x =
  f x __ (\y _ -> acc_rect f y)

well_founded_induction_type :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction_type x a =
  acc_rect (\x0 _ x1 -> x x0 x1) a

well_founded_induction :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction =
  well_founded_induction_type

eq_dec :: Nat -> Nat -> Sumbool
eq_dec n =
  nat_rec (\m -> case m of {
                  O -> Left;
                  S _ -> Right})
    (\_ iHn m -> case m of {
                  O -> Right;
                  S n0 -> iHn n0})
    n

type Set a = List a

empty_set :: Set a1
empty_set =
  Nil

set_add :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Set a1
set_add aeq_dec a x =
  case x of {
   Nil -> Cons a Nil;
   Cons a1 x1 ->
    case aeq_dec a a1 of {
     Left -> Cons a1 x1;
     Right -> Cons a1 (set_add aeq_dec a x1)}}

set_union :: (a1 -> a1 -> Sumbool) -> (Set a1) -> (Set a1) -> Set a1
set_union aeq_dec x y =
  case y of {
   Nil -> x;
   Cons a1 y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)}

type Name = Nat

name_eq_dec :: Name -> Name -> Sumbool
name_eq_dec =
  eq_dec

data Term =
   Var Name
 | Cst Name
 | Con Name Term Term

term_rect :: (Name -> a1) -> (Name -> a1) -> (Name -> Term -> a1 -> Term ->
             a1 -> a1) -> Term -> a1
term_rect f f0 f1 t =
  case t of {
   Var n -> f n;
   Cst n -> f0 n;
   Con n t0 t1 -> f1 n t0 (term_rect f f0 f1 t0) t1 (term_rect f f0 f1 t1)}

term_rec :: (Name -> a1) -> (Name -> a1) -> (Name -> Term -> a1 -> Term -> a1
            -> a1) -> Term -> a1
term_rec =
  term_rect

type Var_set = Set Name

var_set_empty :: Var_set
var_set_empty =
  empty_set

var_set_add :: Name -> Var_set -> Var_set
var_set_add =
  set_add name_eq_dec

var_set_union :: Var_set -> Var_set -> Var_set
var_set_union =
  set_union name_eq_dec

fv_term :: Term -> Var_set
fv_term t =
  case t of {
   Var n -> var_set_add n var_set_empty;
   Cst _ -> var_set_empty;
   Con _ l r -> var_set_union (fv_term l) (fv_term r)}

type Eqsys = List (Prod Name Term)

eqsys_lookup :: Eqsys -> Name -> Option Term
eqsys_lookup s x =
  case s of {
   Nil -> None;
   Cons p s0 ->
    case p of {
     Pair y t ->
      case name_eq_dec x y of {
       Left -> Some t;
       Right -> eqsys_lookup s0 x}}}

eqsys_dom :: Eqsys -> Var_set
eqsys_dom s =
  case s of {
   Nil -> var_set_empty;
   Cons p s0 -> case p of {
                 Pair x _ -> var_set_add x (eqsys_dom s0)}}

eqsys_rhs :: Eqsys -> List Term
eqsys_rhs s =
  case s of {
   Nil -> Nil;
   Cons p s0 -> case p of {
                 Pair _ t -> Cons t (eqsys_rhs s0)}}

fv_terms :: (List Term) -> Var_set
fv_terms ts =
  case ts of {
   Nil -> var_set_empty;
   Cons t ts0 -> var_set_union (fv_term t) (fv_terms ts0)}

eqsys_vars :: Eqsys -> Var_set
eqsys_vars s =
  var_set_union (eqsys_dom s) (fv_terms (eqsys_rhs s))

eqsys_walk_hlp :: Nat -> Eqsys -> Name -> Prod Name Term
eqsys_walk_hlp fuel s x =
  case fuel of {
   O -> Pair x (Var x);
   S fuel0 ->
    case eqsys_lookup s x of {
     Some t -> case t of {
                Var y -> eqsys_walk_hlp fuel0 s y;
                _ -> Pair x t};
     None -> Pair x (Var x)}}

eqsys_walk_aux :: Eqsys -> Name -> (Prod Name Term)
eqsys_walk_aux s x =
  eqsys_walk_hlp (length s) s x

type Wf_eqsys = Eqsys

wf_eqsys_get :: Wf_eqsys -> Eqsys
wf_eqsys_get =
  proj1_sig

wf_eqsys_walk :: Wf_eqsys -> Name -> Prod Name Term
wf_eqsys_walk s x =
  proj1_sig (eqsys_walk_aux (wf_eqsys_get s) x)

common_part_aux :: Term -> Term -> Sumor Term
common_part_aux t1 t2 =
  term_rec (\n _ -> Inleft (Var n)) (\n t3 ->
    case t3 of {
     Var n0 -> Inleft (Var n0);
     Cst n0 ->
      let {s = name_eq_dec n n0} in
      case s of {
       Left -> eq_rect n (Inleft (Cst n)) n0;
       Right -> Inright};
     Con _ _ _ -> Inright}) (\n _ iHt1_1 _ iHt1_2 t3 ->
    case t3 of {
     Var n0 -> Inleft (Var n0);
     Cst _ -> Inright;
     Con n0 t t0 ->
      let {s = name_eq_dec n n0} in
      case s of {
       Left ->
        eq_rect n
          (let {s0 = iHt1_1 t} in
           case s0 of {
            Inleft s1 ->
             let {s2 = iHt1_2 t0} in
             case s2 of {
              Inleft s3 -> Inleft (Con n s1 s3);
              Inright -> Inright};
            Inright -> Inright})
          n0;
       Right -> Inright}})
    t1 t2

common_part :: Term -> Term -> Option Term
common_part t1 t2 =
  case common_part_aux t1 t2 of {
   Inleft s -> Some s;
   Inright -> None}

eqsys_union :: Wf_eqsys -> Name -> Name -> Prod Eqsys
               (Option (Prod Term Term))
eqsys_union s x y =
  case wf_eqsys_walk s x of {
   Pair x0 xt ->
    case wf_eqsys_walk s y of {
     Pair y0 yt ->
      let {s0 = wf_eqsys_get s} in
      case name_eq_dec x0 y0 of {
       Left -> Pair s0 None;
       Right ->
        let {
         res = case xt of {
                Var _ -> None;
                Cst _ -> case yt of {
                          Var _ -> None;
                          _ -> Some (Pair xt yt)};
                Con _ _ _ ->
                 case yt of {
                  Var _ -> None;
                  _ -> Some (Pair xt yt)}}}
        in
        case yt of {
         Var _ -> Pair (Cons (Pair y0 (Var x0)) s0) res;
         _ -> Pair (Cons (Pair x0 (Var y0)) s0) res}}}}

wf_eqsys_union_aux :: Wf_eqsys -> Name -> Name ->
                      (Prod Wf_eqsys (Option (Prod Term Term)))
wf_eqsys_union_aux s x y =
  let {res = eqsys_union s x y} in case res of {
                                    Pair e o -> Pair e o}

wf_eqsys_union :: Wf_eqsys -> Name -> Name -> Prod Wf_eqsys
                  (Option (Prod Term Term))
wf_eqsys_union s x y =
  proj1_sig (wf_eqsys_union_aux s x y)

rational_unify_vt_impl :: Wf_eqsys -> Name -> Term -> Option
                          (Prod Eqsys (Option Term))
rational_unify_vt_impl s x yt =
  case wf_eqsys_walk s x of {
   Pair x0 xt ->
    case xt of {
     Var _ -> Some (Pair (Cons (Pair x0 yt) (wf_eqsys_get s)) None);
     _ ->
      case common_part xt yt of {
       Some t -> Some (Pair (Cons (Pair x0 t) (wf_eqsys_get s)) (Some xt));
       None -> None}}}

rational_unify_vt_aux :: Wf_eqsys -> Name -> Term ->
                         (Option (Prod Wf_eqsys (Option Term)))
rational_unify_vt_aux s x yt =
  let {res = rational_unify_vt_impl s x yt} in
  case res of {
   Some p -> case p of {
              Pair e o -> Some (Pair e o)};
   None -> None}

rational_unify_vt :: Wf_eqsys -> Name -> Term -> Option
                     (Prod Wf_eqsys (Option Term))
rational_unify_vt s x yt =
  proj1_sig (rational_unify_vt_aux s x yt)

data Rational_unification_task =
   RUTask Wf_eqsys Term Term

type Rational_unification_exists_hlp = Any

rational_unification_exists_aux :: Var_set -> Rational_unification_task ->
                                   (Rational_unification_task -> () ->
                                   Rational_unification_exists_hlp) ->
                                   Rational_unification_exists_hlp
rational_unification_exists_aux _ task iH =
  case task of {
   RUTask rational_unification_task_system rational_unification_task_left
    rational_unification_task_right ->
    unsafeCoerce (\_ ->
      case rational_unification_task_left of {
       Var n ->
        case rational_unification_task_right of {
         Var n0 ->
          let {res = wf_eqsys_union rational_unification_task_system n n0} in
          case res of {
           Pair w o ->
            case o of {
             Some p ->
              case p of {
               Pair t t0 ->
                let {iH0 = iH (RUTask w t t0)} in unsafeCoerce iH0 __ __};
             None -> Some w}};
         x ->
          let {res = rational_unify_vt rational_unification_task_system n x}
          in
          case res of {
           Some p ->
            case p of {
             Pair w o ->
              case o of {
               Some t ->
                let {iH0 = iH (RUTask w t x)} in unsafeCoerce iH0 __ __;
               None -> Some w}};
           None -> None}};
       Cst n ->
        case rational_unification_task_right of {
         Var n0 ->
          let {xt = Cst n} in
          let {
           iH0 = iH (RUTask rational_unification_task_system (Var n0) xt)}
          in
          unsafeCoerce iH0 __ __;
         Cst n0 ->
          let {s0 = name_eq_dec n n0} in
          case s0 of {
           Left ->
            eq_rect n (\_ _ -> Some rational_unification_task_system) n0 iH
              __;
           Right -> None};
         Con _ _ _ -> None};
       Con n t t0 ->
        case rational_unification_task_right of {
         Var n0 ->
          let {xt = Con n t t0} in
          let {
           iH0 = iH (RUTask rational_unification_task_system (Var n0) xt)}
          in
          unsafeCoerce iH0 __ __;
         Cst _ -> None;
         Con n0 t1 t2 ->
          let {s0 = name_eq_dec n n0} in
          case s0 of {
           Left ->
            eq_rect n (\iH0 _ ->
              let {
               r = unsafeCoerce iH0 (RUTask rational_unification_task_system
                     t t1) __ __}
              in
              case r of {
               Some w -> unsafeCoerce iH0 (RUTask w t0 t2) __ __;
               None -> None}) n0 iH __;
           Right -> None}}})}

rational_unification_exists :: Wf_eqsys -> Term -> Term -> (Option Wf_eqsys)
rational_unification_exists s t1 t2 =
  let {
   xs = var_set_union (var_set_union (fv_term t1) (fv_term t2))
          (eqsys_vars (wf_eqsys_get s))}
  in
  let {h = rational_unification_exists_aux xs} in
  let {h0 = well_founded_induction h (RUTask s t1 t2)} in unsafeCoerce h0 __

