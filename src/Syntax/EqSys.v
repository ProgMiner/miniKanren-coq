Require Import Eqdep_dec.
Require Import PeanoNat.
Require List.

Require Import Util.Misc.
Require Import Util.Fin.
Require Syntax.Term.

Import EqNotations.


Module Type OrderedSet.

Parameter t : Set.
Parameter lt : t -> t -> Prop.
Parameter compare : forall (x y : t), {lt x y} + {x = y} + {lt y x}.

End OrderedSet.

Module Make (F : Term.FunctionalSymbol) (V : OrderedSet).

Module Term := Term.Make F.

Import Term.
Import (hints) InfiniteTerm.


Notation "x < y" := (V.lt x y).
Notation "x > y" := (V.lt y x).

Definition system : Set := list (prod V.t (simple_term V.t)).

Definition is_equation_on_var (v : V.t) (eq : prod V.t (simple_term V.t)) : bool :=
  let (u, _) := eq in
  match V.compare v u with
  | inleft (right _) => true
  | _ => false
  end.

Definition resolve (v : V.t) (s : system) : option (simple_term V.t) :=
match List.find (is_equation_on_var v) s with
| Some (_, t) => Some t
| None => None
end.

Variant rhs_wf (v : V.t) : option (simple_term V.t) -> Prop :=
| NoneRWF : rhs_wf v None
| VarRWF : forall v', v > v' -> rhs_wf v (Some (VarST v'))
| ConsRWF : forall c, rhs_wf v (Some (ConsST c))
.

Definition wf (s : system) := forall v, rhs_wf v (resolve v s).

Fixpoint walk_hlp fuel (s : system) (v : V.t) : V.t :=
match fuel with
| 0 => v
| S fuel =>
  match resolve v s with
  | Some (VarST v) => walk_hlp fuel s v
  | _ => v
  end
end.

Definition walk s v := walk_hlp (List.length s) s v.

Definition path n m := vec (fin n) m.

Definition path_wf {n m} (p : path n m) := forall v, Vec.is_distinct (fun v' => v' = v) p.

Definition try_drop_var {V : Set} (t : MuTerm.term (option V)) : option (MuTerm.term V) :=
  MuTerm.sequence (T:=option) option_pure option_bind t.

Compute (eq_refl : try_drop_var (MuTerm.VarTerm None) = None).
Compute (eq_refl : try_drop_var (MuTerm.VarTerm (Some None)) = Some _).
Compute (eq_refl : try_drop_var (MuTerm.BindTerm (MuTerm.VarTerm None)) = Some _).
Compute (eq_refl : try_drop_var (MuTerm.BindTerm (MuTerm.VarTerm (Some None))) = None).
Compute (eq_refl : try_drop_var (MuTerm.BindTerm (MuTerm.VarTerm (Some (Some None)))) = Some _).

Fixpoint apply_hlp {V n m} (apply_hlp_k : n_options n V -> MuTerm.term (n_options m V))
                   (t : simple_term (n_options n V)) : MuTerm.term (n_options m V) :=
match t with
| VarST v => apply_hlp_k v
| ConsST (TermCons f ts) => MuTerm.ConsTerm (TermCons f (Vec.map (apply_hlp apply_hlp_k) ts))
end.

Fixpoint apply_hlp_k fuel {V n m} (s : system V n) (p : path n m) (v : n_options n V)
                     : MuTerm.term (n_options m V) :=
match fuel with
| 0 => MuTerm.BindTerm (MuTerm.VarTerm None)
| S fuel =>
  (* walk on system before to remove intermediate binds *)
  match Fin.of_n_options v with
  | inl v => MuTerm.VarTerm (NOptions.n_Somes m v)
  | inr v =>
    match Vec.find (Fin.eq_dec v) p with
    | Some v => MuTerm.VarTerm (Fin.to_n_options _ v)
    | None =>
      let t := apply_hlp (apply_hlp_k fuel s (ConsVec v p)) (Vec.v2a s v) in
      match try_drop_var t with
      | None => MuTerm.BindTerm t
      | Some t => t
      end
    end
  end
end.

Lemma apply_hlp_k_wf {V n m} (s : system V n) (p : path n m) (v : n_options n V) fuel
                     (swf : wf s) (pwf : path_wf p) (Hfuel : fuel + m > n) (Hm : m <= n)
                     : MuTerm.wf (apply_hlp_k fuel s p v).
Proof.
  generalize dependent v. generalize dependent m. induction fuel; intros.
  - exfalso. apply (Nat.lt_irrefl n). eapply Nat.lt_le_trans; eauto.
  - simpl. remember (Fin.of_n_options v) as i. destruct i as [ v' | i ]. constructor.
    remember (Vec.find (Fin.eq_dec i) p) as v'. destruct v' as [ v' | ]. constructor.
    destruct (apply_hlp_some (apply_hlp_k fuel s (ConsVec i p)) (Vec.v2a s i)).
    * specialize (Vec.find_not_p _ _ (eq_sym Heqv')). intro. intro. apply IHfuel.
      rewrite Nat.add_succ_r. auto.
      + inversion Hm. subst m. exfalso. destruct (Vec.all_in_permutation p i). constructor; eauto.
        eapply H; eauto. apply le_n_S. auto.
      + intro. intros i1 i2. intros. destruct i1 as [ i1 | ]; destruct i2 as [ i2 | ]; auto.
        f_equal. apply (Hp j i1 i2); auto. all: exfalso; subst j; eapply H; eauto.
    * rewrite H. destruct (try_drop_var x); eexists; reflexivity.
Qed.

Definition apply {V n} (s : system V n) (t : simple_term (n_options n V))
                 : option (MuTerm.term V) :=
  apply_hlp (apply_hlp_k (S n) s NilVec) t.

Lemma apply_some {V n} (s : system V n) (t : simple_term (n_options n V))
                 : exists res, apply s t = Some res.
Proof.
  apply (apply_hlp_some (apply_hlp_k _ s NilVec)). intro.
  apply apply_hlp_k_some. rewrite Nat.add_0_r. auto. apply le_0_n.
  intro. intros i1. inversion i1.
Qed.

End Make.
