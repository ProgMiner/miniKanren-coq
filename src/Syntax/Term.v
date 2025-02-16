Require Import Eqdep_dec.
Require Import PeanoNat.
Require List.

Require Import Util.Fin.

Import EqNotations.


#[local] Parameter F : Set.
#[local] Parameter F_arity : F -> nat.
#[local] Axiom F_eq_dec : forall (f g : F), {f = g} + {f <> g}.

#[local] Hint Resolve F_eq_dec : core.

#[local] Hint Resolve Nat.eq_dec : core.

Record term_cons (T : Set) := TermCons
  { term_cons_f : F
  ; term_cons_ts : vec T (F_arity term_cons_f)
  }.

Arguments TermCons {_} _ _.
Arguments term_cons_f {_} _.
Arguments term_cons_ts {_} _.

Inductive simple_term (V : Set) : Set :=
| VarST : V -> simple_term V
| ConsST : term_cons (simple_term V) -> simple_term V
.

Arguments VarST {_} _.
Arguments ConsST {_} _.

Module InfiniteTerm.

Record cons (T : Set) := Cons
  { cons_f : F
  ; cons_ts : array T (F_arity cons_f)
  }.

Arguments Cons {_} _ _.
Arguments cons_f {_} _.
Arguments cons_ts {_} _.

Variant head (V T : Set) : Set :=
| VarHead : V -> head V T
| ConsHead : cons T -> head V T
.

Arguments VarHead {_ _} _.
Arguments ConsHead {_ _} _.

CoInductive term V : Set := Term { term_head : head V (term V) }.

Arguments Term {_} _.

Definition step {V} (t : term V) : term V :=
match t with Term t => Term t end.

Lemma step_prop {V} (t : term V) : t = step t.
Proof. destruct t. reflexivity. Qed.

CoInductive eq {V} : term V -> term V -> Prop :=
| VarEq : forall v, eq (Term (VarHead v)) (Term (VarHead v))
| ConsEq : forall f (ts1 ts2 : array (term V) (F_arity f)), (forall i, eq (ts1 i) (ts2 i))
               -> eq (Term (ConsHead (Cons f ts1))) (Term (ConsHead (Cons f ts2)))
.

CoFixpoint eq_refl {V} (t : term V) : eq t t :=
match t as t' return eq t' t' with
| Term (VarHead v) => VarEq v
| Term (ConsHead (Cons f ts)) => ConsEq f ts ts (fun i => eq_refl (ts i))
end.

CoFixpoint eq_sym {V} {t1 t2 : term V} (p : eq t1 t2) : eq t2 t1 :=
match p with
| VarEq v => VarEq v
| ConsEq f ts1 ts2 p => ConsEq f ts2 ts1 (fun i => eq_sym (p i))
end.

CoFixpoint eq_trans {V} {t1 t2 t3 : term V} (p : eq t1 t2) (q : eq t2 t3) : eq t1 t3.
Proof.
  refine (
    match p in eq t1' t2' return eq t2' t3 -> eq t1' t3 with
    | VarEq v => fun q =>
      match q with
      | VarEq _ => VarEq _
      end
    | ConsEq f ts1 ts2 p => fun q => _
    end q
  ).
  inversion q. constructor. intro. apply inj_pair2_eq_dec in H1; auto. subst ts3.
  eapply eq_trans; eauto.
Defined.

Instance eq_equivalence {V} : RelationClasses.Equivalence (eq (V:=V)) :=
  RelationClasses.Build_Equivalence _ eq_refl (fun _ _ => eq_sym) (fun _ _ _ => eq_trans).

CoFixpoint map {V U : Set} (h : V -> U) (t : term V) : term U :=
match t with
| Term (VarHead v) => Term (VarHead (h v))
| Term (ConsHead (Cons f ts)) => Term (ConsHead (Cons f (fun i => map h (ts i))))
end.

Lemma map_cons {V U : Set} (h : V -> U) c : eq (map h (Term (ConsHead c)))
                 (Term (ConsHead (Cons c.(cons_f) (fun i => map h (c.(cons_ts) i))))).
Proof. destruct c as [ f ts ]. rewrite step_prop at 1. reflexivity. Qed.

CoFixpoint map_eq {V U : Set} (h : V -> U) {t1 t2 : term V} (p : eq t1 t2)
                  : eq (map h t1) (map h t2) :=
rew <- [fun x => eq x _] step_prop (map h t1) in
rew <- [fun x => eq _ x] step_prop (map h t2) in
match p in eq t1' t2' return eq (step (map h t1')) (step (map h t2')) with
| VarEq v => VarEq (h v)
| ConsEq f ts1 ts2 p => ConsEq f _ _ (fun i => map_eq h (p i))
end.

CoFixpoint map_ext {V U : Set} [g h : V -> U] (p : forall v, g v = h v)
                   (t : term V) : eq (map g t) (map h t) :=
rew <- [fun x => eq x _] step_prop (map g t) in
rew <- [fun x => eq _ x] step_prop (map h t) in
match t as t' return eq (step (map g t')) (step (map h t')) with
| Term (VarHead v) => rew [fun x => eq _ (Term (VarHead x))] p v in VarEq (g v)
| Term (ConsHead (Cons f ts)) => ConsEq f _ _ (fun i => map_ext p (ts i))
end.

CoFixpoint map_map {V U W : Set} (g : V -> U) (h : U -> W) (t : term V)
       : eq (map h (map g t)) (map (fun x => h (g x)) t) :=
rew <- [fun x => eq x _] step_prop (map h (map g t)) in
rew <- [fun x => eq _ x] step_prop (map (fun x => h (g x)) t) in
match t as t' return eq (step (map h (map g t'))) (step (map (fun x => h (g x)) t')) with
| Term (VarHead v) => VarEq (h (g v))
| Term (ConsHead (Cons f ts)) => ConsEq f _ _ (fun i => map_map g h (ts i))
end.

Definition pure {V : Set} (v : V) : term V := Term (VarHead v).

CoFixpoint bind {V U : Set} (k : V -> term U) (t : term V) : term U :=
match t with
| Term (VarHead v) => k v
| Term (ConsHead (Cons f ts)) => Term (ConsHead (Cons f (fun i => bind k (ts i))))
end.

Lemma bind_cons {V U : Set} (k : V -> term U) c : eq (bind k (Term (ConsHead c)))
                  (Term (ConsHead (Cons c.(cons_f) (fun i => bind k (c.(cons_ts) i))))).
Proof. destruct c as [f ts]. rewrite step_prop at 1. reflexivity. Qed.

CoFixpoint bind_eq {V U : Set} (k : V -> term U) {t1 t2} (p : eq t1 t2)
                   : eq (bind k t1) (bind k t2) :=
rew <- [fun x => eq x _] step_prop (bind k t1) in
rew <- [fun x => eq _ x] step_prop (bind k t2) in
match p in eq t1' t2' return eq (step (bind k t1')) (step (bind k t2')) with
| VarEq v => eq_refl _
| ConsEq f ts1 ts2 p => ConsEq f _ _ (fun i => bind_eq k (p i))
end.

CoFixpoint bind_ext {V U : Set} [k1 k2 : V -> term U] (p : forall v, eq (k1 v) (k2 v))
               (t : term V) : eq (bind k1 t) (bind k2 t) :=
rew <- [fun x => eq x _] step_prop (bind k1 t) in
rew <- [fun x => eq _ x] step_prop (bind k2 t) in
match t as t' return eq (step (bind k1 t')) (step (bind k2 t')) with
| Term (VarHead v) =>
  rew [fun x => eq x _] step_prop (k1 v) in
  rew [fun x => eq _ x] step_prop (k2 v) in
  p v
| Term (ConsHead (Cons f ts)) => ConsEq f _ _ (fun i => bind_ext p (ts i))
end.

Lemma pure_bind {V U : Set} (v : V) (k : V -> term U) : bind k (pure v) = k v.
Proof. rewrite step_prop at 1. symmetry. apply (step_prop (k v)). Qed.

CoFixpoint bind_pure {V : Set} (t : term V) : eq (bind pure t) t :=
rew <- [fun x => eq x _] step_prop (bind pure t) in
rew <- [fun x => eq _ x] step_prop t in
match t as t' return eq (step (bind pure t')) (step t') with
| Term (VarHead v) => VarEq v
| Term (ConsHead (Cons f ts)) => ConsEq f _ _ (fun i => bind_pure (ts i))
end.

CoFixpoint bind_map {V U W : Set} (k : U -> term W) (h : V -> U) (t : term V)
                    : eq (bind k (map h t)) (bind (fun v => k (h v)) t) :=
rew <- [fun x => eq x _] step_prop (bind k (map h t)) in
rew <- [fun x => eq _ x] step_prop (bind (fun v => k (h v)) t) in
match t as t' return eq (step (bind k (map h t'))) (step (bind (fun v => k (h v)) t')) with
| Term (VarHead v) => eq_refl _
| Term (ConsHead (Cons f ts)) => ConsEq f _ _ (fun i => bind_map k h (ts i))
end.

CoFixpoint map_bind {V U W : Set} (h : U -> W) (k : V -> term U) (t : term V)
                    : eq (map h (bind k t)) (bind (fun x => map h (k x)) t) :=
rew <- [fun x => eq x _] step_prop (map h (bind k t)) in
rew <- [fun x => eq _ x] step_prop (bind (fun v => map h (k v)) t) in
match t as t' return eq (step (map h (bind k t'))) (step (bind (fun v => map h (k v)) t')) with
| Term (VarHead v) => eq_refl _
| Term (ConsHead (Cons f ts)) => ConsEq f _ _ (fun i => map_bind h k (ts i))
end.

CoFixpoint bind_assoc {V U W : Set} (k1 : V -> term U) (k2 : U -> term W) (t : term V)
                      : eq (bind k2 (bind k1 t)) (bind (fun x => bind k2 (k1 x)) t) :=
rew <- [fun x => eq x _] step_prop (bind k2 (bind k1 t)) in
rew <- [fun x => eq _ x] step_prop (bind (fun v => bind k2 (k1 v)) t) in
match t as t' return eq (step (bind k2 (bind k1 t'))) (step (bind (fun v => bind k2 (k1 v)) t')) with
| Term (VarHead v) => eq_refl _
| Term (ConsHead (Cons f ts)) => ConsEq f _ _ (fun i => bind_assoc k1 k2 (ts i))
end.

Definition subst {V : Set} (t : term V) := bind (option_rec (fun _ => term V) pure t).

Lemma subst_cons {V : Set} (t : term V) c : eq (subst t (Term (ConsHead c)))
                   (Term (ConsHead (Cons c.(cons_f) (fun i => subst t (c.(cons_ts) i))))).
Proof. apply bind_cons. Qed.

Lemma subst_eq {V} (t : term V) {t1 t2} (p : eq t1 t2) : eq (subst t t1) (subst t t2).
Proof. apply bind_eq. auto. Qed.

Lemma subst_ext {V} {t1 t2 : term V} (p : eq t1 t2) t : eq (subst t1 t) (subst t2 t).
Proof. apply bind_ext. intro. destruct v as [ v | ]. reflexivity. auto. Qed.

Inductive path {V} : term V -> Set :=
| HerePath : forall t, path t
| ConsPath : forall c i, path (c.(cons_ts) i) -> path (Term (ConsHead c))
| EqPath : forall {t1 t2}, eq t1 t2 -> path t1 -> path t2
.

Fixpoint at_path {V} {t : term V} (p : path t) : term V :=
match p with
| HerePath t => t
| ConsPath _ _ p => at_path p
| EqPath _ p => at_path p
end.

Lemma at_path_eq {V} {t1 t2 : term V} (H : eq t1 t2) (p : path t1)
                 : eq (at_path p) (at_path (EqPath H p)).
Proof. reflexivity. Qed.

Definition is_subterm {V} (t1 t2 : term V) : Prop := exists (p : path t2), eq t1 (at_path p).

Lemma is_subterm_eq_lhs {V} {t1 t1' t2 : term V} (p : eq t1 t1')
                        (H : is_subterm t1 t2) : is_subterm t1' t2.
Proof. destruct H. exists x. etransitivity; eauto. symmetry. auto. Qed.

Lemma is_subterm_eq_rhs {V} {t1 t2 t2' : term V} (p : eq t2 t2')
                        (H : is_subterm t1 t2) : is_subterm t1 t2'.
Proof. destruct H. eexists. etransitivity. eauto. unshelve apply at_path_eq. auto. Qed.

Definition is_regular {V} (t : term V) : Prop :=
  exists (ts : list (term V)), List.Forall (fun t' => is_subterm t' t) ts
  /\ forall t', is_subterm t' t -> List.Exists (eq t') ts.

Definition regular_term V : Set := { t : term V | is_regular t }.

Definition telescope := telescope term.

Definition apply_telescope {V n} := Telescope.apply (fun V => subst (V:=V)) (V:=V) (n:=n).

Lemma apply_telescope_eq {V n} (tsc : telescope V n) {t1 t2} (p : eq t1 t2)
                         : eq (apply_telescope tsc t1) (apply_telescope tsc t2).
Proof. induction tsc. auto. apply IHtsc. apply subst_eq. auto. Qed.

Lemma apply_telescope_cons {V n} (tsc : telescope V n) {c}
                           : eq (apply_telescope tsc (Term (ConsHead c)))
                             (Term (ConsHead (Cons c.(cons_f) (fun i =>
                               apply_telescope tsc (c.(cons_ts) i))))).
Proof.
  induction tsc; destruct c as [ f ts ]; cbn.
  - constructor. intro. apply eq_refl.
  - etransitivity; [ | apply (IHtsc (Cons f (fun i => subst t (ts i)))) ].
    apply apply_telescope_eq. apply subst_cons.
Qed.

Inductive telescope_eq {V} : forall {n}, telescope V n -> telescope V n -> Prop :=
| NilTE : telescope_eq NilTelescope NilTelescope
| ConsTE {n : nat} {t1 t2 : term (n_options n V)} {tsc1 tsc2} : eq t1 t2 -> telescope_eq tsc1 tsc2
                            -> telescope_eq (ConsTelescope t1 tsc1) (ConsTelescope t2 tsc2)
.

Lemma telescope_eq_refl {V n} (tsc : telescope V n) : telescope_eq tsc tsc.
Proof. induction tsc; constructor. reflexivity. auto. Qed.

Lemma telescope_eq_sym {V n} {tsc1 tsc2 : telescope V n} (p : telescope_eq tsc1 tsc2)
                       : telescope_eq tsc2 tsc1.
Proof. induction p; constructor. symmetry. auto. auto. Qed.

Lemma telescope_eq_trans {V n} {tsc1 tsc2 tsc3 : telescope V n}
                         (p : telescope_eq tsc1 tsc2) (q : telescope_eq tsc2 tsc3)
                         : telescope_eq tsc1 tsc3.
Proof.
  induction p. auto. inversion q. subst n0. apply inj_pair2_eq_dec in H1; auto.
  apply inj_pair2_eq_dec in H2; auto. apply inj_pair2_eq_dec in H3; auto. subst t0 tsc0 tsc3.
  constructor. etransitivity; eauto. apply IHp. auto.
Qed.

Instance telescope_eq_equivalence {V n} : RelationClasses.Equivalence (telescope_eq (V:=V) (n:=n)) :=
  RelationClasses.Build_Equivalence _ telescope_eq_refl (fun _ _ => telescope_eq_sym)
    (fun _ _ _ => telescope_eq_trans).

Lemma apply_telescope_ext {V n} {tsc1 tsc2 : telescope V n} (p : telescope_eq tsc1 tsc2)
                          (t : term (n_options n V))
                          : eq (apply_telescope tsc1 t) (apply_telescope tsc2 t).
Proof.
  induction p. reflexivity. etransitivity. apply IHp. cbn.
  apply apply_telescope_eq. apply subst_ext. auto.
Qed.

Module Test.

#[local] Parameter f : F.
#[local] Parameter g : F.
#[local] Axiom f_arity : F_arity f = 2.

CoFixpoint test1 : term nat := Term (ConsHead (Cons f (fun _ => test1))).

CoFixpoint test2 n : term nat :=
  let xs := fun (i : fin (F_arity f)) =>
    match rew f_arity in i with
    | None => Term (VarHead n)
    | Some _ => test2 (S n)
    end
  in Term (ConsHead (Cons f xs)).

CoFixpoint test3 : term False := Term (ConsHead (Cons f (fun _ => test3')))
with test3' : term False := Term (ConsHead (Cons g (fun _ => test3))).

End Test.

End InfiniteTerm.

Import (hints) InfiniteTerm.

Module MuTerm.

Unset Elimination Schemes.

Inductive term (V : Set) : Set :=
| VarTerm : V -> term V
| ConsTerm : term_cons (term V) -> term V
| BindTerm : term (option V) -> term V
.

Set Elimination Schemes.

Arguments VarTerm {_} _.
Arguments ConsTerm {_} _.
Arguments BindTerm {_} _.

Definition term_ind (P : forall V, term V -> Prop)
                    (var_term : forall V v, P V (VarTerm v))
                    (cons_term : forall V f ts, (forall i, P V (Vec.v2a ts i))
                              -> P V (ConsTerm (TermCons f ts)))
                    (bind_term : forall (V : Set) t, P (option V) t -> P V (BindTerm t))
                    : forall V t, P V t :=
fix term_ind V t :=
  match t as t' return P V t' with
  | VarTerm v => var_term V v
  | ConsTerm (TermCons f ts) =>
    cons_term V f ts (Vec.v2a_dep (term_ind V) ts)
  | BindTerm t => bind_term V t (term_ind (option V) t)
  end.

Fixpoint depth {V} (t : term V) : nat :=
match t with
| VarTerm _ => 1
| ConsTerm (TermCons _ ts) => S (List.list_max (Vec.to_list (Vec.map depth ts)))
| BindTerm t => 1 + depth t
end.

Fixpoint map {V U : Set} (h : V -> U) (t : term V) : term U :=
match t with
| VarTerm x => VarTerm (h x)
| ConsTerm (TermCons f ts) => ConsTerm (TermCons f (Vec.map (map h) ts))
| BindTerm t => BindTerm (map (option_map h) t)
end.

Lemma map_ext {V U : Set} [g h : V -> U] (p : forall v, g v = h v)
              (t : term V) : map g t = map h t.
Proof.
  generalize dependent U. induction t; intros; simpl; f_equal. auto.
  - f_equal. apply Vec.map_ext. auto.
  - apply IHt. intro. destruct v; auto. simpl. f_equal. apply p.
Qed.

Lemma map_map {V U W : Set} (g : V -> U) (h : U -> W) (t : term V)
              : map h (map g t) = map (fun x => h (g x)) t.
Proof.
  generalize dependent W. generalize dependent U. induction t; intros; simpl. auto.
  - f_equal. f_equal. rewrite Vec.map_map. apply Vec.map_ext. auto.
  - f_equal. etransitivity. apply IHt. apply map_ext. intro. destruct v; auto.
Qed.

Definition pure {V : Set} (x : V) : term V := VarTerm x.

Definition bind_bind_k {V U : Set} (k : V -> term U) (v : option V) : term (option U) :=
match v with
| None => VarTerm None
| Some v => map Some (k v)
end.

Fixpoint bind {V U : Set} (k : V -> term U) (t : term V) : term U :=
match t with
| VarTerm v => k v
| ConsTerm (TermCons f ts) => ConsTerm (TermCons f (Vec.map (bind k) ts))
| BindTerm t => BindTerm (bind (bind_bind_k k) t)
end.

Lemma bind_ext {V U : Set} [k1 k2 : V -> term U] (p : forall v, k1 v = k2 v)
               (t : term V) : bind k1 t = bind k2 t.
Proof.
  generalize dependent U. induction t; intros; simpl. auto.
  - f_equal. f_equal. apply Vec.map_ext. auto.
  - f_equal. apply IHt. intro. destruct v; auto. simpl. rewrite p. auto.
Qed.

Lemma pure_bind {V U : Set} (v : V) (k : V -> term U) : bind k (pure v) = k v.
Proof. auto. Qed.

Lemma bind_pure {V : Set} (t : term V) : bind pure t = t.
Proof.
  induction t; simpl. auto.
  - f_equal. f_equal. etransitivity; [ | apply Vec.map_id ]. apply Vec.map_ext. auto.
  - f_equal. etransitivity; [ | apply IHt ]. apply bind_ext. intro. destruct v; auto.
Qed.

Lemma bind_map {V U W : Set} (k : U -> term W) (h : V -> U) (t : term V)
               : bind k (map h t) = bind (fun v => k (h v)) t.
Proof.
  generalize dependent W. generalize dependent U. induction t; intros; simpl. auto.
  - f_equal. f_equal. rewrite Vec.map_map. apply Vec.map_ext. auto.
  - f_equal. etransitivity. apply IHt. apply bind_ext. intro. destruct v; auto.
Qed.

Lemma map_bind {V U W : Set} (h : U -> W) (k : V -> term U) (t : term V)
               : map h (bind k t) = bind (fun x => map h (k x)) t.
Proof.
  generalize dependent W. generalize dependent U. induction t; intros; simpl. auto.
  - f_equal. f_equal. rewrite Vec.map_map. apply Vec.map_ext. auto.
  - f_equal. etransitivity. apply IHt. apply bind_ext.
    intro. destruct v; auto. simpl. etransitivity. apply map_map. symmetry.
    etransitivity. apply map_map. apply map_ext. auto.
Qed.

Lemma bind_assoc {V U W : Set} (k1 : V -> term U) (k2 : U -> term W) (t : term V)
                 : bind k2 (bind k1 t) = bind (fun x => bind k2 (k1 x)) t.
Proof.
  generalize dependent W. generalize dependent U. induction t; intros; simpl. auto.
  - f_equal. f_equal. rewrite Vec.map_map. apply Vec.map_ext. auto.
  - f_equal. etransitivity. apply IHt. apply bind_ext. intro. destruct v; auto. simpl.
    rewrite bind_map. rewrite map_bind. apply bind_ext. eauto.
Qed.

Lemma map_as_bind {V U : Set} (h : V -> U) (t : term V) : map h t = bind (fun v => pure (h v)) t.
Proof. etransitivity. symmetry. apply bind_pure. apply bind_map. Qed.

Definition subst {V : Set} (t : term V) := bind (option_rec (fun _ => term V) pure t).

Inductive wf {V} : term V -> Prop :=
| VarWF : forall v, wf (VarTerm v)
| ConsWF : forall c, (forall i, wf (Vec.v2a c.(term_cons_ts) i)) -> wf (ConsTerm c)
| BindWF : forall c, wf (ConsTerm c) -> wf (BindTerm (ConsTerm c))
.

Lemma wf_cons_subterm {V} {c : term_cons (term V)} (twf : wf (ConsTerm c)) (i : fin _)
                      : wf (Vec.v2a c.(term_cons_ts) i).
Proof. inversion twf. apply H0. Qed.

Lemma wf_bind_nested {V : Set} {t : term (option V)} (twf : wf (BindTerm t)) : wf t.
Proof. inversion_clear twf. auto. Qed.

Lemma map_wf {V U : Set} {t} (h : V -> U) (twf : wf t) : wf (map h t).
Proof.
  generalize dependent U. induction twf; intros. constructor.
  - destruct c. constructor. intro. rewrite Vec.map_prop. simpl. rewrite Vec.array_vec_array. auto.
  - destruct c as [ f ts ]. constructor. apply IHtwf.
Qed.

Lemma bind_wf {V U : Set} {t} [k : V -> term U] (twfs : forall v, wf (k v))
              (twf : wf t) : wf (bind k t).
Proof.
  generalize dependent U. induction twf; intros; simpl. auto.
  - destruct c. constructor. intro. rewrite Vec.map_prop. simpl. rewrite Vec.array_vec_array. auto.
  - destruct c as [ f ts ]. constructor. apply IHtwf. intro.
    destruct v. apply map_wf. auto. constructor.
Qed.

Corollary subst_wf {V} {t1 : term V} {t2} (twf1 : wf t1) (twf2 : wf t2) : wf (subst t1 t2).
Proof. apply bind_wf; auto. intro. destruct v; auto. simpl. constructor. Qed.

Definition one_unfold {V : Set} (t : term (option V)) := subst (BindTerm t) t.

Corollary wf_one_unfold_wf {V : Set} {t : term (option V)} (twf : wf (BindTerm t))
                           : wf (one_unfold t).
Proof. apply subst_wf; auto. apply wf_bind_nested. auto. Qed.

Lemma wf_one_unfold_not_bind {V : Set} {t t' : term (option V)} (twf : wf (BindTerm t))
                             : one_unfold t <> BindTerm t'.
Proof. inversion twf. intro. destruct c. inversion H1. Qed.

Definition unfold_hlp {V} (unfold : forall (t : term V), wf t -> InfiniteTerm.term V)
                      (t : term (option V)) (twf : wf (BindTerm t))
                      (t' : term V) (p : one_unfold t = t') (twf' : wf t')
                      : InfiniteTerm.term V :=
match t' as t'' return one_unfold t = t'' -> wf t'' -> _ with
| VarTerm v => fun _ _ => InfiniteTerm.Term (InfiniteTerm.VarHead v)
| ConsTerm (TermCons f ts) => fun _ twf =>
  InfiniteTerm.Term (InfiniteTerm.ConsHead (InfiniteTerm.Cons f
    (fun i => unfold (Vec.v2a ts i) (wf_cons_subterm twf i))))
| BindTerm t => fun p _ => False_rec _ (wf_one_unfold_not_bind twf p)
end p twf'.

CoFixpoint unfold {V} (t : term V) (twf : wf t) : InfiniteTerm.term V :=
match t as t' return wf t' -> _ with
| VarTerm v => fun _ => InfiniteTerm.Term (InfiniteTerm.VarHead v)
| ConsTerm (TermCons f ts) => fun twf =>
  InfiniteTerm.Term (InfiniteTerm.ConsHead (InfiniteTerm.Cons f
    (fun i => unfold (Vec.v2a ts i) (wf_cons_subterm twf i))))
| BindTerm t => fun twf => unfold_hlp unfold t twf (one_unfold t) eq_refl (wf_one_unfold_wf twf)
end twf.

CoFixpoint unfold_irrelevance {V} {t : term V} (twf1 twf2 : wf t)
                              : InfiniteTerm.eq (unfold t twf1) (unfold t twf2) :=
rew <- [fun x => InfiniteTerm.eq x _] InfiniteTerm.step_prop (unfold t twf1) in
rew <- [fun x => InfiniteTerm.eq _ x] InfiniteTerm.step_prop (unfold t twf2) in
match t as t' return forall (twf1 twf2 : wf t'),
  InfiniteTerm.eq (InfiniteTerm.step (unfold t' twf1)) (InfiniteTerm.step (unfold t' twf2))
with
| VarTerm v => fun _ _ => InfiniteTerm.VarEq v
| ConsTerm (TermCons f ts) => fun twf1 twf2 =>
  InfiniteTerm.ConsEq f _ _ (fun i => unfold_irrelevance _ _)
| BindTerm t => fun twf1 twf2 =>
  rew [fun x => InfiniteTerm.eq x _] InfiniteTerm.step_prop (unfold_hlp unfold t twf1 _ _ _) in
  rew [fun x => InfiniteTerm.eq _ x] InfiniteTerm.step_prop (unfold_hlp unfold t twf2 _ _ _) in
  match one_unfold t as t' return forall (p : one_unfold t = t') (twf1' twf2' : wf t'),
    InfiniteTerm.eq (unfold_hlp unfold t twf1 t' p twf1') (unfold_hlp unfold t twf2 t' p twf2')
  with
  | VarTerm v => fun _ _ _ => InfiniteTerm.VarEq v
  | ConsTerm (TermCons f ts) => fun _ twf1 twf2 =>
    InfiniteTerm.ConsEq f _ _ (fun i => unfold_irrelevance _ _)
  | BindTerm t => fun p _ _ => False_ind _ (wf_one_unfold_not_bind twf1 p)
  end eq_refl (wf_one_unfold_wf twf1) (wf_one_unfold_wf twf2)
end twf1 twf2.

Lemma unfold_ext {V} {t1 t2 : term V} (twf1 : wf t1) (twf2 : wf t2) (p : t1 = t2)
                 : InfiniteTerm.eq (unfold t1 twf1) (unfold t2 twf2).
Proof. generalize dependent twf1. rewrite p. intro. apply unfold_irrelevance. Qed.

CoFixpoint unfold_bind {V U : Set} [k : V -> term U] (twfs : forall v, wf (k v))
                       {t : term V} (twf : wf t) (twf' : wf (bind k t))
                       : InfiniteTerm.eq (InfiniteTerm.bind (fun v => unfold (k v) (twfs v)) (unfold t twf))
                         (unfold (bind k t) twf') :=
rew <- [fun x => InfiniteTerm.eq x _] InfiniteTerm.step_prop (InfiniteTerm.bind _ (unfold t twf)) in
rew <- [fun x => InfiniteTerm.eq _ x] InfiniteTerm.step_prop (unfold _ _) in
match t as t' return forall (twf : wf t') (twf' : wf (bind k t')),
  InfiniteTerm.eq (InfiniteTerm.step (InfiniteTerm.bind (fun v => unfold (k v) (twfs v)) (unfold t' twf)))
    (InfiniteTerm.step (unfold (bind k t') twf'))
with
| VarTerm v => fun twf twf' =>
  rew [fun x => InfiniteTerm.eq x _] InfiniteTerm.step_prop (unfold (k v) _) in
  rew [fun x => InfiniteTerm.eq _ x] InfiniteTerm.step_prop (unfold (k v) _) in
  unfold_irrelevance (twfs v) twf'
| ConsTerm (TermCons f ts) => fun twf twf' =>
  InfiniteTerm.ConsEq f _ _ (fun i =>
    (
      rew <- [fun x => forall (twf'' : wf (Vec.v2a x i)), InfiniteTerm.eq _ (unfold _ twf'')]
        Vec.map_prop (bind _) _
      in
      rew <- [fun x => forall (twf'' : wf x), InfiniteTerm.eq _ (unfold _ twf'')]
        Vec.array_vec_array _ i
      in
      unfold_bind twfs (wf_cons_subterm twf i)
    ) (wf_cons_subterm twf' i)
  )
| BindTerm t =>
  match t as t' return forall (twf : wf (BindTerm t')) (twf' : wf (bind k (BindTerm t'))), _ with
  | VarTerm _ => fun twf _ => False_rec _ match twf with end
  | ConsTerm (TermCons f ts) => fun twf twf' =>
    InfiniteTerm.ConsEq f _ _ (fun i =>
      (
        rew <- [fun x =>
          forall (twf1 : wf (Vec.v2a x i)) twf2,
          InfiniteTerm.eq (InfiniteTerm.bind _ (unfold _ twf1)) _
        ] Vec.map_prop _ _ in
        rew <- [fun x =>
          forall (twf1 : wf x) twf2,
          InfiniteTerm.eq (InfiniteTerm.bind _ (unfold _ twf1)) _
        ] Vec.array_vec_array _ i in
        rew <- [fun x => forall twf1 (twf2 : wf (Vec.v2a x i)), InfiniteTerm.eq _ (unfold _ twf2)]
          Vec.map_prop _ _
        in
        rew <- [fun x => forall twf1 (twf2 : wf x), InfiniteTerm.eq _ (unfold _ twf2)]
          Vec.array_vec_array _ i
        in
        rew <- [fun x =>
          forall twf1 (twf2 : wf (bind _ (Vec.v2a x i))), InfiniteTerm.eq _ (unfold _ twf2)
        ] Vec.map_prop _ _ in
        rew <- [fun x => forall twf1 (twf2 : wf (bind _ x)), InfiniteTerm.eq _ (unfold _ twf2)]
          Vec.array_vec_array _ i
        in
        rew <- [fun x => forall twf1 (twf2 : wf x), InfiniteTerm.eq _ (unfold _ twf2)]
          bind_assoc _ _ _
        in
        rew <- [fun x => forall twf1 (twf2 : wf x), InfiniteTerm.eq _ (unfold _ twf2)]
          bind_ext (fun v =>
            match v as v' return bind _ (bind_bind_k k v') = bind k (option_rec _ pure _ v') with
            | None => eq_refl
            | Some v => eq_trans (bind_map _ _ _) (bind_pure _)
            end
          ) _
        in
        rew [fun x => forall twf1 (twf2 : wf x), InfiniteTerm.eq _ (unfold _ twf2)]
          bind_assoc _ _ _
        in
        unfold_bind twfs
      ) (wf_cons_subterm (wf_one_unfold_wf twf) i) (wf_cons_subterm (wf_one_unfold_wf twf') i)
    )
  | BindTerm _ => fun twf _ => False_rec _ match twf with end
  end
end twf twf'.

Corollary unfold_subst {V : Set} {t1 : term V} {t2} (twf1 : wf t1) (twf2 : wf t2)
                       : InfiniteTerm.eq (InfiniteTerm.subst (unfold t1 twf1) (unfold t2 twf2))
                         (unfold (subst t1 t2) (subst_wf twf1 twf2)).
Proof.
  etransitivity.
  2: unshelve apply unfold_bind; auto; destruct v; auto; constructor.
  apply InfiniteTerm.bind_ext. intro. destruct v; [ | reflexivity ].
  rewrite InfiniteTerm.step_prop at 1. rewrite InfiniteTerm.step_prop. reflexivity.
Qed.

Lemma unfold_bind_term {V : Set} {t : term (option V)} (twf : wf (BindTerm t))
                       : InfiniteTerm.eq (unfold (BindTerm t) twf) (unfold (subst (BindTerm t) t)
                         (subst_wf twf (wf_bind_nested twf))).
Proof.
  generalize (subst_wf twf (wf_bind_nested twf)) as twf'. remember (subst (BindTerm t) t) as t'.
  intro. rewrite InfiniteTerm.step_prop at 1. rewrite InfiniteTerm.step_prop.
  destruct t'; destruct t; inversion twf; subst t; destruct c as [ f ts ]; inversion Heqt'.
  subst t0. constructor. intro. apply unfold_irrelevance.
Qed.

Inductive path {V} : forall n, term (n_options n V) -> Set :=
| HerePath : forall [n] t, path n t
| ConsPath : forall [n] c i, path n (Vec.v2a c.(term_cons_ts) i) -> path n (ConsTerm c)
| BindPath : forall [n] t, path (S n) t -> path n (BindTerm t)
.

Fixpoint paths_hlp fuel {V : Set} n (t : term (n_options n V)) : list (path n t) :=
match fuel with
| 0 => nil
| S fuel =>
  cons (HerePath t) (
    match t as t' return list (path n t') with
    | VarTerm _ => nil
    | ConsTerm c => List.concat (Vec.to_list (Vec.a2v (fun i =>
      List.map (ConsPath c i) (paths_hlp fuel n (Vec.v2a c.(term_cons_ts) i)))))
    | BindTerm t => List.map (BindPath t) (paths_hlp fuel (S n) t)
    end
  )
end.

Lemma paths_hlp_prop {V : Set} {n} [t : term (n_options n V)] (p : path n t)
                     fuel (Hfuel : fuel >= depth t)
                     : List.Exists (fun p' => p' = p) (paths_hlp fuel n t).
Proof.
  generalize dependent fuel. induction p; intros.
  - destruct fuel.
    * destruct t; inversion Hfuel. destruct t. inversion Hfuel.
    * constructor. auto.
  - destruct c as [ f ts ]. destruct fuel. inversion Hfuel. right. apply List.Exists_concat.
    apply List.Exists_nth. exists (Fin.to_nat i).
    exists (List.map (ConsPath (TermCons f ts) i) (paths_hlp fuel n (Vec.v2a ts i))).
    constructor. rewrite Vec.to_list_length. apply Fin.to_nat_prop.
    erewrite List.nth_error_nth. 2: apply Vec.to_list_nth. rewrite Vec.array_vec_array.
    apply List.Exists_map. eapply List.Exists_impl; [ | apply IHp ]. intros p' Hp'. f_equal. auto.
    apply le_S_n in Hfuel. apply List.list_max_le in Hfuel.
    unshelve eapply List.Forall_nth in Hfuel. apply (Fin.to_nat i). apply 0.
    erewrite List.nth_error_nth in Hfuel. apply Hfuel. etransitivity. apply Vec.to_list_nth.
    f_equal. rewrite Vec.map_prop. rewrite Vec.array_vec_array. auto.
    rewrite Vec.to_list_length. apply Fin.to_nat_prop.
  - destruct fuel. inversion Hfuel. right. apply List.Exists_map.
    eapply List.Exists_impl; [ | apply IHp ]. intros p' Hp'. f_equal. auto. apply le_S_n. auto.
Qed.

Definition paths {V : Set} (t : term V) := paths_hlp (depth t) 0 t.

Lemma paths_prop {V : Set} (t : term V) (p : path 0 t) : List.Exists (fun p' => p' = p) (paths t).
Proof. apply paths_hlp_prop. auto. Qed.

Fixpoint unfold_subterm_hlp {V n} (tsc : InfiniteTerm.telescope V n)
                            {t : term (n_options n V)} (twf : wf t)
                            (p : path n t) : InfiniteTerm.term V :=
match p in path n' t' return telescope InfiniteTerm.term V n' -> wf t' -> _ with
| HerePath t => fun tsc twf => InfiniteTerm.apply_telescope tsc (unfold t twf)
| ConsPath c i p => fun tsc twf => unfold_subterm_hlp tsc (wf_cons_subterm twf i) p
| BindPath t p => fun tsc twf =>
  unfold_subterm_hlp (ConsTelescope (unfold (BindTerm t) twf) tsc) (wf_bind_nested twf) p
end tsc twf.

Lemma unfold_subterm_hlp_ext {V n} {tsc1 tsc2 : InfiniteTerm.telescope V n}
                             (H : InfiniteTerm.telescope_eq tsc1 tsc2)
                             {t : term (n_options n V)} (twf : wf t) (p : path n t)
                             : InfiniteTerm.eq (unfold_subterm_hlp tsc1 twf p)
                               (unfold_subterm_hlp tsc2 twf p).
Proof.
  induction p; simpl.
  - apply InfiniteTerm.apply_telescope_ext. auto.
  - apply IHp. auto.
  - apply IHp. constructor; auto. reflexivity.
Qed.

Lemma unfold_subterm_hlp_irrelevance {V n} (tsc : InfiniteTerm.telescope V n)
                                     {t : term (n_options n V)} (twf1 twf2 : wf t) (p : path n t)
                                     : InfiniteTerm.eq (unfold_subterm_hlp tsc twf1 p)
                                       (unfold_subterm_hlp tsc twf2 p).
Proof.
  induction p.
  - apply InfiniteTerm.apply_telescope_eq. apply unfold_irrelevance.
  - apply IHp.
  - simpl. etransitivity. eapply unfold_subterm_hlp_ext. constructor.
    apply unfold_irrelevance. reflexivity. apply IHp.
Qed.

Lemma unfold_subterm_hlp_prop {V n} (tsc : InfiniteTerm.telescope V n)
                              {t : term (n_options n V)} (twf : wf t) (p : path n t)
                              : InfiniteTerm.is_subterm (unfold_subterm_hlp tsc twf p)
                                (InfiniteTerm.apply_telescope tsc (unfold t twf)).
Proof.
  induction p. eexists (InfiniteTerm.HerePath _). reflexivity.
  - destruct c as [ f ts ]. destruct (IHp tsc (wf_cons_subterm twf i)) as [ p' Hp' ].
    rewrite (InfiniteTerm.step_prop (unfold _ _)).
    eapply InfiniteTerm.is_subterm_eq_rhs. symmetry. apply InfiniteTerm.apply_telescope_cons.
    exists (InfiniteTerm.ConsPath (InfiniteTerm.Cons f (fun j =>
      InfiniteTerm.apply_telescope tsc (unfold (Vec.v2a ts j) (wf_cons_subterm twf j)))) _ p').
    apply Hp'.
  - specialize (IHp (ConsTelescope (unfold (BindTerm t) twf) tsc) (wf_bind_nested twf)).
    eapply InfiniteTerm.is_subterm_eq_rhs; eauto. apply (InfiniteTerm.apply_telescope_eq tsc).
    etransitivity. apply unfold_subst. symmetry. apply unfold_bind_term.
Qed.

Definition unfold_subterm {V} {t : term V} (twf : wf t) (p : path 0 t) :=
  unfold_subterm_hlp NilTelescope twf p.

Lemma unfold_subterm_prop {V} {t : term V} (twf : wf t) (p : path 0 t)
                          : InfiniteTerm.is_subterm (unfold_subterm twf p) (unfold t twf).
Proof. apply (unfold_subterm_hlp_prop NilTelescope). Qed.

Definition telescope := telescope term.

Definition apply_telescope {V n} := Telescope.apply (fun V => subst (V:=V)) (V:=V) (n:=n).

Lemma apply_telescope_cons {V n} (tsc : telescope V n) (c : term_cons (term (n_options n V)))
                           : apply_telescope tsc (ConsTerm c) = ConsTerm (TermCons c.(term_cons_f)
                             (Vec.map (apply_telescope tsc) c.(term_cons_ts))).
Proof.
  induction tsc; destruct c as [ f ts ].
  - cbn. rewrite Vec.map_prop. rewrite Vec.vec_array_vec. reflexivity.
  - etransitivity. apply IHtsc. simpl. rewrite Vec.map_map.
    erewrite Vec.map_ext. reflexivity. intro. reflexivity.
Qed.

Lemma apply_telescope_inside {V n} (tsc : telescope V n) (t : term (n_options n V))
                             : bind (fun v => apply_telescope tsc (pure v)) t = apply_telescope tsc t.
Proof.
  induction tsc. apply bind_pure. etransitivity; [ | apply IHtsc ].
  etransitivity; [ | symmetry; apply bind_assoc ]. apply bind_ext. intro. destruct v; auto.
Qed.

Definition apply_telescope_bind_k {V n} (tsc : telescope V n) (v : n_options (S n) V) :=
match v with
| None => pure None
| Some v => map Some (apply_telescope tsc (pure v))
end.

Lemma apply_telescope_bind {V n} (tsc : telescope V n) (t : term (n_options (S n) V))
                           : apply_telescope tsc (BindTerm t) = BindTerm (bind (apply_telescope_bind_k tsc) t).
Proof.
  induction tsc.
  - cbn. f_equal. etransitivity. symmetry. apply bind_pure. apply bind_ext. intro. destruct v; auto.
  - etransitivity. apply IHtsc. f_equal. etransitivity. apply bind_assoc. apply bind_ext.
    intro. repeat (destruct v as [ v | ]; auto). etransitivity. apply bind_map. simpl.
    etransitivity. symmetry. apply map_bind. f_equal. cbn. apply apply_telescope_inside.
Qed.

Lemma apply_telescope_collapse {V n} (tsc : telescope V n) (v : n_options n V)
                               {m t tsc'} (p : Telescope.collapse tsc v = Some (existT _ m (t, tsc')))
                               : apply_telescope tsc (VarTerm v) = apply_telescope tsc' t.
Proof. apply Telescope.apply_collapse; eauto. Qed.

Lemma apply_telescope_not_added {V n} (tsc : telescope V n)
                                (v : n_options n V) (H : ~(NOptions.is_added v))
                                : exists v', apply_telescope tsc (VarTerm v) = VarTerm v'.
Proof. apply Telescope.apply_not_added; eauto. Qed.

Definition decode_inf_path_cons {V n}
                                (decode_inf_path : term (n_options n V)
                                               -> forall {t2 : InfiniteTerm.term V},
                                                  InfiniteTerm.path t2
                                               -> option (prod nat (list { f & fin (F_arity f) })))
                                (c1 : term_cons (term (n_options n V)))
                                (c2 : InfiniteTerm.cons (InfiniteTerm.term V))
                                (i : fin (F_arity c2.(InfiniteTerm.cons_f)))
                                (p : InfiniteTerm.path (c2.(InfiniteTerm.cons_ts) i))
                                (need_dec : bool)
                                : option (prod nat (list { f & fin (F_arity f) })) :=
match F_eq_dec c1.(term_cons_f) c2.(InfiniteTerm.cons_f) with
| left H =>
  let t1 := Vec.v2a c1.(term_cons_ts) (rew <- [fun x => fin (F_arity x)] H in i) in
  match decode_inf_path t1 p with
  | None => None
  | Some (m, p') =>
    if Nat.eq_dec n m
    then Some (if need_dec then m - 1 else m, cons (existT _ c2.(InfiniteTerm.cons_f) i) p')
    else Some (m, p')
  end
| right _ => None
end.

Definition decode_inf_path_bind {V : Set}
  (decode_inf_path : forall {n} (tsc : telescope V n)
                     (t1 : term (n_options n V)) {t2 : InfiniteTerm.term V}
                     (p : InfiniteTerm.path t2),
                     option (prod nat (list { f & fin (F_arity f) })))
  {n} (tsc : telescope V n) (t1 : term (n_options (S n) V))
  (c2 : InfiniteTerm.cons (InfiniteTerm.term V)) (i : fin (F_arity c2.(InfiniteTerm.cons_f)))
  (p : InfiniteTerm.path (c2.(InfiniteTerm.cons_ts) i))
  : option (prod nat (list { f & fin (F_arity f) })) :=
let tsc := ConsTelescope (BindTerm t1) tsc in
match t1 with
| ConsTerm c1 => decode_inf_path_cons (decode_inf_path tsc) c1 c2 i p true
| _ => None
end.

Fixpoint decode_inf_path {V n} (tsc : telescope V n) (t1 : term (n_options n V))
                         {t2 : InfiniteTerm.term V} (p : InfiniteTerm.path t2)
                         : option (prod nat (list { f & fin (F_arity f) })) :=
match p with
| InfiniteTerm.HerePath _ => Some (n, nil)
| InfiniteTerm.ConsPath c2 i p =>
  match t1 with
  | VarTerm v =>
    match Telescope.collapse tsc v with
    | Some (existT _ n (BindTerm t1, tsc)) =>
      decode_inf_path_bind (fun n => decode_inf_path) tsc t1 c2 i p
    | _ => None
    end
  | ConsTerm c1 => decode_inf_path_cons (decode_inf_path tsc) c1 c2 i p false
  | BindTerm t1 => decode_inf_path_bind (fun n => decode_inf_path) tsc t1 c2 i p
  end
| InfiniteTerm.EqPath _ p => decode_inf_path tsc t1 p
end.

Definition refine_inf_path_cons {V n}
                                (refine_inf_path : forall (t : term (n_options n V)),
                                                   list { f & fin (F_arity f) } -> path n t)
                                (c : term_cons (term (n_options n V)))
                                f (i : fin (F_arity f)) (p : list { f & fin (F_arity f) })
                                : path n (ConsTerm c) :=
match F_eq_dec c.(term_cons_f) f with
| left Hf =>
  let i' := rew <- [fun x => fin (F_arity x)] Hf in i in
  ConsPath c i' (refine_inf_path (Vec.v2a c.(term_cons_ts) i') p)
| right _ => HerePath _
end.

Fixpoint refine_inf_path {V n} (t : term (n_options n V)) (p : list { f & fin (F_arity f) })
                         : path n t :=
match p with
| nil => HerePath t
| cons (existT _ f i) p =>
  match t as t' return path n t' with
  | VarTerm _ => HerePath _
  | ConsTerm c => refine_inf_path_cons refine_inf_path c f i p
  | BindTerm t =>
    match t as t' return path n (BindTerm t') with
    | ConsTerm c =>
      let c := c : term_cons (term (n_options (S n) V)) in
      BindPath _ (refine_inf_path_cons refine_inf_path c f i p)
    | _ => HerePath _
    end
  end
end.

Definition wf_term V := { t : term V & wf t }.

Definition wf_term_term {V} (t : wf_term V) := let (t, _) := t in t.

Definition wf_term_wf {V} (t : wf_term V) : wf (wf_term_term t) :=
  let (t, twf) return wf (wf_term_term t) := t in twf.

Definition wf_subst {V} (t1 : wf_term V) (t2 : wf_term (option V)) : wf_term V :=
  existT _ (subst (wf_term_term t1) (wf_term_term t2)) (subst_wf (wf_term_wf t1) (wf_term_wf t2)).

Definition wf_telescope := Fin.telescope wf_term.

Fixpoint wf_telescope_forget {V n} (tsc : wf_telescope V n) : telescope V n :=
match tsc in Fin.telescope _ _ n' return telescope V n' with
| NilTelescope => NilTelescope
| ConsTelescope t tsc => ConsTelescope (wf_term_term t) (wf_telescope_forget tsc)
end.

Definition wf_telescope_forget_collapse_hlp
  {V} (x : { m & prod (wf_term (n_options m V)) (wf_telescope V m) })
  : { m & prod (term (n_options m V)) (telescope V m) } :=
  let (m, t_tsc) := x in
  let (t, tsc) := t_tsc in
  existT _ m (wf_term_term t, wf_telescope_forget tsc).

Lemma wf_telescope_forget_collapse {V n} (tsc : wf_telescope V n) (v : n_options n V)
                                   : Telescope.collapse (wf_telescope_forget tsc) v
                                   = option_map wf_telescope_forget_collapse_hlp
                                     (Telescope.collapse tsc v).
Proof. induction tsc. auto. destruct v. apply IHtsc. auto. Qed.

Lemma wf_apply_telescope_forget_wf {V n} (tsc : wf_telescope V n)
                                   (t : term (n_options n V)) (twf : wf t)
                                   : wf (apply_telescope (wf_telescope_forget tsc) t).
Proof. induction tsc. auto. apply IHtsc. apply subst_wf; auto. apply wf_term_wf. Qed.

Fixpoint wf_telescope_unfold {V n} (tsc : wf_telescope V n) : InfiniteTerm.telescope V n :=
match tsc in Fin.telescope _ _ n' return Fin.telescope _ _ n' with
| NilTelescope => NilTelescope
| ConsTelescope (existT _ t twf) tsc => ConsTelescope (unfold t twf) (wf_telescope_unfold tsc)
end.

Definition wf_apply_telescope {V n} := Telescope.apply (fun V => wf_subst (V:=V)) (V:=V) (n:=n).

Lemma wf_apply_telescope_term {V n} (tsc : wf_telescope V n) (t : wf_term (n_options n V))
                              : wf_term_term (wf_apply_telescope tsc t)
                              = apply_telescope (wf_telescope_forget tsc) (wf_term_term t).
Proof. induction tsc. auto. apply IHtsc. Qed.

Definition wf_unfold {V} (t : wf_term V) := unfold (wf_term_term t) (wf_term_wf t).

Lemma wf_unfold_irrelevance {V} {t : term V} (twf1 twf2 : wf t)
                            : InfiniteTerm.eq (wf_unfold (existT _ _ twf1)) (wf_unfold (existT _ _ twf2)).
Proof. apply unfold_irrelevance. Qed.

Lemma wf_unfold_apply_telescope {V n} (tsc : wf_telescope V n) (t : wf_term (n_options n V))
                                : InfiniteTerm.eq (wf_unfold (wf_apply_telescope tsc t))
                                  (unfold (apply_telescope (wf_telescope_forget tsc) (wf_term_term t))
                                    (wf_apply_telescope_forget_wf tsc (wf_term_term t) (wf_term_wf t))).
Proof.
  unfold wf_unfold. generalize (wf_term_wf (wf_apply_telescope tsc t)) as twf'.
  rewrite wf_apply_telescope_term. intro. apply unfold_irrelevance.
Qed.

Lemma wf_unfold_apply_telescope_collapse
  {V n} (tsc : wf_telescope V n) (v : n_options n V) (twf : wf (VarTerm v))
  {m t tsc'} (p : Telescope.collapse tsc v = Some (existT _ m (t, tsc')))
  : InfiniteTerm.eq (wf_unfold (wf_apply_telescope tsc (existT _ _ twf)))
    (wf_unfold (wf_apply_telescope tsc' t)).
Proof.
  etransitivity. apply wf_unfold_apply_telescope. simpl. destruct t as [ t' twf' ].
  generalize (wf_apply_telescope_forget_wf tsc _ twf). erewrite apply_telescope_collapse. intro.
  transitivity (unfold _ (wf_apply_telescope_forget_wf tsc' _ twf')). apply unfold_irrelevance.
  symmetry. apply wf_unfold_apply_telescope. etransitivity. apply wf_telescope_forget_collapse.
  rewrite p. reflexivity.
Qed.

Lemma wf_apply_telescope_unfold {V n} (tsc : wf_telescope V n) (t : wf_term (n_options n V))
                                : InfiniteTerm.eq (wf_unfold (wf_apply_telescope tsc t))
                                  (InfiniteTerm.apply_telescope (wf_telescope_unfold tsc) (wf_unfold t)).
Proof.
  induction tsc. reflexivity. destruct t0 as [ t' twf' ]. etransitivity. apply IHtsc. cbn.
  apply InfiniteTerm.apply_telescope_eq. destruct t as [ t twf ]. symmetry.
  apply unfold_subst.
Qed.

Definition wf_unfold_subterm {V n} (tsc : wf_telescope V n) (t : wf_term (n_options n V))
                             (p : path n (wf_term_term t)) :=
  unfold_subterm_hlp (wf_telescope_unfold tsc) (wf_term_wf t) p.

Definition decode_inf_path_spec {V n} (tsc : wf_telescope V n) (t : wf_term (n_options n V))
                                (p : InfiniteTerm.path (wf_unfold (wf_apply_telescope tsc t))) :=
  exists m res, decode_inf_path (wf_telescope_forget tsc) (wf_term_term t) p = Some (m, res) /\ m <= n
/\ (m = n -> InfiniteTerm.eq (wf_unfold_subterm tsc t (refine_inf_path _ res)) (InfiniteTerm.at_path p))
/\ (m < n -> exists (v : n_options n V) t' tsc', Telescope.collapse tsc v = Some (existT _ m (t', tsc'))
          /\ InfiniteTerm.eq (wf_unfold_subterm tsc' t' (refine_inf_path _ res)) (InfiniteTerm.at_path p)).

Definition wf_bind_term V := { t : wf_term V & { t' & wf_term_term t = BindTerm t' } }.

Definition wf_bind_term_term {V} (t : wf_bind_term V) := let (t, _) := t in t.

Definition wf_bind_telescope := Fin.telescope wf_bind_term.

Fixpoint wf_bind_telescope_forget_bind {V n} (tsc : wf_bind_telescope V n) : wf_telescope V n :=
match tsc in Fin.telescope _ _ n' return wf_telescope V n' with
| NilTelescope => NilTelescope
| ConsTelescope t tsc => ConsTelescope (wf_bind_term_term t) (wf_bind_telescope_forget_bind tsc)
end.

Definition wf_bind_telescope_forget_bind_collapse_hlp
  {V} (x : { m & prod (wf_bind_term (n_options m V)) (wf_bind_telescope V m) })
  : { m & prod (wf_term (n_options m V)) (wf_telescope V m) } :=
  let (m, t_tsc) := x in
  let (t, tsc) := t_tsc in
  existT _ m (wf_bind_term_term t, wf_bind_telescope_forget_bind tsc).

Lemma wf_bind_telescope_forget_bind_collapse
  {V n} (tsc : wf_bind_telescope V n) {U} (v : n_options n U)
  : Telescope.collapse (wf_bind_telescope_forget_bind tsc) v
  = option_map wf_bind_telescope_forget_bind_collapse_hlp (Telescope.collapse tsc v).
Proof. induction tsc. auto. destruct v. apply IHtsc. auto. Qed.

Definition wf_bind_telescope_forget {V n} (tsc : wf_bind_telescope V n) : telescope V n :=
  wf_telescope_forget (wf_bind_telescope_forget_bind tsc).

Definition wf_bind_telescope_forget_collapse_hlp
  {V} (x : { m & prod (wf_bind_term (n_options m V)) (wf_bind_telescope V m) })
  := wf_telescope_forget_collapse_hlp (wf_bind_telescope_forget_bind_collapse_hlp x).

Lemma wf_bind_telescope_forget_collapse
  {V n} (tsc : wf_bind_telescope V n) (v : n_options n V)
  : Telescope.collapse (wf_bind_telescope_forget tsc) v
  = option_map wf_bind_telescope_forget_collapse_hlp (Telescope.collapse tsc v).
Proof.
  etransitivity. apply wf_telescope_forget_collapse.
  induction tsc. auto. destruct v. apply IHtsc. auto.
Qed.

Lemma decode_inf_path_prop {V n} (tsc : wf_bind_telescope V n) (t : wf_term (n_options n V))
                           (p : InfiniteTerm.path (wf_unfold (wf_apply_telescope
                             (wf_bind_telescope_forget_bind tsc) t)))
                           : decode_inf_path_spec (wf_bind_telescope_forget_bind tsc) t p.
Proof.
  rename t into t1. unfold decode_inf_path_spec.
  remember (wf_unfold (wf_apply_telescope (wf_bind_telescope_forget_bind tsc) t1)) as t2.
  rename Heqt2 into Heqt2'.
  assert (Heqt2 : InfiniteTerm.eq t2 (wf_unfold (wf_apply_telescope (wf_bind_telescope_forget_bind tsc) t1))).
  rewrite Heqt2'. reflexivity. clear Heqt2'.
  generalize dependent n. induction p; intros.
  - simpl. eexists. eexists. constructor. reflexivity. constructor. auto. constructor; intro.
    symmetry. etransitivity. apply Heqt2. apply wf_apply_telescope_unfold. exfalso. eapply Nat.lt_irrefl. eauto.
  - rename c into c2. destruct t1 as [ t1 twf ]. destruct t1 as [ v | c1 | ].
    * destruct (NOptions.is_added_dec v) as [ Hv | Hv ].
      + apply (Telescope.collapse_some tsc) in Hv. destruct Hv.
        destruct x as [ m [ [ [ t1' twf' ] [ t1'' Ht1' ] ] tsc' ] ]. simpl in * |-.
        specialize (wf_bind_telescope_forget_collapse tsc v). intro. rewrite H in H0. cbn in H0.
        simpl. fold (wf_bind_telescope_forget tsc). rewrite H0. clear H0. subst t1'. inversion twf'.
        rename c into c1. subst t1''. simpl. evar (t'' : term V). evar (twf'' : wf t'').
        assert (Heqt2' : InfiniteTerm.eq (InfiniteTerm.Term (InfiniteTerm.ConsHead c2)) (unfold t'' twf'')).
        etransitivity. apply Heqt2. etransitivity. apply wf_unfold_apply_telescope_collapse.
        etransitivity. apply wf_bind_telescope_forget_bind_collapse. rewrite H. reflexivity.
        apply wf_unfold_apply_telescope. simpl in t'', twf''. subst t''. generalize dependent twf''.
        rewrite apply_telescope_bind. destruct c1 as [ f1 ts1 ]. intros. simpl in * |-.
        rewrite InfiniteTerm.step_prop in Heqt2'. simpl in Heqt2'.
        set (Hf := F_eq_dec f1 (InfiniteTerm.cons_f c2)).
        refine (_ : exists m res, match Hf with left H => _ | right _ => _ end = Some (m, res) /\ _).
        remember Hf. subst Hf. rename s into Hf. destruct Hf as [ Hf | Hf ].
        specialize (IHp (S m) (ConsTelescope (existT _ (existT _ _ (BindWF _ H1)) (existT _ _ eq_refl)) tsc')
          (existT _ _ (wf_cons_subterm H1 (rew <- [fun x => fin (F_arity x)] Hf in i)))).
        destruct IHp as [ m' [ res [ Hres [ Hm' [ Hmeq Hmlt ] ] ] ] ]. 
        inversion Heqt2'. subst c2. clear ts3 ts4 H2 H3 H4. rename ts0 into ts2.
        simpl in *. destruct Hf. rename f1 into f. inversion Heqt2'. clear f0 H0.
        apply inj_pair2_eq_dec in H3; auto. apply inj_pair2_eq_dec in H4; auto. subst ts3 ts4.
        etransitivity. apply H2. symmetry. etransitivity. apply wf_unfold_apply_telescope. simpl.
        apply unfold_ext. repeat rewrite Vec.map_prop. repeat rewrite Vec.array_vec_array.
        rewrite bind_assoc. etransitivity. symmetry. apply apply_telescope_inside. apply bind_ext.
        intro. destruct v0 as [ v0 | ]; cbn. rewrite bind_map. simpl. rewrite bind_pure. reflexivity.
        etransitivity. apply apply_telescope_bind. f_equal. simpl. rewrite <- Vec.map_prop. reflexivity.
        evar (resT : Set). evar (res' : resT). subst resT. set (Hres' := Hres : res' = _).
        refine (_ : exists m res, match res' with Some (m, p') => _ | None => _ end = Some (m, res) /\ _).
        rewrite Hres'. clear Hres' res'. remember (Nat.eq_dec (S m) m') as cond.
        destruct cond as [ cond | cond ]. subst m'. clear Hmlt. simpl. exists m. eexists.
        constructor. rewrite Nat.sub_0_r. reflexivity. constructor.
        apply Telescope.collapse_some_m in H. apply Nat.lt_le_incl. auto. constructor; intro.
        apply Telescope.collapse_some_m in H. subst m. exfalso. eapply Nat.lt_irrefl. eauto.
        exists v. eexists. eexists. constructor. etransitivity.
        apply wf_bind_telescope_forget_bind_collapse. rewrite H. simpl. reflexivity.
        etransitivity; [ | apply Hmeq; auto ]. unfold wf_unfold_subterm. simpl.
        unfold refine_inf_path_cons. simpl. rewrite <- Heqs. simpl.
        etransitivity. apply unfold_subterm_hlp_irrelevance. apply unfold_subterm_hlp_ext.
        constructor. apply unfold_irrelevance. reflexivity.
        exists m'. eexists. constructor. reflexivity. constructor. transitivity m.
        inversion Hm'. exfalso. apply cond. auto. auto. apply Nat.lt_le_incl.
        eapply Telescope.collapse_some_m. apply H. constructor; intro. subst m'.
        apply Telescope.collapse_some_m in H. exfalso. apply cond. apply Nat.le_antisymm; auto.
        destruct Hmlt as [ v' [ t' [ tsc'' [ Hv' Hp ] ] ] ]. inversion Hm'.
        exfalso. apply cond. auto. apply le_n_S. auto.
        destruct v' as [ v' | ]; simpl in *.
        specialize (wf_bind_telescope_forget_bind_collapse tsc v). rewrite H. simpl. intro.
        specialize (Telescope.collapse_compose _ v v' H2 Hv'). intro. destruct H3 as [ v'' Hv'' ].
        exists v''. eexists. eexists. constructor. eauto. auto.
        inversion Hv'. subst m'. apply inj_pair2_eq_dec in H4; auto. apply inj_pair2_eq_dec in H5; auto.
        subst tsc'' t'. exists v. eexists. eexists. constructor. etransitivity.
        apply wf_bind_telescope_forget_bind_collapse. rewrite H. reflexivity. simpl in *.
        etransitivity; [ | apply Hp ]. apply unfold_subterm_hlp_irrelevance.
        clear Heqs. destruct c2 as [ f2 ts2 ]. simpl in *. exfalso. apply Hf.
        inversion Heqt2'. auto.
      + apply (apply_telescope_not_added (wf_bind_telescope_forget tsc)) in Hv.
        destruct Hv as [ v' Hv ].
        assert (Heqt2' : InfiniteTerm.eq (InfiniteTerm.Term (InfiniteTerm.ConsHead c2))
          (InfiniteTerm.Term (InfiniteTerm.VarHead v'))).
        etransitivity. apply Heqt2. etransitivity. apply wf_unfold_apply_telescope.
        evar (t' : term V). evar (twf' : wf t'). subst t'.
        refine (_ : InfiniteTerm.eq (unfold (apply_telescope (wf_bind_telescope_forget tsc) _) twf') _).
        generalize dependent twf'. simpl. rewrite Hv. intro. rewrite InfiniteTerm.step_prop at 1.
        reflexivity. inversion Heqt2'.
    * destruct c1 as [ f1 ts1 ]. simpl. unfold decode_inf_path_cons. simpl.
      evar (t'' : term V). evar (twf'' : wf t'').
      assert (Heqt2' : InfiniteTerm.eq (InfiniteTerm.Term (InfiniteTerm.ConsHead c2)) (unfold t'' twf'')).
      etransitivity. apply Heqt2. apply wf_unfold_apply_telescope.
      simpl in t'', twf''. subst t''. generalize dependent twf''.
      rewrite apply_telescope_cons. intros. rewrite InfiniteTerm.step_prop in Heqt2'. simpl in * |-.
      set (Hf' := F_eq_dec f1 (InfiniteTerm.cons_f c2)). remember Hf'. destruct s as [ Hf | Hf ]; subst Hf'.
      specialize (IHp _ tsc (existT _ _ (wf_cons_subterm twf
        (rew <- [fun x => fin (F_arity x)] Hf in i)))).
      destruct IHp as [ m [ res [ Hres [ Hm [ Hmeq Hmlt ] ] ] ] ]. destruct c2 as [ f2 ts2 ].
      simpl in *. destruct Hf. inversion Heqt2'. apply inj_pair2_eq_dec in H1; auto.
      apply inj_pair2_eq_dec in H2; auto. subst f ts3 ts4. etransitivity. apply H0. symmetry.
      etransitivity. apply wf_unfold_apply_telescope. apply unfold_ext. rewrite Vec.map_prop.
      rewrite Vec.array_vec_array. reflexivity. simpl in * |-. rewrite Hres.
      remember (Nat.eq_dec n m) as cond. destruct cond.
      subst m. clear Hmlt Hm. exists n. eexists. constructor. reflexivity. constructor; auto.
      constructor; intro. clear H. etransitivity; [ | apply Hmeq ]; auto.
      unfold wf_unfold_subterm. simpl. unfold refine_inf_path_cons. simpl. rewrite <- Heqs.
      reflexivity. exfalso. eapply Nat.lt_irrefl. eauto.
      exists m. eexists. constructor. reflexivity. constructor. auto. constructor; intros; auto.
      exfalso. apply n0. auto.
      exfalso. apply Hf. destruct c2 as [ f2 ts2 ]. simpl in *. inversion Heqt2'. auto.
    * destruct t1. 1, 3: inversion twf. simpl.
      evar (t'' : term V). evar (twf'' : wf t'').
      assert (Heqt2' : InfiniteTerm.eq (InfiniteTerm.Term (InfiniteTerm.ConsHead c2)) (unfold t'' twf'')).
      etransitivity. apply Heqt2. apply wf_unfold_apply_telescope.
      simpl in t'', twf''. subst t''. generalize dependent twf''.
      rewrite apply_telescope_bind. destruct t as [ f1 ts1 ]. intros. simpl in *.
      rewrite InfiniteTerm.step_prop in Heqt2'. simpl in * |-. unfold decode_inf_path_cons. simpl.
      set (Hf' := F_eq_dec f1 (InfiniteTerm.cons_f c2)). remember Hf'. destruct s as [ Hf | Hf ]; subst Hf'.
      specialize (IHp _ (ConsTelescope (existT _ (existT _ _ twf) (existT _ _ eq_refl)) tsc)
        (existT _ _ (wf_cons_subterm (wf_bind_nested twf) (rew <- [fun x => fin (F_arity x)] Hf in i)))).
      destruct IHp as [ m [ res [ Hres [ Hm [ Hmeq Hmlt ] ] ] ] ].
      destruct c2 as [ f2 ts2 ]. simpl in *. destruct Hf.
      inversion Heqt2'. apply inj_pair2_eq_dec in H1; auto. apply inj_pair2_eq_dec in H2; auto.
      subst f ts3 ts4. etransitivity. apply H0. symmetry. etransitivity.
      apply wf_unfold_apply_telescope. apply unfold_ext. repeat rewrite Vec.map_prop.
      repeat rewrite Vec.array_vec_array. rewrite bind_assoc. etransitivity. symmetry.
      apply apply_telescope_inside. apply bind_ext. intro. destruct v as [ v | ]; cbn.
      rewrite bind_map. cbn. rewrite bind_pure. reflexivity.
      etransitivity. apply apply_telescope_bind. f_equal. simpl. rewrite <- Vec.map_prop. auto.
      evar (resT : Set). evar (res' : resT). subst resT. set (Hres' := Hres : res' = _).
      refine (_ : exists m res, match res' with Some (m, p') => if Nat.eq_dec (S n) m then _ else _
        | None => _ end = Some (m, res) /\ _).
      rewrite Hres'. clear Hres' res'. remember (Nat.eq_dec (S n) m) as cond.
      destruct cond; try subst m; eexists; eexists; constructor; eauto; constructor; simpl.
      rewrite Nat.sub_0_r. auto. constructor; intros. clear H. etransitivity; [ | eapply Hmeq; auto ].
      unfold wf_unfold_subterm. unfold refine_inf_path_cons. simpl. rewrite <- Heqs. reflexivity.
      exfalso. eapply Nat.lt_irrefl. rewrite Nat.sub_0_r in H. eauto.
      inversion Hm; auto. subst m. exfalso. apply n0. auto. constructor; intro.
      subst m. clear n0 Heqcond Hmeq Hm. destruct Hmlt as [ v' [ t' [ tsc' [ Hv' Hp ] ] ] ]. auto. etransitivity; [ | apply Hp ].
      generalize dependent Hv'. destruct v' as [ v' | ]; simpl; intro.
      apply Telescope.collapse_some_m in Hv'. exfalso. eapply Nat.lt_irrefl. eauto.
      inversion Hv'. apply inj_pair2_eq_dec in H0; auto. apply inj_pair2_eq_dec in H1; auto.
      subst t' tsc'. reflexivity.
      clear Hm Hmeq n0 Heqcond. destruct Hmlt as [ v' [ t' [ tsc' [ Hv' Hp ] ] ] ]. auto.
      destruct v' as [ v' | ]. exists v'. eexists. eexists. constructor; eauto.
      simpl in Hv'. inversion Hv'. subst m. exfalso. eapply Nat.lt_irrefl. eauto.
      exfalso. apply Hf. inversion Heqt2'. auto.
  - rename e into H. simpl. apply IHp. etransitivity. apply H. apply Heqt2.
Qed.

Definition path_of_inf_path {V} (t : term V) (twf : wf t) (p : InfiniteTerm.path (unfold t twf))
                            : path 0 t :=
match decode_inf_path NilTelescope t p with
| Some (_, p) => refine_inf_path (t : term (n_options 0 V)) p
| None => HerePath _
end.

Lemma path_of_inf_path_prop {V} (t : term V) (twf : wf t) (p : InfiniteTerm.path (unfold t twf))
                            : InfiniteTerm.eq (unfold_subterm twf (path_of_inf_path t twf p))
                              (InfiniteTerm.at_path p).
Proof.
  specialize (decode_inf_path_prop NilTelescope (existT _ t twf) p). cbn. intro.
  destruct H as [ m [ res [ Hres [ Hm [ Hmeq _ ] ] ] ] ]. simpl in *. inversion Hm. subst m. clear Hm.
  evar (res' : option (prod nat (list { f & fin (F_arity f) }))).
  refine (_ : InfiniteTerm.eq (unfold_subterm twf (match res' with None => _ | Some (_, p) => _ end)) _).
  rewrite (Hres : res' = _). clear res'. apply Hmeq. auto.
Qed.

Definition unfold_subterms {V} (t : term V) (twf : wf t) : list (InfiniteTerm.term V) :=
  List.map (unfold_subterm twf) (paths t).

Lemma unfold_subterms_prop {V} (t : term V) (twf : wf t)
                           : List.Forall (fun t' => InfiniteTerm.is_subterm t' (unfold t twf))
                             (unfold_subterms t twf).
Proof.
  apply List.Forall_forall. intros t' H. apply List.in_map_iff in H. destruct H as [ p H ].
  destruct H as [ H _ ]. subst t'. apply unfold_subterm_prop.
Qed.

Theorem unfold_regular {V} {t : term V} (twf : wf t) : InfiniteTerm.is_regular (unfold t twf).
Proof.
  exists (unfold_subterms t twf). constructor. apply unfold_subterms_prop. intros.
  destruct H as [ p Hp ]. specialize (path_of_inf_path_prop t twf p). intro.
  apply List.Exists_map. eapply List.Exists_impl; [ | apply paths_prop ]. simpl.
  intros. etransitivity. apply Hp. symmetry. rewrite H0. apply H.
Qed.

End MuTerm.
