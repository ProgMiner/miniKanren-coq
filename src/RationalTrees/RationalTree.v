Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Coq.Lists.ListSet.
Require Export Coq.Structures.OrderedTypeEx.
Require Export Coq.Structures.Orders.
Require Import Coq.Sorting.Mergesort.
Import EqNotations.

Require Import Unification.


(* Infinite Term *)

CoInductive inf_term : Set :=
| VarInf : name -> inf_term
| CstInf : name -> inf_term
| ConInf : name -> inf_term -> inf_term -> inf_term
.

Definition inf_term_step (t : inf_term) : inf_term :=
match t with
| VarInf n => VarInf n
| CstInf n => CstInf n
| ConInf n t1 t2 => ConInf n t1 t2
end.

Lemma inf_term_step_prop t : t = inf_term_step t.
Proof. destruct t; auto. Qed.

CoInductive inf_term_eq : inf_term -> inf_term -> Prop :=
| VarInfEq n : inf_term_eq (VarInf n) (VarInf n)
| CstInfEq n : inf_term_eq (CstInf n) (CstInf n)
| ConInfEq n l1 l2 r1 r2 : inf_term_eq l1 l2 -> inf_term_eq r1 r2
                        -> inf_term_eq (ConInf n l1 r1) (ConInf n l2 r2)
.

Hint Constructors inf_term_eq : core.

CoFixpoint inf_term_eq_refl t : inf_term_eq t t :=
match t with
| VarInf n => VarInfEq n
| CstInf n => CstInfEq n
| ConInf n l r => ConInfEq n l l r r (inf_term_eq_refl l) (inf_term_eq_refl r)
end.

CoFixpoint inf_term_eq_sym {t1 t2} (p : inf_term_eq t1 t2) : inf_term_eq t2 t1 :=
match p with
| VarInfEq n => VarInfEq n
| CstInfEq n => CstInfEq n
| ConInfEq n l1 l2 r1 r2 pl pr => ConInfEq n l2 l1 r2 r1 (inf_term_eq_sym pl) (inf_term_eq_sym pr)
end.

CoFixpoint inf_term_eq_trans {t1 t2 t3} (p : inf_term_eq t1 t2) (q : inf_term_eq t2 t3)
                             : inf_term_eq t1 t3.
Proof.
  refine (
    match p in inf_term_eq t1' t2' return inf_term_eq t2' t3 -> inf_term_eq t1' t3 with
    | VarInfEq n => fun q =>
      match q with
      | VarInfEq _ => VarInfEq _
      end
    | CstInfEq n => fun q =>
      match q with
      | CstInfEq _ => CstInfEq _
      end
    | ConInfEq n l1 l2 r1 r2 pl pr => fun q => _
    end q
  ).
  good_inversion q.
  refine (ConInfEq n l1 l3 r1 r3 (inf_term_eq_trans _ _ _ pl H3) (inf_term_eq_trans _ _ _ pr H4)).
Defined.

Instance inf_term_eq_equivalence : RelationClasses.Equivalence inf_term_eq :=
  RelationClasses.Build_Equivalence _ inf_term_eq_refl (fun _ _ => inf_term_eq_sym)
    (fun _ _ _ => inf_term_eq_trans).

Definition inf_subst : Set := name -> inf_term.

Definition inf_subst_trivial : inf_subst := fun n => VarInf n.

Definition inf_subst_singleton n t : inf_subst :=
  fun n' => if name_eq_dec n n' then t else VarInf n'.

CoFixpoint apply_inf_subst (s : inf_subst) (t : inf_term) : inf_term :=
match t with
| VarInf n' => s n'
| CstInf n' => CstInf n'
| ConInf n' l r => ConInf n' (apply_inf_subst s l) (apply_inf_subst s r)
end.

CoFixpoint apply_inf_subst_eq s t1 t2 (p : inf_term_eq t1 t2)
                            : inf_term_eq (apply_inf_subst s t1) (apply_inf_subst s t2) :=
match p with
| VarInfEq n => inf_term_eq_refl _
| CstInfEq n => inf_term_eq_refl _
| ConInfEq n l1 l2 r1 r2 pl pr =>
  rew <- [fun x => inf_term_eq x _] inf_term_step_prop (apply_inf_subst s (ConInf n l1 r1)) in
  rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (apply_inf_subst s (ConInf n l2 r2)) in
  ConInfEq n _ _ _ _ (apply_inf_subst_eq s l1 l2 pl) (apply_inf_subst_eq s r1 r2 pr)
end.

CoFixpoint apply_inf_subst_trivial t : inf_term_eq (apply_inf_subst inf_subst_trivial t) t :=
rew <- [fun x => inf_term_eq x _] inf_term_step_prop (apply_inf_subst inf_subst_trivial t) in
match t as t' return inf_term_eq (inf_term_step (apply_inf_subst inf_subst_trivial t')) t' with
| VarInf n => VarInfEq _
| CstInf n => CstInfEq _
| ConInf n l r => ConInfEq n _ _ _ _ (apply_inf_subst_trivial l) (apply_inf_subst_trivial r)
end.

Definition inf_subst_compose (s1 s2 : inf_subst) : inf_subst :=
  fun n => apply_inf_subst s1 (s2 n).

CoFixpoint inf_subst_compose_prop s1 s2 t
                                : inf_term_eq (apply_inf_subst (inf_subst_compose s1 s2) t)
                                              (apply_inf_subst s1 (apply_inf_subst s2 t)) :=
rew <- [fun x => inf_term_eq x _] inf_term_step_prop (apply_inf_subst _ t) in
rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (apply_inf_subst _ (apply_inf_subst _ t)) in
match t as t'
return inf_term_eq (inf_term_step (apply_inf_subst (inf_subst_compose s1 s2) t'))
                   (inf_term_step (apply_inf_subst s1 (apply_inf_subst s2 t')))
with
| VarInf n =>
  rew [fun x => inf_term_eq x _] inf_term_step_prop (apply_inf_subst s1 (s2 n)) in
  rew [fun x => inf_term_eq _ x] inf_term_step_prop (apply_inf_subst s1 _) in
  rew <- [fun x => inf_term_eq _ (apply_inf_subst s1 x)] inf_term_step_prop _ in
  rew [fun x => inf_term_eq _ (apply_inf_subst s1 x)] inf_term_step_prop (s2 n) in
  inf_term_eq_refl _
| CstInf n => CstInfEq _
| ConInf n l r =>
  ConInfEq n _ _ _ _ (inf_subst_compose_prop s1 s2 l) (inf_subst_compose_prop s1 s2 r)
end.

CoInductive is_inf_term_FV (x : name) : inf_term -> Prop :=
| VarInfFV : is_inf_term_FV x (VarInf x)
| ConInfFVL n l r : is_inf_term_FV x l -> is_inf_term_FV x (ConInf n l r)
| ConInfFVR n l r : is_inf_term_FV x r -> is_inf_term_FV x (ConInf n l r)
.

CoFixpoint apply_inf_subst_ext s1 s2 t
                               (p : forall n, is_inf_term_FV n t -> inf_term_eq (s1 n) (s2 n))
                             : inf_term_eq (apply_inf_subst s1 t) (apply_inf_subst s2 t) :=
rew <- [fun x => inf_term_eq x _] inf_term_step_prop (apply_inf_subst s1 t) in
rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (apply_inf_subst s2 t) in
match t as t'
return (forall n, is_inf_term_FV n t' -> inf_term_eq (s1 n) (s2 n))
    -> inf_term_eq (inf_term_step (apply_inf_subst s1 t'))
                   (inf_term_step (apply_inf_subst s2 t'))
with
| VarInf n => fun p =>
  rew [fun x => inf_term_eq x _] inf_term_step_prop (s1 n) in
  rew [fun x => inf_term_eq _ x] inf_term_step_prop (s2 n) in
  p n (VarInfFV _)
| CstInf n => fun _ => CstInfEq _
| ConInf n l r => fun p => ConInfEq n _ _ _ _
  (apply_inf_subst_ext s1 s2 l (fun n' p' => p n' (ConInfFVL _ _ _ _ p')))
  (apply_inf_subst_ext s1 s2 r (fun n' p' => p n' (ConInfFVR _ _ _ _ p')))
end p.

Definition is_ground_inf_term (t : inf_term) : Prop := forall x, ~is_inf_term_FV x t.

Lemma CstInf_is_ground_inf_term n : is_ground_inf_term (CstInf n).
Proof. intros x p. inversion p. Qed.

Lemma ConInf_is_ground_inf_term {n l r} (lH : is_ground_inf_term l) (rH : is_ground_inf_term r)
                              : is_ground_inf_term (ConInf n l r).
Proof. intros x p. good_inversion p; [ eapply lH | eapply rH ]; eauto. Qed.

Inductive is_inf_subterm : inf_term -> inf_term -> Prop :=
| EqInfSubterm t1 t2 : inf_term_eq t1 t2 -> is_inf_subterm t1 t2
| ConInfSubtermL n t1 l2 r2 : is_inf_subterm t1 l2 -> is_inf_subterm t1 (ConInf n l2 r2)
| ConInfSubtermR n t1 l2 r2 : is_inf_subterm t1 r2 -> is_inf_subterm t1 (ConInf n l2 r2)
.

Lemma is_inf_subterm_ext l1 l2 r1 r2 (H1 : inf_term_eq l1 r1) (H2 : inf_term_eq l2 r2)
                         (H3 : is_inf_subterm l1 l2)
                       : is_inf_subterm r1 r2.
Proof.
  generalize dependent r2. induction H3; intros.
  * constructor. etransitivity. symmetry. eauto. etransitivity. eauto. eauto.
  * good_inversion H2. apply ConInfSubtermL. apply IHis_inf_subterm; auto.
  * good_inversion H2. apply ConInfSubtermR. apply IHis_inf_subterm; auto.
Qed.

Fixpoint term_to_inf_term (t : term) : inf_term :=
match t with
| Var n => VarInf n
| Cst n => CstInf n
| Con n l r => ConInf n (term_to_inf_term l) (term_to_inf_term r)
end.

Lemma term_to_inf_term_eq t1 t2
                        : t1 = t2 <-> inf_term_eq (term_to_inf_term t1) (term_to_inf_term t2).
Proof.
  constructor; intro.
  * subst t2. rename t1 into t. reflexivity.
  * generalize dependent t2.
    induction t1 as [ n1 | n1 | n1 l1 IHl1 r1 ]; intros;
      destruct t2 as [ n2 | n2 | n2 l2 r2 ]; good_inversion H; auto.
    apply IHl1 in H2. apply IHr1 in H7. subst. auto.
Qed.

Lemma term_to_inf_term_fv t n : In n (fv_term t) <-> is_inf_term_FV n (term_to_inf_term t).
Proof.
  constructor; intro.
  * induction t.
    - destruct H; [ | inversion H ]. subst. constructor.
    - inversion H.
    - simpl in H. apply set_union_elim in H. destruct H.
      apply ConInfFVL. apply IHt1. auto.
      apply ConInfFVR. apply IHt2. auto.
  * induction t.
    - good_inversion H. left. auto.
    - inversion H.
    - good_inversion H.
      apply set_union_intro1. apply IHt1. auto.
      apply set_union_intro2. apply IHt2. auto.
Qed.

Lemma term_to_inf_term_ground t : fv_term t = var_set_empty
                              <-> is_ground_inf_term (term_to_inf_term t).
Proof.
  constructor; intro.
  * intros n H1. absurd (In n var_set_empty); auto. rewrite <- H. apply term_to_inf_term_fv. auto.
  * apply incl_l_nil. intros n H1. exfalso. eapply H. apply term_to_inf_term_fv. eauto.
Qed.


(* Rational Tree Term *)

Definition is_rt (t : inf_term) : Prop :=
  exists (ts : list inf_term), List.Forall (fun t' => is_inf_subterm t' t) ts
                            /\ forall t', is_inf_subterm t' t -> List.Exists (inf_term_eq t') ts.

Lemma CstInf_is_rt n : is_rt (CstInf n).
Proof. exists [CstInf n]. repeat constructor. good_inversion H. auto. Qed.

Lemma ConInf_is_rt {n l r} (lH : is_rt l) (rH : is_rt r) : is_rt (ConInf n l r).
Proof.
  destruct lH as [ lst [ lH1 lH2 ] ]. destruct rH as [ rst [ rH1 rH2 ] ].
  exists (ConInf n l r :: lst ++ rst). constructor. constructor. constructor. reflexivity.
  apply Forall_app. constructor; eapply Forall_impl; eauto; simpl; intros.
  apply ConInfSubtermL. auto. apply ConInfSubtermR. auto.
  intros. good_inversion H. left. auto. all: right; apply Exists_app.
  left. apply lH2. auto. right. apply rH2. auto.
Qed.

Inductive is_subterm : term -> term -> Prop :=
| EqSubterm t : is_subterm t t
| ConSubtermL n t1 l2 r2 : is_subterm t1 l2 -> is_subterm t1 (Con n l2 r2)
| ConSubtermR n t1 l2 r2 : is_subterm t1 r2 -> is_subterm t1 (Con n l2 r2)
.

Lemma is_subterm_inf t1 t2 : is_subterm t1 t2
                         <-> is_inf_subterm (term_to_inf_term t1) (term_to_inf_term t2).
Proof.
  constructor; intro.
  * induction H.
    - constructor. reflexivity.
    - apply ConInfSubtermL. auto.
    - apply ConInfSubtermR. auto.
  * remember (term_to_inf_term t1) as t1'. symmetry in Heqt1'.
    remember (term_to_inf_term t2) as t2'. symmetry in Heqt2'.
    generalize dependent t2. generalize dependent t1.
    induction H; intros; subst.
    - apply term_to_inf_term_eq in H. subst. constructor.
    - destruct t2; good_inversion Heqt2'. apply ConSubtermL. auto.
    - destruct t2; good_inversion Heqt2'. apply ConSubtermR. auto.
Qed.

Lemma is_subterm_inf_inv t1 t2 (H : is_inf_subterm t1 (term_to_inf_term t2))
                       : exists t1', inf_term_eq t1 (term_to_inf_term t1')
                                  /\ is_subterm t1' t2.
Proof.
  remember (term_to_inf_term t2) as t2'. symmetry in Heqt2'.
  generalize dependent t2. induction H; intros; subst.
  * eexists. constructor; eauto. constructor.
  * destruct t2; good_inversion Heqt2'. edestruct IHis_inf_subterm as [ t1' [ H1 H2 ] ]. auto.
    eexists. constructor; eauto. apply ConSubtermL. auto.
  * destruct t2; good_inversion Heqt2'. edestruct IHis_inf_subterm as [ t1' [ H1 H2 ] ]. auto.
    eexists. constructor; eauto. apply ConSubtermR. auto.
Qed.

Fixpoint term_subterms (t : term) : list term :=
  set_add term_eq_dec t
    (match t with
    | Con _ l r => set_union term_eq_dec (term_subterms l) (term_subterms r)
    | _ => empty_set _
    end).

Lemma term_subterms_distinct t : NoDup (term_subterms t).
Proof. induction t; apply set_add_nodup; try apply NoDup_nil. apply set_union_nodup; auto. Qed.

Lemma term_subterms_prop t1 t2 : is_subterm t1 t2 <-> In t1 (term_subterms t2).
Proof.
  constructor; intro.
  * induction H.
    - destruct t; apply set_add_intro2; auto.
    - apply set_add_intro1. apply set_union_intro1. auto.
    - apply set_add_intro1. apply set_union_intro2. auto.
  * induction t2 as [ n2 | n2 | n2 l2 IHl2 r2 ].
    - destruct H; [ | inversion H ]. subst. constructor.
    - destruct H; [ | inversion H ]. subst. constructor.
    - simpl in H. apply set_add_elim in H. destruct H; [ | apply set_union_elim in H; destruct H ].
      + subst. constructor.
      + apply ConSubtermL. auto.
      + apply ConSubtermR. auto.
Qed.

Lemma term_subterms_prop_inf t1 t2 : is_inf_subterm t1 (term_to_inf_term t2)
                                 <-> exists t1', inf_term_eq t1 (term_to_inf_term t1')
                                              /\ In t1' (term_subterms t2).
Proof.
  constructor; intro.
  * apply is_subterm_inf_inv in H. destruct H as [ t1' [ H1 H2 ] ].
    eexists. constructor; eauto. apply term_subterms_prop. auto.
  * destruct H as [ t1' [ H1 H2 ] ]. apply term_subterms_prop in H2. apply is_subterm_inf in H2.
    eapply is_inf_subterm_ext; eauto; symmetry; auto. reflexivity.
Qed.

Lemma term_to_inf_term_is_rt t : is_rt (term_to_inf_term t).
Proof.
  exists (map term_to_inf_term (term_subterms t)). constructor.
  * apply Forall_forall. intros t' H. apply in_map_iff in H. destruct H as [ t'' [ H1 H2 ] ].
    subst. apply is_subterm_inf. apply term_subterms_prop. auto.
  * intros. apply Exists_exists. apply is_subterm_inf_inv in H. destruct H as [ t'' [ H1 H2 ] ].
    exists (term_to_inf_term t''). constructor; auto. apply in_map_iff.
    eexists. constructor; auto. apply term_subterms_prop. auto.
Qed.

Definition rt_term : Set := { t | is_rt t }.

Definition ground_rt_term : Set := { t | is_rt t /\ is_ground_inf_term t }.

Definition grt_eq (t1 t2 : ground_rt_term) : Prop := inf_term_eq (proj1_sig t1) (proj1_sig t2).

Lemma grt_eq_refl (f : ground_rt_term) : grt_eq f f.
Proof. unfold grt_eq. reflexivity. Qed.

Lemma grt_eq_sym {f1 f2} (p : grt_eq f1 f2) : grt_eq f2 f1.
Proof. unfold grt_eq. symmetry. apply p. Qed.

Lemma grt_eq_trans {f1 f2 f3} (p : grt_eq f1 f2) (q : grt_eq f2 f3) : grt_eq f1 f3.
Proof. unfold grt_eq. etransitivity. apply p. apply q. Qed.

Instance grt_eq_equivalence : RelationClasses.Equivalence grt_eq :=
  RelationClasses.Build_Equivalence _ grt_eq_refl (fun _ _ => grt_eq_sym)
    (fun _ _ _ => grt_eq_trans).


(* Mu-Term *)

Inductive mu_term : Set :=
| VarMu : name -> mu_term
| CstMu : name -> mu_term
| ConMu : name -> mu_term -> mu_term -> mu_term
| BndMu : name -> mu_term -> mu_term
.

Fixpoint mu_subst (x : name) (t' t : mu_term) : mu_term :=
match t with
| VarMu n => if name_eq_dec x n then t' else VarMu n
| CstMu n => CstMu n
| ConMu n l r => ConMu n (mu_subst x t' l) (mu_subst x t' r)
| BndMu n t => if name_eq_dec x n then BndMu n t else BndMu n (mu_subst x t' t)
end.

(* Actually, we only need to forbid (mu x. x) because of interpretation inexistence,
 * but in practice it's convenient to allow only constructor inside of binder
 * since all other legal mu-terms can be easily converted to the corresponding form
 *)
Inductive mu_term_wf : mu_term -> Prop :=
| VarMuWF n : mu_term_wf (VarMu n)
| CstMuWF n : mu_term_wf (CstMu n)
| ConMuWF n l r : mu_term_wf l -> mu_term_wf r -> mu_term_wf (ConMu n l r)
| BndMuWF n1 n2 l r : mu_term_wf (ConMu n2 l r) -> mu_term_wf (BndMu n1 (ConMu n2 l r))
.

Lemma mu_term_wf_con_l {n l r} (twf : mu_term_wf (ConMu n l r)) : mu_term_wf l.
Proof. inversion twf. auto. Qed.

Lemma mu_term_wf_con_r {n l r} (twf : mu_term_wf (ConMu n l r)) : mu_term_wf r.
Proof. inversion twf. auto. Qed.

Lemma mu_subst_wf {n t' t} (twf' : mu_term_wf t') (twf : mu_term_wf t) : mu_term_wf (mu_subst n t' t).
Proof.
  induction t; simpl; auto.
  - destruct (name_eq_dec n n0); subst; auto.
  - good_inversion twf. constructor; [ apply IHt1 | apply IHt2 ]; auto.
  - destruct (name_eq_dec n n0). subst. auto. good_inversion twf.
    specialize (IHt H0). good_inversion IHt. simpl. constructor. constructor; auto.
Qed.

Definition unfold_mu_step (n : name) (t : mu_term) : mu_term :=
  mu_subst n (BndMu n t) t.

Lemma unfold_mu_step_wf {n t} (twf : mu_term_wf (BndMu n t)) : mu_term_wf (unfold_mu_step n t).
Proof. apply mu_subst_wf. auto. good_inversion twf. auto. Qed.

Lemma unfold_mu_step_not_BndMu {n n' t t'} (twf : mu_term_wf (BndMu n t))
                             : unfold_mu_step n t <> BndMu n' t'.
Proof. unfold unfold_mu_step. good_inversion twf. simpl. intro. inversion H. Qed.

Definition unfold_mu_hlp (unfold_mu : forall t, mu_term_wf t -> inf_term)
                         n t (twf : mu_term_wf (BndMu n t)) : inf_term :=
match unfold_mu_step n t as t' return mu_term_wf t' -> unfold_mu_step n t = t' -> _ with
| VarMu n => fun _ _ => VarInf n
| CstMu n => fun _ _ => CstInf n
| ConMu n l r => fun twf _ =>
  ConInf n (unfold_mu l (mu_term_wf_con_l twf)) (unfold_mu r (mu_term_wf_con_r twf))
| BndMu n' t' => fun _ p => False_rec _ (unfold_mu_step_not_BndMu twf p)
end (unfold_mu_step_wf twf) eq_refl.

CoFixpoint unfold_mu (t : mu_term) (twf : mu_term_wf t) : inf_term :=
match t as t' return mu_term_wf t' -> _ with
| VarMu n => fun _ => VarInf n
| CstMu n => fun _ => CstInf n
| ConMu n l r => fun twf =>
  ConInf n (unfold_mu l (mu_term_wf_con_l twf)) (unfold_mu r (mu_term_wf_con_r twf))
| BndMu n t => fun twf => unfold_mu_hlp unfold_mu n t twf
end twf.
