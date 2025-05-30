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


(* Utils *)

Polymorphic Fixpoint n_options (T : Type) (n : nat) : Type :=
match n with
| 0 => T
| S n => option (n_options T n)
end.

Polymorphic Fixpoint map_filter [T R] (f : T -> option R) (xs : list T) : list R :=
match xs with
| nil => nil
| x::xs =>
  match f x with
  | None => map_filter f xs
  | Some x => x :: map_filter f xs
  end
end.

Polymorphic Lemma map_filter_map_l [T S R] (f : S -> R) (g : T -> option S) xs
                                 : map f (map_filter g xs)
                                 = map_filter (fun x => option_map f (g x)) xs.
Proof.
  induction xs as [ | x xs ]. auto.
  simpl. destruct (g x) as [ y | ]; auto. simpl. f_equal. apply IHxs.
Qed.

Polymorphic Lemma map_filter_map_r [T S R] (f : S -> option R) (g : T -> S) xs
                                 : map_filter f (map g xs) = map_filter (fun x => f (g x)) xs.
Proof. induction xs as [ | x xs ]. auto. simpl. rewrite IHxs. auto. Qed.

Polymorphic Lemma map_filter_In [T R] (f : T -> option R) xs y
                              : In y (map_filter f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  constructor; intro.
  * induction xs as [ | x xs ]. inversion H. simpl in H.
    remember (f x) as res. symmetry in Heqres. destruct res as [ z | ]. destruct H.
    - subst z. eexists. constructor; eauto. left. auto.
    - apply IHxs in H. destruct H as [ x' [ H1 H2 ] ]. eexists. simpl. constructor; eauto.
    - apply IHxs in H. destruct H as [ x' [ H1 H2 ] ]. eexists. simpl. constructor; eauto.
  * destruct H as [ x' [ H1 H2 ] ]. induction xs as [ | x xs ]. inversion H1. destruct H1.
    - subst x'. simpl. rewrite H2. left. auto.
    - apply IHxs in H. simpl. destruct (f x); simpl; auto.
Qed.


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
                             : inf_term_eq t1 t3 :=
match p in inf_term_eq t1' t2' return inf_term_eq t2' t3 -> inf_term_eq t1' t3 with
| VarInfEq n => fun q =>
  match q with
  | VarInfEq _ => VarInfEq _
  end
| CstInfEq n => fun q =>
  match q with
  | CstInfEq _ => CstInfEq _
  end
| ConInfEq n l1 l2 r1 r2 pl pr => fun q =>
  match q in inf_term_eq t2' t3'
  return ConInf n l2 r2 = t2' -> inf_term_eq (ConInf n l1 r1) t3'
  with
  | VarInfEq _ => fun p => match p with end
  | CstInfEq _ => fun p => match p with end
  | ConInfEq n' l2' l3 r2' r3 pl' pr' => fun p =>
    let pn : n = n' := match p in _ = ConInf n' _ _ return n = n' with
    | eq_refl => eq_refl
    end in
    let pl2 : l2' = l2 := match p in _ = ConInf _ l2' _ return l2' = l2 with
    | eq_refl => eq_refl
    end in
    let pr2 : r2' = r2 := match p in _ = ConInf _ _ r2' return r2' = r2 with
    | eq_refl => eq_refl
    end in
    rew [fun x => inf_term_eq _ (ConInf x _ _)] pn in ConInfEq n l1 l3 r1 r3
    (inf_term_eq_trans pl (rew [fun x => inf_term_eq x _] pl2 in pl'))
    (inf_term_eq_trans pr (rew [fun x => inf_term_eq x _] pr2 in pr'))
  end eq_refl
end q.

Instance inf_term_eq_equivalence : RelationClasses.Equivalence inf_term_eq :=
  RelationClasses.Build_Equivalence _ inf_term_eq_refl (fun _ _ => inf_term_eq_sym)
    (fun _ _ _ => inf_term_eq_trans).

CoInductive is_inf_term_FV (x : name) : inf_term -> Prop :=
| VarInfFV : is_inf_term_FV x (VarInf x)
| ConInfFVL n l r : is_inf_term_FV x l -> is_inf_term_FV x (ConInf n l r)
| ConInfFVR n l r : is_inf_term_FV x r -> is_inf_term_FV x (ConInf n l r)
.

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

Inductive mu_term' (V : Set) : Set :=
| VarMu' : V -> mu_term' V
| CstMu' : name -> mu_term' V
| ConMu' : name -> mu_term' V -> mu_term' V -> mu_term' V
| BndMu' : mu_term' (option V) -> mu_term' V
.

Arguments VarMu' [_] _.
Arguments CstMu' [_] _.
Arguments ConMu' [_] _ _ _.
Arguments BndMu' [_] _.

Fixpoint mu_term'_fv [V] (t : mu_term' V) : list V :=
match t with
| VarMu' n => [n]
| CstMu' _ => []
| ConMu' _ l r => mu_term'_fv l ++ mu_term'_fv r
| BndMu' t => map_filter id (mu_term'_fv t)
end.

Fixpoint mu_term'_map [V U : Set] (f : V -> U) (t : mu_term' V) : mu_term' U :=
match t with
| VarMu' n => VarMu' (f n)
| CstMu' n => CstMu' n
| ConMu' n l r => ConMu' n (mu_term'_map f l) (mu_term'_map f r)
| BndMu' t => BndMu' (mu_term'_map (option_map f) t)
end.

Lemma mu_term'_map_fv [V U : Set] (f : V -> U) t
                    : mu_term'_fv (mu_term'_map f t) = map f (mu_term'_fv t).
Proof.
  generalize dependent U. induction t; simpl; intros; auto.
  * rewrite IHt1, IHt2. symmetry. apply map_app.
  * rewrite IHt. etransitivity. apply map_filter_map_r. symmetry.
    etransitivity. apply map_filter_map_l. auto.
Qed.

Lemma mu_term'_map_ext [V U : Set] (f g : V -> U) t
                     : (forall v, In v (mu_term'_fv t) -> f v = g v)
                   <-> mu_term'_map f t = mu_term'_map g t.
Proof.
  constructor; intro.
  * generalize dependent U. induction t; simpl; intros; f_equal.
    - apply H. left. auto.
    - apply IHt1. intros. apply H. apply in_app_iff. auto.
    - apply IHt2. intros. apply H. apply in_app_iff. auto.
    - apply IHt. intros. destruct v; simpl; f_equal. apply H.
      apply map_filter_In. eexists. constructor; eauto.
  * generalize dependent U. induction t; simpl; intros.
    - destruct H0. good_inversion H. auto. inversion H0.
    - inversion H0.
    - good_inversion H. apply in_app_iff in H0. destruct H0.
      apply IHt1; auto. apply IHt2; auto.
    - good_inversion H. apply map_filter_In in H0. destruct H0 as [ x [ H0 H1 ] ].
      unfold id in H1. subst x. eapply IHt in H2; eauto. simpl in H2. good_inversion H2. auto.
Qed.

Lemma mu_term'_map_inj [V U : Set] (f : V -> U) t1 t2
                       (H1 : forall x y, f x = f y -> x = y)
                       (H2 : mu_term'_map f t1 = mu_term'_map f t2)
                     : t1 = t2.
Proof.
  generalize dependent t2. generalize dependent U.
  induction t1; simpl; intros; destruct t2; good_inversion H2; simpl; f_equal; auto.
  * eapply IHt1_1; eauto.
  * eapply IHt1_2; eauto.
  * eapply IHt1; eauto. intros. destruct x; destruct y; good_inversion H; f_equal.
    apply H1. auto.
Qed.

Lemma mu_term'_map_map [V U W : Set] (f : U -> W) (g : V -> U) t
                     : mu_term'_map f (mu_term'_map g t) = mu_term'_map (fun x => f (g x)) t.
Proof.
  generalize dependent W. generalize dependent U. induction t; simpl; intros; f_equal; auto.
  etransitivity. apply IHt. apply mu_term'_map_ext. intros. destruct v; auto.
Qed.

Definition mu_term'_BndMu'_k [V U : Set] (k : V -> mu_term' U)
                             (n : option V) : mu_term' (option U) :=
match n with
| None => VarMu' None
| Some n => mu_term'_map Some (k n)
end.

Fixpoint mu_term'_bind [V U : Set] (k : V -> mu_term' U) (t : mu_term' V) : mu_term' U :=
match t with
| VarMu' n => k n
| CstMu' n => CstMu' n
| ConMu' n l r => ConMu' n (mu_term'_bind k l) (mu_term'_bind k r)
| BndMu' t => BndMu' (mu_term'_bind (mu_term'_BndMu'_k k) t)
end.

Lemma mu_term'_bind_ext [V U : Set] (f g : V -> mu_term' U) t
                      : (forall v, In v (mu_term'_fv t) -> f v = g v)
                    <-> mu_term'_bind f t = mu_term'_bind g t.
Proof.
  constructor; intro.
  * generalize dependent U. induction t; simpl; intros; auto; f_equal.
    - apply IHt1. intros. apply H. apply in_app_iff. auto.
    - apply IHt2. intros. apply H. apply in_app_iff. auto.
    - apply IHt. intros. destruct v; simpl; f_equal.
      apply H. apply map_filter_In. eexists. constructor; eauto.
  * generalize dependent U. induction t; simpl; intros.
    - destruct H0. subst. auto. inversion H0.
    - inversion H0.
    - good_inversion H. apply in_app_iff in H0. destruct H0.
      apply IHt1; auto. apply IHt2; auto.
    - good_inversion H. apply map_filter_In in H0. destruct H0 as [ x [ H0 H1 ] ].
      unfold id in H1. subst x. eapply IHt in H2; eauto. simpl in H2.
      apply mu_term'_map_inj in H2; auto. intros. good_inversion H. auto.
Qed.

Lemma mu_term'_bind_pure [V : Set] t : mu_term'_bind (VarMu' (V:=V)) t = t.
Proof.
  induction t; simpl; f_equal; auto. etransitivity; [ | eauto ].
  apply mu_term'_bind_ext. intros. destruct v; auto.
Qed.

Lemma mu_term'_bind_map_r [V U W : Set] (k : U -> mu_term' W) (f : V -> U) t
                        : mu_term'_bind k (mu_term'_map f t) = mu_term'_bind (fun x => k (f x)) t.
Proof.
  generalize dependent W. generalize dependent U. induction t; simpl; intros; f_equal; auto.
  etransitivity. apply IHt. apply mu_term'_bind_ext. intros. destruct v; auto.
Qed.

Lemma mu_term'_bind_map_l [V U W : Set] (f : U -> W) (k : V -> mu_term' U) t
                        : mu_term'_map f (mu_term'_bind k t)
                        = mu_term'_bind (fun x => mu_term'_map f (k x)) t.
Proof.
  generalize dependent W. generalize dependent U. induction t; simpl; intros; f_equal; auto.
  etransitivity. apply IHt. apply mu_term'_bind_ext. intros. destruct v; auto. simpl.
  etransitivity. apply mu_term'_map_map. symmetry. etransitivity. apply mu_term'_map_map.
  apply mu_term'_map_ext. intros. auto.
Qed.

Lemma mu_term'_bind_assoc [V U W : Set] (k1 : U -> mu_term' W) (k2 : V -> mu_term' U) t
                        : mu_term'_bind k1 (mu_term'_bind k2 t)
                        = mu_term'_bind (fun x => mu_term'_bind k1 (k2 x)) t.
Proof.
  generalize dependent W. generalize dependent U. induction t; simpl; intros; f_equal; auto.
  etransitivity. apply IHt. apply mu_term'_bind_ext. intros. destruct v; auto. simpl.
  etransitivity. apply mu_term'_bind_map_r. symmetry. etransitivity. apply mu_term'_bind_map_l.
  apply mu_term'_bind_ext. intros. auto.
Qed.

(* Actually, we only need to forbid (mu x. x) because of interpretation inexistence,
 * but in practice it's convenient to allow only constructor inside of binder
 * since all other legal mu-terms can be easily converted to the corresponding form
 *)
Inductive mu_term_wf' [V] : mu_term' V -> Prop :=
| VarMuWF' n : mu_term_wf' (VarMu' n)
| CstMuWF' n : mu_term_wf' (CstMu' n)
| ConMuWF' n l r : mu_term_wf' l -> mu_term_wf' r -> mu_term_wf' (ConMu' n l r)
| BndMuWF' n l r : mu_term_wf' (ConMu' n l r) -> mu_term_wf' (BndMu' (ConMu' n l r))
.

Lemma mu_term_wf'_ConMu_l [V] {n} {l r : mu_term' V}
                          (H : mu_term_wf' (ConMu' n l r))
                        : mu_term_wf' l.
Proof. inversion H. auto. Qed.

Lemma mu_term_wf'_ConMu_r [V] {n} {l r : mu_term' V}
                          (H : mu_term_wf' (ConMu' n l r))
                        : mu_term_wf' r.
Proof. inversion H. auto. Qed.

Lemma mu_term'_map_wf [V U : Set] (f : V -> U) {t} (H : mu_term_wf' t)
                    : mu_term_wf' (mu_term'_map f t).
Proof. generalize dependent U. induction H; simpl; intros; constructor; eauto. Qed.

Lemma mu_term'_bind_wf [V U : Set] (k : V -> mu_term' U) {t}
                       (H1 : forall n, mu_term_wf' (k n))
                       (H2 : mu_term_wf' t)
                     : mu_term_wf' (mu_term'_bind k t).
Proof.
  generalize dependent U. induction H2; simpl; intros; auto; constructor; auto.
  apply IHmu_term_wf'. intros. destruct n0; [ | constructor ]. apply mu_term'_map_wf. auto.
Qed.

Definition mu_unfold_step'_k [V : Set] (t : mu_term' (option V)) (n : option V) : mu_term' V :=
match n with
| None => BndMu' t
| Some n => VarMu' n
end.

Lemma mu_unfold_step'_k_bind [V U : Set] (k : V -> mu_term' U) (t1 : mu_term' (option V)) t2
                           : mu_term'_bind k (mu_term'_bind (mu_unfold_step'_k t1) t2)
                           = mu_term'_bind (mu_unfold_step'_k (mu_term'_bind (mu_term'_BndMu'_k k) t1))
                                           (mu_term'_bind (mu_term'_BndMu'_k k) t2).
Proof.
  etransitivity. apply mu_term'_bind_assoc. symmetry.
  etransitivity. apply mu_term'_bind_assoc. apply mu_term'_bind_ext.
  intros. clear t2 H. destruct v; auto. simpl.
  etransitivity. apply mu_term'_bind_map_r. symmetry.
  etransitivity. symmetry. apply mu_term'_bind_pure.
  apply mu_term'_bind_ext. intros. auto.
Qed.

Definition mu_unfold_step' [V : Set] (t : mu_term' (option V)) : mu_term' V :=
  mu_term'_bind (mu_unfold_step'_k t) t.

Lemma mu_unfold_step'_wf [V : Set] {t : mu_term' (option V)}
                         (H : mu_term_wf' (BndMu' t))
                       : mu_term_wf' (mu_unfold_step' t).
Proof.
  apply mu_term'_bind_wf.
  * intro. destruct n. constructor. auto.
  * inversion H. auto.
Qed.

Lemma mu_unfold_step_not_BndMu [V : Set] {t t' : mu_term' (option V)}
                               (H : mu_term_wf' (BndMu' t))
                             : mu_unfold_step' t <> BndMu' t'.
Proof. unfold mu_unfold_step'. good_inversion H. simpl. intro. inversion H. Qed.

Definition mu_unfold_hlp' (mu_unfold' : forall (t : mu_term' name), mu_term_wf' t -> inf_term)
                          t (t' : mu_term' name) (H1 : mu_unfold_step' t = t')
                          (H2 : mu_term_wf' (BndMu' t)) (H3 : mu_term_wf' t')
                        : inf_term :=
match t' as t'' return mu_term_wf' t'' -> mu_unfold_step' t = t'' -> _ with
| VarMu' n => fun _ _ => VarInf n
| CstMu' n => fun _ _ => CstInf n
| ConMu' n l r => fun H3 _ =>
  ConInf n (mu_unfold' l (mu_term_wf'_ConMu_l H3)) (mu_unfold' r (mu_term_wf'_ConMu_r H3))
| BndMu' t' => fun _ H1 => False_rec _ (mu_unfold_step_not_BndMu H2 H1)
end H3 H1.

CoFixpoint mu_unfold' (t : mu_term' name) (H : mu_term_wf' t) : inf_term :=
match t as t' return mu_term_wf' t' -> _ with
| VarMu' n => fun _ => VarInf n
| CstMu' n => fun _ => CstInf n
| ConMu' n l r => fun H =>
  ConInf n (mu_unfold' l (mu_term_wf'_ConMu_l H)) (mu_unfold' r (mu_term_wf'_ConMu_r H))
| BndMu' t => fun H => mu_unfold_hlp' mu_unfold' t _ eq_refl H (mu_unfold_step'_wf H)
end H.

CoFixpoint mu_unfold'_irrelevance t H1 H2 : inf_term_eq (mu_unfold' t H1) (mu_unfold' t H2) :=
rew <- [fun x => inf_term_eq x _] inf_term_step_prop (mu_unfold' t H1) in
rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (mu_unfold' t H2) in
match t as t'
return forall H1 H2, inf_term_eq (inf_term_step (mu_unfold' t' H1))
                                 (inf_term_step (mu_unfold' t' H2))
with
| VarMu' n => fun _ _ => VarInfEq n
| CstMu' n => fun _ _ => CstInfEq n
| ConMu' n l r => fun H1 H2 =>
  ConInfEq n _ _ _ _ (mu_unfold'_irrelevance _ _ _) (mu_unfold'_irrelevance _ _ _)
| BndMu' t => fun H1 H2 =>
  rew [fun x => inf_term_eq x _] inf_term_step_prop (mu_unfold_hlp' mu_unfold' t _ _ H1 _) in
  rew [fun x => inf_term_eq _ x] inf_term_step_prop (mu_unfold_hlp' mu_unfold' t _ _ H2 _) in
  match mu_unfold_step' t as t'
  return forall p H1' H2', inf_term_eq (mu_unfold_hlp' mu_unfold' t t' p H1 H1')
                                       (mu_unfold_hlp' mu_unfold' t t' p H2 H2')
  with
  | VarMu' n' => fun _ _ _ => VarInfEq n'
  | CstMu' n' => fun _ _ _ => CstInfEq n'
  | ConMu' n' l r => fun _ H1' H2' =>
    ConInfEq n' _ _ _ _ (mu_unfold'_irrelevance _ _ _) (mu_unfold'_irrelevance _ _ _)
  | BndMu' t' => fun p _ _ => False_ind _ (mu_unfold_step_not_BndMu H1 p)
  end eq_refl _ _
end H1 H2.

CoFixpoint mu_unfold'_bind k t (H1 : mu_term_wf' t)
                           (H2 : mu_term_wf' (mu_term'_bind k t))
                           (H3 : forall x, mu_term_wf' (k x))
                         : inf_term_eq (mu_unfold' (mu_term'_bind k t) H2)
                                       (apply_inf_subst (fun x => mu_unfold' (k x) (H3 x))
                                                        (mu_unfold' t H1)) :=
rew <- [fun x => inf_term_eq x _] inf_term_step_prop (mu_unfold' (mu_term'_bind k t) H2) in
rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (apply_inf_subst _ (mu_unfold' t H1)) in
match t as t'
return forall H1 H2, inf_term_eq (inf_term_step (mu_unfold' (mu_term'_bind k t') H2))
                                 (inf_term_step (apply_inf_subst (fun x => mu_unfold' (k x) (H3 x))
                                                                 (mu_unfold' t' H1)))
with
| VarMu' n => fun H1 H2 =>
  rew [fun x => inf_term_eq x _] inf_term_step_prop (mu_unfold' (k n) H2) in
  rew [fun x => inf_term_eq _ x] inf_term_step_prop (mu_unfold' (k n) (H3 n)) in
  mu_unfold'_irrelevance (k n) H2 (H3 n)
| CstMu' n => fun _ _ => CstInfEq n
| ConMu' n l r => fun H1 H2 =>
  ConInfEq n _ _ _ _ (mu_unfold'_bind k l _ _ _) (mu_unfold'_bind k r _ _ _)
| BndMu' (ConMu' n l r) => fun H1 H2 => ConInfEq n _ _ _ _
  ((
    rew [fun x => forall (H2 : mu_term_wf' x), inf_term_eq (mu_unfold' _ H2) _]
      mu_unfold_step'_k_bind k (ConMu' n l r) l
    in
    ((fun H2 => mu_unfold'_bind k _ _ H2 H3) : forall H2, inf_term_eq (mu_unfold' _ H2) _)
  ) _)
  ((
    rew [fun x => forall (H2 : mu_term_wf' x), inf_term_eq (mu_unfold' _ H2) _]
      mu_unfold_step'_k_bind k (ConMu' n l r) r
    in
    ((fun H2 => mu_unfold'_bind k _ _ H2 H3) : forall H2, inf_term_eq (mu_unfold' _ H2) _)
  ) _)
| BndMu' (VarMu' n) => fun H1 => False_rec _ (match H1 with end)
| BndMu' (CstMu' n) => fun H1 => False_rec _ (match H1 with end)
| BndMu' (BndMu' t) => fun H1 => False_rec _ (match H1 with end)
end H1 H2.

Corollary mu_unfold'_bind' k s t1 t2 (H1 : mu_term_wf' t1) (H2 : forall n, mu_term_wf' (k n))
                           (H3 : inf_term_eq (mu_unfold' t1 H1) t2)
                           (H4 : forall n, inf_term_eq (mu_unfold' (k n) (H2 n)) (s n))
                           (H5 : mu_term_wf' (mu_term'_bind k t1))
                         : inf_term_eq (mu_unfold' (mu_term'_bind k t1) H5) (apply_inf_subst s t2).
Proof.
  etransitivity. apply mu_unfold'_bind.
  etransitivity. apply apply_inf_subst_eq. eauto.
  apply apply_inf_subst_ext. intros. eauto.
Qed.

Inductive mu_term : Set :=
| VarMu : name -> mu_term
| CstMu : name -> mu_term
| ConMu : name -> mu_term -> mu_term -> mu_term
| BndMu : name -> mu_term -> mu_term
.

Definition mu_term_to_mu_term'_f (n n' : name) : option name :=
  if name_eq_dec n n' then None else Some n'.

Fixpoint mu_term_to_mu_term' (t : mu_term) : mu_term' name :=
match t with
| VarMu n => VarMu' n
| CstMu n => CstMu' n
| ConMu n l r => ConMu' n (mu_term_to_mu_term' l) (mu_term_to_mu_term' r)
| BndMu n t => BndMu' (mu_term'_map (mu_term_to_mu_term'_f n) (mu_term_to_mu_term' t))
end.

Fixpoint mu_term_fv (t : mu_term) : var_set :=
match t with
| VarMu x => [x]
| CstMu _ => []
| ConMu _ l r => var_set_union (mu_term_fv l) (mu_term_fv r)
| BndMu x t => var_set_remove x (mu_term_fv t)
end.

Lemma mu_term_fv_distinct t : NoDup (mu_term_fv t).
Proof.
  induction t; repeat constructor; auto.
  * apply set_union_nodup; auto.
  * apply set_remove_nodup. auto.
Qed.

Lemma mu_term_fv_prop t n : In n (mu_term_fv t) <-> In n (mu_term'_fv (mu_term_to_mu_term' t)).
Proof.
  induction t; simpl; try reflexivity.
  * constructor; intro.
    - apply in_app_iff. apply set_union_elim in H.
      destruct H. apply IHt1 in H. auto. apply IHt2 in H. auto.
    - apply in_app_iff in H. apply set_union_intro.
      destruct H. apply IHt1 in H. auto. apply IHt2 in H. auto.
  * constructor; intro.
    - apply set_remove_iff in H; [ | apply mu_term_fv_distinct ]. destruct H.
      apply map_filter_In. apply IHt in H. exists (Some n). constructor; auto.
      rewrite mu_term'_map_fv. apply in_map_iff. eexists. constructor; eauto.
      unfold mu_term_to_mu_term'_f. destruct (name_eq_dec n0 n); auto. exfalso. apply H0. auto.
    - apply set_remove_iff. apply mu_term_fv_distinct. apply map_filter_In in H.
      destruct H as [ x [ H1 H2 ] ]. unfold id in H2. subst x.
      rewrite mu_term'_map_fv in H1. apply in_map_iff in H1.
      destruct H1 as [ x [ H1 H2 ] ]. unfold mu_term_to_mu_term'_f in H1.
      destruct (name_eq_dec n0 x); good_inversion H1. constructor; auto.
      apply IHt. auto.
Qed.

Definition mu_term_wf (t : mu_term) : Prop := mu_term_wf' (mu_term_to_mu_term' t).

Definition mu_unfold (t : mu_term) (H : mu_term_wf t) : inf_term :=
  mu_unfold' (mu_term_to_mu_term' t) H.

Lemma mu_unfold_irrelevance t H1 H2 : inf_term_eq (mu_unfold t H1) (mu_unfold t H2).
Proof. apply mu_unfold'_irrelevance. Qed.
