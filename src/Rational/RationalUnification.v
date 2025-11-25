From Stdlib Require Import List.
Import ListNotations.

Require Import Unification.
Require Import RationalTerm.

Definition eqsys := list (name * term).

Fixpoint eqsys_lookup (s : eqsys) (x : name) : option term :=
match s with
| [] => None
| (y, t) :: s =>
  if name_eq_dec x y then Some t
  else eqsys_lookup s x
end.

Definition in_eqsys_dom (s : eqsys) (x : name) := exists t, eqsys_lookup s x = Some t.

Fixpoint eqsys_dom (s : eqsys) : var_set :=
match s with
| [] => var_set_empty
| (x, _) :: s => var_set_add x (eqsys_dom s)
end.

Lemma eqsys_dom_spec s x : In x (eqsys_dom s) <-> in_eqsys_dom s x.
Proof.
  constructor; intro.
  * induction s as [ | [ y t ] s IH ]. inversion H. simpl in H.
    apply ListSet.set_add_elim in H. unfold in_eqsys_dom. simpl.
    destruct (name_eq_dec x y).
    - exists t. auto.
    - destruct H. subst y. contradiction. destruct IH as [ t' IH ]. apply H. exists t'. auto.
  * induction s as [ | [ y t ] s IH ]. destruct H as [ t H ]. inversion H.
    destruct H as [ t' H ]. simpl in H. destruct (name_eq_dec x y).
    - apply ListSet.set_add_intro2. auto.
    - apply ListSet.set_add_intro1. apply IH. exists t'. auto.
Qed.

Lemma eqsys_dom_nodup s : NoDup (eqsys_dom s).
Proof.
  induction s as [ | [ x t ] s IH ]. constructor.
  apply ListSet.set_add_nodup. auto.
Qed.

Lemma var_set_add_incl x xs : incl (var_set_add x xs) (x :: xs).
Proof. intros y H. apply ListSet.set_add_elim in H. destruct H. left. auto. right. auto. Qed.

Lemma eqsys_dom_size s : length (eqsys_dom s) <= length s.
Proof.
  induction s as [ | [ x t ] s IH ]. auto. simpl. transitivity (length (x :: eqsys_dom s)).
  * apply NoDup_incl_length. apply ListSet.set_add_nodup. apply eqsys_dom_nodup.
    apply var_set_add_incl.
  * apply le_n_S. auto.
Qed.

Definition eqsys_dom_erase (s : eqsys) (x : name) : eqsys :=
  filter (fun p => if name_eq_dec x (fst p) then false else true) s.

Lemma eqsys_dom_erase_none s x : eqsys_lookup (eqsys_dom_erase s x) x = None.
Proof.
  induction s as [ | [ z t ] s IH ]. auto. simpl.
  remember (name_eq_dec x z) as cond. destruct cond. auto. simpl. rewrite <- Heqcond. auto.
Qed.

Lemma eqsys_dom_erase_same s x y (H : x <> y) : eqsys_lookup (eqsys_dom_erase s x) y = eqsys_lookup s y.
Proof.
  induction s as [ | [ z t ] s IH ]. auto. simpl.
  destruct (name_eq_dec x z).
  * rewrite IH. destruct (name_eq_dec y z). subst y z. contradiction. auto.
  * simpl. destruct (name_eq_dec y z); auto.
Qed.

Fixpoint term_subterms (t : term) : list term :=
match t with
| Var _ => [t]
| Cst _ => [t]
| Con f l r => t :: term_subterms l ++ term_subterms r
end.

Lemma term_subterms_self t : In t (term_subterms t).
Proof. induction t; left; auto. Qed.

Lemma term_subterms_incl t1 t2 (H : In t1 (term_subterms t2)) : incl (term_subterms t1) (term_subterms t2).
Proof.
  induction t2; simpl in H.
  * destruct H. subst. apply incl_refl. inversion H.
  * destruct H. subst. apply incl_refl. inversion H.
  * destruct H. subst. apply incl_refl. apply in_app_or in H. simpl. apply incl_tl. destruct H.
    - apply incl_appl. auto.
    - apply incl_appr. auto.
Qed.

Definition in_eqsys_rhs (s : eqsys) (t : term) := exists x, eqsys_lookup s x = Some t.

Fixpoint eqsys_rhs (s : eqsys) : list term :=
match s with
| [] => []
| (_, t) :: s => t :: eqsys_rhs s
end.

Lemma eqsys_rhs_in s t (H : in_eqsys_rhs s t) : In t (eqsys_rhs s).
Proof.
  destruct H as [ x H ]. induction s as [ | [ y t' ] s ]. inversion H.
  simpl in H. destruct (name_eq_dec x y). good_inversion H. simpl. left. auto.
  simpl. right. auto.
Qed.

Example eqsys_rhs_not_in : ~(forall s t, In t (eqsys_rhs s) -> in_eqsys_rhs s t).
Proof.
  intro. specialize (H [(1, Cst 1); (1, Cst 2)] (Cst 2)).
  destruct H as [ x H ]. simpl. auto. simpl in H. destruct (name_eq_dec x 1); inversion H.
Qed.

Definition eqsys_subterms (s : eqsys) : list term := flat_map term_subterms (eqsys_rhs s).

Lemma eqsys_rhs_subterms s t : In t (eqsys_subterms s)
                           <-> (exists t', In t' (eqsys_rhs s) /\ In t (term_subterms t')).
Proof. apply in_flat_map. Qed.

Inductive eqsys_walk_result (s : eqsys) : name -> name * term -> Prop :=
| ESWalkVar x : eqsys_lookup s x = None -> eqsys_walk_result s x (x, Var x)
| ESWalkWalk x y r : eqsys_lookup s x = Some (Var y) -> eqsys_walk_result s y r -> eqsys_walk_result s x r
| ESWalkCst x c : eqsys_lookup s x = Some (Cst c) -> eqsys_walk_result s x (x, Cst c)
| ESWalkCon x f l r : eqsys_lookup s x = Some (Con f l r) -> eqsys_walk_result s x (x, Con f l r)
.

Lemma eqsys_walk_result_inj s x r1 r2 (H1 : eqsys_walk_result s x r1) (H2 : eqsys_walk_result s x r2) : r1 = r2.
Proof. revert r2 H2. induction H1; intros; good_inversion H2; rewrite H in H0; good_inversion H0; auto. Qed.

Fixpoint eqsys_walk_hlp (fuel : nat) (s : eqsys) (x : name) : name * term :=
match fuel with
| 0 => (x, Var x)
| S fuel =>
  match eqsys_lookup s x with
  | None => (x, Var x)
  | Some (Var y) => eqsys_walk_hlp fuel s y
  | Some t => (x, t)
  end
end.

Inductive eqsys_walk_path (s : eqsys) : name -> list name -> Prop :=
| ESWalkPathVar x : eqsys_lookup s x = None -> eqsys_walk_path s x []
| ESWalkPathWalk x y p : eqsys_lookup s x = Some (Var y) -> eqsys_walk_path s y p -> eqsys_walk_path s x (x :: p)
| ESWalkPathCst x c : eqsys_lookup s x = Some (Cst c) -> eqsys_walk_path s x [x]
| ESWalkPathCon x f l r : eqsys_lookup s x = Some (Con f l r) -> eqsys_walk_path s x [x]
.

Lemma eqsys_walk_path_inj s x p1 p2 (H1 : eqsys_walk_path s x p1) (H2 : eqsys_walk_path s x p2) : p1 = p2.
Proof.
  revert p2 H2. induction H1; intros; good_inversion H2; auto; rewrite H in H0; good_inversion H0.
  f_equal. auto.
Qed.

Lemma eqsys_walk_path_split s x y p1 p2 (H : eqsys_walk_path s x (p1 ++ y :: p2)) : eqsys_walk_path s y (y :: p2).
Proof.
  remember (p1 ++ y :: p2) as p. revert y p1 p2 Heqp. induction H; intros.
  * symmetry in Heqp. apply app_eq_nil in Heqp. destruct Heqp. inversion H1.
  * destruct p1 as [ | x' p1 ]; good_inversion Heqp.
    - econstructor. eauto. auto.
    - eapply IHeqsys_walk_path. reflexivity.
  * destruct p1 as [ | x' p1 ]; good_inversion Heqp.
    - eapply ESWalkPathCst. eauto.
    - symmetry in H2. apply app_eq_nil in H2. destruct H2. inversion H1.
  * destruct p1 as [ | x' p1 ]; good_inversion Heqp.
    - eapply ESWalkPathCon. eauto.
    - symmetry in H2. apply app_eq_nil in H2. destruct H2. inversion H1.
Qed.

Polymorphic Lemma singleton_nodup {A : Type} (x : A) : NoDup [x].
Proof. constructor. intro. inversion H. constructor. Qed.

Lemma eqsys_walk_path_nodup s x p (H : eqsys_walk_path s x p) : NoDup p.
Proof.
  induction H. constructor. 2, 3: apply singleton_nodup.
  constructor; auto. intro. apply in_split in H1. destruct H1 as [ p1 [ p2 H1 ] ].
  set (H2 := H0). rewrite H1 in H2. apply eqsys_walk_path_split in H2.
  eapply eqsys_walk_path_inj in H2. 2: { eapply ESWalkPathWalk. eauto. eauto. }
  good_inversion H2. rewrite (app_assoc p1 [x] p2 : p1 ++ x :: p2 = _) in H4.
  apply (app_inv_tail p2 _ []) in H4. apply app_eq_nil in H4. destruct H4. inversion H2.
Qed.

Polymorphic Lemma singleton_incl {A : Type} (x : A) (xs : list A) (H : In x xs) : incl [x] xs.
Proof. apply incl_cons. auto. apply incl_nil_l. Qed.

Lemma eqsys_walk_path_in_dom s x p (H : eqsys_walk_path s x p) : incl p (eqsys_dom s).
Proof.
  induction H.
  * apply incl_nil_l.
  * apply incl_cons; auto. apply eqsys_dom_spec. eexists. eauto.
  * apply singleton_incl. apply eqsys_dom_spec. eexists. eauto.
  * apply singleton_incl. apply eqsys_dom_spec. eexists. eauto.
Qed.

Lemma eqsys_walk_hlp_path s x p fuel (H1 : eqsys_walk_path s x p) (H2 : length p <= fuel)
                        : eqsys_walk_result s x (eqsys_walk_hlp fuel s x).
Proof.
   revert fuel H2. induction H1; intros.
   * destruct fuel. constructor. auto. simpl. rewrite H. constructor. auto.
   * destruct fuel. inversion H2. simpl. rewrite H. econstructor. eauto.
     apply IHeqsys_walk_path. apply le_S_n. auto.
   * destruct fuel. inversion H2. simpl. rewrite H. constructor. auto.
   * destruct fuel. inversion H2. simpl. rewrite H. constructor. auto.
Qed.

Definition eqsys_walkable (s : eqsys) (x : name) : Prop := exists r, eqsys_walk_result s x r.

Lemma eqsys_walkable_path s x (H : eqsys_walkable s x) : exists p, eqsys_walk_path s x p.
Proof.
  destruct H as [ r H ]. induction H.
  * exists []. constructor. auto.
  * destruct IHeqsys_walk_result as [ p IH ]. exists (x :: p). econstructor; eauto.
  * exists [x]. eapply ESWalkPathCst. eauto.
  * exists [x]. eapply ESWalkPathCon. eauto.
Qed.

Lemma eqsys_walk_aux s x (H : eqsys_walkable s x) : { r | eqsys_walk_result s x r }.
Proof.
  exists (eqsys_walk_hlp (length s) s x). apply eqsys_walkable_path in H. destruct H as [ p H ].
  eapply eqsys_walk_hlp_path. eauto. transitivity (length (eqsys_dom s)).
  2: apply eqsys_dom_size. apply NoDup_incl_length. eapply eqsys_walk_path_nodup. eauto.
  eapply eqsys_walk_path_in_dom. eauto.
Qed.

Definition eqsys_well_formed (s : eqsys) : Prop := forall x, eqsys_walkable s x.

Definition wf_eqsys : Set := { s | eqsys_well_formed s }.

Definition wf_eqsys_get (s : wf_eqsys) : eqsys := proj1_sig s.

Fact wf_eqsys_get_well_formed (s : wf_eqsys) : eqsys_well_formed (wf_eqsys_get s).
Proof. unfold wf_eqsys_get. apply proj2_sig. Qed.

Definition wf_eqsys_walk (s : wf_eqsys) (x : name) : name * term :=
  proj1_sig (eqsys_walk_aux (wf_eqsys_get s) x (wf_eqsys_get_well_formed s x)).

Fact wf_eqsys_walk_prop s x : eqsys_walk_result (wf_eqsys_get s) x (wf_eqsys_walk s x).
Proof. unfold wf_eqsys_walk. destruct eqsys_walk_aux. auto. Qed.

Lemma wf_eqsys_walk_var s x y z (H : wf_eqsys_walk s x = (y, Var z)) : y = z.
Proof.
  specialize (wf_eqsys_walk_prop s x). intro H1. rewrite H in H1.
  remember (y, Var z) as r. revert y z Heqr. induction H1; intros.
  * good_inversion Heqr. auto.
  * apply IHeqsys_walk_result; auto. eapply eqsys_walk_result_inj; eauto.
    apply wf_eqsys_walk_prop.
  * inversion Heqr.
  * inversion Heqr.
Qed.

Lemma wf_eqsys_walk_idemp s x : wf_eqsys_walk s x = wf_eqsys_walk s (fst (wf_eqsys_walk s x)).
Proof.
  specialize (wf_eqsys_walk_prop s x). intro H. remember (wf_eqsys_walk s x) as r.
  induction H; simpl; auto. apply IHeqsys_walk_result.
  eapply eqsys_walk_result_inj. eauto. apply wf_eqsys_walk_prop.
Qed.

Corollary wf_eqsys_walk_fst_inj s x1 x2 y t1 t2
                            (H1 : wf_eqsys_walk s x1 = (y, t1))
                            (H2 : wf_eqsys_walk s x2 = (y, t2))
                          : t1 = t2.
Proof.
  set (H1' := H1). rewrite wf_eqsys_walk_idemp in H1'. rewrite H1 in H1'. simpl in H1'.
  set (H2' := H2). rewrite wf_eqsys_walk_idemp in H2'. rewrite H2 in H2'. simpl in H2'.
  rewrite H2' in H1'. good_inversion H1'. auto.
Qed.

Lemma wf_eqsys_walk_rhs s x : In (snd (wf_eqsys_walk s x)) (eqsys_rhs (wf_eqsys_get s))
                           \/ exists y, wf_eqsys_walk s x = (y, Var y).
Proof.
  specialize (wf_eqsys_walk_prop s x). intro H. remember (wf_eqsys_walk s x) as r.
  induction H; simpl.
  * right. eexists. auto.
  * apply IHeqsys_walk_result. eapply eqsys_walk_result_inj. eauto. apply wf_eqsys_walk_prop.
  * left. apply eqsys_rhs_in. eexists. eauto.
  * left. apply eqsys_rhs_in. eexists. eauto.
Qed.

CoFixpoint wf_eqsys_image_hlp (s : wf_eqsys) (t : term) :=
match t with
| Var x =>
    match wf_eqsys_walk s x with
    | (_, Var x) => InfVar x
    | (_, Cst c) => InfCst c
    | (_, Con f l r) => InfCon f (wf_eqsys_image_hlp s l) (wf_eqsys_image_hlp s r)
    end
| Cst c => InfCst c
| Con f l r => InfCon f (wf_eqsys_image_hlp s l) (wf_eqsys_image_hlp s r)
end.

Lemma wf_eqsys_image_hlp_step s x : inf_term_eq (wf_eqsys_image_hlp s (Var x))
                                                (wf_eqsys_image_hlp s (snd (wf_eqsys_walk s x))).
Proof.
  remember (wf_eqsys_walk s x) as r. destruct r as [ y t ].
  rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl. rewrite <- Heqr.
  destruct t; try reflexivity. symmetry in Heqr.
  set (H := Heqr). apply wf_eqsys_walk_var in H. subst n.
  set (H := Heqr). rewrite wf_eqsys_walk_idemp in H. rewrite Heqr in H.
  simpl in H. rewrite H. reflexivity.
Qed.

Polymorphic Lemma in_incl_trans {A : Type} (x : A) (xs ys : list A) (H1 : In x xs) (H2 : incl xs ys) : In x ys.
Proof. auto. Qed.

Lemma wf_eqsys_image_hlp_subterm s t l (H : inf_subterm (wf_eqsys_image_hlp s t) l)
  : exists r, inf_term_eq l (wf_eqsys_image_hlp s r)
 /\ (In r (term_subterms t) \/ In r (eqsys_subterms (wf_eqsys_get s))).
Proof.
  destruct H as [ p H ]. remember (wf_eqsys_image_hlp s t) as t'.
  revert t Heqt'. induction H; intros t' Heqt'.
  * subst t. eexists. constructor. reflexivity. left. apply term_subterms_self.
  * destruct t'; rewrite inf_term_step_prop in Heqt'; good_inversion Heqt'.
    - remember (wf_eqsys_walk s n) as res. destruct res as [ y t' ].
      destruct t'; good_inversion H1. edestruct IHinf_path_to as [ r [ IH1 IH2 ] ]. reflexivity.
      exists r. constructor. auto. destruct IH2; auto. right. apply eqsys_rhs_subterms.
      exists (Con n0 t'1 t'2). constructor. specialize (wf_eqsys_walk_rhs s n). intro.
      destruct H1. 2: { destruct H1 as [ n' H1 ]. rewrite H1 in Heqres. inversion Heqres. }
      rewrite <- Heqres in H1. auto. eapply in_incl_trans. eauto. apply term_subterms_incl.
      simpl. right. apply in_or_app. left. apply term_subterms_self.
    - edestruct IHinf_path_to as [ r [ IH1 IH2 ] ]. reflexivity. exists r. constructor. auto.
      destruct IH2; auto. left. simpl. right. apply in_or_app. auto.
  * destruct t'; rewrite inf_term_step_prop in Heqt'; good_inversion Heqt'.
    - remember (wf_eqsys_walk s n) as res. destruct res as [ y t' ].
      destruct t'; good_inversion H1. edestruct IHinf_path_to as [ r [ IH1 IH2 ] ]. reflexivity.
      exists r. constructor. auto. destruct IH2; auto. right. apply eqsys_rhs_subterms.
      exists (Con n0 t'1 t'2). constructor. specialize (wf_eqsys_walk_rhs s n). intro.
      destruct H1. 2: { destruct H1 as [ n' H1 ]. rewrite H1 in Heqres. inversion Heqres. }
      rewrite <- Heqres in H1. auto. eapply in_incl_trans. eauto. apply term_subterms_incl.
      simpl. right. apply in_or_app. right. apply term_subterms_self.
    - edestruct IHinf_path_to as [ r [ IH1 IH2 ] ]. reflexivity. exists r. constructor. auto.
      destruct IH2; auto. left. simpl. right. apply in_or_app. auto.
Qed.

Definition wf_eqsys_image (s : wf_eqsys) (x : name) := wf_eqsys_image_hlp s (Var x).

Fixpoint wf_eqsys_apply (s : wf_eqsys) (t : term) :=
match t with
| Var x => wf_eqsys_image s x
| Cst c => InfCst c
| Con f l r => InfCon f (wf_eqsys_apply s l) (wf_eqsys_apply s r)
end.

Lemma wf_eqsys_image_hlp_apply s t : inf_term_eq (wf_eqsys_image_hlp s t) (wf_eqsys_apply s t).
Proof.
  induction t; rewrite inf_term_step_prop at 1; simpl.
  * rewrite inf_term_step_prop. simpl. reflexivity.
  * reflexivity.
  * apply inf_term_eq_con; auto.
Qed.

Lemma wf_eqsys_apply_var s x : inf_term_eq (wf_eqsys_image s x) (wf_eqsys_apply s (snd (wf_eqsys_walk s x))).
Proof. etransitivity. apply wf_eqsys_image_hlp_step. apply wf_eqsys_image_hlp_apply. Qed.

Definition wf_eqsys_inf_subterms (s : wf_eqsys) : list inf_term :=
  map (wf_eqsys_apply s) (eqsys_subterms (wf_eqsys_get s)).

Theorem wf_eqsys_image_rational s x : is_rational_term (wf_eqsys_image s x).
Proof.
  exists (InfVar (fst (wf_eqsys_walk s x)) :: wf_eqsys_inf_subterms s). intros.
  apply wf_eqsys_image_hlp_subterm in H. simpl in H.
  destruct H as [ r [ H1 H2 ] ]. destruct H2.
  * destruct H. 2: inversion H. subst. exists (wf_eqsys_apply s (snd (wf_eqsys_walk s x))).
    constructor. etransitivity. eauto. apply wf_eqsys_apply_var. destruct (wf_eqsys_walk_rhs s x).
    - right. apply in_map. eapply in_incl_trans. eauto. intros t Ht. apply eqsys_rhs_subterms.
      exists t. constructor. auto. apply term_subterms_self.
    - left. destruct H as [ y H ]. rewrite H. simpl. rewrite inf_term_step_prop. simpl.
      set (H' := H). rewrite wf_eqsys_walk_idemp in H'. rewrite H in H'. simpl in H'.
      rewrite H'. auto.
  * exists (wf_eqsys_apply s r). constructor.
    - etransitivity. eauto. apply wf_eqsys_image_hlp_apply.
    - right. apply in_map. auto.
Qed.

Corollary wf_eqsys_apply_rational s t : is_rational_term (wf_eqsys_apply s t).
Proof.
  induction t.
  * apply wf_eqsys_image_rational.
  * exists [InfCst n]. intros. destruct H as [ p H ]. good_inversion H.
    exists (InfCst n). constructor. reflexivity. left. auto.
  * destruct IHt1 as [ ts1 IH1 ]. destruct IHt2 as [ ts2 IH2 ].
    exists (InfCon n (wf_eqsys_apply s t1) (wf_eqsys_apply s t2) :: ts1 ++ ts2). intros.
    destruct H as [ p H ]. good_inversion H.
    - eexists. constructor. reflexivity. left. auto.
    - assert (exists p, inf_path_to (wf_eqsys_apply s t1) p l). exists p0. auto.
      apply IH1 in H. destruct H as [ r [ H1 H2 ] ]. exists r. constructor; auto.
      right. apply in_or_app. left. auto.
    - assert (exists p, inf_path_to (wf_eqsys_apply s t2) p l). exists p0. auto.
      apply IH2 in H. destruct H as [ r [ H1 H2 ] ]. exists r. constructor; auto.
      right. apply in_or_app. right. auto.
Qed.
