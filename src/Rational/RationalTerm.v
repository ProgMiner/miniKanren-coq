From Stdlib Require Import List.
Import ListNotations.

Require Import Unification.

CoInductive inf_term : Set :=
| InfVar : name -> inf_term
| InfCst : name -> inf_term
| InfCon : name -> inf_term -> inf_term -> inf_term
.

Definition inf_term_step (t : inf_term) : inf_term :=
match t with
| InfVar x => InfVar x
| InfCst c => InfCst c
| InfCon f l r => InfCon f l r
end.

Lemma inf_term_step_prop t : t = inf_term_step t.
Proof. intros. destruct t; reflexivity. Qed.

Fixpoint term_to_inf (t : term) : inf_term :=
match t with
| Var x => InfVar x
| Cst c => InfCst c
| Con f l r => InfCon f (term_to_inf l) (term_to_inf r)
end.

Inductive path : Set :=
| Here : path
| Left : path -> path
| Right : path -> path
.

Inductive inf_path_to : inf_term -> path -> inf_term -> Prop :=
| InfHere t : inf_path_to t Here t
| InfLeft f l r p t : inf_path_to l p t -> inf_path_to (InfCon f l r) (Left p) t
| InfRight f l r p t : inf_path_to r p t -> inf_path_to (InfCon f l r) (Right p) t
.

Lemma inf_path_to_inj t p t1 t2 (H : inf_path_to t p t1) : inf_path_to t p t2 -> t1 = t2.
Proof. induction H; intro H'; inversion H'; subst; auto. Qed.

Definition inf_term_eq_node (l r : inf_term) : Prop :=
match l, r with
| InfVar l, InfVar r => l = r
| InfCst l, InfCst r => l = r
| InfCon l _ _, InfCon r _ _ => l = r
| _, _ => False
end.

Instance inf_term_eq_node_refl : RelationClasses.Reflexive inf_term_eq_node.
Proof. intro t. destruct t; simpl; auto. Qed.

Instance inf_term_eq_node_sym : RelationClasses.Symmetric inf_term_eq_node.
Proof. intros l r. destruct l; destruct r; simpl; auto. Qed.

Instance inf_term_eq_node_trans : RelationClasses.Transitive inf_term_eq_node.
Proof.
  intros a b c H1 H2.
  destruct a; destruct b; destruct c; good_inversion H1; good_inversion H2; simpl; auto.
Qed.

Instance inf_term_eq_node_equiv : RelationClasses.Equivalence inf_term_eq_node :=
  RelationClasses.Build_Equivalence _ _ _ _.

Definition inf_term_eq (l r : inf_term) : Prop :=
  forall p l', inf_path_to l p l' -> exists r', inf_path_to r p r' /\ inf_term_eq_node l' r'.

Lemma inf_term_eq_con n l1 l2 r1 r2 (H1 : inf_term_eq l1 l2) (H2 : inf_term_eq r1 r2)
                    : inf_term_eq (InfCon n l1 r1) (InfCon n l2 r2).
Proof.
  intros p l' Hp. good_inversion Hp.
  * eexists. constructor. constructor. reflexivity.
  * apply H1 in H6. destruct H6 as [ r' [ H1_1 H1_2 ] ]. exists r'. constructor; auto. constructor. auto.
  * apply H2 in H6. destruct H6 as [ r' [ H2_1 H2_2 ] ]. exists r'. constructor; auto. constructor. auto.
Qed.

Lemma inf_term_eq_conl n1 n2 l1 l2 r1 r2 (H : inf_term_eq (InfCon n1 l1 r1) (InfCon n2 l2 r2))
                     : inf_term_eq l1 l2.
Proof.
  intros p l1' Hp. destruct (H (Left p) l1') as [ r [ H1 H2 ] ]. constructor. auto.
  exists r. good_inversion H1. constructor; auto.
Qed.

Lemma inf_term_eq_conr n1 n2 l1 l2 r1 r2 (H : inf_term_eq (InfCon n1 l1 r1) (InfCon n2 l2 r2))
                     : inf_term_eq r1 r2.
Proof.
  intros p r1' Hp. destruct (H (Right p) r1') as [ r [ H1 H2 ] ]. constructor. auto.
  exists r. good_inversion H1. constructor; auto.
Qed.

Instance inf_term_eq_refl : RelationClasses.Reflexive inf_term_eq.
Proof.
  intros t p l' H. induction H.
  * exists t. constructor. constructor. reflexivity.
  * destruct IHinf_path_to as [ r' [ IH1 IH2 ] ]. exists r'. constructor; auto. constructor. auto.
  * destruct IHinf_path_to as [ r' [ IH1 IH2 ] ]. exists r'. constructor; auto. constructor. auto.
Qed.

Instance inf_term_eq_sym : RelationClasses.Symmetric inf_term_eq.
Proof.
  intros l r H p r' Hp. revert l H. induction Hp.
  * intros. edestruct H as [ l' [ H1 H2 ] ]. constructor. good_inversion H1.
    exists l. constructor. constructor. symmetry. auto.
  * rename l into rl. rename r into rr. rename t into rl'. intros l H. destruct l.
    - edestruct (H Here) as [ l' [ H1 H2 ] ]. constructor. good_inversion H1. inversion H2.
    - edestruct (H Here) as [ l' [ H1 H2 ] ]. constructor. good_inversion H1. inversion H2.
    - edestruct (H Here) as [ l' [ H1 H2 ] ]. constructor. good_inversion H1. good_inversion H2.
      rename l1 into ll. rename l2 into lr. edestruct (IHHp ll) as [ ll' [ H1 H2 ] ].
      + intros q ll' Hq. destruct (H (Left q) ll') as [ r' [ H1 H2 ] ]. constructor. auto.
        exists r'. constructor; auto. good_inversion H1. auto.
      + exists ll'. constructor; auto. constructor. auto.
  * rename l into rl. rename r into rr. rename t into rr'. intros l H. destruct l.
    - edestruct (H Here) as [ l' [ H1 H2 ] ]. constructor. good_inversion H1. inversion H2.
    - edestruct (H Here) as [ l' [ H1 H2 ] ]. constructor. good_inversion H1. inversion H2.
    - edestruct (H Here) as [ l' [ H1 H2 ] ]. constructor. good_inversion H1. good_inversion H2.
      rename l1 into ll. rename l2 into lr. edestruct (IHHp lr) as [ lr' [ H1 H2 ] ].
      + intros q lr' Hq. destruct (H (Right q) lr') as [ r' [ H1 H2 ] ]. constructor. auto.
        exists r'. constructor; auto. good_inversion H1. auto.
      + exists lr'. constructor; auto. constructor. auto.
Qed.

Instance inf_term_eq_trans : RelationClasses.Transitive inf_term_eq.
Proof.
  intros a b c H1 H2 p a' Hp. revert b c H1 H2. induction Hp.
  * intros. rename t into a.
    destruct (H1 Here a) as [ b' [ H1_1 H1_2 ] ]. constructor. good_inversion H1_1.
    destruct (H2 Here b') as [ c' [ H2_1 H2_2 ] ]. constructor. good_inversion H2_1.
    exists c'. constructor. constructor. etransitivity; eauto.
  * intros b c H1 H2. destruct b. 3: destruct c.
    - edestruct (H1 Here) as [ a' [ H1_1 H1_2 ] ]. constructor. good_inversion H1_1. inversion H1_2.
    - edestruct (H1 Here) as [ a' [ H1_1 H1_2 ] ]. constructor. good_inversion H1_1. inversion H1_2.
    - edestruct (H2 Here) as [ b' [ H2_1 H2_2 ] ]. constructor. good_inversion H2_1. inversion H2_2.
    - edestruct (H2 Here) as [ b' [ H2_1 H2_2 ] ]. constructor. good_inversion H2_1. inversion H2_2.
    - rename f into af. rename l into al. rename r into ar.
      rename n into bf. rename b1 into bl. rename b2 into br.
      rename n0 into cf. rename c1 into cl. rename c2 into cr.
      destruct (IHHp bl cl) as [ cl' [ IH1 IH2 ] ].
      + intros q al' Hq. destruct (H1 (Left q) al') as [ bl' [ H1_1 H1_2 ] ]. constructor. auto.
        exists bl'. constructor; auto. good_inversion H1_1. auto.
      + intros q bl' Hq. destruct (H2 (Left q) bl') as [ cl' [ H2_1 H2_2 ] ]. constructor. auto.
        exists cl'. constructor; auto. good_inversion H2_1. auto.
      + exists cl'. constructor; auto. constructor. auto.
  * intros b c H1 H2. destruct b. 3: destruct c.
    - edestruct (H1 Here) as [ a' [ H1_1 H1_2 ] ]. constructor. good_inversion H1_1. inversion H1_2.
    - edestruct (H1 Here) as [ a' [ H1_1 H1_2 ] ]. constructor. good_inversion H1_1. inversion H1_2.
    - edestruct (H2 Here) as [ b' [ H2_1 H2_2 ] ]. constructor. good_inversion H2_1. inversion H2_2.
    - edestruct (H2 Here) as [ b' [ H2_1 H2_2 ] ]. constructor. good_inversion H2_1. inversion H2_2.
    - rename f into af. rename l into al. rename r into ar.
      rename n into bf. rename b1 into bl. rename b2 into br.
      rename n0 into cf. rename c1 into cl. rename c2 into cr.
      destruct (IHHp br cr) as [ cr' [ IH1 IH2 ] ].
      + intros q ar' Hq. destruct (H1 (Right q) ar') as [ br' [ H1_1 H1_2 ] ]. constructor. auto.
        exists br'. constructor; auto. good_inversion H1_1. auto.
      + intros q br' Hq. destruct (H2 (Right q) br') as [ cr' [ H2_1 H2_2 ] ]. constructor. auto.
        exists cr'. constructor; auto. good_inversion H2_1. auto.
      + exists cr'. constructor; auto. constructor. auto.
Qed.

Lemma inf_path_to_eq p l1 l2 r1 r2 (H1 : inf_term_eq l1 l2) (H2 : inf_term_eq r1 r2)
                     (H3 : inf_path_to l1 p r1)
                   : exists t, inf_path_to l2 p t /\ inf_term_eq t r2.
Proof.
  revert l2 r2 H1 H2. induction H3; intros.
  * exists l2. constructor. constructor. etransitivity. symmetry. eauto. auto.
  * destruct l2 as [ | | f' l' r' ].
    - edestruct (H1 Here). constructor. destruct H. good_inversion H. inversion H0.
    - edestruct (H1 Here). constructor. destruct H. good_inversion H. inversion H0.
    - edestruct IHinf_path_to as [ t' [ IH1 IH2 ] ]. eapply inf_term_eq_conl. eauto. eauto.
      exists t'. constructor; auto. constructor. auto.
  * destruct l2 as [ | | f' l' r' ].
    - edestruct (H1 Here). constructor. destruct H. good_inversion H. inversion H0.
    - edestruct (H1 Here). constructor. destruct H. good_inversion H. inversion H0.
    - edestruct IHinf_path_to as [ t' [ IH1 IH2 ] ]. eapply inf_term_eq_conr. eauto. eauto.
      exists t'. constructor; auto. constructor. auto.
Qed.

Instance inf_term_eq_equiv : RelationClasses.Equivalence inf_term_eq :=
  RelationClasses.Build_Equivalence _ _ _ _.

Lemma term_to_inf_inj t1 t2 (H : inf_term_eq (term_to_inf t1) (term_to_inf t2)) : t1 = t2.
Proof.
  revert t2 H. induction t1; intros.
  * edestruct (H Here) as [ t' [ H1 H2 ] ]. constructor.
    good_inversion H1. destruct t2; good_inversion H2. auto.
  * edestruct (H Here) as [ t' [ H1 H2 ] ]. constructor.
    good_inversion H1. destruct t2; good_inversion H2. auto.
  * edestruct (H Here) as [ t' [ H1 H2 ] ]. constructor.
    good_inversion H1. destruct t2; good_inversion H2. f_equal.
    - apply IHt1_1. eapply inf_term_eq_conl. eauto.
    - apply IHt1_2. eapply inf_term_eq_conr. eauto.
Qed.

Definition inf_subterm (l r : inf_term) := exists p, inf_path_to l p r.

Instance inf_subterm_refl : RelationClasses.Reflexive inf_subterm.
Proof. intro. exists Here. constructor. Qed.

Instance inf_subterm_trans : RelationClasses.Transitive inf_subterm.
Proof.
  intros a b c H1. destruct H1 as [ p H1 ]. revert c. induction H1; intros. auto.
  * edestruct IHinf_path_to as [ q IH ]. eauto. exists (Left q). constructor. auto.
  * edestruct IHinf_path_to as [ q IH ]. eauto. exists (Right q). constructor. auto.
Qed.

Lemma inf_subterm_eq l1 l2 r1 r2 (H1 : inf_term_eq l1 l2) (H2 : inf_term_eq r1 r2)
                     (H3 : inf_subterm l1 r1)
                   : exists t, inf_subterm l2 t /\ inf_term_eq t r2.
Proof.
  destruct H3 as [ p H ]. eapply inf_path_to_eq in H; eauto.
  destruct H as [ t [ H3 H4 ] ]. exists t. constructor; auto. exists p. auto.
Qed.

Definition is_rational_term (t : inf_term) :=
  exists ts, forall l, inf_subterm t l -> Exists (inf_term_eq l) ts.

Lemma is_rational_eq t1 t2 (H1 : inf_term_eq t1 t2) (H2 : is_rational_term t1) : is_rational_term t2.
Proof.
  destruct H2 as [ ts H2 ]. exists ts. intros. eapply inf_subterm_eq in H.
  destruct H as [ t [ H3 H4 ] ]. apply H2 in H3. clear H2. apply Exists_exists in H3.
  destruct H3 as [ t' [ H2 H3 ] ]. apply Exists_exists. exists t'. constructor. auto.
  etransitivity. symmetry. apply H4. auto. symmetry. auto. reflexivity.
Qed.

Lemma inf_subterm_rational l r (H1 : is_rational_term l) (H2 : inf_subterm l r) : is_rational_term r.
Proof. destruct H1 as [ ts H1 ]. exists ts. intros. apply H1. transitivity r; auto. Qed.

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

Lemma term_to_inf_rational t : is_rational_term (term_to_inf t).
Proof.
  exists (map term_to_inf (term_subterms t)). intros. destruct H as [ p H ].
  remember (term_to_inf t) as t'. revert t Heqt'. induction H; intros.
  * subst. apply Exists_map. apply Exists_exists. exists t0. constructor.
    apply term_subterms_self. reflexivity.
  * destruct t0 as [ | | f' l' r' ]; good_inversion Heqt'.
    apply Exists_map. simpl. apply Exists_cons_tl. apply Exists_app. left. apply Exists_map.
    apply IHinf_path_to. auto.
  * destruct t0 as [ | | f' l' r' ]; good_inversion Heqt'.
    apply Exists_map. simpl. apply Exists_cons_tl. apply Exists_app. right. apply Exists_map.
    apply IHinf_path_to. auto.
Qed.

Definition inf_subst : Set := list (name * inf_term).

Definition inf_subst_empty : inf_subst := [].

Definition inf_subst_singleton (x : name) (t : inf_term) : inf_subst := [(x, t)].

Definition subst_to_inf (s : subst) : inf_subst := map (fun x => (fst x, term_to_inf (snd x))) s.

Fixpoint inf_subst_dom (s : inf_subst) : var_set :=
match s with
| [] => var_set_empty
| (x, _) :: s => var_set_add x (inf_subst_dom s)
end.

(* TODO: поменять возвращаемый тип на inf_term *)
Fixpoint inf_image (s : inf_subst) (x : name) : option inf_term :=
match s with
| [] => None
| (y, t) :: s => if name_eq_dec x y then Some t else inf_image s x
end.

Lemma inf_image_empty x : inf_image inf_subst_empty x = None.
Proof. reflexivity. Qed.

Lemma inf_image_dom s x : (exists t, inf_image s x = Some t) <-> In x (inf_subst_dom s).
Proof.
  induction s as [ | [ y t ] s ]; simpl.
  * constructor; intro. destruct H as [ t H ]. inversion H. inversion H.
  * destruct (name_eq_dec x y).
    - constructor; intro. apply ListSet.set_add_intro2. auto. eexists. reflexivity.
    - constructor; intro. apply ListSet.set_add_intro1. apply IHs. auto.
      apply ListSet.set_add_elim in H. destruct H. contradiction. apply IHs. auto.
Qed.

Lemma inf_image_dom_inv s x : inf_image s x = None <-> ~In x (inf_subst_dom s).
Proof.
  constructor; intro.
  * intro. apply inf_image_dom in H0. destruct H0. rewrite H0 in H. inversion H.
  * remember (inf_image s x) as res. destruct res as [ t | ]; auto. symmetry in Heqres.
    exfalso. apply H. apply inf_image_dom. eexists. eauto.
Qed.

Lemma image_inf s x : inf_image (subst_to_inf s) x = option_map term_to_inf (image s x).
Proof.
  induction s as [ | [ y t ] s ]. auto. simpl.
  destruct (name_eq_dec x y); destruct (PeanoNat.Nat.eq_dec y x); auto; subst; contradiction.
Qed.

Definition is_rational_subst (s : inf_subst) :=
  exists ts, forall x t, inf_image s x = Some t ->
    forall l, inf_subterm t l -> Exists (inf_term_eq l) (ts x).

Fact inf_image_rational s x t (H1 : is_rational_subst s) (H2 : inf_image s x = Some t) : is_rational_term t.
Proof. destruct H1 as [ ts H1 ]. exists (ts x). apply H1. auto. Qed.

CoFixpoint inf_subst_apply (s : inf_subst) (t : inf_term) : inf_term :=
match t with
| InfVar x => match inf_image s x with None => t | Some t' => t' end
| InfCst _ => t
| InfCon f l r => InfCon f (inf_subst_apply s l) (inf_subst_apply s r)
end.

Lemma apply_subst_inf s t : inf_subst_apply (subst_to_inf s) (term_to_inf t) = term_to_inf (apply_subst s t).
Proof.
  induction t; rewrite inf_term_step_prop at 1; auto; simpl.
  * rewrite image_inf. destruct (image s n); auto. destruct t; auto.
  * f_equal; auto.
Qed.

Lemma inf_subst_apply_eq_node s t1 t2 (H : inf_term_eq_node t1 t2)
                       : inf_term_eq_node (inf_subst_apply s t1) (inf_subst_apply s t2).
Proof. destruct t1; destruct t2; good_inversion H; reflexivity. Qed.

Lemma inf_subst_apply_eq s t1 t2 (H : inf_term_eq t1 t2)
                       : inf_term_eq (inf_subst_apply s t1) (inf_subst_apply s t2).
Proof.
  intros p t1' Hp. remember (inf_subst_apply s t1) as t. revert t1 t2 H Heqt.
  induction Hp; intros.
  * subst. eexists. constructor. constructor.
    specialize (H Here t1). destruct H as [ t2' [ H1 H2 ] ]. constructor.
    good_inversion H1. apply inf_subst_apply_eq_node. auto.
  * rewrite inf_term_step_prop in Heqt. destruct t1; good_inversion Heqt.
    - edestruct (H Here) as [ t2' [ H2 H3 ] ]. constructor. good_inversion H2.
      destruct t2'; good_inversion H3. clear H. remember (inf_image s n0) as t'.
      destruct t' as [ [ | | f' l' r' ] | ]; good_inversion H1.
      exists t. constructor. rewrite inf_term_step_prop at 1. simpl. rewrite <- Heqt'.
      constructor. auto. reflexivity.
    - edestruct (H Here) as [ t2' [ H1 H2 ] ]. constructor. good_inversion H1.
      destruct t2'; good_inversion H2. specialize (IHHp t1_1 t2'1).
      destruct IHHp as [ r' [ IH1 IH2 ] ]; auto. eapply inf_term_eq_conl. eauto.
      exists r'. constructor; auto. rewrite inf_term_step_prop at 1. constructor. auto.
  * rewrite inf_term_step_prop in Heqt. destruct t1; good_inversion Heqt.
    - edestruct (H Here) as [ t2' [ H2 H3 ] ]. constructor. good_inversion H2.
      destruct t2'; good_inversion H3. clear H. remember (inf_image s n0) as t'.
      destruct t' as [ [ | | f' l' r' ] | ]; good_inversion H1.
      exists t. constructor. rewrite inf_term_step_prop at 1. simpl. rewrite <- Heqt'.
      constructor. auto. reflexivity.
    - edestruct (H Here) as [ t2' [ H1 H2 ] ]. constructor. good_inversion H1.
      destruct t2'; good_inversion H2. specialize (IHHp t1_2 t2'2).
      destruct IHHp as [ r' [ IH1 IH2 ] ]; auto. eapply inf_term_eq_conr. eauto.
      exists r'. constructor; auto. rewrite inf_term_step_prop at 1. constructor. auto.
Qed.

Lemma inf_subst_apply_subterm s l r (H : inf_subterm (inf_subst_apply s l) r)
                            : (exists t, inf_subterm l t /\ inf_term_eq (inf_subst_apply s t) r)
                           \/ (exists x t, inf_subterm l (InfVar x)
                                        /\ inf_image s x = Some t
                                        /\ inf_subterm t r).
Proof.
  destruct H as [ p H ]. remember (inf_subst_apply s l) as l'. revert l Heql'. induction H; intros.
  * left. exists l. constructor. reflexivity. subst. reflexivity.
  * destruct l0 as [ x | | f' l' r' ]; rewrite inf_term_step_prop in Heql'; good_inversion Heql'.
    - remember (inf_image s x) as x'. destruct x' as [ x' | ]; good_inversion H1.
      destruct x'; good_inversion H2. right. exists x. exists (InfCon n x'1 x'2).
      constructor. reflexivity. constructor. auto. exists (Left p). constructor. auto.
    - specialize (IHinf_path_to _ eq_refl). destruct IHinf_path_to as [ IH | IH ].
      + destruct IH as [ t' [ IH1 IH2 ] ]. left. exists t'. constructor; auto.
        destruct IH1 as [ q IH1 ]. exists (Left q). constructor. auto.
      + destruct IH as [ x [ t' [ IH1 IH2 ] ] ]. right. exists x. exists t'. constructor; auto.
        destruct IH1 as [ q IH1 ]. exists (Left q). constructor. auto.
  * destruct l0 as [ x | | f' l' r' ]; rewrite inf_term_step_prop in Heql'; good_inversion Heql'.
    - remember (inf_image s x) as x'. destruct x' as [ x' | ]; good_inversion H1.
      destruct x'; good_inversion H2. right. exists x. exists (InfCon n x'1 x'2).
      constructor. reflexivity. constructor. auto. exists (Right p). constructor. auto.
    - specialize (IHinf_path_to _ eq_refl). destruct IHinf_path_to as [ IH | IH ].
      + destruct IH as [ t' [ IH1 IH2 ] ]. left. exists t'. constructor; auto.
        destruct IH1 as [ q IH1 ]. exists (Right q). constructor. auto.
      + destruct IH as [ x [ t' [ IH1 IH2 ] ] ]. right. exists x. exists t'. constructor; auto.
        destruct IH1 as [ q IH1 ]. exists (Right q). constructor. auto.
Qed.

Lemma inf_subst_apply_empty t : inf_term_eq (inf_subst_apply inf_subst_empty t) t.
Proof.
  intros p t' Hp. remember (inf_subst_apply inf_subst_empty t) as t1. revert t Heqt1.
  induction Hp; intros.
  * subst. eexists. constructor. constructor. rewrite inf_term_step_prop at 1. simpl.
    destruct t0; reflexivity.
  * rewrite inf_term_step_prop in Heqt1. destruct t0; good_inversion Heqt1.
    edestruct IHHp as [ r' [ IH1 IH2 ] ]. reflexivity.
    exists r'. constructor; auto. constructor. auto.
  * rewrite inf_term_step_prop in Heqt1. destruct t0; good_inversion Heqt1.
    edestruct IHHp as [ r' [ IH1 IH2 ] ]. reflexivity.
    exists r'. constructor; auto. constructor. auto.
Qed.

Lemma inf_subst_apply_rational s t (H1 : is_rational_subst s) (H2 : is_rational_term t)
                             : is_rational_term (inf_subst_apply s t).
Proof.
  destruct H1 as [ tsf H1 ]. destruct H2 as [ ts H2 ].
  exists (map (inf_subst_apply s) ts ++ flat_map tsf (inf_subst_dom s)). intros.
  apply inf_subst_apply_subterm in H. destruct H.
  * destruct H as [ t' [ H3 H4 ] ]. apply H2 in H3. apply Exists_exists in H3.
    destruct H3 as [ r [ H3 H5 ] ]. apply Exists_app. left. apply Exists_map. apply Exists_exists.
    exists r. constructor. auto. etransitivity. symmetry. eauto. apply inf_subst_apply_eq. auto.
  * destruct H as [ x [ t' [ H3 [ H4 H5 ] ] ] ]. apply Exists_app. right. apply Exists_flat_map.
    apply Exists_exists. exists x. constructor. apply inf_image_dom. eexists. eauto.
    eapply H1. eauto. auto.
Qed.

Definition inf_subst_eq (s1 s2 : inf_subst) : Prop :=
  forall t, inf_term_eq (inf_subst_apply s1 t) (inf_subst_apply s2 t).

Instance inf_subst_eq_refl : RelationClasses.Reflexive inf_subst_eq.
Proof. intros s x. reflexivity. Qed.

Instance inf_subst_eq_sym : RelationClasses.Symmetric inf_subst_eq.
Proof. intros s1 s2 H x. symmetry. auto. Qed.

Instance inf_subst_eq_trans : RelationClasses.Transitive inf_subst_eq.
Proof. intros s1 s2 s3 H1 H2 x. etransitivity; eauto. Qed.

Instance inf_subst_eq_equiv : RelationClasses.Equivalence inf_subst_eq :=
  RelationClasses.Build_Equivalence _ _ _ _.

Definition inf_subst_compose (s1 s2 : inf_subst) : inf_subst :=
  map (fun p => (fst p, inf_subst_apply s1 (snd p))) s2 ++ s1.

Lemma compose_subst_inf s1 s2 : inf_subst_compose (subst_to_inf s1) (subst_to_inf s2) = subst_to_inf (compose s2 s1).
Proof.
  symmetry. etransitivity. apply map_app. unfold inf_subst_compose. f_equal.
  etransitivity. apply map_map. symmetry. etransitivity. apply map_map.
  apply map_ext. intro. simpl. f_equal. apply apply_subst_inf.
Qed.

Lemma inf_subst_compose_image_somer s1 s2 x t (H : inf_image s2 x = Some t)
                                  : inf_image (inf_subst_compose s1 s2) x = Some (inf_subst_apply s1 t).
Proof.
  induction s2 as [ | [ y t' ] s2 ]. inversion H.
  simpl in H. simpl. destruct (name_eq_dec x y); good_inversion H. auto.
  apply IHs2 in H1. auto.
Qed.

Lemma inf_subst_compose_image_somel s1 s2 x t (H1 : inf_image s1 x = Some t) (H2 : inf_image s2 x = None)
                                  : inf_image (inf_subst_compose s1 s2) x = Some t.
Proof.
  induction s2 as [ | [ y t' ] s2 ]. auto.
  simpl in H2. simpl. destruct (name_eq_dec x y); good_inversion H2.
  apply IHs2 in H0. auto.
Qed.

Lemma inf_subst_compose_dom s1 s2 x : In x (inf_subst_dom (inf_subst_compose s1 s2))
                                  <-> In x (inf_subst_dom s1) \/ In x (inf_subst_dom s2).
Proof.
  induction s2 as [ | [ y t ] s2 ]; simpl.
  * constructor; intro. left. auto. destruct H. auto. inversion H.
  * constructor; intro.
    - apply ListSet.set_add_elim in H. destruct H.
      + subst y. right. apply ListSet.set_add_intro2. auto.
      + apply IHs2 in H. destruct H. auto. right. apply ListSet.set_add_intro1. auto.
    - destruct H.
      + apply ListSet.set_add_intro1. apply IHs2. auto.
      + apply ListSet.set_add_elim in H. destruct H. apply ListSet.set_add_intro2. auto.
        apply ListSet.set_add_intro1. apply IHs2. auto.
Qed.

Lemma inf_subst_compose_spec s1 s2 t : inf_term_eq (inf_subst_apply s1 (inf_subst_apply s2 t))
                                                   (inf_subst_apply (inf_subst_compose s1 s2) t).
Proof.
  intros p l' Hp. remember (inf_subst_apply s1 (inf_subst_apply s2 t)) as t'. revert t Heqt'.
  induction Hp; intros.
  * subst. eexists. constructor. constructor.
    rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. destruct t0; simpl; auto.
    remember (inf_image s2 n) as res2. symmetry in Heqres2. destruct res2 as [ t | ].
    - erewrite inf_subst_compose_image_somer; eauto. destruct t; simpl; auto.
      + destruct (inf_image s1 n0) as [ t | ]. reflexivity. simpl. rewrite Heqres2. simpl. auto.
      + rewrite Heqres2. simpl. auto.
    - remember (inf_image s1 n) as res1. symmetry in Heqres1. destruct res1 as [ t | ].
      + erewrite inf_subst_compose_image_somel; eauto. reflexivity.
      + assert (inf_image (inf_subst_compose s1 s2) n = None). {
          apply inf_image_dom_inv. intro. apply inf_subst_compose_dom in H.
          destruct H; apply inf_image_dom in H; destruct H.
          * rewrite H in Heqres1. inversion Heqres1.
          * rewrite H in Heqres2. inversion Heqres2.
        }
        rewrite H. simpl. rewrite Heqres2. simpl. auto.
  * rewrite inf_term_step_prop in Heqt'. destruct t0; good_inversion Heqt'.
    - remember (inf_image s2 n) as res2. symmetry in Heqres2.
      destruct res2 as [ t' | ].
      + destruct t'. remember (inf_image s1 n0) as res1. symmetry in Heqres1.
        destruct res1 as [ t' | ]. destruct t'; good_inversion H0.
        ** exists t. constructor. rewrite inf_term_step_prop at 1. simpl.
           erewrite inf_subst_compose_image_somer; eauto. simpl. rewrite Heqres1. constructor. auto.
           reflexivity.
        ** simpl in H0. rewrite Heqres2 in H0. inversion H0.
        ** simpl in H0. rewrite Heqres2 in H0. inversion H0.
        ** good_inversion H0. exists t. constructor. rewrite inf_term_step_prop at 1. simpl.
           erewrite inf_subst_compose_image_somer; eauto. simpl. constructor. eauto. reflexivity.
      + remember (inf_image s1 n) as res1. symmetry in Heqres1.
        destruct res1 as [ t' | ]. destruct t'; good_inversion H0.
        ** exists t. constructor. rewrite inf_term_step_prop at 1. simpl.
           erewrite inf_subst_compose_image_somel; eauto. constructor. eauto. reflexivity.
        ** simpl in H0. rewrite Heqres2 in H0. inversion H0.
    - destruct (IHHp t0_1) as [ r' [ IH1 IH2 ] ]. auto.
      exists r'. constructor; auto. rewrite inf_term_step_prop at 1. simpl. constructor. auto.
  * rewrite inf_term_step_prop in Heqt'. destruct t0; good_inversion Heqt'.
    - remember (inf_image s2 n) as res2. symmetry in Heqres2.
      destruct res2 as [ t' | ].
      + destruct t'. remember (inf_image s1 n0) as res1. symmetry in Heqres1.
        destruct res1 as [ t' | ]. destruct t'; good_inversion H0.
        ** exists t. constructor. rewrite inf_term_step_prop at 1. simpl.
           erewrite inf_subst_compose_image_somer; eauto. simpl. rewrite Heqres1. constructor. auto.
           reflexivity.
        ** simpl in H0. rewrite Heqres2 in H0. inversion H0.
        ** simpl in H0. rewrite Heqres2 in H0. inversion H0.
        ** good_inversion H0. exists t. constructor. rewrite inf_term_step_prop at 1. simpl.
           erewrite inf_subst_compose_image_somer; eauto. simpl. constructor. eauto. reflexivity.
      + remember (inf_image s1 n) as res1. symmetry in Heqres1.
        destruct res1 as [ t' | ]. destruct t'; good_inversion H0.
        ** exists t. constructor. rewrite inf_term_step_prop at 1. simpl.
           erewrite inf_subst_compose_image_somel; eauto. constructor. eauto. reflexivity.
        ** simpl in H0. rewrite Heqres2 in H0. inversion H0.
    - destruct (IHHp t0_2) as [ r' [ IH1 IH2 ] ]. auto.
      exists r'. constructor; auto. rewrite inf_term_step_prop at 1. simpl. constructor. auto.
Qed.

Lemma inf_subst_compose_eq l1 l2 r1 r2 (H1 : inf_subst_eq l1 r1) (H2 : inf_subst_eq l2 r2)
                         : inf_subst_eq (inf_subst_compose l1 l2) (inf_subst_compose r1 r2).
Proof.
  intro. etransitivity. symmetry. apply inf_subst_compose_spec. etransitivity.
  apply H1. etransitivity. apply inf_subst_apply_eq. apply H2. apply inf_subst_compose_spec.
Qed.

Lemma inf_subst_compose_empty_l s : inf_subst_eq (inf_subst_compose inf_subst_empty s) s.
Proof.
  intro. etransitivity. symmetry. apply inf_subst_compose_spec. apply inf_subst_apply_empty.
Qed.

Lemma inf_subst_compose_empty_r s : inf_subst_eq (inf_subst_compose s inf_subst_empty) s.
Proof.
  intro. etransitivity. symmetry. apply inf_subst_compose_spec.
  apply inf_subst_apply_eq. apply inf_subst_apply_empty.
Qed.

Lemma inf_subst_compose_assoc s1 s2 s3 : inf_subst_eq (inf_subst_compose s1 (inf_subst_compose s2 s3))
                                                      (inf_subst_compose (inf_subst_compose s1 s2) s3).
Proof.
  intro. etransitivity. symmetry. apply inf_subst_compose_spec.
  etransitivity. apply inf_subst_apply_eq. symmetry. apply inf_subst_compose_spec.
  etransitivity; apply inf_subst_compose_spec.
Qed.

Definition inf_subst_more_general (m s : inf_subst) : Prop :=
  exists (s' : inf_subst), inf_subst_eq s (inf_subst_compose s' m).

Fact inf_subst_more_general_empty s : inf_subst_more_general inf_subst_empty s.
Proof. exists s. apply inf_subst_compose_empty_r. Qed.

Instance inf_subst_more_general_refl : RelationClasses.Reflexive inf_subst_more_general.
Proof. intro. exists inf_subst_empty. symmetry. apply inf_subst_compose_empty_l. Qed.

Instance inf_subst_more_general_trans : RelationClasses.Transitive inf_subst_more_general.
Proof.
  intros s1 s2 s3 H1 H2. destruct H1 as [ s1' H1 ]. destruct H2 as [ s2' H2 ].
  exists (inf_subst_compose s2' s1'). etransitivity. eauto. clear s3 H2.
  symmetry. etransitivity. symmetry. apply inf_subst_compose_assoc.
  apply inf_subst_compose_eq. reflexivity. symmetry. auto.
Qed.

Instance inf_subst_more_general_preorder : RelationClasses.PreOrder inf_subst_more_general :=
  {| RelationClasses.PreOrder_Reflexive := _ ; RelationClasses.PreOrder_Transitive := _ |}.

Definition inf_min_subst (P : inf_subst -> Prop) (s : inf_subst) :=
  P s /\ forall s', P s' -> inf_subst_more_general s s'.

Definition inf_unifier (t1 t2 : inf_term) (s : inf_subst) : Prop :=
  inf_term_eq (inf_subst_apply s t1) (inf_subst_apply s t2).

Lemma unifier_inf s t1 t2 : unifier s t1 t2 <-> inf_unifier (term_to_inf t1) (term_to_inf t2) (subst_to_inf s).
Proof.
  unfold unifier. unfold inf_unifier. rewrite apply_subst_inf. rewrite apply_subst_inf.
  constructor; intro.
  * rewrite H. reflexivity.
  * apply term_to_inf_inj. auto.
Qed.

Definition inf_mgu (t1 t2 : inf_term) (s : inf_subst) : Prop :=
  inf_min_subst (inf_unifier t1 t2) s.

Definition inf_min_subst_extension (P : inf_subst -> Prop) (m s : inf_subst) : Prop :=
  inf_min_subst (fun s' => inf_subst_more_general m s' /\ P s') s.

Definition inf_min_unifying_extension (t1 t2 : inf_term) (m s : inf_subst) : Prop :=
  inf_min_subst_extension (inf_unifier t1 t2) m s.

Fact inf_min_unifying_extension_empty t1 t2 s : inf_min_unifying_extension t1 t2 inf_subst_empty s
                                            <-> inf_mgu t1 t2 s.
Proof.
  constructor; intro.
  * destruct H as [ [ _ H1 ] H2 ]. constructor; auto.
    intros. apply H2. constructor; auto. apply inf_subst_more_general_empty.
  * destruct H as [ H1 H2 ]. constructor. constructor; auto. apply inf_subst_more_general_empty.
    intros. apply H2. destruct H as [ _ H ]. auto.
Qed.
