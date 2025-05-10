Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Extraction.

Require Import Unification.
Require Import RationalTree.
Require Import Streams.
Require Import Language.
Require Import RTDenotationalSem.


(* Utils *)

Fixpoint first_nats (k : nat) : list nat :=
match k with
| 0 => []
| S n => n :: first_nats n
end.

Lemma first_nats_less (n k : nat) (H : In n (first_nats k)) : n < k.
Proof. induction k; inversion H. lia. apply IHk in H0. lia. Qed.

Lemma max_either n m : max n m = n \/ max n m = m.
Proof. destruct (PeanoNat.Nat.max_spec n m) as [ [ _ H ] | [ _ H ] ]; auto. Qed.

Definition fv_terms (ts : terms) := var_set_union (fv_term (fst ts)) (fv_term (snd ts)).

Lemma fv_terms_In ts n : In n (fv_terms ts) <-> In n (fv_term (fst ts)) \/ In n (fv_term (snd ts)).
Proof. constructor; intro. apply set_union_elim in H. auto. apply set_union_intro. auto. Qed.

Definition fv_terms_list (ts : list terms) :=
  fold_right var_set_union var_set_empty (map fv_terms ts).

Lemma fv_terms_list_In ts n : In n (fv_terms_list ts)
                          <-> exists ts', In ts' ts /\ In n (fv_terms ts').
Proof.
  induction ts as [ | ts' ts ].
  * constructor; intro. inversion H. destruct H as [ ts' [ H _ ] ]. inversion H.
  * constructor; intro.
    - apply set_union_elim in H. destruct H. exists ts'. constructor; auto. left. auto.
      apply IHts in H. destruct H as [ ts'' [ H1 H2 ] ]. exists ts''. constructor; auto.
      right. auto.
    - destruct H as [ ts'' [ H1 H2 ] ]. good_inversion H1. apply set_union_intro1. auto.
      apply set_union_intro2. apply IHts. exists ts''. auto.
Qed.


(* States *)

Definition unification_state : Set := eq_sys * nat.

Variant unification_state_wf : unification_state -> Prop :=
| UnificationStateWF s n : eq_sys_wf s
                        -> (forall x, in_eq_sys_dom x s -> x < n)
                        -> (forall x, in_eq_sys_vran x s -> x < n)
                        -> unification_state_wf (s, n)
.

Inductive nt_state : Set :=
| Leaf : goal -> unification_state -> nt_state
| Sum : nt_state -> nt_state -> nt_state
| Prod : nt_state -> goal -> nt_state
.

Inductive is_fv_of_nt_state : name -> nt_state -> Prop :=
| isfvnstLeaf x g s : is_fv_of_goal x g -> is_fv_of_nt_state x (Leaf g s)
| isfvnstSumL x nst1 nst2 : is_fv_of_nt_state x nst1 -> is_fv_of_nt_state x (Sum nst1 nst2)
| isfvnstSumR x nst1 nst2 : is_fv_of_nt_state x nst2 -> is_fv_of_nt_state x (Sum nst1 nst2)
| isfvnstProdL x nst g : is_fv_of_nt_state x nst -> is_fv_of_nt_state x (Prod nst g)
| isfvnstProdR x nst g : is_fv_of_goal x g -> is_fv_of_nt_state x (Prod nst g)
.

Hint Constructors is_fv_of_nt_state : core.

Inductive is_counter_of_nt_state : nat -> nt_state -> Prop :=
| iscnstLeaf g s n : is_counter_of_nt_state n (Leaf g (s, n))
| iscnstSumL n nst1 nst2 : is_counter_of_nt_state n nst1
                        -> is_counter_of_nt_state n (Sum nst1 nst2)
| iscnstSumR n nst1 nst2 : is_counter_of_nt_state n nst2
                        -> is_counter_of_nt_state n (Sum nst1 nst2)
| iscnstProd n nst g : is_counter_of_nt_state n nst
                    -> is_counter_of_nt_state n (Prod nst g)
.

Hint Constructors is_counter_of_nt_state : core.

Inductive nt_state_wf : nt_state -> Prop :=
| wfLeaf g s n : unification_state_wf (s, n)
              -> (forall x, is_fv_of_goal x g -> x < n)
              -> nt_state_wf (Leaf g (s, n))
| wfSum nst1 nst2 : nt_state_wf nst1 -> nt_state_wf nst2 -> nt_state_wf (Sum nst1 nst2)
| wfProd nst g : nt_state_wf nst
              -> (forall x n, is_counter_of_nt_state n nst -> is_fv_of_goal x g -> x < n)
              -> nt_state_wf (Prod nst g)
.

Hint Constructors nt_state_wf : core.

Variant state : Set :=
| Stop : state
| NTState : nt_state -> state.

Variant is_fv_of_state : name -> state -> Prop :=
| isfvstC x nst : is_fv_of_nt_state x nst -> is_fv_of_state x (NTState nst)
.

Hint Constructors is_fv_of_state : core.

Variant state_wf : state -> Prop :=
| wfTerminal : state_wf Stop
| wfNonTerminal nst : nt_state_wf nst -> state_wf (NTState nst)
.

Hint Constructors state_wf : core.

Lemma initial_state_wf g k (HC : closed_goal_in_context (first_nats k) g)
                     : nt_state_wf (Leaf g (eq_sys_trivial, k)).
Proof.
  constructor. constructor. apply eq_sys_trivial_wf. all: intros.
  * good_inversion H. inversion H0.
  * good_inversion H. destruct H1 as [ t' [ [ n' H1 ] _ ] ]. inversion H1.
  * apply first_nats_less. apply HC. auto.
Qed.


(* Unification *)

Definition rt_unification_step (s : eq_sys) (n : nat) (t1 t2 : term)
                             : option (unification_state * list terms) :=
match t1, t2 with
| Var x, Var y =>
  match eq_sys_union s x y with
  | (None, s) => Some ((s, n), [])
  | (Some (t1, t2), s) => Some ((s, n), [(term_head_to_term t1, term_head_to_term t2)])
  end
| Var x, t =>
  match eq_sys_find s x with
  | (_, Some t') => Some ((s, n), [(t, term_head_to_term t')])
  | (_, None) =>
    match t with
    | Var _ => None
    | Cst c => Some ((eq_sys_bind s x (CstHead c), n), [])
    | Con c t1 t2 =>
      Some ((eq_sys_bind s x (ConHead c n (S n)), 2 + n), [(Var n, t1); (Var (S n), t2)])
    end
  end
| t, Var x => Some ((s, n), [(Var x, t)])
| Cst c1, Cst c2 =>
  if name_eq_dec c1 c2 then Some ((s, n), [])
  else None
| Con c1 l1 r1, Con c2 l2 r2 =>
  if name_eq_dec c1 c2 then Some ((s, n), [(l1, l2); (r1, r2)])
  else None
| _, _ => None
end.

Lemma rt_unification_step_wf t1 t2 s s' n ts (H1 : unification_state_wf (s, n))
                             (H2 : forall x, In x (fv_term t1) -> x < n)
                             (H3 : forall x, In x (fv_term t2) -> x < n)
                             (H4 : rt_unification_step s n t1 t2 = Some (s', ts))
                : unification_state_wf s' /\ n <= snd s'
               /\ forall n', In n' (fv_terms_list ts) -> n' < snd s'.
Proof.
  destruct t1 as [ x | c1 | c1 l1 r1 ]; destruct t2 as [ y | c2 | c2 l2 r2 ]; simpl in H4.
  * remember (eq_sys_union s x y) as res. symmetry in Heqres. destruct res as [ ts' s1 ].
    assert (s' = (s1, n)). destruct ts' as [ [ t1 t2 ] | ]; good_inversion H4; auto.
    subst. unshelve erewrite (_ : s1 = snd (eq_sys_union s x y)). rewrite Heqres. auto.
    good_inversion H1. constructor; [ | constructor ]; auto. clear H4 Heqres. constructor.
    - apply eq_sys_union_wf. auto.
    - intros x' H. apply eq_sys_union_dom in H; auto. destruct H. apply H6. auto.
      destruct H; [ apply H2 | apply H3 ]; left; auto.
    - intros x' H. apply eq_sys_union_vran in H; auto.
    - intros. simpl. destruct ts' as [ [ t1 t2 ] | ]; good_inversion H4; [ | inversion H ].
      assert (fst (eq_sys_union s x y) = Some (t1, t2)). rewrite Heqres. auto. clear Heqres.
      apply eq_sys_union_terms in H0. apply fv_terms_list_In in H. destruct H as [ ts' [ H H1 ] ].
      good_inversion H; [ | inversion H4 ]. destruct H0.
      apply fv_terms_In in H1. simpl in H1.
      destruct H1; rewrite <- fv_term_head_prop in H1;
        (eapply in_eq_sys_rhs_fv in H1; eauto; destruct H1; [ apply H6 | apply H7 ]; auto).
  * remember (eq_sys_find s x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H4;
      [ constructor; auto; constructor
      | good_inversion H1; constructor; constructor
      ]; auto.
    - intros y H. simpl. apply fv_terms_list_In in H. destruct H as [ ts' H ]. destruct H.
      good_inversion H; [ | inversion H4 ]. apply fv_terms_In in H0. destruct H0. inversion H.
      simpl in H. rewrite <- fv_term_head_prop in H. apply eq_sys_find_some in Heqres.
      eapply in_eq_sys_rhs_fv in H. good_inversion H1. destruct H; [ apply H6 | apply H7 ]; eauto.
      eexists. eauto.
    - apply eq_sys_bind_wf. auto.
    - intros y H. apply eq_sys_bind_dom in H. destruct H. apply H5. auto.
      rewrite Heqres in H. simpl in H. subst. destruct (in_dec name_eq_dec x (eq_sys_dom s)).
      apply in_eq_sys_dom_prop in i. apply H5. eexists.
      unshelve erewrite (_ : x' = fst (eq_sys_find s x)). rewrite Heqres. auto.
      destruct (H4 x i) as [ p H ]. eapply eq_sys_find_root. eauto.
      rewrite eq_sys_find_no in Heqres. good_inversion Heqres. apply H2. left. auto.
      apply in_eq_sys_dom_inv. intro. apply n0. apply in_eq_sys_dom_prop. auto.
    - intros y H. apply eq_sys_bind_vran in H. destruct H. rewrite Heqres in H. simpl in H.
      destruct H0. apply H6. auto. inversion H0.
  * remember (eq_sys_find s x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H4;
      [ constructor; auto; constructor
      | good_inversion H1; constructor; constructor
      ]; auto.
    - intros y H. simpl. apply fv_terms_list_In in H. destruct H as [ ts' H ]. destruct H.
      good_inversion H; [ | inversion H4 ]. apply fv_terms_In in H0. destruct H0. apply H3. apply H.
      simpl in H. rewrite <- fv_term_head_prop in H. apply eq_sys_find_some in Heqres.
      eapply in_eq_sys_rhs_fv in H. good_inversion H1. destruct H; [ apply H6 | apply H7 ]; eauto.
      eexists. eauto.
    - apply eq_sys_bind_wf. auto.
    - intros y H. transitivity n; [ | lia ].
      apply eq_sys_bind_dom in H. destruct H. apply H5. auto.
      rewrite Heqres in H. simpl in H. subst. destruct (in_dec name_eq_dec x (eq_sys_dom s)).
      apply in_eq_sys_dom_prop in i. apply H5. eexists.
      unshelve erewrite (_ : x' = fst (eq_sys_find s x)). rewrite Heqres. auto.
      destruct (H4 x i) as [ p H ]. eapply eq_sys_find_root. eauto.
      rewrite eq_sys_find_no in Heqres. good_inversion Heqres. apply H2. left. auto.
      apply in_eq_sys_dom_inv. intro. apply n0. apply in_eq_sys_dom_prop. auto.
    - intros y H. apply eq_sys_bind_vran in H. destruct H. rewrite Heqres in H. simpl in H.
      destruct H0. transitivity n. apply H6. auto. lia. apply set_add_elim in H0. destruct H0. lia.
      apply set_add_elim in H0. destruct H0. lia. inversion H0.
    - simpl. lia.
    - intros y H. simpl. apply fv_terms_list_In in H. destruct H as [ ts' H ]. destruct H.
      good_inversion H; [ | good_inversion H1; [ | inversion H ] ]; apply fv_terms_In in H0.
      + destruct H0. good_inversion H; [ | inversion H0 ]. lia.
        transitivity n; [ | lia ]. apply H3. apply set_union_intro1. auto.
      + destruct H0. good_inversion H; [ | inversion H0 ]. lia.
        transitivity n; [ | lia ]. apply H3. apply set_union_intro2. auto.
  * good_inversion H4. auto.
  * destruct (name_eq_dec c1 c2); good_inversion H4. auto.
  * inversion H4.
  * good_inversion H4. constructor; auto; constructor; auto.
    intros x H. simpl. apply fv_terms_list_In in H. destruct H as [ ts' H ]. destruct H.
    good_inversion H; [ | inversion H4 ]. apply fv_terms_In in H0.
    destruct H0; [ apply H3 | apply H2 ]; auto.
  * inversion H4.
  * destruct (name_eq_dec c1 c2); good_inversion H4. constructor; auto; constructor; auto.
    intros x H. simpl. apply fv_terms_list_In in H. destruct H as [ ts' H ]. destruct H.
    good_inversion H; [ | good_inversion H4; [ | inversion H ] ]; apply fv_terms_In in H0.
    - destruct H0; [ apply H2 | apply H3 ]; apply set_union_intro1; auto.
    - destruct H0; [ apply H2 | apply H3 ]; apply set_union_intro2; auto.
Qed.

Reserved Notation "s == t1 |_| t2 => s'" (at level 0).

Inductive rt_unify : unification_state -> term -> term -> option unification_state -> Prop :=
| StepRTUnify s1 n t1 t2 s2 s3 ts : rt_unification_step s1 n t1 t2 = Some (s2, ts)
                                 -> rt_unify_many s2 ts s3 -> (s1, n) == t1 |_| t2 => s3
| FailRTUnify s n t1 t2 : rt_unification_step s n t1 t2 = None -> (s, n) == t1 |_| t2 => None

with rt_unify_many : unification_state -> list terms -> option unification_state -> Prop :=
| NoneRTUnifyMany s : rt_unify_many s [] (Some s)
| StepRTUnifyMany s1 s2 s3 t1 t2 ts : s1 == t1 |_| t2 => (Some s2) -> rt_unify_many s2 ts s3
                                   -> rt_unify_many s1 ((t1, t2) :: ts) s3
| FailRTUnifyMany s t1 t2 ts : s == t1 |_| t2 => None -> rt_unify_many s ((t1, t2) :: ts) None

where "s == t1 |_| t2 => s'" := (rt_unify s t1 t2 s').

Fixpoint rt_unify_wf t1 t2 s s' (H1 : unification_state_wf s)
                     (H2 : forall x, In x (fv_terms (t1, t2)) -> x < snd s)
                     (H3 : s == t1 |_| t2 => (Some s'))
                   : unification_state_wf s' /\ snd s <= snd s'
with rt_unify_many_wf ts s s' (H1 : unification_state_wf s)
                      (H2 : forall x, In x (fv_terms_list ts) -> x < snd s)
                      (H3 : rt_unify_many s ts (Some s'))
                    : unification_state_wf s' /\ snd s <= snd s'.
Proof.
  * good_inversion H3. apply rt_unification_step_wf in H; auto. destruct H. destruct H3.
    apply rt_unify_many_wf in H0; auto. destruct H0. constructor; auto. simpl. lia.
    all: intros; apply H2; apply fv_terms_In; auto.
  * good_inversion H3. constructor; auto.
    apply rt_unify_wf in H; auto. destruct H. apply rt_unify_many_wf in H0; auto.
    - destruct H0. constructor; auto. lia.
    - intros. eapply PeanoNat.Nat.lt_le_trans. apply H2. apply set_union_intro2. auto. auto.
    - intros. apply H2. apply set_union_intro1. auto.
Qed.

Lemma rt_unify_inject_exists x t s n (H1 : unification_state_wf (s, n))
                             (H2 : x < n) (H3 : forall y, In y (fv_term t) -> y < n)
                             (H : ~in_eq_sys_dom x s)
                           : { s' | (s, n) == Var x |_| t => s'
                                 /\ forall s1 n1 y, s' = Some (s1, n1)
                                 -> in_eq_sys_dom y s1 -> in_eq_sys_dom y s \/ y = x
                                                       \/ In y (fv_term t) \/ n <= y }.
Proof.
  generalize dependent x. generalize dependent n. generalize dependent s.
  induction t as [ y | c | c t1 IHt1 t2 ]; intros.
  all: assert (eq_sys_find s x = (x, None));
    [ apply eq_sys_find_no; unfold in_eq_sys_dom in H; destruct (eq_sys_find_step s x); auto;
      exfalso; apply H; eexists; auto
    | ].
  * remember (eq_sys_union s x y) as res. symmetry in Heqres.
    destruct res as [ [ [ t1 t2 ] | ] s' ].
    - absurd (fst (eq_sys_union s x y) = Some (t1, t2)).
      intro. rewrite eq_sys_union_no_term in H4. inversion H4. left. rewrite H0. auto.
      rewrite Heqres. auto.
    - exists (Some (s', n)). constructor. econstructor. simpl. rewrite Heqres. auto. constructor.
      intros s1 n1 z. intros. symmetry in H4. good_inversion H4.
      unshelve erewrite (_ : s' = snd (eq_sys_union s x y)) in H5. rewrite Heqres. auto.
      good_inversion H1. apply eq_sys_union_dom in H5; auto.
      destruct H5; auto. destruct H1; auto. right. right. left. left. auto.
  * eexists. constructor. econstructor. unfold rt_unification_step. rewrite H0. auto. constructor.
    intros. symmetry in H4. good_inversion H4. apply eq_sys_bind_dom in H5. destruct H5; auto.
    rewrite H0 in H4. auto.
  * assert (rt_unification_step s n (Var x) (Con c t1 t2)
           = Some ((eq_sys_bind s x (ConHead c n (S n)), 2 + n), [(Var n, t1); (Var (S n), t2)])).
    unfold rt_unification_step. rewrite H0. auto.
    set (H5 := H4). apply rt_unification_step_wf in H5; auto.
    simpl in H5. destruct H5. destruct H6. clear H6.
    set (H6 := H5). eapply IHt1 in H6. destruct H6 as [ [ [ s1 n1 ] | ] [ Hs1 Hs1' ] ].
    set (Hs1'' := Hs1). apply rt_unify_wf in Hs1'';
      [ simpl in Hs1''; destruct Hs1''
      | clear Hs1'' ..
      ].
    edestruct IHt2 as [ [ s2 | ] Hs2 ].
    5: {
      eexists. constructor. econstructor. unfold rt_unification_step. rewrite H0. auto.
      econstructor. apply Hs1. econstructor. apply Hs2. constructor.
      intros. good_inversion H6. eapply Hs2 in H10; eauto.
      destruct H10 as [ H10 | [ H10 | [ H10 | H10 ] ] ]; auto. eapply Hs1' in H10; auto.
      destruct H10 as [ H10 | [ H10 | [ H10 | H10 ] ] ]; auto.
      all: try (right; right; right; lia).
      - apply eq_sys_bind_dom in H10. destruct H10; auto. rewrite H0 in H6. auto.
      - right. right. left. apply set_union_intro1. auto.
      - right. right. left. apply set_union_intro2. auto.
    }
    all: auto.
    - intros. eapply PeanoNat.Nat.lt_le_trans. apply H3. apply set_union_intro2. auto. lia.
    - intro. eapply Hs1' in H9; auto. destruct H9 as [ H9 | [ H9 | [ H9 | H9 ] ] ]; try lia.
      + apply eq_sys_bind_dom in H9. good_inversion H1. destruct H9. apply H13 in H1. lia.
        rewrite H0 in H1. simpl in H1. lia.
      + absurd (S n < n). lia. apply H3. apply set_union_intro1. auto.
    - exists None. constructor. econstructor. eauto. econstructor. eauto. constructor. apply Hs2.
      intros. inversion H9.
    - intro y. intros. simpl. apply fv_terms_In in H6. simpl in H6. destruct H6.
      + destruct H6. lia. contradiction.
      + eapply PeanoNat.Nat.lt_le_trans. apply H3. apply set_union_intro1. auto. lia.
    - exists None. constructor. econstructor. eauto. constructor. auto.
      intros. inversion H6.
    - intros. eapply PeanoNat.Nat.lt_le_trans. apply H3. apply set_union_intro1. auto. lia.
    - intro. apply eq_sys_bind_dom in H8. destruct H8. good_inversion H1. apply H12 in H8. lia.
      rewrite H0 in H8. simpl in H8. lia.
    - intros y Hy. good_inversion Hy; [ | inversion H6 ]. auto.
Qed.

Lemma rt_unify_vars_exists x y s n (H1 : unification_state_wf (s, n)) (H2 : x < n) (H3 : y < n)
                         : { s' | (s, n) == Var x |_| Var y => s' }.
Proof.
  set (P := fun m => forall x y s n,
                            unification_state_wf (s, n) -> x < n -> y < n
                         -> eq_sys_interp_size (eq_sys_ensure_vars s (first_nats n)) = m
                         -> { s' | (s, n) == Var x |_| Var y => s'
                                /\ forall s1 n1, s' = Some (s1, n1)
                                              -> eq_sys_interp_size (eq_sys_ensure_vars s1
                                                   (first_nats n)) <= m }).
  assert (P (eq_sys_interp_size s)). {
    apply (well_founded_induction PeanoNat.Nat.lt_wf_0).
    clear x y s n H1 H2 H3. subst P. simpl. intros m IHm x y s n H1 H2 H3 H4. subst.
    remember (eq_sys_union s x y) as res. symmetry in Heqres.
    destruct res as [ [ [ [ c1 | c1 l1 r1 ] [ c2 | c2 l2 r2 ] ] | ] s' ].
    * remember (name_eq_dec c1 c2) as cond. symmetry in Heqcond. destruct cond.
      - exists (Some (s', n)). constructor. econstructor. simpl. rewrite Heqres. auto.
        econstructor. econstructor. simpl. rewrite Heqcond. auto. constructor. constructor.
        intros. symmetry in H. good_inversion H. (* apply eq_sys_union_interp_size_some in Heqres. *)
        apply NoDup_incl_length. apply eq_sys_roots_distinct. intros z H.
        apply eq_sys_roots_prop in H. destruct H as [ t H ]. apply eq_sys_ensure_vars_prop in H.
        destruct H. apply eq_sys_
        rewrite Heqres. lia.
      - exists None. constructor. econstructor. simpl. rewrite Heqres. auto.
        constructor. constructor. simpl. rewrite Heqcond. auto. intros. inversion H.
    * exists None. constructor. econstructor. simpl. rewrite Heqres. auto.
      constructor. constructor. auto. intros. inversion H.
    * exists None. constructor. econstructor. simpl. rewrite Heqres. auto.
      constructor. constructor. auto. intros. inversion H.
    *
    ...
  }
  edestruct H as [ s' [ H0 _ ] ]. eauto. apply H2. apply H3. auto. eexists. apply H0.
Qed.

Definition terms_height (ts : terms) : nat := max (height (fst ts)) (height (snd ts)).

Lemma terms_height_var1 x t : terms_height (Var x, t) = height t.
Proof. destruct t; auto. Qed.

Lemma terms_height_var2 x t : terms_height (Var x, t) = height t.
Proof. destruct t; auto. Qed.

Definition terms_height_less (ts1 ts2 : terms) : Prop := terms_height ts1 < terms_height ts2.

Lemma terms_height_not_zero ts : terms_height ts <> 0.
Proof. destruct ts as [ [ n1 | n1 | n1 l1 r1 ] [ n2 | n2 | n2 l2 r2 ] ]; intro; good_inversion H. Qed.

Lemma terms_height_less_wf : well_founded terms_height_less.
Proof.
  intro ts. remember (terms_height ts) as h. symmetry in Heqh.
  generalize dependent ts. induction h; intros; destruct ts as [ t1 t2 ].
  * destruct t1; destruct t2; good_inversion Heqh.
  * destruct t1 as [ x | n1 | n1 l1 r1 ]; destruct t2 as [ y | n2 | n2 l2 r2 ].
    1, 2, 4, 5: good_inversion Heqh; constructor; intros ts H; good_inversion H;
      [ exfalso; eapply terms_height_not_zero; eauto
      | good_inversion H1
      ].
    all: good_inversion Heqh; constructor; intros [ t1 t2 ] H; good_inversion H;
      [ apply IHh; auto | ].
    1, 2: destruct (IHh (l2, r2)); auto.
    1, 2: rewrite PeanoNat.Nat.max_0_r in *; destruct (IHh (l1, r1)); auto.
    destruct (max_either (max (height l1) (height r1)) (max (height l2) (height r2)));
      rewrite H in *; clear H.
    - destruct (IHh (l1, r1)); auto.
    - destruct (IHh (l2, r2)); auto.
Qed.

Lemma rt_unify_exists_aux t1 t2 s n m (int : eq_sys_interp m)
                          (H1 : unification_state_wf (s, n)) (H2 : is_interp_of_eq_sys int s)
                          (H3 : forall x, In x (fv_terms (t1, t2)) -> x < n)
                        : { s' | (s, n) == t1 |_| t2 => s' }.
Proof.
  set (P := fun m => forall t1 t2 s n (int : eq_sys_interp m),
                            unification_state_wf (s, n)
                         -> is_interp_of_eq_sys int s
                         -> (forall x, In x (fv_terms (t1, t2)) -> x < n)
                         -> { s' | (s, n) == t1 |_| t2 => s' }).
  assert (P m). {
    apply (well_founded_induction Wf_nat.lt_wf). subst P. clear t1 t2 s n m int H1 H2 H3. simpl.
    intros m IHm t1 t2 s n int H1 H2 H3.
    ...
  }
  subst P. simpl in H. eapply H; eauto.

Lemma rt_unify_exists t1 t2 s (H : unification_state_wf s) : { s' | s == t1 |_| t2 => s' }.
Proof.
  destruct s as [ s n ]. edestruct eq_sys_interp_exists. good_inversion H. eauto.
  eapply rt_unify_exists_aux; eauto.
Qed.


(* LTS *)

Inductive label : Set :=
| Step : label
| Answer : eq_sys -> nat -> label
.

Inductive eval_step : nt_state -> label -> state -> Prop :=
| esFail s n : eval_step (Leaf Fail s n) Step Stop
(*
| esUnifyFail t1 t2 s n : mgu (apply_subst s t1) (apply_subst s t2) None
                       -> eval_step (Leaf (Unify t1 t2) s n) Step Stop
| esUnifySuccess t1 t2 s d n : mgu (apply_subst s t1) (apply_subst s t2) (Some d)
                            -> eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s d) n) Stop
*)
| esDisj g1 g2 s n : eval_step (Leaf (Disj g1 g2) s n) Step (NTState (Sum (Leaf g1 s n) (Leaf g2 s n)))
| esConj g1 g2 s n : eval_step (Leaf (Conj g1 g2) s n) Step (NTState (Prod (Leaf g1 s n) g2))
| esFresh fg s n : eval_step (Leaf (Fresh fg) s n) Step (NTState (Leaf (fg n) s (S n)))
| esInvoke r arg s n : eval_step (Leaf (Invoke r arg) s n) Step (NTState (Leaf (proj1_sig (Prog r) arg) s n))
| esSumE nst1 nst2 l : eval_step nst1 l Stop -> eval_step (Sum nst1 nst2) l (NTState nst2)
| esSumNE nst1 nst1' nst2 l : eval_step nst1 l (NTState nst1')
                          -> eval_step (Sum nst1 nst2) l (NTState (Sum nst2 nst1'))
| esProdSE nst g : eval_step nst Step Stop -> eval_step (Prod nst g) Step Stop
| esProdAE nst g s n : eval_step nst (Answer s n) Stop
                    -> eval_step (Prod nst g) Step (NTState (Leaf g s n))
| esProdSNE nst g nst' : eval_step nst Step (NTState nst')
                      -> eval_step (Prod nst g) Step (NTState (Prod nst' g))
| esProdANE nst g s n nst' : eval_step nst (Answer s n) (NTState nst')
                          -> eval_step (Prod nst g) Step (NTState (Sum (Leaf g s n) (Prod nst' g)))
.

Hint Constructors eval_step : core.

Lemma counter_in_answer
      (nst : nt_state)
      (s : subst)
      (n : nat)
      (st : state)
      (EV : eval_step nst (Answer s n) st) :
      is_counter_of_nt_state n nst.
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; auto.
Qed.

Lemma counter_in_next_state
      (n : nat)
      (nst nst_next : nt_state)
      (l : label)
      (EV : eval_step nst l (NTState nst_next))
      (ISC_NEXT :  is_counter_of_nt_state n nst_next) :
      exists n', n' <= n /\ is_counter_of_nt_state n' nst.
Proof.
  remember (NTState nst_next) as st.
  revert Heqst ISC_NEXT. revert nst_next.
  induction EV; intros; good_inversion Heqst.
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; good_inversion ISC; auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; good_inversion ISC; auto. } }
  { good_inversion ISC_NEXT. exists n0. split.
    { repeat constructor. }
    { auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; auto. } }
  { exists n. split.
    { constructor. }
    { auto. } }
  { specialize (IHEV nst1' eq_refl). good_inversion ISC_NEXT.
    { exists n. split.
      { constructor. }
      { auto. } }
    { apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
      exists n'; auto. } }
  { good_inversion ISC_NEXT. exists n0.
    eapply counter_in_answer in EV. split; auto. }
  { specialize (IHEV nst' eq_refl). good_inversion ISC_NEXT.
    apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
    exists n'; auto. }
  { specialize (IHEV nst' eq_refl). good_inversion ISC_NEXT.
    { good_inversion ISC. exists n0.
      eapply counter_in_answer in EV. split; auto. }
    { good_inversion ISC. apply IHEV in ISC0.
      destruct ISC0 as [n' [LE ISC]]. exists n'; auto. } }
Qed.

Lemma well_formed_subst_in_answer
      (nst : nt_state)
      (s : subst)
      (n : nat)
      (st : state)
      (EV : eval_step nst (Answer s n) st)
      (WF : nt_state_wf nst) :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; good_inversion WF; auto.
  assert (FV_LT_N_1 : forall x, In x (fv_term (apply_subst s0 t1)) -> x < n).
  { clear MGU. clear d. intros. induction t1.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply VRAN_LT_COUNTER. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt1_1; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyL. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt1_2; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyL. simpl.
        apply set_union_intro. right. auto. } } }
  assert (FV_LT_N_2 : forall x, In x (fv_term (apply_subst s0 t2)) -> x < n).
  { clear MGU. clear d. intros. induction t2.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply VRAN_LT_COUNTER. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt2_1; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyR. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt2_2; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyR. simpl.
        apply set_union_intro. right. auto. } } }
  specialize (mgu_dom _ _ _ MGU). intro S'_DOM.
  specialize (mgu_vran _ _ _ MGU). intro S'_VRAN.
  split.
  { intros. apply compose_dom in H. destruct H; auto.
    apply S'_DOM in H. destruct H; auto. }
  { intros. apply compose_vran in H. destruct H; auto.
    apply S'_VRAN in H. destruct H; auto. }
Qed.

Lemma well_formedness_preservation
      (nst : nt_state)
      (l : label)
      (st : state)
      (EV : eval_step nst l st)
      (WF : nt_state_wf nst) :
      state_wf st.
Proof.
  intros. induction EV; good_inversion WF; auto.
  { constructor. auto. }
  { constructor. constructor; auto.
    intros. good_inversion FRN_COUNTER. subst. auto. }
  { constructor. constructor; auto.
    1-2: intros; eapply PeanoNat.Nat.lt_trans; eauto.
    intros. destruct (PeanoNat.Nat.eq_dec n x).
    { lia. }
    { apply PeanoNat.Nat.lt_lt_succ_r. apply FV_LT_COUNTER. econstructor; eauto. } }
  { constructor. constructor; auto.
    specialize (proj2_sig (Language.Prog r)). intro CC.
    simpl in CC. destruct CC as [CL _]. red in CL. red in CL. auto. }
  { specialize (IHEV WF_L).
    good_inversion IHEV. auto. }
  { constructor. constructor; auto.
    1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
    intros. apply FV_LT_COUNTER; auto. eapply counter_in_answer; eauto. }
  { specialize (IHEV WF_L). good_inversion IHEV.
    constructor. constructor; auto. intros.
    eapply counter_in_next_state in EV; eauto.
    destruct EV as [frn' [LE ISC]]. eapply PeanoNat.Nat.lt_le_trans.
    2: eauto.
    auto. }
  { specialize (IHEV WF_L). good_inversion IHEV.
    constructor. constructor.
    { constructor.
      1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
      intros. apply FV_LT_COUNTER; auto.
      eapply counter_in_answer; eauto. }
    { constructor; auto. intros.
      eapply counter_in_next_state in EV; eauto.
      destruct EV as [frn' [Le ISC]]. eapply PeanoNat.Nat.lt_le_trans.
      2: eauto.
      auto. } }
Qed.

Lemma eval_step_exists
      (nst : nt_state) :
      {l : label & {st : state & eval_step nst l st}}.
Proof.
  induction nst.
  { destruct g.
    1,3-6: repeat eexists; econstructor.
    { assert ({r & mgu (apply_subst s t) (apply_subst s t0) r}).
      { apply mgu_result_exists. }
      destruct H. destruct x.
      { repeat eexists; eauto. }
      { repeat eexists; eauto. } } }
  { destruct IHnst1 as [l1 [st1 IH1]]. destruct st1.
    all: repeat eexists; eauto. }
  { destruct IHnst as [l [st IH]]. destruct st; destruct l.
    all: repeat eexists; eauto. }
Defined.

Lemma eval_step_unique
      (nst : nt_state)
      (l1 l2 : label)
      (st1 st2 : state)
      (STEP_1 : eval_step nst l1 st1)
      (STEP_2 : eval_step nst l2 st2) :
      l1 = l2 /\ st1 = st2.
Proof.
  revert STEP_1 STEP_2. revert l1 l2 st1 st2. induction nst.
  { intros. destruct g; good_inversion STEP_1; good_inversion STEP_2; auto.
    { assert (C : None = Some d).
      { eapply mgu_result_unique; eassumption. }
      inversion C. }
    { assert (C : None = Some d).
      { eapply mgu_result_unique; eassumption. }
      inversion C. }
    { assert (EQ : Some d = Some d0).
      { eapply mgu_result_unique; eassumption. }
      good_inversion EQ. auto. } }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    specialize (IHnst1 _ _ _ _ STEP_L STEP_L0); inversion IHnst1;
    inversion H0; subst; auto. }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    specialize (IHnst _ _ _ _ STEP_L STEP_L0); inversion IHnst; subst;
    inversion H; inversion H0; auto. }
Qed.



(* Operational Semantics *)

Definition trace : Set := @stream label.

CoInductive op_sem : state -> trace -> Prop :=
| osStop : op_sem Stop Nil
| osNTState : forall nst l st t (EV: eval_step nst l st)
                                (OP: op_sem st t),
                                op_sem (NTState nst) (Cons l t).

Hint Constructors op_sem : core.

CoFixpoint trace_from (st : state) : trace :=
  match st with
  | Stop => Nil
  | NTState nst =>
    match eval_step_exists nst with
    | existT _ l (existT _ nst' ev_nst_nst') =>
      Cons l (trace_from nst')
    end
  end.

Lemma trace_from_correct
      (st : state) :
      op_sem st (trace_from st).
Proof.
  revert st. cofix CIH. destruct st.
  { rewrite helper_eq. simpl. constructor. }
  { rewrite helper_eq. simpl. destruct (eval_step_exists n).
    destruct s. econstructor; eauto. }
Qed.

Lemma op_sem_exists
      (st : state) :
      {t : trace & op_sem st t}.
Proof.
  eexists. eapply trace_from_correct.
Defined.

Lemma op_sem_unique
      (st : state)
      (t1 t2 : trace)
      (OP_1 : op_sem st t1)
      (OP_2 : op_sem st t2) :
      equal_streams t1 t2.
Proof.
  revert OP_1 OP_2. revert t1 t2 st.
  cofix CIH. intros. inversion OP_1; inversion OP_2;
  rewrite <- H1 in H; inversion H.
  { constructor. }
  { subst.
    specialize (eval_step_unique _ _ _ _ _ EV EV0).
    intros [EQL EQST]. constructor.
    { auto. }
    { subst. eapply CIH; eauto. } }
Qed.

Definition in_denotational_analog (t : trace) (f : repr_fun) : Prop :=
  exists (s : subst) (n : nat),
    in_stream (Answer s n) t /\ [ s ,  f ].

Notation "{| t , f |}" := (in_denotational_analog t f).

Lemma counter_in_trace
      (g : goal)
      (s sr : subst)
      (n nr : nat)
      (tr : trace)
      (OP : op_sem (NTState (Leaf g s n)) tr)
      (HIn : in_stream (Answer sr nr) tr) :
      n <= nr.
Proof.
  remember (Leaf g s n) as nst.
  assert (CNT_GE : forall n', is_counter_of_nt_state n' nst -> n <= n').
  { intros. subst. good_inversion H. auto. }
  clear Heqnst. revert CNT_GE OP. revert n nst.
  remember (Answer sr nr). induction HIn; intros; subst.
  { good_inversion OP. apply counter_in_answer in EV. auto. }
  { good_inversion OP. destruct st.
    { good_inversion OP0. good_inversion HIn. }
    { apply IHHIn with n0; auto. intros.
      specialize (counter_in_next_state _ _ _ _ EV H). intros.
      destruct H0. destruct H0. apply CNT_GE in H1.
      eapply PeanoNat.Nat.le_trans; eauto. } }
Qed.

Lemma well_formed_subst_in_trace
      (st : state)
      (WF : state_wf st)
      (t : trace)
      (OP : op_sem st t)
      (s : subst)
      (n : nat)
      (IS_ANS: in_stream (Answer s n) t) :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). revert WF OP. revert st.
  induction IS_ANS; intros.
  { good_inversion OP. good_inversion WF.
    eapply well_formed_subst_in_answer; eauto. }
  { good_inversion OP. good_inversion WF.
    apply IHIS_ANS with st0; auto.
    eapply well_formedness_preservation; eauto. }
Qed.

Lemma sum_op_sem
      (nst1 nst2 : nt_state)
      (t1 t2 t : trace)
      (OP_1 : op_sem (NTState nst1) t1)
      (OP_2 : op_sem (NTState nst2) t2)
      (OP_12 : op_sem (NTState (Sum nst1 nst2)) t) :
      interleave t1 t2 t.
Proof.
  revert OP_1 OP_2 OP_12. revert t1 t2 t nst1 nst2.
  cofix CIH. intros. inversion OP_1. subst. inversion OP_12. subst.
  inversion EV0; subst; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
  intros [EQL EQST]; subst; constructor.
  { inversion OP. subst. specialize (op_sem_unique _ _ _ OP_2 OP0).
    intro EQS. inversion EQS; subst.
    { constructor. constructor. }
    { constructor. constructor. auto. } }
  { eapply CIH; eassumption. }
Qed.

Lemma sum_op_sem_in
      (nst1 nst2 : nt_state)
      (t1 t2 t : trace)
      (r : label)
      (OP_1 : op_sem (NTState nst1) t1)
      (OP_2 : op_sem (NTState nst2) t2)
      (OP_12 : op_sem (NTState (Sum nst1 nst2)) t) :
      in_stream r t <-> in_stream r t1 \/ in_stream r t2.
Proof.
  apply interleave_in. eapply sum_op_sem; eauto.
Qed.

Lemma disj_termination
      (g1 g2 : goal)
      (s : subst)
      (n : nat)
      (t1 t2 t : trace)
      (r : label)
      (OP_1 : op_sem (NTState (Leaf g1 s n)) t1)
      (OP_2 : op_sem (NTState (Leaf g2 s n)) t2)
      (OP_12 : op_sem (NTState (Leaf (Disj g1 g2) s n)) t) :
      finite t <-> finite t1 /\ finite t2.
Proof.
  good_inversion OP_12. good_inversion EV.
  assert (forall t, finite (Cons Step t) <-> finite t).
  { intros; split; intros H.
    { inversion H; auto. }
    { constructor; auto. } }
  eapply RelationClasses.iff_Transitive. eapply (H t0).
  apply interleave_finite. eapply sum_op_sem; eauto.
Qed.

Lemma prod_op_sem_in
      (nst : nt_state)
      (g : goal)
      (s : subst)
      (n : nat)
      (t1 t2 t : trace)
      (r : label)
      (OP : op_sem (NTState (Prod nst g)) t)
      (OP1 : op_sem (NTState nst) t1)
      (OP2 : op_sem (NTState (Leaf g s n)) t2)
      (IN_1 : in_stream (Answer s n) t1)
      (IN_2 : in_stream r t2) :
      in_stream r t.
Proof.
  revert OP OP1. revert t nst. remember (Answer s n) as r1.
  induction IN_1; intros; subst.
  { good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
    intro eqs; destruct eqs; subst; good_inversion H.
    { constructor. specialize (op_sem_unique _ _ _ OP2 OP1).
      intros. eapply in_equal_streams; eauto. }
    { constructor. specialize (op_sem_exists (NTState (Leaf g s0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (NTState (Prod nst' g))).
      intro H. destruct H as [t4 OP4].
      specialize (sum_op_sem _ _ _ _ _ OP3 OP4 OP1).
      intro interH. eapply interleave_in in interH.
      eapply interH. left. specialize (op_sem_unique _ _ _ OP2 OP3).
      intros. eapply in_equal_streams; eauto. } }
  { specialize (IHIN_1 eq_refl).
    good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
    intro eqs; destruct eqs; subst.
    1-2: good_inversion OP0; good_inversion IN_1.
    { constructor. eapply IHIN_1; eauto. }
    { constructor. specialize (op_sem_exists (NTState (Leaf g s0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (NTState (Prod nst' g))).
      intro H. destruct H as [t4 OP4].
      specialize (sum_op_sem _ _ _ _ _ OP3 OP4 OP1).
      intro interH. eapply interleave_in in interH.
      eapply interH. right. eapply IHIN_1; eauto. } }
Qed.

(*
Extraction Language Haskell.

Extraction "extracted/interleaving_interpreter.hs" op_sem_exists.
*)
