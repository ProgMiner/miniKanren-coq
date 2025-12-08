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

Lemma in_eqsys_dom_inv s x : ~in_eqsys_dom s x <-> eqsys_lookup s x = None.
Proof.
  remember (eqsys_lookup s x) as res. symmetry in Heqres. destruct res.
  * constructor; intro. exfalso. apply H. eexists. eauto. inversion H.
  * constructor; intro. auto. intro. destruct H0. rewrite H0 in Heqres. inversion Heqres.
Qed.

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

Lemma eqsys_walk_result_var s x y z (H : eqsys_walk_result s x (y, Var z)) : y = z.
Proof.
  remember (y, Var z) as r. revert y z Heqr.
  induction H; intros; auto; good_inversion Heqr. auto.
Qed.

Lemma eqsys_walk_result_var_dom s x y z (H : eqsys_walk_result s x (y, Var z)) : ~in_eqsys_dom s z.
Proof.
  remember (y, Var z) as r. revert y z Heqr.
  induction H; intros; good_inversion Heqr.
  * apply in_eqsys_dom_inv. auto.
  * eapply IHeqsys_walk_result. reflexivity.
Qed.

Lemma eqsys_walk_result_last s x y z t (H : eqsys_walk_result s x (y, t))
                           : eqsys_lookup s y <> Some (Var z).
Proof.
  remember (y, t) as r. revert y t Heqr. induction H; intros; good_inversion Heqr; try rewrite H.
  all: try (intro; inversion H0; fail). eapply IHeqsys_walk_result. auto.
Qed.

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

Inductive eqsys_walk_fuel_path (s : eqsys) : name -> list name -> Prop :=
| ESWalkFuelPathVar x : eqsys_lookup s x = None -> eqsys_walk_fuel_path s x []
| ESWalkFuelPathWalk x y p : eqsys_lookup s x = Some (Var y) -> eqsys_walk_fuel_path s y p -> eqsys_walk_fuel_path s x (x :: p)
| ESWalkFuelPathCst x c : eqsys_lookup s x = Some (Cst c) -> eqsys_walk_fuel_path s x [x]
| ESWalkFuelPathCon x f l r : eqsys_lookup s x = Some (Con f l r) -> eqsys_walk_fuel_path s x [x]
.

Lemma eqsys_walk_fuel_path_inj s x p1 p2
                               (H1 : eqsys_walk_fuel_path s x p1)
                               (H2 : eqsys_walk_fuel_path s x p2)
                             : p1 = p2.
Proof.
  revert p2 H2. induction H1; intros; good_inversion H2; auto; rewrite H in H0; good_inversion H0.
  f_equal. auto.
Qed.

Lemma eqsys_walk_fuel_path_result s x res (H : eqsys_walk_result s x res)
                                : exists p, eqsys_walk_fuel_path s x p.
Proof.
  induction H.
  * exists []. constructor. auto.
  * destruct IHeqsys_walk_result as [ p H1 ]. exists (x :: p). econstructor; eauto.
  * exists [x]. eapply ESWalkFuelPathCst. eauto.
  * exists [x]. eapply ESWalkFuelPathCon. eauto.
Qed.

Lemma eqsys_walk_fuel_path_split s x y p1 p2 (H : eqsys_walk_fuel_path s x (p1 ++ y :: p2))
                               : eqsys_walk_fuel_path s y (y :: p2).
Proof.
  remember (p1 ++ y :: p2) as p. revert y p1 p2 Heqp. induction H; intros.
  * symmetry in Heqp. apply app_eq_nil in Heqp. destruct Heqp. inversion H1.
  * destruct p1 as [ | x' p1 ]; good_inversion Heqp.
    - econstructor. eauto. auto.
    - eapply IHeqsys_walk_fuel_path. reflexivity.
  * destruct p1 as [ | x' p1 ]; good_inversion Heqp.
    - eapply ESWalkFuelPathCst. eauto.
    - symmetry in H2. apply app_eq_nil in H2. destruct H2. inversion H1.
  * destruct p1 as [ | x' p1 ]; good_inversion Heqp.
    - eapply ESWalkFuelPathCon. eauto.
    - symmetry in H2. apply app_eq_nil in H2. destruct H2. inversion H1.
Qed.

Polymorphic Lemma singleton_nodup {A : Type} (x : A) : NoDup [x].
Proof. constructor. intro. inversion H. constructor. Qed.

Lemma eqsys_walk_fuel_path_nodup s x p (H : eqsys_walk_fuel_path s x p) : NoDup p.
Proof.
  induction H. constructor. 2, 3: apply singleton_nodup.
  constructor; auto. intro. apply in_split in H1. destruct H1 as [ p1 [ p2 H1 ] ].
  set (H2 := H0). rewrite H1 in H2. apply eqsys_walk_fuel_path_split in H2.
  eapply eqsys_walk_fuel_path_inj in H2. 2: { eapply ESWalkFuelPathWalk. eauto. eauto. }
  good_inversion H2. rewrite (app_assoc p1 [x] p2 : p1 ++ x :: p2 = _) in H4.
  apply (app_inv_tail p2 _ []) in H4. apply app_eq_nil in H4. destruct H4. inversion H2.
Qed.

Polymorphic Lemma singleton_incl {A : Type} (x : A) (xs : list A) (H : In x xs) : incl [x] xs.
Proof. apply incl_cons. auto. apply incl_nil_l. Qed.

Lemma eqsys_walk_fuel_path_in_dom s x p (H : eqsys_walk_fuel_path s x p) : incl p (eqsys_dom s).
Proof.
  induction H.
  * apply incl_nil_l.
  * apply incl_cons; auto. apply eqsys_dom_spec. eexists. eauto.
  * apply singleton_incl. apply eqsys_dom_spec. eexists. eauto.
  * apply singleton_incl. apply eqsys_dom_spec. eexists. eauto.
Qed.

Lemma eqsys_walk_hlp_fuel s x p fuel (H1 : eqsys_walk_fuel_path s x p) (H2 : length p <= fuel)
                        : eqsys_walk_result s x (eqsys_walk_hlp fuel s x).
Proof.
   revert fuel H2. induction H1; intros.
   * destruct fuel. constructor. auto. simpl. rewrite H. constructor. auto.
   * destruct fuel. inversion H2. simpl. rewrite H. econstructor. eauto.
     apply IHeqsys_walk_fuel_path. apply le_S_n. auto.
   * destruct fuel. inversion H2. simpl. rewrite H. constructor. auto.
   * destruct fuel. inversion H2. simpl. rewrite H. constructor. auto.
Qed.

Inductive eqsys_walk_path (s : eqsys) : name -> list name -> Prop :=
| ESWalkPathVar x : eqsys_lookup s x = None -> eqsys_walk_path s x [x]
| ESWalkPathWalk x y p : eqsys_lookup s x = Some (Var y) -> eqsys_walk_path s y p -> eqsys_walk_path s x (x :: p)
| ESWalkPathCst x c : eqsys_lookup s x = Some (Cst c) -> eqsys_walk_path s x [x]
| ESWalkPathCon x f l r : eqsys_lookup s x = Some (Con f l r) -> eqsys_walk_path s x [x]
.

Lemma eqsys_walk_path_inj s x p1 p2 (H1 : eqsys_walk_path s x p1) (H2 : eqsys_walk_path s x p2)
                        : p1 = p2.
Proof.
  revert p2 H2. induction H1; intros; good_inversion H2; auto; rewrite H in H0; good_inversion H0.
  f_equal. auto.
Qed.

Lemma eqsys_walk_path_split s x y p1 p2 (H : eqsys_walk_path s x (p1 ++ y :: p2)) : eqsys_walk_path s y (y :: p2).
Proof.
  remember (p1 ++ y :: p2) as p. symmetry in Heqp. revert y p1 p2 Heqp. induction H; intros.
  * destruct p1; good_inversion Heqp. constructor. auto.
    apply app_eq_nil in H2. destruct H2. inversion H1.
  * destruct p1; good_inversion Heqp. eapply ESWalkPathWalk; eauto.
    eapply IHeqsys_walk_path. reflexivity.
  * destruct p1; good_inversion Heqp. eapply ESWalkPathCst. eauto.
    apply app_eq_nil in H2. destruct H2. inversion H1.
  * destruct p1; good_inversion Heqp. eapply ESWalkPathCon. eauto.
    apply app_eq_nil in H2. destruct H2. inversion H1.
Qed.

Lemma eqsys_walk_path_nodup s x p (H : eqsys_walk_path s x p) : NoDup p.
Proof.
  induction H. 1, 3, 4: apply singleton_nodup. constructor; auto. intro.
  apply in_split in H1. destruct H1 as [ p1 [ p2 H1 ] ].
  set (H2 := H0). rewrite H1 in H2. apply eqsys_walk_path_split in H2.
  eapply eqsys_walk_path_inj in H2. 2: { eapply ESWalkPathWalk. eauto. eauto. }
  good_inversion H2. rewrite (app_assoc p1 [x] p2 : p1 ++ x :: p2 = _) in H4.
  apply (app_inv_tail p2 _ []) in H4. apply app_eq_nil in H4. destruct H4. inversion H2.
Qed.

Lemma eqsys_walk_path_transport s x y r p1 p2 (H1 : eqsys_walk_result s x r)
                                (H2 : eqsys_walk_path s y (p1 ++ x :: p2))
                              : eqsys_walk_result s y r.
Proof.
  remember (p1 ++ x :: p2) as p. symmetry in Heqp. revert p1 Heqp.
  induction H2; intros; destruct p1; good_inversion Heqp; auto.
  all: try (apply app_eq_nil in H3; destruct H3; inversion H2).
  eapply ESWalkWalk. eauto. eapply IHeqsys_walk_path. reflexivity.
Qed.

Lemma eqsys_walk_path_transport_inv s x y r p1 p2 (H1 : eqsys_walk_result s y r)
                                    (H2 : eqsys_walk_path s y (p1 ++ x :: p2))
                                  : eqsys_walk_result s x r.
Proof.
  remember (p1 ++ x :: p2) as p. symmetry in Heqp. revert p1 Heqp.
  induction H2; intros; destruct p1; good_inversion Heqp; auto.
  all: try (apply app_eq_nil in H3; destruct H3; inversion H2).
  eapply IHeqsys_walk_path; eauto. good_inversion H1; rewrite H0 in H; good_inversion H. auto.
Qed.

Lemma eqsys_walk_path_result_fst s x y t (H : eqsys_walk_result s x (y, t))
                               : eqsys_walk_path s y [y].
Proof.
  remember (y, t) as res. symmetry in Heqres. revert y t Heqres. induction H; intros.
  * good_inversion Heqres. constructor. auto.
  * eapply IHeqsys_walk_result. eauto.
  * good_inversion Heqres. eapply ESWalkPathCst. eauto.
  * good_inversion Heqres. eapply ESWalkPathCon. eauto.
Qed.

Lemma eqsys_walk_path_result_fst_in s x p y t (H1 : eqsys_walk_path s x p)
                                    (H2 : eqsys_walk_result s x (y, t))
                                  : In y p.
Proof.
  induction H1; good_inversion H2; simpl; auto; rewrite H in *; try (inversion H0; fail).
  good_inversion H0. right. auto.
Qed.

Lemma eqsys_walk_path_extend_concat x y t s p q1 q2 (H1 : ~In x q1)
                                    (H2 : eqsys_walk_path ((x, t) :: s) x p)
                                    (H3 : eqsys_walk_path s y (q1 ++ x :: q2))
                                  : eqsys_walk_path ((x, t) :: s) y (q1 ++ p).
Proof.
  remember (q1 ++ x :: q2) as q. symmetry in Heqq. revert q1 q2 H1 Heqq.
  induction H3; intros; destruct q1; good_inversion Heqq; auto.
  1, 3, 4: apply app_eq_nil in H4; destruct H4; inversion H3.
  simpl. econstructor.
    - simpl. destruct (name_eq_dec x0 x). exfalso. apply H1. left. auto. eauto.
    - eapply IHeqsys_walk_path. intro. apply H1. right. auto. reflexivity.
Qed.

Lemma eqsys_walk_path_extend_same x y t s q (H1 : ~In x q) (H2 : eqsys_walk_path s y q)
                                : eqsys_walk_path ((x, t) :: s) y q.
Proof.
  induction H2.
  * constructor. simpl. destruct (name_eq_dec x0 x); auto. exfalso. apply H1. left. auto.
  * econstructor. simpl. destruct (name_eq_dec x0 x); eauto. exfalso. apply H1. left. auto.
    apply IHeqsys_walk_path. intro. apply H1. right. auto.
  * eapply ESWalkPathCst. simpl. destruct (name_eq_dec x0 x); eauto. exfalso. apply H1. left. auto.
  * eapply ESWalkPathCon. simpl. destruct (name_eq_dec x0 x); eauto. exfalso. apply H1. left. auto.
Qed.

Lemma eqsys_walk_result_ext s1 s2 x p r (H1 : eqsys_walk_result s1 x r) (H2 : eqsys_walk_path s1 x p)
                            (H3 : forall y, In y p -> eqsys_lookup s1 y = eqsys_lookup s2 y)
                          : eqsys_walk_result s2 x r.
Proof.
  induction H2; good_inversion H1; rewrite H in H0; good_inversion H0.
  * constructor. rewrite <- H3. auto. left. auto.
  * eapply ESWalkWalk. rewrite <- H3. eauto. left. auto. apply IHeqsys_walk_path. auto.
    intros. apply H3. right. auto.
  * eapply ESWalkCst. rewrite <- H3. auto. left. auto.
  * eapply ESWalkCon. rewrite <- H3. auto. left. auto.
Qed.

Definition eqsys_walkable (s : eqsys) (x : name) : Prop := exists r, eqsys_walk_result s x r.

Lemma eqsys_walkable_path s x : eqsys_walkable s x <-> exists p, eqsys_walk_path s x p.
Proof.
  constructor; intro.
  * destruct H as [ res H ]. induction H.
    - exists [x]. constructor. auto.
    - destruct IHeqsys_walk_result as [ p IH ]. exists (x :: p). econstructor; eauto.
    - exists [x]. eapply ESWalkPathCst. eauto.
    - exists [x]. eapply ESWalkPathCon. eauto.
  * destruct H as [ p H ]. induction H.
    - eexists. constructor. auto.
    - destruct IHeqsys_walk_path as [ res IH ]. exists res. econstructor; eauto.
    - eexists. apply ESWalkCst. eauto.
    - eexists. apply ESWalkCon. eauto.
Qed.

Lemma eqsys_walk_result_ext' s1 s2 x r (H1 : eqsys_walk_result s1 x r)
                             (H2 : forall y, eqsys_lookup s1 y = eqsys_lookup s2 y)
                           : eqsys_walk_result s2 x r.
Proof.
  edestruct eqsys_walkable_path as [ [ p H3 ] _ ]. eexists. eauto.
  eapply eqsys_walk_result_ext; eauto.
Qed.

Polymorphic Lemma in_split_dec {A : Type} (x : A) (dec : forall y, {x = y} + {x <> y}) xs (H : In x xs)
                             : exists xs1 xs2, xs = xs1 ++ x :: xs2 /\ ~In x xs1.
Proof.
  induction xs. inversion H. destruct (dec a).
  * subst a. clear H IHxs. exists []. exists xs. constructor. auto. intro. inversion H.
  * destruct H. subst a. contradiction. apply IHxs in H. destruct H as [ xs1 [ xs2 [ IH1 IH2 ] ] ].
    exists (a :: xs1). exists xs2. constructor. subst xs. auto.
    intro. destruct H. subst a. contradiction. auto.
Qed.

Lemma eqsys_walkable_extend x y t s (H1 : eqsys_walkable s y) (H2 : eqsys_walkable ((x, t) :: s) x)
                          : eqsys_walkable ((x, t) :: s) y.
Proof.
  apply eqsys_walkable_path in H1. destruct H1 as [ p H1 ].
  apply eqsys_walkable_path in H2. destruct H2 as [ q H2 ].
  apply eqsys_walkable_path. destruct (in_dec name_eq_dec x p) as [ H | H ].
  * apply (in_split_dec _ (name_eq_dec x)) in H. destruct H as [ p1 [ p2 [ H3 H4 ] ] ]. subst p.
    exists (p1 ++ q). eapply eqsys_walk_path_extend_concat; eauto.
  * exists p. apply eqsys_walk_path_extend_same; auto.
Qed.

Lemma eqsys_walkable_extend_var x y s (H : eqsys_walkable ((x, Var y) :: s) y)
                          : eqsys_walkable ((x, Var y) :: s) x.
Proof.
  destruct H as [ res H ]. exists res. econstructor; eauto. simpl.
  destruct (name_eq_dec x x). auto. contradiction.
Qed.

Lemma eqsys_walkable_fuel_path s x (H : eqsys_walkable s x) : exists p, eqsys_walk_fuel_path s x p.
Proof.
  destruct H as [ r H ]. induction H.
  * exists []. constructor. auto.
  * destruct IHeqsys_walk_result as [ p IH ]. exists (x :: p). econstructor; eauto.
  * exists [x]. eapply ESWalkFuelPathCst. eauto.
  * exists [x]. eapply ESWalkFuelPathCon. eauto.
Qed.

Lemma eqsys_walk_aux s x (H : eqsys_walkable s x) : { r | eqsys_walk_result s x r }.
Proof.
  exists (eqsys_walk_hlp (length s) s x). apply eqsys_walkable_fuel_path in H. destruct H as [ p H ].
  eapply eqsys_walk_hlp_fuel. eauto. transitivity (length (eqsys_dom s)).
  2: apply eqsys_dom_size. apply NoDup_incl_length. eapply eqsys_walk_fuel_path_nodup. eauto.
  eapply eqsys_walk_fuel_path_in_dom. eauto.
Qed.

Definition eqsys_well_formed (s : eqsys) : Prop := forall x, eqsys_walkable s x.

Lemma eqsys_well_formed_extend x t s (H1 : eqsys_well_formed s) (H2 : eqsys_walkable ((x, t) :: s) x)
                             : eqsys_well_formed ((x, t) :: s).
Proof. intro y. destruct (name_eq_dec x y). subst y. auto. apply eqsys_walkable_extend; auto. Qed.

Definition wf_eqsys : Set := { s | eqsys_well_formed s }.

Definition wf_eqsys_get (s : wf_eqsys) : eqsys := proj1_sig s.

Fact wf_eqsys_get_well_formed s : eqsys_well_formed (wf_eqsys_get s).
Proof. unfold wf_eqsys_get. apply proj2_sig. Qed.

Fact wf_eqsys_extend_well_formed s x t (H : eqsys_walkable ((x, t) :: wf_eqsys_get s) x)
                               : eqsys_well_formed ((x, t) :: wf_eqsys_get s).
Proof. apply eqsys_well_formed_extend; auto. apply wf_eqsys_get_well_formed. Qed.

Definition wf_eqsys_eq (s1 s2 : wf_eqsys) := wf_eqsys_get s1 = wf_eqsys_get s2.

Definition wf_eqsys_walk (s : wf_eqsys) (x : name) : name * term :=
  proj1_sig (eqsys_walk_aux (wf_eqsys_get s) x (wf_eqsys_get_well_formed s x)).

Fact wf_eqsys_walk_prop s x : eqsys_walk_result (wf_eqsys_get s) x (wf_eqsys_walk s x).
Proof. unfold wf_eqsys_walk. destruct eqsys_walk_aux. auto. Qed.

Corollary wf_eqsys_walk_ext s x r (H : eqsys_walk_result (wf_eqsys_get s) x r) : wf_eqsys_walk s x = r.
Proof. eapply eqsys_walk_result_inj. apply wf_eqsys_walk_prop. auto. Qed.

Lemma wf_eqsys_walk_eq s1 s2 x (H : wf_eqsys_eq s1 s2) : wf_eqsys_walk s1 x = wf_eqsys_walk s2 x.
Proof. apply wf_eqsys_walk_ext. rewrite H. apply wf_eqsys_walk_prop. Qed.

Lemma wf_eqsys_walk_var s x y z (H : wf_eqsys_walk s x = (y, Var z)) : y = z.
Proof. eapply eqsys_walk_result_var. rewrite <- H. apply wf_eqsys_walk_prop. Qed.

Lemma wf_eqsys_walk_var_dom s x y z (H : wf_eqsys_walk s x = (y, Var z))
                          : ~in_eqsys_dom (wf_eqsys_get s) z.
Proof. eapply eqsys_walk_result_var_dom. rewrite <- H. apply wf_eqsys_walk_prop. Qed.

Lemma wf_eqsys_walk_idemp s x : wf_eqsys_walk s x = wf_eqsys_walk s (fst (wf_eqsys_walk s x)).
Proof.
  specialize (wf_eqsys_walk_prop s x). intro H. remember (wf_eqsys_walk s x) as r.
  induction H; simpl; auto. apply IHeqsys_walk_result.
  symmetry. eapply wf_eqsys_walk_ext. eauto.
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
  * apply IHeqsys_walk_result. symmetry. eapply wf_eqsys_walk_ext. eauto.
  * left. apply eqsys_rhs_in. eexists. eauto.
  * left. apply eqsys_rhs_in. eexists. eauto.
Qed.

Lemma wf_eqsys_walk_extend_unbound s1 s2 x y t (H1 : ~in_eqsys_dom (wf_eqsys_get s1) x)
                                   (H2 : wf_eqsys_get s2 = (x, t) :: wf_eqsys_get s1)
                                 : wf_eqsys_walk s1 y = wf_eqsys_walk s2 y
                                \/ wf_eqsys_walk s1 y = (x, Var x)
                                /\ wf_eqsys_walk s2 y = wf_eqsys_walk s2 x.
Proof.
  assert (exists p, eqsys_walk_path (wf_eqsys_get s1) y p). {
    apply eqsys_walkable_path. eexists. apply wf_eqsys_walk_prop.
  }
  destruct H as [ p H ]. destruct (in_dec name_eq_dec x p).
  * right. apply (in_split_dec _ (name_eq_dec x)) in i.
    destruct i as [ p1 [ p2 [ H' i ] ] ]. subst. constructor.
    - apply wf_eqsys_walk_ext. eapply eqsys_walk_path_transport; eauto. constructor.
      apply in_eqsys_dom_inv. auto.
    - assert (exists q, eqsys_walk_path (wf_eqsys_get s2) x q). {
        apply eqsys_walkable_path. eexists. apply wf_eqsys_walk_prop.
      }
      destruct H0 as [ q H0 ]. apply wf_eqsys_walk_ext.
      eapply eqsys_walk_path_extend_concat in H; eauto.
      2: rewrite <- H2; eauto. rewrite <- H2 in H. destruct q. inversion H0.
      replace n with x in *. 2: { good_inversion H0; auto. }
      clear n. eapply eqsys_walk_path_transport; eauto. apply wf_eqsys_walk_prop.
  * left. symmetry. apply wf_eqsys_walk_ext. eapply eqsys_walk_result_ext. 2: eauto.
    apply wf_eqsys_walk_prop. intros. rewrite H2. simpl. destruct (name_eq_dec y0 x); auto.
    subst. contradiction.
Qed.

Lemma wf_eqsys_walk_extend_new s1 s2 x t (H1 : wf_eqsys_get s2 = (x, t) :: wf_eqsys_get s1)
                             : wf_eqsys_walk s2 x = (x, t) \/ exists y, t = Var y.
Proof.
  destruct t. right. eexists. auto.
  all: left; apply wf_eqsys_walk_ext; rewrite H1; constructor; simpl.
  all: destruct (name_eq_dec x x); auto; contradiction.
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

Lemma wf_eqsys_image_hlp_eq s1 s2 t (H : wf_eqsys_eq s1 s2)
                          : inf_term_eq (wf_eqsys_image_hlp s1 t) (wf_eqsys_image_hlp s2 t).
Proof.
  intros p l' Hp. remember (wf_eqsys_image_hlp s1 t) as t'. revert t Heqt'. induction Hp; intros.
  * eexists. constructor. constructor. rewrite Heqt'. clear t Heqt'. rename t0 into t.
    rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. destruct t; simpl; auto.
    erewrite wf_eqsys_walk_eq; eauto. destruct (wf_eqsys_walk s2 n). destruct t; reflexivity.
  * rewrite inf_term_step_prop in Heqt'. destruct t0; good_inversion Heqt'.
    - remember (wf_eqsys_walk s1 n) as res. destruct res. destruct t0; good_inversion H1.
      edestruct IHHp as [ r' [ IH1 IH2 ] ]. reflexivity. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. erewrite wf_eqsys_walk_eq. rewrite <- Heqres.
      constructor. auto. symmetry. auto.
    - edestruct IHHp as [ r' [ IH1 IH2 ] ]. reflexivity. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. constructor. auto.
  * rewrite inf_term_step_prop in Heqt'. destruct t0; good_inversion Heqt'.
    - remember (wf_eqsys_walk s1 n) as res. destruct res. destruct t0; good_inversion H1.
      edestruct IHHp as [ r' [ IH1 IH2 ] ]. reflexivity. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. erewrite wf_eqsys_walk_eq. rewrite <- Heqres.
      constructor. auto. symmetry. auto.
    - edestruct IHHp as [ r' [ IH1 IH2 ] ]. reflexivity. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. constructor. auto.
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

Corollary wf_eqsys_image_eq s1 s2 x (H : wf_eqsys_eq s1 s2)
                          : inf_term_eq (wf_eqsys_image s1 x) (wf_eqsys_image s2 x).
Proof. apply wf_eqsys_image_hlp_eq. auto. Qed.

Fixpoint wf_eqsys_apply (s : wf_eqsys) (t : term) :=
match t with
| Var x => wf_eqsys_image s x
| Cst c => InfCst c
| Con f l r => InfCon f (wf_eqsys_apply s l) (wf_eqsys_apply s r)
end.

Lemma wf_eqsys_image_hlp_apply s t : wf_eqsys_image_hlp s t = wf_eqsys_apply s t.
Proof.
  induction t; rewrite inf_term_step_prop at 1; simpl.
  * rewrite inf_term_step_prop. reflexivity.
  * reflexivity.
  * f_equal; auto.
Qed.

Lemma wf_eqsys_image_walk s x : inf_term_eq (wf_eqsys_image s x) (wf_eqsys_apply s (snd (wf_eqsys_walk s x))).
Proof. etransitivity. apply wf_eqsys_image_hlp_step. rewrite wf_eqsys_image_hlp_apply. reflexivity. Qed.

Lemma wf_eqsys_apply_eq s1 s2 t (H : wf_eqsys_eq s1 s2)
                      : inf_term_eq (wf_eqsys_apply s1 t) (wf_eqsys_apply s2 t).
Proof.
  induction t; simpl.
  * apply wf_eqsys_image_eq. auto.
  * reflexivity.
  * apply inf_term_eq_con; auto.
Qed.

Definition wf_eqsys_inf_subterms (s : wf_eqsys) : list inf_term :=
  map (wf_eqsys_apply s) (eqsys_subterms (wf_eqsys_get s)).

Definition wf_eqsys_to_subst (s : wf_eqsys) : inf_subst :=
  map (fun x => (x, wf_eqsys_image s x)) (eqsys_dom (wf_eqsys_get s)).

Lemma wf_eqsys_to_subst_dom' s x (H : In x (inf_subst_dom (wf_eqsys_to_subst s)))
                           : in_eqsys_dom (wf_eqsys_get s) x.
Proof.
  apply eqsys_dom_spec. unfold wf_eqsys_to_subst in H.
  remember (eqsys_dom (wf_eqsys_get s)) as xs. clear Heqxs.
  induction xs as [ | y xs IH ]. inversion H. simpl in H.
  remember (wf_eqsys_walk s y) as res. destruct res. destruct t. destruct (name_eq_dec y n0).
  right. apply IH. eapply ListSet.set_remove_1. eauto.
  all: apply ListSet.set_add_elim in H; destruct H; [ left | right; apply IH ]; auto.
Qed.

Lemma wf_eqsys_to_subst_image s x : inf_image (wf_eqsys_to_subst s) x = wf_eqsys_image s x.
Proof.
  destruct (in_dec name_eq_dec x (eqsys_dom (wf_eqsys_get s))).
  * unfold wf_eqsys_to_subst. remember (eqsys_dom (wf_eqsys_get s)) as xs. clear Heqxs.
    induction xs as [ | y xs IH ]. inversion i. simpl. destruct (name_eq_dec x y). subst. auto.
    apply IH. destruct i; auto. subst. contradiction.
  * transitivity (InfVar x).
    - apply inf_image_dom. intro. apply n. apply eqsys_dom_spec. apply wf_eqsys_to_subst_dom'. auto.
    - rewrite inf_term_step_prop. simpl.
      erewrite (wf_eqsys_walk_ext _ _ (x, Var x)). auto.
      constructor. apply in_eqsys_dom_inv. intro. apply n. apply eqsys_dom_spec. auto.
Qed.

Lemma wf_eqsys_to_subst_dom s x : in_eqsys_dom (wf_eqsys_get s) x
                              <-> In x (inf_subst_dom (wf_eqsys_to_subst s)).
Proof.
  constructor; intro.
  * apply inf_image_dom_inv. rewrite wf_eqsys_to_subst_image.
    rewrite inf_term_step_prop at 1. simpl.
    assert (eqsys_walkable (wf_eqsys_get s) x). apply wf_eqsys_get_well_formed.
    destruct H0 as [ res H0 ]. erewrite wf_eqsys_walk_ext; eauto. destruct res as [ y t ].
    destruct t; try (intro; inversion H1; fail). apply eqsys_walk_result_var_dom in H0.
    intro. good_inversion H1. auto.
  * apply wf_eqsys_to_subst_dom'. auto.
Qed.

Lemma wf_eqsys_to_subst_apply s t
  : inf_term_eq (inf_subst_apply (wf_eqsys_to_subst s) (term_to_inf t)) (wf_eqsys_apply s t).
Proof.
  symmetry. induction t; rewrite inf_term_step_prop; simpl.
  * rewrite wf_eqsys_to_subst_image. fold (inf_term_step (wf_eqsys_image s n)).
    rewrite <- inf_term_step_prop. reflexivity.
  * rewrite inf_term_step_prop. simpl. reflexivity.
  * apply inf_term_eq_con; auto.
Qed.

Lemma wf_eqsys_to_subst_eq s1 s2 (H : wf_eqsys_eq s1 s2)
                         : inf_subst_eq (wf_eqsys_to_subst s1) (wf_eqsys_to_subst s2).
Proof.
  apply inf_subst_eq_ext. intro. repeat rewrite wf_eqsys_to_subst_image.
  apply wf_eqsys_image_eq. auto.
Qed.

Lemma wf_eqsys_to_subst_ext_walk s1 s2 (H : forall x, wf_eqsys_walk s1 x = wf_eqsys_walk s2 x)
                               : inf_subst_eq (wf_eqsys_to_subst s1) (wf_eqsys_to_subst s2).
Proof.
  apply inf_subst_eq_ext. intro. repeat rewrite wf_eqsys_to_subst_image.
  unfold wf_eqsys_image. generalize (Var x). clear x. intro. intros p l' Hp.
  remember (wf_eqsys_image_hlp s1 t) as t'. revert t Heqt'. induction Hp; intros.
  * subst. eexists. constructor. constructor. destruct t0; simpl; auto.
    rewrite H. destruct (wf_eqsys_walk s2 n). destruct t; auto.
  * rewrite inf_term_step_prop in Heqt'. destruct t0; good_inversion Heqt'.
    - remember (wf_eqsys_walk s1 n) as res. destruct res. destruct t0; good_inversion H1.
      edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. rewrite <- H, <- Heqres. constructor. auto.
    - edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. constructor. auto.
  * rewrite inf_term_step_prop in Heqt'. destruct t0; good_inversion Heqt'.
    - remember (wf_eqsys_walk s1 n) as res. destruct res. destruct t0; good_inversion H1.
      edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. rewrite <- H, <- Heqres. constructor. auto.
    - edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. constructor. auto.
Qed.

Lemma wf_eqsys_to_subst_ext_lookup s1 s2
  (H : forall x, eqsys_lookup (wf_eqsys_get s1) x = eqsys_lookup (wf_eqsys_get s2) x)
: inf_subst_eq (wf_eqsys_to_subst s1) (wf_eqsys_to_subst s2).
Proof.
  apply wf_eqsys_to_subst_ext_walk. intro. apply wf_eqsys_walk_ext.
  eapply eqsys_walk_result_ext'. apply wf_eqsys_walk_prop. auto.
Qed.

Theorem wf_eqsys_to_subst_triangular s : inf_subst_triangular (wf_eqsys_to_subst s).
Proof.
  intros x y H1 H2. rewrite wf_eqsys_to_subst_image in H2.
  apply wf_eqsys_image_hlp_subterm in H2. destruct H2 as [ t [ H2 H3 ] ].
  edestruct (H2 Here). constructor. destruct H. good_inversion H. clear H2.
  rewrite inf_term_step_prop in H0. destruct t; try inversion H0. simpl in H0.
  remember (wf_eqsys_walk s n) as res. destruct res as [ z t ]. destruct t; good_inversion H0.
  symmetry in Heqres. set (H' := Heqres). eapply wf_eqsys_walk_var in H'. subst n0.
  assert (eqsys_walk_result (wf_eqsys_get s) n (z, Var z)).
  rewrite <- Heqres. apply wf_eqsys_walk_prop. apply eqsys_walk_result_var_dom in H.
  apply H. apply wf_eqsys_to_subst_dom. auto.
Qed.

Theorem wf_eqsys_to_subst_rational s : is_rational_subst (wf_eqsys_to_subst s).
Proof.
  exists (fun x => InfVar (fst (wf_eqsys_walk s x)) :: wf_eqsys_inf_subterms s). intros.
  rewrite wf_eqsys_to_subst_image in H. apply wf_eqsys_image_hlp_subterm in H. simpl in H.
  destruct H as [ r [ H1 H2 ] ]. destruct H2.
  * destruct H. 2: inversion H. subst. destruct (wf_eqsys_walk_rhs s x).
    - apply Exists_cons_tl. apply Exists_map. apply Exists_flat_map. apply Exists_exists.
      exists (snd (wf_eqsys_walk s x)). constructor. auto. apply Exists_exists.
      exists (snd (wf_eqsys_walk s x)). constructor. apply term_subterms_self.
      etransitivity. eauto. apply wf_eqsys_image_walk.
    - destruct H as [ y H ]. rewrite H. simpl. apply Exists_cons_hd. etransitivity. eauto.
      rewrite inf_term_step_prop at 1. simpl. rewrite H. reflexivity.
  * apply Exists_cons_tl. apply Exists_map. apply Exists_exists. eexists. constructor. eauto.
    etransitivity. eauto. rewrite wf_eqsys_image_hlp_apply. reflexivity.
Qed.

Corollary wf_eqsys_to_subst_image_rational s x : is_rational_term (inf_image (wf_eqsys_to_subst s) x).
Proof. eapply inf_image_rational; eauto. apply wf_eqsys_to_subst_rational. Qed.

Corollary wf_eqsys_to_subst_apply_rational s t (H : is_rational_term t)
                                         : is_rational_term (inf_subst_apply (wf_eqsys_to_subst s) t).
Proof. apply inf_subst_apply_rational; auto. apply wf_eqsys_to_subst_rational. Qed.

Corollary wf_eqsys_image_rational s x : is_rational_term (wf_eqsys_image s x).
Proof. rewrite <- wf_eqsys_to_subst_image. apply wf_eqsys_to_subst_image_rational. Qed.

Corollary wf_eqsys_apply_rational s t : is_rational_term (wf_eqsys_apply s t).
Proof.
  eapply is_rational_eq. apply wf_eqsys_to_subst_apply.
  apply inf_subst_apply_rational. apply wf_eqsys_to_subst_rational.
  apply term_to_inf_rational.
Qed.

Lemma wf_eqsys_to_subst_extend_unbound s1 s2 x t (H1 : ~in_eqsys_dom (wf_eqsys_get s1) x)
                                       (H2 : wf_eqsys_get s2 = (x, t) :: wf_eqsys_get s1)
  : inf_subst_eq (wf_eqsys_to_subst s2)
                 (inf_subst_compose (inf_subst_singleton x (wf_eqsys_image s2 x))
                                    (wf_eqsys_to_subst s1)).
Proof.
  apply inf_subst_eq_ext. intro y. rewrite inf_subst_compose_image.
  repeat rewrite wf_eqsys_to_subst_image. unfold wf_eqsys_image.
  generalize (Var y). clear y. intros t' p l' Hp.
  remember (wf_eqsys_image_hlp s2 t') as l. revert t' Heql. induction Hp; intros.
  * subst. eexists. constructor. constructor. destruct t'; simpl; auto.
    edestruct wf_eqsys_walk_extend_unbound; eauto.
    - rewrite <- H. destruct (wf_eqsys_walk s1 n). destruct t0; auto.
      destruct (name_eq_dec n1 x); auto. subst. symmetry in H.
      set (H' := H). apply wf_eqsys_walk_var in H'. subst.
      set (H' := H). rewrite wf_eqsys_walk_idemp in H'. rewrite H in H'. simpl in H'.
      simpl. rewrite H'. auto.
    - destruct H. rewrite H. destruct (name_eq_dec x x). 2: contradiction. rewrite H0. simpl.
      destruct (wf_eqsys_walk s2 x). destruct t0; auto.
  * rewrite inf_term_step_prop in Heql; destruct t'; good_inversion Heql.
    - remember (wf_eqsys_walk s2 n) as res. destruct res. destruct t1; good_inversion H0.
      edestruct wf_eqsys_walk_extend_unbound; eauto.
      + edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto.
        exists r'. constructor; auto. rewrite inf_term_step_prop at 1. simpl.
        rewrite H. rewrite <- Heqres. constructor. auto.
      + destruct H. exists t0. constructor; try reflexivity.
        rewrite inf_term_step_prop at 1. simpl. rewrite H.
        destruct (name_eq_dec x x). 2: contradiction. simpl.
        rewrite <- H0. rewrite <- Heqres. constructor. auto.
    - edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. constructor. auto.
  * rewrite inf_term_step_prop in Heql; destruct t'; good_inversion Heql.
    - remember (wf_eqsys_walk s2 n) as res. destruct res. destruct t1; good_inversion H0.
      edestruct wf_eqsys_walk_extend_unbound; eauto.
      + edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto.
        exists r'. constructor; auto. rewrite inf_term_step_prop at 1. simpl.
        rewrite H. rewrite <- Heqres. constructor. auto.
      + destruct H. exists t0. constructor; try reflexivity.
        rewrite inf_term_step_prop at 1. simpl. rewrite H.
        destruct (name_eq_dec x x). 2: contradiction. simpl.
        rewrite <- H0. rewrite <- Heqres. constructor. auto.
    - edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. constructor. auto.
Qed.

Lemma wf_eqsys_to_subst_extend_unbound_more_general s1 s2 x t
  (H1 : ~in_eqsys_dom (wf_eqsys_get s1) x) (H2 : wf_eqsys_get s2 = (x, t) :: wf_eqsys_get s1)
: inf_subst_more_general (wf_eqsys_to_subst s1) (wf_eqsys_to_subst s2).
Proof.
  exists (inf_subst_singleton x (wf_eqsys_image s2 x)).
  eapply wf_eqsys_to_subst_extend_unbound; eauto.
Qed.

Inductive is_common_part : term -> term -> term -> Prop :=
| VarLCP x t : is_common_part (Var x) t (Var x)
| VarRCP x t : is_common_part t (Var x) (Var x)
| CstCP c : is_common_part (Cst c) (Cst c) (Cst c)
| ConCP f l1 l2 l r1 r2 r : is_common_part l1 l2 l -> is_common_part r1 r2 r -> is_common_part (Con f l1 r1) (Con f l2 r2) (Con f l r)
.

Lemma is_common_part_inf_unifiable s t1 t2 (H : inf_unifier (term_to_inf t1) (term_to_inf t2) s)
                                 : exists t, is_common_part t1 t2 t.
Proof.
  revert t2 H. induction t1; intros.
  * exists (Var n). constructor.
  * destruct t2.
    - exists (Var n0). constructor.
    - edestruct (H Here) as [ t [ H1 H2 ] ]. constructor. good_inversion H1.
      rewrite inf_term_step_prop in H2 at 1. rewrite inf_term_step_prop in H2.
      good_inversion H2. exists (Cst n0). constructor.
    - edestruct (H Here) as [ t [ H1 H2 ] ]. constructor. good_inversion H1.
      rewrite inf_term_step_prop in H2 at 1. rewrite inf_term_step_prop in H2. good_inversion H2.
  * destruct t2.
    - exists (Var n0). constructor.
    - edestruct (H Here) as [ t [ H1 H2 ] ]. constructor. good_inversion H1.
      rewrite inf_term_step_prop in H2 at 1. rewrite inf_term_step_prop in H2. good_inversion H2.
    - edestruct (H Here) as [ t [ H1 H2 ] ]. constructor. good_inversion H1.
      rewrite inf_term_step_prop in H2 at 1. rewrite inf_term_step_prop in H2. good_inversion H2.
      unfold inf_unifier in H. rewrite inf_term_step_prop in H at 1. rewrite inf_term_step_prop in H.
      simpl in H.
      edestruct IHt1_1 as [ l H2 ]. eapply inf_term_eq_conl. eauto.
      edestruct IHt1_2 as [ r H3 ]. eapply inf_term_eq_conr. eauto.
      exists (Con n0 l r). constructor; auto.
Qed.

Corollary is_common_part_unifiable s t1 t2 (H : unifier s t1 t2) : exists t, is_common_part t1 t2 t.
Proof. eapply is_common_part_inf_unifiable. apply unifier_inf. eauto. Qed.

Lemma common_part_aux t1 t2 : { t | is_common_part t1 t2 t } + {~exists t, is_common_part t1 t2 t}.
Proof.
  revert t2. induction t1; intro.
  * left. exists (Var n). constructor.
  * destruct t2.
    - left. exists (Var n0). constructor.
    - destruct (name_eq_dec n n0). subst n0. left. exists (Cst n). constructor.
      right. intro. destruct H. good_inversion H. auto.
    - right. intro. destruct H. good_inversion H.
  * destruct t2.
    - left. exists (Var n0). constructor.
    - right. intro. destruct H. good_inversion H.
    - destruct (name_eq_dec n n0). 2: { right. intro. destruct H. good_inversion H. auto. }
      subst n0. destruct (IHt1_1 t2_1). destruct (IHt1_2 t2_2).
      destruct s as [ l H1 ]. destruct s0 as [ r H2 ]. left. exists (Con n l r). constructor; auto.
      all: right; intro; destruct H; good_inversion H; apply n0; eexists; eauto.
Qed.

Definition common_part (t1 t2 : term) : option term :=
match common_part_aux t1 t2 with
| inleft (exist _ t _) => Some t
| inright _ => None
end.

Fact common_part_none t1 t2 : common_part t1 t2 = None <-> ~exists t, is_common_part t1 t2 t.
Proof.
  unfold common_part. destruct (common_part_aux t1 t2).
  * destruct s as [ t H ]. constructor; intro. inversion H0. exfalso. apply H0. eexists. eauto.
  * constructor; intro; auto.
Qed.

Fact common_part_some t1 t2 t (H : common_part t1 t2 = Some t) : is_common_part t1 t2 t.
Proof.
  unfold common_part in H. destruct (common_part_aux t1 t2).
  * destruct s as [ t' H1 ]. good_inversion H. auto.
  * inversion H.
Qed.

Fact common_part_some' t1 t2 : (exists t, common_part t1 t2 = Some t) <-> (exists t, is_common_part t1 t2 t).
Proof.
  constructor; intro; destruct H as [ t H ].
  * exists t. apply common_part_some. auto.
  * remember (common_part t1 t2). destruct o. eexists. eauto.
    symmetry in Heqo. apply common_part_none in Heqo. exfalso. apply Heqo. eexists. eauto.
Qed.

Definition wf_eqsys_union_result_hlp (s : wf_eqsys) (x y : name)
                                     (res : option (wf_eqsys * option (term * term))) : Prop :=
match res with
| None =>
  forall s', inf_subst_more_general (wf_eqsys_to_subst s) s' -> ~inf_unifier (InfVar x) (InfVar y) s'
| Some (s', None) =>
  inf_min_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst s) (wf_eqsys_to_subst s')
| Some (s', Some (t1, t2)) =>
  forall s'', inf_min_unifying_extension (term_to_inf t1) (term_to_inf t2) (wf_eqsys_to_subst s') s''
           -> inf_min_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst s) s''
end.

Lemma wf_eqsys_union_result_hlp_sym s x y res (H : wf_eqsys_union_result_hlp s x y res)
                                  : wf_eqsys_union_result_hlp s y x res.
Proof.
  destruct res. destruct p as [ s' ts ]. destruct ts. destruct p as [ t1 t2 ]. all: simpl in *.
  * intros. apply inf_min_unifying_extension_sym. auto.
  * apply inf_min_unifying_extension_sym. auto.
  * intros. intro. eapply H; eauto. apply inf_unifier_sym. auto.
Qed.

Definition wf_eqsys_union_spec
  (union : wf_eqsys -> name -> name -> option (wf_eqsys * option (term * term))) : Prop :=
  forall s x y, wf_eqsys_union_result_hlp s x y (union s x y).

Definition eqsys_union (s : wf_eqsys) (x y : name) : option (eqsys * option (term * term)) :=
  let (x, xt) := wf_eqsys_walk s x in
  let (y, yt) := wf_eqsys_walk s y in

  if name_eq_dec x y then Some (wf_eqsys_get s, None)
  else match xt, yt with
  | Var _, _ => Some ((x, yt) :: wf_eqsys_get s, None)
  | _, Var _ => Some ((y, xt) :: wf_eqsys_get s, None)
  | _, _ =>
    match common_part xt yt with
    | Some t => Some ((x, t) :: wf_eqsys_get s, Some (xt, yt))
    | None => None
    end
  end.

Lemma eqsys_union_well_formed s s' x y res (H : eqsys_union s x y = Some (s', res))
                            : eqsys_well_formed s'.
Proof.
  unfold eqsys_union in H.
  remember (wf_eqsys_walk s x) as res1. symmetry in Heqres1. destruct res1 as [ x' xt ].
  remember (wf_eqsys_walk s y) as res2. symmetry in Heqres2. destruct res2 as [ y' yt ].
  destruct (name_eq_dec x' y'). good_inversion H. apply wf_eqsys_get_well_formed.
  destruct xt; destruct yt; good_inversion H.
  * set (H' := Heqres2). apply wf_eqsys_walk_var in H'. subst n1.
    apply wf_eqsys_extend_well_formed. apply eqsys_walkable_extend_var. apply eqsys_walkable_path.
    exists [y']. apply eqsys_walk_path_extend_same.
    - intro. destruct H; good_inversion H. contradiction.
    - eapply eqsys_walk_path_result_fst. erewrite <- Heqres2. apply wf_eqsys_walk_prop.
  * apply wf_eqsys_extend_well_formed. eexists. eapply ESWalkCst. simpl.
    destruct (name_eq_dec x' x'). auto. contradiction.
  * apply wf_eqsys_extend_well_formed. eexists. eapply ESWalkCon. simpl.
    destruct (name_eq_dec x' x'). auto. contradiction.
  * apply wf_eqsys_extend_well_formed. eexists. eapply ESWalkCst. simpl.
    destruct (name_eq_dec y' y'). auto. contradiction.
  * remember (common_part (Cst n0) (Cst n1)) as t. destruct t as [ t | ]; good_inversion H1.
    symmetry in Heqt. apply common_part_some in Heqt. good_inversion Heqt.
    apply wf_eqsys_extend_well_formed. eexists. eapply ESWalkCst. simpl.
    destruct (name_eq_dec x' x'). auto. contradiction.
  * remember (common_part (Cst n0) (Con n1 yt1 yt2)) as t. destruct t as [ t | ]; good_inversion H1.
    symmetry in Heqt. apply common_part_some in Heqt. inversion Heqt.
  * apply wf_eqsys_extend_well_formed. eexists. eapply ESWalkCon. simpl.
    destruct (name_eq_dec y' y'). auto. contradiction.
  * remember (common_part (Con n0 xt1 xt2) (Cst n1)) as t. destruct t as [ t | ]; good_inversion H1.
    symmetry in Heqt. apply common_part_some in Heqt. inversion Heqt.
  * remember (common_part (Con n0 xt1 xt2) (Con n1 yt1 yt2)) as t.
    destruct t as [ t | ]; good_inversion H1. symmetry in Heqt.
    apply common_part_some in Heqt. good_inversion Heqt.
    apply wf_eqsys_extend_well_formed. eexists. eapply ESWalkCon. simpl.
    destruct (name_eq_dec x' x'). auto. contradiction.
Qed.

Lemma wf_eqsys_union_aux s x y : { res | match res with
                                         | None => eqsys_union s x y = None
                                         | Some (s', ts) => eqsys_union s x y = Some (wf_eqsys_get s', ts)
                                         end }.
Proof.
  remember (eqsys_union s x y) as res. destruct res as [ res | ].
  * symmetry in Heqres. destruct res as [ s' ts ].
    set (s'' := exist _ s' (eqsys_union_well_formed _ _ _ _ _ Heqres) : wf_eqsys).
    exists (Some (s'', ts)). auto.
  * exists None. auto.
Defined.

Definition wf_eqsys_union (s : wf_eqsys) (x y : name) : option (wf_eqsys * option (term * term)) :=
  proj1_sig (wf_eqsys_union_aux s x y).

Fact wf_eqsys_union_some s x y s' ts (H : wf_eqsys_union s x y = Some (s', ts))
                       : eqsys_union s x y = Some (wf_eqsys_get s', ts).
Proof. unfold wf_eqsys_union in H. destruct (wf_eqsys_union_aux s x y). simpl in H. subst. auto. Qed.

Fact wf_eqsys_union_none s x y (H : wf_eqsys_union s x y = None) : eqsys_union s x y = None.
Proof. unfold wf_eqsys_union in H. destruct (wf_eqsys_union_aux s x y). simpl in H. subst. auto. Qed.

Lemma wf_eqsys_union_prop_same s x y z xt yt
                               (H1 : wf_eqsys_walk s x = (z, xt))
                               (H2 : wf_eqsys_walk s y = (z, yt))
                             : wf_eqsys_union_result_hlp s x y (wf_eqsys_union s x y).
Proof.
  remember (wf_eqsys_union s x y) as res. symmetry in Heqres. destruct res as [ res | ].
  2: {
    apply wf_eqsys_union_none in Heqres. unfold eqsys_union in Heqres. rewrite H1, H2 in Heqres.
    destruct (name_eq_dec z z). inversion Heqres. contradiction.
  }
  destruct res as [ s' ts ]. apply wf_eqsys_union_some in Heqres.
  unfold eqsys_union in Heqres. rewrite H1, H2 in Heqres.
  destruct (name_eq_dec z z); try contradiction. clear e. good_inversion Heqres; simpl.
  set (H' := H2). eapply wf_eqsys_walk_fst_inj in H'. 2: apply H1. subst. rename yt into t.
  eapply inf_min_unifying_extension_eq; try apply inf_min_unifying_extension_same.
  1, 2, 3: reflexivity. apply wf_eqsys_to_subst_eq. auto.
  apply inf_unifier_triangular. apply wf_eqsys_to_subst_triangular. apply inf_unifier_sym.
  apply inf_unifier_triangular. apply wf_eqsys_to_subst_triangular. apply inf_unifier_sym.
  rewrite (inf_term_step_prop (inf_subst_apply _ (InfVar x))).
  rewrite (inf_term_step_prop (inf_subst_apply _ (InfVar y))).
  simpl. repeat rewrite wf_eqsys_to_subst_image. simpl. rewrite H1, H2.
  apply inf_unifier_refl.
Qed.

Lemma wf_eqsys_union_prop_var_l s x y x' (H1 : wf_eqsys_walk s x = (x', Var x'))
                                (H2 : forall y' yt, wf_eqsys_walk s y = (y', yt) -> x' <> y')
                              : wf_eqsys_union_result_hlp s x y (wf_eqsys_union s x y).
Proof.
  remember (wf_eqsys_union s x y) as res. symmetry in Heqres. destruct res as [ res | ].
  2: {
    apply wf_eqsys_union_none in Heqres. unfold eqsys_union in Heqres. rewrite H1 in Heqres.
    destruct (wf_eqsys_walk s y). destruct (name_eq_dec x' n); inversion Heqres.
  }
  destruct res as [ s' ts ]. apply wf_eqsys_union_some in Heqres.
  unfold eqsys_union in Heqres. rewrite H1 in Heqres.
  remember (wf_eqsys_walk s y) as y'. destruct y' as [ y' t ]. symmetry in Heqy'.
  destruct (name_eq_dec x' y'); good_inversion Heqres; simpl. exfalso. eapply H2; auto. clear H2.
  assert (~in_eqsys_dom (wf_eqsys_get s) x'). eapply wf_eqsys_walk_var_dom. eauto.
  assert (wf_eqsys_walk s' y = wf_eqsys_walk s y). {
    edestruct wf_eqsys_walk_extend_unbound; eauto. destruct H2; auto.
    rewrite H2 in Heqy'. good_inversion Heqy'. contradiction.
  }
  assert (wf_eqsys_walk s' x = wf_eqsys_walk s' x'). {
    edestruct wf_eqsys_walk_extend_unbound; eauto. 2: destruct H3; eauto.
    rewrite H3 in H1. apply wf_eqsys_walk_var_dom in H1. exfalso. apply H1.
    eexists. rewrite <- H0. simpl. destruct (name_eq_dec x' x'); try contradiction. auto.
  }
  assert (snd (wf_eqsys_walk s' x') = t). {
    edestruct wf_eqsys_walk_extend_new; eauto. rewrite H4. auto. destruct H4. subst.
    set (H' := Heqy'). apply wf_eqsys_walk_var in H'. subst x0.
    replace (wf_eqsys_walk s' x') with (y', Var y'). auto. symmetry.
    apply wf_eqsys_walk_ext. econstructor. rewrite <- H0. simpl.
    destruct (name_eq_dec x' x'); try contradiction. auto.
    constructor. apply in_eqsys_dom_inv. eapply wf_eqsys_walk_var_dom. rewrite H2. eauto.
  }
  symmetry in H0. constructor. constructor.
  * eapply wf_eqsys_to_subst_extend_unbound_more_general; eauto.
  * apply inf_unifier_triangular. apply wf_eqsys_to_subst_triangular.
    rewrite inf_term_step_prop at 1. simpl. rewrite wf_eqsys_to_subst_image.
    fold (inf_term_step (wf_eqsys_image s' x)). rewrite <- inf_term_step_prop.
    eapply inf_unifier_eq. symmetry. apply wf_eqsys_image_walk. reflexivity. reflexivity.
    rewrite H3. rewrite H4. apply inf_unifier_sym. apply inf_unifier_triangular.
    apply wf_eqsys_to_subst_triangular. rewrite inf_term_step_prop at 1. simpl.
    rewrite wf_eqsys_to_subst_image. fold (inf_term_step (wf_eqsys_image s' y)).
    rewrite <- inf_term_step_prop. eapply inf_unifier_eq. symmetry. apply wf_eqsys_image_walk.
    reflexivity. reflexivity. rewrite H2. rewrite Heqy'. simpl. apply inf_unifier_refl.
  * intro s1. intros. destruct H5 as [ [ s1' H5 ] H6 ].
    exists s1'. etransitivity. eauto. symmetry.
    etransitivity. apply inf_subst_compose_eq. reflexivity.
    eapply wf_eqsys_to_subst_extend_unbound; eauto.
    etransitivity. apply inf_subst_compose_assoc.
    apply inf_subst_compose_eq; try reflexivity.
    apply inf_subst_eq_ext. intro z. rewrite inf_subst_compose_image. simpl.
    destruct (name_eq_dec z x'). 2: {
      rewrite inf_term_step_prop at 1. simpl. fold (inf_term_step (inf_image s1' z)).
      rewrite <- inf_term_step_prop. reflexivity.
    }
    subst z. symmetry. eapply inf_subst_recursive_unifier.
    - etransitivity. apply wf_eqsys_image_walk. rewrite H4.
      etransitivity. symmetry. apply wf_eqsys_to_subst_apply.
      etransitivity. eapply wf_eqsys_to_subst_extend_unbound; eauto.
      symmetry. apply inf_subst_compose_spec.
    - replace (inf_image s1' x')
         with (inf_subst_apply s1' (inf_subst_apply (wf_eqsys_to_subst s) (InfVar x))).
      etransitivity. apply inf_subst_compose_spec. etransitivity. symmetry. apply H5.
      etransitivity. apply H6. etransitivity. apply H5.
      etransitivity. symmetry. apply inf_subst_compose_spec. apply inf_subst_apply_eq.
      replace (inf_subst_apply (wf_eqsys_to_subst s) (InfVar y)) with (wf_eqsys_image s y).
      etransitivity. apply wf_eqsys_image_walk. rewrite Heqy'.
      symmetry. apply wf_eqsys_to_subst_apply.
      rewrite inf_term_step_prop. simpl. rewrite wf_eqsys_to_subst_image.
      rewrite inf_term_step_prop at 1. auto.
      rewrite inf_term_step_prop at 1. simpl. rewrite wf_eqsys_to_subst_image. simpl.
      rewrite H1. rewrite inf_term_step_prop. auto.
    - intro. rewrite inf_term_step_prop in H7 at 1. destruct t; good_inversion H7.
      rewrite wf_eqsys_to_subst_image in H9. simpl in H9.
      set (H' := Heqy'). apply wf_eqsys_walk_var in H'. subst n0.
      apply wf_eqsys_walk_var_dom in Heqy'. apply in_eqsys_dom_inv in Heqy'.
      erewrite wf_eqsys_walk_ext in H9. 2: constructor; auto. simpl in H9.
      good_inversion H9. contradiction.
Qed.

Lemma wf_eqsys_union_prop_var_r s x y y' (H1 : wf_eqsys_walk s y = (y', Var y'))
                                (H2 : forall x' xt, wf_eqsys_walk s x = (x', xt) -> x' <> y')
                                (H3 : forall x' z, wf_eqsys_walk s x <> (x', Var z))
                              : wf_eqsys_union_result_hlp s x y (wf_eqsys_union s x y).
Proof.
  remember (wf_eqsys_union s x y) as res. symmetry in Heqres. destruct res as [ res | ]. 2: {
    apply wf_eqsys_union_none in Heqres. unfold eqsys_union in Heqres. rewrite H1 in Heqres.
    destruct (wf_eqsys_walk s x). destruct (name_eq_dec n y'). inversion Heqres.
    destruct t; inversion Heqres.
  }
  destruct res as [ s' ts ]. apply wf_eqsys_union_some in Heqres.
  unfold eqsys_union in Heqres. rewrite H1 in Heqres.
  remember (wf_eqsys_walk s x) as x'. destruct x' as [ x' t ]. symmetry in Heqx'.
  destruct (name_eq_dec x' y'); good_inversion Heqres; simpl. exfalso. eapply H2; auto.
  assert (Some ((y', t) :: wf_eqsys_get s, None) = Some (wf_eqsys_get s', ts)). {
    destruct t; auto. exfalso. eapply H3. auto.
  }
  clear H3 H0. good_inversion H.
  set (H' := H1). eapply wf_eqsys_union_prop_var_l in H'. 2: {
    intros. symmetry. eapply H2. rewrite <- Heqx'. eauto.
  }
  clear H2. remember (wf_eqsys_union s y x) as res'. symmetry in Heqres'.
  destruct res' as [ res' | ]. 2: {
    apply wf_eqsys_union_none in Heqres'. unfold eqsys_union in Heqres'. rewrite H1 in Heqres'.
    rewrite Heqx' in Heqres'. destruct (name_eq_dec y' x'); inversion Heqres'.
  }
  destruct res' as [ s1 ts1 ]. apply wf_eqsys_union_some in Heqres'.
  unfold eqsys_union in Heqres'. rewrite H1, Heqx' in Heqres'.
  destruct (name_eq_dec y' x'). subst. contradiction. clear n0.
  good_inversion Heqres'. simpl in H'. apply inf_min_unifying_extension_sym.
  eapply inf_min_unifying_extension_eq; eauto; try reflexivity.
  apply wf_eqsys_to_subst_eq. unfold wf_eqsys_eq. rewrite <- H0. auto.
Qed.

Lemma wf_eqsys_union_prop : wf_eqsys_union_spec wf_eqsys_union.
Proof.
  intros s x y. remember (wf_eqsys_union s x y) as res.
  symmetry in Heqres. destruct res as [ res | ].
  * destruct res as [ s' ts ].
    remember (wf_eqsys_walk s x) as res1. symmetry in Heqres1. destruct res1 as [ x' tx ].
    remember (wf_eqsys_walk s y) as res2. symmetry in Heqres2. destruct res2 as [ y' ty ].
    remember (name_eq_dec x' y') as cond. symmetry in Heqcond. destruct cond. {
      subst y'. rewrite <- Heqres. eapply wf_eqsys_union_prop_same; eauto.
    }
    destruct tx.
    set (H' := Heqres1). apply wf_eqsys_walk_var in H'. subst n0.
    rewrite <- Heqres. eapply wf_eqsys_union_prop_var_l; eauto. {
      intros. rewrite H in Heqres2. good_inversion Heqres2. auto.
    }
    all: destruct ty.
    1, 4: set (H' := Heqres2); apply wf_eqsys_walk_var in H'; subst n1;
        rewrite <- Heqres; eapply wf_eqsys_union_prop_var_r; eauto;
        [ intros; rewrite H in Heqres1; good_inversion Heqres1; auto
        | intros; rewrite Heqres1; intro; inversion H
        ].
    all: apply wf_eqsys_union_some in Heqres; unfold eqsys_union in Heqres.
    all: rewrite Heqres1, Heqres2, Heqcond in Heqres.
    - remember (common_part (Cst n0) (Cst n1)) as res'. symmetry in Heqres'.
      destruct res'; good_inversion Heqres. apply common_part_some in Heqres'.
      good_inversion Heqres'.
      assert (inf_subst_eq (wf_eqsys_to_subst s) (wf_eqsys_to_subst s')). {
        apply wf_eqsys_to_subst_ext_lookup. intro z. rewrite <- H0. simpl.
        destruct (name_eq_dec z x'); auto. subst z.
        assert (eqsys_walk_result (wf_eqsys_get s) x' (x', Cst n1)). {
          set (H' := Heqres1). rewrite wf_eqsys_walk_idemp in H'.
          rewrite Heqres1 in H'. simpl in H'. rewrite <- H'. apply wf_eqsys_walk_prop.
        }
        set (H' := H). good_inversion H'; auto. exfalso. eapply eqsys_walk_result_last; eauto.
      }
      simpl. intros. destruct H1 as [ [ H1 H2 ] H3 ]. constructor. constructor.
      + eapply inf_subst_more_general_eq; eauto. symmetry. auto. reflexivity.
      + destruct H1 as [ s1 H1 ]. unfold inf_unifier. etransitivity. apply H1. symmetry.
        etransitivity. apply H1. symmetry. repeat rewrite <- inf_subst_compose_spec.
        apply inf_subst_apply_eq.
        etransitivity. symmetry. apply H. symmetry. etransitivity. symmetry. apply H.
        rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
        repeat rewrite wf_eqsys_to_subst_image. simpl. rewrite Heqres1, Heqres2. reflexivity.
      + intros s1 H4. destruct H4. apply H3. constructor.
        eapply inf_subst_more_general_eq; eauto. reflexivity. apply inf_unifier_refl.
    - remember (common_part (Cst n0) (Con n1 ty1 ty2)) as res'. symmetry in Heqres'.
      destruct res'; good_inversion Heqres. apply common_part_some in Heqres'. inversion Heqres'.
    - remember (common_part (Con n0 tx1 tx2) (Cst n1)) as res'. symmetry in Heqres'.
      destruct res'; good_inversion Heqres. apply common_part_some in Heqres'. inversion Heqres'.
    - remember (common_part (Con n0 tx1 tx2) (Con n1 ty1 ty2)) as res'. symmetry in Heqres'.
      destruct res'; good_inversion Heqres. apply common_part_some in Heqres'. simpl.
      admit.
  * apply wf_eqsys_union_none in Heqres. unfold eqsys_union in Heqres.
    remember (wf_eqsys_walk s x) as res1. symmetry in Heqres1. destruct res1 as [ x' xt ].
    remember (wf_eqsys_walk s y) as res2. symmetry in Heqres2. destruct res2 as [ y' yt ].
    destruct (name_eq_dec x' y'). inversion Heqres.
    assert (common_part xt yt = None -> wf_eqsys_union_result_hlp s x y None). {
      clear Heqres. intro. apply common_part_none in H. simpl. intros. intro. apply H.
      destruct H0 as [ s1 H0 ].
      apply (is_common_part_inf_unifiable (inf_subst_compose s1 (wf_eqsys_to_subst s))).
      unfold inf_unifier. etransitivity. 2: etransitivity. 2: apply H1. symmetry.
      * etransitivity. apply H0. repeat rewrite <- inf_subst_compose_spec.
        apply inf_subst_apply_eq. fold (term_to_inf (Var x)).
        repeat rewrite wf_eqsys_to_subst_apply. simpl. rewrite wf_eqsys_image_walk.
        rewrite Heqres1. reflexivity.
      * etransitivity. apply H0. repeat rewrite <- inf_subst_compose_spec.
        apply inf_subst_apply_eq. fold (term_to_inf (Var y)).
        repeat rewrite wf_eqsys_to_subst_apply. simpl. rewrite wf_eqsys_image_walk.
        rewrite Heqres2. reflexivity.
    }
    destruct xt; destruct yt; good_inversion Heqres.
    - remember (common_part (Cst n0) (Cst n1)) as res.
      destruct res; good_inversion H1. apply H. auto.
    - remember (common_part (Cst n0) (Con n1 yt1 yt2)) as res.
      destruct res; good_inversion H1. apply H. auto.
    - remember (common_part (Con n0 xt1 xt2) (Cst n1)) as res.
      destruct res; good_inversion H1. apply H. auto.
    - remember (common_part (Con n0 xt1 xt2) (Con n1 yt1 yt2)) as res.
      destruct res; good_inversion H1. apply H. auto.
Admitted.
