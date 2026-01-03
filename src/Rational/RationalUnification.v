From Stdlib Require Import Wellfounded.Lexicographic_Product.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Unification.
Require Import RationalTerm.

Definition eqsys := list (name * term).

Definition eqsys_empty : eqsys := [].

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

Fixpoint fv_terms (ts : list term) : var_set :=
match ts with
| [] => var_set_empty
| t :: ts => var_set_union (fv_term t) (fv_terms ts)
end.

Lemma fv_terms_nodup ts : NoDup (fv_terms ts).
Proof. induction ts as [ | t ]. constructor. apply ListSet.set_union_nodup. apply fv_term_nodup. auto. Qed.

Lemma fv_terms_in x ts : In x (fv_terms ts) <-> Exists (fun t => In x (fv_term t)) ts.
Proof.
  induction ts as [ | t ]. constructor; intros; inversion H.
  constructor; intros.
  * simpl in H. apply ListSet.set_union_elim in H. destruct H. left. auto. right. apply IHts. auto.
  * good_inversion H. apply ListSet.set_union_intro1. auto.
    apply ListSet.set_union_intro2. apply IHts. auto.
Qed.

Definition eqsys_vars (s : eqsys) : var_set := var_set_union (eqsys_dom s) (fv_terms (eqsys_rhs s)).

Lemma eqsys_vars_nodup s : NoDup (eqsys_vars s).
Proof. apply ListSet.set_union_nodup. apply eqsys_dom_nodup. apply fv_terms_nodup. Qed.

Lemma eqsys_vars_in s x (H : In x (eqsys_vars s))
                  : in_eqsys_dom s x \/ exists t, In t (eqsys_rhs s) /\ In x (fv_term t).
Proof.
  apply ListSet.set_union_elim in H. destruct H.
  * left. apply eqsys_dom_spec. auto.
  * right. apply Exists_exists. apply fv_terms_in. auto.
Qed.

Lemma eqsys_vars_in_dom s x (H : in_eqsys_dom s x) : In x (eqsys_vars s).
Proof. apply ListSet.set_union_intro1. apply eqsys_dom_spec. auto. Qed.

Lemma eqsys_vars_in_rhs s t x (H1 : In t (eqsys_rhs s)) (H2 : In x (fv_term t)) : In x (eqsys_vars s).
Proof. apply ListSet.set_union_intro2. apply fv_terms_in. apply Exists_exists. eexists. constructor; eauto. Qed.

Definition is_eqsys_root (s : eqsys) (x : name) : bool :=
match eqsys_lookup s x with
| Some (Var y) => false
| _ => true
end.

Lemma is_eqsys_root_true s x : is_eqsys_root s x = true <-> forall y, eqsys_lookup s x <> Some (Var y).
Proof.
  unfold is_eqsys_root. destruct (eqsys_lookup s x) as [ [] | ].
  constructor; intros. inversion H. exfalso. eapply H. auto.
  all: constructor; intros; auto; intro; inversion H0.
Qed.

Lemma is_eqsys_root_false s x : is_eqsys_root s x = false <-> exists y, eqsys_lookup s x = Some (Var y).
Proof.
  unfold is_eqsys_root. destruct (eqsys_lookup s x) as [ [] | ].
  constructor; intros; auto. eexists. auto.
  all: constructor; intros; good_inversion H; inversion H0.
Qed.

Definition eqsys_roots (s : eqsys) (xs : var_set) : var_set := filter (is_eqsys_root s) xs.

Lemma eqsys_roots_nodup s xs (H : NoDup xs) : NoDup (eqsys_roots s xs).
Proof. apply NoDup_filter. auto. Qed.

Lemma eqsys_roots_in s xs x (H1 : In x xs) (H2 : is_eqsys_root s x = true) : In x (eqsys_roots s xs).
Proof. apply filter_In. constructor; auto. Qed.

Lemma eqsys_roots_in_root s xs x (H : In x (eqsys_roots s xs)) : is_eqsys_root s x = true.
Proof. apply filter_In in H. apply H. Qed.

Lemma eqsys_roots_in_xs s xs x (H : In x (eqsys_roots s xs)) : In x xs.
Proof. apply filter_In in H. apply H. Qed.

Polymorphic Lemma NoDup_length_ext [A] (xs : list A) ys (H1 : NoDup xs) (H2 : NoDup ys)
                                   (H3 : incl xs ys) (H4 : incl ys xs)
                                 : length xs = length ys.
Proof. apply PeanoNat.Nat.le_antisymm; apply NoDup_incl_length; auto. Qed.

Definition eqsys_roots_num (s : eqsys) (xs : var_set) : nat := var_set_size (eqsys_roots s xs).

Lemma eqsys_roots_num_extend_nonvar s xs x t (H1 : NoDup xs) (H2 : In x xs)
                                    (H3 : is_eqsys_root s x = true) (H4 : forall y, t <> Var y)
                               : eqsys_roots_num s xs = eqsys_roots_num ((x, t) :: s) xs.
Proof.
  apply NoDup_length_ext; try apply eqsys_roots_nodup; auto.
  * intros z ?. apply eqsys_roots_in. apply eqsys_roots_in_xs in H. auto.
    remember (name_eq_dec z x) as cond. symmetry in Heqcond. destruct cond.
    apply is_eqsys_root_true. intro y. simpl. rewrite Heqcond. intro. good_inversion H0. eapply H4. auto.
    unfold is_eqsys_root. simpl. rewrite Heqcond. apply eqsys_roots_in_root in H. auto.
  * intros z ?. apply eqsys_roots_in. apply eqsys_roots_in_xs in H. auto.
    apply eqsys_roots_in_root in H. unfold is_eqsys_root in H. simpl in H.
    destruct (name_eq_dec z x); auto. subst. auto.
Qed.

Lemma eqsys_roots_num_extend_var s xs x y (H1 : NoDup xs) (H2 : In x xs) (H3 : is_eqsys_root s x = true)
                               : eqsys_roots_num s xs = 1 + eqsys_roots_num ((x, Var y) :: s) xs.
Proof.
  refine (_ : _ = var_set_size (x :: eqsys_roots ((x, Var y) :: s) xs)). apply NoDup_length_ext.
  * apply eqsys_roots_nodup. auto.
  * constructor. intro. apply eqsys_roots_in_root in H. unfold is_eqsys_root in H. simpl in H.
    destruct (name_eq_dec x x). inversion H. contradiction. apply eqsys_roots_nodup. auto.
  * intros z ?. remember (name_eq_dec z x) as cond. destruct cond. left. auto.
    symmetry in Heqcond. right. apply eqsys_roots_in. eapply eqsys_roots_in_xs. eauto.
    unfold is_eqsys_root. simpl. rewrite Heqcond. eapply eqsys_roots_in_root. eauto.
  * intros z ?. destruct H; try subst z; apply eqsys_roots_in; auto.
    eapply eqsys_roots_in_xs. eauto. apply eqsys_roots_in_root in H. unfold is_eqsys_root in H.
    simpl in H. destruct (name_eq_dec z x). inversion H. auto.
Qed.

Fixpoint term_nonvar_size (t : term) : nat :=
match t with
| Var _ => 0
| Cst _ => 1
| Con _ l r => 1 + term_nonvar_size l + term_nonvar_size r
end.

Definition eqsys_rhs_nonvar_size (s : eqsys) (x : name) : nat :=
match eqsys_lookup s x with
| None => 0
| Some t => term_nonvar_size t
end.

Definition eqsys_nonvar_size_hlp (s : eqsys) (xs : var_set) : nat :=
  list_sum (map (eqsys_rhs_nonvar_size s) xs).

Definition eqsys_nonvar_size (s : eqsys) : nat := eqsys_nonvar_size_hlp s (eqsys_dom s).

Lemma eqsys_nonvar_size_extend x t s : eqsys_nonvar_size ((x, t) :: s) + eqsys_rhs_nonvar_size s x
                                     = eqsys_nonvar_size s + term_nonvar_size t.
Proof.
  destruct (in_dec name_eq_dec x (eqsys_dom s)).
  * transitivity (eqsys_nonvar_size_hlp ((x, t) :: s) (eqsys_dom s) + eqsys_rhs_nonvar_size s x). {
      f_equal. apply Permutation_list_sum. apply Permutation_map.
      apply NoDup_Permutation; try apply eqsys_dom_nodup. intro z. constructor; intro.
      * apply ListSet.set_add_elim in H. destruct H; subst; auto.
      * apply ListSet.set_add_intro1. auto.
    }
    transitivity (eqsys_nonvar_size_hlp ((x, t) :: s) (x :: var_set_remove x (eqsys_dom s)) + eqsys_rhs_nonvar_size s x). {
      f_equal. apply Permutation_list_sum. apply Permutation_map.
      apply NoDup_Permutation. apply eqsys_dom_nodup.
      * constructor.
        - intro. apply ListSet.set_remove_2 in H. contradiction. apply eqsys_dom_nodup.
        - apply ListSet.set_remove_nodup. apply eqsys_dom_nodup.
      * intro z. constructor; intro.
        - destruct (name_eq_dec x z). left. auto. right. apply ListSet.set_remove_3; auto.
        - destruct H. subst. auto. apply ListSet.set_remove_1 in H. auto.
    }
    transitivity (term_nonvar_size t + eqsys_nonvar_size_hlp ((x, t) :: s) (var_set_remove x (eqsys_dom s)) + eqsys_rhs_nonvar_size s x). {
      f_equal. unfold eqsys_nonvar_size_hlp. simpl. f_equal. unfold eqsys_rhs_nonvar_size.
      simpl. destruct (name_eq_dec x x). auto. contradiction.
    }
    transitivity (term_nonvar_size t + eqsys_nonvar_size_hlp s (var_set_remove x (eqsys_dom s)) + eqsys_rhs_nonvar_size s x). {
      f_equal. f_equal. unfold eqsys_nonvar_size_hlp. f_equal. apply map_ext_in. intros z ?.
      unfold eqsys_rhs_nonvar_size. simpl. destruct (name_eq_dec z x); auto.
      exfalso. apply ListSet.set_remove_2 in H. auto. apply eqsys_dom_nodup.
    }
    rewrite (PeanoNat.Nat.add_comm (eqsys_nonvar_size s)), <- PeanoNat.Nat.add_assoc. f_equal.
    transitivity (eqsys_nonvar_size_hlp s (x :: var_set_remove x (eqsys_dom s))). {
      rewrite PeanoNat.Nat.add_comm. auto.
    }
    apply Permutation_list_sum. apply Permutation_map.
    apply NoDup_Permutation. 2: apply eqsys_dom_nodup.
    - constructor.
      + intro. apply ListSet.set_remove_2 in H. auto. apply eqsys_dom_nodup.
      + apply ListSet.set_remove_nodup. apply eqsys_dom_nodup.
    - intro z. constructor; intro.
      + destruct H. subst. auto. apply ListSet.set_remove_1 in H. auto.
      + destruct (name_eq_dec x z). left. auto. right. apply ListSet.set_remove_3; auto.
  * transitivity (eqsys_nonvar_size ((x, t) :: s)). {
      unfold eqsys_rhs_nonvar_size. replace (eqsys_lookup s x) with (@None term). auto.
      symmetry. apply in_eqsys_dom_inv. intro. apply eqsys_dom_spec in H. auto.
    }
    transitivity (eqsys_nonvar_size_hlp ((x, t) :: s) (x :: eqsys_dom s)). {
      apply Permutation_list_sum. apply Permutation_map.
      apply NoDup_Permutation. apply eqsys_dom_nodup.
      * constructor. auto. apply eqsys_dom_nodup.
      * intro z. constructor; intros.
        - apply ListSet.set_add_elim in H. destruct H. left. auto. right. auto.
        - destruct H. apply ListSet.set_add_intro2. auto. apply ListSet.set_add_intro1. auto.
    }
    transitivity (term_nonvar_size t + eqsys_nonvar_size_hlp ((x, t) :: s) (eqsys_dom s)). {
      unfold eqsys_nonvar_size_hlp. simpl. f_equal. unfold eqsys_rhs_nonvar_size. simpl.
      destruct (name_eq_dec x x). auto. contradiction.
    }
    rewrite PeanoNat.Nat.add_comm. f_equal. unfold eqsys_nonvar_size, eqsys_nonvar_size_hlp.
    f_equal. apply map_ext_in. intros z ?. unfold eqsys_rhs_nonvar_size. simpl.
    destruct (name_eq_dec z x). subst. contradiction. auto.
Qed.

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

Lemma eqsys_walk_result_last_nonvar s x y t (H1 : eqsys_walk_result s x (y, t)) (H2 : t <> Var y)
                                  : eqsys_lookup s y = Some t.
Proof.
  remember (y, t) as r. revert y t H2 Heqr. induction H1; intros; good_inversion Heqr; eauto.
  contradiction.
Qed.

Lemma eqsys_walk_result_var_dom s x y z (H : eqsys_walk_result s x (y, Var z)) : ~in_eqsys_dom s z.
Proof.
  remember (y, Var z) as r. revert y z Heqr.
  induction H; intros; good_inversion Heqr.
  * apply in_eqsys_dom_inv. auto.
  * eapply IHeqsys_walk_result. reflexivity.
Qed.

Lemma eqsys_walk_result_var_dom_inv s x y t (H1 : eqsys_walk_result s x (y, t)) (H2 : t <> Var y)
                                  : in_eqsys_dom s y.
Proof. apply eqsys_walk_result_last_nonvar in H1; auto. eexists. eauto. Qed.

Lemma eqsys_walk_result_last s x y z t (H : eqsys_walk_result s x (y, t))
                           : eqsys_lookup s y <> Some (Var z).
Proof.
  remember (y, t) as r. revert y t Heqr. induction H; intros; good_inversion Heqr; try rewrite H.
  all: try (intro; inversion H0; fail). eapply IHeqsys_walk_result. auto.
Qed.

Lemma eqsys_walk_result_in_vars s x y t (H : eqsys_walk_result s x (y, t))
                              : In y (eqsys_vars s) \/ x = y.
Proof.
  remember (y, t) as r. revert y t Heqr. induction H; intros; good_inversion Heqr; auto.
  edestruct IHeqsys_walk_result; auto. subst y0. left. eapply eqsys_vars_in_rhs.
  apply eqsys_rhs_in. exists x. eauto. simpl. auto.
Qed.

Lemma eqsys_walk_result_root s x y t (H : eqsys_walk_result s x (y, t))
                           : is_eqsys_root s y = true.
Proof. apply is_eqsys_root_true. intro. eapply eqsys_walk_result_last. eauto. Qed.

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

Lemma wf_eqsys_extend_well_formed s x t (H : eqsys_walkable ((x, t) :: wf_eqsys_get s) x)
                                : eqsys_well_formed ((x, t) :: wf_eqsys_get s).
Proof. apply eqsys_well_formed_extend; auto. apply wf_eqsys_get_well_formed. Qed.

Fact eqsys_empty_well_formed : eqsys_well_formed eqsys_empty.
Proof. intro. exists (x, Var x). constructor. auto. Qed.

Definition wf_eqsys_empty : wf_eqsys := exist _ _ eqsys_empty_well_formed.

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

Lemma wf_eqsys_walk_last_nonvar s x y t (H1 : wf_eqsys_walk s x = (y, t)) (H2 : t <> Var y)
                              : eqsys_lookup (wf_eqsys_get s) y = Some t.
Proof. eapply eqsys_walk_result_last_nonvar; auto. rewrite <- H1. apply wf_eqsys_walk_prop. Qed.

Lemma wf_eqsys_walk_var_dom s x y z (H : wf_eqsys_walk s x = (y, Var z))
                          : ~in_eqsys_dom (wf_eqsys_get s) z.
Proof. eapply eqsys_walk_result_var_dom. rewrite <- H. apply wf_eqsys_walk_prop. Qed.

Lemma wf_eqsys_walk_var_dom_inv s x y t (H1 : wf_eqsys_walk s x = (y, t)) (H2 : t <> Var y)
                              : in_eqsys_dom (wf_eqsys_get s) y.
Proof. eapply eqsys_walk_result_var_dom_inv; eauto. rewrite <- H1. apply wf_eqsys_walk_prop. Qed.

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

Lemma wf_eqsys_walk_rhs s x : in_eqsys_rhs (wf_eqsys_get s) (snd (wf_eqsys_walk s x))
                           \/ exists y, wf_eqsys_walk s x = (y, Var y).
Proof.
  specialize (wf_eqsys_walk_prop s x). intro H. remember (wf_eqsys_walk s x) as r.
  induction H; simpl.
  * right. eexists. auto.
  * apply IHeqsys_walk_result. symmetry. eapply wf_eqsys_walk_ext. eauto.
  * left. eexists. eauto.
  * left. eexists. eauto.
Qed.

Lemma wf_eqsys_walk_root s x y t (H : wf_eqsys_walk s x = (y, t))
                       : is_eqsys_root (wf_eqsys_get s) y = true.
Proof. eapply eqsys_walk_result_root. rewrite <- H. apply wf_eqsys_walk_prop. Qed.

Lemma wf_eqsys_walk_in_vars s x y t (H : wf_eqsys_walk s x = (y, t))
                       : In y (eqsys_vars (wf_eqsys_get s)) \/ x = y.
Proof. eapply eqsys_walk_result_in_vars. rewrite <- H. apply wf_eqsys_walk_prop. Qed.

Lemma wf_eqsys_walk_extend s1 s2 x y t (H2 : wf_eqsys_get s2 = (x, t) :: wf_eqsys_get s1)
                         : wf_eqsys_walk s1 y = wf_eqsys_walk s2 y
                        \/ wf_eqsys_walk s1 y = wf_eqsys_walk s1 x
                        /\ wf_eqsys_walk s2 y = wf_eqsys_walk s2 x.
Proof.
  assert (exists p, eqsys_walk_path (wf_eqsys_get s1) y p). {
    apply eqsys_walkable_path. eexists. apply wf_eqsys_walk_prop.
  }
  destruct H as [ p H ]. destruct (in_dec name_eq_dec x p).
  * right. apply (in_split_dec _ (name_eq_dec x)) in i.
    destruct i as [ p1 [ p2 [ H' i ] ] ]. subst. constructor.
    - apply wf_eqsys_walk_ext. eapply eqsys_walk_path_transport; eauto. apply wf_eqsys_walk_prop.
    - assert (exists q, eqsys_walk_path (wf_eqsys_get s2) x q). {
        apply eqsys_walkable_path. eexists. apply wf_eqsys_walk_prop.
      }
      destruct H0 as [ q H0 ]. apply wf_eqsys_walk_ext.
      eapply eqsys_walk_path_extend_concat in H; eauto.
      2: rewrite <- H2; eauto. rewrite <- H2 in H. destruct q. inversion H0.
      replace n with x in * by (good_inversion H0; auto). clear n.
      eapply eqsys_walk_path_transport; eauto. apply wf_eqsys_walk_prop.
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
  remember (wf_eqsys_walk s x) as r. symmetry in Heqr. destruct r as [ y t ].
  rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl. rewrite Heqr.
  destruct t; try reflexivity.
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
      apply eqsys_rhs_in in H1. rewrite <- Heqres in H1. auto. eapply in_incl_trans. eauto.
      apply term_subterms_incl. simpl. right. apply in_or_app. left. apply term_subterms_self.
    - edestruct IHinf_path_to as [ r [ IH1 IH2 ] ]. reflexivity. exists r. constructor. auto.
      destruct IH2; auto. left. simpl. right. apply in_or_app. auto.
  * destruct t'; rewrite inf_term_step_prop in Heqt'; good_inversion Heqt'.
    - remember (wf_eqsys_walk s n) as res. destruct res as [ y t' ].
      destruct t'; good_inversion H1. edestruct IHinf_path_to as [ r [ IH1 IH2 ] ]. reflexivity.
      exists r. constructor. auto. destruct IH2; auto. right. apply eqsys_rhs_subterms.
      exists (Con n0 t'1 t'2). constructor. specialize (wf_eqsys_walk_rhs s n). intro.
      destruct H1. 2: { destruct H1 as [ n' H1 ]. rewrite H1 in Heqres. inversion Heqres. }
      apply eqsys_rhs_in in H1. rewrite <- Heqres in H1. auto. eapply in_incl_trans. eauto.
      apply term_subterms_incl. simpl. right. apply in_or_app. right. apply term_subterms_self.
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
  induction t; rewrite inf_term_step_prop at 1; simpl; f_equal; auto.
  symmetry. apply inf_term_step_prop.
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

Fact wf_eqsys_to_subst_empty : wf_eqsys_to_subst wf_eqsys_empty = inf_subst_empty.
Proof. auto. Qed.

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
    - rewrite inf_term_step_prop. simpl. erewrite (wf_eqsys_walk_ext _ _ (x, Var x)). auto.
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
  : inf_subst_apply (wf_eqsys_to_subst s) (term_to_inf t) = wf_eqsys_apply s t.
Proof.
  symmetry. induction t. 2, 3: rewrite inf_term_step_prop; simpl; f_equal; auto.
  simpl. rewrite inf_subst_apply_var, wf_eqsys_to_subst_image. auto.
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
      exists (snd (wf_eqsys_walk s x)). constructor. apply eqsys_rhs_in. auto. apply Exists_exists.
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
  rewrite <- wf_eqsys_to_subst_apply. apply inf_subst_apply_rational.
  apply wf_eqsys_to_subst_rational. apply term_to_inf_rational.
Qed.

Lemma wf_eqsys_to_subst_extend_unbound s1 s2 x t (H1 : ~in_eqsys_dom (wf_eqsys_get s1) x)
                                       (H2 : wf_eqsys_get s2 = (x, t) :: wf_eqsys_get s1)
  : inf_subst_eq (wf_eqsys_to_subst s2)
                 (inf_subst_compose (inf_subst_singleton x (wf_eqsys_image s2 x))
                                    (wf_eqsys_to_subst s1)).
Proof.
  assert (H3 : wf_eqsys_walk s1 x = (x, Var x)). {
    apply wf_eqsys_walk_ext. apply ESWalkVar. apply in_eqsys_dom_inv. auto.
  }
  apply inf_subst_eq_ext. intro y. rewrite inf_subst_compose_image.
  repeat rewrite wf_eqsys_to_subst_image. unfold wf_eqsys_image.
  generalize (Var y). clear y. intros t' p l' Hp.
  remember (wf_eqsys_image_hlp s2 t') as l. revert t' Heql. induction Hp; intros.
  * subst. eexists. constructor. constructor. destruct t'; simpl; auto.
    edestruct wf_eqsys_walk_extend; eauto.
    - rewrite <- H. destruct (wf_eqsys_walk s1 n). destruct t0; auto.
      destruct (name_eq_dec n1 x); auto. subst. symmetry in H.
      set (H' := H). apply wf_eqsys_walk_var in H'. subst.
      set (H' := H). rewrite wf_eqsys_walk_idemp in H'. rewrite H in H'. simpl in H'.
      simpl. rewrite H'. auto.
    - destruct H. rewrite H, H0, H3. destruct (name_eq_dec x x); try contradiction. simpl.
      destruct (wf_eqsys_walk s2 x) as [ ? [] ]; auto.
  * rewrite inf_term_step_prop in Heql; destruct t'; good_inversion Heql.
    - remember (wf_eqsys_walk s2 n) as res. destruct res. destruct t1; good_inversion H0.
      edestruct wf_eqsys_walk_extend; eauto.
      + edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto.
        exists r'. constructor; auto. rewrite inf_term_step_prop at 1. simpl.
        rewrite H, <- Heqres. constructor. auto.
      + destruct H. exists t0. constructor; try reflexivity.
        rewrite inf_term_step_prop at 1. simpl. rewrite H, H3.
        destruct (name_eq_dec x x); try contradiction. simpl.
        rewrite <- H0, <- Heqres. constructor. auto.
    - edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. constructor. auto.
  * rewrite inf_term_step_prop in Heql; destruct t'; good_inversion Heql.
    - remember (wf_eqsys_walk s2 n) as res. destruct res. destruct t1; good_inversion H0.
      edestruct wf_eqsys_walk_extend; eauto.
      + edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto.
        exists r'. constructor; auto. rewrite inf_term_step_prop at 1. simpl.
        rewrite H, <- Heqres. constructor. auto.
      + destruct H. exists t0. constructor; try reflexivity.
        rewrite inf_term_step_prop at 1. simpl. rewrite H, H3.
        destruct (name_eq_dec x x); try contradiction. simpl.
        rewrite <- H0, <- Heqres. constructor. auto.
    - edestruct IHHp as [ r' [ IH1 IH2 ] ]. auto. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. simpl. constructor. auto.
Qed.

Lemma wf_eqsys_to_subst_extend_inv_unifier s1 s2 s x t
  (H1 : wf_eqsys_get s2 = (x, t) :: wf_eqsys_get s1)
  (H2 : inf_unifier (wf_eqsys_image s1 x) (wf_eqsys_apply s1 t) s)
: inf_subst_eq (inf_subst_compose s (wf_eqsys_to_subst s1)) (inf_subst_compose s (wf_eqsys_to_subst s2)).
Proof.
  assert (Ht : t <> Var x). {
    assert (eqsys_walkable (wf_eqsys_get s2) x). apply wf_eqsys_get_well_formed.
    clear s H2. intro. subst. destruct H as [ res ]. induction H; rewrite H1 in H; simpl in H.
    all: destruct (name_eq_dec x x); try contradiction; inversion H. subst. auto.
  }
  assert (H3 : forall y, t = Var y -> wf_eqsys_walk s1 y = wf_eqsys_walk s2 y). {
    intros. subst. apply wf_eqsys_walk_ext.
    assert (exists p, eqsys_walk_path (wf_eqsys_get s2) y p).
    apply eqsys_walkable_path. apply wf_eqsys_get_well_formed.
    destruct H as [ p ]. eapply eqsys_walk_result_ext; eauto. apply wf_eqsys_walk_prop.
    intros z ?. rewrite H1. simpl. destruct (name_eq_dec z x); auto. subst z.
    eapply ESWalkPathWalk in H. apply eqsys_walk_path_nodup in H. good_inversion H.
    exfalso. eauto. rewrite H1. simpl. destruct (name_eq_dec x x). auto. contradiction.
  }
  apply inf_subst_eq_ext. intro z. repeat rewrite inf_subst_compose_image, wf_eqsys_to_subst_image.
  fold (wf_eqsys_apply s1 (Var z)). fold (wf_eqsys_apply s2 (Var z)). generalize (Var z). clear z.
  intro l. symmetry. apply inf_unifier_sym in H2. intros p l' Hp.
  remember (inf_subst_apply s (wf_eqsys_apply s2 l)) as t'.
  assert (H5 : inf_term_eq t' (inf_subst_apply s (wf_eqsys_apply s2 l))).
  rewrite Heqt'. reflexivity. clear Heqt'. revert l H5. induction Hp; intros.
  * edestruct (H5 Here) as [ ? [] ]. constructor. good_inversion H. clear H5.
    destruct l; eexists; constructor; try constructor; rewrite H0; try reflexivity.
    clear t0 H0. simpl wf_eqsys_apply. edestruct wf_eqsys_walk_extend as [ | [] ]; eauto.
    - simpl. rewrite H. destruct (wf_eqsys_walk s2 n) as [ ? [] ]; auto.
      apply inf_term_eq_node_refl.
    - edestruct (H2 Here) as [ ? [] ]. constructor. good_inversion H4.
      etransitivity. etransitivity. 2: apply H5. 2: simpl; rewrite H; apply inf_term_eq_node_refl.
      apply inf_subst_apply_eq_node. transitivity (wf_eqsys_image s2 x). simpl. rewrite H0.
      apply inf_term_eq_node_refl. edestruct wf_eqsys_walk_extend_new; eauto.
      + simpl. rewrite H4. destruct t; simpl; auto.
        set (H' := H4). apply wf_eqsys_walk_var in H'. subst n0.
        apply wf_eqsys_walk_var_dom in H4. contradiction.
      + destruct H4 as [ y ]. subst. simpl. erewrite wf_eqsys_walk_ext. 2: {
          eapply ESWalkWalk. rewrite H1. simpl. destruct (name_eq_dec x x). auto. contradiction.
          apply wf_eqsys_walk_prop.
        }
        rewrite H3; auto. destruct (wf_eqsys_walk s2 y) as [ ? [] ]; auto.
  * edestruct (H5 Here) as [ ? [] ]. constructor. good_inversion H.
    destruct l0; try good_inversion H0. 2: {
      rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conl in H5.
      apply IHHp in H5. clear IHHp. destruct H5 as [ r' [] ]. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. constructor. auto.
    }
    simpl wf_eqsys_apply in H0, H5. remember (wf_eqsys_image s2 n) as t'. symmetry in Heqt'.
    rewrite inf_term_step_prop in Heqt' at 1. simpl in Heqt'.
    edestruct wf_eqsys_walk_extend as [ | [] ]; eauto.
    - remember (wf_eqsys_walk s2 n) as res. symmetry in Heqres.
      destruct res as [ n' [] ]; good_inversion Heqt'; try good_inversion H0.
      + clear H0. edestruct (H5 (Left p)) as [ r' [] ]. constructor. eauto.
        exists r'. constructor; auto. simpl.
        rewrite (inf_term_step_prop (wf_eqsys_image s1 n)). simpl. rewrite H, Heqres. auto.
      + rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conl in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r' [] ]. exists r'. constructor; auto.
        rewrite inf_term_step_prop at 1. simpl. rewrite H, Heqres. constructor.
        rewrite wf_eqsys_image_hlp_apply. auto.
    - rewrite H4 in Heqt'. edestruct wf_eqsys_walk_extend_new; eauto.
      + rewrite H6 in Heqt'. destruct t; good_inversion Heqt'; try good_inversion H0. {
          apply wf_eqsys_walk_var in H6. subst n0. contradiction.
        }
        rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conl in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r1 [] ]. edestruct (H2 (Left p)) as [ r2 [] ].
        rewrite inf_term_step_prop at 1. constructor. eauto.
        exists r2. constructor. 2: etransitivity; eauto. simpl.
        replace (wf_eqsys_image s1 n) with (wf_eqsys_image s1 x). auto.
        rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl. rewrite H. reflexivity.
      + destruct H6 as [ y ]. subst t.
        assert (wf_eqsys_walk s2 x = wf_eqsys_walk s2 y). {
          apply wf_eqsys_walk_ext. eapply ESWalkWalk. rewrite H1. simpl.
          destruct (name_eq_dec x x). auto. contradiction. apply wf_eqsys_walk_prop.
        }
        rewrite H6 in Heqt'. remember (wf_eqsys_walk s2 y) as res. symmetry in Heqres.
        destruct res as [ y' [] ]; good_inversion Heqt'; try good_inversion H0. {
          clear H0. apply wf_eqsys_walk_var in H6. subst n0.
          edestruct (H5 (Left p)) as [ r1 [] ]. constructor. eauto.
          edestruct (H2 (Left p)) as [ r2 [] ]. simpl.
          rewrite (inf_term_step_prop (wf_eqsys_image s1 y)). simpl.
          rewrite H3, Heqres; auto. eauto. exists r2. constructor. 2: etransitivity; eauto.
          simpl. replace (wf_eqsys_image s1 n) with (wf_eqsys_image s1 x). auto.
          rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
          rewrite H. reflexivity.
        }
        rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conl in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r1 [] ]. edestruct (H2 (Left p)) as [ r2 [] ]. simpl.
        rewrite inf_term_step_prop at 1. simpl. rewrite H3, Heqres; auto. constructor.
        rewrite wf_eqsys_image_hlp_apply. eauto. exists r2. constructor. 2: etransitivity; eauto.
        simpl. replace (wf_eqsys_image s1 n) with (wf_eqsys_image s1 x). auto.
        rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl. rewrite H. reflexivity.
  * edestruct (H5 Here) as [ ? [] ]. constructor. good_inversion H.
    destruct l0; try good_inversion H0. 2: {
      rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conr in H5.
      apply IHHp in H5. clear IHHp. destruct H5 as [ r' [] ]. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. constructor. auto.
    }
    simpl wf_eqsys_apply in H0, H5. remember (wf_eqsys_image s2 n) as t'. symmetry in Heqt'.
    rewrite inf_term_step_prop in Heqt' at 1. simpl in Heqt'.
    edestruct wf_eqsys_walk_extend as [ | [] ]; eauto.
    - remember (wf_eqsys_walk s2 n) as res. symmetry in Heqres.
      destruct res as [ n' [] ]; good_inversion Heqt'; try good_inversion H0.
      + clear H0. edestruct (H5 (Right p)) as [ r' [] ]. constructor. eauto.
        exists r'. constructor; auto. simpl.
        rewrite (inf_term_step_prop (wf_eqsys_image s1 n)). simpl. rewrite H, Heqres. auto.
      + rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conr in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r' [] ]. exists r'. constructor; auto.
        rewrite inf_term_step_prop at 1. simpl. rewrite H, Heqres. constructor.
        rewrite wf_eqsys_image_hlp_apply. auto.
    - rewrite H4 in Heqt'. edestruct wf_eqsys_walk_extend_new; eauto.
      + rewrite H6 in Heqt'. destruct t; good_inversion Heqt'; try good_inversion H0. {
          apply wf_eqsys_walk_var in H6. subst n0. contradiction.
        }
        rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conr in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r1 [] ]. edestruct (H2 (Right p)) as [ r2 [] ].
        rewrite inf_term_step_prop at 1. constructor. eauto.
        exists r2. constructor. 2: etransitivity; eauto. simpl.
        replace (wf_eqsys_image s1 n) with (wf_eqsys_image s1 x). auto.
        rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl. rewrite H. reflexivity.
      + destruct H6 as [ y ]. subst t.
        assert (wf_eqsys_walk s2 x = wf_eqsys_walk s2 y). {
          apply wf_eqsys_walk_ext. eapply ESWalkWalk. rewrite H1. simpl.
          destruct (name_eq_dec x x). auto. contradiction. apply wf_eqsys_walk_prop.
        }
        rewrite H6 in Heqt'. remember (wf_eqsys_walk s2 y) as res. symmetry in Heqres.
        destruct res as [ y' [] ]; good_inversion Heqt'; try good_inversion H0. {
          clear H0. apply wf_eqsys_walk_var in H6. subst n0.
          edestruct (H5 (Right p)) as [ r1 [] ]. constructor. eauto.
          edestruct (H2 (Right p)) as [ r2 [] ]. simpl.
          rewrite (inf_term_step_prop (wf_eqsys_image s1 y)). simpl.
          rewrite H3, Heqres; auto. eauto. exists r2. constructor. 2: etransitivity; eauto.
          simpl. replace (wf_eqsys_image s1 n) with (wf_eqsys_image s1 x). auto.
          rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
          rewrite H. reflexivity.
        }
        rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conr in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r1 [] ]. edestruct (H2 (Right p)) as [ r2 [] ]. simpl.
        rewrite inf_term_step_prop at 1. simpl. rewrite H3, Heqres; auto. constructor.
        rewrite wf_eqsys_image_hlp_apply. eauto. exists r2. constructor. 2: etransitivity; eauto.
        simpl. replace (wf_eqsys_image s1 n) with (wf_eqsys_image s1 x). auto.
        rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl. rewrite H. reflexivity.
Qed.

Lemma wf_eqsys_to_subst_extend_bound_unifier s1 s2 s x t
  (H1 : in_eqsys_dom (wf_eqsys_get s1) x) (H2 : wf_eqsys_get s2 = (x, t) :: wf_eqsys_get s1)
  (H3 : inf_unifier (wf_eqsys_apply s2 (snd (wf_eqsys_walk s1 x))) (wf_eqsys_apply s2 t) s)
: inf_subst_eq (inf_subst_compose s (wf_eqsys_to_subst s1)) (inf_subst_compose s (wf_eqsys_to_subst s2)).
Proof.
  assert (H4 : forall x', wf_eqsys_walk s1 x = (x', Var x') -> wf_eqsys_walk s2 x' = (x', Var x')). {
    intros. set (H4 := H). apply wf_eqsys_walk_var_dom, in_eqsys_dom_inv, ESWalkVar in H4.
    set (H5 := H4). apply eqsys_walk_path_result_fst in H5. apply wf_eqsys_walk_ext.
    eapply eqsys_walk_result_ext; eauto. intros. destruct H0; good_inversion H0.
    rewrite H2. simpl. destruct (name_eq_dec y x); auto. subst y.
    apply wf_eqsys_walk_var_dom in H. contradiction.
  }
  apply inf_subst_eq_ext. intro z. repeat rewrite inf_subst_compose_image, wf_eqsys_to_subst_image.
  fold (wf_eqsys_apply s1 (Var z)). fold (wf_eqsys_apply s2 (Var z)). generalize (Var z). clear z.
  intros l p l' Hp. remember (inf_subst_apply s (wf_eqsys_apply s1 l)) as t'.
  assert (H5 : inf_term_eq t' (inf_subst_apply s (wf_eqsys_apply s1 l))).
  rewrite Heqt'. reflexivity. clear Heqt'. revert l H5. induction Hp; intros.
  * edestruct (H5 Here) as [ ? [] ]. constructor. good_inversion H. clear H5.
    destruct l; eexists; constructor; try constructor; rewrite H0; try reflexivity.
    clear t0 H0. simpl wf_eqsys_apply. edestruct wf_eqsys_walk_extend as [ | [] ]; eauto.
    - simpl. rewrite H. destruct (wf_eqsys_walk s2 n) as [ ? [] ]; auto.
      apply inf_term_eq_node_refl.
    - edestruct wf_eqsys_image_walk as [ ? [] ]. constructor. good_inversion H5.
      etransitivity. apply inf_subst_apply_eq_node. apply H6. clear H6. rewrite H.
      symmetry. edestruct wf_eqsys_image_walk as [ ? [] ]. constructor. good_inversion H5.
      etransitivity. apply inf_subst_apply_eq_node. apply H6. clear H6. rewrite H0.
      clear n H H0. symmetry. etransitivity. 2: etransitivity. 2: {
        edestruct (H3 Here) as [ ? [] ]. constructor. good_inversion H. apply H0.
      }
      all: apply inf_subst_apply_eq_node.
      + remember (wf_eqsys_walk s1 x) as res. symmetry in Heqres.
        destruct res as [ x' [] ]; try reflexivity.
        set (H' := Heqres). apply wf_eqsys_walk_var in H'. subst n.
        set (H5 := Heqres). rewrite wf_eqsys_walk_idemp in H5. rewrite Heqres in H5. simpl in H5.
        simpl. rewrite H4, H5; auto.
      + symmetry. edestruct wf_eqsys_walk_extend_new; eauto. rewrite H. reflexivity.
        destruct H as [ y ]. subst. erewrite wf_eqsys_walk_ext. 2: {
          eapply ESWalkWalk. rewrite H2. simpl. destruct (name_eq_dec x x). auto. contradiction.
          apply wf_eqsys_walk_prop.
        }
        symmetry. edestruct wf_eqsys_image_walk as [ ? [] ]. constructor. good_inversion H. apply H0.
  * edestruct (H5 Here) as [ ? [] ]. constructor. good_inversion H.
    destruct l0; try good_inversion H0. 2: {
      rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conl in H5.
      apply IHHp in H5. clear IHHp. destruct H5 as [ r' [] ]. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. constructor. auto.
    }
    simpl wf_eqsys_apply in H0, H5. remember (wf_eqsys_image s1 n) as t'. symmetry in Heqt'.
    rewrite inf_term_step_prop in Heqt' at 1. simpl in Heqt'.
    edestruct wf_eqsys_walk_extend as [ | [] ]; eauto; rewrite H in Heqt'.
    - remember (wf_eqsys_walk s2 n) as res. symmetry in Heqres.
      destruct res as [ n' [] ]; good_inversion Heqt'; try good_inversion H0.
      + clear H0. edestruct (H5 (Left p)) as [ r' [] ]. constructor. eauto.
        exists r'. constructor; auto. simpl.
        rewrite (inf_term_step_prop (wf_eqsys_image s2 n)). simpl. rewrite Heqres. auto.
      + rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conl in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r' [] ]. exists r'. constructor; auto.
        rewrite inf_term_step_prop at 1. simpl. rewrite Heqres. constructor.
        rewrite wf_eqsys_image_hlp_apply. auto.
    - assert (inf_term_eq (wf_eqsys_apply s2 t) (wf_eqsys_image s2 n)). {
        rewrite wf_eqsys_image_walk. rewrite H6.
        edestruct wf_eqsys_walk_extend_new; eauto. rewrite H7. reflexivity.
        destruct H7 as [ y ]. subst. simpl. rewrite wf_eqsys_image_walk.
        erewrite (wf_eqsys_walk_ext s2 x). reflexivity. eapply ESWalkWalk.
        rewrite H2. simpl. destruct (name_eq_dec x x). auto. contradiction.
        apply wf_eqsys_walk_prop.
      }
      eapply inf_subst_apply_eq in H7. unfold inf_unifier in H3. rewrite H7 in H3. clear H7.
      remember (wf_eqsys_walk s1 x) as res. symmetry in Heqres.
      destruct res as [ x' [] ]; good_inversion Heqt'; try good_inversion H0.
      + clear H0. edestruct (H5 (Left p)) as [ r1 [] ]. constructor. eauto.
        set (H' := H). apply wf_eqsys_walk_var in H'. subst n0.
        edestruct (H3 (Left p)) as [ r2 [] ]. simpl.
        rewrite (inf_term_step_prop (wf_eqsys_image s2 x')). simpl. rewrite H4; eauto.
        exists r2. constructor. auto. etransitivity; eauto.
      + rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conl in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r1 [] ]. edestruct (H3 (Left p)) as [ r2 [] ].
        rewrite inf_term_step_prop at 1. simpl. constructor. eauto.
        exists r2. constructor. auto. etransitivity; eauto.
  * edestruct (H5 Here) as [ ? [] ]. constructor. good_inversion H.
    destruct l0; try good_inversion H0. 2: {
      rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conr in H5.
      apply IHHp in H5. clear IHHp. destruct H5 as [ r' [] ]. exists r'. constructor; auto.
      rewrite inf_term_step_prop at 1. constructor. auto.
    }
    simpl wf_eqsys_apply in H0, H5. remember (wf_eqsys_image s1 n) as t'. symmetry in Heqt'.
    rewrite inf_term_step_prop in Heqt' at 1. simpl in Heqt'.
    edestruct wf_eqsys_walk_extend as [ | [] ]; eauto; rewrite H in Heqt'.
    - remember (wf_eqsys_walk s2 n) as res. symmetry in Heqres.
      destruct res as [ n' [] ]; good_inversion Heqt'; try good_inversion H0.
      + clear H0. edestruct (H5 (Right p)) as [ r' [] ]. constructor. eauto.
        exists r'. constructor; auto. simpl.
        rewrite (inf_term_step_prop (wf_eqsys_image s2 n)). simpl. rewrite Heqres. auto.
      + rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conr in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r' [] ]. exists r'. constructor; auto.
        rewrite inf_term_step_prop at 1. simpl. rewrite Heqres. constructor.
        rewrite wf_eqsys_image_hlp_apply. auto.
    - assert (inf_term_eq (wf_eqsys_apply s2 t) (wf_eqsys_image s2 n)). {
        rewrite wf_eqsys_image_walk. rewrite H6.
        edestruct wf_eqsys_walk_extend_new; eauto. rewrite H7. reflexivity.
        destruct H7 as [ y ]. subst. simpl. rewrite wf_eqsys_image_walk.
        erewrite (wf_eqsys_walk_ext s2 x). reflexivity. eapply ESWalkWalk.
        rewrite H2. simpl. destruct (name_eq_dec x x). auto. contradiction.
        apply wf_eqsys_walk_prop.
      }
      eapply inf_subst_apply_eq in H7. unfold inf_unifier in H3. rewrite H7 in H3. clear H7.
      remember (wf_eqsys_walk s1 x) as res. symmetry in Heqres.
      destruct res as [ x' [] ]; good_inversion Heqt'; try good_inversion H0.
      + clear H0. edestruct (H5 (Right p)) as [ r1 [] ]. constructor. eauto.
        set (H' := H). apply wf_eqsys_walk_var in H'. subst n0.
        edestruct (H3 (Right p)) as [ r2 [] ]. simpl.
        rewrite (inf_term_step_prop (wf_eqsys_image s2 x')). simpl. rewrite H4; eauto.
        exists r2. constructor. auto. etransitivity; eauto.
      + rewrite inf_term_step_prop in H5. simpl in H5. apply inf_term_eq_conr in H5.
        rewrite wf_eqsys_image_hlp_apply in H5. apply IHHp in H5. clear IHHp.
        destruct H5 as [ r1 [] ]. edestruct (H3 (Right p)) as [ r2 [] ].
        rewrite inf_term_step_prop at 1. simpl. constructor. eauto.
        exists r2. constructor. auto. etransitivity; eauto.
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

Lemma is_common_part_refl t : is_common_part t t t.
Proof. induction t; constructor; auto. Qed.

Lemma is_common_part_sym t1 t2 t (H : is_common_part t1 t2 t) : is_common_part t2 t1 t.
Proof. induction H; constructor; auto. Qed.

Lemma is_common_part_vars t1 t2 t x (H1 : is_common_part t1 t2 t) (H2 : In x (fv_term t))
                        : In x (fv_term t1) \/ (In x (fv_term t2)).
Proof.
  induction H1; auto. simpl in H2. apply ListSet.set_union_elim in H2. destruct H2.
  * apply IHis_common_part1 in H. destruct H; [ left | right ]; apply ListSet.set_union_intro1; auto.
  * apply IHis_common_part2 in H. destruct H; [ left | right ]; apply ListSet.set_union_intro2; auto.
Qed.

Lemma is_common_part_nonvar_size t1 t2 t (H1 : is_common_part t1 t2 t)
                               : term_nonvar_size t <= term_nonvar_size t1.
Proof. induction H1; simpl; try lia. Qed.

Lemma is_common_part_same_nonvar_size_con l1 l2 l r1 r2 r
                                          (H1 : is_common_part l1 l2 l) (H2 : is_common_part r1 r2 r)
                                          (H3 : term_nonvar_size l1 + term_nonvar_size r1
                                              = term_nonvar_size l + term_nonvar_size r)
                                        : term_nonvar_size l1 = term_nonvar_size l
                                       /\ term_nonvar_size r1 = term_nonvar_size r.
Proof.
  revert r1 r2 r H2 H3. induction H1; simpl; intros.
  * constructor; auto.
  * destruct (PeanoNat.Nat.eq_dec (term_nonvar_size t) 0). constructor; lia.
    absurd (term_nonvar_size r > term_nonvar_size r1).
    - intro. apply is_common_part_nonvar_size in H2. lia.
    - lia.
  * constructor; lia.
  * good_inversion H3. specialize IHis_common_part1 with (r1 := Con f r1 r0) (r := Con f r r4).
    edestruct IHis_common_part1 as [ IH1 IH2 ]. constructor; eauto. simpl. lia. simpl in IH2.
    specialize IHis_common_part2 with (r1 := Con f l1 r0) (r := Con f l r4).
    edestruct IHis_common_part2 as [ IH3 IH4 ]. constructor; eauto. simpl. lia. simpl in IH4.
    constructor; lia.
Qed.

Lemma is_common_part_nonvar_size_inv t1 t2 t (H1 : is_common_part t1 t2 t)
                                     (H2 : term_nonvar_size t1 = term_nonvar_size t)
                                   : is_common_part t1 t2 t1.
Proof.
  induction H1; try constructor; simpl in H2.
  * destruct t; good_inversion H2. constructor.
  * apply IHis_common_part1. eapply is_common_part_same_nonvar_size_con; eauto. lia.
  * apply IHis_common_part2. eapply is_common_part_same_nonvar_size_con. apply H1_. eauto. lia.
Qed.

Lemma is_common_part_inf_unifiable s t1 t2 t (H1 : is_common_part t1 t2 t)
                                   (H2 : inf_unifier (term_to_inf t1) (term_to_inf t2) s)
                                 : inf_unifier (term_to_inf t1) (term_to_inf t) s.
Proof.
  induction H1; auto. apply inf_unifier_refl. unfold inf_unifier in H2 |- *.
  rewrite inf_term_step_prop in H2 at 1 |- * at 1. rewrite inf_term_step_prop in H2 |- *.
  simpl in H2 |- *. apply inf_term_eq_con.
  * apply IHis_common_part1. eapply inf_term_eq_conl. eauto.
  * apply IHis_common_part2. eapply inf_term_eq_conr. eauto.
Qed.

Corollary is_common_part_unifiable s t1 t2 t (H1 : is_common_part t1 t2 t) (H2 : unifier s t1 t2)
                                 : unifier s t1 t.
Proof. apply unifier_inf. eapply is_common_part_inf_unifiable. eauto. apply unifier_inf. auto. Qed.

Lemma is_common_part_inf_unifiable_inv s t1 t2 (H : inf_unifier (term_to_inf t1) (term_to_inf t2) s)
                                     : exists t, is_common_part t1 t2 t.
Proof.
  revert t2 H. induction t1; intros.
  * exists (Var n). constructor.
  * destruct t2.
    - exists (Var n0). constructor.
    - edestruct (H Here) as [ t [ H1 H2 ] ]. constructor. good_inversion H1.
      rewrite inf_term_step_prop in H2 at 1. rewrite inf_term_step_prop in H2.
      good_inversion H2. eexists. constructor.
    - edestruct (H Here) as [ t [ H1 H2 ] ]. constructor. good_inversion H1.
      rewrite inf_term_step_prop in H2 at 1. rewrite inf_term_step_prop in H2. inversion H2.
  * destruct t2.
    - exists (Var n0). constructor.
    - edestruct (H Here) as [ t [ H1 H2 ] ]. constructor. good_inversion H1.
      rewrite inf_term_step_prop in H2 at 1. rewrite inf_term_step_prop in H2. inversion H2.
    - edestruct (H Here) as [ t [ H1 H2 ] ]. constructor. good_inversion H1.
      rewrite inf_term_step_prop in H2 at 1. rewrite inf_term_step_prop in H2. good_inversion H2.
      unfold inf_unifier in H. rewrite inf_term_step_prop in H at 1. rewrite inf_term_step_prop in H.
      simpl in H.
      edestruct IHt1_1 as [ l H2 ]. eapply inf_term_eq_conl. eauto.
      edestruct IHt1_2 as [ r H3 ]. eapply inf_term_eq_conr. eauto.
      eexists. constructor; eauto.
Qed.

Corollary is_common_part_unifiable_inv s t1 t2 (H : unifier s t1 t2) : exists t, is_common_part t1 t2 t.
Proof. eapply is_common_part_inf_unifiable_inv. apply unifier_inf. eauto. Qed.

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

Definition wf_eqsys_union_spec (s : wf_eqsys) (x y : name)
                               (res : wf_eqsys * option (term * term)) : Prop :=
match res with
| (s', None) =>
  (
    inf_min_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst s) (wf_eqsys_to_subst s')
  ) /\ (
    forall xs, NoDup xs -> In x xs -> In y xs -> incl (eqsys_vars (wf_eqsys_get s)) xs
            -> eqsys_roots_num (wf_eqsys_get s') xs <= eqsys_roots_num (wf_eqsys_get s) xs
  ) /\ (
    eqsys_nonvar_size (wf_eqsys_get s') <= eqsys_nonvar_size (wf_eqsys_get s)
  ) /\ (
    forall z, In z (eqsys_vars (wf_eqsys_get s')) -> In z (eqsys_vars (wf_eqsys_get s))
                                                  \/ z = x \/ z = y
  )
| (s', Some (t1, t2)) =>
  (
    forall s'', inf_min_unifying_extension (term_to_inf t1) (term_to_inf t2) (wf_eqsys_to_subst s') s''
             -> inf_min_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst s) s''
  ) /\ (
    forall s'', inf_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst s) s''
             -> inf_unifying_extension (term_to_inf t1) (term_to_inf t2) (wf_eqsys_to_subst s') s''
  ) /\ (
    forall xs, NoDup xs -> incl (eqsys_dom (wf_eqsys_get s)) xs
            -> eqsys_roots_num (wf_eqsys_get s) xs = 1 + eqsys_roots_num (wf_eqsys_get s') xs
  ) /\ (
    incl (eqsys_vars (wf_eqsys_get s')) (eqsys_vars (wf_eqsys_get s))
 /\ in_eqsys_rhs (wf_eqsys_get s) t1 /\ in_eqsys_rhs (wf_eqsys_get s) t2
  )
end.

(*
Тут есть варианты:
1. Когда с одной стороны свободная переменная, можно цеплять её за терм другой переменной —
   это даст такую же систему с точностью до walk, но увеличит размер системы,
   что значительно усложняет доказательство терминируемости
2. Когда с обеих сторон связанные переменные, можно вычислять common part
   и связывать объединённые переменные с ним — это должно быть эквивалентно
   с точки зрения спецификации union и позволяет ускорять алгоритм за счёт
   раннего обнаружения ошибок и упрощения системы, но на терминируемость глобально не влияет
*)

Definition eqsys_union (s : wf_eqsys) (x y : name) : eqsys * option (term * term) :=
  let (x, xt) := wf_eqsys_walk s x in
  let (y, yt) := wf_eqsys_walk s y in
  let s := wf_eqsys_get s in

  if name_eq_dec x y then (s, None)
  else
    let res := match xt, yt with
    | Var _, _ => None
    | _, Var _ => None
    | _, _ => Some (xt, yt)
    end in

    let (x, y) := match yt with
    | Var _ => (y, x)
    | _ => (x, y)
    end in

    ((x, Var y) :: s, res).

Lemma eqsys_union_well_formed s s' x y res (H : eqsys_union s x y = (s', res))
                            : eqsys_well_formed s'.
Proof.
  unfold eqsys_union in H.
  remember (wf_eqsys_walk s x) as res1. symmetry in Heqres1. destruct res1 as [ x' xt ].
  remember (wf_eqsys_walk s y) as res2. symmetry in Heqres2. destruct res2 as [ y' yt ].
  destruct (name_eq_dec x' y'). good_inversion H. apply wf_eqsys_get_well_formed.
  assert (H1 : eqsys_walkable ((y', Var x') :: wf_eqsys_get s) y'). {
    apply eqsys_walkable_extend_var. apply eqsys_walkable_path.
    exists [x']. apply eqsys_walk_path_extend_same.
    * intro. destruct H0; good_inversion H0. contradiction.
    * eapply eqsys_walk_path_result_fst. erewrite <- Heqres1. apply wf_eqsys_walk_prop.
  }
  assert (H2 : eqsys_walkable ((x', Var y') :: wf_eqsys_get s) x'). {
    apply eqsys_walkable_extend_var. apply eqsys_walkable_path.
    exists [y']. apply eqsys_walk_path_extend_same.
    * intro. destruct H0; good_inversion H0. contradiction.
    * eapply eqsys_walk_path_result_fst. erewrite <- Heqres2. apply wf_eqsys_walk_prop.
  }
  destruct yt; good_inversion H; apply wf_eqsys_extend_well_formed; auto.
Qed.

Lemma wf_eqsys_union_aux s x y : { res | match res with
                                         | (s', ts) => eqsys_union s x y = (wf_eqsys_get s', ts)
                                         end }.
Proof.
  remember (eqsys_union s x y) as res. symmetry in Heqres. destruct res as [ s' ts ].
  set (s'' := exist _ s' (eqsys_union_well_formed _ _ _ _ _ Heqres) : wf_eqsys).
  exists (s'', ts). auto.
Defined.

Definition wf_eqsys_union (s : wf_eqsys) (x y : name) : wf_eqsys * option (term * term) :=
  proj1_sig (wf_eqsys_union_aux s x y).

Fact wf_eqsys_union_def s x y s' ts (H : wf_eqsys_union s x y = (s', ts))
                      : eqsys_union s x y = (wf_eqsys_get s', ts).
Proof. unfold wf_eqsys_union in H. destruct (wf_eqsys_union_aux s x y). simpl in H. subst. auto. Qed.

Lemma wf_eqsys_union_same_prop s s' x y z xt yt
  (H : wf_eqsys_eq s s') (H1 : wf_eqsys_walk s x = (z, xt)) (H2 : wf_eqsys_walk s y = (z, yt))
: inf_min_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst s) (wf_eqsys_to_subst s').
Proof.
  eapply inf_min_unifying_extension_eq. 1, 2, 3: reflexivity. apply wf_eqsys_to_subst_eq. eauto.
  apply inf_min_unifying_extension_same.
  eapply inf_unifier_eq. 3: apply wf_eqsys_to_subst_eq; eauto. all: try reflexivity.
  fold (term_to_inf (Var x)). fold (term_to_inf (Var y)). unfold inf_unifier.
  repeat rewrite wf_eqsys_to_subst_apply. simpl.
  rewrite wf_eqsys_image_walk. rewrite H1. simpl.
  rewrite wf_eqsys_image_walk. rewrite H2. simpl.
  replace xt with yt. reflexivity. eapply wf_eqsys_walk_fst_inj; eauto.
Qed.

Lemma wf_eqsys_union_unbound_prop1 s s' x y x' y' t
  (H : wf_eqsys_get s' = (x', Var y') :: wf_eqsys_get s) (H1 : x' <> y')
  (H2 : wf_eqsys_walk s x = (x', Var x')) (H3 : wf_eqsys_walk s y = (y', t))
: inf_min_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst s) (wf_eqsys_to_subst s').
Proof.
  apply (inf_min_unifying_extension_unifier _ (InfVar x')). {
    unfold inf_unifier. repeat rewrite inf_subst_apply_var, wf_eqsys_to_subst_image.
    rewrite wf_eqsys_image_walk. rewrite H2. reflexivity.
  }
  assert (~in_eqsys_dom (wf_eqsys_get s) x'). eapply wf_eqsys_walk_var_dom. eauto.
  apply inf_min_unifying_extension_unbound.
  * etransitivity. eapply wf_eqsys_to_subst_extend_unbound; eauto.
    apply inf_subst_compose_eq; try reflexivity.
    rewrite inf_subst_apply_var, wf_eqsys_to_subst_image.
    apply inf_subst_eq_ext. intro z.
    destruct (name_eq_dec z x'). 2: repeat rewrite inf_image_singleton_other; auto; reflexivity.
    subst z. repeat rewrite inf_image_singleton_same, wf_eqsys_image_walk.
    replace (wf_eqsys_walk s' y) with (wf_eqsys_walk s' x'). reflexivity.
    transitivity (wf_eqsys_walk s' y'). {
      apply wf_eqsys_walk_ext. eapply ESWalkWalk. rewrite H. simpl.
      destruct (name_eq_dec x' x'). auto. contradiction. apply wf_eqsys_walk_prop.
    }
    assert (wf_eqsys_walk s x = wf_eqsys_walk s x'). rewrite wf_eqsys_walk_idemp, H2. auto.
    assert (wf_eqsys_walk s y = wf_eqsys_walk s y'). rewrite wf_eqsys_walk_idemp, H3. auto.
    transitivity (wf_eqsys_walk s y'). {
      edestruct wf_eqsys_walk_extend as [ | [] ]; eauto.
      rewrite H4, <- H6, <- H5, H3 in H2. good_inversion H2. contradiction.
    }
    rewrite <- H5.
    edestruct wf_eqsys_walk_extend as [ | [] ]; eauto.
    rewrite H6, <- H4, H2 in H3. good_inversion H3. contradiction.
  * intro. apply wf_eqsys_to_subst_dom in H4. auto.
  * rewrite inf_subst_apply_var, wf_eqsys_to_subst_image.
    rewrite inf_term_step_prop at 1. simpl. rewrite H3. intro.
    destruct t; good_inversion H4. apply wf_eqsys_walk_var in H3. auto.
Qed.

Lemma wf_eqsys_union_unbound_prop2 s s' x y x' y' t xs
  (H1 : NoDup xs) (H2 : In x xs) (H3 : incl (eqsys_vars (wf_eqsys_get s)) xs)
  (H4 : wf_eqsys_walk s x = (x', Var x')) (H5 : wf_eqsys_walk s y = (y', t))
  (H6 : wf_eqsys_get s' = (x', Var y') :: wf_eqsys_get s)
: eqsys_roots_num (wf_eqsys_get s') xs <= eqsys_roots_num (wf_eqsys_get s) xs.
Proof.
  assert (In x' xs). apply wf_eqsys_walk_in_vars in H4. destruct H4; subst; auto.
  assert (is_eqsys_root (wf_eqsys_get s) x' = true). apply wf_eqsys_walk_root in H4. auto.
  erewrite (eqsys_roots_num_extend_var (wf_eqsys_get s) _ x' y'); eauto. rewrite H6. lia.
Qed.

Lemma wf_eqsys_union_unbound_prop3 s s' x y x' y' t
  (H1 : wf_eqsys_walk s x = (x', Var x')) (H2 : wf_eqsys_walk s y = (y', t))
  (H3 : wf_eqsys_get s' = (x', Var y') :: wf_eqsys_get s)
: eqsys_nonvar_size (wf_eqsys_get s') <= eqsys_nonvar_size (wf_eqsys_get s).
Proof.
  rewrite H3. specialize (eqsys_nonvar_size_extend x' (Var y') (wf_eqsys_get s)).
  intro. simpl in H. lia.
Qed.

Lemma wf_eqsys_union_unbound_prop4 s s' x y x' y' t z
  (H1 : wf_eqsys_walk s x = (x', Var x')) (H2 : wf_eqsys_walk s y = (y', t))
  (H3 : wf_eqsys_get s' = (x', Var y') :: wf_eqsys_get s)
  (H4 : In z (eqsys_vars (wf_eqsys_get s')))
: In z (eqsys_vars (wf_eqsys_get s)) \/ z = x \/ z = y.
Proof.
  apply eqsys_vars_in in H4. destruct H4.
  * apply eqsys_dom_spec in H. rewrite H3 in H. simpl in H.
    apply ListSet.set_add_elim in H. destruct H.
    - subst z. apply wf_eqsys_walk_in_vars in H1. destruct H1; auto.
    - left. apply eqsys_vars_in_dom. apply eqsys_dom_spec. auto.
  * destruct H as [ t' [] ]. rewrite H3 in H. destruct H.
    - subst. destruct H0; good_inversion H. apply wf_eqsys_walk_in_vars in H2. destruct H2; auto.
    - left. eapply eqsys_vars_in_rhs; eauto.
Qed.

Lemma wf_eqsys_union_bound_prop1 m m' s x y x' y' t1 t2
  (H1 : x' <> y') (H2 : t1 <> Var x')
  (H3 : wf_eqsys_walk m x = (x', t1)) (H4 : wf_eqsys_walk m y = (y', t2))
  (H5 : wf_eqsys_get m' = (x', Var y') :: wf_eqsys_get m)
  (H6 : inf_min_unifying_extension (term_to_inf t1) (term_to_inf t2) (wf_eqsys_to_subst m') s)
: inf_min_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst m) s.
Proof.
  destruct H6 as [ [ [ s' ] ] ].
  assert (wf_eqsys_walk m x' = (x', t1)). {
    set (H' := H3). rewrite wf_eqsys_walk_idemp in H'. rewrite H3 in H'. simpl in H'. auto.
  }
  assert (wf_eqsys_walk m y' = (y', t2)). {
    set (H' := H4). rewrite wf_eqsys_walk_idemp in H'. rewrite H4 in H'. simpl in H'. auto.
  }
  assert (in_eqsys_dom (wf_eqsys_get m) x'). eapply wf_eqsys_walk_var_dom_inv; eauto.
  assert (inf_subst_eq s (inf_subst_compose s' (wf_eqsys_to_subst m))). {
    rewrite H. symmetry. eapply wf_eqsys_to_subst_extend_bound_unifier; eauto.
    rewrite H7. simpl. unfold inf_unifier. rewrite <- wf_eqsys_to_subst_apply, inf_subst_compose_spec.
    etransitivity. symmetry. apply H. etransitivity. apply H0. etransitivity. apply H.
    rewrite <- inf_subst_compose_spec. apply inf_subst_apply_eq. rewrite wf_eqsys_to_subst_apply.
    rewrite wf_eqsys_image_walk. replace t2 with (snd (wf_eqsys_walk m' y')). reflexivity.
    edestruct wf_eqsys_walk_extend; eauto. rewrite <- H10, H8. auto.
    destruct H10. rewrite <- H10, H8 in H7. good_inversion H7. contradiction.
  }
  constructor. constructor. eexists. eauto.
  * eapply inf_unifier_eq. 1, 2: reflexivity. symmetry. apply H10. unfold inf_unifier.
    repeat rewrite <- inf_subst_compose_spec, inf_subst_apply_var, wf_eqsys_to_subst_image.
    etransitivity. 2: etransitivity. 2: apply H0. symmetry. all: etransitivity; [ apply H10 | ].
    all: rewrite <- inf_subst_compose_spec; apply inf_subst_apply_eq.
    all: rewrite wf_eqsys_to_subst_apply; rewrite wf_eqsys_image_walk.
    rewrite H3. reflexivity. rewrite H4. reflexivity.
  * intros s1 [ [ s1' ] ]. apply H6.
    assert (inf_subst_eq s1 (inf_subst_compose s1' (wf_eqsys_to_subst m'))). {
      rewrite H11. eapply wf_eqsys_to_subst_extend_inv_unifier; eauto.
      unfold inf_unifier. fold (wf_eqsys_apply m (Var x')).
      repeat rewrite <- wf_eqsys_to_subst_apply, inf_subst_compose_spec.
      etransitivity. symmetry. etransitivity. symmetry. apply H12.
      all: etransitivity; try apply H11; repeat rewrite <- inf_subst_compose_spec.
      all: apply inf_subst_apply_eq; rewrite inf_subst_apply_var, wf_eqsys_to_subst_image.
      all: rewrite wf_eqsys_to_subst_apply; simpl.
      replace (wf_eqsys_image m x') with (wf_eqsys_image m x). reflexivity.
      rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
      rewrite H3, H7. reflexivity.
      replace (wf_eqsys_image m y') with (wf_eqsys_image m y). reflexivity.
      rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
      rewrite H4, H8. reflexivity.
    }
    constructor. eexists. eauto. unfold inf_unifier.
    etransitivity. etransitivity. 2: apply H12.
    all: etransitivity; [ apply H11 | ]; symmetry; etransitivity; [ apply H11 | ].
    all: repeat rewrite <- inf_subst_compose_spec; apply inf_subst_apply_eq. 2: symmetry.
    all: rewrite inf_subst_apply_var, wf_eqsys_to_subst_image, wf_eqsys_image_walk, wf_eqsys_to_subst_apply.
    rewrite H3. reflexivity. rewrite H4. reflexivity.
Qed.

Lemma wf_eqsys_union_bound_prop2 m m' s x y x' y' t1 t2
  (H1 : wf_eqsys_walk m x = (x', t1)) (H2 : wf_eqsys_walk m y = (y', t2))
  (H3 : wf_eqsys_get m' = (x', Var y') :: wf_eqsys_get m)
  (H4 : inf_unifying_extension (InfVar x) (InfVar y) (wf_eqsys_to_subst m) s)
: inf_unifying_extension (term_to_inf t1) (term_to_inf t2) (wf_eqsys_to_subst m') s.
Proof.
  destruct H4 as [ [ s' ] ].
  assert (wf_eqsys_walk m x' = (x', t1)). {
    set (H' := H1). rewrite wf_eqsys_walk_idemp in H'. rewrite H1 in H'. simpl in H'. auto.
  }
  assert (wf_eqsys_walk m y' = (y', t2)). {
    set (H' := H2). rewrite wf_eqsys_walk_idemp in H'. rewrite H2 in H'. simpl in H'. auto.
  }
  assert (inf_subst_eq s (inf_subst_compose s' (wf_eqsys_to_subst m'))). {
    rewrite H. eapply wf_eqsys_to_subst_extend_inv_unifier; eauto.
    unfold inf_unifier. fold (wf_eqsys_apply m (Var x')).
    repeat rewrite <- wf_eqsys_to_subst_apply, inf_subst_compose_spec.
    etransitivity. symmetry. etransitivity. symmetry. apply H0.
    all: etransitivity; try apply H; repeat rewrite <- inf_subst_compose_spec.
    all: apply inf_subst_apply_eq; rewrite inf_subst_apply_var, wf_eqsys_to_subst_image.
    all: rewrite wf_eqsys_to_subst_apply; simpl.
    replace (wf_eqsys_image m x') with (wf_eqsys_image m x). reflexivity.
    rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
    rewrite H1, H4. reflexivity.
    replace (wf_eqsys_image m y') with (wf_eqsys_image m y). reflexivity.
    rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
    rewrite H2, H5. reflexivity.
  }
  constructor. eexists. eauto. unfold inf_unifier.
  etransitivity. etransitivity. 2: apply H0.
  all: etransitivity; [ apply H | ]; symmetry; etransitivity; [ apply H | ].
  all: repeat rewrite <- inf_subst_compose_spec; apply inf_subst_apply_eq. 2: symmetry.
  all: rewrite inf_subst_apply_var, wf_eqsys_to_subst_image, wf_eqsys_image_walk, wf_eqsys_to_subst_apply.
  rewrite H1. reflexivity. rewrite H2. reflexivity.
Qed.

Lemma wf_eqsys_union_bound_prop3 s s' x x' y' t xs
  (H1 : NoDup xs) (H2 : incl (eqsys_dom (wf_eqsys_get s)) xs) (H3 : t <> Var x')
  (H4 : wf_eqsys_walk s x = (x', t)) (H5 : wf_eqsys_get s' = (x', Var y') :: wf_eqsys_get s)
: eqsys_roots_num (wf_eqsys_get s) xs = 1 + eqsys_roots_num (wf_eqsys_get s') xs.
Proof.
  rewrite H5. apply eqsys_roots_num_extend_var. auto.
  * destruct t. apply wf_eqsys_walk_var in H4. subst n. contradiction.
    all: apply H2; apply eqsys_dom_spec; eapply wf_eqsys_walk_var_dom_inv; eauto.
  * apply wf_eqsys_walk_root in H4. auto.
Qed.

Lemma wf_eqsys_union_bound_prop4 s s' x x' y y' t1 t2
    (H1 : wf_eqsys_walk s x = (x', t1)) (H2 : wf_eqsys_walk s y = (y', t2))
    (H3 : t1 <> Var x') (H4 : t2 <> Var y') (H5 : wf_eqsys_get s' = (x', Var y') :: wf_eqsys_get s)
  : incl (eqsys_vars (wf_eqsys_get s')) (eqsys_vars (wf_eqsys_get s))
 /\ in_eqsys_rhs (wf_eqsys_get s) t1 /\ in_eqsys_rhs (wf_eqsys_get s) t2.
Proof.
  constructor.
  * intros z ?. apply eqsys_vars_in in H. destruct H.
    - destruct H as [ t' ]. rewrite H5 in H. simpl in H. apply eqsys_vars_in_dom.
      destruct (name_eq_dec z x').
      + subst z. good_inversion H. apply wf_eqsys_walk_var_dom_inv in H1; auto.
      + eexists. eauto.
    - destruct H as [ t' [] ]. rewrite H5 in H. simpl in H. destruct H.
      + subst. destruct H0. 2: contradiction. subst z. apply eqsys_vars_in_dom.
        apply wf_eqsys_walk_var_dom_inv in H2; auto.
      + eapply eqsys_vars_in_rhs; eauto.
  * constructor.
    - edestruct wf_eqsys_walk_rhs. rewrite H1 in H. auto. destruct H. rewrite H in H1.
      good_inversion H1. contradiction.
    - edestruct wf_eqsys_walk_rhs. rewrite H2 in H. auto. destruct H. rewrite H in H2.
      good_inversion H2. contradiction.
Qed.

Lemma wf_eqsys_union_prop s x y : wf_eqsys_union_spec s x y (wf_eqsys_union s x y).
Proof.
  remember (wf_eqsys_union s x y) as res. symmetry in Heqres.
  destruct res as [ s' ts ]. apply wf_eqsys_union_def in Heqres. unfold eqsys_union in Heqres.
  remember (wf_eqsys_walk s x) as res1. symmetry in Heqres1. destruct res1 as [ x' tx ].
  remember (wf_eqsys_walk s y) as res2. symmetry in Heqres2. destruct res2 as [ y' ty ].
  destruct (name_eq_dec x' y').
  * good_inversion Heqres. constructor. eapply wf_eqsys_union_same_prop; eauto.
    constructor; try constructor; intros; rewrite H0; auto.
  * symmetry in Heqres. destruct ty; good_inversion Heqres.
    replace (match tx with | Var _ | _ => None end) with (@None (term * term)) by (destruct tx; auto).
    set (H' := Heqres2). apply wf_eqsys_walk_var in H'. subst n0.
    constructor. apply inf_min_unifying_extension_sym. eapply wf_eqsys_union_unbound_prop1; eauto.
    constructor. intros. eapply wf_eqsys_union_unbound_prop2; try apply H0; eauto.
    constructor; intros. eapply wf_eqsys_union_unbound_prop3; try apply H0; eauto.
    eapply wf_eqsys_union_unbound_prop4 in H0. 2: apply Heqres2. 2, 3: eauto.
    destruct H0 as [ | [ | ] ]; auto.
    all: destruct tx.
    1, 4: set (H' := Heqres1); apply wf_eqsys_walk_var in H'; subst n1.
    1, 2: constructor; try eapply wf_eqsys_union_unbound_prop1; eauto.
    1, 2: constructor; intros; try eapply wf_eqsys_union_unbound_prop2; try apply H1; eauto.
    1, 2: constructor; intros; try eapply wf_eqsys_union_unbound_prop3; eauto.
    1, 2: eapply wf_eqsys_union_unbound_prop4; eauto.
    all: constructor; intros; try eapply wf_eqsys_union_bound_prop1; eauto.
    all: try (constructor; intros; try eapply wf_eqsys_union_bound_prop2; eauto).
    all: try (constructor; intros; try eapply wf_eqsys_union_bound_prop3; try apply H0; eauto).
    all: try eapply wf_eqsys_union_bound_prop4; eauto.
    all: intros ?; try inversion H1; try inversion H2; try inversion H.
Qed.

Corollary wf_eqsys_union_prop' s x y res (H : wf_eqsys_union s x y = res)
                             : wf_eqsys_union_spec s x y res.
Proof. subst. apply wf_eqsys_union_prop. Qed.

Definition rational_unify_vt_spec (s : wf_eqsys) (x : name) (yt : term)
                                  (res : option (wf_eqsys * option term)) : Prop :=
match res with
| None =>
  forall s', inf_subst_more_general (wf_eqsys_to_subst s) s'
          -> ~inf_unifier (InfVar x) (term_to_inf yt) s'
| Some (s', None) =>
  (
    inf_min_unifying_extension (InfVar x) (term_to_inf yt) (wf_eqsys_to_subst s) (wf_eqsys_to_subst s')
  ) /\ (
    forall xs, NoDup xs -> In x xs -> incl (eqsys_vars (wf_eqsys_get s)) xs
            -> eqsys_roots_num (wf_eqsys_get s') xs = eqsys_roots_num (wf_eqsys_get s) xs
  ) /\ (
    eqsys_nonvar_size (wf_eqsys_get s') = eqsys_nonvar_size (wf_eqsys_get s) + term_nonvar_size yt
  ) /\ (
    forall z, In z (eqsys_vars (wf_eqsys_get s')) -> In z (eqsys_vars (wf_eqsys_get s))
                                                  \/ z = x \/ In z (fv_term yt)
  )
| Some (s', Some xt) =>
  (
    forall s'', inf_min_unifying_extension (term_to_inf xt) (term_to_inf yt) (wf_eqsys_to_subst s') s''
             -> inf_min_unifying_extension (InfVar x) (term_to_inf yt) (wf_eqsys_to_subst s) s''
  ) /\ (
    forall s'', inf_unifying_extension (InfVar x) (term_to_inf yt) (wf_eqsys_to_subst s) s''
             -> inf_unifying_extension (term_to_inf xt) (term_to_inf yt) (wf_eqsys_to_subst s') s''
  ) /\ (
    forall xs, NoDup xs -> In x xs -> incl (eqsys_vars (wf_eqsys_get s)) xs
            -> eqsys_roots_num (wf_eqsys_get s') xs = eqsys_roots_num (wf_eqsys_get s) xs
  ) /\ (
    exists t, is_common_part xt yt t /\ eqsys_nonvar_size (wf_eqsys_get s') + term_nonvar_size xt
                                      = eqsys_nonvar_size (wf_eqsys_get s) + term_nonvar_size t
  ) /\ (
    forall z, In z (eqsys_vars (wf_eqsys_get s')) -> In z (eqsys_vars (wf_eqsys_get s))
                                                  \/ In z (fv_term yt)
  ) /\ (
    in_eqsys_rhs (wf_eqsys_get s) xt
  ) /\ (
    forall x, xt <> Var x
  )
end.

Definition rational_unify_vt_impl (s : wf_eqsys) (x : name) (yt : term) : option (eqsys * option term) :=
  let (x, xt) := wf_eqsys_walk s x in

  match xt with
  | Var _ => Some ((x, yt) :: wf_eqsys_get s, None)
  | _ =>
    match common_part xt yt with
    | None => None
    | Some t => Some ((x, t) :: wf_eqsys_get s, Some xt)
    end
  end.

Lemma rational_unify_vt_impl_well_formed s s' x yt t (H1 : forall y, yt <> Var y)
                                         (H2 : rational_unify_vt_impl s x yt = Some (s', t))
                                       : eqsys_well_formed s'.
Proof.
  unfold rational_unify_vt_impl in H2.
  remember (wf_eqsys_walk s x) as res1. symmetry in Heqres1. destruct res1 as [ x' xt ].
  remember (name_eq_dec x' x') as cond. symmetry in Heqcond. destruct cond. 2: contradiction.
  destruct xt.
  * good_inversion H2. apply eqsys_well_formed_extend. apply wf_eqsys_get_well_formed.
    destruct yt. exfalso. eapply H1. auto. all: eexists. apply ESWalkCst. 2: apply ESWalkCon.
    all: simpl; rewrite Heqcond; auto; contradiction.
  * remember (common_part (Cst n) yt) as res2. symmetry in Heqres2.
    destruct res2; good_inversion H2. apply common_part_some in Heqres2. good_inversion Heqres2.
    exfalso. eapply H1. auto. apply eqsys_well_formed_extend. apply wf_eqsys_get_well_formed.
    eexists. apply ESWalkCst. simpl. rewrite Heqcond. auto.
  * remember (common_part (Con n xt1 xt2) yt) as res2. symmetry in Heqres2.
    destruct res2; good_inversion H2. apply common_part_some in Heqres2. good_inversion Heqres2.
    exfalso. eapply H1. auto. apply eqsys_well_formed_extend. apply wf_eqsys_get_well_formed.
    eexists. apply ESWalkCon. simpl. rewrite Heqcond. auto.
Qed.

Lemma rational_unify_vt_aux s x yt (H : forall y, yt <> Var y)
  : { res | match res with
            | None => rational_unify_vt_impl s x yt = None
            | Some (s', xt) => rational_unify_vt_impl s x yt = Some (wf_eqsys_get s', xt)
            end }.
Proof.
  remember (rational_unify_vt_impl s x yt) as res. symmetry in Heqres. destruct res as [ [ s' xt ] | ].
  * exists (Some (exist _ _ (rational_unify_vt_impl_well_formed _ _ _ _ _ H Heqres), xt)). auto.
  * exists None. auto.
Qed.

Definition rational_unify_vt (s : wf_eqsys) (x : name) (yt : term) (H : forall y, yt <> Var y)
                           : option (wf_eqsys * option term) :=
  proj1_sig (rational_unify_vt_aux s x yt H).

Fact rational_unify_vt_none s x yt H : rational_unify_vt s x yt H = None
                                   <-> rational_unify_vt_impl s x yt = None.
Proof.
  unfold rational_unify_vt. destruct (rational_unify_vt_aux s x yt H) as [ [ [ s' xt ] | ] H1 ]; simpl.
  * constructor; intro. inversion H0. rewrite H0 in H1. inversion H1.
  * constructor; intro; auto.
Qed.

Fact rational_unify_vt_some s x yt H s' xt (H1 : rational_unify_vt s x yt H = Some (s', xt))
                          : rational_unify_vt_impl s x yt = Some (wf_eqsys_get s', xt).
Proof.
  unfold rational_unify_vt in H1.
  destruct (rational_unify_vt_aux s x yt H) as [ [ [ s1 xt1 ] | ] H2 ]; good_inversion H1. auto.
Qed.

Lemma rational_unify_vt_unbound_prop1 s s' x x' yt (H1 : wf_eqsys_walk s x = (x', Var x'))
                                      (H2 : wf_eqsys_get s' = (x', yt) :: wf_eqsys_get s)
  : inf_min_unifying_extension (InfVar x) (term_to_inf yt) (wf_eqsys_to_subst s) (wf_eqsys_to_subst s').
Proof.
  assert (~in_eqsys_dom (wf_eqsys_get s) x'). apply wf_eqsys_walk_var_dom in H1. auto.
  assert (inf_subst_eq (wf_eqsys_to_subst s') (inf_subst_compose (inf_subst_singleton x' (wf_eqsys_apply s' yt)) (wf_eqsys_to_subst s))). {
    rewrite wf_eqsys_to_subst_extend_unbound; eauto. apply inf_subst_compose_eq; try reflexivity.
    apply inf_subst_eq_ext. intro z. destruct (name_eq_dec x' z). subst z.
    2: repeat rewrite inf_image_singleton_other; auto; reflexivity.
    repeat rewrite inf_image_singleton_same. rewrite wf_eqsys_image_walk.
    edestruct wf_eqsys_walk_extend_new; eauto. rewrite H0. reflexivity.
    destruct H0 as [ y ]. subst. simpl. rewrite wf_eqsys_image_walk.
    erewrite wf_eqsys_walk_ext. reflexivity. eapply ESWalkWalk. rewrite H2. simpl.
    destruct (name_eq_dec x' x'). auto. contradiction. apply wf_eqsys_walk_prop.
  }
  constructor. constructor. eexists. eauto.
  * unfold inf_unifier. etransitivity. apply H0. rewrite wf_eqsys_to_subst_apply.
    rewrite <- inf_subst_compose_spec, inf_subst_apply_var, wf_eqsys_to_subst_image.
    rewrite (inf_term_step_prop (wf_eqsys_image s x)). simpl. rewrite H1.
    rewrite inf_subst_apply_var, inf_image_singleton_same. reflexivity.
  * intros s1 [ [ s1' ] ]. exists s1'. rewrite H3. symmetry.
    etransitivity. apply inf_subst_compose_eq. reflexivity. apply H0.
    rewrite inf_subst_compose_assoc. apply inf_subst_compose_eq; try reflexivity.
    apply inf_subst_eq_ext. intro z. rewrite inf_subst_compose_image.
    destruct (name_eq_dec x' z). subst z. rewrite inf_image_singleton_same. symmetry.
    2: rewrite inf_image_singleton_other, inf_subst_apply_var; auto; reflexivity.
    eapply inf_subst_recursive_unifier.
    - rewrite <- wf_eqsys_to_subst_apply. etransitivity. apply H0.
      rewrite <- inf_subst_compose_spec. repeat rewrite wf_eqsys_to_subst_apply. reflexivity.
    - etransitivity. etransitivity. 2: apply H4. symmetry.
      all: etransitivity; [ apply H3 | ]; rewrite <- inf_subst_compose_spec.
      + rewrite inf_subst_apply_var, wf_eqsys_to_subst_image.
        replace (wf_eqsys_image s x) with (InfVar x'). rewrite inf_subst_apply_var. reflexivity.
        rewrite inf_term_step_prop. simpl. rewrite H1. auto.
      + apply inf_subst_apply_eq. rewrite wf_eqsys_to_subst_apply. reflexivity.
    - intro. destruct yt; good_inversion H5. rewrite inf_term_step_prop in H7 at 1. simpl in H7.
      remember (wf_eqsys_walk s n) as res. destruct res as [ n' [] ]; good_inversion H7.
      symmetry in Heqres. set (H' := Heqres). apply wf_eqsys_walk_var in H'. subst n'.
      assert (exists p, eqsys_walk_path (wf_eqsys_get s') x' p).
      apply eqsys_walkable_path. apply wf_eqsys_get_well_formed.
      assert (exists p, eqsys_walk_path (wf_eqsys_get s) n p).
      apply eqsys_walkable_path. apply wf_eqsys_get_well_formed.
      destruct H5 as [ p ]. destruct H6 as [ q ].
      set (H' := H6). eapply eqsys_walk_path_result_fst_in in H'.
      2: rewrite <- Heqres; apply wf_eqsys_walk_prop.
      apply in_split_dec in H'. 2: apply name_eq_dec. destruct H' as [ q1 [ q2 [] ] ]. subst.
      eapply eqsys_walk_path_extend_concat in H6; eauto. 2: rewrite <- H2; eauto.
      rewrite <- H2 in H6. assert (exists p', p = x' :: n :: p'). {
        remember (name_eq_dec x' x') as cond. symmetry in Heqcond. destruct cond; try contradiction.
        good_inversion H5; rewrite H2 in H7; simpl in H7; rewrite Heqcond in H7; good_inversion H7.
        good_inversion H9; eexists; auto.
      }
      destruct H7 as [ p' ]. subst. rename p' into p.
      assert (exists q1', q1 = n :: q1'). {
        good_inversion H6; destruct q1; good_inversion H7; try (eexists; auto; fail).
        apply eqsys_walk_path_nodup in H5. good_inversion H5. exfalso. apply H10. left. auto.
      }
      destruct H7 as [ q1' ]. subst. rename q1' into q1. apply eqsys_walk_path_nodup in H6.
      good_inversion H6. apply H10. apply in_app_iff. right. right. left. auto.
Qed.

Lemma rational_unify_vt_unbound_prop2 s s' x x' yt xs (H1 : forall y, yt <> Var y)
                                      (H2 : wf_eqsys_walk s x = (x', Var x'))
                                      (H3 : wf_eqsys_get s' = (x', yt) :: wf_eqsys_get s)
                                      (H4 : NoDup xs) (H5 : In x xs)
                                      (H6 : incl (eqsys_vars (wf_eqsys_get s)) xs)
                                    : eqsys_roots_num (wf_eqsys_get s') xs
                                    = eqsys_roots_num (wf_eqsys_get s) xs.
Proof.
  rewrite H3. symmetry. apply eqsys_roots_num_extend_nonvar; auto.
  * apply wf_eqsys_walk_in_vars in H2. destruct H2; subst; auto.
  * apply wf_eqsys_walk_root in H2. auto.
Qed.

Lemma rational_unify_vt_unbound_prop3 s s' x x' yt (H1 : wf_eqsys_walk s x = (x', Var x'))
                                      (H2 : wf_eqsys_get s' = (x', yt) :: wf_eqsys_get s)
                                    : eqsys_nonvar_size (wf_eqsys_get s')
                                    = eqsys_nonvar_size (wf_eqsys_get s) + term_nonvar_size yt.
Proof.
  transitivity (eqsys_nonvar_size (wf_eqsys_get s') + eqsys_rhs_nonvar_size (wf_eqsys_get s) x').
  2: rewrite H2; apply eqsys_nonvar_size_extend. unfold eqsys_rhs_nonvar_size.
  apply wf_eqsys_walk_var_dom, in_eqsys_dom_inv in H1. rewrite H1. lia.
Qed.

Lemma rational_unify_vt_unbound_prop4 s s' x x' yt z (H1 : wf_eqsys_walk s x = (x', Var x'))
                                      (H2 : wf_eqsys_get s' = (x', yt) :: wf_eqsys_get s)
                                      (H3 : In z (eqsys_vars (wf_eqsys_get s')))
                                    : In z (eqsys_vars (wf_eqsys_get s))
                                   \/ z = x \/ In z (fv_term yt).
Proof.
  apply eqsys_vars_in in H3. destruct H3.
  * apply eqsys_dom_spec in H. rewrite H2 in H. simpl in H.
    apply ListSet.set_add_elim in H. destruct H.
    - subst z. apply wf_eqsys_walk_in_vars in H1. destruct H1; auto.
    - left. apply eqsys_vars_in_dom. apply eqsys_dom_spec. auto.
  * destruct H as [ t [] ]. rewrite H2 in H. destruct H. subst. auto.
    left. eapply eqsys_vars_in_rhs; eauto.
Qed.

Lemma rational_unify_vt_bound_prop1 s1 s2 s3 x x' xt yt t
  (H1 : wf_eqsys_walk s1 x = (x', xt)) (H2 : xt <> Var x')
  (H3 : is_common_part xt yt t) (H4 : wf_eqsys_get s2 = (x', t) :: wf_eqsys_get s1)
  (H5 : inf_min_unifying_extension (term_to_inf xt) (term_to_inf yt) (wf_eqsys_to_subst s2) s3)
: inf_min_unifying_extension (InfVar x) (term_to_inf yt) (wf_eqsys_to_subst s1) s3.
Proof.
  destruct H5 as [ [ [ s3' ] ] ].
  set (H6 := H1). rewrite wf_eqsys_walk_idemp, H1 in H6. simpl in H6.
  assert (inf_subst_eq s3 (inf_subst_compose s3' (wf_eqsys_to_subst s1))). {
    rewrite H. symmetry. eapply wf_eqsys_to_subst_extend_bound_unifier; eauto.
    eapply wf_eqsys_walk_var_dom_inv; eauto. rewrite H6. simpl.
    repeat rewrite <- wf_eqsys_to_subst_apply. unfold inf_unifier.
    repeat rewrite inf_subst_compose_spec. eapply is_common_part_inf_unifiable; eauto.
    eapply inf_unifier_eq; eauto; reflexivity.
  }
  constructor. constructor. eexists. eauto.
  * unfold inf_unifier. etransitivity. 2: apply H0. etransitivity. apply H7.
    symmetry. etransitivity. apply H7. symmetry. repeat rewrite <- inf_subst_compose_spec.
    apply inf_subst_apply_eq. rewrite inf_subst_apply_var, wf_eqsys_to_subst_image.
    rewrite wf_eqsys_image_walk, wf_eqsys_to_subst_apply, H1. reflexivity.
  * intros s' [ [ s'' ] ]. apply H5.
    assert (inf_subst_eq s' (inf_subst_compose s'' (wf_eqsys_to_subst s2))). {
      rewrite H8. eapply wf_eqsys_to_subst_extend_inv_unifier; eauto. unfold inf_unifier.
      etransitivity. apply inf_subst_apply_eq. apply wf_eqsys_image_walk. rewrite H6. simpl.
      repeat rewrite <- wf_eqsys_to_subst_apply, inf_subst_compose_spec.
      eapply is_common_part_inf_unifiable; eauto. unfold inf_unifier. symmetry.
      etransitivity. symmetry. apply H8. etransitivity. symmetry. apply H9.
      etransitivity. apply H8. repeat rewrite <- inf_subst_compose_spec. apply inf_subst_apply_eq.
      rewrite inf_subst_apply_var, wf_eqsys_to_subst_image, wf_eqsys_to_subst_apply.
      rewrite wf_eqsys_image_walk, H1. reflexivity.
    }
    constructor. eexists. eauto. unfold inf_unifier. etransitivity; try apply H9.
    etransitivity. apply H8. symmetry. etransitivity. apply H8.
    repeat rewrite <- inf_subst_compose_spec. apply inf_subst_apply_eq.
    rewrite inf_subst_apply_var, wf_eqsys_to_subst_image, wf_eqsys_to_subst_apply.
    rewrite wf_eqsys_image_walk, H1. reflexivity.
Qed.

Lemma rational_unify_vt_bound_prop2 s1 s2 s3 x x' xt yt t
  (H1 : wf_eqsys_walk s1 x = (x', xt)) (H2 : is_common_part xt yt t)
  (H3 : wf_eqsys_get s2 = (x', t) :: wf_eqsys_get s1)
  (H4 : inf_unifying_extension (InfVar x) (term_to_inf yt) (wf_eqsys_to_subst s1) s3)
: inf_unifying_extension (term_to_inf xt) (term_to_inf yt) (wf_eqsys_to_subst s2) s3.
Proof.
  destruct H4 as [ [ s3' ] ].
  set (H4 := H1). rewrite wf_eqsys_walk_idemp, H1 in H4. simpl in H4.
  assert (inf_subst_eq s3 (inf_subst_compose s3' (wf_eqsys_to_subst s2))). {
    rewrite H. eapply wf_eqsys_to_subst_extend_inv_unifier; eauto. unfold inf_unifier.
    etransitivity. apply inf_subst_apply_eq. apply wf_eqsys_image_walk. rewrite H4. simpl.
    repeat rewrite <- wf_eqsys_to_subst_apply, inf_subst_compose_spec.
    eapply is_common_part_inf_unifiable; eauto. unfold inf_unifier. symmetry.
    etransitivity. symmetry. apply H. etransitivity. symmetry. apply H0.
    etransitivity. apply H. repeat rewrite <- inf_subst_compose_spec. apply inf_subst_apply_eq.
    rewrite inf_subst_apply_var, wf_eqsys_to_subst_image, wf_eqsys_to_subst_apply.
    rewrite wf_eqsys_image_walk, H1. reflexivity.
  }
  constructor. eexists. eauto. unfold inf_unifier. etransitivity; try apply H0.
  etransitivity. apply H. symmetry. etransitivity. apply H.
  repeat rewrite <- inf_subst_compose_spec. apply inf_subst_apply_eq.
  rewrite inf_subst_apply_var, wf_eqsys_to_subst_image, wf_eqsys_to_subst_apply.
  rewrite wf_eqsys_image_walk, H1. reflexivity.
Qed.

Lemma rational_unify_vt_bound_prop3 s1 s2 x x' xt yt t xs
  (H1 : wf_eqsys_walk s1 x = (x', xt)) (H2 : is_common_part xt yt t)
  (H3 : forall x, xt <> Var x) (H4 : forall y, yt <> Var y)
  (H5 : wf_eqsys_get s2 = (x', t) :: wf_eqsys_get s1)
  (H6 : NoDup xs) (H7 : In x xs) (H8 : incl (eqsys_vars (wf_eqsys_get s1)) xs)
: eqsys_roots_num (wf_eqsys_get s2) xs = eqsys_roots_num (wf_eqsys_get s1) xs.
Proof.
  rewrite H5. symmetry. apply eqsys_roots_num_extend_nonvar; auto.
  * apply wf_eqsys_walk_in_vars in H1. destruct H1. apply H8. auto. subst. auto.
  * apply wf_eqsys_walk_root in H1. auto.
  * good_inversion H2. exfalso. eapply H3. auto. exfalso. eapply H4. auto.
    intros ? ?. inversion H. intros ? ?. inversion H2.
Qed.

Lemma rational_unify_vt_bound_prop4 s1 s2 x x' xt yt t
    (H1 : wf_eqsys_walk s1 x = (x', xt)) (H2 : xt <> Var x')
    (H3 : is_common_part xt yt t) (H4 : wf_eqsys_get s2 = (x', t) :: wf_eqsys_get s1)
  : exists t, is_common_part xt yt t /\ eqsys_nonvar_size (wf_eqsys_get s2) + term_nonvar_size xt
                                      = eqsys_nonvar_size (wf_eqsys_get s1) + term_nonvar_size t.
Proof.
  exists t. constructor. auto. etransitivity. 2: apply eqsys_nonvar_size_extend. rewrite <- H4.
  f_equal. unfold eqsys_rhs_nonvar_size. apply wf_eqsys_walk_last_nonvar in H1; auto. rewrite H1. auto.
Qed.

Lemma rational_unify_vt_bound_prop5 s1 s2 x x' xt yt t z
    (H1 : wf_eqsys_walk s1 x = (x', xt)) (H2 : xt <> Var x')
    (H3 : is_common_part xt yt t) (H4 : In z (eqsys_vars (wf_eqsys_get s2)))
    (H5 : wf_eqsys_get s2 = (x', t) :: wf_eqsys_get s1)
  : In z (eqsys_vars (wf_eqsys_get s1)) \/ In z (fv_term yt).
Proof.
  apply eqsys_vars_in in H4. destruct H4.
  * destruct H as [ t' ? ]. rewrite H5 in H. simpl in H. left.
    apply eqsys_vars_in_dom. destruct (name_eq_dec z x').
    - apply wf_eqsys_walk_last_nonvar in H1; auto. eexists. subst. eauto.
    - eexists. eauto.
  * destruct H as [ t' [] ]. rewrite H5 in H. simpl in H. destruct H. subst t'.
    eapply is_common_part_vars in H3; eauto. clear H0. destruct H3; auto.
    - left. eapply eqsys_vars_in_rhs; eauto. apply eqsys_rhs_in.
      edestruct wf_eqsys_walk_rhs. rewrite H1 in H0. auto.
      destruct H0 as [ z' ]. rewrite H0 in H1. good_inversion H1. contradiction.
    - left. eapply eqsys_vars_in_rhs; eauto.
Qed.

Lemma rational_unify_vt_bound_prop6 s x x' xt
    (H1 : wf_eqsys_walk s x = (x', xt)) (H2 : xt <> Var x')
  : in_eqsys_rhs (wf_eqsys_get s) xt.
Proof.
  edestruct wf_eqsys_walk_rhs. rewrite H1 in H. auto.
  destruct H. rewrite H in H1. good_inversion H1. contradiction.
Qed.

Lemma rational_unify_vt_fail_prop m s x x' xt yt (H1 : wf_eqsys_walk m x = (x', xt))
                                  (H2 : ~exists t, is_common_part xt yt t)
                                  (H3 : inf_subst_more_general (wf_eqsys_to_subst m) s)
                                : ~inf_unifier (InfVar x) (term_to_inf yt) s.
Proof.
  intro. apply H2. eapply is_common_part_inf_unifiable_inv. unfold inf_unifier.
  etransitivity; try apply H. destruct H3 as [ s' ]. etransitivity. apply H0. symmetry.
  etransitivity. apply H0. repeat rewrite <- inf_subst_compose_spec. apply inf_subst_apply_eq.
  rewrite inf_subst_apply_var, wf_eqsys_to_subst_image, wf_eqsys_to_subst_apply.
  rewrite wf_eqsys_image_walk, H1. reflexivity.
Qed.

Lemma rational_unify_vt_prop s x yt H : rational_unify_vt_spec s x yt (rational_unify_vt s x yt H).
Proof.
  remember (rational_unify_vt s x yt H) as res. symmetry in Heqres. destruct res as [ [ s' xt' ] | ].
  * apply rational_unify_vt_some in Heqres. unfold rational_unify_vt_impl in Heqres.
    remember (wf_eqsys_walk s x) as res1. symmetry in Heqres1. destruct res1 as [ x' [ z | c | f l r ] ].
    - good_inversion Heqres. set (H' := Heqres1). apply wf_eqsys_walk_var in H'. subst z.
      constructor. eapply rational_unify_vt_unbound_prop1; eauto.
      constructor; intros. eapply rational_unify_vt_unbound_prop2; eauto.
      constructor; intros. eapply rational_unify_vt_unbound_prop3; eauto.
      eapply rational_unify_vt_unbound_prop4; eauto.
    - set (xt := Cst c) in *. remember (common_part xt yt) as res2. symmetry in Heqres2.
      destruct res2; good_inversion Heqres. apply common_part_some in Heqres2.
      assert (forall z, xt <> Var z). intros ? ?. inversion H0.
      constructor; intros. eapply rational_unify_vt_bound_prop1; eauto.
      constructor; intros. eapply rational_unify_vt_bound_prop2; eauto.
      constructor; intros. eapply rational_unify_vt_bound_prop3; eauto.
      constructor. eapply rational_unify_vt_bound_prop4; eauto.
      constructor; intros. eapply rational_unify_vt_bound_prop5; eauto.
      constructor; auto. eapply rational_unify_vt_bound_prop6; eauto.
    - set (xt := Con f l r) in *. remember (common_part xt yt) as res2. symmetry in Heqres2.
      destruct res2; good_inversion Heqres. apply common_part_some in Heqres2.
      assert (forall z, xt <> Var z). intros ? ?. inversion H0.
      constructor; intros. eapply rational_unify_vt_bound_prop1; eauto.
      constructor; intros. eapply rational_unify_vt_bound_prop2; eauto.
      constructor; intros. eapply rational_unify_vt_bound_prop3; eauto.
      constructor. eapply rational_unify_vt_bound_prop4; eauto.
      constructor; intros. eapply rational_unify_vt_bound_prop5; eauto.
      constructor; auto. eapply rational_unify_vt_bound_prop6; eauto.
  * apply rational_unify_vt_none in Heqres. unfold rational_unify_vt_impl in Heqres.
    remember (wf_eqsys_walk s x) as res1. symmetry in Heqres1.
    destruct res1 as [ x' [ z | c | f l r ] ]. inversion Heqres.
    - set (xt := Cst c) in *. remember (common_part xt yt) as res2. symmetry in Heqres2.
      destruct res2; good_inversion Heqres. apply common_part_none in Heqres2. simpl. intros.
      eapply rational_unify_vt_fail_prop; eauto.
    - set (xt := Con f l r) in *. remember (common_part xt yt) as res2. symmetry in Heqres2.
      destruct res2; good_inversion Heqres. apply common_part_none in Heqres2. simpl. intros.
      eapply rational_unify_vt_fail_prop; eauto.
Qed.

Corollary rational_unify_vt_prop' s x yt H1 res (H2 : rational_unify_vt s x yt H1 = res)
                                : rational_unify_vt_spec s x yt res.
Proof. subst. apply rational_unify_vt_prop. Qed.

Inductive rational_unification : wf_eqsys -> term -> term -> option wf_eqsys -> Prop :=
| RUVarVarStop x y s1 s2 : wf_eqsys_union s1 x y = (s2, None)
                        -> rational_unification s1 (Var x) (Var y) (Some s2)
| RUVarVarCont x y t1 t2 s1 s2 res : wf_eqsys_union s1 x y = (s2, Some (t1, t2))
                                 -> rational_unification s2 t1 t2 res
                                 -> rational_unification s1 (Var x) (Var y) res
| RUVarTermFail x yt H s : rational_unify_vt s x yt H = None
                        -> rational_unification s (Var x) yt None
| RUVarTermStop x yt H s1 s2 : rational_unify_vt s1 x yt H = Some (s2, None)
                            -> rational_unification s1 (Var x) yt (Some s2)
| RUVarTermCont x yt H xt s1 s2 res : rational_unify_vt s1 x yt H = Some (s2, Some xt)
                                   -> rational_unification s2 xt yt res
                                   -> rational_unification s1 (Var x) yt res
| RUTermVar xt y s res : (forall x, xt <> Var x)
                      -> rational_unification s (Var y) xt res
                      -> rational_unification s xt (Var y) res
| RUCstCstFail c1 c2 s : c1 <> c2 -> rational_unification s (Cst c1) (Cst c2) None
| RUCstCstStop c s : rational_unification s (Cst c) (Cst c) (Some s)
| RUCstCon c f l r s : rational_unification s (Cst c) (Con f l r) None
| RUConCst c f l r s : rational_unification s (Con f l r) (Cst c) None
| RUConConFail f1 f2 l1 l2 r1 r2 s : f1 <> f2
                                  -> rational_unification s (Con f1 l1 r1) (Con f2 l2 r2) None
| RUConConContL f l1 l2 r1 r2 s : rational_unification s l1 l2 None
                               -> rational_unification s (Con f l1 r1) (Con f l2 r2) None
| RUConConContR f l1 l2 r1 r2 s1 s2 res : rational_unification s1 l1 l2 (Some s2)
                                       -> rational_unification s2 r1 r2 res
                                       -> rational_unification s1 (Con f l1 r1) (Con f l2 r2) res
.

Theorem rational_unification_correct s s' t1 t2 (H : rational_unification s t1 t2 (Some s'))
  : inf_min_unifying_extension (term_to_inf t1) (term_to_inf t2) (wf_eqsys_to_subst s) (wf_eqsys_to_subst s').
Proof.
  remember (Some s') as res. revert s' Heqres. induction H; intros; good_inversion Heqres.
  * apply wf_eqsys_union_prop' in H. apply H.
  * apply wf_eqsys_union_prop' in H. apply H. auto.
  * apply rational_unify_vt_prop' in H0. apply H0.
  * apply rational_unify_vt_prop' in H0. apply H0. auto.
  * apply inf_min_unifying_extension_sym. auto.
  * apply inf_min_unifying_extension_same. apply inf_unifier_refl.
  * edestruct IHrational_unification1 as [ [] ]. auto.
    edestruct IHrational_unification2 as [ [] ]. auto.
    constructor. constructor.
    - eapply inf_subst_more_general_trans; eauto.
    - unfold inf_unifier. rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
      apply inf_term_eq_con; auto. eapply inf_unifier_more_general; eauto.
    - intros ? []. unfold inf_unifier in H8. rewrite inf_term_step_prop in H8 at 1, H8. simpl in H8.
      apply H6. constructor. apply H3. constructor. auto.
      + eapply inf_term_eq_conl. eauto.
      + eapply inf_term_eq_conr. eauto.
Qed.

Corollary rational_unification_mgu s t1 t2 (H : rational_unification wf_eqsys_empty t1 t2 (Some s))
                                 : inf_mgu (term_to_inf t1) (term_to_inf t2) (wf_eqsys_to_subst s).
Proof. apply inf_min_unifying_extension_empty. apply rational_unification_correct in H. auto. Qed.

Theorem rational_unification_complete s s' t1 t2 (H1 : rational_unification s t1 t2 None)
  : ~inf_unifying_extension (term_to_inf t1) (term_to_inf t2) (wf_eqsys_to_subst s) s'.
Proof.
  remember None as res. revert Heqres. induction H1; intros; good_inversion Heqres.
  * apply wf_eqsys_union_prop' in H. intro. apply H in H0. eapply IHrational_unification; auto.
  * apply rational_unify_vt_prop' in H0. intros []. eapply H0; eauto.
  * apply rational_unify_vt_prop' in H0. intro. apply H0 in H2. eapply IHrational_unification; auto.
  * intro. eapply IHrational_unification. auto. apply inf_unifying_extension_sym. auto.
  * intros [ _ ]. edestruct (H0 Here) as [ ? [] ]. constructor. good_inversion H1.
    good_inversion H2. auto.
  * intros [ _ ]. edestruct (H Here) as [ ? [] ]. constructor. good_inversion H0. inversion H1.
  * intros [ _ ]. edestruct (H Here) as [ ? [] ]. constructor. good_inversion H0. inversion H1.
  * intros [ _ ]. edestruct (H0 Here) as [ ? [] ]. constructor. good_inversion H1.
    good_inversion H2. auto.
  * intros []. eapply IHrational_unification. auto. constructor. auto.
    unfold inf_unifier in H0. rewrite inf_term_step_prop in H0 at 1, H0.
    eapply inf_term_eq_conl. apply H0.
  * intros []. eapply IHrational_unification2. auto.
    unfold inf_unifier in H0. rewrite inf_term_step_prop in H0 at 1, H0.
    apply rational_unification_correct in H1_. destruct H1_ as [ [] ].
    constructor. apply H3. constructor. auto.
    - eapply inf_term_eq_conl. apply H0.
    - eapply inf_term_eq_conr. apply H0.
Qed.

Corollary rational_unification_complete' s t1 t2 (H : rational_unification wf_eqsys_empty t1 t2 None)
                                       : ~inf_unifier (term_to_inf t1) (term_to_inf t2) s.
Proof.
  eapply rational_unification_complete in H. intro. eapply H. constructor; eauto.
  apply inf_subst_more_general_empty.
Qed.

Lemma rational_unification_result_vars s s' t1 t2 z (H1 : rational_unification s t1 t2 (Some s'))
                                       (H2 : In z (eqsys_vars (wf_eqsys_get s')))
                                     : In z (eqsys_vars (wf_eqsys_get s))
                                    \/ In z (fv_term t1) \/ In z (fv_term t2).
Proof.
  remember (Some s') as res. revert s' H2 Heqres. induction H1; intros; good_inversion Heqres; auto.
  * apply wf_eqsys_union_prop' in H. apply H in H2. simpl. destruct H2 as [ | [ | ] ]; auto.
  * apply wf_eqsys_union_prop' in H. apply IHrational_unification in H2; auto.
    left. destruct H as [ _ [ _ [ _ [ ? [] ] ] ] ]. destruct H2 as [ | [ | ] ]; auto.
    - eapply eqsys_vars_in_rhs; eauto. apply eqsys_rhs_in. auto.
    - eapply eqsys_vars_in_rhs; eauto. apply eqsys_rhs_in. auto.
  * apply rational_unify_vt_prop' in H0. apply H0 in H2. simpl. destruct H2 as [ | [ | ] ]; auto.
  * apply rational_unify_vt_prop' in H0. apply IHrational_unification in H2; auto.
    destruct H0 as [ _ [ _ [ _ [ _ [ ? [ ? _ ] ] ] ] ] ]. destruct H2 as [ | [ | ] ]; auto.
    - apply H0 in H2. destruct H2; auto.
    - left. eapply eqsys_vars_in_rhs; eauto. apply eqsys_rhs_in. auto.
  * apply IHrational_unification in H2; auto. destruct H2 as [ | [ | ] ]; auto.
  * apply IHrational_unification2 in H2; auto. destruct H2 as [ | [ | ] ].
    apply IHrational_unification1 in H; auto; destruct H as [ | [ | ] ].
    auto. all: right.
    - left. apply ListSet.set_union_intro1. auto.
    - right. apply ListSet.set_union_intro1. auto.
    - left. apply ListSet.set_union_intro2. auto.
    - right. apply ListSet.set_union_intro2. auto.
Qed.

Definition rational_unification_system_size (xs : var_set) (s : wf_eqsys) : nat * nat :=
  ( eqsys_roots_num (wf_eqsys_get s) xs
  , eqsys_nonvar_size (wf_eqsys_get s)
  ).

Definition rational_unification_size_lt (x y : nat * nat) : Prop :=
  slexprod _ _ lt lt x y.

Lemma rational_unification_size_lt_lt x y z (H1 : rational_unification_size_lt x y)
                                      (H2 : rational_unification_size_lt y z)
                                    : rational_unification_size_lt x z.
Proof. good_inversion H1; good_inversion H2; try (left; lia). right. lia. Qed.

Lemma rational_unification_size_lt_well_founded : well_founded rational_unification_size_lt.
Proof. apply wf_slexprod; apply Wf_nat.lt_wf. Qed.

Definition rational_unification_size_le (x y : nat * nat) : Prop :=
  x = y \/ rational_unification_size_lt x y.

Lemma rational_unification_size_le_lt x y z (H1 : rational_unification_size_le x y)
                                      (H2 : rational_unification_size_lt y z)
                                    : rational_unification_size_lt x z.
Proof. destruct H1. subst. auto. eapply rational_unification_size_lt_lt; eauto. Qed.

Lemma rational_unification_size_lt_le x y z (H1 : rational_unification_size_lt x y)
                                      (H2 : rational_unification_size_le y z)
                                    : rational_unification_size_lt x z.
Proof. destruct H2. subst. auto. eapply rational_unification_size_lt_lt; eauto. Qed.

Lemma rational_unification_size_le_le x y z (H1 : rational_unification_size_le x y)
                                      (H2 : rational_unification_size_le y z)
                                    : rational_unification_size_le x z.
Proof. destruct H1. subst. auto. right. eapply rational_unification_size_lt_le; eauto. Qed.

Lemma rational_unification_size_le_split x y (H1 : fst x <= fst y) (H2 : snd x <= snd y)
                                       : rational_unification_size_le x y.
Proof.
  destruct x as [ x1 x2 ]. destruct y as [ y1 y2 ]. simpl in *.
  good_inversion H1. good_inversion H2. left. auto. all: right. right. lia. left. lia.
Qed.

Fixpoint rational_unification_income (t1 t2 : term) : nat :=
match t1, t2 with
| Var _, _ => term_nonvar_size t2
| _, Var _ => term_nonvar_size t1
| Cst _, _ => 1
| _, Cst _ => 1
| Con _ l1 r1, Con _ l2 r2 =>
  1 + rational_unification_income l1 l2 + rational_unification_income r1 r2
end.

Lemma rational_unification_income_sym t1 t2 : rational_unification_income t1 t2
                                            = rational_unification_income t2 t1.
Proof. revert t2. induction t1; intros; destruct t2; simpl; auto. Qed.

Lemma rational_unification_income_common_part t1 t2 t (H : is_common_part t1 t2 t)
                                            : rational_unification_income t1 t2 + term_nonvar_size t
                                            = term_nonvar_size t1 + term_nonvar_size t2.
Proof. induction H; simpl; try lia. rewrite rational_unification_income_sym. auto. Qed.

Definition rational_unification_size (xs : var_set) (s : wf_eqsys) (t1 t2 : term) : nat * nat :=
  ( eqsys_roots_num (wf_eqsys_get s) xs
  , eqsys_nonvar_size (wf_eqsys_get s) + rational_unification_income t1 t2
  ).

Record rational_unification_task : Set := RUTask {
  rational_unification_task_system : wf_eqsys ;
  rational_unification_task_left : term ;
  rational_unification_task_right : term ;
}.

Variant rational_unification_recursive_call (xs : var_set)
  : rational_unification_task -> rational_unification_task -> Prop :=
| RUUnionCall s1 s2 x y t1 t2
  : eqsys_roots_num (wf_eqsys_get s2) xs < eqsys_roots_num (wf_eqsys_get s1) xs
 -> rational_unification_recursive_call xs (RUTask s2 t1 t2) (RUTask s1 (Var x) (Var y))
| RUCommonPartCall s1 s2 x xt yt t
  : (forall x, xt <> Var x)
 -> (forall y, yt <> Var y)
 -> is_common_part xt yt t
 -> eqsys_roots_num (wf_eqsys_get s2) xs = eqsys_roots_num (wf_eqsys_get s1) xs
 -> eqsys_nonvar_size (wf_eqsys_get s2) + term_nonvar_size xt
  = eqsys_nonvar_size (wf_eqsys_get s1) + term_nonvar_size t
 -> rational_unification_recursive_call xs (RUTask s2 xt yt) (RUTask s1 (Var x) yt)
| RUSwapVarTermCall s y xt
  : (forall x, xt <> Var x)
 -> rational_unification_recursive_call xs (RUTask s (Var y) xt) (RUTask s xt (Var y))
| RULeftTermCall s f1 f2 l1 l2 r1 r2
  : rational_unification_recursive_call xs (RUTask s l1 l2) (RUTask s (Con f1 l1 r1) (Con f2 l2 r2))
| RURightTermCall s1 s2 f1 f2 l1 l2 r1 r2
  : rational_unification_size_le (rational_unification_system_size xs s2)
                                 (rational_unification_size xs s1 l1 l2)
 -> rational_unification_recursive_call xs (RUTask s2 r1 r2) (RUTask s1 (Con f1 l1 r1) (Con f2 l2 r2))
.

Lemma rational_unification_recursive_call_well_founded xs : well_founded (rational_unification_recursive_call xs).
Proof.
  set (P := fun size => forall s t1 t2, size = rational_unification_size xs s t1 t2
                                     -> Acc (rational_unification_recursive_call xs) (RUTask s t1 t2)).
  specialize well_founded_ind with (R := rational_unification_size_lt) (P := P). intro.
  intros [ s t1 t2 ]. eapply H; try reflexivity. apply rational_unification_size_lt_well_founded.
  clear s t1 t2 H. subst P. simpl. intros size IH.
  assert (forall s t1 t2, rational_unification_size_lt (rational_unification_size xs s t1 t2) size
                       -> Acc (rational_unification_recursive_call xs) (RUTask s t1 t2)). {
    intros. eapply IH; eauto.
  }
  clear IH. rename H into IH.
  assert (IHvar : forall s x yt, rational_unification_size_le (rational_unification_size xs s (Var x) yt) size
               -> Acc (rational_unification_recursive_call xs) (RUTask s (Var x) yt)). {
    intros s1 ? ? ?.
    assert (forall s t1 t2, rational_unification_size_lt (rational_unification_size xs s t1 t2)
                                                         (rational_unification_size xs s1 (Var x) yt)
                         -> Acc (rational_unification_recursive_call xs) (RUTask s t1 t2)). {
      intros. apply IH. eapply rational_unification_size_lt_le; eauto.
    }
    clear size IH H. rename H0 into IH.
    constructor. intros [ s2 t1' t2' ] H1. good_inversion H1.
    * apply IH. left. auto.
    * rename t1' into xt.
      assert (eqsys_nonvar_size (wf_eqsys_get s2) + rational_unification_income xt yt
            = eqsys_nonvar_size (wf_eqsys_get s1) + term_nonvar_size yt). {
        set (H' := H8). apply rational_unification_income_common_part in H'. lia.
      }
      clear H10. rename H into H10. good_inversion H8.
      - exfalso. eapply H6. auto.
      - exfalso. eapply H7. auto.
      - constructor. intros. inversion H.
      - clear H6 H7. constructor. intros. good_inversion H1.
        + apply IH. unfold rational_unification_size. rewrite H9. right. simpl in *. lia.
        + apply IH. destruct H4; good_inversion H1. 2: left; lia.
          all: unfold rational_unification_size; rewrite <- H9.
          1: rewrite H3. 2: rewrite H5. all: right; simpl in *; lia.
    * exfalso. eapply H0. auto.
  }
  intros s1 t1 t2 ?. subst size. destruct t1 as [ x | c1 | f1 l1 r1 ].
  * apply IHvar. left. auto.
  * constructor. intros. good_inversion H. apply IHvar. left. reflexivity.
  * constructor. intros. good_inversion H.
    - apply IHvar. left. reflexivity.
    - apply IH. right. simpl. lia.
    - apply IH. destruct H2; good_inversion H. 2: left; auto. all: unfold rational_unification_size.
      1: rewrite H1. 2: rewrite H3. all: right; simpl in *; lia.
Qed.

Definition rational_unification_result_size_le (xs : var_set) (s : wf_eqsys)
                                               (t1 t2 : term) (r : option wf_eqsys) : Prop :=
match r with
| None => True
| Some r => rational_unification_size_le (rational_unification_system_size xs r)
                                         (rational_unification_size xs s t1 t2)
end.

Lemma rational_unification_result_size_le_le xs s1 s2 r t1 t2 t1' t2'
    (H1 : rational_unification_size_le (rational_unification_size xs s1 t1' t2')
                                       (rational_unification_size xs s2 t1 t2))
    (H2 : rational_unification_result_size_le xs s1 t1' t2' r)
  : rational_unification_result_size_le xs s2 t1 t2 r.
Proof. destruct r as [ r | ]; auto. simpl in *. eapply rational_unification_size_le_le; eauto. Qed.

Record rational_unification_task_xs (s : wf_eqsys) (t1 t2 : term) (xs : var_set) : Prop := {
  rational_unification_task_xs_nodup : NoDup xs ;
  rational_unification_task_xs_system : incl (eqsys_vars (wf_eqsys_get s)) xs ;
  rational_unification_task_xs_left : incl (fv_term t1) xs ;
  rational_unification_task_xs_right : incl (fv_term t2) xs ;
}.

Definition rational_unification_exists_hlp (xs : var_set) (task : rational_unification_task) : Set :=
  let (s, t1, t2) := task in
  rational_unification_task_xs s t1 t2 xs -> { res | rational_unification s t1 t2 res
                                                  /\ rational_unification_result_size_le xs s t1 t2 res }.

Lemma rational_unification_exists_aux xs task
  (IH : forall rec, rational_unification_recursive_call xs rec task
                 -> rational_unification_exists_hlp xs rec)
: rational_unification_exists_hlp xs task.
Proof.
  destruct task as [ s t1 t2 ]. simpl. intros.
  destruct t1 as [ x | c1 | f1 l1 r1 ]; destruct t2 as [ y | c2 | f2 l2 r2 ].
  * remember (wf_eqsys_union s x y) as res. symmetry in Heqres.
    set (H1 := Heqres). apply wf_eqsys_union_prop' in H1. destruct res as [ s' [ [ t1 t2 ] | ] ].
    - destruct H1 as [ _ [ _ [] ] ]. specialize (IH (RUTask s' t1 t2)). simpl in IH.
      assert (eqsys_roots_num (wf_eqsys_get s') xs < eqsys_roots_num (wf_eqsys_get s) xs). {
        rewrite H0. lia. apply H. intros z ?. apply H. apply eqsys_vars_in_dom.
        apply eqsys_dom_spec. auto.
      }
      destruct IH as [ res [] ].
      + apply RUUnionCall. auto.
      + constructor. apply H. all: destruct H as [ _ H _ _ ].
        ** intros z ?. apply H. apply H1. auto.
        ** intros z ?. apply H. eapply eqsys_vars_in_rhs; eauto. apply eqsys_rhs_in. apply H1.
        ** intros z ?. apply H. eapply eqsys_vars_in_rhs; eauto. apply eqsys_rhs_in. apply H1.
      + exists res. constructor. eapply RUVarVarCont; eauto. destruct res as [ res | ]; auto.
        eapply rational_unification_result_size_le_le; eauto. right. left. auto.
    - exists (Some s'). constructor. apply RUVarVarStop. auto. simpl.
      apply rational_unification_size_le_split; simpl. apply H1.
      5: rewrite PeanoNat.Nat.add_0_r; apply H1. apply H.
      + destruct H as [ _ _ H _ ]. apply H. left. auto.
      + destruct H as [ _ _ _ H ]. apply H. left. auto.
      + apply H.
  * set (yt := Cst c2). assert (Hy : forall y, yt <> Var y). intros ? ?. inversion H0.
    remember (rational_unify_vt s x yt Hy) as res. symmetry in Heqres.
    set (H1 := Heqres). eapply rational_unify_vt_prop' in H1. destruct res as [ [ s' [ xt | ] ] | ].
    - destruct H1 as [ _ [ _ [ ? [ ? [ ? [] ] ] ] ] ].
      assert (eqsys_roots_num (wf_eqsys_get s') xs = eqsys_roots_num (wf_eqsys_get s) xs). {
        apply H0. apply H. 2: apply H. destruct H as [ _ _ H _ ]. apply H. left. auto.
      }
      clear H0. specialize (IH (RUTask s' xt yt)). simpl in IH. destruct IH as [ res [] ].
      + destruct H1 as [ t [] ]. eapply RUCommonPartCall; eauto.
      + constructor. 1, 4: apply H.
        ** intros z ?. apply H2 in H0. destruct H0; apply H in H0; auto.
        ** intros z ?. apply H. eapply eqsys_vars_in_rhs; eauto. apply eqsys_rhs_in. auto.
      + exists res. constructor. eapply RUVarTermCont; eauto.
        eapply rational_unification_result_size_le_le; eauto.
        apply rational_unification_size_le_split; simpl. lia. destruct H1 as [ t [] ].
        apply rational_unification_income_common_part in H1. simpl in *. lia.
    - exists (Some s'). constructor. eapply RUVarTermStop. eauto.
      destruct H1 as [ _ [] ]. apply rational_unification_size_le_split; simpl in *; try lia.
      rewrite H0. reflexivity. 1, 3: apply H. destruct H as [ _ _ H _ ]. apply H. left. auto.
    - exists None. constructor; simpl; auto. eapply RUVarTermFail. eauto.
  * set (yt := Con f2 l2 r2). assert (Hy : forall y, yt <> Var y). intros ? ?. inversion H0.
    remember (rational_unify_vt s x yt Hy) as res. symmetry in Heqres.
    set (H1 := Heqres). eapply rational_unify_vt_prop' in H1. destruct res as [ [ s' [ xt | ] ] | ].
    - destruct H1 as [ _ [ _ [ ? [ ? [ ? [] ] ] ] ] ].
      assert (eqsys_roots_num (wf_eqsys_get s') xs = eqsys_roots_num (wf_eqsys_get s) xs). {
        apply H0. apply H. 2: apply H. destruct H as [ _ _ H _ ]. apply H. left. auto.
      }
      clear H0. specialize (IH (RUTask s' xt yt)). simpl in IH. destruct IH as [ res [] ].
      + destruct H1 as [ t [] ]. eapply RUCommonPartCall; eauto.
      + constructor. 1, 4: apply H.
        ** intros z ?. apply H2 in H0. destruct H0; apply H in H0; auto.
        ** intros z ?. apply H. eapply eqsys_vars_in_rhs; eauto. apply eqsys_rhs_in. auto.
      + exists res. constructor. eapply RUVarTermCont; eauto.
        eapply rational_unification_result_size_le_le; eauto.
        apply rational_unification_size_le_split; simpl. lia. destruct H1 as [ t [] ].
        apply rational_unification_income_common_part in H1. simpl in *. lia.
    - exists (Some s'). constructor. eapply RUVarTermStop. eauto.
      destruct H1 as [ _ [] ]. apply rational_unification_size_le_split; simpl in *; try lia.
      rewrite H0. reflexivity. 1, 3: apply H. destruct H as [ _ _ H _ ]. apply H. left. auto.
    - exists None. constructor; simpl; auto. eapply RUVarTermFail. eauto.
  * set (xt := Cst c1). assert (Hx : forall x, xt <> Var x). intros ? ?. inversion H0.
    specialize (IH (RUTask s (Var y) xt)). destruct IH as [ res [] ].
    - apply RUSwapVarTermCall; auto.
    - constructor; apply H.
    - exists res. constructor; auto. apply RUTermVar; auto.
  * destruct (name_eq_dec c1 c2) as [ H1 | H1 ].
    - subst c2. exists (Some s). constructor. apply RUCstCstStop. right. right. simpl. lia.
    - exists None. constructor; simpl; auto. apply RUCstCstFail. auto.
  * exists None. constructor; simpl; auto. apply RUCstCon.
  * set (xt := Con f1 l1 r1). assert (Hx : forall x, xt <> Var x). intros ? ?. inversion H0.
    specialize (IH (RUTask s (Var y) xt)). destruct IH as [ res [] ].
    - apply RUSwapVarTermCall; auto.
    - constructor; apply H.
    - exists res. constructor; auto. apply RUTermVar; auto.
  * exists None. constructor; simpl; auto. apply RUConCst.
  * destruct (name_eq_dec f1 f2) as [ H1 | H1 ]. subst f2. 2: {
      exists None. constructor; simpl; auto. apply RUConConFail. auto.
    }
    edestruct (IH (RUTask s l1 l2)) as [ [ s2 | ] [] ]. 4: {
      exists None. constructor; auto. apply RUConConContL. auto.
    }
    3: edestruct (IH (RUTask s2 r1 r2)) as [ res [] ]. 5: {
      exists res. constructor. eapply RUConConContR; eauto.
      eapply rational_unification_result_size_le_le; eauto.
      destruct H1; good_inversion H1. 2: right; left; auto.
      all: unfold rational_unification_size. 1: rewrite H5. 2: rewrite H7.
      all: right; right; simpl; lia.
    }
    - apply RULeftTermCall; auto.
    - constructor; try apply H.
      + intros z ?. destruct H as [ _ _ H _ ]. apply H. apply ListSet.set_union_intro1. auto.
      + intros z ?. destruct H as [ _ _ _ H ]. apply H. apply ListSet.set_union_intro1. auto.
    - apply RURightTermCall. apply H1.
    - constructor. apply H.
      + intros z ?. eapply rational_unification_result_vars in H0; eauto. clear H2.
        destruct H0 as [ | [ | ] ]. apply H in H0. auto.
        ** destruct H as [ _ _ H _ ]. apply H. apply ListSet.set_union_intro1. auto.
        ** destruct H as [ _ _ _ H ]. apply H. apply ListSet.set_union_intro1. auto.
      + intros z ?. destruct H as [ _ _ H _ ]. apply H. apply ListSet.set_union_intro2. auto.
      + intros z ?. destruct H as [ _ _ _ H ]. apply H. apply ListSet.set_union_intro2. auto.
Qed.

Theorem rational_unification_exists s t1 t2 : { res | rational_unification s t1 t2 res }.
Proof.
  set (xs := var_set_union (var_set_union (fv_term t1) (fv_term t2)) (eqsys_vars (wf_eqsys_get s))).
  specialize (rational_unification_exists_aux xs). intro.
  apply well_founded_induction with (a := RUTask s t1 t2) in H.
  2: apply rational_unification_recursive_call_well_founded.
  edestruct H as [ r [] ]. 2: exists r; auto. constructor.
  * apply ListSet.set_union_nodup. apply ListSet.set_union_nodup; apply fv_term_nodup.
    apply eqsys_vars_nodup.
  * intros x ?. apply ListSet.set_union_intro2. auto.
  * intros x ?. apply ListSet.set_union_intro1. apply ListSet.set_union_intro1. auto.
  * intros x ?. apply ListSet.set_union_intro1. apply ListSet.set_union_intro2. auto.
Qed.
