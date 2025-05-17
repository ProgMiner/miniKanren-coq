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
Require Import RationalTree.


(* Utils *)

Lemma NoDup_length [A] (xs ys : list A) (H1 : NoDup xs) (H2 : NoDup ys)
                   (H : forall a, In a xs <-> In a ys)
                 : length xs = length ys.
Proof. apply Nat.le_antisymm; apply NoDup_incl_length; auto; intros a H'; apply H; auto. Qed.

Fixpoint first_nats (k : nat) : list nat :=
match k with
| 0 => []
| S n => n :: first_nats n
end.

Lemma first_nats_prop (i k : nat) : In i (first_nats k) <-> i < k.
Proof.
  induction k; constructor; intro; good_inversion H.
  * lia.
* apply IHk in H0. lia.
  * left. auto.
  * right. apply IHk. lia.
Qed.

Lemma max_either n m : max n m = n \/ max n m = m.
Proof. destruct (PeanoNat.Nat.max_spec n m) as [ [ _ H ] | [ _ H ] ]; auto. Qed.

(* more convenient for induction than [height] *)
Fixpoint term_height (t : term) : nat :=
match t with
| Con _ l r => S (max (term_height l) (term_height r))
| _ => 0
end.

Definition terms_height (ts : terms) : nat := max (term_height (fst ts)) (term_height (snd ts)).

Definition terms_height_less (ts1 ts2 : terms) : Prop := terms_height ts1 < terms_height ts2.

Lemma terms_height_less_wf : well_founded terms_height_less.
Proof.
  intro ts. remember (terms_height ts) as h. symmetry in Heqh.
  generalize dependent ts. induction h; intros; destruct ts as [ t1 t2 ].
  * destruct t1; destruct t2; good_inversion Heqh; constructor; intros; inversion H.
  * destruct t1 as [ x | n1 | n1 l1 r1 ]; destruct t2 as [ y | n2 | n2 l2 r2 ];
      good_inversion Heqh; constructor; intros [ t1 t2 ] H;
      (good_inversion H; [ apply IHh; auto | ]).
    1, 2: destruct (IHh (l2, r2)); auto.
    1, 2: destruct (IHh (l1, r1)); auto.
    destruct (max_either (max (term_height l1) (term_height r1))
                         (max (term_height l2) (term_height r2)));
      rewrite H in *; clear H.
    - destruct (IHh (l1, r1)); auto.
    - destruct (IHh (l2, r2)); auto.
Qed.

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


(* Equation System *)

Variant term_head : Set :=
| CstHead : name -> term_head
| ConHead : name -> name -> name -> term_head
.

Definition term_head_to_term (t : term_head) : term :=
match t with
| CstHead n => Cst n
| ConHead n x y => Con n (Var x) (Var y)
end.

Definition fv_term_head (t : term_head) : var_set :=
match t with
| CstHead _ => var_set_empty
| ConHead _ n1 n2 => var_set_add n2 (var_set_add n1 var_set_empty)
end.

Lemma fv_term_head_prop t : fv_term_head t = fv_term (term_head_to_term t).
Proof. destruct t; auto. Qed.

Variant eq_sys_node : Set :=
| RootESNode : term_head -> eq_sys_node
| LinkESNode : name -> eq_sys_node
.

Definition eq_sys := list (name * eq_sys_node).

Definition eq_sys_trivial : eq_sys := [].

Fixpoint eq_sys_lookup (s : eq_sys) (n : name) : option eq_sys_node :=
match s with
| [] => None
| (n', node) :: s =>
  if name_eq_dec n n' then Some node
  else eq_sys_lookup s n
end.

Lemma eq_sys_lookup_extend s n n' node (H1 : n <> n')
                         : eq_sys_lookup ((n', node) :: s) n = eq_sys_lookup s n.
Proof. simpl. destruct (name_eq_dec n n'). contradiction. auto. Qed.

Fixpoint eq_sys_dom (s : eq_sys) : var_set :=
match s with
| [] => var_set_empty
| (n, _) :: s => var_set_add n (eq_sys_dom s)
end.

Lemma eq_sys_dom_distinct (s : eq_sys) : NoDup (eq_sys_dom s).
Proof. induction s as [ | [ n node ] s ]. constructor. simpl. apply set_add_nodup. auto. Qed.

Local Hint Resolve eq_sys_dom_distinct : core.

Definition eq_sys_dom' (s : eq_sys) : list name := map fst s.

Lemma eq_sys_dom'_prop (s : eq_sys) n : In n (eq_sys_dom s) <-> In n (eq_sys_dom' s).
Proof.
  induction s as [ | [ n' node' ] s ]; constructor; intro; auto; simpl in *.
  * apply set_add_elim in H. destruct H. left. auto. right. apply IHs. auto.
  * apply set_add_iff. destruct H. left. auto. right. apply IHs. auto.
Qed.

Lemma eq_sys_dom'_size (s : eq_sys) : var_set_size (eq_sys_dom' s) = length s.
Proof. apply length_map. Qed.

Lemma eq_sys_dom_size (s : eq_sys) : var_set_size (eq_sys_dom s) <= length s.
Proof.
  rewrite <- eq_sys_dom'_size. apply NoDup_incl_length. auto.
  intro. apply eq_sys_dom'_prop.
Qed.

Lemma eq_sys_dom_size_prop ns s (H1 : NoDup ns) (H2 : incl ns (eq_sys_dom s))
                         : length ns <= length s.
Proof. etransitivity; try apply eq_sys_dom_size. apply NoDup_incl_length; auto. Qed.

Definition in_eq_sys_dom (n : name) (s : eq_sys) : Prop :=
  exists node, eq_sys_lookup s n = Some node.

Lemma in_eq_sys_dom_inv n s : ~in_eq_sys_dom n s <-> eq_sys_lookup s n = None.
Proof.
  constructor; intro.
  * unfold in_eq_sys_dom in H. destruct (eq_sys_lookup s n); auto.
    exfalso. apply H. eexists. auto.
  * intro. destruct H0. rewrite H in H0. inversion H0.
Qed.

Lemma in_eq_sys_dom_prop n s : in_eq_sys_dom n s <-> In n (eq_sys_dom s).
Proof.
  induction s as [ | [ n' node' ] s ].
  * constructor; intro; destruct H; inversion H.
  * constructor; intro.
    - destruct H as [ node H ]. simpl in *. apply set_add_iff. destruct (name_eq_dec n n').
      good_inversion H. left. auto. right. apply IHs. eexists. eauto.
    - unfold in_eq_sys_dom. simpl in *. destruct (name_eq_dec n n'). eauto.
      apply set_add_elim in H. destruct H; try contradiction. apply IHs. auto.
Qed.

Lemma in_eq_sys_dom_prop' n s : ~in_eq_sys_dom n s <-> ~In n (eq_sys_dom s).
Proof. constructor; intro; intro; apply H; apply in_eq_sys_dom_prop; auto. Qed.

Definition eq_sys_dom_erase (s : eq_sys) n :=
  filter (fun eq => if name_eq_dec (fst eq) n then false else true) s.

Lemma eq_sys_dom_erase_prop s n x : In x (eq_sys_dom (eq_sys_dom_erase s n))
                                <-> In x (var_set_remove n (eq_sys_dom s)).
Proof.
  constructor; intro.
  * apply eq_sys_dom'_prop in H. apply in_map_iff in H. destruct H as [ [ n' node' ] [ H1 H2 ] ].
    simpl in *. subst. apply filter_In in H2. destruct H2. revert H0. simpl.
    destruct (name_eq_dec x n). intro. inversion H0. rename n0 into H1. intro. clear H0.
    apply set_remove_iff; auto. constructor; auto. apply eq_sys_dom'_prop. apply in_map_iff.
    exists (x, node'). constructor; auto.
  * apply set_remove_iff in H; auto. destruct H. apply eq_sys_dom'_prop in H. apply in_map_iff in H.
    destruct H as [ [ n' node' ] [ H1 H2 ] ]. simpl in *. subst. apply eq_sys_dom'_prop.
    apply in_map_iff. exists (x, node'). constructor; auto. apply filter_In. constructor; auto.
    simpl. destruct (name_eq_dec x n); auto.
Qed.

Lemma eq_sys_dom_erase_size s n (H : in_eq_sys_dom n s)
                          : var_set_size (eq_sys_dom s)
                          = S (var_set_size (eq_sys_dom (eq_sys_dom_erase s n))).
Proof.
  refine (_ : _ = length (n :: (eq_sys_dom (eq_sys_dom_erase s n)))).
  apply in_eq_sys_dom_prop in H. apply NoDup_length. auto. apply NoDup_cons; auto.
  intro. apply eq_sys_dom_erase_prop in H0. apply set_remove_iff in H0; auto. destruct H0. auto.
  intro n'. constructor; intro Hn'.
  * destruct (name_eq_dec n n'). left. auto.
    right. apply eq_sys_dom_erase_prop. apply set_remove_iff; auto.
  * good_inversion Hn'. auto. apply eq_sys_dom_erase_prop in H0.
    apply set_remove_iff in H0; auto. apply H0.
Qed.

Lemma eq_sys_dom_erase_lookup s n1 n2 (H : n1 <> n2)
                            : eq_sys_lookup (eq_sys_dom_erase s n1) n2
                            = eq_sys_lookup s n2.
Proof.
  induction s as [ | [ n' node' ] s ]. auto. simpl. destruct (name_eq_dec n' n1).
  * subst. destruct (name_eq_dec n2 n1); auto. exfalso. auto.
  * simpl. destruct (name_eq_dec n2 n'); auto.
Qed.

Lemma eq_sys_dom_erase_no s n (H : ~in_eq_sys_dom n s) : eq_sys_dom_erase s n = s.
Proof.
  apply forallb_filter_id. apply forallb_forall. intros [ n' node ] H0. simpl.
  destruct (name_eq_dec n' n); auto. subst. exfalso. apply H.
  assert (In n (eq_sys_dom' s)). apply in_map_iff. eexists. constructor; eauto. auto.
  apply eq_sys_dom'_prop in H1. apply in_eq_sys_dom_prop. auto.
Qed.

Lemma eq_sys_dom_erase_extend_lookup s n n' node (H : eq_sys_lookup s n = Some node)
                                   : eq_sys_lookup ((n, node) :: eq_sys_dom_erase s n) n'
                                   = eq_sys_lookup s n'.
Proof.
  simpl. destruct (name_eq_dec n' n). subst. auto.
  apply eq_sys_dom_erase_lookup. auto.
Qed.

Definition eq_sys_dom_erase' := fold_right (fun n s => eq_sys_dom_erase s n).

Lemma eq_sys_dom_erase'_prop s ns n
                           : In n (eq_sys_dom (eq_sys_dom_erase' s ns))
                         <-> In n (eq_sys_dom s) /\ ~In n ns.
Proof.
  induction ns as [ | n' ns ]; intros; constructor; intro.
  * constructor; auto.
  * apply H.
  * apply eq_sys_dom_erase_prop in H. apply set_remove_iff in H; auto. destruct H. apply IHns in H.
    destruct H. constructor; auto. intro. destruct H2; auto.
  * destruct H. apply eq_sys_dom_erase_prop. apply set_remove_iff; auto. constructor; auto.
    apply IHns. constructor; auto. intro. apply H0. right. auto. intro. apply H0. left. auto.
Qed.

Definition in_eq_sys_rhs (t : term_head) (s : eq_sys) : Prop :=
  exists n, eq_sys_lookup s n = Some (RootESNode t).

Definition in_eq_sys_rhs_vars (n : name) (s : eq_sys) : Prop :=
  exists t, in_eq_sys_rhs t s /\ In n (fv_term_head t).

Lemma in_eq_sys_rhs_vars_add_root s n1 n2 t (H : in_eq_sys_rhs_vars n1 ((n2, RootESNode t) :: s))
                                : in_eq_sys_rhs_vars n1 s \/ In n1 (fv_term_head t).
Proof.
  destruct H as [ t' [ [ n1' H1 ] H2 ] ]. simpl in H1. destruct (name_eq_dec n1' n2).
  good_inversion H1. auto. left. exists t'. constructor; auto. eexists. eauto.
Qed.

Lemma in_eq_sys_rhs_vars_add_link s x y z (H : in_eq_sys_rhs_vars z ((x, LinkESNode y) :: s))
                                : in_eq_sys_rhs_vars z s.
Proof.
  destruct H as [ t [ [ z' H1 ] H2 ] ]. exists t. constructor; auto.
  exists z'. simpl in H1. destruct (name_eq_dec z' x). inversion H1. auto.
Qed.

Definition in_eq_sys_links (n : name) (s : eq_sys) : Prop :=
  exists n', eq_sys_lookup s n' = Some (LinkESNode n).

Lemma in_eq_sys_links_add_root s n1 n2 t (H : in_eq_sys_links n1 ((n2, RootESNode t) :: s))
                             : in_eq_sys_links n1 s.
Proof.
  destruct H as [ n1' H ]. simpl in H. destruct (name_eq_dec n1' n2).
  inversion H. exists n1'. auto.
Qed.

Lemma in_eq_sys_links_add_link s x y z (H : in_eq_sys_links z ((x, LinkESNode y) :: s))
                             : in_eq_sys_links z s \/ z = y.
Proof.
  destruct H as [ z' H ]. simpl in H. destruct (name_eq_dec z' x).
  good_inversion H. auto. left. exists z'. auto.
Qed.

(* Set of equation system variables is a set of all variables the system built on:
 * - Variables of domain
 * - Variables linking to from other variables
 * - Variables from terms of image
 *)
Definition in_eq_sys_vars (n : name) (s : eq_sys) : Prop :=
  in_eq_sys_dom n s \/ in_eq_sys_rhs_vars n s \/ in_eq_sys_links n s.

Lemma in_eq_sys_vars_add_root s n1 n2 t (H : in_eq_sys_vars n1 ((n2, RootESNode t) :: s))
                     : in_eq_sys_vars n1 s \/ n1 = n2 \/ In n1 (fv_term_head t).
Proof.
  destruct H as [ H | [ H | H ] ].
  * apply in_eq_sys_dom_prop in H. apply set_add_elim in H. destruct H. auto.
    apply in_eq_sys_dom_prop in H. left. left. auto.
  * apply in_eq_sys_rhs_vars_add_root in H. destruct H; auto. left. right. auto.
  * apply in_eq_sys_links_add_root in H. left. right. auto.
Qed.

Lemma in_eq_sys_vars_add_link s x y z (H : in_eq_sys_vars z ((x, (LinkESNode y)) :: s))
                            : in_eq_sys_vars z s \/ z = x \/ z = y.
Proof.
  destruct H as [ H | [ H | H ] ].
  * apply in_eq_sys_dom_prop in H. apply set_add_elim in H. destruct H. auto.
    apply in_eq_sys_dom_prop in H. left. left. auto.
  * apply in_eq_sys_rhs_vars_add_link in H. left. right. auto.
  * apply in_eq_sys_links_add_link in H. destruct H; auto. left. right. auto.
Qed.

Definition in_eq_sys_vran (n : name) (s : eq_sys) : Prop :=
  ~in_eq_sys_dom n s /\ (in_eq_sys_rhs_vars n s \/ in_eq_sys_links n s).

Inductive eq_sys_name_wf s : name -> var_set -> Prop :=
| RootESNameWF n t : eq_sys_lookup s n = Some (RootESNode t) -> eq_sys_name_wf s n [n]
| FreeESNameWF n : eq_sys_lookup s n = None -> eq_sys_name_wf s n [n]
| LinkESNameWF n n' p : eq_sys_lookup s n = Some (LinkESNode n')
                     -> eq_sys_name_wf s n' p -> eq_sys_name_wf s n (n::p)
.

Lemma eq_sys_name_wf_ext s1 s2 n p (H1 : eq_sys_name_wf s1 n p)
                         (H2 : forall n, eq_sys_lookup s1 n = eq_sys_lookup s2 n)
                       : eq_sys_name_wf s2 n p.
Proof.
  induction H1; rewrite H2 in H.
  * econstructor. eauto.
  * constructor. auto.
  * econstructor. eauto. auto.
Qed.

Lemma eq_sys_name_wf_func s n p1 p2 (H1 : eq_sys_name_wf s n p1) (H2 : eq_sys_name_wf s n p2)
                        : p1 = p2.
Proof.
  generalize dependent p2.
  induction H1; intros; good_inversion H2; auto; rewrite H0 in H; good_inversion H.
  f_equal. apply IHeq_sys_name_wf. auto.
Qed.

Lemma eq_sys_name_wf_cut s n p n' (H1 : In n' p) (H2 : eq_sys_name_wf s n p)
                       : exists p1 p2, p = p1 ++ n' :: p2 /\ eq_sys_name_wf s n' (n'::p2).
Proof.
  generalize dependent n'. induction H2; intros; (good_inversion H1; [ | try inversion H0 ]).
  * exists []. exists []. repeat econstructor. eauto.
  * exists []. exists []. repeat constructor. auto.
  * exists []. exists p. repeat econstructor; eauto.
  * apply IHeq_sys_name_wf in H0. destruct H0 as [ p1 [ p2 [ H0 H1 ] ] ]. subst.
    exists (n::p1). exists p2. constructor; auto.
Qed.

Lemma eq_sys_name_wf_nonrec s n p (H : eq_sys_name_wf s n p) : NoDup p.
Proof.
  induction H; constructor; auto; try constructor.
  intro. eapply eq_sys_name_wf_cut in H1; eauto. destruct H1 as [ p1 [ p2 [ H1 H2 ] ] ].
  assert (Hp : n::p2 = n::p). eapply eq_sys_name_wf_func; eauto. econstructor; eauto.
  good_inversion Hp. specialize (app_assoc p1 [n] p2). simpl. intro. rewrite H1 in H4.
  apply (app_inv_tail_iff p2 []) in H4.
  assert (In n (p1 ++ [n])). apply in_app_iff. right. constructor. auto.
  rewrite <- H4 in H3. inversion H3.
Qed.

Lemma eq_sys_name_wf_nonloop s n p (H : eq_sys_name_wf s n p)
                           : eq_sys_lookup s n <> Some (LinkESNode n).
Proof.
  intro. set (H' := H).
  good_inversion H'; rewrite H1 in H0; good_inversion H0. apply eq_sys_name_wf_nonrec in H.
  good_inversion H2; rewrite H0 in H1; good_inversion H1. good_inversion H. apply H4. left. auto.
Qed.

Lemma eq_sys_name_wf_in_dom s n p n' (H1 : eq_sys_name_wf s n p) (H2 : In n' p)
                          : in_eq_sys_dom n' s \/ ~in_eq_sys_dom n' s
                                               /\ exists p', p = p' ++ [n'].
Proof.
  induction H1; good_inversion H2. 2, 4: inversion H0. 1, 3: left; eexists; eauto.
  * right; constructor. apply in_eq_sys_dom_inv. auto. exists []. auto.
  * apply IHeq_sys_name_wf in H0. destruct H0; auto.
    right. destruct H0 as [ H0 [ p' H2 ] ]. constructor; auto.
    exists (n::p'). rewrite H2. auto.
Qed.

Lemma eq_sys_name_wf_add_root1 s n1 n2 t p (H : eq_sys_name_wf s n1 p)
                             : exists p', eq_sys_name_wf ((n2, RootESNode t) :: s) n1 p'.
Proof.
  induction H; remember (name_eq_dec n n2) as dec; symmetry in Heqdec; destruct dec; subst.
  1, 3, 5: eexists; econstructor; simpl; rewrite Heqdec; eauto.
  * eexists. econstructor. simpl. rewrite Heqdec. eauto.
  * eexists. constructor. simpl. rewrite Heqdec. auto.
  * destruct IHeq_sys_name_wf as [ p' H1 ]. exists (n::p'). econstructor; eauto. simpl.
    rewrite Heqdec. auto.
Qed.

Lemma eq_sys_name_wf_add_root2 s n1 n2 t p (H : eq_sys_name_wf s n1 (p ++ [n2]))
                             : eq_sys_name_wf ((n2, RootESNode t) :: s) n1 (p ++ [n2]).
Proof.
  remember (p ++ [n2]) as p'. symmetry in Heqp'. generalize dependent p.
  induction H; intros; remember (name_eq_dec n n2) as dec; symmetry in Heqdec; destruct dec; subst.
  * econstructor. simpl. rewrite Heqdec. eauto.
  * econstructor. simpl. rewrite Heqdec. eauto.
  * econstructor. simpl. rewrite Heqdec. eauto.
  * constructor. simpl. rewrite Heqdec. eauto.
  * destruct p0 as [ | n p0 ]; good_inversion Heqp'. good_inversion H0.
    absurd (NoDup (n2 :: p0 ++ [n2])). intro. good_inversion H1. apply H4.
    apply in_app_iff. right. left. auto.
    eapply eq_sys_name_wf_nonrec. econstructor. eauto. eauto.
  * destruct p0 as [ | n1 p0 ]; good_inversion Heqp'. good_inversion H0.
    econstructor. simpl. rewrite Heqdec. eauto. eapply IHeq_sys_name_wf. auto.
Qed.

Lemma eq_sys_name_wf_add_root3 s n1 n2 t p (H1 : eq_sys_name_wf s n1 p) (H2 : ~In n2 p)
                             : eq_sys_name_wf ((n2, RootESNode t) :: s) n1 p.
Proof.
  induction H1.
  * econstructor. simpl. destruct (name_eq_dec n n2). exfalso. apply H2. left. auto. eauto.
  * constructor. simpl. destruct (name_eq_dec n n2). exfalso. apply H2. left. auto. auto.
  * econstructor. simpl. destruct (name_eq_dec n n2). exfalso. apply H2. left. auto. eauto.
    apply IHeq_sys_name_wf. intro. apply H2. right. auto.
Qed.

Lemma eq_sys_name_wf_add_link1 s n1 n2 n p (H1 : eq_sys_name_wf s n p) (H2 : ~In n1 p)
                             : eq_sys_name_wf ((n1, LinkESNode n2) :: s) n p.
Proof.
  induction H1.
  * econstructor. simpl. destruct (name_eq_dec n n1); eauto. exfalso. apply H2. left. auto.
  * constructor. simpl. destruct (name_eq_dec n n1); auto. exfalso. apply H2. left. auto.
  * econstructor. simpl. destruct (name_eq_dec n n1). exfalso. apply H2. left. auto. eauto.
    apply IHeq_sys_name_wf. intro. apply H2. right. auto.
Qed.

Lemma eq_sys_name_wf_add_link2 s n1 n2 n p p2 (H1 : ~In n1 p2)
                               (H2 : eq_sys_name_wf s n p) (H3 : eq_sys_name_wf s n2 p2)
                             : exists p', eq_sys_name_wf ((n1, LinkESNode n2) :: s) n p'.
Proof.
  induction H2; remember (name_eq_dec n n1) as dec; symmetry in Heqdec; destruct dec; subst.
  1, 3, 5: exists (n1::p2); econstructor;
    [ simpl; rewrite Heqdec
    | apply eq_sys_name_wf_add_link1
    ]; auto.
  * exists [n]. econstructor. simpl. rewrite Heqdec. eauto.
  * exists [n]. constructor. simpl. rewrite Heqdec. auto.
  * destruct IHeq_sys_name_wf as [ p' IH ]. exists (n::p'). econstructor; eauto.
    simpl. rewrite Heqdec. auto.
Qed.

Lemma eq_sys_name_wf_add_link3 s n n1 n2 p1 p2
                               (H1 : eq_sys_name_wf s n (p1 ++ [n1]))
                               (H2 : eq_sys_name_wf ((n1, LinkESNode n2) :: s) n2 p2)
                             : eq_sys_name_wf ((n1, LinkESNode n2) :: s) n (p1 ++ n1 :: p2).
Proof.
  remember (p1 ++ [n1]) as p. generalize dependent p1. induction H1; intros.
  * apply (app_inj_tail []) in Heqp. destruct Heqp. subst. econstructor. simpl.
    destruct (name_eq_dec n1 n1). auto. contradiction. auto.
  * apply (app_inj_tail []) in Heqp. destruct Heqp. subst. econstructor. simpl.
    destruct (name_eq_dec n1 n1). auto. contradiction. auto.
  * destruct p1 as [ | n'' p1' ].
    destruct p as [ | n1'' p1'' ]. good_inversion Heqp. inversion H1. inversion Heqp.
    good_inversion Heqp. remember (name_eq_dec n'' n1) as dec. symmetry in Heqdec. destruct dec.
    - absurd (NoDup (n1 :: p1' ++ [n1])).
      intro. good_inversion H0. apply H5. apply in_app_iff. right. left. auto.
      eapply eq_sys_name_wf_nonrec. econstructor. subst. eauto. eauto.
    - econstructor. simpl. rewrite Heqdec. eauto. apply IHeq_sys_name_wf. auto.
Qed.

Lemma eq_sys_name_wf_extend s n1 n2 node p (H1 : eq_sys_name_wf s n1 p) (H2 : ~In n2 p)
                          : eq_sys_name_wf ((n2, node) :: s) n1 p.
Proof.
  destruct node as [ t | n2' ].
  apply eq_sys_name_wf_add_root3; auto.
  apply eq_sys_name_wf_add_link1; auto.
Qed.

Lemma eq_sys_name_wf_len1 s n p (H : eq_sys_name_wf s n p)
                        : var_set_size p <= length s
                       \/ var_set_size p <= S (length s)
                       /\ exists p' n', p = p' ++ [n'] /\ ~in_eq_sys_dom n' s.
Proof.
  destruct (@exists_last _ p) as [ p' [ n' H1 ] ]; auto. good_inversion H; intro; inversion H.
  destruct (in_dec name_eq_dec n' (eq_sys_dom s)).
  * left. apply eq_sys_dom_size_prop. eapply eq_sys_name_wf_nonrec. eauto.
    intros n1 Hn1. eapply eq_sys_name_wf_in_dom in Hn1; eauto. destruct Hn1.
    - apply in_eq_sys_dom_prop. auto.
    - destruct H0. destruct H2 as [ p1 H2 ]. rewrite H2 in H1. apply app_inj_tail in H1.
      destruct H1. subst. auto.
  * right. constructor.
    - refine (_ : _ <= length ((n', RootESNode (CstHead 0)) :: s)).
      apply eq_sys_dom_size_prop. eapply eq_sys_name_wf_nonrec. eauto.
      intros n1 Hn1. eapply eq_sys_name_wf_in_dom in Hn1; eauto. destruct Hn1.
      + apply set_add_intro1. apply in_eq_sys_dom_prop. auto.
      + destruct H0. destruct H2 as [ p1 H2 ]. rewrite H2 in H1. apply app_inj_tail in H1.
        destruct H1. apply set_add_intro2. auto.
    - eexists. eexists. constructor; eauto. apply in_eq_sys_dom_prop'. auto.
Qed.

Lemma eq_sys_name_wf_len2 s n p (H : eq_sys_name_wf s n p) : var_set_size p <= S (length s).
Proof. apply eq_sys_name_wf_len1 in H. destruct H; auto. destruct H. lia. Qed.

Lemma eq_sys_dom_erase_name_wf1 s n n' p (H : ~In n' p)
                              : eq_sys_name_wf (eq_sys_dom_erase s n') n p <-> eq_sys_name_wf s n p.
Proof.
  constructor; intro.
  * induction H0; (rewrite eq_sys_dom_erase_lookup in H0; [ | intro; apply H; left; auto ]).
    - econstructor. eauto.
    - constructor. auto.
    - econstructor. eauto. apply IHeq_sys_name_wf. intro. apply H. right. auto.
  * induction H0; (erewrite <- eq_sys_dom_erase_lookup in H0; [ | intro; apply H; left; eauto ]).
    - econstructor. eauto.
    - constructor. auto.
    - econstructor. eauto. apply IHeq_sys_name_wf. intro. apply H. right. auto.
Qed.

Lemma eq_sys_dom_erase_name_wf2 s n n' p (H : eq_sys_name_wf s n p)
                              : exists p', eq_sys_name_wf (eq_sys_dom_erase s n') n p'.
Proof.
  induction H; destruct (name_eq_dec n n').
  1, 3, 5: exists [n]; constructor; apply in_eq_sys_dom_inv;
    intro Hn; apply in_eq_sys_dom_prop in Hn; apply eq_sys_dom_erase_prop in Hn;
    apply set_remove_iff in Hn; auto; apply Hn; auto.
  * exists [n]. econstructor. rewrite eq_sys_dom_erase_lookup; eauto.
  * exists [n]. constructor. rewrite eq_sys_dom_erase_lookup; auto.
  * destruct IHeq_sys_name_wf as [ p' IH ]. exists (n::p'). econstructor; eauto.
    rewrite eq_sys_dom_erase_lookup; eauto.
Qed.

Lemma eq_sys_name_wf_dec' s n : { p | eq_sys_name_wf s n p } + {~exists p, eq_sys_name_wf s n p}.
Proof.
  remember (var_set_size (eq_sys_dom s)) as m. symmetry in Heqm.
  generalize dependent n. generalize dependent s. induction m; intros.
  * assert (s = []). apply length_zero_iff_nil in Heqm. destruct s as [ | [ n' node ] s ]. auto.
    simpl in Heqm. apply set_add_not_empty in Heqm. inversion Heqm. subst. clear Heqm.
    left. eexists. constructor. auto.
  * remember (eq_sys_lookup s n) as res. symmetry in Heqres. destruct res as [ [ t | n' ] | ].
    - left. exists [n]. econstructor. eauto.
    - set (s' := eq_sys_dom_erase s n).
      assert (var_set_size (eq_sys_dom s') = m). symmetry. apply Nat.succ_inj. rewrite <- Heqm.
      apply eq_sys_dom_erase_size. eexists. eauto. specialize (IHm s' H n'). clear Heqm H.
      destruct IHm as [ [ p' IHm ] | IHm ]. destruct (in_dec name_eq_dec n p').
      + right. intro. destruct H as [ p H ]. set (H1 := H). apply eq_sys_name_wf_nonrec in H1.
        good_inversion H; rewrite H0 in Heqres; good_inversion Heqres. good_inversion H1.
        eapply eq_sys_dom_erase_name_wf1 in H2; eauto.
        assert (p' = p0). eapply eq_sys_name_wf_func; eauto. subst p0. auto.
      + left. exists (n::p'). econstructor. eauto. apply eq_sys_dom_erase_name_wf1 in IHm; auto.
      + right. intro. destruct H as [ p H ]. set (H1 := H). apply eq_sys_name_wf_nonrec in H1.
        good_inversion H; rewrite H0 in Heqres; good_inversion Heqres. apply IHm. exists p0.
        good_inversion H1. apply eq_sys_dom_erase_name_wf1; auto.
    - left. exists [n]. constructor. auto.
Qed.

Lemma eq_sys_name_wf_dec s n : {exists p, eq_sys_name_wf s n p} + {~exists p, eq_sys_name_wf s n p}.
Proof. destruct (eq_sys_name_wf_dec' s n); eauto. destruct s0. left. eexists. eauto. Qed.

Definition eq_sys_wf s : Prop := forall n, exists p, eq_sys_name_wf s n p.

Lemma eq_sys_wf_ext s1 s2 (H1 : eq_sys_wf s1)
                    (H2 : forall n, eq_sys_lookup s1 n = eq_sys_lookup s2 n)
                  : eq_sys_wf s2.
Proof. intro n. destruct (H1 n) as [ p H ]. eexists. eapply eq_sys_name_wf_ext; eauto. Qed.

Lemma eq_sys_trivial_wf : eq_sys_wf eq_sys_trivial.
Proof. intro n. eexists. constructor. auto. Qed.

Lemma eq_sys_wf_add_root s n t (H1 : eq_sys_wf s) : eq_sys_wf ((n, RootESNode t) :: s).
Proof. intro n'. destruct (H1 n') as [ p H ]. eapply eq_sys_name_wf_add_root1. eauto. Qed.

Lemma eq_sys_wf_add_link s n1 n2 p (H1 : eq_sys_wf s) (H2 : eq_sys_name_wf s n2 p) (H3 : ~In n1 p)
                       : eq_sys_wf ((n1, LinkESNode n2) :: s).
Proof. intro n'. destruct (H1 n') as [ p' H ]. eapply eq_sys_name_wf_add_link2; eauto. Qed.

Lemma eq_sys_dom_erase_wf s n (H : eq_sys_wf s) : eq_sys_wf (eq_sys_dom_erase s n).
Proof. intro n'. destruct (H n') as [ p' Hn' ]. eapply eq_sys_dom_erase_name_wf2; eauto. Qed.

Lemma eq_sys_dom_erase'_wf s ns (H : eq_sys_wf s) : eq_sys_wf (eq_sys_dom_erase' s ns).
Proof. induction ns as [ | n ns ]. auto. simpl. apply eq_sys_dom_erase_wf. auto. Qed.

Fixpoint eq_sys_find_hlp (s : eq_sys) (fuel : nat) (n : name) : name * option term_head :=
match fuel with
| 0 => (n, None)
| S fuel =>
  match eq_sys_lookup s n with
  | None => (n, None)
  | Some (RootESNode t) => (n, Some t)
  | Some (LinkESNode n) => eq_sys_find_hlp s fuel n
  end
end.

Lemma eq_sys_find_hlp_fuel_aux1 s fuel1 fuel2 n p (H : eq_sys_name_wf s n p)
                                (H1 : var_set_size p <= fuel1) (H2 : var_set_size p <= fuel2)
                              : eq_sys_find_hlp s fuel1 n = eq_sys_find_hlp s fuel2 n.
Proof.
  generalize dependent fuel1. generalize dependent fuel2. induction H; intros.
  - good_inversion H1; good_inversion H2; auto; simpl; try rewrite H; auto.
  - good_inversion H1; good_inversion H2; auto; simpl; try rewrite H; auto.
  - good_inversion H1; good_inversion H2; auto; simpl; rewrite H;
      apply IHeq_sys_name_wf; simpl in *; try lia.
Qed.

Lemma eq_sys_find_hlp_fuel_aux2 s fuel n n' p
                                (H1 : eq_sys_name_wf s n (p ++ [n'])) (H2 : ~in_eq_sys_dom n' s)
                                (H3 : var_set_size p <= fuel)
                              : eq_sys_find_hlp s fuel n = (n', None).
Proof.
  generalize dependent fuel.
  remember (p ++ [n']) as p'. generalize dependent p. induction H1; intros.
  - apply (app_inj_tail []) in Heqp'. destruct Heqp'. subst. exfalso. apply H2. eexists. eauto.
  - apply (app_inj_tail []) in Heqp'. destruct Heqp'. subst. destruct fuel; simpl; try rewrite H; auto.
  - destruct p0 as [ | n1 p' ]; good_inversion Heqp'. exfalso. apply H2. eexists. eauto.
    simpl in H3. good_inversion H3; eauto; simpl; rewrite H; eapply IHeq_sys_name_wf; eauto. lia.
Qed.

Lemma eq_sys_find_hlp_fuel s fuel1 fuel2 n p (H : eq_sys_name_wf s n p)
                           (H1 : length s <= fuel1) (H2 : length s <= fuel2)
                         : eq_sys_find_hlp s fuel1 n = eq_sys_find_hlp s fuel2 n.
Proof.
  set (H' := H). apply eq_sys_name_wf_len1 in H'. destruct H'.
  - eapply eq_sys_find_hlp_fuel_aux1; eauto; lia.
  - destruct H0 as [ H0 [ p' [ n' [ H3 H4 ] ] ] ]. subst.
    assert (var_set_size p' <= length s). unfold var_set_size in H0. rewrite length_app in H0.
    rewrite Nat.add_comm in H0. simpl in H0. apply le_S_n in H0. auto.
    transitivity (n', None : option term_head); [ | symmetry ];
      eapply eq_sys_find_hlp_fuel_aux2; eauto; lia.
Qed.

Lemma eq_sys_find_hlp_ext s1 s2 fuel n p (H1 : eq_sys_name_wf s1 n p) (H2 : var_set_size p <= fuel)
                          (H3 : forall n, eq_sys_lookup s1 n = eq_sys_lookup s2 n)
                        : eq_sys_find_hlp s1 fuel n = eq_sys_find_hlp s2 fuel n.
Proof.
  generalize dependent fuel.
  induction H1; intros; (destruct fuel; [ inversion H2 | ]);
    simpl in *; rewrite <- H3; rewrite H; auto.
  apply IHeq_sys_name_wf. lia.
Qed.

Lemma eq_sys_find_hlp_fst_ext s1 s2 fuel n p
                              (H1 : eq_sys_name_wf s1 n p)
                              (H2 : eq_sys_name_wf s2 n p)
                              (H3 : var_set_size p <= fuel)
                            : fst (eq_sys_find_hlp s1 fuel n) = fst (eq_sys_find_hlp s2 fuel n).
Proof.
  generalize dependent fuel.
  induction H1; intros; (destruct fuel; [ inversion H3 | ]); good_inversion H2; simpl.
  * rewrite H, H0. auto.
  * rewrite H, H0. auto.
  * inversion H5.
  * rewrite H, H0. auto.
  * rewrite H, H0. auto.
  * inversion H5.
  * inversion H1.
  * inversion H1.
  * rewrite H, H4. assert (n' = n'0). good_inversion H1; good_inversion H6; auto. subst.
    apply IHeq_sys_name_wf; auto. simpl in H3. lia.
Qed.

Lemma eq_sys_find_hlp_no s fuel n (H : eq_sys_lookup s n = None)
                       : eq_sys_find_hlp s fuel n = (n, None).
Proof. destruct fuel. auto. simpl. rewrite H. auto. Qed.

Lemma eq_sys_find_hlp_no_inv s fuel n1 n2 p (H1 : eq_sys_name_wf s n1 p)
                             (H2 : var_set_size p <= fuel)
                             (H3 : eq_sys_find_hlp s fuel n1 = (n2, None))
                           : eq_sys_lookup s n2 = None.
Proof.
  generalize dependent fuel.
  induction H1; intros; (destruct fuel; [ inversion H2 | ]); simpl in H3; rewrite H in H3.
  * inversion H3.
  * good_inversion H3. auto.
  * apply IHeq_sys_name_wf in H3. auto. simpl in H2. lia.
Qed.

Lemma eq_sys_find_hlp_some s fuel n n' t (H : eq_sys_find_hlp s fuel n = (n', Some t))
                         : eq_sys_lookup s n' = Some (RootESNode t).
Proof.
  generalize dependent n. induction fuel; intros. inversion H. simpl in H.
  remember (eq_sys_lookup s n) as res. symmetry in Heqres.
  destruct res as [ [ t' | n'' ] | ]; good_inversion H. auto.
  apply IHfuel in H1. auto.
Qed.

Lemma eq_sys_find_hlp_root s fuel n n' p (H1 : eq_sys_name_wf s n p) (H2 : var_set_size p <= fuel)
                           (H3 : fst (eq_sys_find_hlp s fuel n) = n')
                         : eq_sys_name_wf s n' [n'].
Proof.
  subst. generalize dependent fuel.
  induction H1; intros; destruct fuel; simpl in *; try lia; rewrite H; subst; simpl.
  * econstructor. eauto.
  * constructor. auto.
  * eapply IHeq_sys_name_wf. apply le_S_n. auto.
Qed.

Lemma eq_sys_find_hlp_last s fuel n1 n2 p (H1 : eq_sys_name_wf s n1 p) (H2 : var_set_size p <= fuel)
                           (H3 : fst (eq_sys_find_hlp s fuel n1) = n2)
                         : exists p', p = p' ++ [n2].
Proof.
  generalize dependent fuel.
  induction H1; intros; (destruct fuel; [ inversion H2 | ]); simpl in H3; rewrite H in H3.
  * good_inversion H3. exists []. auto.
  * good_inversion H3. exists []. auto.
  * apply IHeq_sys_name_wf in H3. destruct H3 as [ p' H3 ].
    exists (n::p'). rewrite H3. auto. simpl in H2. lia.
Qed.

Lemma eq_sys_find_hlp_in_vars_aux s fuel n (H : in_eq_sys_links n s)
                            : in_eq_sys_links (fst (eq_sys_find_hlp s fuel n)) s.
Proof.
  generalize dependent n. induction fuel; intros; simpl. auto.
  remember (eq_sys_lookup s n) as res. symmetry in Heqres.
  destruct res as [ [ t | n' ] | ]; auto. apply IHfuel. eexists. eauto.
Qed.

Lemma eq_sys_find_hlp_in_vars s fuel n
                            : in_eq_sys_vars (fst (eq_sys_find_hlp s fuel n)) s
                           \/ fst (eq_sys_find_hlp s fuel n) = n.
Proof.
  destruct fuel; simpl. auto.
  remember (eq_sys_lookup s n) as res. symmetry in Heqres.
  destruct res as [ [ t | n' ] | ]; auto. left. right. right.
  eapply eq_sys_find_hlp_in_vars_aux. eexists. eauto.
Qed.

Lemma eq_sys_find_hlp_in_rhs s fuel n t (H : snd (eq_sys_find_hlp s fuel n) = Some t)
                           : in_eq_sys_rhs t s.
Proof.
  generalize dependent n. induction fuel; intros. inversion H. simpl in H.
  remember (eq_sys_lookup s n) as res. symmetry in Heqres. destruct res as [ [ t' | n' ] | ].
  - good_inversion H. eexists. eauto.
  - apply IHfuel in H. auto.
  - inversion H.
Qed.

Definition eq_sys_find s n := eq_sys_find_hlp s (length s) n.

Lemma eq_sys_find_ext s1 s2 n p (H1 : eq_sys_name_wf s1 n p)
                      (H2 : forall n, eq_sys_lookup s1 n = eq_sys_lookup s2 n)
                    : eq_sys_find s1 n = eq_sys_find s2 n.
Proof.
  unfold eq_sys_find.
  transitivity (eq_sys_find_hlp s1 (S (max (length s1) (length s2))) n).
  eapply eq_sys_find_hlp_fuel. eauto. auto. lia.
  transitivity (eq_sys_find_hlp s2 (S (max (length s1) (length s2))) n).
  eapply eq_sys_find_hlp_ext; eauto. apply eq_sys_name_wf_len2 in H1; lia.
  eapply eq_sys_name_wf_ext in H1; eauto. eapply eq_sys_find_hlp_fuel. eauto. lia. auto.
Qed.

Lemma eq_sys_find_fst_ext s1 s2 n p (H1 : eq_sys_name_wf s1 n p) (H2 : eq_sys_name_wf s2 n p)
                        : fst (eq_sys_find s1 n) = fst (eq_sys_find s2 n).
Proof.
  unfold eq_sys_find.
  transitivity (fst (eq_sys_find_hlp s1 (S (max (length s1) (length s2))) n)).
  f_equal. eapply eq_sys_find_hlp_fuel. eauto. auto. lia.
  transitivity (fst (eq_sys_find_hlp s2 (S (max (length s1) (length s2))) n)).
  eapply eq_sys_find_hlp_fst_ext; eauto. apply eq_sys_name_wf_len2 in H1. lia.
  f_equal. eapply eq_sys_find_hlp_fuel. eauto. lia. auto.
Qed.

Lemma eq_sys_find_link s n1 n2 p (H1 : eq_sys_name_wf s n1 p)
                       (H2 : eq_sys_lookup s n1 = Some (LinkESNode n2))
                     : eq_sys_find s n1 = eq_sys_find s n2.
Proof.
  unfold eq_sys_find at 1. erewrite (eq_sys_find_hlp_fuel _ _ (S (length s))); eauto.
  simpl. rewrite H2. auto.
Qed.

Lemma eq_sys_find_no s n (H : eq_sys_lookup s n = None) : eq_sys_find s n = (n, None).
Proof. apply eq_sys_find_hlp_no. auto. Qed.

Lemma eq_sys_find_no_inv s n1 n2 p (H1 : eq_sys_name_wf s n1 p)
                         (H2 : eq_sys_find s n1 = (n2, None))
                       : eq_sys_lookup s n2 = None.
Proof.
  unfold eq_sys_find in H2. erewrite (eq_sys_find_hlp_fuel _ _ (S (length s))) in H2; eauto.
  eapply eq_sys_find_hlp_no_inv in H2; eauto. eapply eq_sys_name_wf_len2. eauto.
Qed.

Lemma eq_sys_find_some s n n' t (H : eq_sys_find s n = (n', Some t))
                     : eq_sys_lookup s n' = Some (RootESNode t).
Proof. eapply eq_sys_find_hlp_some. eauto. Qed.

Lemma eq_sys_find_some_inv s n t (H : eq_sys_lookup s n = Some (RootESNode t))
                         : eq_sys_find s n = (n, Some t).
Proof.
  unfold eq_sys_find.
  unshelve erewrite (_ : length s = S (pred (length s))). {
    destruct s as [ | [ n' node ] s ]. inversion H. auto.
  }
  simpl. rewrite H. auto.
Qed.

Lemma eq_sys_find_root s n n' p (H1 : eq_sys_name_wf s n p) (H2 : fst (eq_sys_find s n) = n')
                     : eq_sys_name_wf s n' [n'].
Proof.
  unfold eq_sys_find in H2. erewrite (eq_sys_find_hlp_fuel _ _ (S (length s))) in H2; eauto.
  eapply eq_sys_find_hlp_root in H2; eauto. eapply eq_sys_name_wf_len2. eauto.
Qed.

Lemma eq_sys_find_in_path s n1 n2 p (H1 : eq_sys_name_wf s n1 p) (H2 : In n2 p)
                        : eq_sys_find s n1 = eq_sys_find s n2.
Proof.
  induction H1; intros.
  * good_inversion H2; [ | inversion H0 ]. auto.
  * good_inversion H2; [ | inversion H0 ]. auto.
  * good_inversion H2. auto. etransitivity. eapply (eq_sys_find_link _ _ _ (n::p)); eauto.
    econstructor; eauto. apply IHeq_sys_name_wf. auto.
Qed.

Lemma eq_sys_find_last s n1 n2 p (H1 : eq_sys_name_wf s n1 p) (H2 : fst (eq_sys_find s n1) = n2)
                     : exists p', p = p' ++ [n2].
Proof.
  unfold eq_sys_find in H2. erewrite (eq_sys_find_hlp_fuel _ _ (S (length s))) in H2; eauto.
  eapply eq_sys_find_hlp_last in H2; eauto. eapply eq_sys_name_wf_len2. eauto.
Qed.

Lemma eq_sys_find_in_vars s n : in_eq_sys_vars (fst (eq_sys_find s n)) s
                             \/ fst (eq_sys_find s n) = n.
Proof. apply eq_sys_find_hlp_in_vars. Qed.

Lemma eq_sys_find_in_rhs s n t (H : snd (eq_sys_find s n) = Some t) : in_eq_sys_rhs t s.
Proof. apply eq_sys_find_hlp_in_rhs in H. auto. Qed.

Lemma eq_sys_find_dom_erase_extend s n n' node p (H1 : eq_sys_name_wf s n' p)
                                   (H2 : eq_sys_lookup s n = Some node)
                                 : eq_sys_find ((n, node) :: eq_sys_dom_erase s n) n'
                                 = eq_sys_find s n'.
Proof.
  symmetry. eapply eq_sys_find_ext; eauto. intro.
  symmetry. apply eq_sys_dom_erase_extend_lookup. auto.
Qed.

Definition eq_sys_image_hlp (image : name -> inf_term) (t : name * option term_head) : inf_term :=
match t with
| (n, None) => VarInf n
| (_, Some (CstHead n)) => CstInf n
| (_, Some (ConHead n n1 n2)) => ConInf n (image n1) (image n2)
end.

CoFixpoint eq_sys_image (s : eq_sys) (n : name) : inf_term :=
  eq_sys_image_hlp (eq_sys_image s) (eq_sys_find s n).

Lemma eq_sys_image_no s n (H : ~in_eq_sys_dom n s) : eq_sys_image s n = VarInf n.
Proof.
  rewrite inf_term_step_prop at 1. simpl.
  rewrite eq_sys_find_no. simpl. auto.
  apply in_eq_sys_dom_inv. auto.
Qed.

Lemma eq_sys_image_find s n p (H : eq_sys_name_wf s n p)
                      : inf_term_eq (eq_sys_image s n) (eq_sys_image s (fst (eq_sys_find s n))).
Proof.
  rewrite inf_term_step_prop at 1. simpl.
  remember (eq_sys_find s n) as res. symmetry in Heqres.
  destruct res as [ n' [ [ c | c l r ] | ] ]; rewrite inf_term_step_prop; simpl.
  * apply eq_sys_find_some in Heqres. erewrite eq_sys_find_some_inv; eauto. reflexivity.
  * apply eq_sys_find_some in Heqres. erewrite eq_sys_find_some_inv; eauto. reflexivity.
  * eapply eq_sys_find_no_inv in Heqres; eauto. rewrite eq_sys_find_no; auto.
Qed.

CoFixpoint eq_sys_image_ext s s' n (H : forall n', eq_sys_find s n' = eq_sys_find s' n')
                          : inf_term_eq (eq_sys_image s n) (eq_sys_image s' n) :=
rew <- [fun x => inf_term_eq x _] inf_term_step_prop (eq_sys_image s n) in
rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (eq_sys_image s' n) in
rew <- [fun x => inf_term_eq (inf_term_step (eq_sys_image_hlp _ x)) _] H n in
match eq_sys_find s' n as res
return inf_term_eq (inf_term_step (eq_sys_image_hlp _ res)) (inf_term_step (eq_sys_image_hlp _ res))
with
| (n, None) => VarInfEq n : inf_term_eq (inf_term_step (VarInf n)) (inf_term_step (VarInf n))
| (_, Some (CstHead n)) =>
  CstInfEq n : inf_term_eq (inf_term_step (CstInf n)) (inf_term_step (CstInf n))
| (_, Some (ConHead n n1 n2)) =>
  ConInfEq n _ _ _ _ (eq_sys_image_ext _ _ n1 H) (eq_sys_image_ext _ _ n2 H)
    : inf_term_eq (inf_term_step (ConInf _ _ _)) (inf_term_step (ConInf _ _ _))
end.

(* we unable to use transitivity here due to CoFixpoint restrictions *)
CoFixpoint eq_sys_image_extend_aux s n1 n2 node
  (H1 : forall n2 n2', eq_sys_find s n2 = (n2', None)
                    -> inf_term_eq (eq_sys_image ((n1, node) :: s) n2)
                                   (if name_eq_dec n1 n2'
                                    then eq_sys_image ((n1, node) :: s) n1
                                    else VarInf n2'))
  (H2 : forall n2 n2' c2, eq_sys_find s n2 = (n2', Some (CstHead c2))
                       -> inf_term_eq (eq_sys_image ((n1, node) :: s) n2)
                                      (CstInf c2))
  (H3 : forall n2 n2_1 n2_2 c1 l1 r1, eq_sys_find s n2 = (n2_1, Some (ConHead c1 l1 r1))
                                   -> eq_sys_find ((n1, node) :: s) n2 = (n2_2, None)
                                   -> False)
  (H4 : forall n2 n2_1 n2_2 c1 c2 l1 r1, eq_sys_find s n2 = (n2_1, Some (ConHead c1 l1 r1))
                                      -> eq_sys_find ((n1, node) :: s) n2 = (n2_2, Some (CstHead c2))
                                      -> False)
  (H5 : forall n2 n2_1 n2_2 c1 c2 l1 l2 r1 r2, eq_sys_find s n2 = (n2_1, Some (ConHead c1 l1 r1))
                                            -> eq_sys_find ((n1, node) :: s) n2 = (n2_2, Some (ConHead c2 l2 r2))
                                            -> c1 = c2)
  (H6 : forall n2 n2_1 n2_2 c1 c2 l1 l2 r1 r2, eq_sys_find s n2 = (n2_1, Some (ConHead c1 l1 r1))
                                            -> eq_sys_find ((n1, node) :: s) n2 = (n2_2, Some (ConHead c2 l2 r2))
                                            -> l1 = l2)
  (H7 : forall n2 n2_1 n2_2 c1 c2 l1 l2 r1 r2, eq_sys_find s n2 = (n2_1, Some (ConHead c1 l1 r1))
                                            -> eq_sys_find ((n1, node) :: s) n2 = (n2_2, Some (ConHead c2 l2 r2))
                                            -> r1 = r2)
: inf_term_eq (eq_sys_image ((n1, node) :: s) n2)
              (apply_inf_subst (inf_subst_singleton n1 (eq_sys_image ((n1, node) :: s) n1))
                               (eq_sys_image s n2)) :=
rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (apply_inf_subst (inf_subst_singleton n1 _)
                                                                      (eq_sys_image s n2)) in
match eq_sys_find s n2 as res
return eq_sys_find s n2 = res
    -> inf_term_eq (eq_sys_image ((n1, node) :: s) n2)
                   (inf_term_step (apply_inf_subst _ (eq_sys_image_hlp _ res)))
with
| (n2', None) => fun p =>
  rew [fun x => inf_term_eq _ x] inf_term_step_prop (if name_eq_dec n1 n2' then _ else _) in
  H1 _ _ p
| (n2', Some (CstHead c2)) => H2 _ _ _
| (n2_2, Some (ConHead c2 l2 r2)) => fun p =>
  rew <- [fun x => inf_term_eq x _] inf_term_step_prop (eq_sys_image ((n1, node) :: s) n2) in
  match eq_sys_find ((n1, node) :: s) n2 as res
  return eq_sys_find ((n1, node) :: s) n2 = res
      -> inf_term_eq (inf_term_step (eq_sys_image_hlp _ res)) (ConInf c2 _ _)
  with
  | (n2_1, None) => fun q => False_ind _ (H3 _ _ _ _ _ _ p q)
  | (n2_1, Some (CstHead c1)) => fun q => False_ind _ (H4 _ _ _ _ _ _ _ p q)
  | (n2_1, Some (ConHead c1 l1 r1)) => fun q =>
    rew [fun c => inf_term_eq (ConInf c _ _) (ConInf c2 _ _)] H5 _ _ _ _ _ _ _ _ _ p q in
    rew [fun l => inf_term_eq (ConInf _ (eq_sys_image _ l) _) _] H6 _ _ _ _ _ _ _ _ _ p q in
    rew [fun r => inf_term_eq (ConInf _ _ (eq_sys_image _ r)) _] H7 _ _ _ _ _ _ _ _ _ p q in
    ConInfEq _ _ _ _ _ (eq_sys_image_extend_aux _ _ l2 _ H1 H2 H3 H4 H5 H6 H7)
                       (eq_sys_image_extend_aux _ _ r2 _ H1 H2 H3 H4 H5 H6 H7)
  end eq_refl
end eq_refl.

Lemma eq_sys_image_extend s n1 n2 node (H1 : eq_sys_wf s) (H2 : eq_sys_wf ((n1, node) :: s))
                          (H3 : eq_sys_lookup s n1 = None)
                        : inf_term_eq (eq_sys_image ((n1, node) :: s) n2)
                                      (apply_inf_subst (inf_subst_singleton n1
                                                          (eq_sys_image ((n1, node) :: s) n1))
                                                       (eq_sys_image s n2)).
Proof.
  apply eq_sys_image_extend_aux; clear n2; intros.
  * remember (name_eq_dec n1 n2') as dec. symmetry in Heqdec. destruct dec.
    - subst n2'. destruct (H1 n2) as [ p Hp ]. set (Hp' := Hp).
      eapply eq_sys_find_last in Hp'; [ | rewrite H; auto ]. destruct Hp' as [ p' Hp' ].
      subst p. rename p' into p. simpl in Hp. destruct node as [ t | n1' ].
      + set (Hp' := Hp). eapply eq_sys_name_wf_add_root2 in Hp'.
        etransitivity. eapply eq_sys_image_find. eauto.
        erewrite eq_sys_find_fst_ext; [ | apply Hp' | apply Hp ].
        rewrite H. reflexivity.
      + destruct (H2 n1') as [ p1 Hp1 ]. eapply eq_sys_name_wf_add_link3 in Hp; [ | apply Hp1 ].
        etransitivity. eapply eq_sys_image_find. eauto. erewrite eq_sys_find_in_path; eauto.
        2: apply in_app_iff; right; left; auto. symmetry.
        destruct (H2 n1) as [ p' Hp' ]. eapply eq_sys_image_find. eauto.
    - destruct (H1 n2) as [ p Hp ]. set (Hp' := Hp). eapply eq_sys_name_wf_extend in Hp'.
      etransitivity. eapply eq_sys_image_find. eauto.
      erewrite eq_sys_find_fst_ext; [ | apply Hp' | apply Hp ].
      rewrite H. simpl. rewrite inf_term_step_prop at 1. simpl.
      erewrite eq_sys_find_no. reflexivity.
      + simpl. destruct (name_eq_dec n2' n1); [ | eapply eq_sys_find_no_inv; eauto ].
        exfalso. apply n. auto.
      + intro. erewrite eq_sys_find_in_path in H; eauto. apply eq_sys_find_no in H3.
        rewrite H in H3. inversion H3. apply n. auto.
  * destruct (H1 n2) as [ p Hp ]. set (Hp' := Hp). eapply eq_sys_name_wf_extend in Hp'.
    etransitivity. eapply eq_sys_image_find. eauto.
    erewrite eq_sys_find_fst_ext; [ | apply Hp' | apply Hp ].
    rewrite H. simpl. rewrite inf_term_step_prop at 1. simpl.
    erewrite eq_sys_find_some_inv. 2: {
      simpl. destruct (name_eq_dec n2' n1); [ | eapply eq_sys_find_some; eauto ].
      apply eq_sys_find_no in H3. erewrite <- eq_sys_find_in_path in H3. rewrite H in H3.
      inversion H3. eauto. eapply eq_sys_find_last in Hp; [ | rewrite H; auto ].
      destruct Hp as [ p' Hp ]. subst p. apply in_app_iff. right. left. auto.
    }
    reflexivity.
    intro. erewrite eq_sys_find_in_path in H; eauto. apply eq_sys_find_no in H3.
    rewrite H in H3. inversion H3.
  * destruct (H1 n2) as [ p Hp ]. set (Hp' := Hp). eapply eq_sys_name_wf_extend in Hp'.
    assert (n2_1 = n2_2). {
      eapply eq_sys_find_fst_ext in Hp'.
      rewrite H in Hp'. rewrite H0 in Hp'.
      simpl in Hp'. auto. auto.
    }
    subst n2_2. rename n2_1 into n2'.
    eapply eq_sys_find_no_inv in H0; eauto.
    simpl in H0. destruct (name_eq_dec n2' n1). inversion H0.
    eapply eq_sys_find_some in H. rewrite H0 in H. inversion H.
    intro. erewrite eq_sys_find_in_path in H; eauto. rewrite eq_sys_find_no in H; auto.
    inversion H.
  * destruct (H1 n2) as [ p Hp ]. set (Hp' := Hp). eapply eq_sys_name_wf_extend in Hp'.
    assert (n2_1 = n2_2). {
      eapply eq_sys_find_fst_ext in Hp'.
      rewrite H in Hp'. rewrite H0 in Hp'.
      simpl in Hp'. auto. auto.
    }
    subst n2_2. rename n2_1 into n2'.
    eapply eq_sys_find_some in H0; eauto.
    simpl in H0. destruct (name_eq_dec n2' n1). subst n2'.
    apply eq_sys_find_some in H. rewrite H3 in H. inversion H.
    eapply eq_sys_find_some in H. rewrite H0 in H. inversion H.
    intro. erewrite eq_sys_find_in_path in H; eauto. rewrite eq_sys_find_no in H; auto.
    inversion H.
  * destruct (H1 n2) as [ p Hp ]. set (Hp' := Hp). eapply eq_sys_name_wf_extend in Hp'.
    assert (n2_1 = n2_2). {
      eapply eq_sys_find_fst_ext in Hp'.
      rewrite H in Hp'. rewrite H0 in Hp'.
      simpl in Hp'. auto. auto.
    }
    subst n2_2. rename n2_1 into n2'.
    eapply eq_sys_find_some in H0; eauto.
    simpl in H0. destruct (name_eq_dec n2' n1). subst n2'.
    apply eq_sys_find_some in H. rewrite H3 in H. inversion H.
    eapply eq_sys_find_some in H. rewrite H0 in H. good_inversion H. auto.
    intro. erewrite eq_sys_find_in_path in H; eauto. rewrite eq_sys_find_no in H; auto.
    inversion H.
  * destruct (H1 n2) as [ p Hp ]. set (Hp' := Hp). eapply eq_sys_name_wf_extend in Hp'.
    assert (n2_1 = n2_2). {
      eapply eq_sys_find_fst_ext in Hp'.
      rewrite H in Hp'. rewrite H0 in Hp'.
      simpl in Hp'. auto. auto.
    }
    subst n2_2. rename n2_1 into n2'.
    eapply eq_sys_find_some in H0; eauto.
    simpl in H0. destruct (name_eq_dec n2' n1). subst n2'.
    apply eq_sys_find_some in H. rewrite H3 in H. inversion H.
    eapply eq_sys_find_some in H. rewrite H0 in H. good_inversion H. auto.
    intro. erewrite eq_sys_find_in_path in H; eauto. rewrite eq_sys_find_no in H; auto.
    inversion H.
  * destruct (H1 n2) as [ p Hp ]. set (Hp' := Hp). eapply eq_sys_name_wf_extend in Hp'.
    assert (n2_1 = n2_2). {
      eapply eq_sys_find_fst_ext in Hp'.
      rewrite H in Hp'. rewrite H0 in Hp'.
      simpl in Hp'. auto. auto.
    }
    subst n2_2. rename n2_1 into n2'.
    eapply eq_sys_find_some in H0; eauto.
    simpl in H0. destruct (name_eq_dec n2' n1). subst n2'.
    apply eq_sys_find_some in H. rewrite H3 in H. inversion H.
    eapply eq_sys_find_some in H. rewrite H0 in H. good_inversion H. auto.
    intro. erewrite eq_sys_find_in_path in H; eauto. rewrite eq_sys_find_no in H; auto.
    inversion H.
Qed.

Lemma eq_sys_image_dom_erase_extend s n n' node (H1 : eq_sys_wf s)
                                    (H2 : eq_sys_lookup s n = Some node)
                                  : inf_term_eq (eq_sys_image ((n, node) :: eq_sys_dom_erase s n) n')
                                                (eq_sys_image s n').
Proof.
  apply eq_sys_image_ext. clear n'. intros.
  destruct (H1 n'). eapply eq_sys_find_dom_erase_extend; eauto.
Qed.

Fixpoint eq_sys_apply (s : eq_sys) (t : term) : inf_term :=
match t with
| Var n => eq_sys_image s n
| Cst n => CstInf n
| Con n t1 t2 => ConInf n (eq_sys_apply s t1) (eq_sys_apply s t2)
end.

Lemma eq_sys_image_find_apply s n p t (H1 : eq_sys_name_wf s n p)
                              (H2 : snd (eq_sys_find s n) = Some t)
                            : inf_term_eq (eq_sys_image s n) (eq_sys_apply s (term_head_to_term t)).
Proof.
  rewrite inf_term_step_prop at 1. simpl.
  remember (eq_sys_find s n) as res. symmetry in Heqres.
  destruct res as [ n' [ t' | ] ]; good_inversion H2.
  destruct t as [ c | c l r ]; reflexivity.
Qed.

Lemma eq_sys_apply_ext s1 s2 t : inf_term_eq (eq_sys_apply s1 t) (eq_sys_apply s2 t)
                             <-> (forall n, In n (fv_term t)
                                         -> inf_term_eq (eq_sys_image s1 n) (eq_sys_image s2 n)).
Proof.
  constructor; intros.
  * induction t as [ n' | n' | n' l IHl r ]; simpl in H.
    - destruct H0; [ | inversion H0 ]. subst. auto.
    - inversion H0.
    - good_inversion H. simpl in H0. apply set_union_elim in H0.
      destruct H0; [ apply IHl | apply IHr ]; auto.
  * induction t as [ n' | n' | n' l IHl r ]; simpl.
    - apply H. left. auto.
    - constructor.
    - constructor; [ apply IHl | apply IHr ]; intros; apply H;
        [ apply set_union_intro1 | apply set_union_intro2 ]; auto.
Qed.

Lemma eq_sys_apply_dom_erase_extend s n node t (H1 : eq_sys_wf s)
                                    (H2 : eq_sys_lookup s n = Some node)
                                  : inf_term_eq (eq_sys_apply ((n, node) :: eq_sys_dom_erase s n) t)
                                                (eq_sys_apply s t).
Proof.
  apply eq_sys_apply_ext. intros n' _.
  apply eq_sys_image_dom_erase_extend; auto.
Qed.

Definition eq_sys_inf_subst (s : eq_sys) : inf_subst := eq_sys_image s.

Lemma eq_sys_inf_subst_prop s t : inf_term_eq (eq_sys_apply s t)
                                              (apply_inf_subst (eq_sys_inf_subst s)
                                                               (term_to_inf_term t)).
Proof.
  induction t as [ n | n | n l IHl r ]; rewrite inf_term_step_prop; simpl.
  * refine (_ : inf_term_eq _ (inf_term_step (eq_sys_image s n))).
    rewrite <- inf_term_step_prop. reflexivity.
  * constructor.
  * constructor. apply IHl. apply IHr.
Qed.

CoFixpoint eq_sys_inf_subst_extend s n node t (H1 : eq_sys_wf s) (H2 : eq_sys_wf ((n, node) :: s))
                                   (H3 : eq_sys_lookup s n = None)
                                 : inf_term_eq (apply_inf_subst (eq_sys_inf_subst ((n, node) :: s)) t)
                                               (apply_inf_subst (inf_subst_singleton n (eq_sys_image ((n, node) :: s) n))
                                                                (apply_inf_subst (eq_sys_inf_subst s) t)) :=
rew <- [fun x => inf_term_eq x _] inf_term_step_prop (apply_inf_subst _ t) in
rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (apply_inf_subst _ (apply_inf_subst _ t)) in
match t as t'
return inf_term_eq (inf_term_step (apply_inf_subst (eq_sys_inf_subst ((n, node) :: s)) t'))
                   (inf_term_step (apply_inf_subst _ (apply_inf_subst (eq_sys_inf_subst s) t')))
with
| VarInf n' =>
  rew [fun x => inf_term_eq x _] inf_term_step_prop (eq_sys_image _ n') in
  rew [fun x => inf_term_eq _ x] inf_term_step_prop (apply_inf_subst (inf_subst_singleton n _)
                                                                     (eq_sys_image s n')) in
  eq_sys_image_extend _ _ _ _ H1 H2 H3
| CstInf n' => CstInfEq _
| ConInf n' l r => ConInfEq n' _ _ _ _
  (eq_sys_inf_subst_extend _ _ _ _ H1 H2 H3)
  (eq_sys_inf_subst_extend _ _ _ _ H1 H2 H3)
end.

Lemma eq_sys_apply_extend s n node t (H1 : eq_sys_wf s) (H2 : eq_sys_wf ((n, node) :: s))
                          (H3 : eq_sys_lookup s n = None)
                        : inf_term_eq (eq_sys_apply ((n, node) :: s) t)
                                      (apply_inf_subst (inf_subst_singleton n (eq_sys_image ((n, node) :: s) n))
                                                       (eq_sys_apply s t)).
Proof.
  etransitivity. apply eq_sys_inf_subst_prop. symmetry.
  etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop. symmetry.
  apply eq_sys_inf_subst_extend; auto.
Qed.

Lemma eq_sys_apply_dom_erase s n t (H1 : eq_sys_wf s)
                           : inf_term_eq (eq_sys_apply s t)
                                         (apply_inf_subst (inf_subst_singleton n (eq_sys_image s n))
                                                          (eq_sys_apply (eq_sys_dom_erase s n) t)).
Proof.
  remember (eq_sys_lookup s n) as res. symmetry in Heqres. destruct res as [ node | ].
  * set (H2 := H1).
    eapply eq_sys_wf_ext in H2; [ | intros; symmetry; apply eq_sys_dom_erase_extend_lookup; eauto ].
    etransitivity. symmetry. apply eq_sys_apply_dom_erase_extend; eauto. etransitivity.
    apply eq_sys_apply_extend. apply eq_sys_dom_erase_wf. auto. auto.
    apply in_eq_sys_dom_inv. intro. apply in_eq_sys_dom_prop in H.
    apply eq_sys_dom_erase_prop in H. apply set_remove_iff in H; auto. destruct H. auto.
    apply apply_inf_subst_ext. intros n' _. unfold inf_subst_singleton.
    destruct (name_eq_dec n n'). apply eq_sys_image_dom_erase_extend; auto. auto.
  * symmetry. rewrite eq_sys_dom_erase_no. 2: apply in_eq_sys_dom_inv; auto.
    etransitivity; [ | apply apply_inf_subst_trivial ]. apply apply_inf_subst_ext.
    intros n' _. unfold inf_subst_singleton. destruct (name_eq_dec n n'); auto. subst n'.
    rewrite eq_sys_image_no. auto. apply in_eq_sys_dom_inv. auto.
Qed.

Definition eq_sys_union (s : eq_sys) (x y : name) : option (term_head * term_head) * eq_sys :=
match eq_sys_find s x, eq_sys_find s y with
| (x, t1), (y, t2) =>
  if name_eq_dec x y then (None, s)
  else
    let res := match t1, t2 with
    | Some t1, Some t2 => Some (t1, t2)
    | _, _ => None
    end in
    let (x, y) := match t2 with
    | Some _ => (y, x)
    | _ => (x, y)
    end in
    (res, (y, LinkESNode x) :: s)
end.

Lemma eq_sys_union_wf s x y (H : eq_sys_wf s) : eq_sys_wf (snd (eq_sys_union s x y)).
Proof.
  unfold eq_sys_union.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  destruct (name_eq_dec x' y'). auto. simpl.
  destruct t2 as [ t2 | ]; eapply eq_sys_wf_add_link; eauto.
  * apply (f_equal fst) in Heqresy. destruct (H y). eapply eq_sys_find_root; eauto.
  * intro. apply n. good_inversion H0. auto. inversion H1.
  * apply (f_equal fst) in Heqresx. destruct (H x). eapply eq_sys_find_root; eauto.
  * intro. apply n. good_inversion H0. auto. inversion H1.
Qed.

Lemma eq_sys_union_vars s x y z (H1 : eq_sys_wf s) (H2 : in_eq_sys_vars z (snd (eq_sys_union s x y)))
                      : in_eq_sys_vars z s \/ z = fst (eq_sys_find s x) \/ z = fst (eq_sys_find s y).
Proof.
  unfold eq_sys_union in H2.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  destruct (name_eq_dec x' y'). auto.
  destruct t2 as [ t2 | ]; simpl in H2; apply in_eq_sys_vars_add_link in H2;
    destruct H2 as [ H2 | [ H2 | H2 ] ]; auto.
Qed.

Lemma eq_sys_union_terms s x y t1 t2 (H : fst (eq_sys_union s x y) = Some (t1, t2))
                       : in_eq_sys_rhs t1 s /\ in_eq_sys_rhs t2 s.
Proof.
  unfold eq_sys_union in H.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1' ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2' ].
  destruct (name_eq_dec x' y'). inversion H.
  destruct t1' as [ t1' | ]; destruct t2' as [ t2' | ]; [ | inversion H .. ].
  good_inversion H. constructor; [ exists x' | exists y' ]; eapply eq_sys_find_some; eauto.
Qed.

Definition eq_sys_bind (s : eq_sys) (n : name) (t : term_head) : eq_sys :=
  let (n, _) := eq_sys_find s n in (n, RootESNode t) :: s.

Lemma eq_sys_bind_wf s n t (H : eq_sys_wf s) : eq_sys_wf (eq_sys_bind s n t).
Proof. unfold eq_sys_bind. destruct (eq_sys_find s n). apply eq_sys_wf_add_root. auto. Qed.

Lemma eq_sys_bind_vars s n1 n2 t (H : in_eq_sys_vars n1 (eq_sys_bind s n2 t))
                     : in_eq_sys_vars n1 s \/ n1 = fst (eq_sys_find s n2) \/ In n1 (fv_term_head t).
Proof. unfold eq_sys_bind in H. destruct (eq_sys_find s n2). apply in_eq_sys_vars_add_root. auto. Qed.


(* Equation System Roots *)

Definition is_eq_sys_root n s : Prop :=
  eq_sys_lookup s n = None \/ exists t, eq_sys_lookup s n = Some (RootESNode t).

Lemma is_eq_sys_root_prop n s : is_eq_sys_root n s <-> eq_sys_name_wf s n [n].
Proof.
  constructor; intro.
  * destruct H as [ H | [ t H ] ]; [ constructor | econstructor ]; eauto.
  * good_inversion H. right. eexists. eauto. left. auto. inversion H3.
Qed.

Lemma eq_sys_find_root_inv s n (H : is_eq_sys_root n s) : fst (eq_sys_find s n) = n.
Proof.
  set (H' := H). apply is_eq_sys_root_prop in H'.
  unfold eq_sys_find. erewrite (eq_sys_find_hlp_fuel _ _ (S (length s))); eauto. simpl.
  destruct H as [ H | [ t H ] ]; rewrite H; auto.
Qed.

Lemma eq_sys_union_roots s x y z
                         (H : is_eq_sys_root z (snd (eq_sys_union s x y)))
                       : is_eq_sys_root z s.
Proof.
  unfold eq_sys_union in H.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  destruct (name_eq_dec x' y'). auto.
  destruct t2 as [ t2 | ]; destruct H as [ H | [ t H ] ]; simpl in H.
  * destruct (name_eq_dec z x'). inversion H. left. auto.
  * destruct (name_eq_dec z x'). inversion H. right. eexists. eauto.
  * destruct (name_eq_dec z y'). inversion H. left. auto.
  * destruct (name_eq_dec z y'). inversion H. right. eexists. eauto.
Qed.

Definition eq_sys_roots (s : eq_sys) (ns : var_set) : var_set :=
  nodup name_eq_dec (map (fun n => fst (eq_sys_find s n)) ns).

Lemma eq_sys_roots_distinct s ns : NoDup (eq_sys_roots s ns).
Proof. apply NoDup_nodup. Qed.

Lemma eq_sys_roots_prop s ns n : In n (eq_sys_roots s ns)
                             <-> exists n', In n' ns /\ fst (eq_sys_find s n') = n.
Proof.
  constructor; intro.
  * apply nodup_In in H. apply in_map_iff in H. destruct H as [ n' [ H1 H2 ] ].
    eexists. constructor; eauto.
  * destruct H as [ n' [ H1 H2 ] ]. apply nodup_In. apply in_map_iff.
    eexists. constructor; eauto.
Qed.

Lemma eq_sys_roots_are_roots s ns n (H1 : eq_sys_wf s) (H2 : In n (eq_sys_roots s ns))
                           : is_eq_sys_root n s.
Proof.
  apply eq_sys_roots_prop in H2. destruct H2 as [ n' [ H2 H3 ] ]. apply is_eq_sys_root_prop.
  destruct (H1 n') as [ p H ]. eapply eq_sys_find_root; eauto.
Qed.

Definition is_eq_sys_root_of n s ns : Prop := is_eq_sys_root n s /\ In n ns.

Lemma eq_sys_roots_of s ns n (H : is_eq_sys_root_of n s ns) : In n (eq_sys_roots s ns).
Proof.
  destruct H. apply eq_sys_find_root_inv in H. apply eq_sys_roots_prop.
  eexists. constructor; eauto.
Qed.

Lemma eq_sys_roots_all s ns n (H1 : eq_sys_wf s) (H2 : forall n, in_eq_sys_vars n s -> In n ns)
                     : is_eq_sys_root_of n s ns <-> In n (eq_sys_roots s ns).
Proof.
  constructor; intro. apply eq_sys_roots_of. auto.
  apply eq_sys_roots_prop in H. destruct H as [ n' [ H3 H4 ] ].
  destruct (eq_sys_find_in_vars s n').
  * apply H2 in H. rewrite H4 in H. constructor; auto.
    apply is_eq_sys_root_prop. destruct (H1 n') as [ p H5 ]. eapply eq_sys_find_root; eauto.
  * rewrite H4 in H. subst n'. constructor; auto.
    apply is_eq_sys_root_prop. destruct (H1 n) as [ p H5 ]. eapply eq_sys_find_root; eauto.
Qed.

Lemma eq_sys_union_roots_size s x y ns (H1 : eq_sys_wf s) (H2 : In x ns) (H3 : In y ns)
                              (H4 : forall z, in_eq_sys_vars z s -> In z ns)
                            : var_set_size (eq_sys_roots (snd (eq_sys_union s x y)) ns)
                           <= var_set_size (eq_sys_roots s ns).
Proof.
  apply NoDup_incl_length. apply eq_sys_roots_distinct.
  intros z H. apply eq_sys_roots_all in H. destruct H as [ H5 H6 ].
  apply eq_sys_union_roots in H5. apply eq_sys_roots_all; auto. constructor; auto.
  apply eq_sys_union_wf. auto.
  intros. apply eq_sys_union_vars in H5; auto. destruct H5; auto. destruct H5.
  * destruct (eq_sys_find_in_vars s x). apply H4. rewrite H5. auto. rewrite H6 in H5. subst x. auto.
  * destruct (eq_sys_find_in_vars s y). apply H4. rewrite H5. auto. rewrite H6 in H5. subst y. auto.
Qed.

Lemma eq_sys_union_some_roots_size_aux s x y ns
                                   (H1 : eq_sys_wf s) (H2 : eq_sys_wf ((x, LinkESNode y) :: s))
                                   (H3 : is_eq_sys_root_of x s ns) (H4 : is_eq_sys_root_of y s ns)
                                   (H5 : forall z, in_eq_sys_vars z s -> In z ns)
                                 : var_set_size (eq_sys_roots s ns)
                                 = S (var_set_size (eq_sys_roots ((x, LinkESNode y) :: s) ns)).
Proof.
  refine (_ : _ = length (x :: eq_sys_roots _ ns)).
  apply NoDup_length; [ | constructor | .. ]; try apply eq_sys_roots_distinct. {
    intro. apply eq_sys_roots_are_roots in H; auto.
    destruct H as [ H | [ t H ] ]; simpl in H; destruct (name_eq_dec x x);
      try apply n0; auto; inversion H.
  }
  intro z. constructor; intro.
  * apply eq_sys_roots_all in H; auto. destruct H.
    remember (name_eq_dec z x) as cond. symmetry in Heqcond. destruct cond.
    subst. left. auto. right. apply eq_sys_roots_all; auto. {
      intros. apply in_eq_sys_vars_add_link in H6.
      destruct H6 as [ H6 | [ H6 | H6 ] ]; subst; auto.
      apply H3. apply H4.
    }
    constructor; auto. destruct H as [ H | [ t H ] ].
    left. simpl. rewrite Heqcond. auto.
    right. simpl. rewrite Heqcond. eexists. eauto.
  * good_inversion H.
    + apply eq_sys_roots_all; auto.
    + apply eq_sys_roots_all; auto. apply eq_sys_roots_all in H0; auto.
      destruct H0. constructor; auto.
      destruct H as [ H | [ t H ] ]; simpl in H; destruct (name_eq_dec z x); subst.
      1, 3: inversion H. left. auto. right. eexists. eauto.
      intros. apply in_eq_sys_vars_add_link in H6.
      destruct H6 as [ H6 | [ H6 | H6 ] ]; subst; auto.
      apply H3. apply H4.
Qed.

Lemma eq_sys_union_some_roots_size s s' x y ns ts (H1 : eq_sys_wf s) (H2 : In x ns) (H3 : In y ns)
                                   (H4 : forall z, in_eq_sys_vars z s -> In z ns)
                                   (H5 : eq_sys_union s x y = (Some ts, s'))
                                 : var_set_size (eq_sys_roots s ns)
                                 = S (var_set_size (eq_sys_roots s' ns)).
Proof.
  assert (eq_sys_wf s'). {
    unshelve erewrite (_ : s' = snd (eq_sys_union s x y)). rewrite H5. auto.
    apply eq_sys_union_wf. auto.
  }
  unfold eq_sys_union in H5.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  remember (name_eq_dec x' y') as cond. symmetry in Heqcond. destruct cond. inversion H5.
  assert (Hx' : is_eq_sys_root_of x' s ns). {
    constructor.
    * apply is_eq_sys_root_prop. destruct (H1 x) as [ p H6 ].
      eapply eq_sys_find_root; eauto. rewrite Heqresx. auto.
    * destruct (eq_sys_find_in_vars s x); rewrite Heqresx in H0. apply H4. auto. subst. auto.
  }
  assert (Hy' : is_eq_sys_root_of y' s ns). {
    constructor.
    * apply is_eq_sys_root_prop. destruct (H1 y) as [ p H6 ].
      eapply eq_sys_find_root; eauto. rewrite Heqresy. auto.
    * destruct (eq_sys_find_in_vars s y); rewrite Heqresy in H0. apply H4. auto. subst. auto.
  }
  destruct t2 as [ t2 | ]; good_inversion H5; apply eq_sys_union_some_roots_size_aux; auto.
Qed.


(* Unification *)

Definition unification_state : Set := eq_sys * nat.

Definition unification_state_wf (s : unification_state) : Prop :=
  eq_sys_wf (fst s) /\ (forall x, in_eq_sys_vars x (fst s) -> x < snd s).

Lemma initial_unification_state_wf k : unification_state_wf (eq_sys_trivial, k).
Proof.
  constructor. apply eq_sys_trivial_wf.
  intros. destruct H as [ H | [ H | H ] ].
  * apply in_eq_sys_dom_prop in H. inversion H.
  * destruct H as [ t [ [ y H1 ] H2 ] ]. inversion H1.
  * destruct H as [ y H ]. inversion H.
Qed.

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
  | (_, Some t') => Some ((s, n), [(term_head_to_term t', t)])
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
                          /\ forall x, In x (fv_terms_list ts) -> x < snd s'.
Proof.
  destruct t1 as [ x | c1 | c1 l1 r1 ]; destruct t2 as [ y | c2 | c2 l2 r2 ]; simpl in H4.
  * remember (eq_sys_union s x y) as res. symmetry in Heqres. destruct res as [ ts' s1 ].
    assert (s' = (s1, n)). destruct ts' as [ [ t1 t2 ] | ]; good_inversion H4; auto.
    subst. unshelve erewrite (_ : s1 = snd (eq_sys_union s x y)). rewrite Heqres. auto.
    constructor; [ | constructor ]; auto. clear H4 Heqres. repeat constructor.
    - apply eq_sys_union_wf. apply H1.
    - intros x' H. apply eq_sys_union_vars in H; [ | apply H1 ].
      destruct H as [ H | H ]. apply H1 in H. auto. destruct H as [ H | H ]; subst.
      + destruct (eq_sys_find_in_vars s x). apply H1. auto. rewrite H. apply H2. left. auto.
      + destruct (eq_sys_find_in_vars s y). apply H1. auto. rewrite H. apply H3. left. auto.
    - intros. simpl. destruct ts' as [ [ t1 t2 ] | ]; good_inversion H4; [ | inversion H ].
      assert (fst (eq_sys_union s x y) = Some (t1, t2)). rewrite Heqres. auto. clear Heqres.
      apply eq_sys_union_terms in H0. apply fv_terms_list_In in H. destruct H as [ ts' [ H H4 ] ].
      good_inversion H; [ | inversion H5 ]. destruct H0. apply fv_terms_In in H4. simpl in H4.
      destruct H4; rewrite <- fv_term_head_prop in H4.
      + apply H1. right. left. exists t1. constructor; auto.
      + apply H1. right. left. exists t2. constructor; auto.
  * remember (eq_sys_find s x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H4;
      [ constructor; auto; constructor
      | repeat constructor
      ]; auto.
    - intros y H. apply fv_terms_list_In in H. destruct H as [ ts' H ]. destruct H.
      good_inversion H; [ | inversion H4 ]. apply fv_terms_In in H0. destruct H0; [ | inversion H ].
      simpl in H. rewrite <- fv_term_head_prop in H. apply eq_sys_find_some in Heqres.
      apply H1. right. left. eexists. constructor; eauto. eexists. eauto.
    - apply eq_sys_bind_wf. apply H1.
    - intros y H. apply eq_sys_bind_vars in H. destruct H. apply H1. auto.
      destruct H; [ | inversion H ]. destruct (eq_sys_find_in_vars s x).
      apply H1. rewrite H. auto. apply H2. left. congruence.
  * remember (eq_sys_find s x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H4;
      [ constructor; auto; constructor
      | constructor; constructor
      ]; auto.
    - intros y H. simpl. apply fv_terms_list_In in H. destruct H as [ ts' H ]. destruct H.
      good_inversion H; [ | inversion H4 ]. apply fv_terms_In in H0. destruct H0; [ | apply H3; auto ].
      simpl in H. rewrite <- fv_term_head_prop in H. apply eq_sys_find_some in Heqres.
      apply H1. right. left. eexists. constructor; eauto. eexists. eauto.
    - apply eq_sys_bind_wf. apply H1.
    - intros y H. apply eq_sys_bind_vars in H. destruct H. apply H1 in H. simpl in *. lia.
      destruct H; subst; simpl. destruct (eq_sys_find_in_vars s x).
      + apply H1 in H. simpl in *. lia.
      + eapply (PeanoNat.Nat.lt_le_trans). apply H2. left. auto. lia.
      + apply set_add_elim in H. destruct H. lia. apply set_add_elim in H. destruct H. lia.
        inversion H.
    - simpl. lia.
    - intros y H. simpl. apply fv_terms_list_In in H. destruct H as [ ts' H ]. destruct H.
      good_inversion H; [ | good_inversion H4; [ | inversion H ] ]; apply fv_terms_In in H0.
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

Lemma rt_unify_wf t1 t2 s s' (H1 : unification_state_wf s)
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

Theorem rt_unify_determined t1 t2 s s1 s2 (H1 : s == t1 |_| t2 => s1) (H2 : s == t1 |_| t2 => s2)
                          : s1 = s2
with rt_unify_many_determined ts s s1 s2 (H1 : rt_unify_many s ts s1) (H2 : rt_unify_many s ts s2)
                            : s1 = s2.
Proof.
  * good_inversion H1; good_inversion H2; auto.
    - rewrite H4 in H. good_inversion H. eapply rt_unify_many_determined; eauto.
    - rewrite H7 in H. inversion H.
    - rewrite H3 in H. inversion H.
  * good_inversion H1; good_inversion H2; auto.
    - apply (rt_unify_determined _ _ _ (Some s3)) in H7; [ | auto ]. good_inversion H7.
      eapply rt_unify_many_determined; eauto.
    - absurd (Some s3 = None). intro. inversion H1. eapply rt_unify_determined; eauto.
    - absurd (None = Some s0). intro. inversion H0. eapply rt_unify_determined; eauto.
Qed.

Definition unification_state_size (s : unification_state) :=
  var_set_size (eq_sys_roots (fst s) (first_nats (snd s))).

Lemma unification_state_size_union s n x y (H1 : x < n) (H2 : y < n)
                                   (H3 : unification_state_wf (s, n))
                                 : unification_state_size (snd (eq_sys_union s x y), n)
                                <= unification_state_size (s, n).
Proof.
  apply eq_sys_union_roots_size. apply H3.
  1, 2: apply first_nats_prop; auto.
  intros. apply first_nats_prop. apply H3. auto.
Qed.

Lemma unification_state_size_union_some s s' n x y ts (H1 : x < n) (H2 : y < n)
                                        (H3 : unification_state_wf (s, n))
                                        (H4 : eq_sys_union s x y = (Some ts, s'))
                                      : unification_state_size (s, n)
                                      = S (unification_state_size (s', n)).
Proof.
  eapply eq_sys_union_some_roots_size; eauto. apply H3.
  1, 2: apply first_nats_prop; auto.
  intros. apply first_nats_prop. apply H3. auto.
Qed.

Lemma rt_unify_vars_terminates x y s n (H1 : unification_state_wf (s, n)) (H2 : x < n) (H3 : y < n)
                             : { s' | (s, n) == Var x |_| Var y => s' }.
Proof.
  set (P := fun m => forall x y s n,
                            unification_state_wf (s, n) -> x < n -> y < n
                         -> unification_state_size (s, n) = m
                         -> { s' | (s, n) == Var x |_| Var y => s'
                                /\ forall s1 n1, s' = Some (s1, n1)
                                              -> unification_state_size (s1, n1) <= m
                                              /\ n1 = n }).
  assert (P (unification_state_size (s, n))). {
    apply (well_founded_induction PeanoNat.Nat.lt_wf_0). clear x y s n H1 H2 H3.
    subst P. simpl. intros m IHm x y s n H1 H2 H3 H4. subst m.
    remember (eq_sys_union s x y) as res. symmetry in Heqres. destruct res as [ ts s' ].
    assert (Hs' : unification_state_wf (s', n)). {
      unshelve erewrite (_ : s' = snd (eq_sys_union s x y)). rewrite Heqres. auto.
      constructor. apply eq_sys_union_wf. apply H1.
      intros. apply eq_sys_union_vars in H; [ | apply H1 ].
      destruct H. apply H1 in H. auto. destruct H.
      * destruct (eq_sys_find_in_vars s x). apply H1. subst. auto.
        rewrite H0 in H. subst. apply H2.
      * destruct (eq_sys_find_in_vars s y). apply H1. subst. auto.
        rewrite H0 in H. subst. apply H3.
    }
    destruct ts as [ [ t1 t2 ] | ].
    * assert (Hm : unification_state_size (s', n) < unification_state_size (s, n)). {
        erewrite (unification_state_size_union_some s s' n x y); eauto.
      }
      destruct t1 as [ c1 | c1 l1 r1 ]; destruct t2 as [ c2 | c2 l2 r2 ].
      - remember (name_eq_dec c1 c2) as cond. symmetry in Heqcond. destruct cond.
        + exists (Some (s', n)). constructor.
          econstructor. simpl. rewrite Heqres. auto. econstructor.
          econstructor. simpl. rewrite Heqcond. auto. constructor. constructor.
          intros. good_inversion H. constructor; auto. lia.
        + exists None. constructor.
          econstructor. simpl. rewrite Heqres. auto. constructor.
          constructor. simpl. rewrite Heqcond. auto.
          intros. inversion H.
      - exists None. constructor. econstructor. simpl. rewrite Heqres. auto.
        constructor. constructor. auto.
        intros. inversion H.
      - exists None. constructor. econstructor. simpl. rewrite Heqres. auto.
        constructor. constructor. auto.
        intros. inversion H.
      - remember (name_eq_dec c1 c2) as cond. symmetry in Heqcond. destruct cond.
        + destruct (eq_sys_union_terms s x y (ConHead c1 l1 r1) (ConHead c2 l2 r2)).
          rewrite Heqres. auto.
          edestruct (IHm (unification_state_size (s', n))) as [ s2 [ Hs2 Hn2 ] ]. 1, 2, 5: eauto.
          3: {
            destruct s2 as [ [ s2 n2 ] | ].
            * set (Hs2' := Hs2). apply rt_unify_wf in Hs2'; auto.
              edestruct (IHm (unification_state_size (s2, n2))) as [ s3 [ Hs3 Hn3 ] ]. 5: eauto.
              5: {
                destruct s3 as [ s3 | ].
                * exists (Some s3). constructor.
                  - econstructor. simpl. rewrite Heqres. auto. econstructor.
                    econstructor. simpl. rewrite Heqcond. auto.
                    econstructor. apply Hs2. econstructor. apply Hs3.
                    constructor. constructor.
                  - intros. good_inversion H4. edestruct Hn2. auto. edestruct Hn3. auto.
                    constructor. etransitivity. apply H6. etransitivity. apply H4. lia.
                    congruence.
                * exists None. constructor.
                  - econstructor. simpl. rewrite Heqres. auto. constructor.
                    econstructor. simpl. rewrite Heqcond. auto.
                    econstructor. apply Hs2. constructor. auto.
                  - intros. inversion H4.
              }
              - eapply PeanoNat.Nat.le_lt_trans. apply Hn2. auto. auto.
              - apply Hs2'.
              - eapply PeanoNat.Nat.lt_le_trans. apply H1. right. left.
                eexists. constructor. apply H. apply set_add_intro2. auto.
                apply Hs2'.
              - eapply PeanoNat.Nat.lt_le_trans. apply H1. right. left.
                eexists. constructor. apply H0. apply set_add_intro2. auto.
                apply Hs2'.
              - intros. apply fv_terms_In in H4. simpl in H4. destruct H4.
                good_inversion H4; [ | inversion H5 ]. apply H1. right. left. eexists.
                constructor. apply H. apply set_add_intro1. apply set_add_intro2. auto.
                good_inversion H4; [ | inversion H5 ]. apply H1. right. left. eexists.
                constructor. apply H0. apply set_add_intro1. apply set_add_intro2. auto.
            * exists None. constructor.
              - econstructor. simpl. rewrite Heqres. auto. constructor.
                econstructor. simpl. rewrite Heqcond. auto. constructor. apply Hs2.
              - intros. inversion H4.
          }
          apply H1. right. left. eexists. constructor. apply H.
          apply set_add_intro1. apply set_add_intro2. auto.
          apply H1. right. left. eexists. constructor. apply H0.
          apply set_add_intro1. apply set_add_intro2. auto.
        + exists None. constructor.
          econstructor. simpl. rewrite Heqres. auto. constructor.
          constructor. simpl. rewrite Heqcond. auto.
          intros. inversion H.
      * exists (Some (s', n)). constructor.
        + econstructor. simpl. rewrite Heqres. auto. constructor.
        + intros. good_inversion H. constructor; auto.
          unshelve erewrite (_ : s1 = snd (eq_sys_union s x y)). rewrite Heqres. auto.
          apply (unification_state_size_union s n1 x y); auto.
  }
  edestruct (H x y) as [ s' [ H0 _ ] ]; eauto.
Qed.

Theorem rt_unify_terminates t1 t2 s n (H1 : unification_state_wf (s, n))
                            (H2 : forall x, In x (fv_terms (t1, t2)) -> x < n)
                          : { s' | (s, n) == t1 |_| t2 => s' }.
Proof.
  set (P := fun ts => forall s n, unification_state_wf (s, n)
                               -> (forall x, In x (fv_terms ts) -> x < n)
                               -> { s' | (s, n) == fst ts |_| snd ts => s' }).
  assert (P (t1, t2)). {
    apply (well_founded_induction terms_height_less_wf). clear t1 t2 s n H1 H2.
    subst P. simpl. intros ts IHts s n H1 H2. destruct ts as [ t1 t2 ]. simpl in *.
    destruct t1 as [ x | c1 | c1 l1 r1 ]; destruct t2 as [ y | c2 | c2 l2 r2 ].
    * apply rt_unify_vars_terminates. auto.
      apply H2. apply set_add_intro1. apply set_add_intro2. auto.
      apply H2. apply set_add_intro2. auto.
    * remember (eq_sys_find s x) as res. symmetry in Heqres.
      destruct res as [ x' [ [ c1 | c1 l1 r1 ] | ] ].
      remember (name_eq_dec c1 c2) as cond. symmetry in Heqcond. destruct cond.
      - exists (Some (s, n)). econstructor. simpl. rewrite Heqres. auto. econstructor.
        econstructor. simpl. rewrite Heqcond. auto. constructor. constructor.
      - exists None. econstructor. simpl. rewrite Heqres. auto. constructor.
        constructor. simpl. rewrite Heqcond. auto.
      - exists None. econstructor. simpl. rewrite Heqres. auto. constructor. constructor. auto.
      - exists (Some (eq_sys_bind s x (CstHead c2), n)).
        econstructor. simpl. rewrite Heqres. auto. constructor.
    * remember (eq_sys_find s x) as res. symmetry in Heqres.
      destruct res as [ x' [ [ c1 | c1 l1 r1 ] | ] ].
      2: remember (name_eq_dec c1 c2) as cond; symmetry in Heqcond; destruct cond.
      - exists None. econstructor. simpl. rewrite Heqres. auto. constructor. constructor. auto.
      - edestruct (IHts (Var l1, l2)) as [ s1 Hs1 ].
        4: {
          destruct s1 as [ [ s1 n1 ] | ].
          * set (Hs1' := Hs1). apply rt_unify_wf in Hs1'; [ | apply H1 | ].
            edestruct (IHts (Var r1, r2)) as [ s2 Hs2 ].
            4: {
              destruct s2 as [ s2 | ].
              * exists (Some s2). econstructor. simpl. rewrite Heqres. auto. econstructor.
                econstructor. simpl. rewrite Heqcond. auto. econstructor.
                apply Hs1. econstructor. apply Hs2. constructor. constructor.
              * exists None. econstructor. simpl. rewrite Heqres. auto. constructor.
                econstructor. simpl. rewrite Heqcond. auto. econstructor.
                apply Hs1. constructor. apply Hs2.
            }
            - unfold terms_height_less. unfold terms_height. simpl. lia.
            - apply Hs1'.
            - intros z H. apply fv_terms_In in H. simpl in H.
              destruct H. destruct H; [ | inversion H ].
              + eapply PeanoNat.Nat.lt_le_trans. apply H1. right. left. eexists. constructor.
                eapply eq_sys_find_in_rhs. simpl. rewrite Heqres. simpl. auto.
                apply set_add_intro2. auto. apply Hs1'.
              + eapply PeanoNat.Nat.lt_le_trans. apply H2. apply fv_terms_In. right.
                apply set_union_intro2. auto. apply Hs1'.
            - intros z H. apply fv_terms_In in H. simpl in *.
              destruct H. destruct H; [ | inversion H ].
              + apply H1. right. left. eexists. constructor.
                eapply eq_sys_find_in_rhs. simpl. rewrite Heqres. simpl. auto.
                apply set_add_intro1. apply set_add_intro2. auto.
              + apply H2. apply fv_terms_In. right. apply set_union_intro1. auto.
          * exists None. econstructor. simpl. rewrite Heqres. auto. constructor.
            econstructor. simpl. rewrite Heqcond. auto. constructor. apply Hs1.
        }
        + unfold terms_height_less. unfold terms_height. simpl. lia.
        + auto.
        + intros z H. apply fv_terms_In in H. simpl in H.
          destruct H. destruct H; [ | inversion H ].
          ** apply H1. right. left. eexists. constructor.
             eapply eq_sys_find_in_rhs. simpl. rewrite Heqres. simpl. auto.
             apply set_add_intro1. apply set_add_intro2. auto.
          ** apply H2. apply fv_terms_In. right. apply set_union_intro1. auto.
      - exists None. econstructor. simpl. rewrite Heqres. auto. constructor.
        constructor. simpl. rewrite Heqcond. auto.
      - assert (Hs' : unification_state_wf (eq_sys_bind s x (ConHead c2 n (S n)), S (S n))). {
          constructor. apply eq_sys_bind_wf. apply H1.
          simpl. intros z H. apply eq_sys_bind_vars in H. destruct H as [ H | [ H | H ] ].
          * apply (PeanoNat.Nat.lt_le_trans _ n); try lia. apply H1. auto.
          * apply (PeanoNat.Nat.lt_le_trans _ n); try lia.
            destruct (eq_sys_find_in_vars s x). apply H1. subst. auto.
            apply H2. apply fv_terms_In. left. apply set_add_intro2. congruence.
          * apply set_add_elim in H.
            destruct H; [ | apply set_add_elim in H; destruct H ]; try lia.
            inversion H.
        }
        edestruct (IHts (Var n, l2)) as [ s1 Hs1 ].
        4: {
          destruct s1 as [ [ s1 n1 ] | ].
          * set (Hs1' := Hs1). apply rt_unify_wf in Hs1'.
            edestruct (IHts (Var (S n), r2)) as [ s2 Hs2 ].
            4: {
              destruct s2 as [ s2 | ].
              * exists (Some s2). econstructor. simpl. rewrite Heqres. auto. econstructor.
                apply Hs1. econstructor. apply Hs2. constructor.
              * exists None. econstructor. simpl. rewrite Heqres. auto. econstructor.
                apply Hs1. constructor. apply Hs2.
            }
            - unfold terms_height_less. unfold terms_height. simpl. lia.
            - apply Hs1'.
            - intros z H. apply fv_terms_In in H. simpl in H.
              destruct H. destruct H; [ | inversion H ].
              all: apply (PeanoNat.Nat.lt_le_trans _ (S (S n))); [ | apply Hs1' ].
              lia.
              eapply PeanoNat.Nat.lt_le_trans. apply H2. apply fv_terms_In. right.
              apply set_union_intro2. auto. lia.
            - auto.
            - intros z H. apply set_union_elim in H. simpl in *.
              destruct H. destruct H; [ | inversion H ]. lia.
              eapply PeanoNat.Nat.lt_le_trans. apply H2. apply fv_terms_In. right.
              apply set_union_intro1. auto. lia.
          * exists None. econstructor. simpl. rewrite Heqres. auto. constructor. apply Hs1.
        }
        + unfold terms_height_less. unfold terms_height. simpl. lia.
        + auto.
        + intros z H. apply fv_terms_In in H. simpl in H.
          destruct H. destruct H; [ | inversion H ]. lia.
          eapply PeanoNat.Nat.lt_le_trans. apply H2. apply fv_terms_In. right.
          apply set_union_intro1. auto. lia.
    * remember (eq_sys_find s y) as res. symmetry in Heqres.
      destruct res as [ y' [ [ c2 | c2 l2 r2 ] | ] ].
      remember (name_eq_dec c2 c1) as cond. symmetry in Heqcond. destruct cond.
      - exists (Some (s, n)). econstructor. simpl. auto. econstructor.
        econstructor. simpl. rewrite Heqres. auto. econstructor.
        econstructor. simpl. rewrite Heqcond. auto. constructor. constructor. constructor.
      - exists None. econstructor. simpl. auto. constructor.
        econstructor. simpl. rewrite Heqres. auto. constructor.
        constructor. simpl. rewrite Heqcond. auto.
      - exists None. econstructor. simpl. auto. constructor.
        econstructor. simpl. rewrite Heqres. auto. constructor. constructor. auto.
      - exists (Some (eq_sys_bind s y (CstHead c1), n)). econstructor. simpl. auto. econstructor.
        econstructor. simpl. rewrite Heqres. auto. constructor. constructor.
    * remember (name_eq_dec c1 c2) as cond. symmetry in Heqcond. destruct cond.
      - exists (Some (s, n)). econstructor. simpl. rewrite Heqcond. auto. constructor.
      - exists None. constructor. simpl. rewrite Heqcond. auto.
    * exists None. constructor. auto.
    * remember (eq_sys_find s y) as res. symmetry in Heqres.
      destruct res as [ y' [ [ c2 | c2 l2 r2 ] | ] ].
      2: remember (name_eq_dec c2 c1) as cond; symmetry in Heqcond; destruct cond.
      - exists None. econstructor. simpl. auto. constructor.
        econstructor. simpl. rewrite Heqres. auto. constructor. constructor. auto.
      - edestruct (IHts (Var l2, l1)) as [ s1 Hs1 ].
        4: {
          destruct s1 as [ [ s1 n1 ] | ].
          * set (Hs1' := Hs1). apply rt_unify_wf in Hs1'; [ | apply H1 | ].
            edestruct (IHts (Var r2, r1)) as [ s2 Hs2 ].
            4: {
              destruct s2 as [ s2 | ].
              * exists (Some s2). econstructor. simpl. auto. econstructor.
                econstructor. simpl. rewrite Heqres. auto. econstructor.
                econstructor. simpl. rewrite Heqcond. auto. econstructor.
                apply Hs1. econstructor. apply Hs2. constructor. constructor. constructor.
              * exists None. econstructor. simpl. auto. constructor.
                econstructor. simpl. rewrite Heqres. auto. constructor.
                econstructor. simpl. rewrite Heqcond. auto. econstructor.
                apply Hs1. constructor. apply Hs2.
            }
            - unfold terms_height_less. unfold terms_height. simpl. lia.
            - apply Hs1'.
            - intros z H. apply fv_terms_In in H. simpl in H.
              destruct H. destruct H; [ | inversion H ].
              + eapply PeanoNat.Nat.lt_le_trans. apply H1. right. left. eexists. constructor.
                eapply eq_sys_find_in_rhs. simpl. rewrite Heqres. simpl. auto.
                apply set_add_intro2. auto. apply Hs1'.
              + eapply PeanoNat.Nat.lt_le_trans. apply H2. apply fv_terms_In. left.
                apply set_union_intro2. auto. apply Hs1'.
            - intros z H. apply fv_terms_In in H. simpl in *.
              destruct H. destruct H; [ | inversion H ].
              + apply H1. right. left. eexists. constructor.
                eapply eq_sys_find_in_rhs. simpl. rewrite Heqres. simpl. auto.
                apply set_add_intro1. apply set_add_intro2. auto.
              + apply H2. apply fv_terms_In. left. apply set_union_intro1. auto.
          * exists None. econstructor. simpl. auto. constructor.
            econstructor. simpl. rewrite Heqres. auto. constructor.
            econstructor. simpl. rewrite Heqcond. auto. constructor. apply Hs1.
        }
        + unfold terms_height_less. unfold terms_height. simpl. lia.
        + auto.
        + intros z H. apply fv_terms_In in H. simpl in H.
          destruct H. destruct H; [ | inversion H ].
          ** apply H1. right. left. eexists. constructor.
             eapply eq_sys_find_in_rhs. simpl. rewrite Heqres. simpl. auto.
             apply set_add_intro1. apply set_add_intro2. auto.
          ** apply H2. apply fv_terms_In. left. apply set_union_intro1. auto.
      - exists None. econstructor. simpl. auto. constructor.
        econstructor. simpl. rewrite Heqres. auto. constructor.
        constructor. simpl. rewrite Heqcond. auto.
      - assert (Hs' : unification_state_wf (eq_sys_bind s y (ConHead c1 n (S n)), S (S n))). {
          constructor. apply eq_sys_bind_wf. apply H1.
          simpl. intros z H. apply eq_sys_bind_vars in H. destruct H as [ H | [ H | H ] ].
          * apply (PeanoNat.Nat.lt_le_trans _ n); try lia. apply H1. auto.
          * apply (PeanoNat.Nat.lt_le_trans _ n); try lia.
            destruct (eq_sys_find_in_vars s y). apply H1. subst. auto.
            apply H2. apply fv_terms_In. right. apply set_add_intro2. congruence.
          * apply set_add_elim in H.
            destruct H; [ | apply set_add_elim in H; destruct H ]; try lia.
            inversion H.
        }
        edestruct (IHts (Var n, l1)) as [ s1 Hs1 ].
        4: {
          destruct s1 as [ [ s1 n1 ] | ].
          * set (Hs1' := Hs1). apply rt_unify_wf in Hs1'.
            edestruct (IHts (Var (S n), r1)) as [ s2 Hs2 ].
            4: {
              destruct s2 as [ s2 | ].
              * exists (Some s2). econstructor. simpl. auto. econstructor.
                econstructor. simpl. rewrite Heqres. auto. econstructor.
                apply Hs1. econstructor. apply Hs2. constructor. constructor.
              * exists None. econstructor. simpl. auto. constructor.
                econstructor. simpl. rewrite Heqres. auto. econstructor.
                apply Hs1. constructor. apply Hs2.
            }
            - unfold terms_height_less. unfold terms_height. simpl. lia.
            - apply Hs1'.
            - intros z H. apply fv_terms_In in H. simpl in H.
              destruct H. destruct H; [ | inversion H ].
              all: apply (PeanoNat.Nat.lt_le_trans _ (S (S n))); [ | apply Hs1' ].
              lia.
              eapply PeanoNat.Nat.lt_le_trans. apply H2. apply fv_terms_In. left.
              apply set_union_intro2. auto. lia.
            - auto.
            - intros z H. apply set_union_elim in H. simpl in *.
              destruct H. destruct H; [ | inversion H ]. lia.
              eapply PeanoNat.Nat.lt_le_trans. apply H2. apply fv_terms_In. left.
              apply set_union_intro1. auto. lia.
          * exists None. econstructor. simpl. auto. constructor.
            econstructor. simpl. rewrite Heqres. auto. constructor. apply Hs1.
        }
        + unfold terms_height_less. unfold terms_height. simpl. lia.
        + auto.
        + intros z H. apply fv_terms_In in H. simpl in H.
          destruct H. destruct H; [ | inversion H ]. lia.
          eapply PeanoNat.Nat.lt_le_trans. apply H2. apply fv_terms_In. left.
          apply set_union_intro1. auto. lia.
    * exists None. constructor. auto.
    * remember (name_eq_dec c1 c2) as cond. symmetry in Heqcond. destruct cond.
      - edestruct (IHts (l1, l2)) as [ s1 Hs1 ].
        4: {
          destruct s1 as [ [ s1 n1 ] | ].
          * set (Hs1' := Hs1). apply rt_unify_wf in Hs1'.
            edestruct (IHts (r1, r2)) as [ s2 Hs2 ].
            4: {
              destruct s2 as [ s2 | ].
              * exists (Some s2). econstructor. simpl. rewrite Heqcond. auto. econstructor.
                apply Hs1. econstructor. apply Hs2. constructor.
              * exists None. econstructor. simpl. rewrite Heqcond. auto. econstructor.
                apply Hs1. constructor. apply Hs2.
            }
            - unfold terms_height_less. unfold terms_height. simpl. lia.
            - apply Hs1'.
            - intros z H. apply fv_terms_In in H. simpl in H.
              destruct H; (apply (PeanoNat.Nat.lt_le_trans _ n);
                [ apply H2; apply fv_terms_In
                | apply Hs1'
                ]); [ left | right ]; apply set_union_intro2; auto.
            - auto.
            - intros z H. apply H2. apply fv_terms_In. apply fv_terms_In in H.
              destruct H; [ left | right ]; apply set_union_intro1; auto.
          * exists None. econstructor. simpl. rewrite Heqcond. auto. constructor. apply Hs1.
        }
        + unfold terms_height_less. unfold terms_height. simpl. lia.
        + auto.
        + intros z H. apply H2. apply fv_terms_In. apply fv_terms_In in H.
          destruct H; [ left | right ]; apply set_union_intro1; auto.
      - exists None. constructor. simpl. rewrite Heqcond. auto.
  }
  apply H; auto.
Qed.


(*
(* Equation System Interpretation *)

Definition eq_sys_interp n : Set :=
  forall i, i < n -> var_set * option term_head.

Definition eq_sys_interp_trivial n : eq_sys_interp n := fun x _ => ([x], None).

Definition eq_sys_interp_wf {n} (int : eq_sys_interp n) : Prop :=
  (forall i H1 H2, int i H1 = int i H2)
/\ (forall i H, fst (int i H) <> var_set_empty)
/\ (forall x i j Hi Hj, In x (fst (int i Hi)) -> In x (fst (int j Hj)) -> i = j).

Lemma eq_sys_interp_trivial_wf n : eq_sys_interp_wf (eq_sys_interp_trivial n).
Proof.
  repeat constructor; auto; intros.
  * intro. inversion H0.
  * simpl in *. destruct H. destruct H0. subst. auto. all: exfalso; auto.
Qed.

Definition eq_sys_interp_soundness s {n} (int : eq_sys_interp n) : Prop :=
  (forall x i H, In x (fst (int i H)) -> In (fst (eq_sys_find s x)) (fst (int i H))
                                      /\ snd (eq_sys_find s x) = snd (int i H)
                                      /\ in_eq_sys_dom x s)
/\ (forall x y i H, In x (fst (int i H)) -> In y (fst (int i H))
                 -> fst (eq_sys_find s x) = fst (eq_sys_find s y)).

Definition eq_sys_interp_completeness s {n} (int : eq_sys_interp n) : Prop :=
  forall x, in_eq_sys_dom x s -> exists i H, In x (fst (int i H)).

Definition is_interp_of_eq_sys {n} (int : eq_sys_interp n) s : Prop :=
  eq_sys_interp_wf int /\ eq_sys_interp_soundness s int /\ eq_sys_interp_completeness s int.

Lemma eq_sys_interp_trivial_is_of_trivial
  : is_interp_of_eq_sys (eq_sys_interp_trivial 0) eq_sys_trivial.
Proof.
  constructor. apply eq_sys_interp_trivial_wf. constructor. constructor.
  intros x i H. inversion H. intros x y i H. inversion H.
  intros x [ node Hx ]. inversion Hx.
Qed.

(*
Lemma eq_sys_interp_lookup s n (int : eq_sys_interp n) x y
                           (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                           (H3 : eq_sys_lookup s x = Some (LinkESNode y))
                         : exists i Hi, In x (fst (int i Hi)) /\ In y (fst (int i Hi)).
Proof.
  assert (Hx1 : in_eq_sys_dom x s). econstructor. eauto.
  assert (Hx2 : exists p, eq_sys_name_wf s x p). apply H1. auto.
  destruct Hx2 as [ px Hx2 ].
  assert (Hy1 : in_eq_sys_dom y s).
  good_inversion Hx2; rewrite H3 in H; good_inversion H.
  good_inversion H0; econstructor; eauto.
  assert (Hy2 : exists p, eq_sys_name_wf s y p). apply H1. auto.
  destruct Hy2 as [ py Hy2 ].
  destruct H2 as [ H4 [ H5 H6 ] ].
  apply H6 in Hx1, Hy1. destruct Hx1 as [ i [ Hi Hx1 ] ]. destruct Hy1 as [ j [ Hj Hy1 ] ].
  set (Hx1' := Hx1). set (Hy1' := Hy1).
  apply H5 in Hx1', Hy1'. destruct Hx1' as [ Hx3 [ Hx4 Hx5 ] ]. destruct Hy1' as [ Hy3 [ Hy4 Hy5 ] ].
  exists i. exists Hi. constructor. auto.
  erewrite eq_sys_find_link in Hx3; eauto.
  destruct H4 as [ H2 [ H4 H7 ] ].
  assert (i = j). eapply H7. apply Hx3. apply Hy3.
  generalize dependent Hi. rewrite H. intros. erewrite H2. eauto.
Qed.

Lemma eq_sys_interp_find_step' s n (int : eq_sys_interp n) x y i Hi
                               (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                               (H3 : eq_sys_find_step s x = Some (LinkESNode y))
                             : In x (fst (int i Hi)) <-> In y (fst (int i Hi)).
Proof.
  eapply eq_sys_interp_find_step in H3; eauto. destruct H3 as [ i' [ Hi' [ H3 H4 ] ] ].
  destruct H2 as [ [ H2 [ _ H5 ] ] _ ].
  constructor; intro.
  * eapply (H5 _ i) in H3; eauto. generalize dependent Hi. rewrite H3. intros. erewrite H2. eauto.
  * eapply (H5 _ i) in H4; eauto. generalize dependent Hi. rewrite H4. intros. erewrite H2. eauto.
Qed.

Definition eq_sys_interp_repr_var s {n} (int : eq_sys_interp n) i Hi : nat :=
match fst (int i Hi) with
| [] => 0
| (x::_) => fst (eq_sys_find s x)
end.

Lemma eq_sys_interp_repr_var_in s n (int : eq_sys_interp n) i Hi
                                (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                              : In (eq_sys_interp_repr_var s int i Hi) (fst (int i Hi)).
Proof.
  unfold eq_sys_interp_repr_var. remember (fst (int i Hi)) as ns. symmetry in Heqns.
  destruct ns as [ | x ns ]. apply H2 in Heqns. inversion Heqns. rewrite <- Heqns.
  apply H2. rewrite Heqns. left. auto.
Qed.

Lemma eq_sys_interp_repr_var_prop s n (int : eq_sys_interp n) i Hi x
                                  (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                                  (H3 : In x (fst (int i Hi)))
                                : fst (eq_sys_find s x) = eq_sys_interp_repr_var s int i Hi.
Proof.
  unfold eq_sys_interp_repr_var. remember (fst (int i Hi)) as ns. symmetry in Heqns.
  destruct ns as [ | y ns ]. apply H2 in Heqns. inversion Heqns. rewrite <- Heqns in *.
  eapply H2. eauto. rewrite Heqns. left. auto.
Qed.

Lemma eq_sys_interp_repr_var_root s n (int : eq_sys_interp n) i Hi
                                  (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                                : exists t, eq_sys_find_step s (eq_sys_interp_repr_var s int i Hi)
                                          = Some (RootESNode t).
Proof.
  unfold eq_sys_interp_repr_var. remember (fst (int i Hi)) as ns. symmetry in Heqns.
  destruct ns as [ | x ns ]. apply H2 in Heqns. inversion Heqns.
  assert (in_eq_sys_dom x s). eapply H2. rewrite Heqns. left. auto.
  apply H1 in H. destruct H as [ p H ]. eexists. eapply eq_sys_find_root. eauto.
Qed.

Definition eq_sys_interp_size_ind_step_sys s {n} (int : eq_sys_interp (S n)) : eq_sys :=
  eq_sys_dom_erase' s (fst (int n (le_n (S n)))).

Lemma eq_sys_interp_size_ind_step_sys_prop s n (int : eq_sys_interp (S n))
                                           (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                                         : eq_sys_wf (eq_sys_interp_size_ind_step_sys s int).
Proof.
  apply eq_sys_dom_erase'_wf. auto. intros n1 n2 H Hn2 Hn1. apply Hn2.
  eapply eq_sys_interp_find_step'; eauto.
Qed.

Lemma eq_sys_interp_size_ind_step_sys_find s n (int : eq_sys_interp (S n)) x i Hi
                                           (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                                           (H3 : In x (fst (int i (le_S _ _ Hi))))
                                         : eq_sys_find (eq_sys_interp_size_ind_step_sys s int) x
                                         = eq_sys_find s x.
Proof.
  set (H1' := H1). eapply eq_sys_interp_size_ind_step_sys_prop in H1'; eauto.
  destruct (H1 x) as [ p1 Hp1 ]. eapply H2. eauto.
  destruct (H1' x) as [ p2 Hp2 ].
  * apply in_eq_sys_dom_prop. apply eq_sys_dom_erase'_prop.
    constructor; auto. apply in_eq_sys_dom_prop. eapply H2. eauto.
    intro. absurd (i = n). lia. eapply H2; eauto.
  * eapply eq_sys_dom_erase'_find; auto; eauto.
Qed.

Definition eq_sys_interp_size_ind_step_interp {n} (int : eq_sys_interp (S n)) : eq_sys_interp n :=
  fun i Hi => int i (le_S _ _ Hi).

Lemma eq_sys_interp_size_ind_step_interp_prop s n (int : eq_sys_interp (S n))
                                              (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                                            : is_interp_of_eq_sys
                                              (eq_sys_interp_size_ind_step_interp int)
                                              (eq_sys_interp_size_ind_step_sys s int).
Proof.
  unfold eq_sys_interp_size_ind_step_interp. repeat constructor; simpl in *; intros.
  * apply H2.
  * apply H2.
  * eapply H2; eauto.
  * erewrite eq_sys_interp_size_ind_step_sys_find; eauto. apply H2. auto.
  * erewrite eq_sys_interp_size_ind_step_sys_find; eauto. apply H2. auto.
  * apply in_eq_sys_dom_prop. apply eq_sys_dom_erase'_prop. constructor.
    apply in_eq_sys_dom_prop. eapply H2. eauto. intro. absurd (i = n). lia.
    eapply H2; eauto.
  * erewrite eq_sys_interp_size_ind_step_sys_find; eauto.
    erewrite eq_sys_interp_size_ind_step_sys_find; eauto.
    eapply H2; eauto.
  * intros x Hx. apply in_eq_sys_dom_prop in Hx. apply eq_sys_dom_erase'_prop in Hx.
    destruct Hx as [ Hx H ]. apply in_eq_sys_dom_prop in Hx.
    destruct H2 as [ H2 [ H3 H4 ] ]. destruct (H4 x Hx) as [ i [ Hi H5 ] ]. exists i.
    assert (i < n) as Hi'. set (Hi' := Hi). good_inversion Hi'; auto. exfalso. apply H.
    destruct H2 as [ H2 [ _ _ ] ]. erewrite H2. eauto.
    exists Hi'. destruct H2 as [ H2 [ _ _ ] ]. erewrite H2. eauto.
Qed.

Lemma eq_sys_interp_size_ind (P : eq_sys -> forall n, eq_sys_interp n -> Prop)
                             (base : forall int, P eq_sys_trivial 0 int)
                             (step : forall s n (int : eq_sys_interp (S n)),
                                            eq_sys_wf s -> is_interp_of_eq_sys int s
                                         -> P (eq_sys_interp_size_ind_step_sys s int) n
                                              (eq_sys_interp_size_ind_step_interp int)
                                         -> P s (S n) int)
                             s n (int : eq_sys_interp n)
                             (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                           : P s n int.
Proof.
  generalize dependent int. generalize dependent s. induction n; intros.
  * destruct s as [ | [ n node ] s ]. apply base. destruct H2 as [ H2 [ H3 H4 ] ].
    destruct (H4 n) as [ i [ H _ ] ]. apply in_eq_sys_dom_prop. apply set_add_intro2. auto.
    inversion H.
  * apply step; auto. clear base step. apply IHn; clear IHn.
    - apply eq_sys_interp_size_ind_step_sys_prop; auto.
    - apply eq_sys_interp_size_ind_step_interp_prop; auto.
Qed.

Definition eq_sys_roots_hlp (s : eq_sys) (n : name) : bool :=
match eq_sys_find_step s n with
| Some (RootESNode _) => true
| _ => false
end.

Lemma eq_sys_roots_hlp_prop s n : eq_sys_roots_hlp s n = true
                              <-> exists t, eq_sys_find_step s n = Some (RootESNode t).
Proof.
  unfold eq_sys_roots_hlp.
  destruct (eq_sys_find_step s n) as [ [ t | n' ] | ]; constructor; intro; auto.
  eexists. auto. 2, 4: destruct H. all: inversion H.
Qed.

Definition eq_sys_roots (s : eq_sys) : var_set := filter (eq_sys_roots_hlp s) (eq_sys_dom s).

Lemma eq_sys_roots_prop s n : In n (eq_sys_roots s)
                          <-> exists t, eq_sys_find_step s n = Some (RootESNode t).
Proof.
  unfold eq_sys_roots. constructor; intro.
  * apply filter_In in H. destruct H. apply eq_sys_roots_hlp_prop in H0. auto.
  * apply filter_In. constructor. apply in_eq_sys_dom_prop. destruct H. econstructor. eauto.
    apply eq_sys_roots_hlp_prop. auto.
Qed.

Lemma eq_sys_roots_distinct s : NoDup (eq_sys_roots s).
Proof. apply NoDup_filter. auto. Qed.

Definition eq_sys_interp_size (s : eq_sys) := var_set_size (eq_sys_roots s).

Lemma eq_sys_interp_size_zero s (H1 : eq_sys_wf s) (H2 : eq_sys_interp_size s = 0)
                            : s = [].
Proof.
  destruct s as [ | [ n [ t | n' ] ] s ]; auto; unfold eq_sys_interp_size in H2.
  * absurd (var_set_size (eq_sys_roots ((n, RootESNode t) :: s)) > 0); try lia. clear H1 H2.
    apply (Nat.le_trans _ (length [n])). auto. apply NoDup_incl_length.
    apply NoDup_cons_iff. constructor; auto. apply NoDup_nil.
    intros x H. good_inversion H; [ | inversion H0 ]. apply eq_sys_roots_prop. exists t.
    simpl. destruct (name_eq_dec x x). auto. contradiction.
  * absurd (var_set_size (eq_sys_roots ((n, LinkESNode n') :: s)) > 0); try lia. clear H2.
    apply (Nat.le_trans _ (length [fst (eq_sys_find ((n, LinkESNode n') :: s) n)])). auto.
    apply NoDup_incl_length. apply NoDup_cons_iff. constructor; auto. apply NoDup_nil.
    intros x H. good_inversion H; [ | inversion H0 ]. apply eq_sys_roots_prop.
    exists (snd (eq_sys_find ((n, LinkESNode n') :: s) n)). destruct (H1 n) as [ p H ].
    apply in_eq_sys_dom_prop. apply set_add_intro2. auto. eapply eq_sys_find_root. eauto.
Qed.

Lemma eq_sys_interp_size_succ s n (H : eq_sys_interp_size s = S n)
                            : { x | exists t, eq_sys_find_step s x = Some (RootESNode t) }.
Proof.
  unfold eq_sys_interp_size in H. remember (eq_sys_roots s) as res. symmetry in Heqres.
  destruct res as [ | x ]. inversion H. clear H. exists x. apply eq_sys_roots_prop.
  rewrite Heqres. left. auto.
Qed.

Lemma eq_sys_interp_size_prop_aux s ns n (H1 : In n ns)
                                  (H2 : forall n', In n' ns -> n = n'
                                               <-> exists t, eq_sys_find_step s n'
                                                           = Some (RootESNode t))
                                : eq_sys_interp_size s = S (eq_sys_interp_size
                                  (eq_sys_dom_erase' s ns)).
Proof.
  refine (_ : _ = var_set_size (n :: eq_sys_roots (eq_sys_dom_erase' s ns))).
  apply NoDup_length. 2: constructor. 1, 3: apply eq_sys_roots_distinct.
  * intro. apply eq_sys_roots_prop in H. destruct H as [ t H ].
    assert (in_eq_sys_dom n (eq_sys_dom_erase' s ns)). eexists. eauto.
    apply in_eq_sys_dom_prop in H0. apply eq_sys_dom_erase'_prop in H0.
    destruct H0. apply H3. auto.
  * intro n'. constructor; intro.
    - apply eq_sys_roots_prop in H. destruct H as [ t' H ].
      destruct (name_eq_dec n' n). subst. left. auto. right. apply eq_sys_roots_prop. eexists.
      erewrite eq_sys_dom_erase'_find_step. eauto. intro. apply n0. symmetry. eapply H2; eauto.
    - apply eq_sys_roots_prop. good_inversion H. apply H2; auto.
      apply eq_sys_roots_prop in H0. destruct H0 as [ t H ].
      assert (in_eq_sys_dom n' (eq_sys_dom_erase' s ns)). eexists. eauto.
      apply in_eq_sys_dom_prop in H0. apply eq_sys_dom_erase'_prop in H0. destruct H0.
      rewrite eq_sys_dom_erase'_find_step in H; auto. eexists. eauto.
Qed.

Lemma eq_sys_interp_size_prop s n (int : eq_sys_interp n)
                              (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                            : eq_sys_interp_size s = n.
Proof.
  set (P := fun s n (int : eq_sys_interp n) => eq_sys_interp_size s = n).
  eapply (eq_sys_interp_size_ind P); eauto; clear s n int H1 H2; subst P; simpl; intros. auto.
  set (x := eq_sys_interp_repr_var s int n (le_n (S n))).
  erewrite (eq_sys_interp_size_prop_aux _ _ x). f_equal. eauto.
  apply eq_sys_interp_repr_var_in; auto.
  intros y H2. constructor; intro. subst. apply eq_sys_interp_repr_var_root; auto.
  assert (fst (eq_sys_find s x) = fst (eq_sys_find s y)). eapply H0; eauto.
  apply eq_sys_interp_repr_var_in; auto. revert H4. unfold eq_sys_find at 1.
  assert (in_eq_sys_dom x s). eapply H0. apply eq_sys_interp_repr_var_in; auto.
  apply H in H4. destruct H4 as [ p H4 ]. destruct H3 as [ t H3 ].
  erewrite (eq_sys_find_hlp_fuel _ _ (S (length s))); eauto.
  erewrite eq_sys_find_root_inv; eauto. simpl.
  edestruct eq_sys_interp_repr_var_root as [ t' H5 ]; eauto.
  rewrite (H5 : eq_sys_find_step s x = _). auto.
Qed.

Definition eq_sys_vars_by_repr_hlp s n n' :=
  if name_eq_dec (fst (eq_sys_find s n')) n then true else false.

Definition eq_sys_vars_by_repr s n : var_set :=
  filter (eq_sys_vars_by_repr_hlp s n) (eq_sys_dom s).

Lemma eq_sys_vars_by_repr_distinct s n : NoDup (eq_sys_vars_by_repr s n).
Proof. apply NoDup_filter. auto. Qed.

Lemma eq_sys_vars_by_repr_prop s n n' : In n' (eq_sys_vars_by_repr s n)
                                    <-> in_eq_sys_dom n' s /\ fst (eq_sys_find s n') = n.
Proof.
  constructor; intro.
  * apply filter_In in H. destruct H. constructor. apply in_eq_sys_dom_prop. auto.
    unfold eq_sys_vars_by_repr_hlp in H0. destruct (name_eq_dec (fst (eq_sys_find s n')) n); auto.
    inversion H0.
  * destruct H. apply filter_In. constructor. apply in_eq_sys_dom_prop. auto.
    unfold eq_sys_vars_by_repr_hlp. destruct (name_eq_dec (fst (eq_sys_find s n')) n); auto.
Qed.

Lemma eq_sys_vars_by_repr_not_empty s n (H : exists t, eq_sys_find_step s n = Some (RootESNode t))
                                  : eq_sys_vars_by_repr s n <> var_set_empty.
Proof.
  intro. absurd (In n (eq_sys_vars_by_repr s n)). rewrite H0. auto.
  apply eq_sys_vars_by_repr_prop. constructor. destruct H. eexists. eauto.
  destruct H as [ t H ]. erewrite eq_sys_find_root_inv; eauto.
Qed.

Lemma eq_sys_interp_exists s (H : eq_sys_wf s)
                         : { int : eq_sys_interp (eq_sys_interp_size s)
                           | is_interp_of_eq_sys int s
                           }.
Proof.
  remember (eq_sys_interp_size s) as n. symmetry in Heqn. generalize dependent s.
  induction n; intros; subst.
  * apply eq_sys_interp_size_zero in Heqn; auto. subst.
    eexists. apply eq_sys_interp_trivial_is_of_trivial.
  * set (Heqn' := Heqn). apply eq_sys_interp_size_succ in Heqn'. destruct Heqn' as [ x Hx ].
    set (ns := eq_sys_vars_by_repr s x). set (s' := eq_sys_dom_erase' s ns).
    assert (eq_sys_wf s'). {
      apply eq_sys_dom_erase'_wf. auto. intros y1 y2. intros. intro.
      apply eq_sys_vars_by_repr_prop in H2. destruct H2. apply H1. apply eq_sys_vars_by_repr_prop.
      constructor. eexists. eauto. apply H in H2. destruct H2 as [ p H2 ].
      erewrite eq_sys_find_link; eauto. eright; eauto.
    }
    set (H1 := H0). apply IHn in H1. destruct H1 as [ int' Hint' ]. unshelve eexists. intros i Hi.
    destruct (Nat.eq_dec i n). exact (ns, snd (eq_sys_find s x)). apply (int' i).
    good_inversion Hi; auto. exfalso. apply n0. auto. simpl.
    repeat constructor; simpl; intros.
    - destruct (Nat.eq_dec i n). auto. apply Hint'.
    - destruct (Nat.eq_dec i n); simpl. apply eq_sys_vars_by_repr_not_empty. auto. apply Hint'.
    - destruct (Nat.eq_dec i n); destruct (Nat.eq_dec j n); simpl in *. lia.
      + apply Hint' in H2. destruct H2 as [ _ [ _ H2 ]]. apply in_eq_sys_dom_prop in H2.
        apply eq_sys_dom_erase'_prop in H2. destruct H2. contradiction.
      + apply Hint' in H1. destruct H1 as [ _ [ _ H1 ] ]. apply in_eq_sys_dom_prop in H1.
        apply eq_sys_dom_erase'_prop in H1. destruct H1. contradiction.
      + eapply Hint'. apply H1. apply H2.
    - destruct (Nat.eq_dec i n); simpl in *. apply eq_sys_vars_by_repr_prop in H2. destruct H2.
      rewrite H3. apply eq_sys_vars_by_repr_prop. destruct Hx as [ t Hx ]. constructor.
      eexists. eauto. erewrite eq_sys_find_root_inv; eauto.
      apply Hint' in H2. destruct H2 as [ H2 [ _ H3 ] ].
      set (H4 := H3). apply H0 in H4. destruct H4 as [ p' H4 ].
      apply in_eq_sys_dom_prop in H3. apply eq_sys_dom_erase'_prop in H3. destruct H3.
      apply in_eq_sys_dom_prop in H3. apply H in H3. destruct H3 as [ p H3 ].
      subst s'. erewrite eq_sys_dom_erase'_find in H2; eauto.
    - destruct (Nat.eq_dec i n); simpl in *. apply eq_sys_vars_by_repr_prop in H2. destruct H2.
      f_equal. apply H in H2. destruct H2 as [ p H2 ]. eapply eq_sys_find_in_path; eauto.
      eapply eq_sys_find_last in H3; eauto. destruct H3 as [ p' H3 ]. rewrite H3.
      apply in_app_iff. right. constructor. auto.
      apply Hint' in H2. destruct H2 as [ _ [ H2 H3 ] ]. etransitivity; [ | apply H2 ]. clear H2.
      f_equal. symmetry. set (H2 := H3). apply in_eq_sys_dom_prop in H2.
      apply eq_sys_dom_erase'_prop in H2. destruct H2. apply in_eq_sys_dom_prop in H2.
      apply H in H2. destruct H2 as [ p H2 ]. apply H0 in H3. destruct H3 as [ p' H3 ].
      eapply eq_sys_dom_erase'_find; eauto.
    - destruct (Nat.eq_dec i n); simpl in *. apply eq_sys_vars_by_repr_prop in H2. apply H2.
      apply Hint' in H2. destruct H2 as [ _ [ _ H2 ] ]. apply in_eq_sys_dom_prop in H2.
      apply eq_sys_dom_erase'_prop in H2. destruct H2. apply in_eq_sys_dom_prop. auto.
    - destruct (Nat.eq_dec i n); simpl in *. apply eq_sys_vars_by_repr_prop in H2, H3.
      destruct H2. destruct H3. congruence.
      transitivity (fst (eq_sys_find s' x0)). f_equal.
      apply Hint' in H2. destruct H2 as [ _ [ _ H2 ] ]. clear H3. set (H3 := H2).
      apply in_eq_sys_dom_prop in H3. apply eq_sys_dom_erase'_prop in H3. destruct H3.
      apply in_eq_sys_dom_prop in H3. apply H0 in H2. destruct H2 as [ p' H2 ].
      apply H in H3. destruct H3 as [ p H3 ]. symmetry. eapply eq_sys_dom_erase'_find; eauto.
      transitivity (fst (eq_sys_find s' y)). eapply Hint'; eauto.
      apply Hint' in H3. destruct H3 as [ _ [ _ H3 ] ]. clear H2. set (H2 := H3).
      apply in_eq_sys_dom_prop in H2. apply eq_sys_dom_erase'_prop in H2. destruct H2.
      apply in_eq_sys_dom_prop in H2. apply H0 in H3. destruct H3 as [ p' H3 ].
      apply H in H2. destruct H2 as [ p H2 ]. f_equal. eapply eq_sys_dom_erase'_find; eauto.
    - intros y Hy. destruct (in_dec name_eq_dec y ns).
      + exists n. exists (le_n _). destruct (Nat.eq_dec n n); auto. contradiction.
      + assert (in_eq_sys_dom y s'). apply in_eq_sys_dom_prop. apply eq_sys_dom_erase'_prop.
        constructor; auto. apply in_eq_sys_dom_prop. auto.
        apply Hint' in H1. destruct H1 as [ i [ Hi H1 ] ]. exists i. exists (le_S _ _ Hi).
        destruct (Nat.eq_dec i n); auto. exfalso. lia.
    - apply Nat.succ_inj. rewrite <- Heqn.
      transitivity (var_set_size (x :: eq_sys_roots s')). auto.
      apply NoDup_length. apply NoDup_cons_iff. constructor. 2, 3: apply eq_sys_roots_distinct.
      intro. apply eq_sys_roots_prop in H2. absurd (in_eq_sys_dom x s').
      intro. apply in_eq_sys_dom_prop in H3. apply eq_sys_dom_erase'_prop in H3. destruct H3.
      apply H4. apply in_eq_sys_dom_prop in H3. apply eq_sys_vars_by_repr_prop. constructor; auto.
      destruct Hx as [ t Hx ]. erewrite eq_sys_find_root_inv; eauto.
      destruct H2. eexists. eauto.
      intro y. constructor; intro.
      + good_inversion H2. apply eq_sys_roots_prop. auto.
        apply eq_sys_roots_prop in H3. destruct H3 as [ t H3 ].
        apply eq_sys_roots_prop. exists t.
        assert (in_eq_sys_dom y s'). eexists. eauto. apply in_eq_sys_dom_prop in H2.
        apply eq_sys_dom_erase'_prop in H2. destruct H2. etransitivity; [ | apply H3 ].
        symmetry. eapply eq_sys_dom_erase'_find_step. auto.
      + destruct (name_eq_dec x y). left. auto. right. apply eq_sys_roots_prop in H2.
        destruct H2 as [ t H2 ]. apply eq_sys_roots_prop. exists t. etransitivity; [ | apply H2 ].
        apply eq_sys_dom_erase'_find_step. intro. apply eq_sys_vars_by_repr_prop in H3.
        destruct H3. apply H in H3. destruct H3 as [ p H3 ].
        good_inversion H3; rewrite H2 in H5; good_inversion H5.
        apply n0. erewrite eq_sys_find_root_inv; eauto.
Qed.
*)

(*
Lemma eq_sys_union_interp_size_some s s' x y ts (H : eq_sys_union s x y = (Some ts, s'))
                             : eq_sys_interp_size s = S (eq_sys_interp_size s').
Proof.
  unfold eq_sys_union in H.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1' ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2' ].
  destruct (name_eq_dec x' y'). inversion H.
  destruct t1' as [ t1 | ]; destruct t2' as [ t2 | ]; good_inversion H.
  rewrite eq_sys_ensure_var_id. 2: eexists; eapply eq_sys_find_some; eauto.
  refine (_ : _ = length (y' :: eq_sys_roots ((y', LinkESNode x') :: s))).
  apply NoDup_length. apply eq_sys_roots_distinct. apply NoDup_cons_iff. constructor.
  intro. apply eq_sys_roots_prop in H. destruct H as [ t H ]. simpl in H.
  destruct (name_eq_dec y' y'); auto. inversion H.
  apply eq_sys_roots_distinct.
  intro z. constructor; intro.
  * destruct (name_eq_dec z y'). left. auto. right.
    apply eq_sys_roots_prop in H. destruct H as [ t H ].
    apply eq_sys_roots_prop. exists t. simpl. destruct (name_eq_dec z y'); auto. contradiction.
  * good_inversion H. apply eq_sys_roots_prop. exists (Some t2). eapply eq_sys_find_some. eauto.
    apply eq_sys_roots_prop in H0. destruct H0 as [ t H ]. simpl in H.
    destruct (name_eq_dec z y'). inversion H. apply eq_sys_roots_prop. eexists. eauto.
Qed.
*)
*)


(* MGU *)

Definition is_inf_unifier (s : inf_subst) (t1 t2 : inf_term) :=
  inf_term_eq (apply_inf_subst s t1) (apply_inf_subst s t2).

Definition is_unification_grow (s1 s2 : eq_sys) (ts : list terms) :=
  exists s', (forall t1 t2, In (t1, t2) ts
                         -> is_inf_unifier (inf_subst_compose s' (eq_sys_inf_subst s1))
                                           (term_to_inf_term t1) (term_to_inf_term t2))
          /\ (forall t, inf_term_eq (eq_sys_apply s2 t) (apply_inf_subst s' (eq_sys_apply s1 t))).

Lemma eq_sys_image_compose_add_link_over_root s1 s2 x y z t1 t2 (H1 : eq_sys_wf s2)
  (H2 : eq_sys_wf ((x, LinkESNode y) :: s2))
  (H3 : x <> y)
  (H4 : eq_sys_lookup s2 x = Some (RootESNode t1))
  (H5 : eq_sys_lookup s2 y = Some (RootESNode t2))
  (H6 : inf_term_eq (apply_inf_subst s1 (eq_sys_apply ((x, LinkESNode y) :: s2) (term_head_to_term t1)))
                    (apply_inf_subst s1 (eq_sys_apply ((x, LinkESNode y) :: s2) (term_head_to_term t2))))
: inf_term_eq (apply_inf_subst s1 (eq_sys_image ((x, LinkESNode y) :: s2) z))
              (apply_inf_subst s1 (eq_sys_image s2 z)).
Proof.
  revert z. cofix IHz. intro.
  rewrite (inf_term_step_prop (eq_sys_image _ _)).
  rewrite (inf_term_step_prop (eq_sys_image s2 _)). simpl.
  remember (eq_sys_find ((x, LinkESNode y) :: s2) z) as res1. symmetry in Heqres1.
  remember (eq_sys_find s2 z) as res2. symmetry in Heqres2. destruct res2 as [ z' t2' ].
  remember (name_eq_dec z' x) as dec. symmetry in Heqdec. destruct dec.
  * subst z'. destruct (H1 z) as [ pz Hpz ]. set (Hpz' := Hpz).
    eapply eq_sys_find_last in Hpz'. 2: rewrite Heqres2; auto.
    destruct Hpz' as [ pz' ]. simpl in H. subst pz. rename pz' into pz.
    erewrite (eq_sys_find_in_path _ z x) in Heqres2; eauto.
    2: apply in_app_iff; right; left; auto.
    erewrite eq_sys_find_some_inv in Heqres2; eauto.
    inversion Heqres2. subst t2'. clear Heqres2.
    set (Hpz' := Hpz). destruct (H2 y) as [ py2 Hpy2 ].
    eapply eq_sys_name_wf_add_link3 in Hpz'; eauto.
    erewrite (eq_sys_find_in_path _ z x) in Heqres1; eauto.
    2: apply in_app_iff; right; left; auto.
    destruct (H2 x) as [ p2 Hp2 ].
    erewrite eq_sys_find_link in Heqres1; eauto; [ | simpl; rewrite Heqdec; auto ].
    erewrite eq_sys_find_some_inv in Heqres1;
      [ | simpl; destruct (name_eq_dec y x); [ exfalso; apply H3; auto | eauto ] ].
    subst res1. simpl.
    destruct t1 as [ c1 | c1 l1 r1 ]; destruct t2 as [ c2 | c2 l2 r2 ];
      rewrite inf_term_step_prop in H6 at 1; rewrite inf_term_step_prop in H6;
      good_inversion H6.
    reflexivity.
    rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl. constructor.
    - eapply inf_term_eq_trans. symmetry. eauto. apply IHz.
    - eapply inf_term_eq_trans. symmetry. eauto. apply IHz.
  * rename n into H7.
    assert (res1 = (z', t2')). {
      destruct (H1 z) as [ pz Hpz ]. set (Hpz' := Hpz).
      apply (eq_sys_name_wf_add_link1 _ x y) in Hpz'. 2: {
        intro. clear Heqres1 Hpz'. induction Hpz.
        * destruct H; [ | inversion H ]. subst n. rewrite H4 in H0. good_inversion H0.
          erewrite eq_sys_find_some_inv in Heqres2; eauto. good_inversion Heqres2. contradiction.
        * destruct H; [ | inversion H ]. subst n. rewrite H4 in H0. inversion H0.
        * destruct H. subst n. rewrite H4 in H0. inversion H0. apply IHHpz; auto.
          rewrite <- Heqres2. symmetry. destruct (H1 n) as [ pn Hpn ].
          eapply eq_sys_find_link; eauto.
      }
      rewrite <- Heqres1. set (Hpz'' := Hpz).
      eapply eq_sys_find_last in Hpz''; auto.
      destruct Hpz'' as [ pz' Hpz'' ]. subst pz. rename pz' into pz.
      rewrite Heqres2 in Hpz, Hpz'. simpl in Hpz, Hpz'.
      erewrite eq_sys_find_in_path; eauto. 2: apply in_app_iff; right; left; auto.
      destruct t2'.
      * apply eq_sys_find_some_inv. simpl. rewrite Heqdec. eapply eq_sys_find_some. eauto.
      * apply eq_sys_find_no. simpl. rewrite Heqdec. eapply eq_sys_find_no_inv; eauto.
    }
    rewrite H. subst. clear Heqres2 H. simpl.
    destruct t2' as [ [ c2 | c2 l2 r2 ] | ]; try reflexivity; simpl.
    rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
    constructor; apply IHz; eauto.
Admitted.

Lemma eq_sys_union_grows_some x y s1 s2 s3 t1 t2 (H1 : eq_sys_wf s1)
                              (H2 : eq_sys_union s1 x y = (Some (t1, t2), s2))
                              (H3 : is_unification_grow s2 s3 [( term_head_to_term t1
                                                               , term_head_to_term t2
                                                               )])
                            : is_unification_grow s1 s3 [(Var x, Var y)].
Proof.
  set (H4 := H1). apply (eq_sys_union_wf _ x y) in H4; eauto. unfold eq_sys_union in *.
  remember (eq_sys_find s1 x) as resx. symmetry in Heqresx. destruct resx as [ x' t1' ].
  remember (eq_sys_find s1 y) as resy. symmetry in Heqresy. destruct resy as [ y' t2' ].
  destruct (name_eq_dec x' y'). inversion H2.
  destruct t1' as [ t1' | ]; destruct t2' as [ t2' | ]; good_inversion H2; simpl in *.
  destruct H3 as [ s2 [ H3 H5 ] ]. exists s2. rename n into Hn.
  assert (Hs1 : forall z, inf_term_eq (apply_inf_subst s2 (eq_sys_image ((x', LinkESNode y') :: s1) z))
                                      (apply_inf_subst s2 (eq_sys_image s1 z))). {
    intro. eapply eq_sys_image_compose_add_link_over_root; eauto.
    * eapply eq_sys_find_some. eauto.
    * eapply eq_sys_find_some. eauto.
    * etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop.
      etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
      etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop.
      etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
      apply H3. left. auto.
  }
  constructor; intros.
  * destruct H; [ | inversion H ]. good_inversion H. unfold is_inf_unifier.
    etransitivity. apply inf_subst_compose_prop.
    etransitivity. apply apply_inf_subst_eq.
    etransitivity. symmetry. apply eq_sys_inf_subst_prop.
    destruct (H1 x) as [ p H ]. eapply eq_sys_image_find; eauto.
    rewrite Heqresx. symmetry.
    etransitivity. apply inf_subst_compose_prop.
    etransitivity. apply apply_inf_subst_eq.
    etransitivity. symmetry. apply eq_sys_inf_subst_prop.
    destruct (H1 y) as [ p H ]. eapply eq_sys_image_find; eauto.
    rewrite Heqresy. symmetry. simpl.
    etransitivity. symmetry. apply Hs1. symmetry.
    etransitivity. symmetry. apply Hs1. symmetry.
    apply apply_inf_subst_eq.
    etransitivity. destruct (H4 x') as [ p H ]. eapply eq_sys_image_find; eauto.
    assert (eq_sys_lookup ((x', LinkESNode y') :: s1) x' = Some (LinkESNode y')).
    simpl. destruct (name_eq_dec x' x'). auto. contradiction.
    destruct (H4 x') as [ p Hp ]. erewrite eq_sys_find_link; eauto. clear p Hp.
    symmetry. destruct (H4 y') as [ p Hp ]. eapply eq_sys_image_find. eauto.
  * etransitivity. apply H5. clear H5 s3.
    etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop.
    etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
    etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop.
    etransitivity. symmetry. apply inf_subst_compose_prop.
    apply apply_inf_subst_ext. intros n _. clear t. symmetry. apply Hs1.
Qed.

Lemma eq_sys_union_grows_none x y s1 s2 s3 (H1 : eq_sys_wf s1)
                              (H2 : eq_sys_union s1 x y = (None, s2))
                              (H3 : is_unification_grow s2 s3 [])
                            : is_unification_grow s1 s3 [(Var x, Var y)].
Proof.
  destruct H3 as [ s2' [ _ H3 ] ].
  set (H4 := H1). apply (eq_sys_union_wf _ x y) in H4; eauto. unfold eq_sys_union in *.
  remember (eq_sys_find s1 x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s1 y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  destruct (name_eq_dec x' y'); [ | destruct t2 as [ t2 | ] ]; good_inversion H2; simpl in H4.
  * clear H4. exists s2'. constructor; auto; intros.
    destruct H; good_inversion H. unfold is_inf_unifier.
    etransitivity. apply inf_subst_compose_prop.
    etransitivity. apply apply_inf_subst_eq. symmetry. apply eq_sys_inf_subst_prop. symmetry.
    etransitivity. apply inf_subst_compose_prop.
    etransitivity. apply apply_inf_subst_eq. symmetry. apply eq_sys_inf_subst_prop. symmetry.
    apply apply_inf_subst_eq. simpl.
    etransitivity. destruct (H1 x) as [ p H ]. eapply eq_sys_image_find; eauto. symmetry.
    etransitivity. destruct (H1 y) as [ p H ]. eapply eq_sys_image_find; eauto. symmetry.
    rewrite Heqresx, Heqresy. simpl. reflexivity.
  * destruct t1. inversion H0. clear H0.
    assert (Hx : eq_sys_lookup s1 x' = None).
    destruct (H1 x) as [ p H ]. eapply eq_sys_find_no_inv; eauto.
    exists (inf_subst_compose s2' (inf_subst_singleton x' (eq_sys_image ((x', LinkESNode y') :: s1) x'))).
    constructor; intros.
    - destruct H; good_inversion H. unfold is_inf_unifier.
      etransitivity. apply inf_subst_compose_prop.
      etransitivity. apply apply_inf_subst_eq. symmetry. apply eq_sys_inf_subst_prop.
      etransitivity. apply inf_subst_compose_prop. symmetry.
      etransitivity. apply inf_subst_compose_prop.
      etransitivity. apply apply_inf_subst_eq. symmetry. apply eq_sys_inf_subst_prop.
      etransitivity. apply inf_subst_compose_prop. symmetry.
      apply apply_inf_subst_eq. simpl.
      etransitivity. apply apply_inf_subst_eq.
      destruct (H1 x) as [ p H ]. eapply eq_sys_image_find; eauto. symmetry.
      etransitivity. apply apply_inf_subst_eq.
      destruct (H1 y) as [ p H ]. eapply eq_sys_image_find; eauto. symmetry.
      rewrite Heqresx, Heqresy. simpl. rewrite (eq_sys_image_no s1 x').
      rewrite inf_term_step_prop at 1. unfold inf_subst_singleton at 1. simpl.
      destruct (name_eq_dec x' x'); [ clear e | contradiction ].
      refine (_ : inf_term_eq (inf_term_step (eq_sys_image _ x')) _).
      rewrite <- inf_term_step_prop.
      destruct (H4 x') as [ p H ].
      etransitivity. eapply eq_sys_image_find. eauto.
      erewrite (eq_sys_find_link _ x' y'); eauto;
        [ | simpl; destruct (name_eq_dec x' x'); [ eauto | contradiction ] ].
      clear p H.
      etransitivity. symmetry. destruct (H4 y') as [ p H ]. eapply eq_sys_image_find. eauto.
      apply eq_sys_image_extend; auto.
      apply in_eq_sys_dom_inv. auto.
    - etransitivity. apply H3. clear s3 H3. symmetry.
      etransitivity. apply inf_subst_compose_prop.
      apply apply_inf_subst_eq. symmetry. apply eq_sys_apply_extend; auto.
  * clear H0.
    assert (Hy : eq_sys_lookup s1 y' = None).
    destruct (H1 y) as [ p H ]. eapply eq_sys_find_no_inv; eauto.
    exists (inf_subst_compose s2' (inf_subst_singleton y' (eq_sys_image ((y', LinkESNode x') :: s1) y'))).
    constructor; intros.
    - destruct H; good_inversion H. unfold is_inf_unifier. symmetry.
      etransitivity. apply inf_subst_compose_prop.
      etransitivity. apply apply_inf_subst_eq. symmetry. apply eq_sys_inf_subst_prop.
      etransitivity. apply inf_subst_compose_prop. symmetry.
      etransitivity. apply inf_subst_compose_prop.
      etransitivity. apply apply_inf_subst_eq. symmetry. apply eq_sys_inf_subst_prop.
      etransitivity. apply inf_subst_compose_prop. symmetry.
      apply apply_inf_subst_eq. simpl.
      etransitivity. apply apply_inf_subst_eq.
      destruct (H1 y) as [ p H ]. eapply eq_sys_image_find; eauto. symmetry.
      etransitivity. apply apply_inf_subst_eq.
      destruct (H1 x) as [ p H ]. eapply eq_sys_image_find; eauto. symmetry.
      rewrite Heqresx, Heqresy. simpl. rewrite (eq_sys_image_no s1 y').
      rewrite inf_term_step_prop at 1. unfold inf_subst_singleton at 1. simpl.
      destruct (name_eq_dec y' y'); [ clear e | contradiction ].
      refine (_ : inf_term_eq (inf_term_step (eq_sys_image _ y')) _).
      rewrite <- inf_term_step_prop.
      destruct (H4 y') as [ p H ].
      etransitivity. eapply eq_sys_image_find. eauto.
      erewrite (eq_sys_find_link _ y' x'); eauto;
        [ | simpl; destruct (name_eq_dec y' y'); [ eauto | contradiction ] ].
      clear p H.
      etransitivity. symmetry. destruct (H4 x') as [ p H ]. eapply eq_sys_image_find. eauto.
      apply eq_sys_image_extend; auto.
      apply in_eq_sys_dom_inv. auto.
    - etransitivity. apply H3. clear s3 H3. symmetry.
      etransitivity. apply inf_subst_compose_prop.
      apply apply_inf_subst_eq. symmetry. apply eq_sys_apply_extend; auto.
Qed.

(*
Lemma eq_sys_bind_grows x t
*)

Lemma rt_unification_step_grows t1 t2 s1 s2 s3 n ts (H1 : unification_state_wf (s1, n))
                                (H2 : rt_unification_step s1 n t1 t2 = Some (s2, ts))
                                (H3 : is_unification_grow (fst s2) s3 ts)
                              : is_unification_grow s1 s3 [(t1, t2)].
Proof.
  destruct t1 as [ x | c1 | c1 l1 r1 ]; destruct t2 as [ y | c2 | c2 l2 r2 ]; simpl in H2.
  * remember (eq_sys_union s1 x y) as res. symmetry in Heqres.
    destruct res as [ [ [ t1 t2 ] | ] s2' ]; good_inversion H2; simpl in H3; rename s2' into s2.
    - eapply eq_sys_union_grows_some; eauto. apply H1.
    - eapply eq_sys_union_grows_none; eauto. apply H1.
  * remember (eq_sys_find s1 x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H2; simpl in H3.
    - destruct H3 as [ s2 [ H3 H4 ] ]. exists s2. constructor; auto; intros.
      destruct H; good_inversion H. unfold is_inf_unifier. symmetry.
      etransitivity. symmetry. apply H3. left. auto.
      etransitivity. apply inf_subst_compose_prop. symmetry.
      etransitivity. apply inf_subst_compose_prop.
      apply apply_inf_subst_eq.
      etransitivity. symmetry. apply eq_sys_inf_subst_prop. symmetry.
      etransitivity. symmetry. apply eq_sys_inf_subst_prop. symmetry. simpl.
      destruct H1 as [ H1 _ ]. destruct (H1 x) as [ p H ].
      eapply eq_sys_image_find_apply; eauto. rewrite Heqres. auto.
    - admit.
  * remember (eq_sys_find s1 x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H2; simpl in H3.
    - destruct H3 as [ s2 [ H3 H4 ] ]. exists s2. constructor; auto; intros.
      destruct H; good_inversion H. unfold is_inf_unifier. symmetry.
      etransitivity. symmetry. apply H3. left. auto.
      etransitivity. apply inf_subst_compose_prop. symmetry.
      etransitivity. apply inf_subst_compose_prop.
      apply apply_inf_subst_eq.
      etransitivity. symmetry. apply eq_sys_inf_subst_prop. symmetry.
      etransitivity. symmetry. apply eq_sys_inf_subst_prop. symmetry. simpl.
      destruct H1 as [ H1 _ ]. destruct (H1 x) as [ p H ].
      eapply eq_sys_image_find_apply; eauto. rewrite Heqres. auto.
    - admit.
  * good_inversion H2. destruct H3 as [ s2 [ H3 H4 ] ].
    exists s2. constructor; auto; intros. unfold is_inf_unifier.
    destruct H; good_inversion H. symmetry. apply H3. left. auto.
  * destruct (name_eq_dec c1 c2); good_inversion H2.
    destruct H3 as [ s2 [ H3 H4 ] ]. exists s2. constructor; auto; intros.
    destruct H; good_inversion H. unfold is_inf_unifier. reflexivity.
  * inversion H2.
  * good_inversion H2. destruct H3 as [ s2 [ H3 H4 ] ].
    exists s2. constructor; auto; intros. unfold is_inf_unifier.
    destruct H; good_inversion H. symmetry. apply H3. left. auto.
  * inversion H2.
  * destruct (name_eq_dec c1 c2); good_inversion H2.
    destruct H3 as [ s2 [ H3 H4 ] ]. exists s2. constructor; auto; intros.
    destruct H; good_inversion H. unfold is_inf_unifier.
    rewrite inf_term_step_prop at 1. rewrite inf_term_step_prop. simpl.
    constructor; apply H3. left. auto. right. left. auto.
Admitted.

Lemma rt_unify_grows t1 t2 s s' n (H1 : unification_state_wf (s, n))
                     (H2 : forall x, In x (fv_term t1) -> x < n)
                     (H3 : forall x, In x (fv_term t2) -> x < n)
                     (H4 : (s, n) == t1 |_| t2 => (Some s'))
                   : is_unification_grow s (fst s') [(t1, t2)]
with rt_unify_many_grows ts s s' n (H1 : unification_state_wf (s, n))
                         (H2 : forall x, In x (fv_terms_list ts) -> x < n)
                         (H3 : rt_unify_many (s, n) ts (Some s'))
                       : is_unification_grow s (fst s') ts.
Proof.
  * good_inversion H4. destruct s2 as [ s2 n2 ]. simpl in *.
    set (H6 := H5). apply rt_unification_step_wf in H6; auto.
    eapply rt_unification_step_grows; eauto.
    eapply rt_unify_many_grows; eauto; apply H6.
  * good_inversion H3.
    - exists inf_subst_trivial. constructor; intros. inversion H.
      simpl. symmetry. apply apply_inf_subst_trivial.
    - destruct s2 as [ s2 n2 ]. set (H3 := H). apply rt_unify_wf in H3; auto.
      apply rt_unify_grows in H; auto. apply rt_unify_many_grows in H0; auto.
      destruct H as [ s1 [ H4 H5 ] ]. destruct H0 as [ s1' [ H6 H7 ] ].
      exists (inf_subst_compose s1' s1). {
        constructor; intros.
        * unfold is_inf_unifier.
          etransitivity. apply inf_subst_compose_prop.
          etransitivity. apply inf_subst_compose_prop. symmetry.
          etransitivity. apply inf_subst_compose_prop.
          etransitivity. apply inf_subst_compose_prop. symmetry.
          destruct H.
          - good_inversion H. apply apply_inf_subst_eq.
            etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
            etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
            apply H4. left. auto.
          - etransitivity. apply apply_inf_subst_eq.
            etransitivity. apply apply_inf_subst_eq.
            symmetry. apply eq_sys_inf_subst_prop. 
            etransitivity. symmetry. apply H5. apply eq_sys_inf_subst_prop.
            etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
            etransitivity. apply apply_inf_subst_eq.
            etransitivity. apply apply_inf_subst_eq.
            symmetry. apply eq_sys_inf_subst_prop. 
            etransitivity. symmetry. apply H5. apply eq_sys_inf_subst_prop.
            etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
            simpl. apply H6. auto.
        * etransitivity. apply H7. symmetry.
          etransitivity. apply inf_subst_compose_prop. symmetry.
          apply apply_inf_subst_eq. apply H5.
      }
      apply H3. all: intros.
      + eapply PeanoNat.Nat.lt_le_trans. apply H2. apply set_union_intro2. auto. apply H3.
      + apply H2. apply set_union_intro1. apply fv_terms_In. left. auto.
      + apply H2. apply set_union_intro1. apply fv_terms_In. right. auto.
      + apply H2. apply set_union_intro1. auto.
Qed.

Definition is_eq_sys_unifier (s : eq_sys) (t1 t2 : term) : Prop :=
  inf_term_eq (eq_sys_apply s t1) (eq_sys_apply s t2).

Lemma rt_unify_unifies t1 t2 s s' n (H1 : unification_state_wf (s, n))
                       (H2 : forall x, In x (fv_term t1) -> x < n)
                       (H3 : forall x, In x (fv_term t2) -> x < n)
                       (H4 : (s, n) == t1 |_| t2 => (Some s'))
                     : is_eq_sys_unifier (fst s') t1 t2.
Proof.
  apply rt_unify_grows in H4; auto. destruct H4 as [ s1 [ H4 H5 ] ]. unfold is_eq_sys_unifier.
  etransitivity. apply H5. etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop.
  etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
  etransitivity. apply H5. etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop.
  etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
  apply H4. left. auto.
Qed.

Lemma rt_unify_many_unifies ts s s' n (H1 : unification_state_wf (s, n))
                            (H2 : forall x, In x (fv_terms_list ts) -> x < n)
                            (H3 : rt_unify_many (s, n) ts (Some s'))
                          : forall t1 t2, In (t1, t2) ts -> is_eq_sys_unifier (fst s') t1 t2.
Proof.
  generalize dependent n. revert s s'.
  induction ts as [ | [ t1 t2 ] ts ]; intros. inversion H. destruct H.
  * symmetry in H. good_inversion H. apply rt_unify_many_grows in H3; auto.
    destruct H3 as [ s1 [ H3 H4 ] ]. unfold is_eq_sys_unifier.
    etransitivity. apply H4. etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop.
    etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
    etransitivity. apply H4. etransitivity. apply apply_inf_subst_eq. apply eq_sys_inf_subst_prop.
    etransitivity. symmetry. apply inf_subst_compose_prop. symmetry.
    apply H3. left. auto.
  * good_inversion H3. apply rt_unify_wf in H8; auto. eapply IHts. apply H8.
    intros. eapply PeanoNat.Nat.lt_le_trans. apply H2. apply set_union_intro2. auto. apply H8.
    destruct s2 as [ s2 n2 ]. auto. auto.
    intros. apply H2. apply set_union_intro1. auto.
Qed.

Lemma rt_unify_saves_unifier t1 t2 t1' t2' s s' n (H1 : unification_state_wf (s, n))
                             (H2 : forall x, In x (fv_term t1') -> x < n)
                             (H3 : forall x, In x (fv_term t2') -> x < n)
                             (H4 : (s, n) == t1' |_| t2' => (Some s'))
                             (H5 : is_eq_sys_unifier s t1 t2)
                           : is_eq_sys_unifier (fst s') t1 t2.
Proof.
  apply rt_unify_grows in H4; auto. destruct H4 as [ s1 [ _ H4 ] ]. unfold is_eq_sys_unifier in *.
  etransitivity. apply H4. symmetry. etransitivity. apply H4. symmetry.
  apply apply_inf_subst_eq. auto.
Qed.

Lemma rt_unify_many_saves_unifier t1 t2 ts s s' n (H1 : unification_state_wf (s, n))
                                  (H2 : forall x, In x (fv_terms_list ts) -> x < n)
                                  (H3 : rt_unify_many (s, n) ts (Some s'))
                                  (H4 : is_eq_sys_unifier s t1 t2)
                                : is_eq_sys_unifier (fst s') t1 t2.
Proof.
  apply rt_unify_many_grows in H3; auto. destruct H3 as [ s1 [ _ H3 ] ].
  unfold is_eq_sys_unifier in *.
  etransitivity. apply H3. symmetry. etransitivity. apply H3. symmetry.
  apply apply_inf_subst_eq. auto.
Qed.

Lemma rt_unification_step_complete_some s s' n t1 t2 ts (H1 : eq_sys_wf s)
                                        (H2 : rt_unification_step s n t1 t2 = Some (s', ts))
                                        (H3 : ~exists s', forall t1 t2, In (t1, t2) ts
                                                                     -> is_eq_sys_unifier s' t1 t2)
                                      : ~exists s', is_eq_sys_unifier s' t1 t2
                                                 /\ forall t1 t2, is_eq_sys_unifier s t1 t2
                                                               -> is_eq_sys_unifier s' t1 t2.
Proof.
  destruct t1 as [ x | c1 | c1 l1 r1 ]; destruct t2 as [ y | c2 | c2 l2 r2 ]; simpl in H2.
  * remember (eq_sys_union s x y) as res. symmetry in Heqres.
    destruct res as [ [ [ t1 t2 ] | ] s1 ]; good_inversion H2.
    - admit.
    - exfalso. apply H3. exists s1. intros. inversion H.
  * remember (eq_sys_find s x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H2.
    - intro. destruct H as [ s' [ H2 H4 ] ]. apply H3. exists s'. intros.
      destruct H; good_inversion H. unfold is_eq_sys_unifier in *. symmetry.
      etransitivity. symmetry. apply H2. apply H4.
      destruct (H1 x) as [ p Hp ]. eapply eq_sys_image_find_apply. eauto.
      rewrite Heqres. reflexivity.
    - exfalso. apply H3. exists s. intros. inversion H.
  * remember (eq_sys_find s x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H2.
    - intro. destruct H as [ s' [ H2 H4 ] ]. apply H3. exists s'. intros.
      destruct H; good_inversion H. unfold is_eq_sys_unifier in *. symmetry.
      etransitivity. symmetry. apply H2. apply H4.
      destruct (H1 x) as [ p Hp ]. eapply eq_sys_image_find_apply. eauto.
      rewrite Heqres. reflexivity.
    - exfalso. apply H3. admit.
  * good_inversion H2. intro. destruct H as [ s' [ H2 H4 ] ]. apply H3. exists s'. intros.
    destruct H; good_inversion H. unfold is_eq_sys_unifier. symmetry. apply H2.
  * destruct (name_eq_dec c1 c2); good_inversion H2.
    exfalso. apply H3. exists s. intros. inversion H.
  * inversion H2.
  * good_inversion H2. intro. destruct H as [ s' [ H2 H4 ] ]. apply H3. exists s'. intros.
    destruct H; good_inversion H. unfold is_eq_sys_unifier. symmetry. apply H2.
  * inversion H2.
  * destruct (name_eq_dec c1 c2); good_inversion H2. intro. destruct H as [ s' [ H2 H4 ] ].
    apply H3. exists s'. intros. destruct H; [ | destruct H ]; good_inversion H;
      good_inversion H2; auto.
Admitted.

Lemma rt_unification_step_complete_none s n t1 t2 (H : rt_unification_step s n t1 t2 = None)
                                      : ~exists s', is_eq_sys_unifier s' t1 t2.
Proof.
  destruct t1 as [ x | c1 | c1 l1 r1 ]; destruct t2 as [ y | c2 | c2 l2 r2 ]; simpl in H.
  * destruct (eq_sys_union s x y) as [ [ [ ] | ] ]; inversion H.
  * destruct (eq_sys_find s x) as [ x' [ | ] ]; inversion H.
  * destruct (eq_sys_find s x) as [ x' [ | ] ]; inversion H.
  * inversion H.
  * destruct (name_eq_dec c1 c2); good_inversion H. rename n0 into H. intro.
    destruct H0 as [ s' H0 ]. good_inversion H0. apply H. auto.
  * clear H. intro. destruct H as [ s' H ]. inversion H.
  * inversion H.
  * clear H. intro. destruct H as [ s' H ]. inversion H.
  * destruct (name_eq_dec c1 c2); good_inversion H. rename n0 into H. intro.
    destruct H0 as [ s' H0 ]. good_inversion H0. apply H. auto.
Qed.

Theorem rt_unify_complete s n t1 t2 (H : (s, n) == t1 |_| t2 => None)
                        : ~exists s', is_eq_sys_unifier s' t1 t2
with rt_unify_many_complete s n ts (H : rt_unify_many (s, n) ts None)
                          : ~exists s', forall t1 t2, In (t1, t2) ts -> is_eq_sys_unifier s' t1 t2.
Proof.
  * good_inversion H.
    - admit.
    - apply rt_unification_step_complete_none in H4. auto.
  * good_inversion H.
    - destruct s2 as [ s2 n2 ]. apply rt_unify_many_complete in H1.
      intro. destruct H as [ s' H ]. apply H1. exists s'. intros. apply H. right. auto.
    - apply rt_unify_complete in H0. intro. destruct H as [ s' H ]. apply H0.
      exists s'. apply H. left. auto.
Admitted.

(*
Lemma is_eq_sys_unifier_ext s1 s2
                            (H : forall x t, inf_term_eq (eq_sys_image s1 x) (eq_sys_apply s1 t)
                                          -> inf_term_eq (eq_sys_image s2 x) (eq_sys_apply s2 t))
                          : forall t1 t2, is_eq_sys_unifier s1 t1 t2 -> is_eq_sys_unifier s2 t1 t2.
Proof.
  induction t1 as [ x | c1 | c1 l1 IHl1 r1 ]; intros.
  * apply H. auto.
  * destruct t2 as [ y | c2 | c2 l2 r2 ]; good_inversion H0; unfold is_eq_sys_unifier.
    - symmetry. apply H. simpl. rewrite H3. reflexivity.
    - reflexivity.
  * destruct t2 as [ y | c2 | c2 l2 r2 ]; good_inversion H0; unfold is_eq_sys_unifier.
    - symmetry. apply H. simpl. rewrite <- H5. constructor; symmetry; auto.
    - simpl. constructor. apply IHl1. auto. apply IHr1. auto.
Qed.

Lemma is_eq_sys_unifier_extend s x node (H1 : eq_sys_wf s) (H2 : eq_sys_wf ((x, node) :: s))
                               (H3 : eq_sys_lookup s x = None)
                             : forall t1 t2, is_eq_sys_unifier s t1 t2
                                          -> is_eq_sys_unifier ((x, node) :: s) t1 t2.
Proof.
  intros. unfold is_eq_sys_unifier. etransitivity. apply eq_sys_apply_extend; auto.
  symmetry. etransitivity. apply eq_sys_apply_extend; auto.
  symmetry. apply apply_inf_subst_eq. auto.
Qed.

Lemma is_eq_sys_unifier_add_root s x t t1 t2 (H1 : eq_sys_wf s)
                                 (H2 : eq_sys_lookup s x = None)
                                 (H3 : is_eq_sys_unifier s t1 t2)
                               : is_eq_sys_unifier ((x, RootESNode t) :: s) t1 t2.
Proof. apply is_eq_sys_unifier_extend; auto. apply eq_sys_wf_add_root. auto. Qed.

Lemma is_eq_sys_unifier_add_link1 s x y t1 t2 (H1 : eq_sys_wf s)
                                  (H2 : eq_sys_wf ((x, LinkESNode y) :: s))
                                  (H3 : eq_sys_lookup s x = None)
                                  (H4 : is_eq_sys_unifier s t1 t2)
                                : is_eq_sys_unifier ((x, LinkESNode y) :: s) t1 t2.
Proof. apply is_eq_sys_unifier_extend; auto. Qed.

Lemma is_eq_sys_unifier_add_link2 s1 s2 x y t1 t2 t1' t2' (H1 : eq_sys_wf s1)
                                  (H2 : eq_sys_wf ((x, LinkESNode y) :: s1))
                                  (H3 : eq_sys_lookup s1 x = Some (RootESNode t1'))
                                  (H4 : eq_sys_lookup s1 y = Some (RootESNode t2'))
                                  (H5 : forall t1 t2, is_eq_sys_unifier ((x, LinkESNode y) :: s1) t1 t2
                                                   -> is_eq_sys_unifier s2 t1 t2)
                                  (H6 : is_eq_sys_unifier s2 (term_head_to_term t1')
                                                             (term_head_to_term t2'))
                                  (H7 : is_eq_sys_unifier s1 t1 t2)
                                : is_eq_sys_unifier s2 t1 t2.
Proof.
  apply (is_eq_sys_unifier_ext s1); auto. clear t1 t2 H7. intros z t H.
  generalize dependent H. induction t as [ z' | c | c l IHl r ]; simpl; intros.
Admitted.

Lemma eq_sys_union_saves_unifier_none t1 t2 x y s s' (H1 : eq_sys_wf s)
                                      (H2 : eq_sys_union s x y = (None, s'))
                                      (H3 : is_eq_sys_unifier s t1 t2)
                                    : is_eq_sys_unifier s' t1 t2.
Proof.
  set (H4 := H1). eapply (eq_sys_union_wf s x y) in H4.
  unfold eq_sys_union in H2, H4.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1' ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2' ].
  destruct (name_eq_dec x' y'). good_inversion H2. auto.
  destruct t1' as [ t1' | ]; destruct t2' as [ t2' | ]; good_inversion H2;
    apply is_eq_sys_unifier_add_link1; auto.
  * destruct (H1 y) as [ p H ]. eapply eq_sys_find_no_inv; eauto.
  * destruct (H1 x) as [ p H ]. eapply eq_sys_find_no_inv; eauto.
  * destruct (H1 y) as [ p H ]. eapply eq_sys_find_no_inv; eauto.
Qed.

Lemma eq_sys_union_saves_unifier_some t1 t2 x y s1 s2 s3 t1' t2' (H1 : eq_sys_wf s1)
                                      (H2 : eq_sys_union s1 x y = (Some (t1', t2'), s2))
                                      (H3 : is_eq_sys_unifier s1 t1 t2)
                                      (H4 : is_eq_sys_unifier s3 (term_head_to_term t1')
                                                                 (term_head_to_term t2'))
                                      (H5 : forall t1 t2, is_eq_sys_unifier s2 t1 t2
                                                       -> is_eq_sys_unifier s3 t1 t2)
                                    : is_eq_sys_unifier s3 t1 t2.
Proof.
  set (H6 := H1). eapply (eq_sys_union_wf s1 x y) in H6.
  unfold eq_sys_union in H2, H6.
  remember (eq_sys_find s1 x) as resx. symmetry in Heqresx. destruct resx as [ x' t1'' ].
  remember (eq_sys_find s1 y) as resy. symmetry in Heqresy. destruct resy as [ y' t2'' ].
  destruct (name_eq_dec x' y'). inversion H2.
  destruct t1'' as [ t1'' | ]; destruct t2'' as [ t2'' | ]; good_inversion H2. simpl in H6.
  eapply (is_eq_sys_unifier_add_link2 s1); eauto; eapply eq_sys_find_some; eauto.
Qed.

Lemma eq_sys_bind_saves_unifier t1 t2 x t s (H1 : eq_sys_wf s)
                                (H2 : snd (eq_sys_find s x) = None)
                                (H3 : is_eq_sys_unifier s t1 t2)
                              : is_eq_sys_unifier (eq_sys_bind s x t) t1 t2.
Proof.
  unfold eq_sys_bind.
  remember (eq_sys_find s x) as res. symmetry in Heqres. destruct res as [ x' t' ].
  simpl in H2. subst. apply is_eq_sys_unifier_add_root; auto.
  destruct (H1 x) as [ p H ]. eapply eq_sys_find_no_inv; eauto.
Qed.

Lemma rt_unification_step_saves_unifier t1 t2 t1' t2' s1 s2 s3 n1 n2 ts
                                        (H1 : unification_state_wf (s1, n1))
                                        (H2 : is_eq_sys_unifier s1 t1 t2)
                                        (H3 : rt_unification_step s1 n1 t1' t2' = Some ((s2, n2), ts))
                                        (H4 : forall t1 t2, is_eq_sys_unifier s2 t1 t2
                                                         -> is_eq_sys_unifier s3 t1 t2)
                                        (H5 : forall t1 t2, In (t1, t2) ts
                                                         -> is_eq_sys_unifier s3 t1 t2)
                                      : is_eq_sys_unifier s3 t1 t2.
Proof.
  destruct t1' as [ x | c1 | c1 l1 r1 ]; destruct t2' as [ y | c2 | c2 l2 r2 ]; simpl in H3.
  * remember (eq_sys_union s1 x y) as res. symmetry in Heqres.
    destruct res as [ [ [ t1' t2' ] | ] s1' ]; good_inversion H3.
    - eapply eq_sys_union_saves_unifier_some; eauto. apply H1. apply H5. left. auto.
    - apply H4. eapply eq_sys_union_saves_unifier_none; eauto. apply H1.
  * remember (eq_sys_find s1 x) as res. symmetry in Heqres.
    destruct res as [ x' [ t' | ] ]; good_inversion H3. auto.
    apply H4. apply eq_sys_bind_saves_unifier. apply H1. rewrite Heqres. auto. auto.
  * remember (eq_sys_find s1 x) as res. symmetry in Heqres.
    destruct res as [ x' [ t' | ] ]; good_inversion H3. auto.
    apply H4. apply eq_sys_bind_saves_unifier. apply H1. rewrite Heqres. auto. auto.
  * good_inversion H3. auto.
  * destruct (name_eq_dec c1 c2); good_inversion H3. auto.
  * inversion H3.
  * good_inversion H3. auto.
  * inversion H3.
  * destruct (name_eq_dec c1 c2); good_inversion H3. auto.
Qed.

Lemma eq_sys_union_unifies_aux x y x' y' s (H1 : eq_sys_wf s)
                               (H2 : eq_sys_wf ((x', LinkESNode y') :: s))
                               (H3 : fst (eq_sys_find s x) = x')
                               (H4 : fst (eq_sys_find s y) = y')
                               (H5 : x' <> y')
                             : inf_term_eq (eq_sys_image ((x', LinkESNode y') :: s) x)
                                           (eq_sys_image ((x', LinkESNode y') :: s) y).
Proof.
  etransitivity. destruct (H2 x) as [ p H ]. eapply eq_sys_image_find. eauto.
  symmetry. etransitivity. destruct (H2 y) as [ p H ]. eapply eq_sys_image_find. eauto.
  unshelve erewrite (_ : fst (eq_sys_find _ y)
                       = fst (eq_sys_find ((x', LinkESNode y') :: s) x)); [ | reflexivity ].
  destruct (H1 x) as [ px1 Hx1 ].
  destruct (H1 y) as [ py Hy1 ]. set (Hy2 := Hy1).
  apply (eq_sys_name_wf_add_link1 s x' y') in Hy2. 2: {
    intro. clear Hy2. apply H5.
    erewrite eq_sys_find_in_path in H4; eauto. etransitivity; [ | apply H4 ].
    symmetry. apply eq_sys_find_root_inv. apply is_eq_sys_root_prop.
    eapply eq_sys_find_root. apply Hx1. auto.
  }
  assert (Hy1' : eq_sys_name_wf s y' [y']). eapply eq_sys_find_root; eauto.
  assert (Hy2' : eq_sys_name_wf ((x', LinkESNode y') :: s) y' [y']). {
    apply eq_sys_name_wf_add_link1. auto. intro.
    destruct H; [ | inversion H ]. apply H5. auto.
  }
  transitivity (fst (eq_sys_find ((x', LinkESNode y') :: s) y')). {
    transitivity (fst (eq_sys_find s y)). eapply eq_sys_find_fst_ext; eauto.
    transitivity (fst (eq_sys_find s y')). rewrite H4. symmetry. apply eq_sys_find_root_inv.
    apply is_eq_sys_root_prop. auto.
    eapply eq_sys_find_fst_ext; eauto.
  }
  destruct (H2 x') as [ px' Hx2' ].
  transitivity (fst (eq_sys_find ((x', LinkESNode y') :: s) x')). {
    erewrite <- eq_sys_find_link; eauto. simpl.
    destruct (name_eq_dec x' x'). auto. contradiction.
  }
  destruct (H2 x) as [ px Hx2 ].
  f_equal. symmetry. eapply eq_sys_find_in_path. eauto.
  set (Hx1' := Hx1). eapply eq_sys_find_last in Hx1'; eauto. destruct Hx1' as [ px1' H ].
  subst px1. rename px1' into px1. eapply eq_sys_name_wf_add_link3 in Hx1; eauto.
  eapply eq_sys_name_wf_func in Hx1; [ | apply Hx2 ].
  subst px. apply in_app_iff. right. left. auto.
Qed.

Lemma eq_sys_union_unifies x y s (H : eq_sys_wf s)
                         : is_eq_sys_unifier (snd (eq_sys_union s x y)) (Var x) (Var y).
Proof.
  set (H' := H). apply (eq_sys_union_wf s x y) in H'. unfold eq_sys_union in *.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  destruct (name_eq_dec x' y').
  * clear H'. subst. unfold is_eq_sys_unifier. simpl. etransitivity; [ | symmetry; etransitivity ].
    - destruct (H x) as [ p H' ]. eapply eq_sys_image_find. eauto.
    - destruct (H y) as [ p H' ]. eapply eq_sys_image_find. eauto.
    - rewrite Heqresx, Heqresy. reflexivity.
  * destruct t2 as [ t2 | ]; unfold is_eq_sys_unifier; simpl in *.
    - apply eq_sys_union_unifies_aux; auto. rewrite Heqresx. auto. rewrite Heqresy. auto.
    - symmetry. apply eq_sys_union_unifies_aux; auto. rewrite Heqresy. auto. rewrite Heqresx. auto.
Qed.

Lemma eq_sys_bind_unifies x t s (H : eq_sys_wf s)
                        : is_eq_sys_unifier (eq_sys_bind s x t) (Var x) (term_head_to_term t).
Proof.
  unfold eq_sys_bind.
  remember (eq_sys_find s x) as res. symmetry in Heqres. destruct res as [ x' t' ].
  assert (Heqres' : fst (eq_sys_find s x) = x'). rewrite Heqres. auto.
  clear t' Heqres. rename Heqres' into Heqres. unfold is_eq_sys_unifier. simpl.
  destruct (H x) as [ p Hp ]. set (Hp' := Hp). eapply eq_sys_find_last in Hp'; eauto.
  destruct Hp' as [ p' Hp' ]. subst p. set (Hp' := Hp). eapply eq_sys_name_wf_add_root2 in Hp'.
  eapply eq_sys_image_find_apply. eauto.
  erewrite (eq_sys_find_in_path _ x x'); eauto.
  erewrite eq_sys_find_some_inv. reflexivity.
  simpl. destruct (name_eq_dec x' x'). auto. contradiction.
  apply in_app_iff. right. left. auto.
Qed.

Lemma rt_unification_step_unifies t1 t2 s1 s2 s3 n1 n2 ts (H1 : eq_sys_wf s1)
                                  (H2 : rt_unification_step s1 n1 t1 t2 = Some ((s2, n2), ts))
                                  (H3 : forall t1 t2, is_eq_sys_unifier s2 t1 t2
                                                   -> is_eq_sys_unifier s3 t1 t2)
                                  (H4 : forall t1 t2, In (t1, t2) ts
                                                   -> is_eq_sys_unifier s3 t1 t2)
                                : is_eq_sys_unifier s3 t1 t2.
Proof.
  destruct t1 as [ x | c1 | c1 l1 r1 ]; destruct t2 as [ y | c2 | c2 l2 r2 ]; simpl in H2.
  * remember (eq_sys_union s1 x y) as res. symmetry in Heqres.
    apply H3. unshelve erewrite (_ : s2 = snd (eq_sys_union s1 x y)).
    destruct res as [ [ [ t1 t2 ] | ] s1' ]; good_inversion H2; rewrite Heqres; auto.
    apply eq_sys_union_unifies. apply H1.
  * remember (eq_sys_find s1 x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H2.
    - unfold is_eq_sys_unifier. etransitivity; [ | apply H4; left; auto ].
      apply H3. destruct (H1 x) as [ p H ].
      eapply eq_sys_image_find_apply; eauto. rewrite Heqres. auto.
    - apply H3. apply eq_sys_bind_unifies. apply H1.
  * remember (eq_sys_find s1 x) as res. symmetry in Heqres.
    destruct res as [ x' [ t | ] ]; good_inversion H2.
    - unfold is_eq_sys_unifier. etransitivity; [ | apply H4; left; auto ].
      apply H3. destruct (H1 x) as [ p H ].
      eapply eq_sys_image_find_apply; eauto. rewrite Heqres. auto.
    - unfold is_eq_sys_unifier. etransitivity. apply H3. apply eq_sys_bind_unifies. apply H1.
      simpl. constructor. apply (H4 (Var n1)). left. auto.
      apply (H4 (Var (S n1))). right. left. auto.
  * good_inversion H2. unfold is_eq_sys_unifier. symmetry. apply H4. left. auto.
  * destruct (name_eq_dec c1 c2); good_inversion H2. unfold is_eq_sys_unifier. reflexivity.
  * inversion H2.
  * good_inversion H2. unfold is_eq_sys_unifier. symmetry. apply H4. left. auto.
  * inversion H2.
  * destruct (name_eq_dec c1 c2); good_inversion H2. unfold is_eq_sys_unifier. simpl.
    constructor; apply H4. left. auto. right. left. auto.
Qed.

Lemma rt_unify_unifies t1 t2 s s' n (H1 : unification_state_wf (s, n))
                       (H2 : forall x, In x (fv_term t1) -> x < n)
                       (H3 : forall x, In x (fv_term t2) -> x < n)
                       (H4 : (s, n) == t1 |_| t2 => (Some s'))
                     : is_eq_sys_unifier (fst s') t1 t2
with rt_unify_many_unifies ts s s' n (H1 : unification_state_wf (s, n))
                           (H2 : forall x, In x (fv_terms_list ts) -> x < n)
                           (H3 : rt_unify_many (s, n) ts (Some s'))
                         : forall t1 t2, In (t1, t2) ts -> is_eq_sys_unifier (fst s') t1 t2
with rt_unify_saves_unifier t1 t2 t1' t2' s s' n (H1 : unification_state_wf (s, n))
                            (H2 : forall x, In x (fv_term t1') -> x < n)
                            (H3 : forall x, In x (fv_term t2') -> x < n)
                            (H4 : is_eq_sys_unifier s t1 t2)
                            (H5 : (s, n) == t1' |_| t2' => (Some s'))
                          : is_eq_sys_unifier (fst s') t1 t2
with rt_unify_many_saves_unifier t1 t2 ts s s' n (H1 : unification_state_wf (s, n))
                                 (H2 : forall x, In x (fv_terms_list ts) -> x < n)
                                 (H3 : is_eq_sys_unifier s t1 t2)
                                 (H4 : rt_unify_many (s, n) ts (Some s'))
                               : is_eq_sys_unifier (fst s') t1 t2.
Proof.
  * good_inversion H4. destruct s2 as [ s2 n2 ].
    set (H6 := H5). apply rt_unification_step_wf in H6; auto. destruct H6 as [ H6 [ H7 H8 ] ].
    eapply rt_unification_step_unifies in H5; eauto. apply H1.
  * good_inversion H3; try destruct s2 as [ s2 n2 ]; intros. inversion H.
    destruct H3. good_inversion H3.
    - set (H3 := H). apply rt_unify_wf in H3; auto. destruct H3 as [ H3 H4 ].
      simpl in *. eapply rt_unify_many_saves_unifier in H0; eauto.
      + intros. eapply PeanoNat.Nat.lt_le_trans. apply H2. apply set_union_intro2. eauto. auto.
      + eapply rt_unify_unifies in H; eauto; intros; apply H2;
          apply set_union_intro1; apply fv_terms_In; auto.
      + intros. apply H2. apply set_union_intro1. auto.
    - apply rt_unify_wf in H; auto.
      eapply rt_unify_many_unifies in H0; eauto. apply H.
      intros. eapply PeanoNat.Nat.lt_le_trans. apply H2. apply set_union_intro2. auto. apply H.
      intros. apply H2. apply set_union_intro1. auto.
  * good_inversion H5. destruct s2 as [ s2 n2 ].
    set (H7 := H6). apply rt_unification_step_wf in H7; auto. destruct H7 as [ H7 [ H8 H9 ] ].
    eapply rt_unification_step_saves_unifier in H6; eauto.
  * good_inversion H4; try destruct s2 as [ s2 n2 ]. auto.
    set (H4 := H). apply rt_unify_wf in H4; auto. destruct H4.
    eapply rt_unify_saves_unifier in H; eauto.
    eapply rt_unify_many_saves_unifier in H0; eauto.
    - intros. eapply PeanoNat.Nat.lt_le_trans. apply H2. apply set_union_intro2. auto. auto.
    - intros. apply H2. apply set_union_intro1. apply fv_terms_In. auto.
    - intros. apply H2. apply set_union_intro1. apply fv_terms_In. auto.
    - intros. apply H2. apply set_union_intro1. auto.
Qed.
*)

Definition is_more_general_eq_sys (m s : eq_sys) : Prop :=
  exists s', forall t, inf_term_eq (eq_sys_apply s t) (apply_inf_subst s' (eq_sys_apply m t)).

Lemma rt_unify_is_most_general t1 t2 s s1 s2 n (H1 : unification_state_wf (s1, n))
                               (H2 : forall x, In x (fv_term t1) -> x < n)
                               (H3 : forall x, In x (fv_term t2) -> x < n)
                               (H4 : is_eq_sys_unifier s t1 t2)
                               (H5 : (s1, n) == t1 |_| t2 => (Some s2))
                             : is_more_general_eq_sys (fst s2) s
with rt_unify_many_is_most_general ts s s1 s2 n (H1 : unification_state_wf (s1, n))
                                   (H2 : forall x, In x (fv_terms_list ts) -> x < n)
                                   (H3 : forall t1 t2, In (t1, t2) ts -> is_eq_sys_unifier s t1 t2)
                                   (H4 : rt_unify_many (s1, n) ts (Some s2))
                                 : is_more_general_eq_sys (fst s2) s.
Admitted.

Definition is_mgu_eq_sys (s : eq_sys) (t1 t2 : term) :=
  is_eq_sys_unifier s t1 t2 /\ forall s', is_eq_sys_unifier s' t1 t2 -> is_more_general_eq_sys s s'.
