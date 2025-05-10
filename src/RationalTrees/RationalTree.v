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

Module NatLebTotal <: TotalLeBool'.

Include Nat.

Lemma leb_total x y : (x <=? y) = true \/ (y <=? x) = true.
Proof.
  repeat rewrite leb_compare. rewrite compare_antisym.
  destruct (y ?= x); auto.
Qed.

End NatLebTotal.

Module SortNat := Sort NatLebTotal.

Module NatFstLebTotal (T : Typ) <: TotalLeBool'.

Definition t : Type := nat * T.t.

Definition leb (x y : t) := NatLebTotal.leb (fst x) (fst y).

Lemma leb_total (x y : t) : leb x y = true \/ leb y x = true.
Proof. destruct x; destruct y. apply NatLebTotal.leb_total. Qed.

End NatFstLebTotal.

Module PairNatNameLebTotal := NatFstLebTotal Nat.

Module SortPairNatName := Sort PairNatNameLebTotal.

Lemma NoDup_length [A] (xs ys : list A) (H1 : NoDup xs) (H2 : NoDup ys)
                   (H : forall a, In a xs <-> In a ys)
                 : length xs = length ys.
Proof. apply Nat.le_antisymm; apply NoDup_incl_length; auto; intros a H'; apply H; auto. Qed.

Lemma filter_filter [A] f g (xs : list A)
                  : filter f (filter g xs) = filter (fun x => (f x && g x)%bool) xs.
Proof.
  induction xs as [ | x xs ]. auto. simpl.
  destruct (g x); simpl; destruct (f x); simpl. f_equal. apply IHxs. all: apply IHxs.
Qed.

Lemma filter_comm [A] f g (xs : list A) : filter f (filter g xs) = filter g (filter f xs).
Proof.
  etransitivity. apply filter_filter. symmetry. etransitivity. apply filter_filter.
  apply filter_ext. intro x. apply Bool.andb_comm.
Qed.

Lemma filter_involutive [A] f (xs : list A) : filter f (filter f xs) = filter f xs.
Proof. etransitivity. apply filter_filter. apply filter_ext. intro x. apply Bool.andb_diag. Qed.

Lemma fold_left_comm_aux [A B] (f : B -> A -> B) xs x acc
                         (H : forall x y acc, f (f acc x) y = f (f acc y) x)
                       : fold_left f xs (f acc x) = f (fold_left f xs acc) x.
Proof.
  generalize dependent acc. induction xs as [ | x' xs ]; intros. auto.
  simpl. rewrite H. apply IHxs.
Qed.

Lemma fold_left_comm [A B] (f : B -> A -> B) xs ys acc
                     (H : forall x y acc, f (f acc x) y = f (f acc y) x)
                   : fold_left f xs (fold_left f ys acc) = fold_left f ys (fold_left f xs acc).
Proof.
  generalize dependent acc. generalize dependent ys. induction xs as [ | x xs ]; intros. auto.
  etransitivity. 2: simpl; apply IHxs. simpl. f_equal. destruct ys. auto. simpl.
  rewrite <- fold_left_comm_aux; auto. rewrite H. auto.
Qed.

Lemma fold_left_perm [A B] (f : B -> A -> B) xs ys acc
                     (H1 : forall x y acc, f (f acc x) y = f (f acc y) x)
                     (H2 : NoDup xs) (H3 : NoDup ys) (H4 : forall x, In x xs <-> In x ys)
         : fold_left f xs acc = fold_left f ys acc.
Proof.
  generalize dependent acc. generalize dependent ys. induction xs as [ | x xs ]; intros.
  * destruct ys as [ | y ys ]. auto. absurd (In y []). auto. apply H4. left. auto.
* refine (_ : fold_left _ xs (fold_left _ [x] acc) = _). rewrite fold_left_comm; auto.
    destruct (in_split x ys) as [ ys1 [ ys2 H ] ]. apply H4. left. auto. subst.
    rewrite fold_left_app. refine (_ : _ = fold_left _ ys2 (fold_left _ [x] _)).
    rewrite (fold_left_comm _ ys2 [x]); auto. f_equal. rewrite <- fold_left_app.
    apply NoDup_cons_iff in H2. destruct H2. apply IHxs. auto. eapply NoDup_remove_1. eauto.
    intro y. constructor; intro.
    - assert (In y (ys1 ++ x :: ys2)). apply H4. right. auto.
      apply in_app_iff. apply in_app_iff in H5. destruct H5. left. auto.
      apply (in_app_iff [x]) in H5. destruct H5. good_inversion H5. contradiction. inversion H6.
      right. auto.
    - assert (In y (x :: xs)). apply H4. apply in_app_iff. apply in_app_iff in H2. destruct H2.
      left. auto. right. right. auto.
      good_inversion H5; auto. exfalso. eapply NoDup_remove_2; eauto.
Qed.

Lemma fold_left_nodup [A B] (f : B -> A -> B) xs acc
                      (H1 : forall (x y : A), {x = y} + {x <> y})
                      (H2 : forall x acc, f (f acc x) x = f acc x)
                      (H3 : forall x y acc, f (f acc x) y = f (f acc y) x)
                    : fold_left f xs acc = fold_left f (nodup H1 xs) acc.
Proof.
  generalize dependent acc. induction xs as [ | x xs ]; intros. auto.
  simpl. destruct (in_dec H1 x xs); simpl. 2: apply IHxs. etransitivity. 2: apply IHxs.
  clear IHxs. apply in_split in i. destruct i as [ xs1 [ xs2 H ] ]. subst.
  refine (_ : fold_left _ (xs1 ++ [x] ++ xs2) _ = _). rewrite fold_left_app.
  rewrite fold_left_comm; auto. simpl. rewrite H2.
  refine (_ : fold_left _ _ (fold_left _ (x::xs2) _) = _).
  rewrite fold_left_comm; auto. rewrite <- fold_left_app. auto.
Qed.

Lemma app_StronglySorted [A] (R : A -> A -> Prop) xs ys
                         (H1 : Sorted.StronglySorted R xs) (H2 : Sorted.StronglySorted R ys)
                         (H : forall x y, In x xs -> In y ys -> R x y)
                       : Sorted.StronglySorted R (xs ++ ys).
Proof.
  induction H1 as [ | x xs ]. auto. simpl. constructor. apply IHStronglySorted.
  intros. apply H; auto. right. auto.
  apply Forall_forall. intros. apply in_app_iff in H3. destruct H3.
  * eapply Forall_forall in H0. apply H0. auto.
  * apply H. left. auto. auto.
Qed.

Lemma map_LocallySorted [A B] (R : B -> B -> Prop) (f : A -> B) xs
                 (H : Sorted.LocallySorted (fun x y => R (f x) (f y)) xs)
               : Sorted.LocallySorted R (map f xs).
Proof. induction H as [ | x | x1 x2 xs ]; simpl; constructor; auto. Qed.

Lemma Sorted_ext2 [A] (R1 R2 : A -> A -> Prop) xs
                  (H1 : forall x y, In x xs -> In y xs -> R1 x y -> R2 x y)
                  (H2 : Sorted.LocallySorted R1 xs)
                : Sorted.LocallySorted R2 xs.
Proof.
  induction H2 as [ | x | x1 x2 xs ]; simpl; constructor; auto.
  apply IHLocallySorted. intros. apply H1; auto; right; auto.
  apply H1; auto. left. auto. right. left. auto.
Qed.

Lemma Sorted_ext1 [A] (R1 R2 : A -> A -> Prop) xs (H1 : forall x y, R1 x y -> R2 x y)
                  (H2 : Sorted.LocallySorted R1 xs)
                : Sorted.LocallySorted R2 xs.
Proof. eapply Sorted_ext2. 2: apply H2. intros. auto. Qed.


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

Inductive is_inf_subterm : inf_term -> inf_term -> Prop :=
| EqInfSubterm t1 t2 : inf_term_eq t1 t2 -> is_inf_subterm t1 t2
| ConInfSubtermL n t1 l2 r2 : is_inf_subterm t1 l2 -> is_inf_subterm t1 (ConInf n l2 r2)
| ConInfSubtermR n t1 l2 r2 : is_inf_subterm t1 r2 -> is_inf_subterm t1 (ConInf n l2 r2)
.

CoInductive is_inf_term_FV (x : name) : inf_term -> Prop :=
| VarInfFV : is_inf_term_FV x (VarInf x)
| ConInfFVL n l r : is_inf_term_FV x l -> is_inf_term_FV x (ConInf n l r)
| ConInfFVR n l r : is_inf_term_FV x r -> is_inf_term_FV x (ConInf n l r)
.

Definition is_ground_inf_term (t : inf_term) : Prop := forall x, ~is_inf_term_FV x t.

Lemma CstInf_is_ground_inf_term n : is_ground_inf_term (CstInf n).
Proof. intros x p. inversion p. Qed.

Lemma ConInf_is_ground_inf_term {n l r} (lH : is_ground_inf_term l) (rH : is_ground_inf_term r)
                              : is_ground_inf_term (ConInf n l r).
Proof. intros x p. good_inversion p; [ eapply lH | eapply rH ]; eauto. Qed.

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

Definition rt_term : Set := { t : inf_term | is_rt t }.

Definition ground_rt_term : Set := { t : inf_term | is_rt t /\ is_ground_inf_term t }.

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
| RootESNode : option term_head -> eq_sys_node
| LinkESNode : name -> eq_sys_node
.

Definition eq_sys := list (name * eq_sys_node).

Definition eq_sys_trivial : eq_sys := [].

Fixpoint eq_sys_find_step (s : eq_sys) (n : name) : option eq_sys_node :=
match s with
| [] => None
| (n', node) :: s =>
  if name_eq_dec n n' then Some node
  else eq_sys_find_step s n
end.

Lemma eq_sys_find_step_prop s n node (H : eq_sys_find_step s n = Some node)
                          : exists s1 s2, s = s1 ++ (n, node) :: s2
                                       /\ forall node', ~In (n, node') s1.
Proof.
  induction s. inversion H. destruct a as [ n' node' ]. revert H. simpl.
  destruct (name_eq_dec n n'); intro. subst. good_inversion H. exists []. exists s. auto.
  apply IHs in H. destruct H as [ s1 [ s2 [ H1 H2 ] ] ]. subst.
  exists ((n', node') :: s1). exists s2. constructor. auto. intro. intro. eapply H2.
  good_inversion H. good_inversion H0. exfalso. apply n0. auto. eauto.
Qed.

Lemma eq_sys_find_step_extend s n n' node (H1 : n <> n')
                            : eq_sys_find_step s n = eq_sys_find_step ((n', node) :: s) n.
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
Proof. induction s as [ | [ n node ] s ]; simpl; eauto. Qed.

Lemma eq_sys_dom_size (s : eq_sys) : var_set_size (eq_sys_dom s) <= length s.
Proof.
  rewrite <- eq_sys_dom'_size. apply NoDup_incl_length. auto.
  intro. apply eq_sys_dom'_prop.
Qed.

(* TODO: может быть и это определение неверное, ведь некоторые переменные отправляются в себя *)
Definition in_eq_sys_dom (n : name) (s : eq_sys) : Prop :=
  exists node, eq_sys_find_step s n = Some node.

Lemma in_eq_sys_dom_inv n s (H : ~in_eq_sys_dom n s) : eq_sys_find_step s n = None.
Proof.
  unfold in_eq_sys_dom in H. destruct (eq_sys_find_step s n); auto.
  exfalso. apply H. eexists. auto.
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

Lemma eq_sys_dom_size_prop ns s (H1 : NoDup ns) (H2 : forall n, In n ns -> in_eq_sys_dom n s)
                    : length ns <= length s.
Proof.
  etransitivity; try apply eq_sys_dom_size. apply NoDup_incl_length. auto.
  intros n p. apply in_eq_sys_dom_prop. apply H2. auto.
Qed.

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
  apply in_eq_sys_dom_prop in H.
  transitivity (var_set_size (var_set_add n (eq_sys_dom (eq_sys_dom_erase s n)))).
  * apply NoDup_length; try apply set_add_nodup; auto.
    intro n'. constructor; intro Hn'.
    - destruct (name_eq_dec n n'). apply set_add_intro2. auto.
      apply set_add_intro1. apply eq_sys_dom_erase_prop. apply set_remove_iff.
      auto. constructor; auto.
    - apply set_add_elim in Hn'. destruct Hn'. subst. auto.
      apply eq_sys_dom_erase_prop in H0. apply set_remove_iff in H0; auto. destruct H0. auto.
  * transitivity (length (n :: eq_sys_dom (eq_sys_dom_erase s n))); auto. apply NoDup_length.
    - apply set_add_nodup. auto.
    - constructor; auto. intro. apply eq_sys_dom_erase_prop in H0. apply set_remove_iff in H0; auto.
      destruct H0. contradiction.
    - intro n'. constructor; intro Hn'.
      apply set_add_elim in Hn'. destruct Hn'; [ left | right ]; auto.
      good_inversion Hn'; [ apply set_add_intro2 | apply set_add_intro1 ]; auto.
Qed.

Lemma eq_sys_dom_erase_comm s n1 n2
                          : eq_sys_dom_erase (eq_sys_dom_erase s n1) n2
                          = eq_sys_dom_erase (eq_sys_dom_erase s n2) n1.
Proof. apply filter_comm. Qed.

Lemma eq_sys_dom_erase_find_step s n1 n2 (H : n1 <> n2)
                               : eq_sys_find_step (eq_sys_dom_erase s n1) n2
                               = eq_sys_find_step s n2.
Proof.
  induction s as [ | [ n' node' ] s ]. auto. simpl. destruct (name_eq_dec n' n1).
  * subst. destruct (name_eq_dec n2 n1). exfalso. apply H. auto. clear n. apply IHs.
  * simpl. destruct (name_eq_dec n2 n'). auto. apply IHs.
Qed.

Definition eq_sys_dom_erase' s ns := fold_left eq_sys_dom_erase ns s.

Lemma eq_sys_dom_erase'_nodup s ns : eq_sys_dom_erase' s ns
                                   = eq_sys_dom_erase' s (nodup name_eq_dec ns).
Proof. apply fold_left_nodup; intros. apply filter_involutive. apply filter_comm. Qed.

Lemma eq_sys_dom_erase'_ext s ns1 ns2 (H : forall x, In x ns1 <-> In x ns2)
                          : eq_sys_dom_erase' s ns1 = eq_sys_dom_erase' s ns2.
Proof.
  etransitivity. apply eq_sys_dom_erase'_nodup. symmetry.
  etransitivity. apply eq_sys_dom_erase'_nodup.
  apply fold_left_perm; intros. apply eq_sys_dom_erase_comm.
  1, 2: apply NoDup_nodup.
  etransitivity. apply nodup_In. symmetry. etransitivity. apply nodup_In. auto.
Qed.

Lemma eq_sys_dom_erase'_comm s ns1 ns2 : eq_sys_dom_erase' (eq_sys_dom_erase' s ns1) ns2
                                       = eq_sys_dom_erase' (eq_sys_dom_erase' s ns2) ns1.
Proof. apply fold_left_comm. intros. apply eq_sys_dom_erase_comm. Qed.

Lemma eq_sys_dom_erase'_prop s ns n
                           : In n (eq_sys_dom (eq_sys_dom_erase' s ns))
                         <-> In n (eq_sys_dom s) /\ ~In n ns.
Proof.
  generalize dependent s. induction ns as [ | n' ns ]; intros; constructor; intro; simpl in *.
  * constructor; auto.
  * apply H.
  * apply IHns in H. destruct H. apply eq_sys_dom_erase_prop in H.
    apply set_remove_iff in H; auto. destruct H. constructor; auto. intro. destruct H2; auto.
  * apply IHns. destruct H. constructor. apply eq_sys_dom_erase_prop. apply set_remove_iff; auto.
    intro. apply H0. right. auto.
Qed.

Lemma eq_sys_dom_erase'_find_step s n ns (H : ~In n ns)
                                : eq_sys_find_step (eq_sys_dom_erase' s ns) n
                                = eq_sys_find_step s n.
Proof.
  generalize dependent s. induction ns as [ | n' ns ]; intros. auto. etransitivity. apply IHns.
  intro. apply H. right. auto. apply eq_sys_dom_erase_find_step. intro. apply H. left. auto.
Qed.

Definition in_eq_sys_rhs (s : eq_sys) (t : term_head) : Prop :=
  exists n, eq_sys_find_step s n = Some (RootESNode (Some t)).

(* TODO: это определение неверное, вместо первого должно быть что переменная ссылается на None *)
Definition in_eq_sys_vran (n : name) (s : eq_sys) : Prop :=
  ~in_eq_sys_dom n s /\ exists t, in_eq_sys_rhs s t /\ In n (fv_term_head t).

Lemma in_eq_sys_rhs_fv s t n (H1 : in_eq_sys_rhs s t) (H2 : In n (fv_term_head t))
                     : in_eq_sys_dom n s \/ in_eq_sys_vran n s.
Proof.
  destruct (in_dec name_eq_dec n (eq_sys_dom s)). left. apply in_eq_sys_dom_prop. auto.
  right. constructor. intro. apply n0. apply in_eq_sys_dom_prop. auto. exists t. constructor; auto.
Qed.

Lemma in_eq_sys_vran_add_link n s n1 n2 (H : in_eq_sys_vran n ((n1, LinkESNode n2) :: s))
                            : in_eq_sys_vran n s /\ n <> n1.
Proof.
  destruct H as [ H [ t [ [ n' H1 ] H2 ] ] ].
  assert (n <> n1). intro. apply H. apply in_eq_sys_dom_prop. apply set_add_intro2. auto.
  constructor; auto. constructor.
  - intro. apply H. apply in_eq_sys_dom_prop. apply set_add_intro1.
    apply in_eq_sys_dom_prop. auto.
  - exists t. constructor; auto. exists n'. simpl in H1. destruct (name_eq_dec n' n1); auto.
    inversion H1.
Qed.

Inductive eq_sys_name_wf s : name -> var_set -> Prop :=
| RootESNameWF n t : eq_sys_find_step s n = Some (RootESNode t) -> eq_sys_name_wf s n [n]
| LinkESNameWF n n' p : eq_sys_find_step s n = Some (LinkESNode n')
                     -> eq_sys_name_wf s n' p -> eq_sys_name_wf s n (n::p)
.

Lemma eq_sys_name_wf_func s n p1 p2 (H1 : eq_sys_name_wf s n p1) (H2 : eq_sys_name_wf s n p2)
                        : p1 = p2.
Proof.
  generalize dependent p2. induction H1; intros; good_inversion H2; auto.
  all: rewrite H0 in H; good_inversion H. f_equal. apply IHeq_sys_name_wf. auto.
Qed.

Lemma eq_sys_name_wf_cut s n p n' (H1 : In n' p) (H2 : eq_sys_name_wf s n p)
                        : exists p1 p2, p = p1 ++ n' :: p2 /\ eq_sys_name_wf s n' (n'::p2).
Proof.
  generalize dependent n'. induction H2; intros; good_inversion H1.
  exists []. exists []. repeat econstructor. eauto. inversion H0.
  exists []. exists p. repeat econstructor; eauto.
  apply IHeq_sys_name_wf in H0. destruct H0 as [ p1 [ p2 [ H0 H1 ] ] ]. subst.
  exists (n::p1). exists p2. constructor. auto. auto.
Qed.

Lemma eq_sys_name_wf_nonrec s n p (H : eq_sys_name_wf s n p) : NoDup p.
Proof.
  induction H; constructor; auto. constructor. intro. eapply eq_sys_name_wf_cut in H1; eauto.
  destruct H1 as [ p1 [ p2 [ H1 H2 ] ] ].
  assert (Hp : n::p2 = n::p). eapply eq_sys_name_wf_func; eauto. econstructor; eauto.
  good_inversion Hp. specialize (app_assoc p1 [n] p2). simpl. intro. rewrite H1 in H4.
  apply (app_inv_tail_iff p2 []) in H4.
  assert (In n (p1 ++ [n])). apply in_app_iff. right. constructor. auto.
  rewrite <- H4 in H3. inversion H3.
Qed.

Lemma eq_sys_name_wf_nonloop s n p (H : eq_sys_name_wf s n p)
                                 : eq_sys_find_step s n <> Some (LinkESNode n).
Proof.
  intro. set (H' := H). good_inversion H'; rewrite H1 in H0; good_inversion H0.
  apply eq_sys_name_wf_nonrec in H. good_inversion H2; rewrite H0 in H1; good_inversion H1.
  good_inversion H. apply H4. left. auto.
Qed.

Lemma eq_sys_name_wf_in_dom s n p n' (H1 : eq_sys_name_wf s n p) (H2 : In n' p)
                          : in_eq_sys_dom n' s.
Proof.
  induction H1; good_inversion H2. 1, 3: eexists; eauto.
  inversion H0. apply IHeq_sys_name_wf. auto.
Qed.

Lemma eq_sys_name_wf_extend s n p n' node (H1 : ~in_eq_sys_dom n' s) (H2 : eq_sys_name_wf s n p)
                          : eq_sys_name_wf ((n', node) :: s) n p.
Proof.
  induction H2.
  - econstructor. symmetry. etransitivity. symmetry. eauto.
    apply eq_sys_find_step_extend. intro. subst. apply H1. eexists. eauto.
  - econstructor. symmetry. etransitivity. symmetry. eauto.
    apply eq_sys_find_step_extend. intro. subst. apply H1. eexists. eauto. auto.
Qed.

Lemma eq_sys_name_wf_add_root s n1 n2 t p (H : eq_sys_name_wf s n1 p)
                            : exists p', eq_sys_name_wf ((n2, RootESNode t) :: s) n1 p'.
Proof.
  induction H; remember (name_eq_dec n n2) as dec; symmetry in Heqdec; destruct dec; subst.
  * exists [n2]. econstructor. simpl. rewrite Heqdec. eauto.
  * exists [n]. econstructor. simpl. rewrite Heqdec. eauto.
  * exists [n2]. econstructor. simpl. rewrite Heqdec. eauto.
  * destruct IHeq_sys_name_wf as [ p' H1 ]. exists (n::p'). econstructor; eauto. simpl.
    rewrite Heqdec. auto.
Qed.

Lemma eq_sys_name_wf_add_link1 s n1 n2 n p (H1 : eq_sys_name_wf s n p) (H2 : ~In n1 p)
                             : eq_sys_name_wf ((n1, LinkESNode n2) :: s) n p.
Proof.
  induction H1.
  * econstructor. simpl. destruct (name_eq_dec n n1); eauto. exfalso. apply H2. left. auto.
  * econstructor. simpl. destruct (name_eq_dec n n1). exfalso. apply H2. left. auto. eauto.
    apply IHeq_sys_name_wf. intro. apply H2. right. auto.
Qed.

Lemma eq_sys_name_wf_add_link2 s n1 n2 n p p2 (H1 : ~In n1 p2)
                               (H2 : eq_sys_name_wf s n p) (H3 : eq_sys_name_wf s n2 p2)
                             : exists p', eq_sys_name_wf ((n1, LinkESNode n2) :: s) n p'.
Proof.
  induction H2; remember (name_eq_dec n n1) as dec; symmetry in Heqdec; destruct dec; subst.
  * exists (n1::p2). econstructor. simpl. rewrite Heqdec. auto.
    apply eq_sys_name_wf_add_link1; auto.
  * exists [n]. econstructor. simpl. rewrite Heqdec. eauto.
  * exists (n1::p2). econstructor. simpl. rewrite Heqdec. auto.
    apply eq_sys_name_wf_add_link1; auto.
  * destruct IHeq_sys_name_wf as [ p' IH ]. exists (n::p'). econstructor; eauto. simpl.
    rewrite Heqdec. auto.
Qed.

Lemma eq_sys_name_wf_len s n p (H : eq_sys_name_wf s n p) : var_set_size p <= length s.
Proof.
  apply eq_sys_dom_size_prop. eapply eq_sys_name_wf_nonrec. eauto.
  intros n' Hn'. eapply eq_sys_name_wf_in_dom; eauto.
Qed.

Lemma eq_sys_dom_erase_name_wf s n n' p (H1 : n <> n') (H2 : eq_sys_name_wf s n' p)
                               (H3 : ~exists n', eq_sys_find_step s n' = Some (LinkESNode n))
                             : eq_sys_name_wf (eq_sys_dom_erase s n) n' p.
Proof.
  induction H2; set (H' := H); erewrite <- eq_sys_dom_erase_find_step in H';
    eauto; econstructor; eauto.
  apply IHeq_sys_name_wf. intro. subst. apply H3. eexists. eauto.
Qed.

Fixpoint eq_sys_find_path_hlp s (fuel : nat) (ns : var_set) n : option var_set :=
match fuel with
| 0 => None
| S fuel =>
  if in_dec name_eq_dec n ns then
    match eq_sys_find_step s n with
    | None => None
    | Some (RootESNode t) => Some [n]
    | Some (LinkESNode n') =>
      match eq_sys_find_path_hlp s fuel (var_set_remove n ns) n' with
      | None => None
      | Some p => Some (n::p)
      end
    end
  else None
end.

Lemma eq_sys_find_path_hlp_incl s fuel ns n p (H : eq_sys_find_path_hlp s fuel ns n = Some p)
                              : incl p ns.
Proof.
  generalize dependent p. generalize dependent n. generalize dependent ns.
  induction fuel; simpl; intros. inversion H.
  destruct (in_dec name_eq_dec n ns). 2: inversion H.
  destruct (eq_sys_find_step s n) as [ [ t | n' ] | ]. 3: inversion H.
  good_inversion H. intros x Hx. good_inversion Hx. auto. inversion H.
  remember (eq_sys_find_path_hlp s fuel (var_set_remove n ns) n') as cond. symmetry in Heqcond.
  destruct cond as [ p' | ]. 2: inversion H. good_inversion H. intros x Hx. good_inversion Hx. auto.
  eapply set_remove_1. eapply IHfuel. eauto. auto.
Qed.

Lemma eq_sys_find_path_hlp_distinct s fuel ns n p (H1 : NoDup ns)
                                    (H2 : eq_sys_find_path_hlp s fuel ns n = Some p)
                                  : NoDup p.
Proof.
  generalize dependent p. generalize dependent n. generalize dependent ns.
  induction fuel; simpl; intros. inversion H2.
  destruct (in_dec name_eq_dec n ns). 2: inversion H2.
  destruct (eq_sys_find_step s n) as [ [ t | n' ] | ]. 3: inversion H2.
  good_inversion H2. apply NoDup_cons. auto. apply NoDup_nil.
  remember (eq_sys_find_path_hlp s fuel (var_set_remove n ns) n') as cond. symmetry in Heqcond.
  destruct cond as [ p' | ]. 2: inversion H2. good_inversion H2. apply NoDup_cons.
  intro. eapply eq_sys_find_path_hlp_incl in H; eauto. apply set_remove_iff in H; auto.
  destruct H. apply H0. auto.
  eapply IHfuel. 2: eauto. apply set_remove_nodup. auto.
Qed.

Lemma eq_sys_find_path_hlp_prop1 s fuel ns n p (H1 : NoDup ns) (H2 : var_set_size ns <= fuel)
                                 (H3 : eq_sys_find_path_hlp s fuel ns n = Some p)
                               : eq_sys_name_wf s n p.
Proof.
  generalize dependent p. generalize dependent n. generalize dependent ns.
  induction fuel; simpl; intros. inversion H3.
  destruct (in_dec name_eq_dec n ns). 2: inversion H3.
  remember (eq_sys_find_step s n) as cond. symmetry in Heqcond.
  destruct cond as [ [ t | n' ] | ]; good_inversion H3. econstructor. eauto.
  remember (eq_sys_find_path_hlp s fuel (var_set_remove n ns) n') as p'. symmetry in Heqp'.
  destruct p' as [ p' | ]; good_inversion H0.
  econstructor. eauto. apply (IHfuel (var_set_remove n ns)); auto.
  apply set_remove_nodup. auto.
  set (ns' := filter (fun x => if name_eq_dec x n then false else true) ns).
  assert (var_set_size (var_set_remove n ns) = var_set_size ns'). {
    apply NoDup_length. apply set_remove_nodup. auto. apply NoDup_filter. auto.
    intro x. constructor; intro. apply set_remove_iff in H; auto. destruct H.
    apply filter_In. constructor; auto. destruct (name_eq_dec x n); auto.
    apply filter_In in H. destruct H. apply set_remove_iff; auto. constructor; auto.
    destruct (name_eq_dec x n); auto. inversion H0.
  }
  rewrite H. clear H.
  assert (S (var_set_size ns') = var_set_size ns). {
    symmetry. etransitivity. symmetry. eapply filter_length. rewrite Nat.add_comm.
    refine (_ : _ + var_set_size ns' = 1 + var_set_size ns').
    apply Nat.add_cancel_r. refine (_ : _ = length [n]).
    apply NoDup_length. apply NoDup_filter. auto. apply NoDup_cons; auto. apply NoDup_nil.
    intro x. constructor; intro. apply filter_In in H. destruct H.
    destruct (name_eq_dec x n). subst. left. auto. inversion H0.
    good_inversion H. apply filter_In. constructor; auto.
    destruct (name_eq_dec x x); auto. inversion H0.
  }
  rewrite <- H in H2. apply le_S_n in H2. auto.
Qed.

Lemma eq_sys_find_path_hlp_prop2 s fuel ns n p (H1 : NoDup ns) (H2 : var_set_size ns <= fuel)
                                 (H3 : incl p ns) (H4 : eq_sys_name_wf s n p)
                               : eq_sys_find_path_hlp s fuel ns n = Some p.
Proof.
  generalize dependent ns. generalize dependent fuel. induction H4; intros.
  * destruct fuel.
    - good_inversion H2. apply length_zero_iff_nil in H4. subst.
      absurd (In n []). auto. apply H3. left. auto.
    - simpl. destruct (in_dec name_eq_dec n ns). rewrite H. auto.
      exfalso. apply n0. apply H3. left. auto.
  * destruct fuel.
    - good_inversion H2. apply length_zero_iff_nil in H5. subst.
      absurd (In n []). auto. apply H3. left. auto.
    - simpl. destruct (in_dec name_eq_dec n ns). rewrite H. rewrite IHeq_sys_name_wf; auto.
      apply set_remove_nodup. auto.
      set (ns' := filter (fun x => if name_eq_dec x n then false else true) ns).
      assert (var_set_size (var_set_remove n ns) = var_set_size ns'). {
        apply NoDup_length. apply set_remove_nodup. auto. apply NoDup_filter. auto.
        intro x. constructor; intro. apply set_remove_iff in H0; auto. destruct H0.
        apply filter_In. constructor; auto. destruct (name_eq_dec x n); auto.
        apply filter_In in H0. destruct H0. apply set_remove_iff; auto. constructor; auto.
        destruct (name_eq_dec x n); auto. inversion H5.
      }
      rewrite H0. clear H0.
      assert (S (var_set_size ns') = var_set_size ns). {
        symmetry. etransitivity. symmetry. eapply filter_length. rewrite Nat.add_comm.
        refine (_ : _ + var_set_size ns' = 1 + var_set_size ns').
        apply Nat.add_cancel_r. refine (_ : _ = length [n]).
        apply NoDup_length. apply NoDup_filter. auto. apply NoDup_cons; auto. apply NoDup_nil.
        intro x. constructor; intro. apply filter_In in H0. destruct H0.
        destruct (name_eq_dec x n). subst. left. auto. inversion H5.
        good_inversion H0. apply filter_In. constructor; auto.
        destruct (name_eq_dec x x); auto. inversion H5.
      }
      rewrite <- H0 in H2. apply le_S_n in H2. auto.
      intros x Hx. destruct (name_eq_dec x n).
      subst. absurd (NoDup (n :: p)). intro. good_inversion H0. apply H7. auto.
      eapply eq_sys_name_wf_nonrec. econstructor; eauto.
      apply set_remove_iff. auto. constructor; auto. apply H3. right. auto.
      exfalso. apply n0. apply H3. left. auto.
Qed.

Lemma eq_sys_find_path_hlp_prop s fuel ns n p (H1 : NoDup ns) (H2 : var_set_size ns <= fuel)
                              : eq_sys_find_path_hlp s fuel ns n = Some p
                            <-> incl p ns /\ eq_sys_name_wf s n p.
Proof.
  constructor; intro.
  * constructor. eapply eq_sys_find_path_hlp_incl. eauto. eapply eq_sys_find_path_hlp_prop1; eauto.
  * destruct H. eapply eq_sys_find_path_hlp_prop2; eauto.
Qed.

Definition eq_sys_find_path s n := eq_sys_find_path_hlp s (length s) (eq_sys_dom s) n.

Lemma eq_sys_find_path_prop s n p : eq_sys_find_path s n = Some p <-> eq_sys_name_wf s n p.
Proof.
  destruct (eq_sys_find_path_hlp_prop s (length s) (eq_sys_dom s) n p). auto.
  apply eq_sys_dom_size. constructor; intro. apply H. auto. apply H0. constructor; auto.
  intros x Hx. apply in_eq_sys_dom_prop. eapply eq_sys_name_wf_in_dom; eauto.
Qed.

Lemma eq_sys_name_wf_dec' s n : { p | eq_sys_name_wf s n p } + {~exists p, eq_sys_name_wf s n p}.
Proof.
  remember (eq_sys_find_path s n) as p. symmetry in Heqp. destruct p as [ p | ].
  * left. exists p. apply eq_sys_find_path_prop. auto.
  * right. intro. destruct H as [ p H ]. apply eq_sys_find_path_prop in H. rewrite Heqp in H.
    inversion H.
Qed.

Lemma eq_sys_name_wf_dec s n : {exists p, eq_sys_name_wf s n p} + {~exists p, eq_sys_name_wf s n p}.
Proof. destruct (eq_sys_name_wf_dec' s n); eauto. destruct s0. left. eexists. eauto. Qed.

Definition eq_sys_wf s : Prop := forall n, in_eq_sys_dom n s -> exists p, eq_sys_name_wf s n p.

Lemma eq_sys_trivial_wf : eq_sys_wf eq_sys_trivial.
Proof. intros n [ node H ]. inversion H. Qed.

Lemma eq_sys_wf_add_root s n t (H1 : eq_sys_wf s) : eq_sys_wf ((n, RootESNode t) :: s).
Proof.
  intros n' H. apply in_eq_sys_dom_prop in H. simpl in H. apply set_add_elim in H. destruct H.
  * subst. exists [n]. econstructor. simpl. destruct (name_eq_dec n n); auto. contradiction.
  * apply in_eq_sys_dom_prop in H. apply H1 in H. destruct H as [ p H ].
    eapply eq_sys_name_wf_add_root. eauto.
Qed.

Lemma eq_sys_wf_add_link s n1 n2 p (H1 : eq_sys_wf s) (H2 : eq_sys_name_wf s n2 p) (H3 : ~In n1 p)
                       : eq_sys_wf ((n1, LinkESNode n2) :: s).
Proof.
  intros n' H. apply in_eq_sys_dom_prop in H. simpl in H. apply set_add_elim in H. destruct H.
  * subst. exists (n1::p). econstructor. simpl. destruct (name_eq_dec n1 n1); auto. contradiction.
    apply eq_sys_name_wf_add_link1; auto.
  * apply in_eq_sys_dom_prop in H. apply H1 in H. destruct H as [ p' H ].
    eapply eq_sys_name_wf_add_link2; eauto.
Qed.

Lemma eq_sys_dom_erase_wf s n (H1 : eq_sys_wf s)
                          (H2 : ~exists n', eq_sys_find_step s n' = Some (LinkESNode n))
                        : eq_sys_wf (eq_sys_dom_erase s n).
Proof.
  intros n1 H3. apply in_eq_sys_dom_prop in H3. apply eq_sys_dom_erase_prop in H3.
  apply set_remove_iff in H3; auto. destruct H3. apply in_eq_sys_dom_prop in H.
  destruct (H1 n1 H) as [ p H3 ]. exists p. apply eq_sys_dom_erase_name_wf; auto.
Qed.

Definition eq_sys_path_size (s : eq_sys) (n : name) : nat :=
match eq_sys_name_wf_dec' s n with
| inleft (exist _ p _) => var_set_size p
| inright _ => 0
end.

Lemma eq_sys_path_size_prop s n1 n2 (H1 : exists p, eq_sys_name_wf s n1 p)
                            (H2 : eq_sys_find_step s n1 = Some (LinkESNode n2))
                          : eq_sys_path_size s n1 = S (eq_sys_path_size s n2).
Proof.
  unfold eq_sys_path_size. destruct (eq_sys_name_wf_dec' s n1) as [ [ p1 H3 ] | H ].
  good_inversion H3; rewrite H2 in H; good_inversion H.
  destruct (eq_sys_name_wf_dec' s n') as [ [ p2 H4 ] | H ].
  rewrite (eq_sys_name_wf_func s n' p p2); auto.
  exfalso. apply H. eexists. eauto.
  exfalso. apply H. auto.
Qed.

Definition eq_sys_topsort (s : eq_sys) (ns : list name) : list name :=
  map snd (SortPairNatName.sort (map (fun n => (eq_sys_path_size s n, n)) ns)).

Lemma eq_sys_topsort_perm s ns n : In n ns <-> In n (eq_sys_topsort s ns).
Proof.
  constructor; intro.
  * unfold eq_sys_topsort. apply in_map_iff. exists (eq_sys_path_size s n, n).
    constructor; auto. eapply Permutation.Permutation_in. apply SortPairNatName.Permuted_sort.
    apply in_map_iff. exists n. constructor; auto.
  * apply in_map_iff in H. destruct H as [ [ v n' ] [ H1 H ] ]. simpl in H1.
    subst. eapply Permutation.Permutation_in in H.
    2: apply Permutation.Permutation_sym; apply SortPairNatName.Permuted_sort.
    apply in_map_iff in H. destruct H as [ n' [ H1 H ] ]. good_inversion H1. auto.
Qed.

(* topsort is reversed! only links to the tail allowed *)
Inductive is_eq_sys_topsort s : list name -> Prop :=
| NilTopsort : is_eq_sys_topsort s []
| ConsTopsort n ns : (forall n', eq_sys_find_step s n = Some (LinkESNode n') -> ~In n' ns)
                  -> is_eq_sys_topsort s ns -> is_eq_sys_topsort s (n::ns)
.

Definition eq_sys_topsort_local s n1 n2 := eq_sys_path_size s n1 <= eq_sys_path_size s n2.

Lemma eq_sys_topsort_local_trans s : Relations_1.Transitive (eq_sys_topsort_local s).
Proof. intros x y z. intros. eapply Nat.le_trans; eauto. Qed.

Lemma is_eq_sys_topsort_prop s ns (H1 : eq_sys_wf s)
                                  (H2 : Sorted.StronglySorted (eq_sys_topsort_local s) ns)
                                : is_eq_sys_topsort s ns.
Proof.
  induction H2 as [ | n ns ]; constructor; auto.
  intros n' H3 H4. apply eq_sys_path_size_prop in H3. eapply Forall_forall in H; eauto.
  unfold eq_sys_topsort_local in H. rewrite H3 in H. lia.
  apply H1. econstructor. eauto.
Qed.

Lemma eq_sys_topsort_prop s ns (H : eq_sys_wf s) : is_eq_sys_topsort s (eq_sys_topsort s ns).
Proof.
  apply is_eq_sys_topsort_prop. auto. apply Sorted.Sorted_StronglySorted.
  intros x y z. intros. eapply eq_sys_topsort_local_trans; eauto.
  apply Sorted.Sorted_LocallySorted_iff. unfold eq_sys_topsort_local. apply map_LocallySorted.
  eapply Sorted_ext2. 2: apply SortPairNatName.LocallySorted_sort.
  intros. eapply Permutation.Permutation_in in H0, H1. apply in_map_iff in H0, H1.
  2, 3: apply Permutation.Permutation_sym; apply SortPairNatName.Permuted_sort.
  destruct H0 as [ x' [ Hx1 Hx2 ] ]. destruct H1 as [ y' [ Hy1 Hy2 ] ].
  subst. simpl in H2. specialize (Nat.leb_spec (eq_sys_path_size s x') (eq_sys_path_size s y')).
  intro. rewrite H2 in H0. good_inversion H0. apply H1.
Qed.

Lemma eq_sys_dom_erase'_wf_aux s ns (H1 : eq_sys_wf s)
                               (H2 : forall n n', eq_sys_find_step s n' = Some (LinkESNode n)
                                               -> ~In n' ns -> ~In n ns)
                               (H3 : is_eq_sys_topsort s ns)
                             : eq_sys_wf (eq_sys_dom_erase' s ns).
Proof.
  induction H3 as [ | n ns ]; intros. auto.
  refine (_ : eq_sys_wf (eq_sys_dom_erase' (eq_sys_dom_erase' s [n]) ns)).
  rewrite eq_sys_dom_erase'_comm. simpl. apply eq_sys_dom_erase_wf. apply IHis_eq_sys_topsort.
  * intros n2 n1. intros. destruct (name_eq_dec n1 n). subst. apply H. auto.
    intro. eapply H2. eauto. intro. good_inversion H6. contradiction. apply H4. auto. right. auto.
  * intro. destruct H0 as [ n' H0 ].
    assert (in_eq_sys_dom n' (eq_sys_dom_erase' s ns)). eexists. eauto.
    apply in_eq_sys_dom_prop in H4. apply eq_sys_dom_erase'_prop in H4. destruct H4.
    rewrite eq_sys_dom_erase'_find_step in H0; auto. apply in_eq_sys_dom_prop in H4.
    eapply H2; eauto. intro. destruct H6. subst n'. destruct (H1 n H4) as [ p H6 ].
    eapply eq_sys_name_wf_nonloop; eauto. eauto. left. auto.
Qed.

Lemma eq_sys_dom_erase'_wf s ns (H1 : eq_sys_wf s)
                                (H2 : forall n n', eq_sys_find_step s n' = Some (LinkESNode n)
                                                -> ~In n' ns -> ~In n ns)
                         : eq_sys_wf (eq_sys_dom_erase' s ns).
Proof.
  rewrite (eq_sys_dom_erase'_ext _ _ (eq_sys_topsort s ns)). apply eq_sys_dom_erase'_wf_aux; auto.
  intros. intro. eapply H2; eauto. intro. apply H0. apply eq_sys_topsort_perm. auto.
  eapply eq_sys_topsort_perm. eauto. apply eq_sys_topsort_prop. auto.
  intro. apply eq_sys_topsort_perm.
Qed.

Fixpoint eq_sys_find_hlp (s : eq_sys) (fuel : nat) (n : name) : name * option term_head :=
match fuel with
| 0 => (n, None)
| S fuel =>
  match eq_sys_find_step s n with
  | None => (n, None)
  | Some (RootESNode t) => (n, t)
  | Some (LinkESNode n) => eq_sys_find_hlp s fuel n
  end
end.

Lemma eq_sys_find_hlp_fuel_aux s fuel1 fuel2 n p (H : eq_sys_name_wf s n p)
                               (H1 : var_set_size p <= fuel1) (H2 : var_set_size p <= fuel2)
                             : eq_sys_find_hlp s fuel1 n = eq_sys_find_hlp s fuel2 n.
Proof.
  generalize dependent fuel1. generalize dependent fuel2. induction H; intros.
  - good_inversion H1; good_inversion H2; auto; simpl; rewrite H; auto.
  - good_inversion H1; good_inversion H2; auto; simpl; rewrite H;
      apply IHeq_sys_name_wf; simpl in *; try lia.
Qed.

Lemma eq_sys_find_hlp_fuel s fuel1 fuel2 n p (H : eq_sys_name_wf s n p)
                           (H1 : length s <= fuel1) (H2 : length s <= fuel2)
                         : eq_sys_find_hlp s fuel1 n = eq_sys_find_hlp s fuel2 n.
Proof.
  eapply eq_sys_find_hlp_fuel_aux; eauto;
    transitivity (length s); try auto;
    eapply eq_sys_name_wf_len; eauto.
Qed.

Lemma eq_sys_find_hlp_ext {s1 s2 fuel n p1 p2}
                          (H1 : eq_sys_name_wf s1 n p1) (H2 : eq_sys_name_wf s2 n p2)
                          (Hfuel1 : var_set_size p1 <= fuel) (Hfuel2 : var_set_size p2 <= fuel)
                          (H : forall n' p1' p2', eq_sys_name_wf s1 n' p1'
                                               -> eq_sys_name_wf s2 n' p2'
                                               -> eq_sys_find_step s1 n' = eq_sys_find_step s2 n')
                        : eq_sys_find_hlp s1 fuel n = eq_sys_find_hlp s2 fuel n.
Proof.
  generalize dependent p2. generalize dependent p1. generalize dependent n.
  generalize dependent fuel. induction fuel; intros. auto. simpl.
  specialize (H _ _ _ H1 H2). rewrite H; eauto.
  good_inversion H1; good_inversion H2; rewrite H1; auto.
  absurd (Some (RootESNode t) = Some (LinkESNode n')). intro. inversion H2.
  etransitivity. symmetry. apply H0. etransitivity. eapply H; eauto. apply H1.
  unshelve eapply (IHfuel _ p _ _ p0); auto; simpl in *; try lia.
  assert (Some (LinkESNode n') = Some (LinkESNode n'0)). etransitivity. symmetry. eauto.
  etransitivity. apply H. auto. good_inversion H2. apply H3.
Qed.

Lemma eq_sys_find_hlp_no {s fuel n} (H : eq_sys_find_step s n = None)
                       : eq_sys_find_hlp s fuel n = (n, None).
Proof. destruct fuel. auto. simpl. rewrite H. auto. Qed.

Lemma eq_sys_find_hlp_some s fuel n n' t (H : eq_sys_find_hlp s fuel n = (n', Some t))
                         : eq_sys_find_step s n' = Some (RootESNode (Some t)).
Proof.
  generalize dependent n. induction fuel; intros. inversion H. simpl in H.
  remember (eq_sys_find_step s n) as res. symmetry in Heqres.
  destruct res as [ [ t' | n'' ] | ]; good_inversion H. auto.
  apply IHfuel in H1. auto.
Qed.

Lemma eq_sys_find_hlp_root s fuel n p (H1 : eq_sys_name_wf s n p) (H2 : var_set_size p <= fuel)
                         : eq_sys_find_step s (fst (eq_sys_find_hlp s fuel n))
                         = Some (RootESNode (snd (eq_sys_find_hlp s fuel n))).
Proof.
  generalize dependent fuel. induction H1; intros; good_inversion H2; simpl; rewrite H; auto.
  apply IHeq_sys_name_wf. simpl in H0. lia.
Qed.

Lemma eq_sys_find_hlp_last s fuel n1 n2 p (H1 : eq_sys_name_wf s n1 p) (H2 : var_set_size p <= fuel)
                           (H3 : fst (eq_sys_find_hlp s fuel n1) = n2)
                         : exists p', p = p' ++ [n2].
Proof.
  generalize dependent fuel. induction H1; intros.
  * destruct fuel. inversion H2. simpl in H3. rewrite H in H3. good_inversion H3. exists []. auto.
  * destruct fuel. inversion H2. simpl in H3. rewrite H in H3. apply IHeq_sys_name_wf in H3.
    destruct H3 as [ p' H3 ]. exists (n::p'). rewrite H3. auto. simpl in H2. lia.
Qed.

Definition eq_sys_find s n := eq_sys_find_hlp s (length s) n.

Lemma eq_sys_find_ext {s1 s2 n p1 p2} (H1 : eq_sys_name_wf s1 n p1) (H2 : eq_sys_name_wf s2 n p2)
                      (H : forall n' p1' p2', eq_sys_name_wf s1 n' p1'
                                           -> eq_sys_name_wf s2 n' p2'
                                           -> eq_sys_find_step s1 n' = eq_sys_find_step s2 n')
                    : eq_sys_find s1 n = eq_sys_find s2 n.
Proof.
  set (fuel := max (length s1) (length s2)).
  transitivity (eq_sys_find_hlp s1 fuel n). eapply eq_sys_find_hlp_fuel; eauto. lia.
  transitivity (eq_sys_find_hlp s2 fuel n). eapply eq_sys_find_hlp_ext; eauto.
  transitivity (length s1); try lia. eapply eq_sys_name_wf_len; eauto.
  transitivity (length s2); try lia. eapply eq_sys_name_wf_len; eauto.
  eapply eq_sys_find_hlp_fuel; eauto. lia.
Qed.

Lemma eq_sys_find_link s n1 n2 p (H1 : eq_sys_name_wf s n1 p)
                       (H2 : eq_sys_find_step s n1 = Some (LinkESNode n2))
                     : eq_sys_find s n1 = eq_sys_find s n2.
Proof.
  unfold eq_sys_find at 1. erewrite (eq_sys_find_hlp_fuel _ _ (S (length s))); eauto.
  simpl. rewrite H2. auto.
Qed.

Lemma eq_sys_find_no {s n} (H : eq_sys_find_step s n = None) : eq_sys_find s n = (n, None).
Proof. apply eq_sys_find_hlp_no. auto. Qed.

Lemma eq_sys_find_some s n n' t (H : eq_sys_find s n = (n', Some t))
                     : eq_sys_find_step s n' = Some (RootESNode (Some t)).
Proof. eapply eq_sys_find_hlp_some. eauto. Qed.

Lemma eq_sys_find_root s n p (H : eq_sys_name_wf s n p)
                     : eq_sys_find_step s (fst (eq_sys_find s n))
                     = Some (RootESNode (snd (eq_sys_find s n))).
Proof. eapply eq_sys_find_hlp_root. eauto. eapply eq_sys_name_wf_len. eauto. Qed.

Lemma eq_sys_find_root_inv s n t (H : eq_sys_find_step s n = Some (RootESNode t))
                         : eq_sys_find s n = (n, t).
Proof.
  unfold eq_sys_find. unshelve erewrite (_ : length s = S (pred (length s))).
  destruct s. inversion H. auto. simpl. rewrite H. auto.
Qed.

Lemma eq_sys_find_in_path s n1 n2 p (H1 : eq_sys_name_wf s n1 p) (H2 : In n2 p)
                        : eq_sys_find s n1 = eq_sys_find s n2.
Proof.
  induction H1; intros.
  * good_inversion H2; [ | inversion H0 ]. auto.
  * good_inversion H2. auto. etransitivity. eapply eq_sys_find_link; eauto. eright; eauto.
    apply IHeq_sys_name_wf. auto.
Qed.

Lemma eq_sys_find_last s n1 n2 p (H1 : eq_sys_name_wf s n1 p) (H2 : fst (eq_sys_find s n1) = n2)
                     : exists p', p = p' ++ [n2].
Proof. eapply eq_sys_find_hlp_last in H2; eauto. eapply eq_sys_name_wf_len. eauto. Qed.

Lemma eq_sys_dom_erase'_find s ns n p1 p2 (H1 : eq_sys_name_wf s n p1)
                             (H2 : eq_sys_name_wf (eq_sys_dom_erase' s ns) n p2)
                           : eq_sys_find (eq_sys_dom_erase' s ns) n = eq_sys_find s n.
Proof.
  eapply eq_sys_find_ext; eauto. intros. apply eq_sys_dom_erase'_find_step.
  assert (in_eq_sys_dom n' (eq_sys_dom_erase' s ns)). good_inversion H; eexists; eauto.
  apply in_eq_sys_dom_prop in H3. apply eq_sys_dom_erase'_prop in H3. apply H3.
Qed.

CoFixpoint eq_sys_image (s : eq_sys) (n : name) : inf_term :=
match eq_sys_find s n with
| (n, None) => VarInf n
| (_, Some (CstHead n)) => CstInf n
| (_, Some (ConHead n n1 n2)) => ConInf n (eq_sys_image s n1) (eq_sys_image s n2)
end.

CoFixpoint eq_sys_image_ext {s s'} n (H : forall n', eq_sys_find s n' = eq_sys_find s' n')
                          : inf_term_eq (eq_sys_image s n) (eq_sys_image s' n) :=
rew <- [fun x => inf_term_eq x _] inf_term_step_prop (eq_sys_image s n) in
rew <- [fun x => inf_term_eq _ x] inf_term_step_prop (eq_sys_image s' n) in
rew <- [fun x => inf_term_eq (match (match x with (_, _) => _ end) return inf_term with
                              | VarInf _ => _
                              | CstInf _ => _
                              | ConInf _ _ _ => _
                              end) (inf_term_step (eq_sys_image s' n))] H n in
match eq_sys_find s' n as res
return inf_term_eq
  (inf_term_step (match res with
                  | (_, None) => _
                  | (_, Some (CstHead _)) => _
                  | (_, Some (ConHead _ _ _)) => _
                  end))
  (inf_term_step (match res with
                  | (_, None) => _
                  | (_, Some (CstHead _)) => _
                  | (_, Some (ConHead _ _ _)) => _
                  end))
with
| (n, None) => VarInfEq n : inf_term_eq (inf_term_step (VarInf n)) (inf_term_step (VarInf n))
| (_, Some (CstHead n)) =>
  CstInfEq n : inf_term_eq (inf_term_step (CstInf n)) (inf_term_step (CstInf n))
| (_, Some (ConHead n n1 n2)) =>
  ConInfEq n _ _ _ _ (eq_sys_image_ext n1 H) (eq_sys_image_ext n2 H)
    : inf_term_eq (inf_term_step (ConInf _ _ _)) (inf_term_step (ConInf _ _ _))
end.

Fixpoint apply_eq_sys (s : eq_sys) (t : term) : inf_term :=
match t with
| Var n => eq_sys_image s n
| Cst n => CstInf n
| Con n t1 t2 => ConInf n (apply_eq_sys s t1) (apply_eq_sys s t2)
end.

CoFixpoint apply_eq_sys_inf (s : eq_sys) (t : inf_term) : inf_term :=
match t with
| VarInf n => eq_sys_image s n
| CstInf n => CstInf n
| ConInf n t1 t2 => ConInf n (apply_eq_sys_inf s t1) (apply_eq_sys_inf s t2)
end.

Definition eq_sys_ensure_var (s : eq_sys) (n : name) : eq_sys :=
match eq_sys_find_step s n with
| Some _ => s
| None => (n, RootESNode None) :: s
end.

Lemma eq_sys_ensure_var_prop s n1 n2 t (H : eq_sys_find_step (eq_sys_ensure_var s n1) n2
                                          = Some (RootESNode t))
                           : eq_sys_find_step s n2 = Some (RootESNode t) \/ n1 = n2.
Proof.
  unfold eq_sys_ensure_var in H. destruct (eq_sys_find_step s n1). auto.
  simpl in H. destruct (name_eq_dec n2 n1); auto.
Qed.

Lemma eq_sys_ensure_var_id s n (H : in_eq_sys_dom n s) : eq_sys_ensure_var s n = s.
Proof. destruct H as [ node H ]. unfold eq_sys_ensure_var. rewrite H. auto. Qed.

Lemma eq_sys_ensure_var_dom s n1 n2 (H : in_eq_sys_dom n1 (eq_sys_ensure_var s n2))
                          : in_eq_sys_dom n1 s \/ (n1 = n2 /\ ~in_eq_sys_dom n1 s).
Proof.
  unfold eq_sys_ensure_var in H. remember (eq_sys_find_step s n2) as res. symmetry in Heqres.
  destruct res as [ node | ]. left. auto. unfold in_eq_sys_dom in H. simpl in H.
  destruct (name_eq_dec n1 n2). right. subst. constructor; auto.
  intro. destruct H0 as [ node H0 ]. rewrite Heqres in H0. inversion H0.
  left. auto.
Qed.

Lemma eq_sys_ensure_var_vran s n1 n2 (H : in_eq_sys_vran n1 (eq_sys_ensure_var s n2))
                           : in_eq_sys_vran n1 s /\ n1 <> n2.
Proof.
  unfold eq_sys_ensure_var in H. remember (eq_sys_find_step s n2) as res. symmetry in Heqres.
  destruct res as [ node | ].
  * constructor; auto. destruct H. intro. subst n2. apply H. eexists. eauto.
  * destruct H as [ H [ t [ [ n' H1 ] H2 ] ] ].
    assert (n1 <> n2). intro. apply H. apply in_eq_sys_dom_prop. apply set_add_intro2. auto.
    constructor; auto. constructor. intro. apply H. apply in_eq_sys_dom_prop. apply set_add_intro1.
    apply in_eq_sys_dom_prop. auto. exists t. constructor; auto. exists n'. simpl in H1.
    destruct (name_eq_dec n' n2); auto. inversion H1.
Qed.

Lemma eq_sys_ensure_var_name_wf {s n1 n2 p} (H : eq_sys_name_wf s n2 p)
                              : eq_sys_name_wf (eq_sys_ensure_var s n1) n2 p.
Proof.
  unfold eq_sys_ensure_var. remember (eq_sys_find_step s n1) as cond.
  symmetry in Heqcond. destruct cond. auto. apply eq_sys_name_wf_extend; auto.
  intro. destruct H0. rewrite H0 in Heqcond. inversion Heqcond.
Qed.

Lemma eq_sys_ensure_var_wf s n (H : eq_sys_wf s) : eq_sys_wf (eq_sys_ensure_var s n).
Proof.
  intros n' H1. apply eq_sys_ensure_var_dom in H1. destruct H1.
  * apply H in H0. destruct H0 as [ p H0 ]. exists p. apply eq_sys_ensure_var_name_wf. auto.
  * destruct H0. subst. exists [n]. econstructor. unfold eq_sys_ensure_var.
    apply in_eq_sys_dom_inv in H1. rewrite H1. simpl. destruct (name_eq_dec n n); auto.
    contradiction.
Qed.

Lemma eq_sys_ensure_var_find {s n1 n2 p} (H : eq_sys_name_wf s n2 p)
                           : eq_sys_find s n2 = eq_sys_find (eq_sys_ensure_var s n1) n2.
Proof.
  unfold eq_sys_ensure_var. remember (eq_sys_find_step s n1) as cond.
  symmetry in Heqcond. destruct cond. auto. apply (@eq_sys_find_ext _ _ _ p p); auto.
  apply eq_sys_name_wf_extend; auto. intro. destruct H0. rewrite Heqcond in H0. inversion H0.
  intros. simpl. destruct (name_eq_dec n' n1); auto.
  subst. good_inversion H0; rewrite Heqcond in H2; inversion H2.
Qed.

Lemma eq_sys_ensure_var_image s x y (H : eq_sys_wf s)
                            : inf_term_eq (eq_sys_image s y) (eq_sys_image (eq_sys_ensure_var s x) y).
Proof.
  apply eq_sys_image_ext. clear y. intro y.
  destruct (in_dec name_eq_dec y (eq_sys_dom s)).
  * destruct (H y). apply in_eq_sys_dom_prop. auto. eapply eq_sys_ensure_var_find. eauto.
  * remember (eq_sys_find_step s y) as res. symmetry in Heqres. destruct res.
    - exfalso. apply n. apply in_eq_sys_dom_prop. eexists. eauto.
    - unfold eq_sys_ensure_var. destruct (eq_sys_find_step s x). auto.
      etransitivity. apply eq_sys_find_no. auto. symmetry. unfold eq_sys_find.
      simpl. destruct (name_eq_dec y x). auto. rewrite Heqres. auto.
Qed.

Definition eq_sys_ensure_vars := fold_right (fun n s => eq_sys_ensure_var s n).

Lemma eq_sys_ensure_vars_prop s ns n t (H : eq_sys_find_step (eq_sys_ensure_vars s ns) n
                                          = Some (RootESNode t))
                            : eq_sys_find_step s n = Some (RootESNode t) \/ In n ns.
Proof.
  induction ns as [ | n' ns ]. auto.
  simpl in *. apply eq_sys_ensure_var_prop in H. destruct H; auto.
  apply IHns in H. destruct H; auto.
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
    (res, (y, LinkESNode x) :: eq_sys_ensure_var s x)
end.

Lemma eq_sys_union_wf s x y (H : eq_sys_wf s) : eq_sys_wf (snd (eq_sys_union s x y)).
Proof.
  unfold eq_sys_union.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  destruct (name_eq_dec x' y'). auto. simpl.
  assert (eq_sys_wf (eq_sys_ensure_var s x')). apply eq_sys_ensure_var_wf. auto.
  assert (eq_sys_find_step (eq_sys_ensure_var s x') x' = Some (RootESNode t1)). {
    destruct (in_dec name_eq_dec x (eq_sys_dom s)).
    * apply in_eq_sys_dom_prop in i. apply H in i. destruct i as [ p Hp ].
      unfold eq_sys_ensure_var. apply eq_sys_find_root in Hp.
      rewrite Heqresx in Hp. simpl in Hp. rewrite Hp. auto.
    * assert (~in_eq_sys_dom x s). intro. apply n0. apply in_eq_sys_dom_prop. auto. clear n0.
      apply in_eq_sys_dom_inv in H1. rewrite eq_sys_find_no in Heqresx; auto.
      symmetry in Heqresx. good_inversion Heqresx. unfold eq_sys_ensure_var. rewrite H1. simpl.
      destruct (name_eq_dec x x); auto. contradiction.
  }
  eapply eq_sys_wf_add_link; eauto. econstructor. eauto. intro. good_inversion H2; contradiction.
Qed.

Lemma eq_sys_union_dom s x y z (H1 : eq_sys_wf s) (H2 : in_eq_sys_dom z (snd (eq_sys_union s x y)))
                     : in_eq_sys_dom z s \/ x = z \/ y = z.
Proof.
  unfold eq_sys_union in H2.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  destruct (name_eq_dec x' y'). auto. simpl in H2. apply in_eq_sys_dom_prop in H2. simpl in H2.
  apply set_add_elim in H2. destruct H2.
  * subst. destruct (in_dec name_eq_dec y (eq_sys_dom s)).
    - apply in_eq_sys_dom_prop in i. left. eexists.
      unshelve erewrite (_ : y' = fst (eq_sys_find s y)). rewrite Heqresy. auto.
      destruct (H1 y). auto. eapply eq_sys_find_root. eauto.
    - rewrite eq_sys_find_no in Heqresy. symmetry in Heqresy. good_inversion Heqresy. auto.
      apply in_eq_sys_dom_inv. intro. apply n0. apply in_eq_sys_dom_prop. auto.
  * apply in_eq_sys_dom_prop in H. apply eq_sys_ensure_var_dom in H. destruct H. auto.
    destruct H. subst. destruct (in_dec name_eq_dec x (eq_sys_dom s)).
    - apply in_eq_sys_dom_prop in i. apply H1 in i. destruct i as [ p H ].
      apply eq_sys_find_root in H. exfalso. apply H0. rewrite Heqresx in H. simpl in H.
      eexists. eauto.
    - rewrite eq_sys_find_no in Heqresx. symmetry in Heqresx. good_inversion Heqresx. auto.
      apply in_eq_sys_dom_inv. intro. apply n0. apply in_eq_sys_dom_prop. auto.
Qed.

Lemma eq_sys_union_vran s x y z (H2 : in_eq_sys_vran z (snd (eq_sys_union s x y)))
                      : in_eq_sys_vran z s.
Proof.
  unfold eq_sys_union in H2.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
  destruct (name_eq_dec x' y'). auto. apply in_eq_sys_vran_add_link in H2. destruct H2.
  apply eq_sys_ensure_var_vran in H. destruct H. auto.
Qed.

Lemma eq_sys_union_terms s x y t1 t2 (H : fst (eq_sys_union s x y) = Some (t1, t2))
                       : in_eq_sys_rhs s t1 /\ in_eq_sys_rhs s t2.
Proof.
  unfold eq_sys_union in H.
  remember (eq_sys_find s x) as resx. symmetry in Heqresx. destruct resx as [ x' t1' ].
  remember (eq_sys_find s y) as resy. symmetry in Heqresy. destruct resy as [ y' t2' ].
  destruct (name_eq_dec x' y'). inversion H.
  destruct t1' as [ t1' | ]; [ | inversion H ].
  destruct t2' as [ t2' | ]; [ | inversion H ].
  good_inversion H. constructor; [ exists x' | exists y' ]; eapply eq_sys_find_some; eauto.
Qed.

Lemma eq_sys_union_no_term s x y (H : snd (eq_sys_find s x) = None \/ snd (eq_sys_find s y) = None)
                         : fst (eq_sys_union s x y) = None.
Proof.
  unfold eq_sys_union.
  destruct (eq_sys_find s x) as [ x' [ t1 | ] ]; destruct (eq_sys_find s y) as [ y' [ t2 | ] ];
    simpl in *; destruct H; good_inversion H; destruct (name_eq_dec x' y'); auto.
Qed.

Definition eq_sys_bind (s : eq_sys) (n : name) (t : term_head) : eq_sys :=
  let (n, _) := eq_sys_find s n in (n, RootESNode (Some t)) :: s.

Lemma eq_sys_bind_dom s n1 n2 t : in_eq_sys_dom n1 (eq_sys_bind s n2 t)
                              <-> in_eq_sys_dom n1 s \/ n1 = fst (eq_sys_find s n2).
Proof.
  constructor; intro.
  * unfold eq_sys_bind in H. destruct (eq_sys_find s n2). apply in_eq_sys_dom_prop in H.
    apply set_add_elim in H. destruct H. right. subst. auto.
    left. apply in_eq_sys_dom_prop. auto.
  * unfold eq_sys_bind. destruct (eq_sys_find s n2). apply in_eq_sys_dom_prop. destruct H.
    apply set_add_intro1. apply in_eq_sys_dom_prop. auto.
    apply set_add_intro2. auto.
Qed.

Lemma eq_sys_bind_vran s n1 n2 t (H : in_eq_sys_vran n1 (eq_sys_bind s n2 t))
                     : n1 <> fst (eq_sys_find s n2)
                    /\ (in_eq_sys_vran n1 s \/ In n1 (fv_term_head t)).
Proof.
  destruct H as [ H [ t' [ [ n' H1 ] H2 ] ] ]. unfold eq_sys_bind in *.
  destruct (eq_sys_find s n2) as [ n2' t2 ]. simpl in *. constructor.
  intro. apply H. apply in_eq_sys_dom_prop. apply set_add_intro2. auto.
  destruct (name_eq_dec n' n2').
  * good_inversion H1. auto.
  * left. constructor.
    intro. apply H. apply in_eq_sys_dom_prop. apply set_add_intro1. apply in_eq_sys_dom_prop. auto.
    exists t'. constructor; auto. exists n'. auto.
Qed.

Lemma eq_sys_bind_wf s n t (H : eq_sys_wf s) : eq_sys_wf (eq_sys_bind s n t).
Proof. unfold eq_sys_bind. destruct (eq_sys_find s n). apply eq_sys_wf_add_root. auto. Qed.


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

Lemma eq_sys_interp_find_step s n (int : eq_sys_interp n) x y
                              (H1 : eq_sys_wf s) (H2 : is_interp_of_eq_sys int s)
                              (H3 : eq_sys_find_step s x = Some (LinkESNode y))
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

(*
Lemma eq_sys_union_ensure_vars_roots s x y z ns
  : In z (eq_sys_roots (snd (eq_sys_union (eq_sys_ensure_vars s ns) x y)))
<-> In z (eq_sys_roots (eq_sys_ensure_vars (snd (eq_sys_union s x y)) ns)).
Proof.
  constructor; intro.
  * apply eq_sys_roots_prop in H. destruct H as [ t H ]. unfold eq_sys_union in H.
    remember (eq_sys_find (eq_sys_ensure_vars s ns) x) as resx. symmetry in Heqresx. destruct resx as [ x' t1 ].
    remember (eq_sys_find (eq_sys_ensure_vars s ns) y) as resy. symmetry in Heqresy. destruct resy as [ y' t2 ].
    //
*)

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


(* MGU *)

Definition is_more_general_eq_sys (m s : eq_sys) : Prop :=
  exists s', forall t, inf_term_eq (apply_eq_sys s t) (apply_eq_sys_inf s' (apply_eq_sys m t)).

Definition is_unifier_eq_sys (s : eq_sys) (t1 t2 : term) : Prop :=
  inf_term_eq (apply_eq_sys s t1) (apply_eq_sys s t2).

Definition is_mgu_eq_sys (s : eq_sys) (t1 t2 : term) :=
  is_unifier_eq_sys s t1 t2 /\ forall s', is_unifier_eq_sys s' t1 t2 -> is_more_general_eq_sys s s'.
