Require Import Eqdep_dec.
Require Import PeanoNat.
Require List.

Import EqNotations.


#[local] Hint Resolve Nat.eq_dec : core.

(* (|T| + n)-valued type *)

Fixpoint n_options (n : nat) (T : Set) : Set :=
match n with
| O => T
| S n => option (n_options n T)
end.

Module NOptions.

Fixpoint n_Somes {T : Set} n (x : T) : n_options n T :=
match n as n' return n_options n' T with
| 0 => x
| S n => Some (n_Somes n x)
end.

Fixpoint sequence {T : Set -> Set} (pure : forall [A : Set], A -> T A)
                  (bind : forall [A B : Set], (A -> T B) -> T A -> T B)
                  {A n} (x : n_options n (T A)) : T (n_options n A) :=
match n as n' return n_options n' (T A) -> T (n_options n' A) with
| 0 => fun x => x
| S n => fun x =>
  match x with
  | None => pure None
  | Some x => bind (fun x => pure (Some x)) (sequence pure bind x)
  end
end x.

Lemma sum_prop (n m : nat) {T} : n_options n (n_options m T) = n_options (n + m) T.
Proof. induction n. auto. simpl. apply (f_equal (fun (T : Set) => option T)). apply IHn. Qed.

Corollary S_option (n : nat) {T} : n_options (S n) T = n_options n (option T).
Proof. symmetry. etransitivity. apply (sum_prop n 1). rewrite Nat.add_1_r. reflexivity. Qed.

Fixpoint is_added {T n} (x : n_options n T) : Prop :=
match n as n' return n_options n' T -> Prop with
| 0 => fun _ => False
| S n => fun x =>
  match x with
  | None => True
  | Some x => is_added x
  end
end x.

Lemma is_added_dec {T n} (x : n_options n T) : is_added x + not (is_added x).
Proof. induction n. eauto. destruct x as [ x | ]; simpl; eauto. Qed.

End NOptions.


(* n-valued type *)

Definition fin n := n_options n False.

Module Fin.

Fixpoint to_nat {n} (i : fin n) : nat :=
match n, i with
| 0, i => match i with end
| S n, i =>
  match i with
  | None => 0
  | Some i => S (to_nat i)
  end
end.

Lemma to_nat_prop {n} {i : fin n} : to_nat i < n.
Proof.
induction n. contradiction. destruct i as [ i | ].
  * apply -> Nat.succ_lt_mono. apply IHn.
  * apply Nat.lt_0_succ.
Qed.

Lemma to_nat_inj {n} (i1 i2 : fin n) (p : to_nat i1 = to_nat i2) : i1 = i2.
Proof.
  induction n. contradiction.
  destruct i1 as [ i1 | ]; destruct i2 as [ i2 | ]; inversion p; auto.
  f_equal. apply IHn. auto.
Qed.

Lemma to_nat_rew n m (i : fin n) (p : n = m) : to_nat (rew [fin] p in i) = to_nat i.
Proof. destruct p. auto. Qed.

Lemma compare {n} (i j : fin n) : {to_nat i < to_nat j} + {i = j} + {to_nat i > to_nat j}.
Proof.
  induction n. inversion i. destruct i as [ i | ]; destruct j as [ j | ]; auto.
  - edestruct IHn as [ [ lt | eq ] | gt ].
    * left. left. apply le_n_S. apply lt.
    * left. right. f_equal. auto.
    * right. apply le_n_S. auto.
  - right. apply Nat.lt_0_succ.
  - left. left. apply Nat.lt_0_succ.
Defined.

Lemma eq_dec {n} (i j : fin n) : {i = j} + {i <> j}.
Proof.
  destruct (compare i j) as [ [ lt | eq ] | gt ]; auto.
  all: right; intro; subst j; eapply Nat.lt_irrefl; eauto.
Defined.

Fixpoint of_nat n i (p : i < n) : fin n :=
match n as n', p return fin n' with
| 0, p => False_rec _ (match p with end)
| S n, p =>
  match i as i' return i' < S n -> fin (S n) with
  | 0 => fun _ => None
  | S i => fun p => Some (of_nat n i (PeanoNat.lt_S_n i n p))
  end p
end.

Lemma of_nat_irrelevance n i (p q : i < n) : of_nat n i p = of_nat n i q.
Proof.
  generalize dependent i. induction n; intros.
  - inversion p.
  - destruct i; auto. apply (f_equal Some). apply IHn.
Qed.

Lemma of_nat_inj n i j (p : i < n) (q : j < n) (s : of_nat n i p = of_nat n j q) : i = j.
Proof.
  generalize dependent i. generalize dependent j.
  induction n; intros. inversion p. destruct i; destruct j; inversion s. auto.
  f_equal. unshelve eapply IHn; eauto.
Qed.

Lemma of_nat_ext n i j (p : i < n) (q : j < n) (s : i = j) : of_nat n i p = of_nat n j q.
Proof. generalize dependent p. rewrite s. intro. apply of_nat_irrelevance. Qed.

Lemma fin_nat_fin n (i : fin n) : of_nat n (to_nat i) to_nat_prop = i.
Proof.
  induction n. contradiction. destruct i; auto.
  simpl. f_equal. erewrite of_nat_irrelevance. apply IHn.
Qed.

Lemma nat_fin_nat n i (p : i < n) : to_nat (of_nat n i p) = i.
Proof.
  generalize dependent i. induction n; intros. inversion p.
  destruct i; auto. simpl. f_equal. apply IHn.
Qed.

Lemma fin_n_m {n m} (p : n = m) {x : fin n} {y : fin m} (q : rew p in x = y) : rew p in x = y.
Proof. auto. Qed.

Lemma fin_0_0 {n m} (p : S n = S m) : rew [fin] p in (None : fin (S n)) = None.
Proof. refine (match p with eq_refl => eq_refl end). Qed.

Fixpoint of_n_options {T n} (x : n_options n T) : sum T (fin n) :=
match n as n' return n_options n' T -> sum T (fin n') with
| 0 => inl
| S n => fun x =>
  match x with
  | None => inr None
  | Some x =>
    match of_n_options x with
    | inl x => inl x
    | inr x => inr (Some x)
    end
  end
end x.

Fixpoint to_n_options T {n} (i : fin n) : n_options n T :=
match n as n' return fin n' -> n_options n' T with
| 0 => fun i => match i with end
| S n => fun i =>
  match i with
  | None => None
  | Some i => Some (to_n_options T i)
  end
end i.

Lemma fin_n_options_fin {n} (i : fin n) T : of_n_options (to_n_options T i) = inr i.
Proof. induction n. inversion i. destruct i as [ i | ]; auto. simpl. rewrite IHn. auto. Qed.


End Fin.


(* telescope is like list but types dependent on (|V| + length of tail)-valued type *)

Inductive telescope (T : Set -> Set) V : nat -> Set :=
| NilTelescope : telescope T V 0
| ConsTelescope {n} : T (n_options n V) -> telescope T V n -> telescope T V (S n)
.

Arguments NilTelescope {_ _}.
Arguments ConsTelescope {_ _ _} _ _.

Module Telescope.

Fixpoint apply {T : Set -> Set} (subst : forall V, T V -> T (option V) -> T V)
               {V n} (tsc : telescope T V n) (t : T (n_options n V)) : T V :=
match tsc in telescope _ _ n' return T (n_options n' V) -> T V with
| NilTelescope => fun t => t
| ConsTelescope t' tsc => fun t => apply subst tsc (subst _ t' t)
end t.

Fixpoint collapse {T V n} (tsc : telescope T V n) {U} (v : n_options n U)
                  : option { m & prod (T (n_options m V)) (telescope T V m) } :=
match tsc in telescope _ _ n' return n_options n' U -> _ with
| NilTelescope => fun _ => None
| ConsTelescope t tsc => fun v =>
  match v with
  | None => Some (existT _ _ (t, tsc))
  | Some v => collapse tsc v
  end
end v.

Lemma collapse_some {T V n} (tsc : telescope T V n) {U} (v : n_options n U)
                    : NOptions.is_added v <-> exists res, collapse tsc v = Some res.
Proof.
  constructor; intro; (induction tsc; [ try destruct H; inversion H | destruct v as [ v | ];
    [ apply IHtsc; auto | ] ]).
  eexists. reflexivity. constructor.
Qed.

Lemma collapse_none {T V n} (tsc : telescope T V n) {U} (v : n_options n U)
                    : ~(NOptions.is_added v) <-> collapse tsc v = None.
Proof.
  constructor; intro; (induction tsc; [ | destruct v as [ v | ]; [ apply IHtsc; auto | ] ]); auto.
  - apply False_rec. apply H. constructor.
  - inversion H.
Qed.

Lemma collapse_some_m {T V n} (tsc : telescope T V n) {U} (v : n_options n U)
                      {m res} (p : collapse tsc v = Some (existT _ m res))
                      : m < n.
Proof.
  generalize dependent m. induction tsc; intros. inversion p. destruct v as [ v | ].
  apply IHtsc in p. auto. simpl in p. inversion p. auto.
Qed.

Lemma collapse_compose {T V n} (tsc : telescope T V n)
                       {U1 U2 m1} (v1 : n_options n U1) (v2 : n_options m1 U2)
                       {t1 tsc1} (p : collapse tsc v1 = Some (existT _ m1 (t1, tsc1)))
                       {m2 t2 tsc2} (q : collapse tsc1 v2 = Some (existT _ m2 (t2, tsc2)))
                       : exists (v : n_options n U2), collapse tsc v = Some (existT _ m2 (t2, tsc2)).
Proof.
  induction tsc. inversion p. destruct v1 as [ v1 | ]. simpl in * |-. apply IHtsc in p.
  destruct p as [ v Hv ]. exists (Some v). apply Hv. simpl in *. inversion p. subst m1.
  apply inj_pair2_eq_dec in H1; auto. apply inj_pair2_eq_dec in H2; auto. subst t1 tsc1.
  exists (Some v2). auto.
Qed.

Lemma apply_collapse {T : Set -> Set} (pure : forall (V : Set), V -> T V)
                     (subst : forall V, T V -> T (option V) -> T V)
                     (subst_pure1 : forall (V : Set) (t : T V), subst _ t (pure _ None) = t)
                     (subst_pure2 : forall (V : Set) (v : V) (t : T V), subst _ t (pure _ (Some v)) = pure _ v)
                     {V n} (tsc : telescope T V n) (v : n_options n V)
                     {m t tsc'} (H : collapse tsc v = Some (existT _ m (t, tsc')))
                     : apply subst tsc (pure _ v) = apply subst tsc' t.
Proof.
  generalize dependent m. induction tsc; intros. inversion H. destruct v.
  etransitivity; [ | apply IHtsc; eauto ]. simpl. rewrite subst_pure2. reflexivity.
  simpl. rewrite subst_pure1. inversion H. subst m. specialize Nat.eq_dec. intro.
  apply inj_pair2_eq_dec in H2; auto. apply inj_pair2_eq_dec in H3; auto.
  subst t0 tsc'. reflexivity.
Qed.

Lemma apply_not_added {T : Set -> Set} (pure : forall (V : Set), V -> T V)
                      (subst : forall V, T V -> T (option V) -> T V)
                      (subst_pure : forall (V : Set) (v : V) (t : T V), subst _ t (pure _ (Some v)) = pure _ v)
                      {V n} (tsc : telescope T V n) (v : n_options n V) (H : ~(NOptions.is_added v))
                      : exists v', apply subst tsc (pure _ v) = pure _ v'.
Proof.
  induction tsc. eexists. reflexivity. simpl. destruct v as [ v | ].
  destruct (IHtsc v); eauto. rewrite subst_pure. rewrite H0. eexists. reflexivity.
  exfalso. apply H. constructor.
Qed.

End Telescope.


(* [n] -> T ≈ list of n values, but not inductive *)

Definition array (T : Set) n : Set := fin n -> T.

Module Array.

(*
(* dependent version requires funext :( *)
Fixpoint array_rec {T R : Set} (z : R) (s : T -> R -> R) n (xs : array T n) : R :=
match n as n' return array T n' -> R with
| 0 => fun _ => z
| S n => fun xs => s (xs None) (array_rec z s n (fun i => xs (Some i)))
end xs.

Definition to_list {T} {n} (xs : array T n) : list T :=
  array_rec nil cons n xs.

Fixpoint of_list {T : Set} (xs : list T) : array T (length xs) :=
match xs as xs' return array T (length xs') with
| nil => fun i => match i with end
| cons x xs => fun i =>
  match i with
  | None => x
  | Some i => of_list xs i
  end
end.

Definition take {t} [n] i (p : i <= n) (xs : array t n) : array t i :=
  fun j => xs (Fin.of_nat n (Fin.to_nat j) (Nat.lt_le_trans _ i n Fin.to_nat_prop p)).

Lemma array_take_irrelevance {t n} i (p q : i <= n) (xs : array t n) (j : fin i)
                             : take i p xs j = take i q xs j.
Proof. unfold take. f_equal. apply Fin.of_nat_irrelevance. Qed.
*)

Definition in_array {t : Set} {n} (x : t) (xs : array t n) := exists i, xs i = x.

End Array.


(* vector - list of n values *)

Inductive vec (T : Set) : nat -> Set :=
| NilVec : vec T 0
| ConsVec : forall {n}, T -> vec T n -> vec T (S n)
.

Arguments NilVec {_}.
Arguments ConsVec {_} [_] _ _.

Module Vec.

Fixpoint v2a {T n} (xs : vec T n) : array T n :=
match xs as xs' in vec _ n' return array T n' with
| NilVec => fun i => match i with end
| ConsVec x xs => fun i =>
  match i with
  | None => x
  | Some i => v2a xs i
  end
end.

(* essentialy this is definitely "fun i => f (v2a xs i)"
   but works as workaround on termination checker *)
Fixpoint v2a_dep {T : Set} [R : T -> Type] (f : forall x, R x)
                 {n} (xs : vec T n) : forall (i : fin n), R (v2a xs i) :=
match xs as xs' in vec _ n' return forall (i : fin n'), R (v2a xs' i) with
| NilVec => fun i => match i with end
| ConsVec x xs => fun i =>
  match i as i' return R (v2a (ConsVec x xs) i') with
  | None => f x
  | Some i => v2a_dep f xs i
  end
end.

Lemma v2a_dep_prop {T : Set} [R : T -> Type] (f : forall x, R x)
                   {n} (xs : vec T n) (i : fin n)
                   : v2a_dep f xs i = f (v2a xs i).
Proof. induction xs. inversion i. destruct i. apply IHxs. auto. Qed.

Fixpoint a2v {T n} (xs : array T n) : vec T n :=
match n as n' return array T n' -> vec T n' with
| 0 => fun _ => NilVec
| S n => fun xs => ConsVec (xs None) (a2v (fun i => xs (Some i)))
end xs.

Lemma a2v_ext {T n} [xs ys : array T n] (H : forall i, xs i = ys i) : a2v xs = a2v ys.
Proof. induction n. auto. simpl. f_equal; auto. Qed.

Lemma vec_array_vec {T n} (xs : vec T n) : a2v (v2a xs) = xs.
Proof. induction xs. auto. simpl. f_equal. auto. Qed.

Lemma array_vec_array {T n} (xs : array T n) (i : fin n) : v2a (a2v xs) i = xs i.
Proof. induction n. inversion i. destruct i. apply IHn. auto. Qed.

Fixpoint map {T R : Set} (f : T -> R) {n} (xs : vec T n) : vec R n :=
match xs in vec _ n' return vec R n' with
| NilVec => NilVec
| ConsVec x xs => ConsVec (f x) (map f xs)
end.

Lemma map_prop {T R : Set} (f : T -> R) {n} (xs : vec T n)
               : map f xs = a2v (fun i => f (v2a xs i)).
Proof. induction xs. auto. simpl. f_equal. auto. Qed.

Corollary map_id {T n} (xs : vec T n) : map id xs = xs.
Proof. rewrite map_prop. apply vec_array_vec. Qed.

Corollary map_map {T S R : Set} (f : S -> R) (g : T -> S) {n} (xs : vec T n)
                  : map f (map g xs) = map (fun x => f (g x)) xs.
Proof. repeat rewrite map_prop. apply a2v_ext. intro. rewrite array_vec_array. auto. Qed.

Corollary map_ext {T R : Set} [f g : T -> R] {n} (xs : vec T n)
                  (H : forall i, f (v2a xs i) = g (v2a xs i))
                  : map f xs = map g xs.
Proof. repeat rewrite map_prop. apply a2v_ext. auto. Qed.

Fixpoint sequence {T : Set -> Set} (pure : forall [A : Set], A -> T A)
                  (bind : forall [A B : Set], (A -> T B) -> T A -> T B)
                  {A n} (xs : vec (T A) n) : T (vec A n) :=
match xs in vec _ n' return T (vec A n') with
| NilVec => pure NilVec
| ConsVec x xs =>
  bind (fun x =>
    bind (fun xs =>
      pure (ConsVec x xs)) (sequence pure bind xs)) x 
end.

Lemma sequence_pure {T : Set -> Set} (pure : forall [A : Set], A -> T A)
                    (bind : forall [A B : Set], (A -> T B) -> T A -> T B)
                    (bind_pure : forall (A B : Set) (k : A -> T B) (x : A), bind k (pure x) = k x)
                    {A n} (xs : vec A n) : sequence pure bind (map (pure (A:=A)) xs) = pure xs.
Proof. induction xs. auto. simpl. rewrite IHxs. rewrite bind_pure. rewrite bind_pure. auto. Qed.

Lemma sequence_pure' {T : Set -> Set} (pure : forall [A : Set], A -> T A)
                     (bind : forall [A B : Set], (A -> T B) -> T A -> T B)
                     (bind_pure : forall (A B : Set) (k : A -> T B) (x : A), bind k (pure x) = k x)
                     {A n} (xs : vec (T A) n) (ys : array A n)
                     (H : forall i, Vec.v2a xs i = pure (ys i))
                     : sequence pure bind xs = pure (Vec.a2v ys).
Proof.
  transitivity (sequence pure bind (Vec.map (pure _) (Vec.a2v ys))). f_equal. symmetry.
  etransitivity. apply map_prop. etransitivity. apply a2v_ext. intro. rewrite array_vec_array.
  symmetry. eauto. apply vec_array_vec. etransitivity. apply sequence_pure. auto. reflexivity.
Qed.

Definition indices n := a2v (fun (i : fin n) => i).

Fixpoint to_list {T n} (xs : vec T n) : list T :=
match xs with
| NilVec => nil
| ConsVec x xs => cons x (to_list xs)
end.

Lemma to_list_length {T n} (xs : vec T n) : length (to_list xs) = n.
Proof. induction xs. auto. simpl. f_equal. auto. Qed.

Lemma to_list_nth {T n} (xs : vec T n) i
                  : List.nth_error (to_list xs) (Fin.to_nat i) = Some (v2a xs i).
Proof. induction xs. inversion i. destruct i; auto. apply IHxs. Qed.

Fixpoint of_list {T : Set} (xs : list T) : vec T (length xs) :=
match xs as xs' return vec T (length xs') with
| nil => NilVec
| cons x xs => ConsVec x (of_list xs)
end.

Fixpoint find {T : Set} [P : T -> Prop] (dec : forall x, {P x} + {~(P x)})
              {n} (xs : vec T n) : option (fin n) :=
match xs in vec _ n' return option (fin n') with
| NilVec => None
| ConsVec x xs =>
  match dec x with
  | left _ => Some None
  | right _ =>
    match find dec xs with
    | None => None
    | Some i => Some (Some i)
    end
  end
end.

Lemma find_p {T : Set} [P : T -> Prop] (dec : forall x, {P x} + {~(P x)})
             {n} (xs : vec T n) (i : fin n) (H : find dec xs = Some i) : P (v2a xs i).
Proof.
  induction xs. inversion H. generalize dependent H. simpl. destruct (dec t).
  - intro. inversion H. auto.
  - destruct (find dec xs) as [ j | ]; intro; inversion H. apply IHxs. auto.
Qed.

Lemma find_not_p {T : Set} [P : T -> Prop] (dec : forall x, {P x} + {~(P x)})
                 {n} (xs : vec T n) (H : find dec xs = None) : forall i, ~(P (v2a xs i)).
Proof.
  induction xs. intro. inversion i. generalize dependent H. simpl. destruct (dec t).
  - intro. inversion H.
  - destruct (find dec xs) as [ j | ]; intro. inversion H. intro. destruct i as [ i | ]; auto.
Qed.

Lemma find_some {T : Set} [P : T -> Prop] (dec : forall x, {P x} + {~(P x)})
                {n} (xs : vec T n) (i : fin n) (H : P (v2a xs i))
                : exists j, find dec xs = Some j.
Proof.
  remember (find dec xs) as res. destruct res as [ j | ]. eexists. reflexivity.
  exfalso. eapply find_not_p. eauto. eauto.
Qed.

Lemma find_none {T : Set} [P : T -> Prop] (dec : forall x, {P x} + {~(P x)})
                {n} (xs : vec T n) (H : forall i, ~(P (v2a xs i)))
                : find dec xs = None.
Proof.
  remember (find dec xs) as res. destruct res as [ j | ]; auto.
  exfalso. eapply H. eapply find_p. eauto.
Qed.

Definition is_distinct {T : Set} (P : T -> Prop) {n} (xs : vec T n) : Prop :=
  forall i j, P (v2a xs i) -> P (v2a xs j) -> i = j.

Lemma find_distinct_some {T : Set} [P : T -> Prop] (dec : forall x, {P x} + {~(P x)})
                         {n} (xs : vec T n) (Hxs : is_distinct P xs)
                         (i : fin n) (H : P (v2a xs i)) : find dec xs = Some i.
Proof.
  destruct (find_some dec xs i H) as [ j Hj ]. rewrite Hj.
  f_equal. apply Hxs; eauto. eapply find_p. eauto.
Qed.

Lemma distinct_indices_len {n m} (xs : vec (fin n) m)
                           (H : forall j, is_distinct (fun i => i = j) xs)
                           : m <= n.
Proof.
  generalize dependent m. induction n; intros. destruct xs. auto. inversion f.
  destruct xs. apply le_0_n. rename n0 into m. rename f into j. apply le_n_S. unshelve eapply IHn.
  - apply Vec.a2v. intro i. remember (Vec.v2a xs i) as j'.
    destruct (Fin.compare j' j) as [ [ lt | eq ] | gt ].
    * unshelve eapply Fin.of_nat. apply (Fin.to_nat j'). eapply Nat.lt_le_trans. eauto.
      apply le_S_n. apply Fin.to_nat_prop.
    * subst j'. specialize (H j None (Some i) eq_refl eq). inversion H.
    * unshelve eapply Fin.of_nat. apply (pred (Fin.to_nat j')). destruct j' as [ j' | ].
      apply Fin.to_nat_prop. inversion gt.
  - Opaque Fin.compare.
    intro j'. intros i1 i2. repeat rewrite Vec.array_vec_array. simpl.
    destruct (Fin.compare (v2a xs i1) j) as [ [ lt1 | eq1 ] | gt1 ];
    destruct (Fin.compare (v2a xs i2) j) as [ [ lt2 | eq2 ] | gt2 ];
    simpl; intros; subst j'; try apply Fin.of_nat_inj in H1.
    4, 5, 6: set H as H'; specialize (H' j None (Some i1) eq_refl eq1); inversion H'.
    2, 5: set H as H'; specialize (H' j None (Some i2) eq_refl eq2); inversion H'.
    * apply (Fin.to_nat_inj (v2a xs i2)) in H1.
      specialize (H (v2a xs i1) (Some i1) (Some i2) eq_refl H1). inversion H. auto.
    * remember (v2a xs i2) as j2. destruct j2 as [ j2 | ].
      specialize (H1 : Fin.to_nat j2 = Fin.to_nat (v2a xs i1)). rewrite <- H1 in lt1.
      exfalso. apply (Nat.nle_succ_diag_l (Fin.to_nat j)). etransitivity; eauto.
      exfalso. eapply (Nat.nlt_0_r). apply gt2.
    * remember (v2a xs i1) as j1. destruct j1 as [ j1 | ].
      specialize (H1 : Fin.to_nat (v2a xs i2) = Fin.to_nat j1). rewrite H1 in lt2.
      exfalso. apply (Nat.nle_succ_diag_l (Fin.to_nat j)). etransitivity; eauto.
      exfalso. eapply (Nat.nlt_0_r). apply gt1.
    * remember (v2a xs i1) as j1. remember (v2a xs i2) as j2.
      destruct j1 as [ j1 | ]. destruct j2 as [ j2 | ]. apply Fin.to_nat_inj in H1. subst j2.
      specialize (H (Some j1) (Some i1) (Some i2) (eq_sym Heqj1) (eq_sym Heqj2)). inversion H. auto.
      inversion gt2. inversion gt1.
    Transparent Fin.compare.
Qed.

Definition is_permutation {n m} (xs : vec (fin n) m) :=
  n = m /\ forall j, is_distinct (fun i => i = j) xs.

Lemma all_in_permutation {n m} (xs : vec (fin n) m) j (H : is_permutation xs)
                         : exists i, Vec.v2a xs i = j.
Proof.
  remember (find (fun i => Fin.eq_dec i j) xs) as res. symmetry in Heqres. destruct res as [ i | ].
  - apply find_p in Heqres. eexists. eauto.
  - assert (Hm : S m <= n).
    * specialize (find_not_p _ xs Heqres). simpl. intro.
      apply (distinct_indices_len (ConsVec j xs)). intro j'. intros i1 i2. intros.
      destruct i1 as [ i1 | ]; destruct i2 as [ i2 | ]; auto.
      destruct H. f_equal. eapply H3; eauto.
      all: exfalso; subst j'; eapply H0; symmetry; eauto.
    * exfalso. apply (Nat.lt_irrefl n). destruct H. subst m. auto.
Qed.

End Vec.
