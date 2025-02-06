Require Import Eqdep_dec.
Require Import PeanoNat.
Import EqNotations.


Section Utils.

Definition gt_0_is_S {n} (p : n > 0) : { n' | n = S n' } :=
match n as n' return n' > 0 -> { m | n' = S m } with
| 0 => fun p => False_rec _ match p with end
| S n => fun p => exist _ n eq_refl
end p.

Fixpoint n_options (n : nat) (t : Set) : Set :=
match n with
| O => t
| S n => option (n_options n t)
end.

(*
Fixpoint n_Somes {t : Set} (n : nat) (x : t) : n_options n t :=
match n as n' return n_options n' t with
| O => x
| S n => Some (n_Somes n x)
end.
*)

Definition fin n := n_options n False.

Fixpoint fin_nat {n} (i : fin n) : nat :=
match n, i with
| 0, i => match i with end
| S n, i =>
  match i with
  | None => 0
  | Some i => S (fin_nat i)
  end
end.

Lemma fin_nat_prop {n} {i : fin n} : fin_nat i < n.
Proof.
induction n. contradiction. destruct i as [ i | ].
  * apply -> Nat.succ_lt_mono. apply IHn.
  * apply Nat.lt_0_succ.
Qed.

Lemma fin_nat_inj {n} (i1 i2 : fin n) (p : fin_nat i1 = fin_nat i2) : i1 = i2.
Proof.
  induction n. contradiction.
  destruct i1 as [ i1 | ]; destruct i2 as [ i2 | ]; inversion p; auto.
  f_equal. apply IHn. auto.
Qed.

Lemma fin_nat_rew n m (i : fin n) (p : n = m) : fin_nat (rew [fin] p in i) = fin_nat i.
Proof. destruct p. auto. Qed.

Fixpoint nat_fin n i (p : i < n) : fin n :=
match n as n', p return fin n' with
| 0, p => False_rec _ (match p with end)
| S n, p =>
  match i as i' return i' < S n -> fin (S n) with
  | 0 => fun _ => None
  | S i => fun p => Some (nat_fin n i (PeanoNat.lt_S_n i n p))
  end p
end.

Lemma nat_fin_irrelevance n i (p q : i < n) : nat_fin n i p = nat_fin n i q.
Proof.
  generalize dependent i. induction n; intros.
  - inversion p.
  - destruct i; auto. apply (f_equal Some). apply IHn.
Qed.

Lemma nat_fin_inj n i j (p : i < n) (q : j < n) (s : nat_fin n i p = nat_fin n j q) : i = j.
Proof.
  generalize dependent i. generalize dependent j.
  induction n; intros. inversion p. destruct i; destruct j; inversion s. auto.
  f_equal. unshelve eapply IHn; eauto.
Qed.

Lemma nat_fin_ext n i j (p : i < n) (q : j < n) (s : i = j) : nat_fin n i p = nat_fin n j q.
Proof. generalize dependent p. rewrite s. intro. apply nat_fin_irrelevance. Qed.

Lemma fin_nat_fin n (i : fin n) : nat_fin n (fin_nat i) fin_nat_prop = i.
Proof.
  induction n. contradiction. destruct i; auto.
  simpl. f_equal. erewrite nat_fin_irrelevance. apply IHn.
Qed.

Lemma nat_fin_nat n i (p : i < n) : fin_nat (nat_fin n i p) = i.
Proof.
  generalize dependent i. induction n; intros. inversion p.
  destruct i; auto. simpl. f_equal. apply IHn.
Qed.

Lemma fin_n_m {n m} (p : n = m) {x : fin n} {y : fin m} (q : rew p in x = y) : rew p in x = y.
Proof. auto. Qed.

Definition fin_0_0 {n m} (p : S n = S m) : rew [fin] p in (None : fin (S n)) = None :=
match p with eq_refl => eq_refl end.

Definition array (t : Set) n : Set := fin n -> t.

(* dependent version requires funext :( *)
Definition array_rec {t S : Set} (z : S) (s : t -> S -> S)
                     : forall n, array t n -> S :=
fix array_rec n :=
  match n with
  | 0 => fun _ => z
  | S n => fun xs => s (xs None) (array_rec n (fun i => xs (Some i)))
  end.

Definition array_take {t} [n] i (p : i <= n) (xs : array t n) : array t i :=
  fun j => xs (nat_fin n (fin_nat j) (Nat.lt_le_trans _ i n fin_nat_prop p)).

Lemma array_take_irrelevance {t n} i (p q : i <= n) (xs : array t n) (j : fin i)
                             : array_take i p xs j = array_take i q xs j.
Proof. unfold array_take. f_equal. apply nat_fin_irrelevance. Qed.

Definition in_array {t : Set} {n} (x : t) (xs : array t n) := exists i, xs i = x.

End Utils.


#[local] Parameter f : Set.

Variant term_head (v t : Set) : Set :=
| VarTH : v -> term_head v t
| ConsTH : forall n, f -> array t n -> term_head v t
.

Unset Elimination Schemes.

Inductive simple_term v : Set :=
| SimpleTerm : term_head v (simple_term v) -> simple_term v
.

Set Elimination Schemes.

CoInductive infinite_term v : Set := InfTerm { get_inf_term : term_head v (infinite_term v) }.

Definition infinite_term_coind {v} (P : Set -> Prop)
                               (inf_term : P v -> v + (f * { n & array (P v) n }))
                               : P v -> infinite_term v :=
cofix infinite_term_coind p :=
  match inf_term p with
  | inl x => InfTerm _ (VarTH _ _ x)
  | inr (f, existT _ n ps) => InfTerm _ (ConsTH _ _ n f (fun i => infinite_term_coind (ps i)))
  end.

Module InfiniteTerm.

CoFixpoint map {v1 v2 : Set} (f : v1 -> v2) (t : infinite_term v1) : infinite_term v2 :=
match t with
| InfTerm _ (VarTH _ _ v) => InfTerm _ (VarTH _ _ (f v))
| InfTerm _ (ConsTH _ _ n f' ts) => InfTerm _ (ConsTH _ _ n f' (fun i => map f (ts i)))
end.

CoInductive eq {v} : infinite_term v -> infinite_term v -> Prop :=
| VarEq : forall x, eq (InfTerm _ (VarTH _ _ x)) (InfTerm _ (VarTH _ _ x))
| ConsEq : forall n f (ts1 ts2 : array (infinite_term v) n),
                  (forall (i : fin n), eq (ts1 i) (ts2 i))
               -> eq (InfTerm _ (ConsTH _ _ n f ts1)) (InfTerm _ (ConsTH _ _ n f ts2))
.

CoFixpoint eq_refl {v} (t : infinite_term v) : eq t t :=
match t as t' return eq t' t' with
| InfTerm _ (VarTH _ _ x) => VarEq x
| InfTerm _ (ConsTH _ _ n f ts) => ConsEq n f ts ts (fun i => eq_refl (ts i))
end.

CoFixpoint eq_sym {v} {t1 t2 : infinite_term v} (p : eq t1 t2) : eq t2 t1 :=
match p with
| VarEq x => VarEq x
| ConsEq n f ts1 ts2 p => ConsEq n f ts2 ts1 (fun i => eq_sym (p i))
end.

Inductive subterm {v} : infinite_term v -> infinite_term v -> Prop :=
| ReflInfSubterm : forall t1 t2, eq t1 t2 -> subterm t1 t2
| ConsInfSubterm : forall t1 t2 n f ts, subterm t1 t2 -> in_array t2 ts
                -> subterm t1 (InfTerm _ (ConsTH _ _ n f ts))
.

Definition step {v} (t : infinite_term v) : infinite_term v :=
match t with InfTerm _ t => InfTerm _ t end.

Lemma step_prop {v} (t : infinite_term v) : t = step t.
Proof. destruct t. reflexivity. Qed.

CoFixpoint eq_map {v u : Set} (f : v -> u) (t1 t2 : infinite_term v) (H : eq t1 t2)
                  : eq (map f t1) (map f t2) :=
match H in eq t1 t2 with
| VarEq x => rew <- [fun x => eq x x] step_prop (map f (InfTerm _ (VarTH _ _ x))) in VarEq (f x)
| ConsEq n f' ts1 ts2 p =>
  rew <- [fun x => eq x _] step_prop (map f (InfTerm _ (ConsTH _ _ n f' ts1))) in
  rew <- [fun x => eq _ x] step_prop (map f (InfTerm _ (ConsTH _ _ n f' ts2))) in
  ConsEq _ _ _ _ (fun i => eq_map f _ _ (p i))
end.

Module Test.

#[local] Parameter F : f.
#[local] Parameter G : f.

CoFixpoint test1 : infinite_term nat := InfTerm _ (ConsTH _ _ 1 F (fun _ => test1)).

CoFixpoint test2 n : infinite_term nat :=
  let xs := fun i =>
    match i with
    | None => InfTerm _ (VarTH _ _ n)
    | Some _ => test2 (S n)
    end
  in InfTerm _ (ConsTH _ _ 2 F xs).

CoFixpoint test3 : infinite_term False := InfTerm _ (ConsTH _ _ 1 F (fun _ => test3'))
with test3' : infinite_term False := InfTerm _ (ConsTH _ _ 1 G (fun _ => test3)).

End Test.

End InfiniteTerm.

Definition regular_term_p {v} (t : infinite_term v) : Prop :=
exists n (ts : array (infinite_term v) n), (forall i, InfiniteTerm.subterm (ts i) t)
/\ forall t', InfiniteTerm.subterm t' t -> exists i, InfiniteTerm.eq t' (ts i).

Definition regular_term v : Set := { t : infinite_term v | regular_term_p t }.

Unset Elimination Schemes.

Inductive mu_term v : Set :=
| MuTerm : term_head v (mu_term v) -> mu_term v
| MuBind : mu_term (option v) -> mu_term v
.

Set Elimination Schemes.

Definition mu_term_ind (P : forall v, mu_term v -> Prop)
                       (mu_term_var : forall v x, P v (MuTerm v (VarTH v _ x)))
                       (mu_term_cons : forall v f n ts, (forall (i : fin n), P v (ts i))
                                    -> P v (MuTerm v (ConsTH v _ n f ts)))
                       (mu_term_bind : forall (v : Set) t, P (option v) t -> P v (MuBind v t))
                       : forall v t, P v t :=
fix mu_term_ind v t :=
  match t as t return P v t with
  | MuTerm _ (VarTH _ _ x) => mu_term_var _ x
  | MuTerm _ (ConsTH _ _ n f ts) => mu_term_cons _ f n ts (fun i => mu_term_ind _ (ts i))
  | MuBind _ t => mu_term_bind _ t (mu_term_ind _ _)
  end.

Definition mu_term_rec (S : forall v, mu_term v -> Set)
                       (mu_term_var : forall v x, S v (MuTerm v (VarTH v _ x)))
                       (mu_term_cons : forall v f n ts, (forall (i : fin n), S v (ts i))
                                    -> S v (MuTerm v (ConsTH v _ n f ts)))
                       (mu_term_bind : forall (v : Set) t, S (option v) t -> S v (MuBind v t))
                       : forall v t, S v t :=
fix mu_term_rec v t :=
  match t as t return S v t with
  | MuTerm _ (VarTH _ _ x) => mu_term_var _ x
  | MuTerm _ (ConsTH _ _ n f ts) => mu_term_cons _ f n ts (fun i => mu_term_rec _ (ts i))
  | MuBind _ t => mu_term_bind _ t (mu_term_rec _ _)
  end.

Definition mu_term_rect (S : forall v, mu_term v -> Type)
                        (mu_term_var : forall v x, S v (MuTerm v (VarTH v _ x)))
                        (mu_term_cons : forall v f n ts, (forall (i : fin n), S v (ts i))
                                     -> S v (MuTerm v (ConsTH v _ n f ts)))
                        (mu_term_bind : forall (v : Set) t, S (option v) t -> S v (MuBind v t))
                        : forall v t, S v t :=
fix mu_term_rect v t :=
  match t as t return S v t with
  | MuTerm _ (VarTH _ _ x) => mu_term_var _ x
  | MuTerm _ (ConsTH _ _ n f ts) => mu_term_cons _ f n ts (fun i => mu_term_rect _ (ts i))
  | MuBind _ t => mu_term_bind _ t (mu_term_rect _ _)
  end.

Module MuTerm.

Definition pure {v : Set} (x : v) : mu_term v := MuTerm _ (VarTH _ _ x).

Fixpoint map {v u : Set} (f : v -> u) (t : mu_term v) : mu_term u :=
match t with
| MuTerm _ (VarTH _ _ x) => MuTerm _ (VarTH _ _ (f x))
| MuTerm _ (ConsTH _ _ n f' ts) => MuTerm _ (ConsTH _ _ n f' (fun i => map f (ts i)))
| MuBind _ t => MuBind _ (map (option_map f) t)
end.

Fixpoint bind {v u : Set} (k : v -> mu_term u) (t : mu_term v) : mu_term u :=
match t with
| MuTerm _ (VarTH _ _ x) => k x
| MuTerm _ (ConsTH _ _ n f ts) => MuTerm _ (ConsTH _ _ n f (fun i => bind k (ts i)))
| MuBind _ t =>
  let k' x :=
    match x with
    | None => MuTerm _ (VarTH _ _ None)
    | Some x => map Some (k x)
    end
  in MuBind _ (bind k' t)
end.

Inductive wf {v} : mu_term v -> Prop :=
| VarWF : forall x, wf (MuTerm _ (VarTH _ _ x))
| ConsWF : forall f n ts, (forall (i : fin n), wf (ts i)) -> wf (MuTerm _ (ConsTH _ _ n f ts))
| BindWF : forall n f ts, wf (MuTerm _ (ConsTH _ _ n f ts))
          -> wf (MuBind _ (MuTerm _ (ConsTH _ _ n f ts)))
.

Lemma wf_cons_list {v f n} {ts : array (mu_term v) n}
                   (twf : wf (MuTerm v (ConsTH _ _ n f ts)))
                   : forall (i : fin n), wf (ts i).
Proof. inversion twf. apply inj_pair2_eq_dec in H2. rewrite H2 in H0. auto. apply Nat.eq_dec. Qed.

Lemma wf_bind_nested {v t} (twf : wf (MuBind v t)) : wf t.
Proof. inversion_clear twf. auto. Qed.

Lemma no_bind_var {v x} (twf : wf (MuBind v (MuTerm _ (VarTH _ _ x)))) : False.
Proof. inversion_clear twf. Qed.

Lemma no_bind_bind {v t} (twf : wf (MuBind v (MuBind _ t))) : False.
Proof. inversion_clear twf. Qed.

Lemma wf_map {v u : Set} {t} (f : v -> u) (twf : wf t) : wf (map f t).
Proof.
  generalize dependent u. induction twf; auto; constructor.
  - intro. apply H0.
  - apply IHtwf.
Qed.

Lemma wf_bind {v u} {t : mu_term v} (twf : wf t)
              (k : v -> mu_term u) (twfs : forall (x : v), wf (k x))
              : wf (bind k t).
Proof.
  generalize dependent u. induction twf; intros; simpl.
  - apply twfs.
  - constructor. intro. apply H0. auto.
  - specialize (IHtwf _ (fun x =>
      match x with Some x => map Some (k x) | None => MuTerm _ (VarTH _ _ None) end)).
    constructor. apply IHtwf. intro. destruct x.
    + apply wf_map. auto.
    + constructor.
Qed.

Definition one_unfold_k {v : Set} (t : mu_term (option v)) (x : option v) :=
match x with
| None => MuBind _ t
| Some x => MuTerm _ (VarTH _ _ x)
end.

Lemma wf_one_unfold_not_bind {v : Set} {t t' : mu_term (option v)} (twf : wf (MuBind _ t))
                             : bind (one_unfold_k t) t <> MuBind _ t'.
Proof. inversion twf. intro. inversion H1. Qed.

Corollary wf_one_unfold_wf {v : Set} {t : mu_term (option v)}
                           (twf : wf (MuBind _ t)) : wf (bind (one_unfold_k t) t).
Proof. apply wf_bind. apply wf_bind_nested. auto. intro. destruct x; auto. constructor. Qed.

CoFixpoint unfold {v} (t : mu_term v) (twf : wf t) : infinite_term v :=
match t, twf with
| MuTerm _ (VarTH _ _ v), _ => InfTerm _ (VarTH _ _ v)
| MuTerm _ (ConsTH _ _ n f ts), twf =>
  let twfs := wf_cons_list twf
  in InfTerm _ (ConsTH _ _ n f (fun i => unfold (ts i) (twfs i)))
| MuBind _ t', twf =>
  match bind (one_unfold_k t') t' as t''
  return bind (one_unfold_k t') t' = t'' -> wf t'' -> infinite_term v with
  | MuTerm _ (VarTH _ _ v) => fun _ _ => InfTerm _ (VarTH _ _ v)
  | MuTerm _ (ConsTH _ _ n f ts) => fun _ twf =>
    let twfs : forall (i : fin n), wf (ts i) := wf_cons_list twf
    in InfTerm _ (ConsTH _ _ n f (fun i => unfold (ts i) (twfs i)))
  | MuBind _ t'' => fun p _ => False_rec _ (wf_one_unfold_not_bind twf p)
  end eq_refl (wf_one_unfold_wf twf)
end.

(*
(* not working *)

Definition resolve_var {v n} (t : array (infinite_term v) n) (x : n_options n v) : infinite_term v.
Admitted.

CoFixpoint unfold_mu_term_aux {v} n (t : mu_term (n_options n v)) (twf : wf t)
                              (ctx : array (infinite_term v) n) : infinite_term v :=
match t, twf with
| MuTerm _ (VarTH _ _ x), _ => resolve_var ctx x
| MuTerm _ (ConsTH _ _ n' f ts), twf =>
  InfTerm _ (ConsTH _ _ n' f (fun i => unfold_mu_term_aux n (ts i) (wf_cons_list twf i) ctx))
| MuBind _ (MuTerm _ (VarTH _ _ _)), twf => False_rec _ (no_bind_var twf)
| MuBind _ (MuTerm _ (ConsTH _ _ n' f ts)), twf =>
  let twfs := wf_cons_list (wf_bind_nested twf)
  in cofix this := InfTerm v (ConsTH v _ n' f (fun (i : fin n') =>
    unfold_mu_term_aux (S n) (ts i) (twfs i) (fun (i : fin (S n)) =>
      match i with None => this | Some i => ctx i end)))
| MuBind _ (MuBind _ t), twf => False_rec _ (no_bind_bind twf)
end.
*)

Definition array_sum {n} (xs : array nat n) : nat := array_rec 0 (fun x acc => x + acc) n xs.

Lemma array_sum_ext {n} (xs ys : array nat n) (p : forall i, xs i = ys i)
                    : array_sum xs = array_sum ys.
Proof. induction n. auto. simpl. f_equal; auto. Qed.

Lemma array_sum_take_step {n} (i : fin n) (xs : array nat n)
  : array_sum (array_take (fin_nat i) (Nat.lt_le_incl _ _ fin_nat_prop) xs) + xs i
    = array_sum (array_take (S (fin_nat i)) fin_nat_prop xs).
Proof.
  induction n. contradiction. destruct i as [ i | ].
  - specialize (IHn i (fun i => xs (Some i))). simpl in *.
    rewrite <- Nat.add_assoc. f_equal.
    etransitivity. 2: etransitivity. 2: apply IHn.
    * f_equal. eapply array_sum_ext. intro j. unfold array_take. simpl.
      f_equal. f_equal. apply nat_fin_irrelevance.
    * f_equal.
      + unfold array_take. simpl. f_equal. f_equal. apply nat_fin_irrelevance.
      + unfold array_take. simpl. apply array_sum_ext. intro.
        f_equal. f_equal. apply nat_fin_irrelevance.
  - simpl. rewrite Nat.add_comm. auto.
Qed.

Lemma array_sum_take_le {n} (xs : array nat n) (i : nat) (p : i <= n)
                       : array_sum (array_take i p xs) <= array_sum xs.
Proof.
  generalize dependent i. induction n.
  - intros. destruct i; inversion p. auto.
  - intros. destruct i as [ i | ]. apply Nat.le_0_l.
    simpl. apply Nat.add_le_mono_l. specialize (IHn (fun i => xs (Some i)) i).
    specialize (le_S_n _ _ p). intro. specialize (IHn H).
    erewrite array_sum_ext. apply IHn. intro j. unfold array_take. simpl.
    f_equal. f_equal. apply nat_fin_irrelevance.
Qed.

Fixpoint array_sum_i {n} (xs : array nat n) (i : fin (array_sum xs)) : fin n :=
match n as n'
return forall (xs : array nat n') (i : fin (array_sum xs)), fin n' with
| 0 => fun xs i => match i with end
| S n => fun xs i =>
  let i' := fin_nat i
  in match i' <? xs None as cond
  return i' <? xs None = cond -> fin (S n) with
  | true => fun _ => None
  | false => fun p => Some (array_sum_i (fun i => xs (Some i))
    (nat_fin (array_sum _) (i' - xs None) (proj2 (Nat.add_lt_mono_r (i' - xs None) _ (xs None))
      (rew <- [fun x => x < _] Nat.sub_add (xs None) i' (proj1 (Nat.ltb_ge i' (xs None)) p) in
        rew Nat.add_comm (xs None) (array_sum _) in fin_nat_prop))))
  end eq_refl
end xs i.

Lemma array_sum_i_prop1 {n} (xs : array nat n) (i : fin (array_sum xs))
                        : let i' := fin_nat (array_sum_i xs i)
                          in array_sum (array_take i' (Nat.lt_le_incl _ _ fin_nat_prop) xs)
                            <= fin_nat i < array_sum (array_take (S i') fin_nat_prop xs).
Proof.
  induction n. inversion i. simpl in *.

  set (b := fin_nat i <? xs None).
  set (fn := fun p0 : b = false => Some (array_sum_i (fun i => xs (Some i))
    (nat_fin (array_sum (fun i => xs (Some i))) (fin_nat i - xs None)
      (proj2 (Nat.add_lt_mono_r (fin_nat i - xs None) (array_sum (fun i => xs (Some i))) (xs None))
        (rew <- [fun x => x < array_sum (fun i => xs (Some i)) + xs None]
          Nat.sub_add (xs None) (fin_nat i) (proj1 (Nat.ltb_ge (fin_nat i) (xs None)) p0)
          in rew [lt (fin_nat i)] Nat.add_comm (xs None) (array_sum (fun i0 : fin n => xs (Some i0)))
          in fin_nat_prop))))).

  refine (_ : array_sum (array_take (fin_nat
    ((if b as cond return (b = cond -> fin (S n))
    then fun _ : b = true => None else fn) eq_refl)) (Nat.lt_le_incl _ _ fin_nat_prop) xs)
    <= fin_nat i < array_take (S (fin_nat
      ((if b as cond return (b = cond -> fin (S n))
      then fun _ : b = true => None else fn) eq_refl))) fin_nat_prop xs None
      + array_sum (fun i0 : fin _ => array_take (S (fin_nat
        ((if b as cond return (b = cond -> fin (S n))
        then fun _ : b = true => None else fn) eq_refl))) fin_nat_prop xs (Some i0))).

  assert (Hfn : forall (q : b = false), exists q', fn q = Some (array_sum_i _
    (nat_fin (array_sum (fun i => xs (Some i))) (fin_nat i - xs None) q'))). {
    intro. eexists. reflexivity.
  }

  generalize dependent fn.

  assert (Hb_lt : b = true -> fin_nat i < xs None) by (intro; apply Nat.ltb_lt; auto).
  assert (Hb_ge : b = false -> fin_nat i >= xs None) by (intro; apply Nat.ltb_ge; auto).

  generalize dependent b. intros. destruct b; simpl.
  - constructor. apply Nat.le_0_l. rewrite Nat.add_0_r. apply Hb_lt. auto.
  - specialize (Hb_ge eq_refl). specialize (Hfn eq_refl). destruct Hfn.
    
    specialize (IHn (fun i => xs (Some i)) (nat_fin _ (fin_nat i - xs None) x)).
    rewrite nat_fin_nat in IHn. destruct IHn. constructor.
    * rewrite H. unfold array_take at 1. simpl. rewrite Nat.add_comm.
      rewrite <- (Nat.sub_add (xs None) (fin_nat i)); auto. apply Nat.add_le_mono_r.
      evar (lhs1 : nat). evar (lhs2 : nat). refine (_ : lhs1 <= _).
      unshelve evar (Hlhs : lhs1 = lhs2); [ | rewrite Hlhs; exact H0 ].
      subst lhs1 lhs2. eapply array_sum_ext. intro. erewrite nat_fin_irrelevance. reflexivity.
    * rewrite H. rewrite <- (Nat.sub_add (xs None) (fin_nat i)) at 1; auto.
      unfold array_take at 1. simpl. rewrite (Nat.add_comm (xs None) (_ + _)).
      apply Nat.add_lt_mono_r. evar (rhs1 : nat). evar (rhs2 : nat). refine (_ : _ < rhs1).
      unshelve evar (Hrhs : rhs1 = rhs2); [ | rewrite Hrhs; exact H1 ].
      subst rhs1 rhs2. unfold array_take. simpl. f_equal.
      + erewrite nat_fin_irrelevance. reflexivity.
      + apply array_sum_ext. intro. erewrite nat_fin_irrelevance. reflexivity.
Qed.

Lemma array_sum_i_prop2 {n} (xs : array nat n) (i : fin (array_sum xs)) (j : fin n)
                        (p : let j' := fin_nat j
                             in array_sum (array_take j' (Nat.lt_le_incl _ _ fin_nat_prop) xs)
                          <= fin_nat i < array_sum (array_take (S j') fin_nat_prop xs))
                        : array_sum_i xs i = j.
Proof.
  induction n. inversion j. simpl in *.

  set (b1 := fin_nat i <? xs None) in *.
  set (fn := fun p0 : b1 = false => Some
    (array_sum_i (fun i0 : fin n => xs (Some i0))
       (nat_fin (array_sum (fun i0 : fin n => xs (Some i0)))
          (fin_nat i - xs None)
          (proj2
             (Nat.add_lt_mono_r (fin_nat i - xs None)
                (array_sum (fun i0 : fin n => xs (Some i0)))
                (xs None))
             (rew <- [fun x : nat =>
                      x <
                      array_sum (fun i0 : fin n => xs (Some i0)) + xs None]
                  Nat.sub_add (xs None) (fin_nat i)
                    (proj1 (Nat.ltb_ge (fin_nat i) (xs None)) p0) in
              rew [lt (fin_nat i)]
                  Nat.add_comm (xs None)
                    (array_sum (fun i0 : fin n => xs (Some i0))) in
              fin_nat_prop))))).

  refine (_ : (if b1 as cond return b1 = cond -> fin (S n)
    then fun _ : b1 = true => None else fn) eq_refl = j).

  assert (Hlt : b1 = true -> fin_nat i < xs None) by (intro; apply Nat.ltb_lt; auto).
  assert (Hge : b1 = false -> fin_nat i >= xs None) by (intro; apply Nat.ltb_ge; auto).

  assert (Hfn : forall (q : b1 = false), exists q',
    fn q = Some (array_sum_i (fun i => xs (Some i)) (nat_fin _ (fin_nat i - xs None) q')))
    by (intros; eexists; reflexivity).

  generalize dependent fn. destruct b1; destruct j as [ j | ]; intros; auto.
  * destruct p as [ p _ ]. simpl in p. specialize (Hlt eq_refl).
    assert (p' : xs None <= fin_nat i) by (eapply Nat.le_trans; [ | apply p ]; apply Nat.le_add_r).
    exfalso. eapply Nat.lt_irrefl. eapply Nat.lt_le_trans. eauto. auto.
  * specialize (Hge eq_refl). specialize (Hfn eq_refl). destruct Hfn as [ q' Hfn ]. rewrite Hfn.
    f_equal. apply IHn. rewrite nat_fin_nat. constructor.
    + destruct p as [ p _ ]. apply <- Nat.add_le_mono_r. rewrite Nat.sub_add; auto.
      rewrite Nat.add_comm. simpl in p. refine (rew [fun x => x <= _] _ in p).
      f_equal. apply array_sum_ext. intro. unfold array_take. simpl.
      erewrite nat_fin_irrelevance. reflexivity.
    + destruct p as [ _ p ]. refine (_ : _ < array_sum (array_take (S (fin_nat j)) _ _)).
      apply <- Nat.add_lt_mono_r. rewrite Nat.sub_add; auto. rewrite Nat.add_comm.
      refine (rew [fun x => _ < _ + x] _ in p). apply array_sum_ext. intro.
      unfold array_take. simpl. erewrite nat_fin_irrelevance. reflexivity.
  *  specialize (Hge eq_refl). specialize (Hfn eq_refl). destruct Hfn as [ q' _ ].
     simpl in p. destruct p as [ _ p ]. rewrite Nat.add_0_r in p. exfalso.
     eapply Nat.lt_irrefl. eapply Nat.lt_le_trans. apply p. auto.
Qed.

Lemma array_sum_i_prop {n} (xs : array nat n) (i : fin (array_sum xs)) (j : fin n)
                       : let j' := fin_nat j
                         in array_sum (array_take j' (Nat.lt_le_incl _ _ fin_nat_prop) xs)
                           <= fin_nat i < array_sum (array_take (S j') fin_nat_prop xs)
                         <-> array_sum_i xs i = j.
Proof. constructor. apply array_sum_i_prop2. intro. rewrite <- H. apply array_sum_i_prop1. Qed.

Lemma array_sum_i_ext {n} (xs ys : array nat n) (i : fin (array_sum xs)) (j : fin (array_sum ys))
                      (p : let i' := (fin_nat (array_sum_i xs i))
                        in array_sum (array_take i' (Nat.lt_le_incl _ _ fin_nat_prop) ys)
                        <= fin_nat j < array_sum (array_take (S i') fin_nat_prop ys))
                      : array_sum_i xs i = array_sum_i ys j.
Proof. symmetry. apply array_sum_i_prop. apply p. Qed.

Fixpoint array_sum_j {n} (xs : array nat n) (i : fin (array_sum xs))
                     : fin (xs (array_sum_i xs i)) :=
match n as n'
return forall (xs : array nat n') (i : fin (array_sum xs)), fin (xs (array_sum_i xs i)) with
| 0 => fun xs i => match i with end
| S n => fun xs i =>
  let i' := fin_nat i
  in match i' <? xs None as cond
  return forall (p : i' <? xs None = cond), fin (xs (
    match cond as cond
    return i' <? xs None = cond -> fin (S n) with
    | true => fun _ => None
    | false => fun p => Some (array_sum_i (fun i => xs (Some i))
      (nat_fin (array_sum _) (i' - xs None) _))
    end p)
  ) with
  | true => fun p => nat_fin (xs None) i' (proj1 (Nat.ltb_lt i' (xs None)) p)
  | false => fun p => array_sum_j (fun i => xs (Some i)) _
  end eq_refl
end xs i.

Lemma array_sum_ij_prop {n} (xs : array nat n) (i : fin (array_sum xs))
                        : fin_nat i = array_sum (array_take (fin_nat (array_sum_i xs i))
                          (Nat.lt_le_incl _ _ fin_nat_prop) xs) + fin_nat (array_sum_j xs i).
Proof.
  induction n. inversion i. simpl. set (b := fin_nat i <? xs None).

  set (fun1 := fun p : b = false =>
    Some (array_sum_i (fun i0 : fin n => xs (Some i0))
      (nat_fin (array_sum (fun i0 : fin n => xs (Some i0))) (fin_nat i - xs None)
        (proj2 (Nat.add_lt_mono_r (fin_nat i - xs None)
          (array_sum (fun i0 : fin n => xs (Some i0))) (xs None))
          (rew <- [fun x : nat => x < array_sum (fun i0 : fin n => xs (Some i0)) + xs None]
            Nat.sub_add (xs None) (fin_nat i) (proj1 (Nat.ltb_ge (fin_nat i) (xs None)) p) in
            rew [lt (fin_nat i)] Nat.add_comm (xs None) (array_sum (fun i0 : fin n => xs (Some i0)))
            in fin_nat_prop))))).

  set (fun2 := fun p : b = true =>
    nat_fin (xs None) (fin_nat i) (proj1 (Nat.ltb_lt (fin_nat i) (xs None)) p)).

  set (fun3 := fun p : b = false =>
    array_sum_j (fun i0 : fin n => xs (Some i0))
      (nat_fin (array_sum (fun i0 : fin n => xs (Some i0))) (fin_nat i - xs None)
        (proj2 (Nat.add_lt_mono_r (fin_nat i - xs None)
          (array_sum (fun i0 : fin n => xs (Some i0))) (xs None))
          (rew <- [fun x : nat => x < array_sum (fun i0 : fin n => xs (Some i0)) + xs None]
            Nat.sub_add (xs None) (fin_nat i) (proj1 (Nat.ltb_ge (fin_nat i) (xs None)) p) in
            rew [lt (fin_nat i)] Nat.add_comm (xs None) (array_sum (fun i0 : fin n => xs (Some i0)))
            in fin_nat_prop))) : fin (xs (fun1 p))).

  refine (_ : fin_nat i = array_sum (array_take
    (fin_nat (match b as cond return (b = cond -> fin (S n)) with
    | true => fun _ : b = true => None
    | false => fun1
    end eq_refl)) (Nat.lt_le_incl _ _ fin_nat_prop) xs)
    + fin_nat (match b as cond return forall (p : b = cond),
      fin (xs (match cond as cond' return b = cond' -> fin (S n) with
        | true => fun _ : b = true => None
        | false => fun1
        end p)) with
    | true => fun2
    | false => fun3
    end eq_refl)).

  assert (Hfun2 : forall (q : b = true), fin_nat i = fin_nat (fun2 q)). {
    intro. unfold fun2. rewrite nat_fin_nat. auto.
  }

  assert (Hfun13 : forall (q : b = false), fin_nat i = array_sum (array_take
    (fin_nat (fun1 q : fin (S n))) (Nat.lt_le_incl _ _ fin_nat_prop) xs) + fin_nat (fun3 q)). {
    intro. unfold fun3. simpl. unfold array_take. simpl. rewrite <- Nat.add_assoc.
    specialize (IHn (fun i => xs (Some i))). etransitivity.
    2: {
      apply (f_equal (fun x => xs None + x)). etransitivity. apply IHn. f_equal.
      * apply array_sum_ext. intro. unfold array_take. erewrite nat_fin_irrelevance. auto.
      * reflexivity.
    }
    rewrite nat_fin_nat. rewrite Nat.add_comm. symmetry. apply Nat.sub_add.
    apply Nat.ltb_ge. auto.
  }
  generalize dependent fun2.
  generalize dependent fun3.
  generalize dependent fun1.
  destruct b; intros.
  - apply Hfun2.
  - apply Hfun13.
Qed.

Corollary array_sum_j_prop {n} (xs : array nat n) (i : fin (array_sum xs))
                           : fin_nat (array_sum_j xs i) = fin_nat i
                             - array_sum (array_take (fin_nat (array_sum_i xs i))
                               (Nat.lt_le_incl _ _ fin_nat_prop) xs).
Proof. rewrite array_sum_ij_prop. rewrite Nat.add_comm. symmetry. apply Nat.add_sub. Qed.

Corollary array_sum_ij_prop1 {n} (xs : array nat n) (i : fin (array_sum xs))
                             : fin_nat i - fin_nat (array_sum_j xs i)
                               = array_sum (array_take (fin_nat (array_sum_i xs i))
                                 (Nat.lt_le_incl _ _ fin_nat_prop) xs).
Proof. rewrite array_sum_ij_prop. apply Nat.add_sub. Qed.

Inductive path :=
| HerePath : path
| ConsPath : nat -> path -> path
.

Fixpoint unfold_subterms_n {v} (t : mu_term v) : nat :=
match t with
| MuTerm _ (VarTH _ _ _) => 1
| MuTerm _ (ConsTH _ _ n _ ts) =>
  1 + array_sum (fun i => unfold_subterms_n (ts i))
| MuBind _ t => unfold_subterms_n t
end.

Lemma unfold_subterms_n_min {v} (t : mu_term v) : unfold_subterms_n t > 0.
Proof. induction t; try apply Nat.lt_0_succ. apply IHt. Qed.

Fixpoint path_i {v} (t : mu_term v) (i : fin (unfold_subterms_n t)) : path :=
match t as t' return fin (unfold_subterms_n t') -> path with
| MuTerm _ (VarTH _ _ _) => fun _ => HerePath
| MuTerm _ (ConsTH _ _ n f ts) => fun i =>
  match i with
  | None => HerePath
  | Some i =>
    let i' := array_sum_i _ i
    in ConsPath (fin_nat i') (path_i (ts i') (array_sum_j _ i))
  end
| MuBind _ t => path_i t
end i.

Lemma path_i_inj {v} (t : mu_term v) (i1 i2 : fin (unfold_subterms_n t))
                 (p : path_i t i1 = path_i t i2) : i1 = i2.
Proof.
  induction t.
  - destruct i1; destruct i2; auto; contradiction.
  - destruct i1 as [ i1 | ]; destruct i2 as [ i2 | ]; auto; inversion p; clear p. f_equal.
    simpl in *. apply fin_nat_inj in H1. apply fin_nat_inj.
    etransitivity. apply array_sum_ij_prop.
    etransitivity. 2: symmetry; apply array_sum_ij_prop.
    set (i1i := array_sum_i _ i1). set (i1j := array_sum_j _ i1).
    set (i2i := array_sum_i _ i2). set (i2j := array_sum_j _ i2).
    remember (H1 : i1i = i2i) as i1i_i2i. clear H1 Heqi1i_i2i.
    f_equal. rewrite i1i_i2i. auto.
    specialize (H i1i i1j).
    set (i1i_i2i' := f_equal (fun m => unfold_subterms_n (ts m)) i1i_i2i).
    specialize (H (rew <- [fin] i1i_i2i' in i2j)).
    rewrite H; clear H.
    * clear H2. generalize dependent i1i_i2i'. clear i1i_i2i i1j.
      remember i1i. clear Heqf1 i1i. remember i2j. clear i2j Heqf2.
      generalize dependent (array_sum_i _ i2). clear i1 i2. simpl. intros.
      destruct i1i_i2i'. auto.
    * etransitivity. apply H2. clear H2.
      refine (_ : path_i (ts i2i) i2j = path_i (ts i1i) (rew <- i1i_i2i' in i2j)).
      remember i1i_i2i. clear Heqe. unfold i1i_i2i'. clear i1j i1i_i2i i1i_i2i'.
      generalize dependent i1i. generalize dependent i2j. generalize dependent (array_sum_i _ i2).
      simpl. clear i1 i2. intros. destruct e. auto.
  - apply IHt. auto.
Qed.

Fixpoint path_i_bind {v u : Set} (t : mu_term v) (k : v -> mu_term u) (p : path)
                     (i : fin (unfold_subterms_n t)) (q : path_i t i = p)
                     : fin (unfold_subterms_n (bind k t)) :=
match t as t'
return forall (i : fin (unfold_subterms_n t')), path_i t' i = p
-> fin (unfold_subterms_n (bind k t')) with
| MuTerm _ (VarTH _ _ x) => fun _ _ =>
  match unfold_subterms_n (k x) as n return n > 0 -> fin n with
  | 0 => fun q => False_rec _ match q with end
  | S _ => fun _ => None
  end (unfold_subterms_n_min (k x))
| MuTerm _ (ConsTH _ _ n f ts) => fun i =>
  match i as i' return path_i (MuTerm _ (ConsTH _ _ n f ts)) i' = p -> fin (S _) with
  | None => fun q => None
  | Some i =>
    let i : fin (array_sum (fun i => unfold_subterms_n (ts i))) := i
    in match p as p' return path_i (MuTerm _ (ConsTH _ _ n f ts)) (Some i) = p' -> fin (S _) with
    | HerePath => fun q => False_rec _ (eq_rec (path_i (MuTerm _ (ConsTH _ _ n f ts)) (Some i))
      (fun p => match p with HerePath => False | _ => unit end) tt HerePath q)
    | ConsPath _ p => fun q =>
      let i' := array_sum_i (fun i => unfold_subterms_n (ts i)) i
      in let j' := path_i_bind (ts i') k p (array_sum_j _ i)
        (match q with eq_refl => eq_refl end)
      in Some (nat_fin _ (array_sum (array_take (fin_nat i') (Nat.lt_le_incl _ _ fin_nat_prop)
        (fun i => unfold_subterms_n (bind k (ts i)))) + fin_nat j')
        (Nat.lt_le_trans _ (array_sum (array_take (S (fin_nat _)) fin_nat_prop _)) _
          (rew array_sum_take_step (array_sum_i _ i) _ in
            proj1 (Nat.add_lt_mono_l _ _ _) fin_nat_prop) (array_sum_take_le _ _ _)))
    end
  end
| MuBind _ t => fun i q => path_i_bind t _ p i q
end i q.

Lemma path_i_bind_irrelevance {v u : Set} (t : mu_term v) (k : v -> mu_term u) (p : path)
                              (i : fin (unfold_subterms_n t)) (q1 q2 : path_i t i = p)
                              : path_i_bind t k p i q1 = path_i_bind t k p i q2.
Proof.
  generalize dependent u. generalize dependent p. induction t; intros. auto.
  - destruct i; auto. destruct p. inversion q1.
    simpl. f_equal. apply nat_fin_ext. f_equal. f_equal. apply H.
  - simpl. apply IHt.
Qed.

Lemma path_0_is_here {v n} (t : mu_term v) (p : S n = unfold_subterms_n t)
                     : path_i t (rew p in None) = HerePath.
Proof.
  generalize dependent n. induction t; auto.
  intros m p. rewrite (fin_n_m p (y := None)). auto. apply fin_0_0.
Qed.

Lemma path_i_bind_prop {v u : Set} (t : mu_term v) (k : v -> mu_term u) (p : path)
                       (i : fin (unfold_subterms_n t)) (q : path_i t i = p)
                       : path_i (bind k t) (path_i_bind t k p i q) = p.
Proof.
  generalize dependent u. generalize dependent p. induction t; intros.
  - transitivity HerePath; auto. simpl in *. clear i q.
    generalize dependent (unfold_subterms_n_min (k x)). intro.
    assert (exists n, S n = unfold_subterms_n (k x)).
    * destruct unfold_subterms_n. inversion g. exists n. auto.
    * destruct H as [ n q ].
    etransitivity. 2: apply (path_0_is_here _ q). f_equal.
    destruct (unfold_subterms_n (k x)). inversion q. symmetry. apply fin_0_0.
  - destruct i as [ i | ]; auto. destruct p; inversion q. simpl. f_equal.
    * etransitivity; [ | apply H1 ]. f_equal. symmetry. apply array_sum_i_ext.
      constructor; rewrite nat_fin_nat.
      + apply Nat.le_add_r.
      + rewrite <- array_sum_take_step. apply Nat.add_lt_mono_l. apply fin_nat_prop.
    * assert (H2' : path_i (ts (array_sum_i (fun i => unfold_subterms_n (ts i)) i))
        (array_sum_j (fun i => unfold_subterms_n (ts i)) i) = p) by exact H2.
      clear H2. rename H2' into H2.

      etransitivity; [ | apply (H _ _ _ H2 _ k) ].

      evar (i' : fin n).
      evar (j' : fin (unfold_subterms_n (bind k (ts i')))).
      refine (_ : path_i (bind k (ts i')) j' = _).

      assert (Hi : i' = array_sum_i (fun i0 : fin n => unfold_subterms_n (ts i0)) i). {
        symmetry. apply array_sum_i_ext. constructor; rewrite nat_fin_nat.
        + apply Nat.le_add_r.
        + rewrite <- array_sum_take_step. apply Nat.add_lt_mono_l. apply fin_nat_prop.
      }

      evar (i'' : fin (array_sum (fun i => unfold_subterms_n (bind k (ts i))))).
      refine (let _ := eq_refl : i' = array_sum_i _ i'' in _). clear e.

      assert (Hj : fin_nat j' = fin_nat (path_i_bind
        (ts (array_sum_i (fun i => unfold_subterms_n (ts i)) i)) k p
        (array_sum_j (fun i => unfold_subterms_n (ts i)) i) H2)). {
        unfold j'. etransitivity.
        apply (array_sum_j_prop (fun i => unfold_subterms_n (bind k (ts i))) i'').
        unfold i''. rewrite nat_fin_nat. rewrite Nat.add_comm at 1.

        assert (aux : forall n m p, m = p -> n + m - p = n). {
          intros. rewrite H0. apply Nat.add_sub.
        }

        etransitivity. eapply aux.
        + clear H1 H2 aux.

          assert (aux : forall n1 n2 (p : n1 = n2) (xs1 : array nat n1) (xs2 : array nat n2),
            (forall i, xs1 i = xs2 (rew [fin] p in i)) -> array_sum xs1 = array_sum xs2). {
            intros n1 n2 p'. rewrite p'. intros. apply array_sum_ext; auto.
          }

          unshelve eapply aux. f_equal. symmetry. apply Hi. intro. clear aux.
          unfold array_take. simpl. f_equal. f_equal. f_equal. apply nat_fin_ext.
          symmetry. apply fin_nat_rew.
        + f_equal. apply path_i_bind_irrelevance.
      }

      generalize dependent j'.
      generalize dependent i'.
      intro. intro. rewrite Hi. intros. f_equal.
      etransitivity. symmetry. apply fin_nat_fin.
      etransitivity; [ | apply fin_nat_fin ].
      apply nat_fin_ext. apply Hj.
  - apply IHt.
Qed.

Corollary path_i_one_unfold_prop {v : Set} (t1 t2 : mu_term (option v)) (p : path)
                            (i : fin (unfold_subterms_n t2)) (q : path_i t2 i = p)
                            : path_i (bind (one_unfold_k t1) t2) (path_i_bind t2 _ p i q) = p.
Proof. apply path_i_bind_prop. Qed.

Fixpoint unfold_subterm {v} {t : mu_term v} (twf : wf t) (i : fin (unfold_subterms_n t))
                        (p : path) (q : path_i t i = p) : infinite_term v :=
match p, q with
| HerePath, _ => unfold t twf
| ConsPath x p, q =>
  match t as t' return wf t' -> forall i', path_i t' i' = ConsPath x p -> infinite_term v with
  | MuTerm _ (VarTH _ _ _) => fun twf i q =>
    False_rec _ (eq_rec HerePath (fun p => match p with HerePath => unit | _ => False end) tt _ q)
  | MuTerm _ (ConsTH _ _ n _ ts) => fun twf i q =>
    match i, q with
    | None, q =>
      False_rec _ (eq_rec HerePath (fun p => match p with HerePath => unit | _ => False end) tt _ q)
    | Some i, q =>
      unfold_subterm (wf_cons_list twf (array_sum_i _ i)) (array_sum_j _ i) p
        (match q with eq_refl => eq_refl end)
    end
  | MuBind _ t => fun twf i q =>
    match t as t', twf return forall i', path_i t' i' = ConsPath x p -> infinite_term v with
    | MuTerm _ (VarTH _ _ _), twf => fun _ => False_rect _ match twf with end
    | MuTerm _ (ConsTH _ _ n f ts), twf => fun i q =>
      match i, q with
      | None, q => unfold _ (wf_one_unfold_wf twf)
      | Some i, q =>
        unfold_subterm (wf_cons_list (wf_one_unfold_wf twf) (array_sum_i _ i))
          (path_i_bind _ _ p (array_sum_j _ i) (match q with eq_refl => eq_refl end)) p
          (path_i_one_unfold_prop _ _ _ _ _)
      end
    | MuBind _ t, twf => False_rec _ match twf with end
    end i q
  end twf i q
end.

Lemma unfold_subterm_prop {v} {t : mu_term v} (twf : wf t) (i : fin (unfold_subterms_n t))
                          (p : path) (q : path_i t i = p)
                          : InfiniteTerm.subterm (unfold_subterm twf i p q) (unfold t twf).
Proof.
  generalize dependent t. induction p; intros. constructor. apply InfiniteTerm.eq_refl.
  destruct t. destruct t. inversion q.
  - destruct i as [ i | ]; [ | inversion q ]. rewrite (InfiniteTerm.step_prop (unfold _ _)).
    eapply InfiniteTerm.ConsInfSubterm. apply IHp. exists (array_sum_i _ i). reflexivity.
  - destruct t; [ destruct t | ]; inversion twf. destruct i as [ i | ]; [ | inversion q ].
    rewrite (InfiniteTerm.step_prop (unfold (MuBind v _) _)). eapply InfiniteTerm.ConsInfSubterm.
    simpl. apply IHp. exists (array_sum_i _ i). reflexivity.
Qed.

Lemma unfold_subterm_irrelevance {v} {t : mu_term v} (twf : wf t) (i : fin (unfold_subterms_n t)) 
                         (p : path) (q1 q2 : path_i t i = p)
                         : unfold_subterm twf i p q1 = unfold_subterm twf i p q2.
Proof.
  generalize dependent t. induction p; intros. auto.
  destruct t. destruct t. inversion q1.
  - destruct i as [ i | ]; [ | inversion q1 ]. apply IHp.
  - destruct t; [ | inversion twf ]. destruct t. inversion twf.
    destruct i as [ i | ]; [ | inversion q1 ]. etransitivity. apply IHp.
    apply (EqdepFacts.f_eq_dep_non_dep _ (fun j => path_i _ j = p) _ _ _ _ _
      (fun j q => @unfold_subterm v _ _ j p q)). apply EqdepFacts.eq_sigT_eq_dep.
    unshelve eapply eq_existT_curried. apply path_i_bind_irrelevance.
    evar (x : nat). evar (q'T : fin x -> Prop). evar (y : fin x). evar (q' : q'T y).
    refine (rew_opp_r _ _ q': _ = q'). 
Qed.

Lemma unfold_subterm_ext {v} {t1 t2 : mu_term v} (Ht : t1 = t2)
                         (twf1 : wf t1) (twf2 : wf t2) (Htwf : rew Ht in twf1 = twf2)
                         (i1 : fin (unfold_subterms_n t1)) (i2 : fin (unfold_subterms_n t2))
                         (Hi : fin_nat i1 = fin_nat i2) (p : path)
                         (q1 : path_i t1 i1 = p) (q2 : path_i t2 i2 = p)
                         : unfold_subterm twf1 i1 p q1 = unfold_subterm twf2 i2 p q2.
Proof.
  destruct Ht. destruct (fin_nat_inj _ _ Hi). destruct Htwf.
  apply unfold_subterm_irrelevance.
Qed.

Definition unfold_subterms {v} (t : mu_term v) (twf : wf t)
                           : array (infinite_term v) (unfold_subterms_n t) :=
fun i => unfold_subterm twf i _ eq_refl.

(*
Inductive subterm {v} : infinite_term v -> infinite_term v -> Prop :=
| ReflInfSubterm : forall t1 t2, eq t1 t2 -> subterm t1 t2
| ConsInfSubterm : forall t1 t2 n f ts, subterm t1 t2 -> in_array t2 ts
                -> subterm t1 (InfTerm _ (ConsTH _ _ n f ts))
.
*)

Inductive mu_subst_telescope : Set -> Set :=
| NilMST : forall v, mu_subst_telescope v
| ConsMST {v : Set} : mu_term (option v) -> mu_subst_telescope v -> mu_subst_telescope (option v)
.

Inductive inf_mu_subterm {v} (vs : list (mu_term )) : forall n, infinite_term v -> mu_term (n_options n v) -> Prop :=
| ReflMuInfST : forall t twf, inf_mu_subterm 0 (unfold t twf) t
| ConsMuInfST : forall n m f ts1 ts2 i, inf_mu_subterm n (ts1 i) (ts2 i)
                                     -> inf_mu_subterm n (InfTerm _ (ConsTH _ _ m f ts1))
                                                         (MuTerm  _ (ConsTH _ _ m f ts2))

.

Lemma unfold_mu_bind_without_var {v : Set} (n : nat) (t : mu_term (n_options n v))
                                 (twf1 : wf t) (twf2 : wf (MuBind _ t)) (t' : infinite_term v)
                                 (H : InfiniteTerm.eq (InfiniteTerm.map (n_Somes n) t') (unfold t twf1))
                                 : InfiniteTerm.eq t' (unfold (MuBind _ t) twf2).
Proof.
  remember (InfiniteTerm.map Some t') as t1'. remember (unfold t twf1) as t1.
  cofix aux. destruct t' as [ t' ]. destruct t1 as [ t1 ]. destruct t1' as [ t1' ]. inversion H.
  - admit.
  - destruct t'; rewrite InfiniteTerm.step_prop in Heqt1'; inversion Heqt1'.
    rewrite H4 in H0; inversion H0.
    ...

Lemma unfold_subterm_surj_aux' {v : Set} (t : mu_term (option v)) (t' : infinite_term v)
                               (twf1 : wf t) (twf2 : wf (MuBind _ t))
                               (H : InfiniteTerm.subterm (InfiniteTerm.map Some t') (unfold t twf1))
                               : InfiniteTerm.subterm t' (unfold (MuBind _ t) twf2).
Proof.
  remember (InfiniteTerm.map Some t') as t1'. remember (unfold t twf1) as t1.
  induction H. rewrite Heqt1 in *. rewrite Heqt1' in *. constructor. eapply unfold_subterm_surj_aux''. eauto.

Lemma unfold_subterm_surj_aux {v} (t : mu_term v) (twf : wf t) (t' : infinite_term v)
                              (H : InfiniteTerm.subterm t' (unfold t twf))
                              : exists i p q, InfiniteTerm.eq t' (unfold_subterm twf i p q).
Proof.
  remember (unfold t twf) as t''. symmetry in Heqt''. generalize dependent t.
  induction H; intros.
  - destruct Heqt''.
    inversion twf; [ destruct H0 | destruct H1 .. ]; exists None, HerePath, eq_refl; auto.
  - rewrite (InfiniteTerm.step_prop (unfold _ _)) in Heqt''.
    inversion twf; [ destruct H1 | destruct H2 .. ]; simpl InfiniteTerm.step in Heqt'';
    inversion Heqt''; destruct H3; destruct H4.
    * admit.
    * apply inj_pair2_eq_dec in H5; [ | apply Nat.eq_dec ]. destruct H5. clear Heqt''.

Lemma unfold_subterm_surj_aux {v} (t : mu_term v) (twf : wf t) (t' : infinite_term v)
                                 (H : InfiniteTerm.subterm t' (unfold t twf))
                                 : exists i p q, InfiniteTerm.eq t' (unfold_subterm twf i p q).
Proof.
  induction t.
  - inversion H. exists None, HerePath, eq_refl. auto.
    rewrite InfiniteTerm.step_prop in H0. inversion H0.
  - inversion H. exists None, HerePath, eq_refl. auto.
    rewrite InfiniteTerm.step_prop in H1. simpl InfiniteTerm.step in *.
    inversion H1. destruct H3. destruct H6. destruct H7. destruct H4 as [ i H4 ]. destruct H4.
    apply inj_pair2_eq_dec in H8; [ | apply Nat.eq_dec ].
    rewrite H8 in H2. specialize (H0 i _ t1 H2). destruct H0 as [ j [ p [ q H0 ] ] ].
    set (i'' := S (array_sum (array_take (fin_nat i) (Nat.lt_le_incl _ _ fin_nat_prop)
      (fun i => unfold_subterms_n (ts i))) + fin_nat j)).
    assert (Hi' : i'' < unfold_subterms_n (MuTerm v (ConsTH v (mu_term v) n0 f1 ts))). {
      unfold i''. simpl. apply -> Nat.succ_lt_mono.
      eapply Nat.lt_le_trans; [ | apply (array_sum_take_le _ (S (fin_nat i)) fin_nat_prop) ].
      rewrite <- array_sum_take_step. apply Nat.add_lt_mono_l. apply fin_nat_prop.
    }
    subst i''. set (i' := nat_fin _ _ Hi'). exists i', (ConsPath (fin_nat i) p).
    assert (Hi : array_sum_i (fun i0 : fin n0 => unfold_subterms_n (ts i0))
      (nat_fin (array_sum (fun i0 : fin n0 => unfold_subterms_n (ts i0)))
        (array_sum (array_take (fin_nat i) (Nat.lt_le_incl (fin_nat i) n0 fin_nat_prop)
           (fun i0 : fin n0 => unfold_subterms_n (ts i0))) + fin_nat j)
        (PeanoNat.lt_S_n _ _ Hi')) = i). {
      apply array_sum_i_prop. rewrite nat_fin_nat. constructor.
        apply Nat.le_add_r. rewrite <- array_sum_take_step. apply Nat.add_lt_mono_l.
        apply fin_nat_prop.
    }
    assert (Hj : fin_nat j = fin_nat (array_sum_j (fun i0 : fin n0 => unfold_subterms_n (ts i0))
      (nat_fin _ _ (PeanoNat.lt_S_n _ _ Hi')))). {
      symmetry. etransitivity. apply (@array_sum_j_prop n0 (fun i => unfold_subterms_n (ts i))).
      rewrite nat_fin_nat.

      assert (aux : forall n m k, n = k -> n + m - k = m). {
        intros. rewrite H3. rewrite Nat.add_comm. apply Nat.add_sub.
      }

      etransitivity. apply aux. clear aux.
      evar (i1 : nat). evar (Hi1 : i1 <= n0). refine (_ : array_sum (array_take i1 Hi1 _) = _).

      assert (Hi1' : i1 = fin_nat (array_sum_i (fun i => unfold_subterms_n (ts i))
        (nat_fin (array_sum (fun i => unfold_subterms_n (ts i))) _ (PeanoNat.lt_S_n _ _ Hi'))))
        by (symmetry; unfold i1; f_equal; auto).
      generalize dependent Hi1. generalize dependent i1. intros i1 pi1. rewrite pi1. clear pi1.
      intros. apply array_sum_ext. intro. apply array_take_irrelevance. auto.
    }
    unshelve eexists.
    * simpl. f_equal. f_equal; auto. etransitivity; [ | apply q ].
      apply EqdepFacts.f_eq_dep_non_dep. apply EqdepFacts.eq_sigT_eq_dep. symmetry.
      apply (eq_existT_curried (eq_sym (f_equal _ Hi))). apply fin_nat_inj.
      etransitivity; [ | apply Hj ].
      etransitivity;
        [ | apply (fin_nat_rew _ _ _ (f_equal unfold_subterms_n (eq_sym (f_equal ts Hi)))) ].
      f_equal. apply (rew_map fin unfold_subterms_n).
    * refine (rew [InfiniteTerm.eq t1] _ in H0). simpl. unshelve eapply unfold_subterm_ext.
      f_equal. symmetry. apply Hi. simpl. admit. auto.
  - simpl. apply IHt.
Admitted.

Lemma unfold_subterm_surj {v} {t : mu_term v} (twf : wf t) (t' : infinite_term v)
                          (H : InfiniteTerm.subterm t' (unfold t twf))
                          : exists i, InfiniteTerm.eq t' (unfold_subterms t twf i).
Proof.
  specialize (unfold_subterm_surj_aux t twf t' H). intro. destruct H0 as [ i [ p [ q H0 ] ] ].
  destruct q. exists i. auto.
Qed.

Lemma unfold_regular {v} {t : mu_term v} (twf : wf t) : regular_term_p (unfold t twf).
Proof.
  exists (unfold_subterms_n t). exists (unfold_subterms _ twf). constructor.
  * intro. apply unfold_subterm_prop.
  * intros. apply unfold_subterm_surj. auto.
Qed.

End MuTerm.
