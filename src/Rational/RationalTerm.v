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

Instance inf_term_eq_equiv : RelationClasses.Equivalence inf_term_eq :=
  RelationClasses.Build_Equivalence _ _ _ _.

Definition inf_subterm (l r : inf_term) := exists p, inf_path_to l p r.

Definition is_rational_term (t : inf_term) :=
  exists ts, forall l, inf_subterm t l -> exists r, inf_term_eq l r /\ List.In r ts.
