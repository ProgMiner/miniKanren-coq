

Definition option_pure [A : Set] (x : A) : option A := Some x.

Definition option_bind [A B : Set] (k : A -> option B) (x : option A) : option B :=
  option_rec (fun _ => option B) k None x.

Lemma option_bind_pure {A B : Set} (k : A -> option B) (x : A)
                       : option_bind k (option_pure x) = k x.
Proof. reflexivity. Qed.

Lemma option_pure_bind {A B : Set} (k : A -> option B) (x : option A)
                       : option_bind (option_pure (A:=A)) x = x.
Proof. destruct x; reflexivity. Qed.

Lemma option_bind_assoc {A B C : Set} (k1 : A -> option B) (k2 : B -> option C) (x : option A)
                        : option_bind k2 (option_bind k1 x)
                        = option_bind (fun x => option_bind k2 (k1 x)) x.
Proof. destruct x; reflexivity. Qed.
