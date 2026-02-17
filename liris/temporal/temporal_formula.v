From iris.proofmode Require Import base classes.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export iprop.
From stdpp Require Import namespaces.
From liris.base_logic Require Import ghost_lock.

(** Simple syntax for writing temporal formulae; cf., LTL, CTL*. *)
Inductive tf `{SI : indexT} `{Σ : gFunctors} {Π : Type} :=
| tf_emp
| tf_atomic (π : Π)
| tf_pure (p : Prop)
| tf_ghost (p : iProp Σ)
| tf_and (P Q : tf)
| tf_or (P Q : tf)
| tf_impl (P Q : tf)
| tf_forall (A : Type) (P : A → tf)
| tf_exist (A : Type) (P : A → tf)
| tf_sep (P Q : tf)
| tf_wand (P Q : tf)
| tf_variant (N : namespace) (k : gl_id) (v : ghost_lock_version) (P Q R : tf).

Global Arguments tf {SI Σ Π}.

(** Notations *)

Declare Scope tf_scope.
Delimit Scope tf_scope with F.
Bind Scope tf_scope with tf.

(* Local Open Scope tf_scope. *)

Notation "'⌜' p '⌝'" := (tf_pure p) : tf_scope.
Notation "'⟨' p '⟩'" := (tf_ghost p%I) : tf_scope.
Infix "∧" := (tf_and) : tf_scope.
Infix "∨" := (tf_or) : tf_scope.
Infix "→" := (tf_impl) : tf_scope.
Notation f_forall A := (tf_forall A).
Notation "∀'" := (f_forall _) (only parsing) : tf_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%F)) ..)) : tf_scope.
Notation f_exist A := (tf_exist A).
Notation "∃'" := (f_exist _) (only parsing) : tf_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%F)) ..)) : tf_scope.
Infix "∗" := (tf_sep) : tf_scope.
Infix "-∗" := (tf_wand) : tf_scope.

(* Notation "'⟨' A '⟩'" := (Syntax.atom A) : tf_scope. *)
(* Notation "'➢' r" := (Syntax.ownM r) (at level 20) : tf_scope. *)
(* Notation "⤉ P" := (Syntax.lift P) (at level 20) : tf_scope. *)

(* Notation "'<pers>' P" := (Syntax.persistently P) : tf_scope. *)
(* Notation "'<affine>' P" := (Syntax.affinely P) : tf_scope. *)
(* Notation "□ P" := (<affine> <pers> P) : tf_scope. *)
(* Notation "■ P" := (Syntax.plainly P) : tf_scope. *)
(* Notation "|==> P" := (Syntax.upd P) : tf_scope. *)
(* Notation "¬ P" := (P → False) : tf_scope. *)
(* Notation "P ==∗ Q" := (P -∗ |==> Q) : tf_scope. *)
(* Notation "'emp'" := (Syntax.empty) : tf_scope. *)

(* FIXME: more to somewhere else. *)
Section aux.
  Context `{SI : indexT}.

  Global Instance big_opL_proper_eq {M : ofe} (o : M → M → M) `{!Monoid o} {A : Type} :
    Proper (pointwise_relation nat (pointwise_relation A eq) ==> eq ==> eq) (big_opL o).
  Proof.
    repeat intro. subst y0. revert x y H. rename x0 into l. induction l; intros f1 f2 Hf; simpl; auto.
    f_equal.
    - rewrite Hf. auto.
    - eapply IHl. repeat intro. rewrite Hf. auto.
  Qed.

End aux.

(** Define some useful patterns corresponding to temporal properties. *)
(* Always P *)
Local Definition tf_always_def `{SI : indexT} Σ Π N k v (P : @tf SI Σ Π) : tf :=
  (tf_variant N k v ⌜ False ⌝ P ⌜ False ⌝)%F.
Local Definition tf_always_aux : seal (@tf_always_def). Proof. by eexists. Qed.
Definition tf_always := tf_always_aux.(unseal).
Local Definition tf_always_unseal :
  @tf_always = @tf_always_def := tf_always_aux.(seal_eq).
Global Arguments tf_always {SI Σ Π}.

(* P Until Q *)
Local Definition tf_until_def `{SI : indexT} Σ Π N k v (P Q : @tf SI Σ Π) : tf :=
  (tf_variant N k v P Q ⌜ True ⌝)%F.
Local Definition tf_until_aux : seal (@tf_until_def). Proof. by eexists. Qed.
Definition tf_until := tf_until_aux.(unseal).
Local Definition tf_until_unseal :
  @tf_until = @tf_until_def := tf_until_aux.(seal_eq).
Global Arguments tf_until {SI Σ Π}.

(* Eventually P *)
Local Definition tf_eventually_def `{SI : indexT} Σ Π N k v (P : @tf SI Σ Π) : tf :=
  (tf_until N k v ⌜ True ⌝ P)%F.
Local Definition tf_eventually_aux : seal (@tf_eventually_def). Proof. by eexists. Qed.
Definition tf_eventually := tf_eventually_aux.(unseal).
Local Definition tf_eventually_unseal :
  @tf_eventually = @tf_eventually_def := tf_eventually_aux.(seal_eq).
Global Arguments tf_eventually {SI Σ Π}.

(* P Weak until Q *)
Local Definition tf_weakuntil_def `{SI : indexT} Σ Π N k v (P Q : @tf SI Σ Π) : tf :=
  (tf_until N k v P (Q ∨ ∃ k v, tf_always N k v P))%F.
  (* (tf_variant N k v ⌜ False ⌝ P (tf_until N k (v + 1) P Q))%F. *)
Local Definition tf_weakuntil_aux : seal (@tf_weakuntil_def). Proof. by eexists. Qed.
Definition tf_weakuntil := tf_weakuntil_aux.(unseal).
Local Definition tf_weakuntil_unseal :
  @tf_weakuntil = @tf_weakuntil_def := tf_weakuntil_aux.(seal_eq).
Global Arguments tf_weakuntil {SI Σ Π}.

(* P Release Q *)
Local Definition tf_release_def `{SI : indexT} Σ Π N k v (P Q : @tf SI Σ Π) : tf :=
  (tf_weakuntil N k v Q (Q ∗ P))%F.
Local Definition tf_release_aux : seal (@tf_release_def). Proof. by eexists. Qed.
Definition tf_release := tf_release_aux.(unseal).
Local Definition tf_release_unseal :
  @tf_release = @tf_release_def := tf_release_aux.(seal_eq).
Global Arguments tf_release {SI Σ Π}.

(* P Strong release Q *)
Local Definition tf_strongrelease_def `{SI : indexT} Σ Π N k v (P Q : @tf SI Σ Π) : tf :=
  (tf_until N k v Q (Q ∗ P))%F.
Local Definition tf_strongrelease_aux : seal (@tf_strongrelease_def). Proof. by eexists. Qed.
Definition tf_strongrelease := tf_strongrelease_aux.(unseal).
Local Definition tf_strongrelease_unseal :
  @tf_strongrelease = @tf_strongrelease_def := tf_strongrelease_aux.(seal_eq).
Global Arguments tf_strongrelease {SI Σ Π}.
