From iris.proofmode Require Import base classes proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import iprop.
From stdpp Require Import namespaces.
From liris.base_logic Require Import obligation.

(** Syntax for writing temporal formulae; cf., LTL, CTL*. *)
Inductive tf `{SI : indexT} `{Σ : gFunctors} {Π : Type} :=
| tf_emp
| tf_atomic (π : Π)
| tf_pure (p : Prop)
| tf_ghost (p : iProp Σ)
| tf_and (P Q : tf)
| tf_or (P Q : tf)
(** For impl and wand, we only allow pure Prop in the left side. *)
| tf_impl (P : Prop) (Q : tf)
| tf_forall (A : Type) (P : A → tf)
| tf_exist (A : Type) (P : A → tf)
| tf_sep (P Q : tf)
(** For impl and wand, we only allow pure Prop in the left side. *)
| tf_wand (P : Prop) (Q : tf)
| tf_pers (P : tf)
| tf_always (N : namespace) (k : oid) (P : tf)
| tf_until (N : namespace) (k : oid) (P Q : tf)
.

Global Arguments tf {SI Σ Π}.

(** Notations *)

Declare Scope tf_scope.
Delimit Scope tf_scope with F.
Bind Scope tf_scope with tf.

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
Notation "□ P" := (tf_pers P%F) : tf_scope.

(** Define patterns corresponding to LTL temporal properties. *)
(* Eventually P *)
Definition tf_eventually `{SI : indexT} {Σ} {Π} N k (P : @tf SI Σ Π) : tf :=
  (tf_until N k ⌜ True ⌝ P)%F.
Global Arguments tf_eventually {SI Σ Π}.

(* P Weak until Q *)
Definition tf_weakuntil `{SI : indexT} {Σ} {Π} N k (P Q : @tf SI Σ Π) : tf :=
  (tf_until N k P (Q ∨ ∃ k', tf_always N k' P))%F.
(*   (tf_variant N k v ⌜ False ⌝ P (tf_until N k (v + 1) P Q))%F. *)
Global Arguments tf_weakuntil {SI Σ Π}.

(* P Release Q *)
Definition tf_release `{SI : indexT} {Σ} {Π} N k (P Q : @tf SI Σ Π) : tf :=
  (tf_weakuntil N k Q (Q ∗ P))%F.
Global Arguments tf_release {SI Σ Π}.

(* P Strong release Q *)
Definition tf_strongrelease `{SI : indexT} {Σ} {Π} N k (P Q : @tf SI Σ Π) : tf :=
  (tf_until N k Q (Q ∗ P))%F.
Global Arguments tf_strongrelease {SI Σ Π}.
