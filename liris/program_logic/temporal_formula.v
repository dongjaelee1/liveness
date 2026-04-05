From iris.proofmode Require Import base classes proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import iprop.
From stdpp Require Import namespaces.
From liris.base_logic Require Import obligation.
(* From liris.prelude Require Import ordinal_facts. *)
From transfinite.stepindex Require Import ordinal_arith.

(** Syntax for writing temporal formulae; cf., LTL, CTL*. *)
Inductive tf `{SI : indexT} {Π : Type} `{Σ : gFunctors} :=
| tf_emp
| tf_atomic (π : Π)
| tf_pure (p : Prop)
| tf_ghost (p : iProp Σ)
| tf_and (P Q : tf)
| tf_or (P Q : tf)
(** For impl and wnad, we only allow pure Prop in the left side.
    This makes the wand just an impl, so we omit the wand. *)
| tf_impl (P : Prop) (Q : tf)
(* | tf_wand (P : Prop) (Q : tf) *)
| tf_forall (A : Type) (P : A → tf)
| tf_exist (A : Type) (P : A → tf)
| tf_sep (P Q : tf)
| tf_pers (P : tf)
| tf_always (N : namespace) (P : tf)
(** P until Q, using namespace N and oid k. *)
| tf_until (N : namespace) (k : oid) (b : bool) (q : Qp) (P Q : tf)
.

Global Arguments tf : clear implicits.
Global Arguments tf {SI Π}.

(** Notations *)

Declare Scope tf_scope.
Delimit Scope tf_scope with F.
Bind Scope tf_scope with tf.

Notation "➢ π" := (tf_atomic π) (at level 50, π at level 1) : tf_scope.
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
(* Infix "-∗" := (tf_wand) : tf_scope. *)
(* Notation "□ P" := (tf_pers P%F) : tf_scope. *)

(** Define patterns corresponding to LTL temporal properties. *)
(* Eventually P *)
Definition tf_eventually `{SI : indexT} {Π} {Σ} N k b q (P : @tf SI Π Σ) : tf Σ :=
  (tf_until N k b q ⌜ True ⌝ P)%F.
Global Arguments tf_eventually {SI Π Σ}.

(* P Weak until Q *)
Definition tf_weakuntil `{SI : indexT} {Π} {Σ} N k b q (P Q : @tf SI Π Σ) : tf Σ :=
  (tf_until N k b q P (Q ∨ tf_always N P))%F.
(*   (tf_variant N k v ⌜ False ⌝ P (tf_until N k (v + 1) P Q))%F. *)
Global Arguments tf_weakuntil {SI Π Σ}.

(* P Release Q *)
Definition tf_release `{SI : indexT} {Π} {Σ} N k b q (P Q : @tf SI Π Σ) : tf Σ :=
  (tf_weakuntil N k b q Q (Q ∗ P))%F.
Global Arguments tf_release {SI Π Σ}.

(* P Strong release Q *)
Definition tf_strongrelease `{SI : indexT} {Π} {Σ} N k b q (P Q : @tf SI Π Σ) : tf Σ :=
  (tf_until N k b q Q (Q ∗ P))%F.
Global Arguments tf_strongrelease {SI Π Σ}.
