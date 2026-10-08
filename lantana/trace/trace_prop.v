From iris.prelude Require Import options.
From lantana.program_logic Require Export language.
From lantana.prelude Require Import axioms.

(** * Trace predicates

    Properties of executions ([trProp]): the LTL connectives, entailment [⊆] and fixpoints.
    The rules are in trace_prop_rules.v; fair scheduling is in fair_scheduling.v. *)

(** ** Predicates on a trace state and on a trace *)
Definition tsProp (Λ : language) := trace_state Λ → Prop.

(** A predicate on the configuration (state and thread pool) of a trace state. *)
Definition ts_state {Λ : language} (φ : state Λ → thread_pool Λ → Prop) : tsProp Λ :=
  λ ξ, let '((Θ, σ), _, _) := ξ in φ σ Θ.

Definition trProp (Λ : language) : Type := trace Λ → Prop.

Definition ts_emb {Λ : language} : tsProp Λ → trProp Λ :=
  λ P τ, P (trace_now τ).

Definition tr_state {Λ : language} (φ : state Λ → thread_pool Λ → Prop) : trProp Λ :=
  ts_emb (ts_state φ).

Definition tr_pure {Λ : language} (P : Prop) : trProp Λ :=
  λ _, P.

Definition tr_and {Λ : language} : trProp Λ → trProp Λ → trProp Λ :=
  λ P Q, (λ τ, (P τ) ∧ (Q τ)).

Definition tr_or {Λ : language} : trProp Λ → trProp Λ → trProp Λ :=
  λ P Q, (λ τ, (P τ) ∨ (Q τ)).

Definition tr_impl {Λ : language} : trProp Λ → trProp Λ → trProp Λ :=
  λ P Q, (λ τ, P τ → (Q τ)).

Definition tr_forall {Λ : language} : ∀ (A : Type), (A → trProp Λ) → trProp Λ :=
  λ A P, (λ τ, ∀ (a : A), (P a τ)).

Definition tr_exist {Λ : language} : ∀ (A : Type), (A → trProp Λ) → trProp Λ :=
  λ A P, (λ τ, ∃ (a : A), (P a τ)).

Definition tr_always {Λ : language} : trProp Λ → trProp Λ :=
  λ P, (λ τ, let '(n, τf) := τ in ∀ m, (n ≤ m) → (P (m, τf))).

Definition tr_until {Λ : language} : trProp Λ → trProp Λ → trProp Λ :=
  λ P Q, (λ τ, let '(n, τf) := τ in ∃ m, (n ≤ m) ∧ (Q (m, τf)) ∧ (∀ l, (n ≤ l < m) → (P (l, τf)))).

Global Instance ts_emb_decide {Λ : language} (P : tsProp Λ) :
  (∀ ξ, Decision (P ξ)) → ∀ τ, Decision (ts_emb P τ).
Proof.
  intros. unfold ts_emb. destruct τ as (n& τf). simpl. eauto.
Qed.

Ltac unfold_trProp :=
  unfold tr_until, tr_always, tr_exist, tr_forall, tr_impl, tr_or, tr_and, tr_pure, tr_state.

(** ** Notations *)

Declare Scope tr_scope.
Delimit Scope tr_scope with R.

Notation "'⌜' p '⌝'" := (tr_pure p) (at level 0, p at level 200) : tr_scope.
Infix "∧" := (tr_and) : tr_scope.
Infix "∨" := (tr_or) : tr_scope.
Infix "→" := (tr_impl) : tr_scope.
Notation r_forall A := (tr_forall A).
Notation "∀'" := (r_forall _) (only parsing) : tr_scope.
Notation "∀ a .. z , P" := (r_forall _ (λ a, .. (r_forall _ (λ z, P%R)) ..)) : tr_scope.
Notation r_exist A := (tr_exist A).
Notation "∃'" := (r_exist _) (only parsing) : tr_scope.
Notation "∃ a .. z , P" := (r_exist _ (λ a, .. (r_exist _ (λ z, P%R)) ..)) : tr_scope.

Definition tr_eventually {Λ : language} : trProp Λ → trProp Λ :=
  λ Q, tr_until (⌜ True ⌝)%R Q.

(** The next position. *)
Definition tr_next {Λ : language} : trProp Λ → trProp Λ :=
  λ P τ, P (trace_next τ).

Notation "□ P" := (tr_always P) (at level 20, right associativity) : tr_scope.
Notation "◇ P" := (tr_eventually P) (at level 20, right associativity) : tr_scope.
Notation "○ P" := (tr_next P) (at level 20, right associativity) : tr_scope.
Notation "P 'Uₜ' Q" := (tr_until P Q) (at level 60, right associativity) : tr_scope.

(** ** Trace entailment [R ⊆ S]: the validity of [R → S] ([⊆] is LTL's [⊨], [→] its
    connective). *)
Definition tr_le {Λ : language} (R S : trProp Λ) : Prop := ∀ τ, R τ → S τ.
Global Instance tr_subseteq {Λ : language} : SubsetEq (trProp Λ) := tr_le.
Lemma tr_le_impl {Λ : language} (R S : trProp Λ) : R ⊆ S ↔ ∀ τ, (R → S)%R τ.
Proof. done. Qed.

(** ** Fixpoints of trace predicates *)
Section tr_fixpoints.
  Context {Λ : language}.
  Implicit Types R : trProp Λ.
  Implicit Types Φ : trProp Λ → trProp Λ.

  Definition tr_mono Φ : Prop := ∀ R R', (∀ τ, R τ → R' τ) → ∀ τ, Φ R τ → Φ R' τ.
  Definition tr_gfp Φ : trProp Λ := λ τ, ∃ R, (∀ τ', R τ' → Φ R τ') ∧ R τ.
  Definition tr_lfp Φ : trProp Λ := λ τ, ∀ R, (∀ τ', Φ R τ' → R τ') → R τ.

End tr_fixpoints.
