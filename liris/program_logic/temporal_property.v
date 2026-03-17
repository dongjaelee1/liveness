From iris.prelude Require Import options.
From liris.program_logic Require Export temporal_formula language weakestpre.

Definition trProp (Λ : language) : Type := trace Λ → Prop.

Definition tr_atomic {Λ : language} (π : state_pred Λ) : trProp Λ :=
  λ τ, let '((Θ, σ), _, _) := (τ.2 τ.1) in state_sat σ Θ π.

Definition tr_pure {Λ : language} (P : Prop) : trProp Λ :=
  λ _, P.

Definition tr_and {Λ : language} : trProp Λ → trProp Λ → trProp Λ :=
  λ P Q, (λ τ, (P τ) ∧ (Q τ)).

Definition tr_or {Λ : language} : trProp Λ → trProp Λ → trProp Λ :=
  λ P Q, (λ τ, (P τ) ∨ (Q τ)).

Definition tr_impl {Λ : language} : Prop → trProp Λ → trProp Λ :=
  λ P Q, (λ τ, P → (Q τ)).

Definition tr_forall {Λ : language} : ∀ (A : Type), (A → trProp Λ) → trProp Λ :=
  λ A P, (λ τ, ∀ (a : A), (P a τ)).

Definition tr_exist {Λ : language} : ∀ (A : Type), (A → trProp Λ) → trProp Λ :=
  λ A P, (λ τ, ∃ (a : A), (P a τ)).

Definition tr_always {Λ : language} : trProp Λ → trProp Λ :=
  λ P, (λ τ, let '(n, τf) := τ in ∀ m, (n ≤ m) → (P (m, τf))).

Definition tr_until {Λ : language} : trProp Λ → trProp Λ → trProp Λ :=
  λ P Q, (λ τ, let '(n, τf) := τ in ∃ m, (n ≤ m) ∧ (Q (m, τf)) ∧ (∀ l, (n ≤ l < m) → (P (l, τf)))).

(** Notations *)

Declare Scope tr_scope.
Delimit Scope tr_scope with R.

Notation "'⌜' p '⌝'" := (tr_pure p) : tr_scope.
Infix "∧" := (tr_and) : tr_scope.
Infix "∨" := (tr_or) : tr_scope.
Infix "→" := (tr_impl) : tr_scope.
Notation r_forall A := (tr_forall A).
Notation "∀'" := (r_forall _) (only parsing) : tr_scope.
Notation "∀ a .. z , P" := (r_forall _ (λ a, .. (r_forall _ (λ z, P%R)) ..)) : tr_scope.
Notation r_exist A := (tr_exist A).
Notation "∃'" := (r_exist _) (only parsing) : tr_scope.
Notation "∃ a .. z , P" := (r_exist _ (λ a, .. (r_exist _ (λ z, P%R)) ..)) : tr_scope.

Fixpoint tf_trace `{SI : indexT} `{!lirisGS Λ Σ}
  (Φ : @tf SI Σ (state_pred Λ)) : trProp Λ :=
  match Φ with
  | tf_emp => (⌜ True ⌝)%R
  | tf_atomic π => tr_atomic π
  | tf_pure p => (⌜p⌝)%R
  | tf_ghost p => (⌜ True ⌝)%R
  | tf_and P Q => (tf_trace P ∧ tf_trace Q)%R
  | tf_or P Q => (tf_trace P ∨ tf_trace Q)%R
  | tf_impl P Q => (P → tf_trace Q)%R
  | tf_forall A P => (∀ (a : A), tf_trace (P a))%R
  | tf_exist A P => (∃ (a : A), tf_trace (P a))%R
  | tf_sep P Q => (tf_trace P ∧ tf_trace Q)%R
  | tf_always N P => tr_always (tf_trace P)
  | tf_until N k b q P Q => tr_until (tf_trace P) (tf_trace Q)
  end.
