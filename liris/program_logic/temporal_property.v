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
  | tf_pers P => (⌜ True ⌝)%R
  | tf_always N P => tr_always (tf_trace P)
  | tf_until N k b q P Q => tr_until (tf_trace P) (tf_trace Q)
  end.

(** Define fair scheduling as a property of a trace. *)
Definition tr_eventually {Λ : language} : trProp Λ → trProp Λ :=
  λ Q, tr_until (⌜ True ⌝)%R Q.

(* These might be expressible using tr_atomic, with some appropriate state_sat.
   But this definition is only used in the adequacy, so we leave it specific for now. *)
Definition thread_active {Λ : language} (i : thread_id) : trProp Λ :=
  λ τ, let '((Θ, σ), _, _) := (τ.2 τ.1) in ∃ e, Θ !! i = Some e ∧ to_val e = None.

Definition thread_na {Λ : language} (i : thread_id) : trProp Λ :=
  λ τ, let '((Θ, σ), _, _) := (τ.2 τ.1) in (Θ !! i = None ∨ ∃ e, Θ !! i = Some e ∧ is_Some (to_val e)).

Definition thread_turn {Λ : language} (i : thread_id) : trProp Λ :=
  λ τ, let '(_, j, _) := (τ.2 τ.1) in i = j.

Definition fair_scheduling {Λ : language} : trProp Λ :=
  tr_always (∀ i, (thread_na i) ∨ (thread_active i ∧ tr_eventually (thread_turn i)))%R.

Section proof.
  Context {Λ : language}.

  Lemma fair_scheduling_next (τ : trace Λ) :
    fair_scheduling τ → fair_scheduling (trace_next τ).
  Proof.
    unfold fair_scheduling, tr_always. destruct τ as (n& τf). simpl. intros.
    specialize (H m). apply H. lia.
  Qed.

  Global Instance thread_na_decide i (τ : trace Λ) : Decision (thread_na i τ).
  Proof.
    unfold thread_na. destruct τ as (n& τf). simpl.
    destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn. destruct (Θ !! i) eqn:Hi.
    - destruct (to_val e) eqn:He.
      + left. right. eauto.
      + right. intros F. destruct F; first done. destruct H as (?&?&?). inv H. rewrite He in H0. done.
    - left. auto.
  Qed.

  Global Instance thread_active_decide i (τ : trace Λ) : Decision (thread_active i τ).
  Proof.
    unfold thread_active. destruct τ as (n& τf). simpl.
    destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn. destruct (Θ !! i) eqn:Hi.
    - destruct (to_val e) eqn:He.
      + right. intros F. destruct F as (?&?&?). inv H.
      + left. eauto.
    - right. intros F. destruct F as (?&?&?). inv H.
  Qed.

  Lemma thread_active_and_not_false i (τ : trace Λ) : thread_na i τ → thread_active i τ → False.
  Proof.
    destruct τ as (n&τf). unfold thread_na, thread_active.
    destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn. simpl. rewrite Htrn.
    intros. destruct (Θ !! i) eqn:LUi.
    + destruct (to_val e) eqn: EQe.
      * destruct H; [done |]. destruct H0 as (?&?&?). inv H0.
      * destruct H; [done |]. destruct H as (?&?&?). inv H. rewrite EQe in H1. done.
    + destruct H0 as (?&?&?). done.
  Qed.

  Lemma thread_active_or_not i (τ : trace Λ) : thread_na i τ ∨ thread_active i τ.
  Proof.
    destruct τ as (n&τf). unfold thread_na, thread_active.
    destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn. simpl. rewrite Htrn.
    destruct (Θ !! i) eqn:LUi; eauto.
    destruct (to_val e) eqn: EQe; eauto.
  Qed.

End proof.
