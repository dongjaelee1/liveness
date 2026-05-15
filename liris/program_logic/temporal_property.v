From iris.prelude Require Import options.
From liris.program_logic Require Export language.
From liris.prelude Require Import axioms.

(** Syntax for writing temporal formulae; cf., LTL, CTL*. *)
Inductive tp {Π : Type} :=
| tp_atomic (π : Π)
| tp_pure (p : Prop)
| tp_and (P Q : tp)
| tp_or (P Q : tp)
(** For impl and wnad, we only allow pure Prop in the left side.
    This makes the wand just an impl, so we omit the wand. *)
| tp_impl (P : Prop) (Q : tp)
| tp_forall (A : Type) (P : A → tp)
| tp_exist (A : Type) (P : A → tp)
| tp_always (P : tp)
| tp_until (P Q : tp)
.

Global Arguments tp : clear implicits.
Global Arguments tp {Π}.

(** Notations *)

Declare Scope tp_scope.
Delimit Scope tp_scope with P.
Bind Scope tp_scope with tp.

Notation "➢ π" := (tp_atomic π) (at level 50, π at level 1) : tp_scope.
Notation "'⌜' p '⌝'" := (tp_pure p) (at level 0, p at level 200) : tp_scope.
Infix "∧" := (tp_and) : tp_scope.
Infix "∨" := (tp_or) : tp_scope.
Infix "→" := (tp_impl) : tp_scope.
Notation f_forall A := (tp_forall A).
Notation "∀'" := (f_forall _) (only parsing) : tp_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%P)) ..)) : tp_scope.
Notation f_exist A := (tp_exist A).
Notation "∃'" := (f_exist _) (only parsing) : tp_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%P)) ..)) : tp_scope.

(** Define patterns corresponding to LTL temporal properties. *)
(* Eventually P *)
Definition tp_eventually {Π} (P : @tp Π) : tp :=
  (tp_until ⌜ True ⌝ P)%P.
Global Arguments tp_eventually {Π}.

(* P Weak until Q *)
Definition tp_weakuntil {Π} (P Q : @tp Π) : tp :=
  (tp_until P (Q ∨ tp_always P))%P.
Global Arguments tp_weakuntil {Π}.

(* P Release Q *)
Definition tp_release {Π} (P Q : @tp Π) : tp :=
  (tp_weakuntil Q (Q ∧ P))%P.
Global Arguments tp_release {Π}.

(* P Strong release Q *)
Definition tp_strongrelease {Π} (P Q : @tp Π) : tp :=
  (tp_until Q (Q ∧ P))%P.
Global Arguments tp_strongrelease {Π}.

Definition tp_true {Π} : @tp Π := ⌜ True ⌝%P.

(** Semantics. *)
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

(** TODO: better tactic for solving trProp implications. *)
Ltac unfold_trProp :=
  unfold tr_until, tr_always, tr_exist, tr_forall, tr_impl, tr_or, tr_and, tr_pure, tr_atomic.

(** Notations *)

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

Fixpoint tp_trace {Λ : language} (Φ : @tp (state_pred Λ)) : trProp Λ :=
  match Φ with
  | tp_atomic π => tr_atomic π
  | tp_pure p => (⌜p⌝)%R
  | tp_and P Q => (tp_trace P ∧ tp_trace Q)%R
  | tp_or P Q => (tp_trace P ∨ tp_trace Q)%R
  | tp_impl P Q => (P → tp_trace Q)%R
  | tp_forall A P => (∀ (a : A), tp_trace (P a))%R
  | tp_exist A P => (∃ (a : A), tp_trace (P a))%R
  | tp_always P => tr_always (tp_trace P)
  | tp_until P Q => tr_until (tp_trace P) (tp_trace Q)
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

Section fair_sched.
  Context {Λ : language}.

  Definition fscnt : Type := thread_id → nat.

  CoInductive beh_fscnt_th (τ : trace Λ) (i : thread_id) (c : nat) : Prop :=
  | beh_fscnt_th_step ρ j κs c' :
    (τ.2 τ.1) = (ρ, j, κs) →
    ((thread_na i τ) ∨ (thread_active i τ ∧ (if (decide (i = j)) then True else c' < c))) →
    beh_fscnt_th (trace_next τ) i c' →
    beh_fscnt_th τ i c.
  Definition beh_fscnt (τ : trace Λ) (γ : fscnt) : Prop :=
    ∀ (i : thread_id), beh_fscnt_th τ i (γ i).

  Lemma beh_fscnt_th_upto_le (τ : trace Λ) i (c1 c2 : nat) :
    beh_fscnt_th τ i c1 →
    c1 ≤ c2 →
    beh_fscnt_th τ i c2.
  Proof.
    intros BEH LEc. inv BEH.
    eapply (beh_fscnt_th_step _ _ _ _ _ _ c'). 1: eauto. 2: auto.
    destruct H0; auto. right. destruct H0. split; auto.
    destruct (decide (i = j)); auto. eapply Nat.lt_le_trans; eauto.
  Qed.

  (** We use choice here. *)
  Lemma fair_scheduling_fscnt (τ : trace Λ) :
    fair_scheduling τ → ∃ (γ : fscnt), beh_fscnt τ γ.
  Proof.
    intros FS. unfold beh_fscnt. apply choice. intros i. destruct τ as (n&τf).
    assert (∀ (s : nat), ((thread_na i (n, τf)) ∨ (thread_active i (n, τf) ∧ thread_turn i (s + n, τf)))
                       → beh_fscnt_th (n, τf) i s); cycle 1.
    { destruct (thread_active_or_not i (n, τf)) as [TH | TH].
      - exists 0. specialize (H 0). apply H. left. auto.
      - specialize (FS n). unshelve edestruct FS. 1: exact i. 1: lia.
        { exfalso. eapply (thread_active_and_not_false _ ((n, τf))); eauto. }
        destruct H0 as [TA TEV]. unfold tr_eventually, tr_until in TEV. destruct TEV as (m& LEm& TTurn& _).
        remember (m - n) as s. assert (m = s + n) by lia. subst m. clear Heqs LEm.
        exists s. apply H. right. auto. }
    revert n FS. cofix CIH; intros. destruct H as [TH | TH].
    - rename TH into TNA. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
      destruct (thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
      + econstructor. 1: eauto. 1: auto.
        unshelve eapply (CIH _ _ 0); auto. apply fair_scheduling_next. auto.
      + pose proof FS as FSn'. specialize (FSn' (S n)).
        unshelve edestruct FSn'. 1: exact i. 1: lia.
        { exfalso. eapply (thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
        destruct H as [TA TEV]. unfold tr_eventually, tr_until in TEV. destruct TEV as (m& LEm& TTurn& _).
        remember (m - (S n)) as s'. assert (m = s' + S n) by lia. subst m. clear Heqs' LEm.
        eapply (beh_fscnt_th_step _ _ _ _ _ _ s'). 1: eauto. 1: auto.
        eapply CIH.
        * apply fair_scheduling_next; auto.
        * right. eauto.
    - destruct TH as [TA TTurn]. destruct s.
      (* Induction on s breask Guarded check? *)
      { simpl in TTurn. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
        unfold thread_turn in TTurn. simpl in TTurn. rewrite Htrn in TTurn. subst j.
        destruct (thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
        - econstructor. 1: eauto.
          { right. split; auto. rewrite decide_True; auto. }
          unshelve eapply (CIH _ _ 0); eauto. eapply fair_scheduling_next; eauto.
        - pose proof FS as FSn'. specialize (FSn' (S n)).
          unshelve edestruct FSn'. 1: exact i. 1: lia.
          { exfalso. eapply (thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
          destruct H as [TA2 TEV2]. unfold tr_eventually, tr_until in TEV2. destruct TEV2 as (m& LEm& TTurn2& _).
          remember (m - (S n)) as s. assert (m = s + S n) by lia. subst m. clear Heqs LEm.
          eapply (beh_fscnt_th_step _ _ _ _ _ _ s). 1: eauto.
          { right. split; auto. rewrite decide_True; auto. }
          apply CIH; auto. apply fair_scheduling_next; auto. }
      { simpl in TTurn. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
        destruct (decide (j = i)).
        - subst j. destruct (thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
          + econstructor. 1: eauto.
            { right. split; auto. rewrite decide_True; auto. }
            unshelve eapply (CIH _ _ 0); eauto. eapply fair_scheduling_next; eauto.
          + pose proof FS as FSn'. specialize (FSn' (S n)).
            unshelve edestruct FSn'. 1: exact i. 1: lia.
            { exfalso. eapply (thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
            destruct H as [TA2 TEV2]. unfold tr_eventually, tr_until in TEV2. destruct TEV2 as (m& LEm& TTurn2& _).
            remember (m - (S n)) as s'. assert (m = s' + S n) by lia. subst m. clear Heqs' LEm.
            eapply (beh_fscnt_th_step _ _ _ _ _ _ s'). 1: eauto.
            { right. split; auto. rewrite decide_True; auto. }
            apply CIH; auto. apply fair_scheduling_next; auto.
        - eapply (beh_fscnt_th_step _ _ _ _ _ _ s). 1: eauto.
          { right. split; auto. rewrite decide_False; auto. }
          apply CIH; auto.
          + apply fair_scheduling_next; auto.
          + simpl. destruct (thread_active_or_not i (S n, τf)) as [? | TA2]; first auto.
            right. replace (s + S n) with (S (s + n)) by lia. split; auto. }
  Qed.

  Definition fscnt_next_rel_th (τ : trace Λ) i (c1 c2 : nat) : Prop :=
    if (decide (i = trace_thread τ)) then True
    else if (decide (thread_na i τ)) then True
         else (c2 < c1).
  Definition fscnt_next_rel (τ : trace Λ) (γ1 γ2 : fscnt) : Prop :=
    ∀ i, fscnt_next_rel_th τ i (γ1 i) (γ2 i).

  (** We again use choice here. *)
  Lemma exists_fscnt_next (τ : trace Λ) (γ : fscnt) :
    beh_fscnt τ γ →
    ∃ γ', beh_fscnt (trace_next τ) γ' ∧ fscnt_next_rel τ γ γ'.
  Proof.
    intros Beh. unfold beh_fscnt, fscnt_next_rel.
    cut (∃ γ', ∀ i, (λ i c, beh_fscnt_th (trace_next τ) i c ∧ fscnt_next_rel_th τ i (γ i) c) i (γ' i)).
    { intros. destruct H. exists x. split; intros; firstorder. }
    apply choice. intros i. specialize (Beh i). inv Beh.
    exists c'. split; auto. unfold fscnt_next_rel_th.
    destruct τ as (n&τf). unfold trace_thread, trace_state. simpl in *.
    rewrite H. simpl. destruct (decide (i = j)); auto. destruct H0.
    { rewrite decide_True; auto. }
    destruct H0. rewrite decide_False; auto.
    intros F. eapply thread_active_and_not_false; eauto.
  Qed.

End fair_sched.
