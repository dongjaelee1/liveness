From iris.prelude Require Import options.
From lantana.program_logic Require Export language.
From lantana.algebra Require Import axioms.

(** * Trace predicates

    Properties of executions ([trProp]): the LTL connectives, their fixpoints, fair
    scheduling and Iris-style safety. *)

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

(** ** Trace entailment [R ⊆ S], and the laws of LTL

    Trace predicates are ordinary predicates on traces, so every valid law of LTL is
    provable from the definitions (classically). The laws below are the ones that proofs
    about exported properties use; all are entailments, so they compose by
    [transitivity]. *)
Definition tr_le {Λ : language} (R S : trProp Λ) : Prop := ∀ τ, R τ → S τ.
Global Instance tr_subseteq {Λ : language} : SubsetEq (trProp Λ) := tr_le.
Global Instance tr_le_preorder {Λ : language} : PreOrder (⊆@{trProp Λ}).
Proof. split; [by intros R τ|intros R S T HRS HST τ HR; by apply HST, HRS]. Qed.

(** Entailment is the validity of the implication: [⊆] is the meta-level [⊨] of LTL, [→] the
    connective. *)
Lemma tr_le_impl {Λ : language} (R S : trProp Λ) : R ⊆ S ↔ ∀ τ, (R → S)%R τ.
Proof. done. Qed.

Ltac tr_unfold :=
  unfold subseteq, tr_subseteq, tr_le, tr_next, tr_eventually, tr_until, tr_always, tr_exist,
    tr_forall, tr_impl, tr_or, tr_and, tr_pure, tr_state, ts_emb, ts_state, trace_now in *; simpl in *.

Section tr_laws.
  Context {Λ : language}.
  Implicit Types R S X : trProp Λ.

  (** Always: reflexive, transitive, monotone, distributes over [∧], and is the greatest
      fixpoint of [R ∧ ○ -] ([tr_always_coind]). *)
  Lemma tr_always_elim R : (□ R)%R ⊆ R.
  Proof. intros [n τf]. tr_unfold. intros H. apply H. lia. Qed.
  Lemma tr_always_next R : (□ R)%R ⊆ (○ □ R)%R.
  Proof. intros [n τf]. tr_unfold. intros H m Hm. apply H. lia. Qed.
  Lemma tr_always_idemp R : (□ R)%R ⊆ (□ □ R)%R.
  Proof. intros [n τf]. tr_unfold. intros H m Hm m' Hm'. apply H. lia. Qed.
  Lemma tr_always_mono R S : R ⊆ S → (□ R)%R ⊆ (□ S)%R.
  Proof. intros HRS [n τf]. tr_unfold. intros H m Hm. apply HRS, H. lia. Qed.
  Lemma tr_always_and R S : (□ (R ∧ S))%R ⊆ (□ R ∧ □ S)%R.
  Proof. intros [n τf]. tr_unfold. intros H. split; intros m Hm; by apply H. Qed.
  Lemma tr_and_always R S : (□ R ∧ □ S)%R ⊆ (□ (R ∧ S))%R.
  Proof. intros [n τf]. tr_unfold. intros [H1 H2] m Hm. auto. Qed.
  Lemma tr_always_impl R S : (□ (R → S) ∧ □ R)%R ⊆ (□ S)%R.
  Proof. intros [n τf]. tr_unfold. intros [H1 H2] m Hm. auto. Qed.
  Lemma tr_always_coind R X : X ⊆ (R ∧ ○ X)%R → X ⊆ (□ R)%R.
  Proof.
    intros HX [n τf]. tr_unfold. intros Hx m Hm.
    assert (∀ d n', X (n', τf) → R (n' + d, τf)) as Hd.
    { induction d as [|d IH]; intros n' Hn'.
      - rewrite Nat.add_0_r. by apply HX.
      - destruct (HX (n', τf) Hn') as [_ Hnext]. replace (n' + S d) with (S n' + d) by lia.
        apply IH. exact Hnext. }
    replace m with (n + (m - n)) by lia. by apply Hd.
  Qed.

  (** Until: the least fixpoint of [S ∨ (R ∧ ○ -)] ([tr_until_now], [tr_until_step],
      [tr_until_ind]), monotone, and stronger than finally. *)
  Lemma tr_until_now R S : S ⊆ tr_until R S.
  Proof. intros [n τf]. tr_unfold. intros H. exists n. split_and!; [lia|done|lia]. Qed.
  Lemma tr_until_step R S : (R ∧ ○ tr_until R S)%R ⊆ tr_until R S.
  Proof.
    intros [n τf]. tr_unfold. intros [HR (m & Hm & HS & HRs)]. exists m. split_and!; [lia|done|].
    intros l Hl. destruct (decide (l = n)) as [->|]; [done|apply HRs; lia].
  Qed.
  Lemma tr_until_unfold R S : tr_until R S ⊆ (S ∨ (R ∧ ○ tr_until R S))%R.
  Proof.
    intros [n τf]. tr_unfold. intros (m & Hm & HS & HRs).
    destruct (decide (m = n)) as [->|]; first by left.
    right. split; first (apply HRs; lia). exists m. split_and!; [lia|done|]. intros l Hl. apply HRs. lia.
  Qed.
  Lemma tr_until_ind R S X : S ⊆ X → (R ∧ ○ X)%R ⊆ X → tr_until R S ⊆ X.
  Proof.
    intros HS HR [n τf]. tr_unfold. intros (m & Hm & HSm & HRs).
    assert (∀ d n', n' + d = m → (∀ l, n' ≤ l < m → R (l, τf)) → X (n', τf)) as Hd.
    { induction d as [|d IH]; intros n' Hd HRs'.
      - rewrite Nat.add_0_r in Hd. subst. by apply HS.
      - apply HR. split; first (apply HRs'; lia).
        change (X (Datatypes.S n', τf)). apply IH; first lia. intros l Hl. apply HRs'. lia. }
    apply (Hd (m - n) n); [lia|exact HRs].
  Qed.
  Lemma tr_until_mono R R' S S' : R ⊆ R' → S ⊆ S' → tr_until R S ⊆ tr_until R' S'.
  Proof.
    intros HR HS [n τf]. tr_unfold. intros (m & Hm & HSm & HRs). exists m. split_and!; [lia|by apply HS|].
    intros l Hl. apply HR, HRs. lia.
  Qed.
  Lemma tr_until_finally R S : tr_until R S ⊆ (◇ S)%R.
  Proof. apply tr_until_mono; [by intros ?|done]. Qed.

  (** Finally. *)
  Lemma tr_finally_intro S : S ⊆ (◇ S)%R.
  Proof. apply tr_until_now. Qed.
  Lemma tr_finally_mono S S' : S ⊆ S' → (◇ S)%R ⊆ (◇ S')%R.
  Proof. intros HS. by apply tr_until_mono. Qed.
  Lemma tr_finally_idemp S : (◇ ◇ S)%R ⊆ (◇ S)%R.
  Proof.
    intros [n τf]. tr_unfold. intros (m & Hm & (m' & Hm' & HS & _) & _). exists m'. split_and!; [lia|done|done].
  Qed.
  Lemma tr_finally_or S S' : (◇ (S ∨ S'))%R ⊆ (◇ S ∨ ◇ S')%R.
  Proof.
    intros [n τf]. tr_unfold. intros (m & Hm & [HS|HS] & _); [left|right]; exists m; split_and!; done.
  Qed.
  Lemma tr_always_finally_resp R S : (□ (R → ◇ S) ∧ ◇ R)%R ⊆ (◇ S)%R.
  Proof.
    intros [n τf]. tr_unfold. intros [H (m & Hm & HR & _)].
    destruct (H m Hm HR) as (m' & Hm' & HS & _). exists m'. split_and!; [lia|done|done].
  Qed.
  Lemma tr_always_finally_mono R S : R ⊆ S → (□ ◇ R)%R ⊆ (□ ◇ S)%R.
  Proof. intros HRS. by apply tr_always_mono, tr_finally_mono. Qed.

  (** Duality: [□] and [◇] are each other's negation (classically). *)
  Lemma tr_not_finally R : (□ (R → ⌜False⌝))%R ⊆ (◇ R → ⌜False⌝)%R.
  Proof. intros [n τf]. tr_unfold. intros H (m & Hm & HR & _). by apply (H m). Qed.
  Lemma tr_not_always R : (◇ R → ⌜False⌝)%R ⊆ (□ (R → ⌜False⌝))%R.
  Proof. intros [n τf]. tr_unfold. intros H m Hm HR. apply H. exists m. split_and!; done. Qed.
  Lemma tr_not_always_finally R : (□ R → ⌜False⌝)%R ⊆ (◇ (R → ⌜False⌝))%R.
  Proof.
    intros [n τf]. tr_unfold. intros H.
    destruct (Classical_Prop.classic (∃ m, n ≤ m ∧ ¬ R (m, τf))) as [(m & Hm & HR)|Hno].
    - exists m. split_and!; done.
    - exfalso. apply H. intros m Hm. destruct (Classical_Prop.classic (R (m, τf))); [done|].
      exfalso. apply Hno. by exists m.
  Qed.
End tr_laws.

(** ** Fixpoints of trace predicates *)
Section tr_fixpoints.
  Context {Λ : language}.
  Implicit Types R : trProp Λ.
  Implicit Types Φ : trProp Λ → trProp Λ.

  Definition tr_mono Φ : Prop := ∀ R R', (∀ τ, R τ → R' τ) → ∀ τ, Φ R τ → Φ R' τ.
  Definition tr_gfp Φ : trProp Λ := λ τ, ∃ R, (∀ τ', R τ' → Φ R τ') ∧ R τ.
  Definition tr_lfp Φ : trProp Λ := λ τ, ∀ R, (∀ τ', Φ R τ' → R τ') → R τ.

  Lemma tr_gfp_coind Φ R : (∀ τ, R τ → Φ R τ) → ∀ τ, R τ → tr_gfp Φ τ.
  Proof. intros HR τ Hτ. by exists R. Qed.
  Lemma tr_gfp_unfold_l Φ : tr_mono Φ → ∀ τ, tr_gfp Φ τ → Φ (tr_gfp Φ) τ.
  Proof.
    intros Hm τ (R & HR & Hτ). eapply Hm; last by apply HR. intros τ' Hτ'. by exists R.
  Qed.
  Lemma tr_gfp_unfold_r Φ : tr_mono Φ → ∀ τ, Φ (tr_gfp Φ) τ → tr_gfp Φ τ.
  Proof.
    intros Hm τ Hτ. exists (Φ (tr_gfp Φ)). split; last done.
    intros τ' Hτ'. eapply Hm; [|exact Hτ']. by apply tr_gfp_unfold_l.
  Qed.

  Lemma tr_lfp_ind Φ R : (∀ τ, Φ R τ → R τ) → ∀ τ, tr_lfp Φ τ → R τ.
  Proof. intros HR τ H. by apply H. Qed.
  Lemma tr_lfp_unfold_r Φ : tr_mono Φ → ∀ τ, Φ (tr_lfp Φ) τ → tr_lfp Φ τ.
  Proof. intros Hm τ Hτ R HR. apply HR. eapply Hm; [|exact Hτ]. intros τ' H'. by apply H'. Qed.
  Lemma tr_lfp_unfold_l Φ : tr_mono Φ → ∀ τ, tr_lfp Φ τ → Φ (tr_lfp Φ) τ.
  Proof.
    intros Hm τ H. apply H. intros τ' H'. eapply Hm; [|exact H']. intros τ'' H''.
    by apply tr_lfp_unfold_r.
  Qed.
End tr_fixpoints.

(** ** Fair scheduling

    Every thread that is active is eventually scheduled. The fairness counter ([fscnt])
    bounds, for every thread, the steps of other threads until its next turn. *)

Definition thread_active {Λ : language} (i : thread_id) : tsProp Λ :=
  λ ξ, let '((Θ, σ), _, _) := ξ in ∃ e, Θ !! i = Some e ∧ to_val e = None.

Definition thread_na {Λ : language} (i : thread_id) : tsProp Λ :=
  λ ξ, let '((Θ, σ), _, _) := ξ in (Θ !! i = None ∨ ∃ e, Θ !! i = Some e ∧ is_Some (to_val e)).

Definition thread_turn {Λ : language} (i : thread_id) : tsProp Λ :=
  λ ξ, let '(_, j, _) := ξ in i = j.

Definition fair_scheduling {Λ : language} : trProp Λ :=
  tr_always (∀ i, (ts_emb (thread_na i)) ∨
                  ((ts_emb (thread_active i)) ∧ tr_eventually (ts_emb (thread_turn i))))%R.

Section thread_status.
  Context {Λ : language}.
  Implicit Type ξ : trace_state Λ.
  Implicit Type τ : trace Λ.

  Lemma fair_scheduling_next (τ : trace Λ) :
    fair_scheduling τ → fair_scheduling (trace_next τ).
  Proof.
    unfold fair_scheduling, tr_always. destruct τ as (n& τf). simpl. intros.
    specialize (H m). apply H. lia.
  Qed.

  Global Instance thread_na_decide i ξ : Decision (thread_na i ξ).
  Proof.
    unfold thread_na. destruct ξ as (((Θ& σ)& j)& κs) eqn:Htrn. destruct (Θ !! i) eqn:Hi.
    - destruct (to_val e) eqn:He.
      + left. right. eauto.
      + right. intros F. destruct F; first done. destruct H as (?&?&?). inv H. rewrite He in H0. done.
    - left. auto.
  Qed.

  Global Instance thread_active_decide i ξ : Decision (thread_active i ξ).
  Proof.
    unfold thread_active. destruct ξ as (((Θ& σ)& j)& κs) eqn:Htrn. destruct (Θ !! i) eqn:Hi.
    - destruct (to_val e) eqn:He.
      + right. intros F. destruct F as (?&?&?). inv H.
      + left. eauto.
    - right. intros F. destruct F as (?&?&?). inv H.
  Qed.

  Lemma thread_active_and_not_false i ξ : thread_na i ξ → thread_active i ξ → False.
  Proof.
    unfold thread_na, thread_active. destruct ξ as (((Θ& σ)& j)& κs) eqn:Htrn.
    intros. destruct (Θ !! i) eqn:LUi.
    + destruct (to_val e) eqn: EQe.
      * destruct H; [done |]. destruct H0 as (?&?&?). inv H0.
      * destruct H; [done |]. destruct H as (?&?&?). inv H. rewrite EQe in H1. done.
    + destruct H0 as (?&?&?). done.
  Qed.
  Lemma ts_emb_thread_active_and_not_false i τ :
    (ts_emb (thread_na i)) τ → (ts_emb (thread_active i)) τ → False.
  Proof.
    destruct τ as (n&τf). unfold ts_emb. simpl. apply thread_active_and_not_false.
  Qed.

  Lemma thread_active_or_not i ξ : thread_na i ξ ∨ thread_active i ξ.
  Proof.
    unfold thread_na, thread_active.
    destruct ξ as (((Θ& σ)& j)& κs) eqn:Htrn.
    destruct (Θ !! i) eqn:LUi; eauto.
    destruct (to_val e) eqn: EQe; eauto.
  Qed.
  Lemma ts_emb_thread_active_or_not i τ : (ts_emb (thread_na i)) τ ∨ (ts_emb (thread_active i)) τ.
  Proof.
    destruct τ as (n&τf). unfold ts_emb. simpl. apply thread_active_or_not.
  Qed.

End thread_status.

Section fair_sched_cnt.
  Context {Λ : language}.
  Implicit Type ξ : trace_state Λ.
  Implicit Type τ : trace Λ.

  Definition fscnt : Type := thread_id → nat.

  CoInductive beh_fscnt_th (τ : trace Λ) (i : thread_id) (c : nat) : Prop :=
  | beh_fscnt_th_step ξ j c' :
    j = trace_thread τ →
    ξ = trace_now τ →
    ((thread_na i ξ) ∨ (thread_active i ξ ∧ (if (decide (i = j)) then True else c' < c))) →
    beh_fscnt_th (trace_next τ) i c' →
    beh_fscnt_th τ i c.
  Definition beh_fscnt (τ : trace Λ) (γ : fscnt) : Prop :=
    ∀ (i : thread_id), beh_fscnt_th τ i (γ i).

  (** Uses choice. *)
  Lemma fair_scheduling_fscnt (τ : trace Λ) :
    fair_scheduling τ → ∃ (γ : fscnt), beh_fscnt τ γ.
  Proof.
    intros FS. unfold beh_fscnt. apply choice. intros i. destruct τ as (n&τf).
    assert (∀ (s : nat),
              (((ts_emb (thread_na i) (n, τf))) ∨
               ((ts_emb (thread_active i) (n, τf)) ∧ (ts_emb (thread_turn i) (s + n, τf))))
              → beh_fscnt_th (n, τf) i s); cycle 1.
    { destruct (ts_emb_thread_active_or_not i (n, τf)) as [TH | TH].
      - exists 0. specialize (H 0). apply H. left. auto.
      - specialize (FS n). unshelve edestruct FS. 1: exact i. 1: lia.
        { exfalso. eapply (ts_emb_thread_active_and_not_false _ ((n, τf))); eauto. }
        destruct H0 as [TA TEV]. unfold tr_eventually, tr_until in TEV. destruct TEV as (m& LEm& TTurn& _).
        remember (m - n) as s. assert (m = s + n) by lia. subst m. clear Heqs LEm.
        exists s. apply H. right. auto. }
    revert n FS. cofix CIH; intros. destruct H as [TH | TH].
    - rename TH into TNA. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
      destruct (ts_emb_thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
      + econstructor. 1,2: eauto. 1: auto.
        unshelve eapply (CIH _ _ 0); auto. apply fair_scheduling_next. auto.
      + pose proof FS as FSn'. specialize (FSn' (S n)).
        unshelve edestruct FSn'. 1: exact i. 1: lia.
        { exfalso. eapply (ts_emb_thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
        destruct H as [TA TEV]. unfold tr_eventually, tr_until in TEV. destruct TEV as (m& LEm& TTurn& _).
        remember (m - (S n)) as s'. assert (m = s' + S n) by lia. subst m. clear Heqs' LEm.
        eapply (beh_fscnt_th_step _ _ _ _ _ s'). 1,2: eauto. 1: auto.
        eapply CIH.
        * apply fair_scheduling_next; auto.
        * right. eauto.
    - destruct TH as [TA TTurn]. destruct s.
      (* A case split on [s], not an induction (which may break the guard condition). *)
      { simpl in TTurn. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
        unfold ts_emb, thread_turn in TTurn. simpl in TTurn. rewrite Htrn in TTurn. subst j.
        destruct (ts_emb_thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
        - econstructor. 1,2: eauto.
          { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_True; eauto. }
          unshelve eapply (CIH _ _ 0); eauto. eapply fair_scheduling_next; eauto.
        - pose proof FS as FSn'. specialize (FSn' (S n)).
          unshelve edestruct FSn'. 1: exact i. 1: lia.
          { exfalso. eapply (ts_emb_thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
          destruct H as [TA2 TEV2]. unfold tr_eventually, tr_until in TEV2. destruct TEV2 as (m& LEm& TTurn2& _).
          remember (m - (S n)) as s. assert (m = s + S n) by lia. subst m. clear Heqs LEm.
          eapply (beh_fscnt_th_step _ _ _ _ _ s). 1,2: eauto.
          { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_True; auto. }
          apply CIH; auto. apply fair_scheduling_next; auto. }
      { simpl in TTurn. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
        destruct (decide (j = i)).
        - subst j. destruct (ts_emb_thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
          + econstructor. 1,2: eauto.
            { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_True; auto. }
            unshelve eapply (CIH _ _ 0); eauto. eapply fair_scheduling_next; eauto.
          + pose proof FS as FSn'. specialize (FSn' (S n)).
            unshelve edestruct FSn'. 1: exact i. 1: lia.
            { exfalso. eapply (ts_emb_thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
            destruct H as [TA2 TEV2]. unfold tr_eventually, tr_until in TEV2. destruct TEV2 as (m& LEm& TTurn2& _).
            remember (m - (S n)) as s'. assert (m = s' + S n) by lia. subst m. clear Heqs' LEm.
            eapply (beh_fscnt_th_step _ _ _ _ _ s'). 1,2: eauto.
            { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_True; auto. }
            apply CIH; auto. apply fair_scheduling_next; auto.
        - eapply (beh_fscnt_th_step _ _ _ _ _ s). 1,2: eauto.
          { right. split; auto. unfold trace_thread. simpl. rewrite Htrn. rewrite decide_False; auto. }
          apply CIH; auto.
          + apply fair_scheduling_next; auto.
          + simpl. destruct (ts_emb_thread_active_or_not i (S n, τf)) as [? | TA2]; first auto.
            right. replace (s + S n) with (S (s + n)) by lia. split; auto. }
  Qed.

  Definition fscnt_next_rel_th (τ : trace Λ) i (c1 c2 : nat) : Prop :=
    if (decide (i = trace_thread τ)) then True
    else if (decide (thread_na i (trace_now τ))) then True
         else (c2 < c1).
  Definition fscnt_next_rel (τ : trace Λ) (γ1 γ2 : fscnt) : Prop :=
    ∀ i, fscnt_next_rel_th τ i (γ1 i) (γ2 i).

  (** Uses choice. *)
  Lemma exists_fscnt_next (τ : trace Λ) (γ : fscnt) :
    beh_fscnt τ γ →
    ∃ γ', beh_fscnt (trace_next τ) γ' ∧ fscnt_next_rel τ γ γ'.
  Proof.
    intros Beh. unfold beh_fscnt, fscnt_next_rel.
    cut (∃ γ', ∀ i, (λ i c, beh_fscnt_th (trace_next τ) i c ∧ fscnt_next_rel_th τ i (γ i) c) i (γ' i)).
    { intros. destruct H. exists x. split; intros; firstorder. }
    apply choice. intros i. specialize (Beh i). inv Beh.
    exists c'. split; auto. unfold fscnt_next_rel_th.
    destruct τ as (n&τf). unfold trace_thread, trace_now. simpl in *.
    destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn. simpl.
    destruct (decide (i = j)); auto. destruct H1.
    { rewrite decide_True; auto. }
    destruct H.
    rewrite /trace_thread /trace_now in H0. simpl in H0. rewrite Htrn in H0. simpl in H0.
    rewrite decide_False in H0; auto.
    rewrite decide_False; auto.
    intros F. eapply thread_active_and_not_false; by eauto.
  Qed.

End fair_sched_cnt.

(** ** Iris-style safety

    The scheduled thread is not stuck, and a terminated thread [i] satisfies its
    postcondition. This [not_stuck] (a [tsProp]) shadows [language.not_stuck]. *)
Definition not_stuck {Λ : language} : tsProp Λ :=
  λ ξ, let '((Θ, σ), i, _) := ξ in
       ∃ e, Θ !! i = Some e ∧
            match to_val e with
            | Some _ => True
            | None => reducible i e σ (dom Θ)
            end.

Definition if_term_val {Λ : language} (i : thread_id) (Φ : thread_id → val Λ → Prop) : tsProp Λ :=
  λ ξ, let '((Θ, _), j, _) := ξ in
       if (decide (i = j))
       then ∃ e, Θ !! j = Some e ∧
                 match (to_val e) with
                 | Some v => Φ i v
                 | None => True
                 end
       else True.

Definition safety_iris {Λ : language} (i : thread_id) (Φ : thread_id → val Λ → Prop) : trProp Λ :=
  tr_always (ts_emb (not_stuck) ∧ ts_emb (if_term_val i Φ))%R.
