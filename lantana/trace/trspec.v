From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export triprop.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.

(** * Trace specifications

    A [trSpec] is a trace property ([trProp], its external reading) with its
    internalization in the logic ([trIProp], its internal reading), adequate for it: if the
    internal reading is satisfiable, the external one holds. This file defines the
    connectives, the state atoms, and complete and instant properties; the rules are in
    trspec_rules.v, the model in trspec_model.v. *)

(** ** Definition *)

(** [trSpec_internal]: the step-indexed reading, which the run establishes;
    [trSpec_adeq]: its satisfiability implies the external reading. *)
Record trSpec {Λ : language} {Σ : gFunctors} := TrSpec {
  trSpec_internal : ∀ `{!temporalGS Λ Σ}, trace Λ → iProp Σ;
  trSpec_external : trProp Λ;
  trSpec_adeq : ∀ `{!temporalGS Λ Σ} (F : iProp Σ) (τ : trace Λ),
    iProp_sat_lc_at_frame F ⊤ (trSpec_internal τ) → trSpec_external τ;
}.
Global Arguments trSpec Λ Σ : clear implicits.
Global Arguments TrSpec {Λ Σ}.
Global Arguments trSpec_internal {Λ Σ} _ {_}.
Global Arguments trSpec_external {Λ Σ}.

Declare Scope trSpec_scope.
Delimit Scope trSpec_scope with SPEC.
Bind Scope trSpec_scope with trSpec.

(** In-logic entailment [G ⊑ G']: the internal reading of [G] implies that of [G']. *)
Definition trSpec_le {Λ Σ} (G G' : trSpec Λ Σ) : Prop :=
  ∀ (H : temporalGS Λ Σ) τ, @trSpec_internal _ _ G H τ ⊢ @trSpec_internal _ _ G' H τ.

Section trSpec_connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : trSpec Λ Σ.

  Program Definition trSpec_pure (p : Prop) : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_pure p; trSpec_external := tr_pure p |}.
  Next Obligation. intros p ? F τ H. by apply sat_elim in H. Qed.

  Definition trSpec_true : trSpec Λ Σ := trSpec_pure True.

  Program Definition trSpec_and G1 G2 : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_and (trSpec_internal G1) (trSpec_internal G2); trSpec_external := tr_and (trSpec_external G1) (trSpec_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold trI_and in H. apply iProp_sat_lc_at_frame_and in H as [H1 H2].
    split; [eapply trSpec_adeq, H1|eapply trSpec_adeq, H2].
  Qed.

  Program Definition trSpec_or G1 G2 : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_or (trSpec_internal G1) (trSpec_internal G2); trSpec_external := tr_or (trSpec_external G1) (trSpec_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold trI_or in H. apply sat_or in H as [H|H].
    - left. by eapply trSpec_adeq.
    - right. by eapply trSpec_adeq.
  Qed.

  (** Implication, with any trace property as antecedent: both readings assume it at the
      level of traces. *)
  Program Definition trSpec_impl (A G : trSpec Λ Σ) : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_impl (trSpec_external A) (trSpec_internal G); trSpec_external := tr_impl (trSpec_external A) (trSpec_external G) |}.
  Next Obligation.
    intros A G ? F τ H HA. unfold trI_impl in H. eapply trSpec_adeq. eapply sat_impl; [apply H|].
    iIntros "_". by iPureIntro.
  Qed.

  (** Over any type: [sat] commutes with [∀]. *)
  Program Definition trSpec_forall {X : Type} (G : X → trSpec Λ Σ) : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_forall X (λ x, trSpec_internal (G x)); trSpec_external := tr_forall X (λ x, trSpec_external (G x)) |}.
  Next Obligation.
    intros X G ? F τ H x. unfold trI_forall in H. eapply trSpec_adeq. by apply (sat_forall x) in H.
  Qed.

  (** Existential quantification needs the existential property of the step index, so only
      types smaller than the ordinals of [ordI] qualify (nat, gnames, oids, Ord.t, ...). *)
  Program Definition trSpec_exist {X : Type} `{!TypeExistentialProperty X ordI} (G : X → trSpec Λ Σ) : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_exist X (λ x, trSpec_internal (G x)); trSpec_external := tr_exist X (λ x, trSpec_external (G x)) |}.
  Next Obligation.
    intros X ? G ? F τ H. unfold trI_exist in H. apply sat_exists in H as [x H].
    exists x. by eapply trSpec_adeq.
  Qed.

  Program Definition trSpec_always G : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_always (trSpec_internal G) (trI_pure True); trSpec_external := tr_always (trSpec_external G) |}.
  Next Obligation.
    intros G ? F τ H.
    cut (tr_always (trSpec_external G ∧ tr_pure True)%R τ).
    { unfold tr_always. destruct τ. intros Hτ m Hm. by destruct (Hτ m Hm). }
    eapply (trI_always_tr_always F (trSpec_internal G) (trI_pure True) (trSpec_external G) (tr_pure True));
      [intros; by eapply trSpec_adeq | intros; exact I | exact H].
  Qed.

  Program Definition trSpec_until G1 G2 : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_exist Ord.t (λ a, trI_until Ord.lt a (trSpec_internal G1) (trSpec_internal G2));
       trSpec_external := tr_until (trSpec_external G1) (trSpec_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H.
    eapply (trI_until_tr_until_gen F (trSpec_internal G1) (trSpec_internal G2) (trSpec_external G1) (trSpec_external G2));
      [intros; by eapply trSpec_adeq | intros; by eapply trSpec_adeq | exact H].
  Qed.

  Definition trSpec_finally G : trSpec Λ Σ := trSpec_until trSpec_true G.

  Lemma trSpec_le_refl G : trSpec_le G G.
  Proof. intros ??. done. Qed.
  Lemma trSpec_le_trans G1 G2 G3 : trSpec_le G1 G2 → trSpec_le G2 G3 → trSpec_le G1 G3.
  Proof. intros H1 H2 ??. by rewrite H1 H2. Qed.
  Lemma trSpec_always_mono_i `{!temporalGS Λ Σ} (G G' : trSpec Λ Σ) :
    ▷ □ (∀ τ, trSpec_internal G τ -∗ trSpec_internal G' τ) -∗
    ∀ τ, trSpec_internal (trSpec_always G) τ -∗ trSpec_internal (trSpec_always G') τ.
  Proof. iIntros "#W" (τ). cbn. by iApply (trI_always_mono_i with "W"). Qed.
  Lemma trSpec_until_mono_i `{!temporalGS Λ Σ} (G1 G2 G1' G2' : trSpec Λ Σ) :
    ▷ □ (∀ τ, trSpec_internal G1 τ -∗ trSpec_internal G1' τ) -∗ ▷ □ (∀ τ, trSpec_internal G2 τ -∗ trSpec_internal G2' τ) -∗
    ∀ τ, trSpec_internal (trSpec_until G1 G2) τ -∗ trSpec_internal (trSpec_until G1' G2') τ.
  Proof.
    iIntros "#W1 #W2" (τ). cbn. rewrite /trI_exist. iIntros "[%a H]". iExists a.
    by iApply (trI_until_mono_i with "W1 W2").
  Qed.

End trSpec_connectives.

Notation "⌜ p ⌝" := (trSpec_pure p) : trSpec_scope.
Infix "∧" := trSpec_and : trSpec_scope.
Infix "∨" := trSpec_or : trSpec_scope.
Infix "→" := trSpec_impl : trSpec_scope.
Notation "∀ x .. y , G" := (trSpec_forall (λ x, .. (trSpec_forall (λ y, G%SPEC)) ..)) : trSpec_scope.
Notation "∃ x .. y , G" := (trSpec_exist (λ x, .. (trSpec_exist (λ y, G%SPEC)) ..)) : trSpec_scope.
Notation "□ G" := (trSpec_always G) (at level 20, right associativity) : trSpec_scope.
Notation "◇ G" := (trSpec_finally G) (at level 20, right associativity) : trSpec_scope.
Notation "G 'Uₜ' H" := (trSpec_until G H) (at level 60, right associativity) : trSpec_scope.

Global Instance trSpec_sqsubseteq {Λ Σ} : SqSubsetEq (trSpec Λ Σ) := trSpec_le.

(** ** Semantic state atoms

    Any predicate on the current state can be an atom, provided some iProp ensures it
    through the state interpretation (e.g. negated points-to facts). *)
Section state_atoms.
  Context {Λ : language} {Σ : gFunctors}.

  Program Definition trSpec_state (φ : state Λ → thread_pool Λ → Prop) : trSpec Λ Σ :=
    {| trSpec_internal _ τ := (let '((Θ, σ), _, _) := τ.2 τ.1 in ⌜φ σ Θ⌝)%I;
       trSpec_external := tr_state φ |}.
  Next Obligation.
    intros φ ? F [n τf] H. rewrite /tr_state /ts_emb /ts_state /trace_now. simpl in *.
    destruct (τf n) as (((Θ&σ)&?)&?). by apply sat_elim in H.
  Qed.

End state_atoms.

(** ** Complete and instant properties

    Complete: the trace reading gives the in-logic reading; instant: the converse. Pure
    facts, state atoms, always and until are complete; the non-temporal ones are also
    instant. They move an antecedent between the two readings (trspec_rules.v). *)
Section complete.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A : trSpec Λ Σ.

  Class TrSpecComplete G : Prop :=
    trSpec_complete : ∀ (H : temporalGS Λ Σ) τ, trSpec_external G τ → ⊢ @trSpec_internal _ _ G H τ.
  Class TrSpecInstant G : Prop :=
    trSpec_instant : ∀ (H : temporalGS Λ Σ) τ, @trSpec_internal _ _ G H τ ⊢ ⌜trSpec_external G τ⌝.

  (** Completeness. *)
  Global Instance trSpec_complete_pure φ : TrSpecComplete (trSpec_pure φ).
  Proof. intros ? τ H. rewrite /= /trI_pure. by iPureIntro. Qed.
  Global Instance trSpec_complete_and G1 G2 : TrSpecComplete G1 → TrSpecComplete G2 → TrSpecComplete (trSpec_and G1 G2).
  Proof. intros H1 H2 ? τ [??]. rewrite /= /trI_and. iSplit; [by iApply H1|by iApply H2]. Qed.
  Global Instance trSpec_complete_or G1 G2 : TrSpecComplete G1 → TrSpecComplete G2 → TrSpecComplete (trSpec_or G1 G2).
  Proof. intros H1 H2 ? τ [?|?]; rewrite /= /trI_or; [iLeft; by iApply H1|iRight; by iApply H2]. Qed.
  Global Instance trSpec_complete_impl A G : TrSpecComplete G → TrSpecComplete (trSpec_impl A G).
  Proof. intros HG ? τ H. rewrite /= /trI_impl. iIntros (HA). iApply HG. by apply H. Qed.
  Global Instance trSpec_complete_forall {X} (G : X → trSpec Λ Σ) :
    (∀ x, TrSpecComplete (G x)) → TrSpecComplete (trSpec_forall G).
  Proof. intros HG ? τ H. rewrite /= /trI_forall. iIntros (x). iApply HG. apply H. Qed.
  Global Instance trSpec_complete_exist {X} `{!TypeExistentialProperty X ordI} (G : X → trSpec Λ Σ) :
    (∀ x, TrSpecComplete (G x)) → TrSpecComplete (trSpec_exist G).
  Proof. intros HG ? τ [x H]. rewrite /= /trI_exist. iExists x. by iApply HG. Qed.

  Global Instance trSpec_complete_always G : TrSpecComplete G → TrSpecComplete (trSpec_always G).
  Proof.
    intros HG ? τ Hτ. rewrite /=.
    iAssert (□ ∀ τ, ⌜tr_always (trSpec_external G) τ⌝ → trI_always (trSpec_internal G) (trI_pure True) τ)%I as "#H";
      last by iApply "H".
    iLöb as "IH". iIntros "!>" ([n τf] Hal). rewrite trI_always_unfold /trI_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iApply ALC_intro. iMod "Hclose" as "_".
    iModIntro. iSplit.
    { iApply HG. apply (Hal n). lia. }
    iSplit; first by rewrite /trI_pure.
    iApply "IH". iPureIntro. intros m Hm. apply Hal. simpl in Hm. lia.
  Qed.

  Global Instance trSpec_complete_until G1 G2 :
    TrSpecComplete G1 → TrSpecComplete G2 → TrSpecComplete (trSpec_until G1 G2).
  Proof.
    intros H1 H2 ? [n τf] (m & Hnm & HQ & HP). rewrite /= /trI_exist.
    (* The measure is the number of steps to the right formula. *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → trSpec_external G1 (l, τf)) →
              ⊢ trI_until Ord.lt (Ord.from_nat d) (trSpec_internal G1) (trSpec_internal G2) (n', τf)) as Hu.
    { induction d as [|d IH]; intros n' Hd Hn' HP'; rewrite trI_until_unfold /trI_until_pre;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iNext; iMod "Hclose" as "_"; iModIntro;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iApply ALC_intro; iMod "Hclose" as "_"; iModIntro.
      - assert (m = n') as -> by lia. iLeft. by iApply H2.
      - iRight. iSplit; first (iApply H1; apply HP'; lia).
        iExists (Ord.from_nat d). iSplit; first (iPureIntro; rewrite Ord.from_nat_S; apply Ord.S_lt).
        iApply (IH (S n')); [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. lia. }
    iExists (Ord.from_nat (m - n)). iApply (Hu _ n eq_refl Hnm). intros l Hl. apply HP. lia.
  Qed.

  Global Instance trSpec_complete_finally G : TrSpecComplete G → TrSpecComplete (trSpec_finally G).
  Proof. intros HG. apply trSpec_complete_until; [apply trSpec_complete_pure|done]. Qed.

  (** Instantness. *)
  Global Instance trSpec_instant_pure φ : TrSpecInstant (trSpec_pure φ).
  Proof. intros ? τ. rewrite /= /trI_pure. by iIntros "%". Qed.
  Global Instance trSpec_instant_and G1 G2 : TrSpecInstant G1 → TrSpecInstant G2 → TrSpecInstant (trSpec_and G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /trI_and. iIntros "H".
    iAssert ⌜trSpec_external G1 τ⌝%I as %?; first by iApply H1; iDestruct "H" as "[$ _]".
    iAssert ⌜trSpec_external G2 τ⌝%I as %?; first by iApply H2; iDestruct "H" as "[_ $]".
    by iPureIntro.
  Qed.
  Global Instance trSpec_instant_or G1 G2 : TrSpecInstant G1 → TrSpecInstant G2 → TrSpecInstant (trSpec_or G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /trI_or. iIntros "[H|H]".
    - iDestruct (H1 with "H") as %?. iPureIntro. by left.
    - iDestruct (H2 with "H") as %?. iPureIntro. by right.
  Qed.
  Global Instance trSpec_instant_impl A G : TrSpecInstant G → TrSpecInstant (trSpec_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /trI_impl. iIntros "H".
    destruct (Classical_Prop.classic (trSpec_external A τ)) as [HA|HA].
    - iDestruct (HG with "(H [//])") as %?. iPureIntro. by intros _.
    - iPureIntro. by intros ?.
  Qed.
  Global Instance trSpec_instant_forall {X} (G : X → trSpec Λ Σ) :
    (∀ x, TrSpecInstant (G x)) → TrSpecInstant (trSpec_forall G).
  Proof.
    intros HG ? τ. rewrite /= /trI_forall /tr_forall.
    destruct (Classical_Prop.classic (∀ x, trSpec_external (G x) τ)) as [Hall|Hn]; first by iIntros "_".
    apply Classical_Pred_Type.not_all_ex_not in Hn as [x Hx].
    iIntros "H". iSpecialize ("H" $! x). iDestruct (HG with "H") as %?. done.
  Qed.
  Global Instance trSpec_instant_exist {X} `{!TypeExistentialProperty X ordI} (G : X → trSpec Λ Σ) :
    (∀ x, TrSpecInstant (G x)) → TrSpecInstant (trSpec_exist G).
  Proof.
    intros HG ? τ. rewrite /= /trI_exist. iIntros "[%x H]". iDestruct (HG with "H") as %?.
    iPureIntro. by exists x.
  Qed.

  Global Instance trSpec_complete_state φ : TrSpecComplete (trSpec_state φ).
  Proof.
    intros ? [n τf]. rewrite /= /tr_state /ts_emb /ts_state /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). intros Hφ. by iPureIntro.
  Qed.
  Global Instance trSpec_instant_state φ : TrSpecInstant (trSpec_state φ).
  Proof.
    intros ? [n τf]. rewrite /= /tr_state /ts_emb /ts_state /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). by iIntros "%".
  Qed.

End complete.
Global Hint Mode TrSpecComplete - - ! : typeclass_instances.
Global Hint Mode TrSpecInstant - - ! : typeclass_instances.
