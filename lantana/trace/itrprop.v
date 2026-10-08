From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export triprop.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.

(** * Internalized trace properties

    An [itrProp] is a trace property ([trProp], its external reading) with its
    internalization in the logic ([trIProp], its internal reading), adequate for it: if the
    internal reading is satisfiable, the external one holds. This file defines the
    connectives, the state atoms, and complete and instant properties; the rules are in
    itrprop_rules.v, the model in itrprop_model.v. *)

(** ** Definition *)

(** [itrProp_internal]: the step-indexed reading, which the run establishes;
    [itrProp_adeq]: its satisfiability implies the external reading. *)
Record itrProp {Λ : language} {Σ : gFunctors} := ItrProp {
  itrProp_internal : ∀ `{!temporalGS Λ Σ}, trace Λ → iProp Σ;
  itrProp_external : trProp Λ;
  itrProp_adeq : ∀ `{!temporalGS Λ Σ} (F : iProp Σ) (τ : trace Λ),
    iProp_sat_lc_at_frame F ⊤ (itrProp_internal τ) → itrProp_external τ;
}.
Global Arguments itrProp Λ Σ : clear implicits.
Global Arguments ItrProp {Λ Σ}.
Global Arguments itrProp_internal {Λ Σ} _ {_}.
Global Arguments itrProp_external {Λ Σ}.

Declare Scope itrProp_scope.
Delimit Scope itrProp_scope with ITR.
Bind Scope itrProp_scope with itrProp.

(** In-logic entailment [G ⊑ G']: the internal reading of [G] implies that of [G']. *)
Definition itrProp_le {Λ Σ} (G G' : itrProp Λ Σ) : Prop :=
  ∀ (H : temporalGS Λ Σ) τ, @itrProp_internal _ _ G H τ ⊢ @itrProp_internal _ _ G' H τ.

Section itrProp_connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : itrProp Λ Σ.

  Program Definition itrProp_pure (p : Prop) : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_pure p; itrProp_external := tr_pure p |}.
  Next Obligation. intros p ? F τ H. by apply sat_elim in H. Qed.

  Definition itrProp_true : itrProp Λ Σ := itrProp_pure True.

  Program Definition itrProp_and G1 G2 : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_and (itrProp_internal G1) (itrProp_internal G2); itrProp_external := tr_and (itrProp_external G1) (itrProp_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold trI_and in H. apply iProp_sat_lc_at_frame_and in H as [H1 H2].
    split; [eapply itrProp_adeq, H1|eapply itrProp_adeq, H2].
  Qed.

  Program Definition itrProp_or G1 G2 : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_or (itrProp_internal G1) (itrProp_internal G2); itrProp_external := tr_or (itrProp_external G1) (itrProp_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold trI_or in H. apply sat_or in H as [H|H].
    - left. by eapply itrProp_adeq.
    - right. by eapply itrProp_adeq.
  Qed.

  (** Implication, with any trace property as antecedent: both readings assume it at the
      level of traces. *)
  Program Definition itrProp_impl (A G : itrProp Λ Σ) : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_impl (itrProp_external A) (itrProp_internal G); itrProp_external := tr_impl (itrProp_external A) (itrProp_external G) |}.
  Next Obligation.
    intros A G ? F τ H HA. unfold trI_impl in H. eapply itrProp_adeq. eapply sat_impl; [apply H|].
    iIntros "_". by iPureIntro.
  Qed.

  (** Over any type: [sat] commutes with [∀]. *)
  Program Definition itrProp_forall {X : Type} (G : X → itrProp Λ Σ) : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_forall X (λ x, itrProp_internal (G x)); itrProp_external := tr_forall X (λ x, itrProp_external (G x)) |}.
  Next Obligation.
    intros X G ? F τ H x. unfold trI_forall in H. eapply itrProp_adeq. by apply (sat_forall x) in H.
  Qed.

  (** Existential quantification needs the existential property of the step index, so only
      types smaller than the ordinals of [ordI] qualify (nat, gnames, oids, Ord.t, ...). *)
  Program Definition itrProp_exist {X : Type} `{!TypeExistentialProperty X ordI} (G : X → itrProp Λ Σ) : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_exist X (λ x, itrProp_internal (G x)); itrProp_external := tr_exist X (λ x, itrProp_external (G x)) |}.
  Next Obligation.
    intros X ? G ? F τ H. unfold trI_exist in H. apply sat_exists in H as [x H].
    exists x. by eapply itrProp_adeq.
  Qed.

  Program Definition itrProp_always G : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_always (itrProp_internal G) (trI_pure True); itrProp_external := tr_always (itrProp_external G) |}.
  Next Obligation.
    intros G ? F τ H.
    cut (tr_always (itrProp_external G ∧ tr_pure True)%R τ).
    { unfold tr_always. destruct τ. intros Hτ m Hm. by destruct (Hτ m Hm). }
    eapply (trI_always_tr_always F (itrProp_internal G) (trI_pure True) (itrProp_external G) (tr_pure True));
      [intros; by eapply itrProp_adeq | intros; exact I | exact H].
  Qed.

  Program Definition itrProp_until G1 G2 : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_exist Ord.t (λ a, trI_until Ord.lt a (itrProp_internal G1) (itrProp_internal G2));
       itrProp_external := tr_until (itrProp_external G1) (itrProp_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H.
    eapply (trI_until_tr_until_gen F (itrProp_internal G1) (itrProp_internal G2) (itrProp_external G1) (itrProp_external G2));
      [intros; by eapply itrProp_adeq | intros; by eapply itrProp_adeq | exact H].
  Qed.

  Definition itrProp_finally G : itrProp Λ Σ := itrProp_until itrProp_true G.

  Lemma itrProp_le_refl G : itrProp_le G G.
  Proof. intros ??. done. Qed.
  Lemma itrProp_le_trans G1 G2 G3 : itrProp_le G1 G2 → itrProp_le G2 G3 → itrProp_le G1 G3.
  Proof. intros H1 H2 ??. by rewrite H1 H2. Qed.
  Lemma itrProp_always_mono_i `{!temporalGS Λ Σ} (G G' : itrProp Λ Σ) :
    ▷ □ (∀ τ, itrProp_internal G τ -∗ itrProp_internal G' τ) -∗
    ∀ τ, itrProp_internal (itrProp_always G) τ -∗ itrProp_internal (itrProp_always G') τ.
  Proof. iIntros "#W" (τ). cbn. by iApply (trI_always_mono_i with "W"). Qed.
  Lemma itrProp_until_mono_i `{!temporalGS Λ Σ} (G1 G2 G1' G2' : itrProp Λ Σ) :
    ▷ □ (∀ τ, itrProp_internal G1 τ -∗ itrProp_internal G1' τ) -∗ ▷ □ (∀ τ, itrProp_internal G2 τ -∗ itrProp_internal G2' τ) -∗
    ∀ τ, itrProp_internal (itrProp_until G1 G2) τ -∗ itrProp_internal (itrProp_until G1' G2') τ.
  Proof.
    iIntros "#W1 #W2" (τ). cbn. rewrite /trI_exist. iIntros "[%a H]". iExists a.
    by iApply (trI_until_mono_i with "W1 W2").
  Qed.

End itrProp_connectives.

Notation "⌜ p ⌝" := (itrProp_pure p) : itrProp_scope.
Infix "∧" := itrProp_and : itrProp_scope.
Infix "∨" := itrProp_or : itrProp_scope.
Infix "→" := itrProp_impl : itrProp_scope.
Notation "∀ x .. y , G" := (itrProp_forall (λ x, .. (itrProp_forall (λ y, G%ITR)) ..)) : itrProp_scope.
Notation "∃ x .. y , G" := (itrProp_exist (λ x, .. (itrProp_exist (λ y, G%ITR)) ..)) : itrProp_scope.
Notation "□ G" := (itrProp_always G) (at level 20, right associativity) : itrProp_scope.
Notation "◇ G" := (itrProp_finally G) (at level 20, right associativity) : itrProp_scope.
Notation "G 'Uₜ' H" := (itrProp_until G H) (at level 60, right associativity) : itrProp_scope.

Global Instance itrProp_sqsubseteq {Λ Σ} : SqSubsetEq (itrProp Λ Σ) := itrProp_le.

(** ** Semantic state atoms

    Any predicate on the current state can be an atom, provided some iProp ensures it
    through the state interpretation (e.g. negated points-to facts). *)
Section state_atoms.
  Context {Λ : language} {Σ : gFunctors}.

  Program Definition itrProp_state (φ : state Λ → thread_pool Λ → Prop) : itrProp Λ Σ :=
    {| itrProp_internal _ τ := (let '((Θ, σ), _, _) := τ.2 τ.1 in ⌜φ σ Θ⌝)%I;
       itrProp_external := tr_state φ |}.
  Next Obligation.
    intros φ ? F [n τf] H. rewrite /tr_state /ts_emb /ts_state /trace_now. simpl in *.
    destruct (τf n) as (((Θ&σ)&?)&?). by apply sat_elim in H.
  Qed.

End state_atoms.

(** ** Complete and instant properties

    Complete: the trace reading gives the in-logic reading; instant: the converse. Pure
    facts, state atoms, always and until are complete; the non-temporal ones are also
    instant. They move an antecedent between the two readings (itrprop_rules.v). *)
Section complete.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A : itrProp Λ Σ.

  Class ItrPropComplete G : Prop :=
    itrProp_complete : ∀ (H : temporalGS Λ Σ) τ, itrProp_external G τ → ⊢ @itrProp_internal _ _ G H τ.
  Class ItrPropInstant G : Prop :=
    itrProp_instant : ∀ (H : temporalGS Λ Σ) τ, @itrProp_internal _ _ G H τ ⊢ ⌜itrProp_external G τ⌝.

  (** Completeness. *)
  Global Instance itrProp_complete_pure φ : ItrPropComplete (itrProp_pure φ).
  Proof. intros ? τ H. rewrite /= /trI_pure. by iPureIntro. Qed.
  Global Instance itrProp_complete_and G1 G2 : ItrPropComplete G1 → ItrPropComplete G2 → ItrPropComplete (itrProp_and G1 G2).
  Proof. intros H1 H2 ? τ [??]. rewrite /= /trI_and. iSplit; [by iApply H1|by iApply H2]. Qed.
  Global Instance itrProp_complete_or G1 G2 : ItrPropComplete G1 → ItrPropComplete G2 → ItrPropComplete (itrProp_or G1 G2).
  Proof. intros H1 H2 ? τ [?|?]; rewrite /= /trI_or; [iLeft; by iApply H1|iRight; by iApply H2]. Qed.
  Global Instance itrProp_complete_impl A G : ItrPropComplete G → ItrPropComplete (itrProp_impl A G).
  Proof. intros HG ? τ H. rewrite /= /trI_impl. iIntros (HA). iApply HG. by apply H. Qed.
  Global Instance itrProp_complete_forall {X} (G : X → itrProp Λ Σ) :
    (∀ x, ItrPropComplete (G x)) → ItrPropComplete (itrProp_forall G).
  Proof. intros HG ? τ H. rewrite /= /trI_forall. iIntros (x). iApply HG. apply H. Qed.
  Global Instance itrProp_complete_exist {X} `{!TypeExistentialProperty X ordI} (G : X → itrProp Λ Σ) :
    (∀ x, ItrPropComplete (G x)) → ItrPropComplete (itrProp_exist G).
  Proof. intros HG ? τ [x H]. rewrite /= /trI_exist. iExists x. by iApply HG. Qed.

  Global Instance itrProp_complete_always G : ItrPropComplete G → ItrPropComplete (itrProp_always G).
  Proof.
    intros HG ? τ Hτ. rewrite /=.
    iAssert (□ ∀ τ, ⌜tr_always (itrProp_external G) τ⌝ → trI_always (itrProp_internal G) (trI_pure True) τ)%I as "#H";
      last by iApply "H".
    iLöb as "IH". iIntros "!>" ([n τf] Hal). rewrite trI_always_unfold /trI_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iApply ALC_intro. iMod "Hclose" as "_".
    iModIntro. iSplit.
    { iApply HG. apply (Hal n). lia. }
    iSplit; first by rewrite /trI_pure.
    iApply "IH". iPureIntro. intros m Hm. apply Hal. simpl in Hm. lia.
  Qed.

  Global Instance itrProp_complete_until G1 G2 :
    ItrPropComplete G1 → ItrPropComplete G2 → ItrPropComplete (itrProp_until G1 G2).
  Proof.
    intros H1 H2 ? [n τf] (m & Hnm & HQ & HP). rewrite /= /trI_exist.
    (* The measure is the number of steps to the right formula. *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → itrProp_external G1 (l, τf)) →
              ⊢ trI_until Ord.lt (Ord.from_nat d) (itrProp_internal G1) (itrProp_internal G2) (n', τf)) as Hu.
    { induction d as [|d IH]; intros n' Hd Hn' HP'; rewrite trI_until_unfold /trI_until_pre;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iNext; iMod "Hclose" as "_"; iModIntro;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iApply ALC_intro; iMod "Hclose" as "_"; iModIntro.
      - assert (m = n') as -> by lia. iLeft. by iApply H2.
      - iRight. iSplit; first (iApply H1; apply HP'; lia).
        iExists (Ord.from_nat d). iSplit; first (iPureIntro; rewrite Ord.from_nat_S; apply Ord.S_lt).
        iApply (IH (S n')); [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. lia. }
    iExists (Ord.from_nat (m - n)). iApply (Hu _ n eq_refl Hnm). intros l Hl. apply HP. lia.
  Qed.

  Global Instance itrProp_complete_finally G : ItrPropComplete G → ItrPropComplete (itrProp_finally G).
  Proof. intros HG. apply itrProp_complete_until; [apply itrProp_complete_pure|done]. Qed.

  (** Instantness. *)
  Global Instance itrProp_instant_pure φ : ItrPropInstant (itrProp_pure φ).
  Proof. intros ? τ. rewrite /= /trI_pure. by iIntros "%". Qed.
  Global Instance itrProp_instant_and G1 G2 : ItrPropInstant G1 → ItrPropInstant G2 → ItrPropInstant (itrProp_and G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /trI_and. iIntros "H".
    iAssert ⌜itrProp_external G1 τ⌝%I as %?; first by iApply H1; iDestruct "H" as "[$ _]".
    iAssert ⌜itrProp_external G2 τ⌝%I as %?; first by iApply H2; iDestruct "H" as "[_ $]".
    by iPureIntro.
  Qed.
  Global Instance itrProp_instant_or G1 G2 : ItrPropInstant G1 → ItrPropInstant G2 → ItrPropInstant (itrProp_or G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /trI_or. iIntros "[H|H]".
    - iDestruct (H1 with "H") as %?. iPureIntro. by left.
    - iDestruct (H2 with "H") as %?. iPureIntro. by right.
  Qed.
  Global Instance itrProp_instant_impl A G : ItrPropInstant G → ItrPropInstant (itrProp_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /trI_impl. iIntros "H".
    destruct (Classical_Prop.classic (itrProp_external A τ)) as [HA|HA].
    - iDestruct (HG with "(H [//])") as %?. iPureIntro. by intros _.
    - iPureIntro. by intros ?.
  Qed.
  Global Instance itrProp_instant_forall {X} (G : X → itrProp Λ Σ) :
    (∀ x, ItrPropInstant (G x)) → ItrPropInstant (itrProp_forall G).
  Proof.
    intros HG ? τ. rewrite /= /trI_forall /tr_forall.
    destruct (Classical_Prop.classic (∀ x, itrProp_external (G x) τ)) as [Hall|Hn]; first by iIntros "_".
    apply Classical_Pred_Type.not_all_ex_not in Hn as [x Hx].
    iIntros "H". iSpecialize ("H" $! x). iDestruct (HG with "H") as %?. done.
  Qed.
  Global Instance itrProp_instant_exist {X} `{!TypeExistentialProperty X ordI} (G : X → itrProp Λ Σ) :
    (∀ x, ItrPropInstant (G x)) → ItrPropInstant (itrProp_exist G).
  Proof.
    intros HG ? τ. rewrite /= /trI_exist. iIntros "[%x H]". iDestruct (HG with "H") as %?.
    iPureIntro. by exists x.
  Qed.

  Global Instance itrProp_complete_state φ : ItrPropComplete (itrProp_state φ).
  Proof.
    intros ? [n τf]. rewrite /= /tr_state /ts_emb /ts_state /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). intros Hφ. by iPureIntro.
  Qed.
  Global Instance itrProp_instant_state φ : ItrPropInstant (itrProp_state φ).
  Proof.
    intros ? [n τf]. rewrite /= /tr_state /ts_emb /ts_state /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). by iIntros "%".
  Qed.

End complete.
Global Hint Mode ItrPropComplete - - ! : typeclass_instances.
Global Hint Mode ItrPropInstant - - ! : typeclass_instances.
