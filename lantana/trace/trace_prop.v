From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trace_step_indexed.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.

(** * Semantic trace properties

    Trace properties ([tps]) with an in-logic and a trace reading, their connectives, state
    atoms, and complete and instant properties. *)

(** ** Semantic trace properties *)

(** [tps_ti]: the step-indexed reading, which the running system establishes in the logic;
    [tps_good]: its satisfiability implies the trace reading [tps_tr]. *)
Record tps {Λ : language} {Σ : gFunctors} := Tps {
  tps_ti : ∀ `{!temporalGS Λ Σ}, trace Λ → iProp Σ;
  tps_tr : trace Λ → Prop;
  tps_good : ∀ `{!temporalGS Λ Σ} (F : iProp Σ) (τ : trace Λ),
    iProp_sat_lc_at_frame F ⊤ (tps_ti τ) → tps_tr τ;
}.
Global Arguments tps Λ Σ : clear implicits.
Global Arguments Tps {Λ Σ}.
Global Arguments tps_ti {Λ Σ} _ {_}.
Global Arguments tps_tr {Λ Σ}.

Declare Scope tps_scope.
Delimit Scope tps_scope with S.
Bind Scope tps_scope with tps.

(** [G ⊑ G']: the step-indexed part of [G] implies that of [G']. *)
Definition tps_le {Λ Σ} (G G' : tps Λ Σ) : Prop :=
  ∀ (H : temporalGS Λ Σ) τ, @tps_ti _ _ G H τ ⊢ @tps_ti _ _ G' H τ.

Section tps_connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : tps Λ Σ.

  Program Definition tps_pure (p : Prop) : tps Λ Σ :=
    {| tps_ti _ := ti_pure p; tps_tr := tr_pure p |}.
  Next Obligation. intros p ? F τ H. by apply sat_elim in H. Qed.

  Definition tps_true : tps Λ Σ := tps_pure True.

  Program Definition tps_atomic (π : state_pred Λ) : tps Λ Σ :=
    {| tps_ti _ := ti_atomic π; tps_tr := tr_atomic π |}.
  Next Obligation.
    intros π ? F [n τf] H. unfold ti_atomic in H. simpl in H.
    unfold tr_atomic, ts_emb, ts_atomic. simpl. destruct (τf n) as (((Θ&σ)&?)&?).
    by apply sat_elim in H.
  Qed.

  Program Definition tps_and G1 G2 : tps Λ Σ :=
    {| tps_ti _ := ti_and (tps_ti G1) (tps_ti G2); tps_tr := tr_and (tps_tr G1) (tps_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold ti_and in H. apply iProp_sat_lc_at_frame_and in H as [H1 H2].
    split; [eapply tps_good, H1|eapply tps_good, H2].
  Qed.

  Program Definition tps_or G1 G2 : tps Λ Σ :=
    {| tps_ti _ := ti_or (tps_ti G1) (tps_ti G2); tps_tr := tr_or (tps_tr G1) (tps_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold ti_or in H. apply sat_or in H as [H|H].
    - left. by eapply tps_good.
    - right. by eapply tps_good.
  Qed.

  (** Implication, with any trace property as antecedent: both readings assume it at the
      level of traces. *)
  Program Definition tps_impl (A G : tps Λ Σ) : tps Λ Σ :=
    {| tps_ti _ := ti_impl (tps_tr A) (tps_ti G); tps_tr := tr_impl (tps_tr A) (tps_tr G) |}.
  Next Obligation.
    intros A G ? F τ H HA. unfold ti_impl in H. eapply tps_good. eapply sat_impl; [apply H|].
    iIntros "_". by iPureIntro.
  Qed.

  (** Over any type: [sat] commutes with [∀]. *)
  Program Definition tps_forall {X : Type} (G : X → tps Λ Σ) : tps Λ Σ :=
    {| tps_ti _ := ti_forall X (λ x, tps_ti (G x)); tps_tr := tr_forall X (λ x, tps_tr (G x)) |}.
  Next Obligation.
    intros X G ? F τ H x. unfold ti_forall in H. eapply tps_good. by apply (sat_forall x) in H.
  Qed.

  (** Existential quantification needs the existential property of the step index, so only
      types smaller than the ordinals of [ordI] qualify (nat, gnames, oids, Ord.t, ...). *)
  Program Definition tps_exist {X : Type} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) : tps Λ Σ :=
    {| tps_ti _ := ti_exist X (λ x, tps_ti (G x)); tps_tr := tr_exist X (λ x, tps_tr (G x)) |}.
  Next Obligation.
    intros X ? G ? F τ H. unfold ti_exist in H. apply sat_exists in H as [x H].
    exists x. by eapply tps_good.
  Qed.

  Program Definition tps_always G : tps Λ Σ :=
    {| tps_ti _ := ti_always (tps_ti G) (ti_pure True); tps_tr := tr_always (tps_tr G) |}.
  Next Obligation.
    intros G ? F τ H.
    cut (tr_always (tps_tr G ∧ tr_pure True)%R τ).
    { unfold tr_always. destruct τ. intros Hτ m Hm. by destruct (Hτ m Hm). }
    eapply (ti_always_tr_always F (tps_ti G) (ti_pure True) (tps_tr G) (tr_pure True));
      [intros; by eapply tps_good | intros; exact I | exact H].
  Qed.

  Program Definition tps_until G1 G2 : tps Λ Σ :=
    {| tps_ti _ := ti_exist Ord.t (λ a, ti_until Ord.lt a (tps_ti G1) (tps_ti G2));
       tps_tr := tr_until (tps_tr G1) (tps_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H.
    eapply (ti_until_tr_until_gen F (tps_ti G1) (tps_ti G2) (tps_tr G1) (tps_tr G2));
      [intros; by eapply tps_good | intros; by eapply tps_good | exact H].
  Qed.

  Definition tps_finally G : tps Λ Σ := tps_until tps_true G.

  Lemma tps_le_refl G : tps_le G G.
  Proof. intros ??. done. Qed.
  Lemma tps_le_trans G1 G2 G3 : tps_le G1 G2 → tps_le G2 G3 → tps_le G1 G3.
  Proof. intros H1 H2 ??. by rewrite H1 H2. Qed.
  Lemma tps_le_true G : tps_le G tps_true.
  Proof. intros ??. by iIntros "_". Qed.
  Lemma tps_and_elim_l G1 G2 : tps_le (tps_and G1 G2) G1.
  Proof. intros ??. rewrite /= /ti_and. by iIntros "[$ _]". Qed.
  Lemma tps_and_elim_r G1 G2 : tps_le (tps_and G1 G2) G2.
  Proof. intros ??. rewrite /= /ti_and. by iIntros "[_ $]". Qed.

  Lemma tps_or_mono G1 G2 G1' G2' :
    tps_le G1 G1' → tps_le G2 G2' → tps_le (tps_or G1 G2) (tps_or G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /ti_or. by rewrite H1 H2. Qed.
  Lemma tps_and_mono G1 G2 G1' G2' :
    tps_le G1 G1' → tps_le G2 G2' → tps_le (tps_and G1 G2) (tps_and G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /ti_and. by rewrite H1 H2. Qed.
  (** Antecedents are compared as trace properties. *)
  Lemma tps_impl_mono A A' G G' :
    (∀ τ, tps_tr A' τ → tps_tr A τ) → tps_le G G' → tps_le (tps_impl A G) (tps_impl A' G').
  Proof. intros HA HG ??. rewrite /= /ti_impl. iIntros "H %H'". iApply HG. iApply "H". eauto. Qed.
  Lemma tps_impl_intro_le A G : tps_le G (tps_impl A G).
  Proof. intros ??. rewrite /= /ti_impl. by iIntros "H _". Qed.
  Lemma tps_forall_mono {X} (G G' : X → tps Λ Σ) :
    (∀ x, tps_le (G x) (G' x)) → tps_le (tps_forall G) (tps_forall G').
  Proof. intros H ??. rewrite /= /ti_forall. iIntros "H %x". iApply H. iApply "H". Qed.
  Lemma tps_exist_mono {X} `{!TypeExistentialProperty X ordI} (G G' : X → tps Λ Σ) :
    (∀ x, tps_le (G x) (G' x)) → tps_le (tps_exist G) (tps_exist G').
  Proof. intros H ??. rewrite /= /ti_exist. iIntros "[%x H]". iExists x. by iApply H. Qed.

  Lemma tps_always_mono G G' : tps_le G G' → tps_le (tps_always G) (tps_always G').
  Proof.
    intros Hle H τ. cbn. iIntros "H".
    iAssert (∀ τ, ti_always (tps_ti G) (ti_pure True) τ -∗ ti_always (tps_ti G') (ti_pure True) τ)%I
      with "[]" as "Hal"; last by iApply "Hal".
    iLöb as "IH". iIntros (τ') "H". rewrite !ti_always_unfold /ti_always_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first (iDestruct "H" as "[H _]"; by iApply Hle).
    iSplit; first by iDestruct "H" as "[_ [$ _]]".
    iDestruct "H" as "[_ [_ H]]". by iApply "IH".
  Qed.

  Lemma tps_until_mono G1 G2 G1' G2' :
    tps_le G1 G1' → tps_le G2 G2' → tps_le (tps_until G1 G2) (tps_until G1' G2').
  Proof.
    intros H1 H2 H τ. cbn. rewrite /ti_exist. iIntros "[%a H]". iExists a.
    iAssert (∀ a τ, ti_until Ord.lt a (tps_ti G1) (tps_ti G2) τ -∗
                    ti_until Ord.lt a (tps_ti G1') (tps_ti G2') τ)%I with "[]" as "Hu";
      last by iApply "Hu".
    iLöb as "IH". iIntros (a' τ') "H". rewrite !ti_until_unfold /ti_until_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. iDestruct "H" as "[H|H]".
    - iLeft. by iApply H2.
    - iRight. iSplit; first (iDestruct "H" as "[H _]"; by iApply H1).
      iDestruct "H" as "[_ (%a''& %Hlt& H)]". iExists a''. iSplit; first done. by iApply "IH".
  Qed.

  Lemma tps_always_mono_i `{!temporalGS Λ Σ} (G G' : tps Λ Σ) :
    ▷ □ (∀ τ, tps_ti G τ -∗ tps_ti G' τ) -∗
    ∀ τ, tps_ti (tps_always G) τ -∗ tps_ti (tps_always G') τ.
  Proof. iIntros "#W" (τ). cbn. by iApply (ti_always_mono_i with "W"). Qed.
  Lemma tps_until_mono_i `{!temporalGS Λ Σ} (G1 G2 G1' G2' : tps Λ Σ) :
    ▷ □ (∀ τ, tps_ti G1 τ -∗ tps_ti G1' τ) -∗ ▷ □ (∀ τ, tps_ti G2 τ -∗ tps_ti G2' τ) -∗
    ∀ τ, tps_ti (tps_until G1 G2) τ -∗ tps_ti (tps_until G1' G2') τ.
  Proof.
    iIntros "#W1 #W2" (τ). cbn. rewrite /ti_exist. iIntros "[%a H]". iExists a.
    by iApply (ti_until_mono_i with "W1 W2").
  Qed.

End tps_connectives.

Notation "⌜ p ⌝" := (tps_pure p) : tps_scope.
Infix "∧" := tps_and : tps_scope.
Infix "∨" := tps_or : tps_scope.
Infix "→" := tps_impl : tps_scope.
Notation "∀ x .. y , G" := (tps_forall (λ x, .. (tps_forall (λ y, G%S)) ..)) : tps_scope.
Notation "∃ x .. y , G" := (tps_exist (λ x, .. (tps_exist (λ y, G%S)) ..)) : tps_scope.

(** ** Semantic state atoms

    Any predicate on the current state can be an atom, provided some iProp ensures it
    through the state interpretation (e.g. negated points-to facts). *)
Section state_atoms.
  Context {Λ : language} {Σ : gFunctors}.

  Program Definition tps_state (φ : state Λ → thread_pool Λ → Prop) : tps Λ Σ :=
    {| tps_ti _ τ := (let '((Θ, σ), _, _) := τ.2 τ.1 in ⌜φ σ Θ⌝)%I;
       tps_tr τ := let '((Θ, σ), _, _) := τ.2 τ.1 in φ σ Θ |}.
  Next Obligation.
    intros φ ? F [n τf] H. simpl in *. destruct (τf n) as (((Θ&σ)&?)&?). by apply sat_elim in H.
  Qed.

End state_atoms.

(** ** Complete and instant trace properties

    An implication [A → G] assumes [A] at the level of traces. In the logic it is introduced
    from [A ∧ H ⊑ G] when [A] is complete (its trace reading gives its in-logic reading), and
    eliminated when [A] is instant (the converse). Pure facts, state atoms, always and until
    are complete; the non-temporal ones are also instant. *)
Section complete.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A : tps Λ Σ.

  Class TpsComplete G : Prop :=
    tps_complete : ∀ (H : temporalGS Λ Σ) τ, tps_tr G τ → ⊢ @tps_ti _ _ G H τ.
  Class TpsInstant G : Prop :=
    tps_instant : ∀ (H : temporalGS Λ Σ) τ, @tps_ti _ _ G H τ ⊢ ⌜tps_tr G τ⌝.

  Lemma tps_impl_intro A H G `{HA : !TpsComplete A} :
    tps_le (tps_and A H) G → tps_le H (tps_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /ti_impl. iIntros "H %Hτ". iApply HG.
    rewrite /= /ti_and. iSplit; last done. by iApply HA.
  Qed.

  Lemma tps_impl_elim A G `{HA : !TpsInstant A} : tps_le (tps_and A (tps_impl A G)) G.
  Proof.
    intros ? τ. rewrite /= /ti_and /ti_impl. iIntros "H".
    iAssert ⌜tps_tr A τ⌝%I as %Hτ; first by iApply HA; iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ H]". by iApply "H".
  Qed.

  (** Completeness. *)
  Global Instance tps_complete_pure φ : TpsComplete (tps_pure φ).
  Proof. intros ? τ H. rewrite /= /ti_pure. by iPureIntro. Qed.
  Global Instance tps_complete_atomic π : TpsComplete (tps_atomic π).
  Proof.
    intros ? [n τf]. rewrite /= /ti_atomic /tr_atomic /ts_emb /ts_atomic /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). intros Hπ. iPureIntro. exact Hπ.
  Qed.
  Global Instance tps_complete_and G1 G2 : TpsComplete G1 → TpsComplete G2 → TpsComplete (tps_and G1 G2).
  Proof. intros H1 H2 ? τ [??]. rewrite /= /ti_and. iSplit; [by iApply H1|by iApply H2]. Qed.
  Global Instance tps_complete_or G1 G2 : TpsComplete G1 → TpsComplete G2 → TpsComplete (tps_or G1 G2).
  Proof. intros H1 H2 ? τ [?|?]; rewrite /= /ti_or; [iLeft; by iApply H1|iRight; by iApply H2]. Qed.
  Global Instance tps_complete_impl A G : TpsComplete G → TpsComplete (tps_impl A G).
  Proof. intros HG ? τ H. rewrite /= /ti_impl. iIntros (HA). iApply HG. by apply H. Qed.
  Global Instance tps_complete_forall {X} (G : X → tps Λ Σ) :
    (∀ x, TpsComplete (G x)) → TpsComplete (tps_forall G).
  Proof. intros HG ? τ H. rewrite /= /ti_forall. iIntros (x). iApply HG. apply H. Qed.
  Global Instance tps_complete_exist {X} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) :
    (∀ x, TpsComplete (G x)) → TpsComplete (tps_exist G).
  Proof. intros HG ? τ [x H]. rewrite /= /ti_exist. iExists x. by iApply HG. Qed.

  Global Instance tps_complete_always G : TpsComplete G → TpsComplete (tps_always G).
  Proof.
    intros HG ? τ Hτ. rewrite /=.
    iAssert (□ ∀ τ, ⌜tr_always (tps_tr G) τ⌝ → ti_always (tps_ti G) (ti_pure True) τ)%I as "#H";
      last by iApply "H".
    iLöb as "IH". iIntros "!>" ([n τf] Hal). rewrite ti_always_unfold /ti_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iApply ALC_intro. iMod "Hclose" as "_".
    iModIntro. iSplit.
    { iApply HG. apply (Hal n). lia. }
    iSplit; first by rewrite /ti_pure.
    iApply "IH". iPureIntro. intros m Hm. apply Hal. simpl in Hm. lia.
  Qed.

  Global Instance tps_complete_until G1 G2 :
    TpsComplete G1 → TpsComplete G2 → TpsComplete (tps_until G1 G2).
  Proof.
    intros H1 H2 ? [n τf] (m & Hnm & HQ & HP). rewrite /= /ti_exist.
    (* The measure is the number of steps to the right formula. *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → tps_tr G1 (l, τf)) →
              ⊢ ti_until Ord.lt (Ord.from_nat d) (tps_ti G1) (tps_ti G2) (n', τf)) as Hu.
    { induction d as [|d IH]; intros n' Hd Hn' HP'; rewrite ti_until_unfold /ti_until_pre;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iNext; iMod "Hclose" as "_"; iModIntro;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iApply ALC_intro; iMod "Hclose" as "_"; iModIntro.
      - assert (m = n') as -> by lia. iLeft. by iApply H2.
      - iRight. iSplit; first (iApply H1; apply HP'; lia).
        iExists (Ord.from_nat d). iSplit; first (iPureIntro; rewrite Ord.from_nat_S; apply Ord.S_lt).
        iApply (IH (S n')); [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. lia. }
    iExists (Ord.from_nat (m - n)). iApply (Hu _ n eq_refl Hnm). intros l Hl. apply HP. lia.
  Qed.

  Global Instance tps_complete_finally G : TpsComplete G → TpsComplete (tps_finally G).
  Proof. intros HG. apply tps_complete_until; [apply tps_complete_pure|done]. Qed.

  (** Instantness. *)
  Global Instance tps_instant_pure φ : TpsInstant (tps_pure φ).
  Proof. intros ? τ. rewrite /= /ti_pure. by iIntros "%". Qed.
  Global Instance tps_instant_atomic π : TpsInstant (tps_atomic π).
  Proof.
    intros ? [n τf]. rewrite /= /ti_atomic /tr_atomic /ts_emb /ts_atomic /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). by iIntros "%".
  Qed.
  Global Instance tps_instant_and G1 G2 : TpsInstant G1 → TpsInstant G2 → TpsInstant (tps_and G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /ti_and. iIntros "H".
    iAssert ⌜tps_tr G1 τ⌝%I as %?; first by iApply H1; iDestruct "H" as "[$ _]".
    iAssert ⌜tps_tr G2 τ⌝%I as %?; first by iApply H2; iDestruct "H" as "[_ $]".
    by iPureIntro.
  Qed.
  Global Instance tps_instant_or G1 G2 : TpsInstant G1 → TpsInstant G2 → TpsInstant (tps_or G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /ti_or. iIntros "[H|H]".
    - iDestruct (H1 with "H") as %?. iPureIntro. by left.
    - iDestruct (H2 with "H") as %?. iPureIntro. by right.
  Qed.
  Global Instance tps_instant_impl A G : TpsInstant G → TpsInstant (tps_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /ti_impl. iIntros "H".
    destruct (Classical_Prop.classic (tps_tr A τ)) as [HA|HA].
    - iDestruct (HG with "(H [//])") as %?. iPureIntro. by intros _.
    - iPureIntro. by intros ?.
  Qed.
  Global Instance tps_instant_forall {X} (G : X → tps Λ Σ) :
    (∀ x, TpsInstant (G x)) → TpsInstant (tps_forall G).
  Proof.
    intros HG ? τ. rewrite /= /ti_forall /tr_forall.
    destruct (Classical_Prop.classic (∀ x, tps_tr (G x) τ)) as [Hall|Hn]; first by iIntros "_".
    apply Classical_Pred_Type.not_all_ex_not in Hn as [x Hx].
    iIntros "H". iSpecialize ("H" $! x). iDestruct (HG with "H") as %?. done.
  Qed.
  Global Instance tps_instant_exist {X} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) :
    (∀ x, TpsInstant (G x)) → TpsInstant (tps_exist G).
  Proof.
    intros HG ? τ. rewrite /= /ti_exist. iIntros "[%x H]". iDestruct (HG with "H") as %?.
    iPureIntro. by exists x.
  Qed.

  Global Instance tps_complete_state φ : TpsComplete (tps_state φ).
  Proof.
    intros ? [n τf]. rewrite /=. destruct (τf n) as (((Θ&σ)&?)&?). intros Hφ. by iPureIntro.
  Qed.
  Global Instance tps_instant_state φ : TpsInstant (tps_state φ).
  Proof. intros ? [n τf]. rewrite /=. destruct (τf n) as (((Θ&σ)&?)&?). by iIntros "%". Qed.

End complete.
Global Hint Mode TpsComplete - - ! : typeclass_instances.
Global Hint Mode TpsInstant - - ! : typeclass_instances.
