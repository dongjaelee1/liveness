From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trace_step_indexed.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.

(** * Semantic trace properties

    Trace properties ([tprop]) with an in-logic and a trace reading, their connectives, state
    atoms, and complete and instant properties. *)

(** ** Semantic trace properties *)

(** [tprop_ti]: the step-indexed reading, which the running system establishes in the logic;
    [tprop_good]: its satisfiability implies the trace reading [tprop_tr]. *)
Record tprop {Λ : language} {Σ : gFunctors} := Tprop {
  tprop_ti : ∀ `{!temporalGS Λ Σ}, trace Λ → iProp Σ;
  tprop_tr : trace Λ → Prop;
  tprop_good : ∀ `{!temporalGS Λ Σ} (F : iProp Σ) (τ : trace Λ),
    iProp_sat_lc_at_frame F ⊤ (tprop_ti τ) → tprop_tr τ;
}.
Global Arguments tprop Λ Σ : clear implicits.
Global Arguments Tprop {Λ Σ}.
Global Arguments tprop_ti {Λ Σ} _ {_}.
Global Arguments tprop_tr {Λ Σ}.

Declare Scope tprop_scope.
Delimit Scope tprop_scope with T.
Bind Scope tprop_scope with tprop.

(** [G ⊑ G']: the step-indexed part of [G] implies that of [G']. *)
Definition tprop_le {Λ Σ} (G G' : tprop Λ Σ) : Prop :=
  ∀ (H : temporalGS Λ Σ) τ, @tprop_ti _ _ G H τ ⊢ @tprop_ti _ _ G' H τ.

Section tprop_connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : tprop Λ Σ.

  Program Definition tprop_pure (p : Prop) : tprop Λ Σ :=
    {| tprop_ti _ := ti_pure p; tprop_tr := tr_pure p |}.
  Next Obligation. intros p ? F τ H. by apply sat_elim in H. Qed.

  Definition tprop_true : tprop Λ Σ := tprop_pure True.

  Program Definition tprop_atomic (π : state_pred Λ) : tprop Λ Σ :=
    {| tprop_ti _ := ti_atomic π; tprop_tr := tr_atomic π |}.
  Next Obligation.
    intros π ? F [n τf] H. unfold ti_atomic in H. simpl in H.
    unfold tr_atomic, ts_emb, ts_atomic. simpl. destruct (τf n) as (((Θ&σ)&?)&?).
    by apply sat_elim in H.
  Qed.

  Program Definition tprop_and G1 G2 : tprop Λ Σ :=
    {| tprop_ti _ := ti_and (tprop_ti G1) (tprop_ti G2); tprop_tr := tr_and (tprop_tr G1) (tprop_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold ti_and in H. apply iProp_sat_lc_at_frame_and in H as [H1 H2].
    split; [eapply tprop_good, H1|eapply tprop_good, H2].
  Qed.

  Program Definition tprop_or G1 G2 : tprop Λ Σ :=
    {| tprop_ti _ := ti_or (tprop_ti G1) (tprop_ti G2); tprop_tr := tr_or (tprop_tr G1) (tprop_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold ti_or in H. apply sat_or in H as [H|H].
    - left. by eapply tprop_good.
    - right. by eapply tprop_good.
  Qed.

  (** Implication, with any trace property as antecedent: both readings assume it at the
      level of traces. *)
  Program Definition tprop_impl (A G : tprop Λ Σ) : tprop Λ Σ :=
    {| tprop_ti _ := ti_impl (tprop_tr A) (tprop_ti G); tprop_tr := tr_impl (tprop_tr A) (tprop_tr G) |}.
  Next Obligation.
    intros A G ? F τ H HA. unfold ti_impl in H. eapply tprop_good. eapply sat_impl; [apply H|].
    iIntros "_". by iPureIntro.
  Qed.

  (** Over any type: [sat] commutes with [∀]. *)
  Program Definition tprop_forall {X : Type} (G : X → tprop Λ Σ) : tprop Λ Σ :=
    {| tprop_ti _ := ti_forall X (λ x, tprop_ti (G x)); tprop_tr := tr_forall X (λ x, tprop_tr (G x)) |}.
  Next Obligation.
    intros X G ? F τ H x. unfold ti_forall in H. eapply tprop_good. by apply (sat_forall x) in H.
  Qed.

  (** Existential quantification needs the existential property of the step index, so only
      types smaller than the ordinals of [ordI] qualify (nat, gnames, oids, Ord.t, ...). *)
  Program Definition tprop_exist {X : Type} `{!TypeExistentialProperty X ordI} (G : X → tprop Λ Σ) : tprop Λ Σ :=
    {| tprop_ti _ := ti_exist X (λ x, tprop_ti (G x)); tprop_tr := tr_exist X (λ x, tprop_tr (G x)) |}.
  Next Obligation.
    intros X ? G ? F τ H. unfold ti_exist in H. apply sat_exists in H as [x H].
    exists x. by eapply tprop_good.
  Qed.

  Program Definition tprop_always G : tprop Λ Σ :=
    {| tprop_ti _ := ti_always (tprop_ti G) (ti_pure True); tprop_tr := tr_always (tprop_tr G) |}.
  Next Obligation.
    intros G ? F τ H.
    cut (tr_always (tprop_tr G ∧ tr_pure True)%R τ).
    { unfold tr_always. destruct τ. intros Hτ m Hm. by destruct (Hτ m Hm). }
    eapply (ti_always_tr_always F (tprop_ti G) (ti_pure True) (tprop_tr G) (tr_pure True));
      [intros; by eapply tprop_good | intros; exact I | exact H].
  Qed.

  Program Definition tprop_until G1 G2 : tprop Λ Σ :=
    {| tprop_ti _ := ti_exist Ord.t (λ a, ti_until Ord.lt a (tprop_ti G1) (tprop_ti G2));
       tprop_tr := tr_until (tprop_tr G1) (tprop_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H.
    eapply (ti_until_tr_until_gen F (tprop_ti G1) (tprop_ti G2) (tprop_tr G1) (tprop_tr G2));
      [intros; by eapply tprop_good | intros; by eapply tprop_good | exact H].
  Qed.

  Definition tprop_finally G : tprop Λ Σ := tprop_until tprop_true G.

  Lemma tprop_le_refl G : tprop_le G G.
  Proof. intros ??. done. Qed.
  Lemma tprop_le_trans G1 G2 G3 : tprop_le G1 G2 → tprop_le G2 G3 → tprop_le G1 G3.
  Proof. intros H1 H2 ??. by rewrite H1 H2. Qed.
  Lemma tprop_le_true G : tprop_le G tprop_true.
  Proof. intros ??. by iIntros "_". Qed.
  Lemma tprop_and_elim_l G1 G2 : tprop_le (tprop_and G1 G2) G1.
  Proof. intros ??. rewrite /= /ti_and. by iIntros "[$ _]". Qed.
  Lemma tprop_and_elim_r G1 G2 : tprop_le (tprop_and G1 G2) G2.
  Proof. intros ??. rewrite /= /ti_and. by iIntros "[_ $]". Qed.

  Lemma tprop_or_mono G1 G2 G1' G2' :
    tprop_le G1 G1' → tprop_le G2 G2' → tprop_le (tprop_or G1 G2) (tprop_or G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /ti_or. by rewrite H1 H2. Qed.
  Lemma tprop_and_mono G1 G2 G1' G2' :
    tprop_le G1 G1' → tprop_le G2 G2' → tprop_le (tprop_and G1 G2) (tprop_and G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /ti_and. by rewrite H1 H2. Qed.
  (** Antecedents are compared as trace properties. *)
  Lemma tprop_impl_mono A A' G G' :
    (∀ τ, tprop_tr A' τ → tprop_tr A τ) → tprop_le G G' → tprop_le (tprop_impl A G) (tprop_impl A' G').
  Proof. intros HA HG ??. rewrite /= /ti_impl. iIntros "H %H'". iApply HG. iApply "H". eauto. Qed.
  Lemma tprop_impl_intro_le A G : tprop_le G (tprop_impl A G).
  Proof. intros ??. rewrite /= /ti_impl. by iIntros "H _". Qed.
  (** The antecedent is read on the trace, so an implication is the disjunction of its
      consequent with the negated antecedent. *)
  Lemma tprop_impl_or_not A G : tprop_le (tprop_impl A G) (tprop_or (tprop_impl A (tprop_pure False)) G).
  Proof.
    intros ? τ. rewrite /= /ti_impl /ti_or /ti_pure. iIntros "H".
    destruct (Classical_Prop.classic (tprop_tr A τ)) as [HA|HA].
    - iRight. by iApply "H".
    - iLeft. by iIntros (?).
  Qed.
  Lemma tprop_or_not_impl A G : tprop_le (tprop_or (tprop_impl A (tprop_pure False)) G) (tprop_impl A G).
  Proof.
    intros ? τ. rewrite /= /ti_impl /ti_or /ti_pure. iIntros "[H|H] %HA"; last done.
    by iDestruct ("H" $! HA) as %[].
  Qed.

  (** Antecedents compose on traces, for any antecedents: a conjunction curries, a
      disjunction splits, an existential becomes a universal. *)
  Lemma tprop_impl_curry A1 A2 G :
    tprop_le (tprop_impl A1 (tprop_impl A2 G)) (tprop_impl (tprop_and A1 A2) G).
  Proof. intros ? τ. rewrite /= /ti_impl /tr_and. iIntros "H" ([H1 H2]). by iApply "H". Qed.
  Lemma tprop_impl_uncurry A1 A2 G :
    tprop_le (tprop_impl (tprop_and A1 A2) G) (tprop_impl A1 (tprop_impl A2 G)).
  Proof. intros ? τ. rewrite /= /ti_impl /tr_and. iIntros "H" (H1 H2). by iApply "H". Qed.
  Lemma tprop_impl_or_split A1 A2 G :
    tprop_le (tprop_and (tprop_impl A1 G) (tprop_impl A2 G)) (tprop_impl (tprop_or A1 A2) G).
  Proof.
    intros ? τ. rewrite /= /ti_and /ti_impl /tr_or. iIntros "H" ([H1|H2]).
    - iDestruct "H" as "[H _]". by iApply "H".
    - iDestruct "H" as "[_ H]". by iApply "H".
  Qed.
  Lemma tprop_impl_or_join A1 A2 G :
    tprop_le (tprop_impl (tprop_or A1 A2) G) (tprop_and (tprop_impl A1 G) (tprop_impl A2 G)).
  Proof.
    intros ? τ. rewrite /= /ti_and /ti_impl /tr_or. iIntros "H".
    iSplit; iIntros (?); iApply "H"; iPureIntro; auto.
  Qed.
  Lemma tprop_impl_exist {X} `{!TypeExistentialProperty X ordI} (A : X → tprop Λ Σ) G :
    tprop_le (tprop_forall (λ x, tprop_impl (A x) G)) (tprop_impl (tprop_exist A) G).
  Proof.
    intros ? τ. rewrite /= /ti_forall /ti_impl /tr_exist. iIntros "H" ([x Hx]). by iApply ("H" $! x).
  Qed.
  Lemma tprop_forall_mono {X} (G G' : X → tprop Λ Σ) :
    (∀ x, tprop_le (G x) (G' x)) → tprop_le (tprop_forall G) (tprop_forall G').
  Proof. intros H ??. rewrite /= /ti_forall. iIntros "H %x". iApply H. iApply "H". Qed.
  Lemma tprop_exist_mono {X} `{!TypeExistentialProperty X ordI} (G G' : X → tprop Λ Σ) :
    (∀ x, tprop_le (G x) (G' x)) → tprop_le (tprop_exist G) (tprop_exist G').
  Proof. intros H ??. rewrite /= /ti_exist. iIntros "[%x H]". iExists x. by iApply H. Qed.

  Lemma tprop_always_mono G G' : tprop_le G G' → tprop_le (tprop_always G) (tprop_always G').
  Proof.
    intros Hle H τ. cbn. iIntros "H".
    iAssert (∀ τ, ti_always (tprop_ti G) (ti_pure True) τ -∗ ti_always (tprop_ti G') (ti_pure True) τ)%I
      with "[]" as "Hal"; last by iApply "Hal".
    iLöb as "IH". iIntros (τ') "H". rewrite !ti_always_unfold /ti_always_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first (iDestruct "H" as "[H _]"; by iApply Hle).
    iSplit; first by iDestruct "H" as "[_ [$ _]]".
    iDestruct "H" as "[_ [_ H]]". by iApply "IH".
  Qed.

  Lemma tprop_until_mono G1 G2 G1' G2' :
    tprop_le G1 G1' → tprop_le G2 G2' → tprop_le (tprop_until G1 G2) (tprop_until G1' G2').
  Proof.
    intros H1 H2 H τ. cbn. rewrite /ti_exist. iIntros "[%a H]". iExists a.
    iAssert (∀ a τ, ti_until Ord.lt a (tprop_ti G1) (tprop_ti G2) τ -∗
                    ti_until Ord.lt a (tprop_ti G1') (tprop_ti G2') τ)%I with "[]" as "Hu";
      last by iApply "Hu".
    iLöb as "IH". iIntros (a' τ') "H". rewrite !ti_until_unfold /ti_until_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. iDestruct "H" as "[H|H]".
    - iLeft. by iApply H2.
    - iRight. iSplit; first (iDestruct "H" as "[H _]"; by iApply H1).
      iDestruct "H" as "[_ (%a''& %Hlt& H)]". iExists a''. iSplit; first done. by iApply "IH".
  Qed.

  Lemma tprop_always_mono_i `{!temporalGS Λ Σ} (G G' : tprop Λ Σ) :
    ▷ □ (∀ τ, tprop_ti G τ -∗ tprop_ti G' τ) -∗
    ∀ τ, tprop_ti (tprop_always G) τ -∗ tprop_ti (tprop_always G') τ.
  Proof. iIntros "#W" (τ). cbn. by iApply (ti_always_mono_i with "W"). Qed.
  Lemma tprop_until_mono_i `{!temporalGS Λ Σ} (G1 G2 G1' G2' : tprop Λ Σ) :
    ▷ □ (∀ τ, tprop_ti G1 τ -∗ tprop_ti G1' τ) -∗ ▷ □ (∀ τ, tprop_ti G2 τ -∗ tprop_ti G2' τ) -∗
    ∀ τ, tprop_ti (tprop_until G1 G2) τ -∗ tprop_ti (tprop_until G1' G2') τ.
  Proof.
    iIntros "#W1 #W2" (τ). cbn. rewrite /ti_exist. iIntros "[%a H]". iExists a.
    by iApply (ti_until_mono_i with "W1 W2").
  Qed.

End tprop_connectives.

Notation "⌜ p ⌝" := (tprop_pure p) : tprop_scope.
Infix "∧" := tprop_and : tprop_scope.
Infix "∨" := tprop_or : tprop_scope.
Infix "→" := tprop_impl : tprop_scope.
Notation "∀ x .. y , G" := (tprop_forall (λ x, .. (tprop_forall (λ y, G%T)) ..)) : tprop_scope.
Notation "∃ x .. y , G" := (tprop_exist (λ x, .. (tprop_exist (λ y, G%T)) ..)) : tprop_scope.

(** ** Semantic state atoms

    Any predicate on the current state can be an atom, provided some iProp ensures it
    through the state interpretation (e.g. negated points-to facts). *)
Section state_atoms.
  Context {Λ : language} {Σ : gFunctors}.

  Program Definition tprop_state (φ : state Λ → thread_pool Λ → Prop) : tprop Λ Σ :=
    {| tprop_ti _ τ := (let '((Θ, σ), _, _) := τ.2 τ.1 in ⌜φ σ Θ⌝)%I;
       tprop_tr τ := let '((Θ, σ), _, _) := τ.2 τ.1 in φ σ Θ |}.
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
  Implicit Types G A : tprop Λ Σ.

  Class TpropComplete G : Prop :=
    tprop_complete : ∀ (H : temporalGS Λ Σ) τ, tprop_tr G τ → ⊢ @tprop_ti _ _ G H τ.
  Class TpropInstant G : Prop :=
    tprop_instant : ∀ (H : temporalGS Λ Σ) τ, @tprop_ti _ _ G H τ ⊢ ⌜tprop_tr G τ⌝.

  Lemma tprop_impl_intro A H G `{HA : !TpropComplete A} :
    tprop_le (tprop_and A H) G → tprop_le H (tprop_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /ti_impl. iIntros "H %Hτ". iApply HG.
    rewrite /= /ti_and. iSplit; last done. by iApply HA.
  Qed.

  Lemma tprop_impl_elim A G `{HA : !TpropInstant A} : tprop_le (tprop_and A (tprop_impl A G)) G.
  Proof.
    intros ? τ. rewrite /= /ti_and /ti_impl. iIntros "H".
    iAssert ⌜tprop_tr A τ⌝%I as %Hτ; first by iApply HA; iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ H]". by iApply "H".
  Qed.

  (** Completeness. *)
  Global Instance tprop_complete_pure φ : TpropComplete (tprop_pure φ).
  Proof. intros ? τ H. rewrite /= /ti_pure. by iPureIntro. Qed.
  Global Instance tprop_complete_atomic π : TpropComplete (tprop_atomic π).
  Proof.
    intros ? [n τf]. rewrite /= /ti_atomic /tr_atomic /ts_emb /ts_atomic /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). intros Hπ. iPureIntro. exact Hπ.
  Qed.
  Global Instance tprop_complete_and G1 G2 : TpropComplete G1 → TpropComplete G2 → TpropComplete (tprop_and G1 G2).
  Proof. intros H1 H2 ? τ [??]. rewrite /= /ti_and. iSplit; [by iApply H1|by iApply H2]. Qed.
  Global Instance tprop_complete_or G1 G2 : TpropComplete G1 → TpropComplete G2 → TpropComplete (tprop_or G1 G2).
  Proof. intros H1 H2 ? τ [?|?]; rewrite /= /ti_or; [iLeft; by iApply H1|iRight; by iApply H2]. Qed.
  Global Instance tprop_complete_impl A G : TpropComplete G → TpropComplete (tprop_impl A G).
  Proof. intros HG ? τ H. rewrite /= /ti_impl. iIntros (HA). iApply HG. by apply H. Qed.
  Global Instance tprop_complete_forall {X} (G : X → tprop Λ Σ) :
    (∀ x, TpropComplete (G x)) → TpropComplete (tprop_forall G).
  Proof. intros HG ? τ H. rewrite /= /ti_forall. iIntros (x). iApply HG. apply H. Qed.
  Global Instance tprop_complete_exist {X} `{!TypeExistentialProperty X ordI} (G : X → tprop Λ Σ) :
    (∀ x, TpropComplete (G x)) → TpropComplete (tprop_exist G).
  Proof. intros HG ? τ [x H]. rewrite /= /ti_exist. iExists x. by iApply HG. Qed.

  Global Instance tprop_complete_always G : TpropComplete G → TpropComplete (tprop_always G).
  Proof.
    intros HG ? τ Hτ. rewrite /=.
    iAssert (□ ∀ τ, ⌜tr_always (tprop_tr G) τ⌝ → ti_always (tprop_ti G) (ti_pure True) τ)%I as "#H";
      last by iApply "H".
    iLöb as "IH". iIntros "!>" ([n τf] Hal). rewrite ti_always_unfold /ti_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iApply ALC_intro. iMod "Hclose" as "_".
    iModIntro. iSplit.
    { iApply HG. apply (Hal n). lia. }
    iSplit; first by rewrite /ti_pure.
    iApply "IH". iPureIntro. intros m Hm. apply Hal. simpl in Hm. lia.
  Qed.

  Global Instance tprop_complete_until G1 G2 :
    TpropComplete G1 → TpropComplete G2 → TpropComplete (tprop_until G1 G2).
  Proof.
    intros H1 H2 ? [n τf] (m & Hnm & HQ & HP). rewrite /= /ti_exist.
    (* The measure is the number of steps to the right formula. *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → tprop_tr G1 (l, τf)) →
              ⊢ ti_until Ord.lt (Ord.from_nat d) (tprop_ti G1) (tprop_ti G2) (n', τf)) as Hu.
    { induction d as [|d IH]; intros n' Hd Hn' HP'; rewrite ti_until_unfold /ti_until_pre;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iNext; iMod "Hclose" as "_"; iModIntro;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iApply ALC_intro; iMod "Hclose" as "_"; iModIntro.
      - assert (m = n') as -> by lia. iLeft. by iApply H2.
      - iRight. iSplit; first (iApply H1; apply HP'; lia).
        iExists (Ord.from_nat d). iSplit; first (iPureIntro; rewrite Ord.from_nat_S; apply Ord.S_lt).
        iApply (IH (S n')); [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. lia. }
    iExists (Ord.from_nat (m - n)). iApply (Hu _ n eq_refl Hnm). intros l Hl. apply HP. lia.
  Qed.

  Global Instance tprop_complete_finally G : TpropComplete G → TpropComplete (tprop_finally G).
  Proof. intros HG. apply tprop_complete_until; [apply tprop_complete_pure|done]. Qed.

  (** Instantness. *)
  Global Instance tprop_instant_pure φ : TpropInstant (tprop_pure φ).
  Proof. intros ? τ. rewrite /= /ti_pure. by iIntros "%". Qed.
  Global Instance tprop_instant_atomic π : TpropInstant (tprop_atomic π).
  Proof.
    intros ? [n τf]. rewrite /= /ti_atomic /tr_atomic /ts_emb /ts_atomic /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). by iIntros "%".
  Qed.
  Global Instance tprop_instant_and G1 G2 : TpropInstant G1 → TpropInstant G2 → TpropInstant (tprop_and G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /ti_and. iIntros "H".
    iAssert ⌜tprop_tr G1 τ⌝%I as %?; first by iApply H1; iDestruct "H" as "[$ _]".
    iAssert ⌜tprop_tr G2 τ⌝%I as %?; first by iApply H2; iDestruct "H" as "[_ $]".
    by iPureIntro.
  Qed.
  Global Instance tprop_instant_or G1 G2 : TpropInstant G1 → TpropInstant G2 → TpropInstant (tprop_or G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /ti_or. iIntros "[H|H]".
    - iDestruct (H1 with "H") as %?. iPureIntro. by left.
    - iDestruct (H2 with "H") as %?. iPureIntro. by right.
  Qed.
  Global Instance tprop_instant_impl A G : TpropInstant G → TpropInstant (tprop_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /ti_impl. iIntros "H".
    destruct (Classical_Prop.classic (tprop_tr A τ)) as [HA|HA].
    - iDestruct (HG with "(H [//])") as %?. iPureIntro. by intros _.
    - iPureIntro. by intros ?.
  Qed.
  Global Instance tprop_instant_forall {X} (G : X → tprop Λ Σ) :
    (∀ x, TpropInstant (G x)) → TpropInstant (tprop_forall G).
  Proof.
    intros HG ? τ. rewrite /= /ti_forall /tr_forall.
    destruct (Classical_Prop.classic (∀ x, tprop_tr (G x) τ)) as [Hall|Hn]; first by iIntros "_".
    apply Classical_Pred_Type.not_all_ex_not in Hn as [x Hx].
    iIntros "H". iSpecialize ("H" $! x). iDestruct (HG with "H") as %?. done.
  Qed.
  Global Instance tprop_instant_exist {X} `{!TypeExistentialProperty X ordI} (G : X → tprop Λ Σ) :
    (∀ x, TpropInstant (G x)) → TpropInstant (tprop_exist G).
  Proof.
    intros HG ? τ. rewrite /= /ti_exist. iIntros "[%x H]". iDestruct (HG with "H") as %?.
    iPureIntro. by exists x.
  Qed.

  Global Instance tprop_complete_state φ : TpropComplete (tprop_state φ).
  Proof.
    intros ? [n τf]. rewrite /=. destruct (τf n) as (((Θ&σ)&?)&?). intros Hφ. by iPureIntro.
  Qed.
  Global Instance tprop_instant_state φ : TpropInstant (tprop_state φ).
  Proof. intros ? [n τf]. rewrite /=. destruct (τf n) as (((Θ&σ)&?)&?). by iIntros "%". Qed.

End complete.
Global Hint Mode TpropComplete - - ! : typeclass_instances.
Global Hint Mode TpropInstant - - ! : typeclass_instances.

(** ** Decided antecedents

    [TpropDecided A ψ]: at any position, [A] holds iff the configurations up to it (as the
    history records them, [trace_hist]) satisfy [ψ]. Such antecedents are decided when a
    guarantee is taken, so an implication with them is exported by a case split
    ([temporal_impl_decided] in guarantee.v). Pure facts and state atoms are decided, and
    decided properties are closed under [∧], [∨], [→], [∀] and [∃]. The temporal operators
    are not: their truth depends on the states to come ([tprop_finally_not_decided]); as
    antecedents they are used on traces ([tprop_impl_intro], with complete antecedents). *)

(** The configurations of a trace up to position [n], in the order of the history. *)
Definition trace_hist {Λ : language} (n : nat) (τf : nat → trace_state Λ) :
    list (state Λ * thread_pool Λ * list (observation Λ)) :=
  (λ m, let '((Θ, σ), _, κs) := τf m in (σ, Θ, κs)) <$> seq 0 (S n).

Lemma trace_hist_last {Λ : language} n (τf : nat → trace_state Λ) :
  last (trace_hist n τf) = Some (let '((Θ, σ), _, κs) := τf n in (σ, Θ, κs)).
Proof. by rewrite /trace_hist seq_S fmap_app last_snoc. Qed.

Section decided.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types A : tprop Λ Σ.
  Local Notation hist := (list (state Λ * thread_pool Λ * list (observation Λ))).

  Class TpropDecided A (ψ : hist → Prop) : Prop :=
    tprop_decided : ∀ n τf, tprop_tr A (n, τf) ↔ ψ (trace_hist n τf).

  (** [φ] holds of the current (last) configuration of a history. *)
  Definition hist_now (φ : state Λ → thread_pool Λ → Prop) : hist → Prop :=
    λ h, ∃ σ Θ κs, last h = Some (σ, Θ, κs) ∧ φ σ Θ.

  Global Instance tprop_decided_pure φ : TpropDecided (tprop_pure φ) (λ _, φ).
  Proof. done. Qed.
  Global Instance tprop_decided_state φ : TpropDecided (tprop_state φ) (hist_now φ).
  Proof.
    intros n τf. rewrite /hist_now trace_hist_last /=. destruct (τf n) as (((Θ&σ)&?)&κs).
    split; [intros; by eexists _, _, _|by intros (?&?&?&[= <- <- <-]&?)].
  Qed.
  Global Instance tprop_decided_atomic π :
    TpropDecided (tprop_atomic π) (hist_now (λ σ Θ, state_sat σ Θ π)).
  Proof.
    intros n τf. rewrite /hist_now trace_hist_last /= /tr_atomic /ts_emb /ts_atomic /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&κs).
    split; [intros; by eexists _, _, _|by intros (?&?&?&[= <- <- <-]&?)].
  Qed.
  Global Instance tprop_decided_and A1 A2 ψ1 ψ2 :
    TpropDecided A1 ψ1 → TpropDecided A2 ψ2 → TpropDecided (tprop_and A1 A2) (λ h, ψ1 h ∧ ψ2 h).
  Proof. intros H1 H2 n τf. specialize (H1 n τf). specialize (H2 n τf). rewrite /= /tr_and. tauto. Qed.
  Global Instance tprop_decided_or A1 A2 ψ1 ψ2 :
    TpropDecided A1 ψ1 → TpropDecided A2 ψ2 → TpropDecided (tprop_or A1 A2) (λ h, ψ1 h ∨ ψ2 h).
  Proof. intros H1 H2 n τf. specialize (H1 n τf). specialize (H2 n τf). rewrite /= /tr_or. tauto. Qed.
  Global Instance tprop_decided_impl A1 A2 ψ1 ψ2 :
    TpropDecided A1 ψ1 → TpropDecided A2 ψ2 → TpropDecided (tprop_impl A1 A2) (λ h, ψ1 h → ψ2 h).
  Proof. intros H1 H2 n τf. specialize (H1 n τf). specialize (H2 n τf). rewrite /= /tr_impl. tauto. Qed.
  Global Instance tprop_decided_forall {X} (A : X → tprop Λ Σ) (ψ : X → hist → Prop) :
    (∀ x, TpropDecided (A x) (ψ x)) → TpropDecided (tprop_forall A) (λ h, ∀ x, ψ x h).
  Proof.
    intros H n τf. rewrite /= /tr_forall. split; intros Hx x; apply (H x n τf), Hx.
  Qed.
  Global Instance tprop_decided_exist {X} `{!TypeExistentialProperty X ordI}
      (A : X → tprop Λ Σ) (ψ : X → hist → Prop) :
    (∀ x, TpropDecided (A x) (ψ x)) → TpropDecided (tprop_exist A) (λ h, ∃ x, ψ x h).
  Proof.
    intros H n τf. rewrite /= /tr_exist. split; intros [x Hx]; exists x; by apply (H x n τf).
  Qed.

  (** A finally is not decided: with a state [σ0, Θ0] outside [φ] and a state [σ1, Θ1] in
      it, two traces with the same configuration at [0] differ on [◇φ] at [0]. *)
  Lemma tprop_finally_not_decided (φ : state Λ → thread_pool Λ → Prop) σ0 Θ0 σ1 Θ1
      (i : thread_id) (κs : list (observation Λ)) (ψ : hist → Prop) :
    ¬ φ σ0 Θ0 → φ σ1 Θ1 → ¬ TpropDecided (tprop_finally (tprop_state φ)) ψ.
  Proof.
    intros H0 H1 Hd.
    set (τ1 := λ m : nat, match m with 0 => ((Θ0, σ0), i, κs) | _ => ((Θ1, σ1), i, κs) end).
    set (τ2 := λ _ : nat, ((Θ0, σ0), i, κs) : trace_state Λ).
    assert (Hh : trace_hist 0 τ1 = trace_hist 0 τ2) by done.
    assert (HF : tprop_tr (Σ:=Σ) (tprop_finally (tprop_state φ)) (0, τ1)).
    { exists 1. split_and!; [lia|done|]. intros l Hl. done. }
    apply Hd in HF. rewrite Hh in HF. apply Hd in HF.
    destruct HF as (m & _ & Hm & _). by apply H0.
  Qed.

End decided.
Global Hint Mode TpropDecided - - ! - : typeclass_instances.
