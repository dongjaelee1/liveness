From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trspec_fixpoint.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.
From lantana.prelude Require Import axioms.

(** * The model of trace specifications

    Under the assumptions of the adequacy theorem (adequacy_temporal.v), a property valid in
    the logic holds on the trace ([trSpec_valid_ext]). Hence in-logic entailment [⊑] is
    sound for the external readings of complete properties, and not complete for them; and
    a guarded fixpoint body has no fold. *)

(** ** Validity, soundness and incompleteness of [⊑] *)
Section model.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G H : trSpec Λ Σ.
  Local Notation histGpreS := (histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))).

  Lemma trSpec_valid_ext `{!mupdGpreS Σ} `{!histGpreS} `{!tregGS.tregGpreS Λ Σ} G τ :
    (∀ Ht : temporalGS Λ Σ, ⊢ trSpec_internal G τ) → trSpec_external G τ.
  Proof.
    intros HG. destruct (τ.2 τ.1) as [[[Θ σ] i] κs].
    assert (iProp_sat (|==> ∃ (Hmupd : mupdGS Σ)
                (Hhist : histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ)))
                (Htreg : tregGS.tregGS Λ Σ),
              (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗ wsat.wsat ∗ wsat.ownE ⊤))
      as Hsat.
    { eapply sat_mono; last apply iProp_sat_intro. iIntros "_".
      iMod (model_interp_alloc 0) as "(%Hmupd& R& W& WOE& _)".
      iMod (history_interp_init (Λ:=Λ) σ Θ κs) as (Hhist) "_".
      iMod (reg_alloc (Λ:=Λ)) as (Htreg) "_".
      iModIntro. iExists Hmupd, Hhist, Htreg. iFrame. }
    apply sat_bupd, sat_exists in Hsat as [Hmupd Hsat].
    apply sat_exists in Hsat as [Hhist Hsat]. apply sat_exists in Hsat as [Htreg Hsat].
    set (Htemp := TemporalG Hmupd Hhist Htreg : temporalGS Λ Σ).
    apply (trSpec_adeq G (temporalGS0:=Htemp) emp).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono; last exact Hsat. iIntros "($& $& $)". iApply (HG Htemp).
  Qed.

  (** Soundness: for a complete [G], in-logic entailment implies trace inclusion. *)
  Lemma trSpec_le_sound `{!mupdGpreS Σ} `{!histGpreS} `{!tregGS.tregGpreS Λ Σ} G G' `{!TrSpecComplete G} :
    G ⊑ G' → trSpec_external G ⊆ trSpec_external G'.
  Proof.
    intros Hle τ HG. apply trSpec_valid_ext. intros Ht. rewrite -(Hle Ht τ). by apply trSpec_complete.
  Qed.

  (** Incompleteness: [□ ⊥ ⊆ ⊥] holds on traces, but [□ ⊥ ⊑ ⊥] does not hold in the logic
      (the reading of [□ ⊥] starts with a later, so it is proved by Löb induction). *)
  Lemma trSpec_always_elim_not_le `{!mupdGpreS Σ} `{!histGpreS} `{!tregGS.tregGpreS Λ Σ} (τ : trace Λ) :
    ¬ ((□ ⌜False⌝)%SPEC ⊑ (⌜False⌝ : trSpec Λ Σ)%SPEC).
  Proof.
    intros Hle. apply (trSpec_valid_ext (trSpec_pure False) τ). intros Ht.
    iLöb as "IH". iPoseProof (Hle Ht τ with "[IH]") as "%HF"; last done.
    rewrite /= trI_always_unfold /trI_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "_". iNext. done.
  Qed.

End model.

(** ** No fold for a guarded body

    A pre-fixpoint (for [⊑]) of the guarded body [X ↦ ⊳ ⊚ ○'X] is valid by Löb induction,
    hence true on every trace, while the least fixpoint of that body on traces is empty. So
    [F (μ F) ⊑ μ F] fails for it, and likewise for [G1 𝒰 G2]. *)
Section no_fold.
  Context {Λ : language} {Σ : gFunctors}.

  Lemma trSpec_guarded_prefix_valid (M : trSpec Λ Σ) :
    trSpec_le (F_until trSpec_true (trSpec_pure False) M) M → ∀ (H : temporalGS Λ Σ) τ, ⊢ @trSpec_internal _ _ M H τ.
  Proof.
    intros HM H. cut (⊢ ∀ τ, @trSpec_internal _ _ M H τ)%I.
    { intros HM' τ. iApply HM'. }
    iLöb as "IH". iIntros (τ). iApply HM. rewrite /F_until /= /trI_or /trI_and /trI_pure.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iApply ALC_intro. iMod "Hclose" as "_".
    iModIntro. iRight. iSplit; first done. iApply "IH".
  Qed.

  (** The model: the instance is allocated as in the adequacy (adequacy_temporal.v). *)
  Lemma trSpec_guarded_prefix_ext `{!mupdGpreS Σ}
      `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
      (M : trSpec Λ Σ) τ :
    trSpec_le (F_until trSpec_true (trSpec_pure False) M) M → trSpec_external M τ.
  Proof.
    intros HM. apply trSpec_valid_ext. intros Ht. apply (trSpec_guarded_prefix_valid M HM Ht).
  Qed.

  Lemma trSpec_mu_unfold_r_guarded `{!mupdGpreS Σ}
      `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
      (τ : trace Λ) :
    ¬ trSpec_le (Λ:=Λ) (Σ:=Σ) (F_until trSpec_true (trSpec_pure False) (trSpec_mu (F_until trSpec_true (trSpec_pure False))))
             (trSpec_mu (F_until trSpec_true (trSpec_pure False))).
  Proof.
    intros Hfold. apply (trSpec_guarded_prefix_ext _ τ), trSpec_mu_until_ext in Hfold.
    destruct τ as [n τf]. by destruct Hfold as (m & _ & [] & _).
  Qed.

End no_fold.
