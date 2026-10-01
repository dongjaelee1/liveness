From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.program_logic Require Export adequacy.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.
From lantana.prelude Require Import axioms.

(** * Semantic temporal formulas

    [tf] is an inductive syntax with three interpretations defined by recursion:
    [tf_logic] (resources owned now), [tf_intuit] (a persistent snapshot of the formula at
    an event) and [tf_to_tp] (its trace property); adequacy is proved by induction on it.
    Being an inductive with constructors quantifying over [Type], it can never quantify
    over itself.

    Here a temporal formula is instead a record bundling the three interpretations with the
    two facts the adequacy proof needs about them (cf. the induction hypothesis of
    [lwp_fix_ti_logic]):
    - [tfp_snap_intro]: the resources, together with the history and model interpretations,
      give the snapshot at the current event;
    - [tfp_sound]: the snapshot, together with the running system, gives the step-indexed
      trace property [ti_logic] of the skeleton.
    Each connective is a smart constructor that proves these facts once and for all.
    The skeleton is a [tp], which must stay small for the existential property of
    transfinite step-indexing; hence quantifiers over large types (including [tfProp]
    itself and [iProp]) are "ghost" quantifiers that do not show up in the skeleton. *)

(** Snapshots are taken at an event: history index [n] with state [σ], thread pool [Θ] and
    observations [κs], and model-history index [i] with obligations [Ω]. *)
Notation snapT Λ Σ :=
  (nat → state Λ → thread_pool Λ → list (observation Λ) → nat → obls → iProp Σ) (only parsing).

Section snap_law.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Definition snap_intro_law (L : iProp Σ) (I : snapT Λ Σ) : Prop :=
    ∀ h n σ Θ κs m i Ω W,
      history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ L ⊢ I n σ Θ κs i Ω.

End snap_law.

Section laws.
  Context `{!lantanaGS Λ Σ}.

  (** The running system: every thread runs its [lwp_fix]. *)
  Definition threads_run (s : stuckness)
    (TQ : gmap thread_id ((expr Λ) * (thread_id → val Λ → iProp Σ))) : iProp Σ :=
    [∗ map] i ↦ '(e, Q) ∈ TQ, match to_val e with
                              | Some v => (lift_term i Q) v
                              | None => lwp_fix s i ⊤ e (lift_term i Q)
                              end.

  Definition sound_law (I : snapT Λ Σ) (t : @tp (state_pred Λ)) : Prop :=
    ∀ s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ,
      behavior (n, τf) →
      beh_fscnt (n, τf) γ →
      v1 ≤ v2 →
      obls_le Ω1 Ω2 →
      owit_inv_lb (fair_sched_fun γ) Ω2 W →
      (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
      Θ = fst <$> TQ →
      (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v2 Ω2 W n (dom Θ) ∗
      threads_run s TQ ∗ I n σ Θ κs v1 Ω1
      ⊢ ti_logic Ord.lt t (n, τf).

End laws.

(** The soundness law must hold whatever the postcondition of forked threads is, so that
    [tfProp] depends on the same ghost state as [tf_logic]. *)
Record tfProp {Λ Σ} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} := TfProp {
  tfp_skel : @tp (state_pred Λ);
  tfp_logic : iProp Σ;
  tfp_snap : snapT Λ Σ;
  tfp_snap_persistent n σ Θ κs i Ω : Persistent (tfp_snap n σ Θ κs i Ω);
  tfp_snap_intro : snap_intro_law tfp_logic tfp_snap;
  tfp_sound fork_post : sound_law (lantanaGS0 := LantanaG _ _ fork_post) tfp_snap tfp_skel;
}.
Global Arguments tfProp Λ Σ {_ _}.
Global Arguments TfProp {Λ Σ _ _}.
Global Arguments tfp_skel {Λ Σ _ _}.
Global Arguments tfp_logic {Λ Σ _ _}.
Global Arguments tfp_snap {Λ Σ _ _}.
Global Arguments tfp_sound {Λ Σ _ _}.
Global Existing Instance tfp_snap_persistent.

Declare Scope tfp_scope.
Delimit Scope tfp_scope with T.
Bind Scope tfp_scope with tfProp.

Notation "'⟦' Φ '⟧ₛ'" := (tfp_logic Φ%T) (format "'⟦' Φ '⟧ₛ'").

(** ** Connectives *)
Section connectives.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types A B : tfProp Λ Σ.

  Program Definition tfp_emp : tfProp Λ Σ :=
    {| tfp_skel := tp_true; tfp_logic := (emp)%I; tfp_snap _ _ _ _ _ _ := (emp)%I |}.
  Next Obligation. iIntros (?????????) "_". done. Qed.
  Next Obligation. iIntros (???????????????????????) "_". done. Qed.

  Program Definition tfp_atomic (π : state_pred Λ) : tfProp Λ Σ :=
    {| tfp_skel := tp_atomic π; tfp_logic := (state_pred_interp π)%I;
       tfp_snap n σ Θ κs _ _ := (event_pred n σ Θ κs π)%I |}.
  Next Obligation.
    iIntros (??????????) "(HI& _& TL)". rewrite /history_interp. iDestruct "HI" as "(HI1& HI2& SI)".
    iPoseProof (state_interp_wf with "[$SI $TL]") as "%".
    iApply (history_interp_event_pred_now with "[HI1 HI2 SI]"). 1: auto.
    rewrite /history_interp. iFrame.
  Qed.
  Next Obligation.
    iIntros (π fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    unfold ti_atomic. iPoseProof (event_pred_history_interp_lookup with "[$HI $TF]") as "%H".
    destruct H as [H ?]. simpl. apply HIST in H. destruct H as [? H]. rewrite H. auto.
  Qed.

  Program Definition tfp_pure (p : Prop) : tfProp Λ Σ :=
    {| tfp_skel := tp_pure p; tfp_logic := (⌜p⌝)%I; tfp_snap _ _ _ _ _ _ := (⌜p⌝)%I |}.
  Next Obligation. iIntros (??????????) "(_& _& $)". Qed.
  Next Obligation. iIntros (????????????????????????) "(_& _& _& $)". Qed.

  (** Pure ghost: resources that are invisible in the trace. *)
  Program Definition tfp_ghost (P : iProp Σ) : tfProp Λ Σ :=
    {| tfp_skel := tp_true; tfp_logic := (P)%I; tfp_snap _ _ _ _ _ _ := (True)%I |}.
  Next Obligation. iIntros (??????????) "_". done. Qed.
  Next Obligation. iIntros (????????????????????????) "_". done. Qed.

  Program Definition tfp_and A B : tfProp Λ Σ :=
    {| tfp_skel := tp_and (tfp_skel A) (tfp_skel B);
       tfp_logic := (⟦A⟧ₛ ∧ ⟦B⟧ₛ)%I;
       tfp_snap n σ Θ κs i Ω := (tfp_snap A n σ Θ κs i Ω ∧ tfp_snap B n σ Θ κs i Ω)%I |}.
  Next Obligation.
    iIntros (A B ?????????) "(HI& MI& TL)". iSplit.
    - iDestruct "TL" as "[TL _]". iApply tfp_snap_intro. iFrame.
    - iDestruct "TL" as "[_ TL]". iApply tfp_snap_intro. iFrame.
  Qed.
  Next Obligation.
    iIntros (A B fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    unfold ti_and. iSplit.
    + iDestruct "TF" as "[TF _]". iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF]"); eauto.
    + iDestruct "TF" as "[_ TF]". iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF]"); eauto.
  Qed.

  Program Definition tfp_or A B : tfProp Λ Σ :=
    {| tfp_skel := tp_or (tfp_skel A) (tfp_skel B);
       tfp_logic := (⟦A⟧ₛ ∨ ⟦B⟧ₛ)%I;
       tfp_snap n σ Θ κs i Ω := (tfp_snap A n σ Θ κs i Ω ∨ tfp_snap B n σ Θ κs i Ω)%I |}.
  Next Obligation.
    iIntros (A B ?????????) "(HI& MI& [TL | TL])".
    - iLeft. iApply tfp_snap_intro. iFrame.
    - iRight. iApply tfp_snap_intro. iFrame.
  Qed.
  Next Obligation.
    iIntros (A B fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    unfold ti_or. iDestruct "TF" as "[TF | TF]".
    + iLeft. iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF]"); eauto.
    + iRight. iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF]"); eauto.
  Qed.

  (** As for [tf_impl], only pure antecedents. *)
  Program Definition tfp_impl (p : Prop) B : tfProp Λ Σ :=
    {| tfp_skel := tp_impl p (tfp_skel B);
       tfp_logic := (⌜p⌝ → ⟦B⟧ₛ)%I;
       tfp_snap n σ Θ κs i Ω := (⌜p⌝ → tfp_snap B n σ Θ κs i Ω)%I |}.
  Next Obligation.
    iIntros (p B ?????????) "(HI& MI& TL) %Hp". iApply tfp_snap_intro. iFrame. by iApply "TL".
  Qed.
  Next Obligation.
    iIntros (p B fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    unfold ti_impl. iIntros "%Hp". iPoseProof ("TF" with "[//]") as "#TF'".
    iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF']"); eauto.
  Qed.

  (** Trace-visible quantifiers: [X] must be small, since it appears in the skeleton. *)
  Program Definition tfp_forall (X : Type) (Φ : X → tfProp Λ Σ) : tfProp Λ Σ :=
    {| tfp_skel := tp_forall X (λ x, tfp_skel (Φ x));
       tfp_logic := (∀ x, ⟦Φ x⟧ₛ)%I;
       tfp_snap n σ Θ κs i Ω := (∀ x, tfp_snap (Φ x) n σ Θ κs i Ω)%I |}.
  Next Obligation.
    iIntros (X Φ ?????????) "(HI& MI& TL) %x". iApply tfp_snap_intro. iFrame. iApply "TL".
  Qed.
  Next Obligation.
    iIntros (X Φ fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    unfold ti_forall. iIntros (x). iSpecialize ("TF" $! x).
    iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF]"); eauto.
  Qed.

  Program Definition tfp_exist (X : Type) (Φ : X → tfProp Λ Σ) : tfProp Λ Σ :=
    {| tfp_skel := tp_exist X (λ x, tfp_skel (Φ x));
       tfp_logic := (∃ x, ⟦Φ x⟧ₛ)%I;
       tfp_snap n σ Θ κs i Ω := (∃ x, tfp_snap (Φ x) n σ Θ κs i Ω)%I |}.
  Next Obligation.
    iIntros (X Φ ?????????) "(HI& MI& [%x TL])". iExists x. iApply tfp_snap_intro. iFrame.
  Qed.
  Next Obligation.
    iIntros (X Φ fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    unfold ti_exist. iDestruct "TF" as (x) "TF". iExists x.
    iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF]"); eauto.
  Qed.

  Program Definition tfp_sep A B : tfProp Λ Σ :=
    {| tfp_skel := tp_and (tfp_skel A) (tfp_skel B);
       tfp_logic := (⟦A⟧ₛ ∗ ⟦B⟧ₛ)%I;
       tfp_snap n σ Θ κs i Ω := (tfp_snap A n σ Θ κs i Ω ∗ tfp_snap B n σ Θ κs i Ω)%I |}.
  Next Obligation.
    iIntros (A B ?????????) "(HI& MI& TL1& TL2)".
    iPoseProof (tfp_snap_intro A with "[$HI $MI $TL1]") as "#$".
    iPoseProof (tfp_snap_intro B with "[$HI $MI $TL2]") as "#$".
  Qed.
  Next Obligation.
    iIntros (A B fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF1& #TF2)". simpl.
    unfold ti_and. iSplit.
    + iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF1]"); eauto.
    + iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF2]"); eauto.
  Qed.

  (** Ghost quantifiers: [X] can be any type, e.g. [tfProp Λ Σ] or [iProp Σ]. The bound
      variable is invisible at the trace level, so only the witnesses whose skeleton is the
      given [t] count. This is the pattern of [lwp_adequacy]'s
      [∃ Φ', ⌜tf_to_tp Φ' = Φ⌝ ∗ ⟦Φ'⟧ₗ], turned into a connective. *)
  Program Definition tfp_gexist {X : Type} (Φ : X → tfProp Λ Σ) (t : @tp (state_pred Λ)) : tfProp Λ Σ :=
    {| tfp_skel := t;
       tfp_logic := (∃ x, ⌜tfp_skel (Φ x) = t⌝ ∗ ⟦Φ x⟧ₛ)%I;
       tfp_snap n σ Θ κs i Ω := (∃ x, ⌜tfp_skel (Φ x) = t⌝ ∗ tfp_snap (Φ x) n σ Θ κs i Ω)%I |}.
  Next Obligation.
    iIntros (X Φ t ?????????) "(HI& MI& (%x& %Ht& TL))". iExists x. iSplit; first done.
    iApply tfp_snap_intro. iFrame.
  Qed.
  Next Obligation.
    iIntros (X Φ t fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)".
    iDestruct "TF" as (x <-) "TF". iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF]"); eauto.
  Qed.

  (** The trace meaning of a ghost universal is [t], provided some witness has skeleton [t]. *)
  Program Definition tfp_gforall {X : Type} (Φ : X → tfProp Λ Σ) (t : @tp (state_pred Λ)) : tfProp Λ Σ :=
    {| tfp_skel := tp_impl (∃ x, tfp_skel (Φ x) = t) t;
       tfp_logic := (∀ x, ⌜tfp_skel (Φ x) = t⌝ → ⟦Φ x⟧ₛ)%I;
       tfp_snap n σ Θ κs i Ω := (∀ x, ⌜tfp_skel (Φ x) = t⌝ → tfp_snap (Φ x) n σ Θ κs i Ω)%I |}.
  Next Obligation.
    iIntros (X Φ t ?????????) "(HI& MI& TL) %x %Ht". iApply tfp_snap_intro. iFrame. by iApply "TL".
  Qed.
  Next Obligation.
    iIntros (X Φ t fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)".
    simpl. unfold ti_impl. iIntros ([x Ht]). iPoseProof ("TF" $! x with "[//]") as "#TF'".
    rewrite -Ht. iApply (tfp_sound with "[$HI $SIa $MI $WPs $TF']"); eauto.
  Qed.

End connectives.

(** ** Temporal connectives

    The soundness of [always] and [until] is the corresponding case of [lwp_fix_ti_logic],
    with the induction hypotheses replaced by the laws of the arguments. *)

(** The obligation invariant of [until] keeps, once discharged, a snapshot of the right
    formula taken at the discharge event. *)
Notation until_disch k I2 :=
  (∃ n' σ' Θ' κs' i' Ω', event_obl i' (n', Ω') k obl_discharged ∗
                         hG_event n' (σ', Θ', κs') ∗ I2 n' σ' Θ' κs' i' Ω')%I (only parsing).

Section temporal.
  Context `{!lantanaGS Λ Σ}.

  Lemma sound_always N (L : iProp Σ) (I : snapT Λ Σ) (t : @tp (state_pred Λ)) :
    (∀ n σ Θ κs i Ω, Persistent (I n σ Θ κs i Ω)) →
    snap_intro_law L I → sound_law I t →
    sound_law (λ _ _ _ _ _ _, inv N L) (tp_always t).
  Proof.
    intros Hpers Hintro Hsound. unfold sound_law, snap_intro_law, threads_run in *.
    iIntros (s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    clear dependent v1 Ω1. rename v2 into v, Ω2 into Ω.
    iRevert (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ) "TF HI SIa MI WPs".
    iLöb as "IH". iIntros (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ) "#TF HI SIa MI WPs".
    rewrite ti_always_unfold /ti_always_pre.
    iMod (inv_acc with "TF") as "[HP ACC]". 1: set_solver.
    iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext.
    iPoseProof (Hintro with "[$HI $MI $HP]") as "#TFP".
    iMod "close" as "_". iMod ("ACC" with "HP") as "_". iModIntro. iSplit.
    { iApply (Hsound with "[$HI $SIa $MI $WPs $TFP]"); eauto. done. }
    (** Fetch the scheduled thread and take a step. *)
    inversion BEH. clear BEH. subst n0 τf0.
    iPoseProof (history_interp_lookup with "HI") as "%LUhn". apply HIST in LUhn. destruct LUhn as (i'&LUhn).
    rewrite H1 in LUhn. inversion LUhn. clear LUhn. subst ρ1 i' κs.
    rename κs0 into κs, H1 into TRn, H3 into TRn1, H4 into BEH.
    iAssert ([∗ map] i ↦ e ∈ Θ, match to_val e with | Some _ => (thP_done i) | None => True end)%I as "#THs".
    { subst. iApply big_sepM_fmap. iApply (big_sepM_impl with "WPs").
      iIntros "!> %%% H". destruct x. simpl. destruct (to_val e); auto. iDestruct "H" as "[$ _]". }
    iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    destruct H2 as [TStep | TDone].
    + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TStep. clear TStep. inversion H. clear H. subst Θ0 σ ρ2. rename H1 into PStep, H0 into LUTi1.
      assert (LUTQi1 : ∃ Q, TQ !! i1 = Some (e1, Q)).
      { subst Θ. rewrite lookup_fmap_Some in LUTi1. destruct LUTi1 as (?&?&?). destruct x. subst. eauto. }
      destruct LUTQi1 as (Q& LUTQi1). iPoseProof (big_sepM_delete _ _ _ _ LUTQi1 with "WPs") as "[WP WPs]".
      pose proof (val_stuck _ _ _ _ _ _ _ _ PStep) as He1. rewrite He1.
      iPoseProof (lwp_fix_unfold_fix with "WP") as "WP". rewrite /lwp_pre He1 /lwp_step.
      iSpecialize ("WP" $! ctx_id). iEval (rewrite !ctx_id_apply) in "WP".
      iMod ("WP" with "[] [//] [$HI $SIa]") as "WP".
      { iPureIntro. apply _. }
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
      iMod (model_interp_gupd_steps with "WP MI") as "(WP& %g0& %v0& %Ω0 & %W0& %& MI)".
      2: eapply LB.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [OND LB0].
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv0".
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA0". 1,2: eauto.
      iDestruct "WP" as "[%NStuck WP]".
      iPoseProof ("WP" with "[//]") as "WP".
      iEval (rewrite !ctx_id_apply) in "WP". rewrite /mprog.
      iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
      unshelve epose proof (mprog_exists_step i1 Ω0 Ω2 W0 (n, τf) γ _ OTA0 OWinv0 LB0 FS ProgO).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
      iMod ("WP" $! W2 with "[]") as "[MI WP]".
      { iPureIntro. split; auto. }
      rewrite /mphys. iMod ("WP" with "MI") as "[MI WP]". iModIntro. iSplit. 1: done.
      iMod "WP". simpl.
      iMod (model_interp_mupd_steps with "WP MI") as "(WP& %g'& %v'& %Ω3& %W3& %& MI)".
      2: eapply LB2.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [LEO LB3]. iMod "WP" as "(HI& WP& Efs)".
      unfold trace_next in *. simpl in *. assert (TDisj : Θ ##ₘ efs).
      { eapply map_disjoint_dom_2, fork_thread_ids; eauto. }
      remember ((<[i1:=e2]> Θ) ∪ efs) as Θ2.
      replace (dom (<[i1:=e2]> Θ) ∪ dom efs) with (dom Θ2); cycle 1.
      { subst Θ2. rewrite dom_union_L. auto. }
      remember ((λ e, (e, fork_post)) <$> efs : gmap thread_id (expr Λ * (thread_id → val Λ → iProp Σ))) as TQefs.
      iAssert ([∗ map] j ↦ '(e, Q) ∈ TQefs, lwpupd j ⊤ e (match to_val e with
                                                          | Some v => lift_term j Q v
                                                          | None => lwp_fix s j ⊤ e (lift_term j Q)
                                                          end))%I with "[Efs]" as "Efs".
      { subst TQefs. iApply big_sepM_fmap. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% WP".
        destruct (to_val x) eqn:EQx.
        - rewrite lwp_fix_unfold_fix /lwp_pre EQx. iMod "WP".
          iApply sfmupd_lwpupd. iMod "WP". by iModIntro.
        - iApply "WP". }
      iMod (all_interp_lwpupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)".
      { subst Θ2 TQefs. rewrite -map_fmap_compose. unfold compose. simpl. rewrite map_fmap_id.
        apply map_union_subseteq_r. apply map_disjoint_insert_l_2; auto. apply not_elem_of_dom.
        apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. }
      1: auto. destruct H as [LEO2 LB4]. destruct (to_val e2) eqn:He2.
      * rewrite lwp_fix_unfold_fix /lwp_pre He2.
        iDestruct "HI" as "[HI SIa]".
        iMod (all_interp_sfgupd_steps with "WP HI MI") as "(WP& HI& %g3& %v3& %Ω5& %W5& %& MI)".
        2: eapply LB4.
        { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
        destruct H as [LEO3 LB5].
        iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix s j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union.
          { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
            apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        iPoseProof ("IH" with "[] [] [] [] [] TF HI SIa MI WPs") as "H".
        1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H1 TRn1. eauto. }
        { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
        iModIntro. iFrame.
      * iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix s j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union.
          { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
            apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iDestruct "HI" as "[HI SIa]".
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        iPoseProof ("IH" with "[] [] [] [] [] TF HI SIa MI WPs") as "H".
        1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H1 TRn1. eauto. }
        { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
        iModIntro. iFrame.
    + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TDone. clear TDone. inversion H. clear H. subst Θ0 σ1 ρ2.
      destruct H1 as (He1&<-&<-&->&->). destruct He1 as [v1 He1]. simpl in *.
      rewrite map_union_empty insert_id in TRn1. 2: auto.
      iPoseProof (history_interp_step with "HI") as "[SI ACC]". iMod ("ACC" with "SI") as "HI".
      pose proof (exists_fscnt_next _ _ FS). destruct H as (γ2& FS2& FSrel).
      unfold trace_next in *. simpl in *.
      assert (TNow : trace_thread (n, τf) = i1).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      assert (TNA : ts_emb (thread_na i1) (n, τf)).
      { unfold ts_emb, thread_na. simpl. rewrite TRn. right. eauto. }
      rewrite -TNow in TNA. pose proof (owit_inv_lb_step_na_turn _ _ _ _ _ TNA OTA LB FSrel) as LB2.
      iDestruct "MI" as "[MHI MI]". iMod (model_history_interp_step _ _ _ (S n) with "MHI") as "MHI".
      1: lia. 1: reflexivity.
      iPoseProof (history_interp_wf with "HI") as "%HistWF".
      iPoseProof ("IH" with "[] [] [] [] [] TF HI SIa [$MHI $MI] WPs") as "H".
      1: eauto. 1: eauto. 1: eauto.
      { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
        - inv H. eapply HIST in LUh. eauto.
        - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
          inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
          destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
          rewrite H2 TRn1. eauto. }
      1: eauto.
      iApply fupd_mask_intro. 1: set_solver. iIntros "close". iSplit. 1: done.
      iModIntro. iMod "close" as "_". iModIntro. iFrame.
  Qed.

  Lemma sound_until N k (L1 : iProp Σ) (I1 : snapT Λ Σ) (t1 : @tp (state_pred Λ))
    (L2 : iProp Σ) (I2 : snapT Λ Σ) (t2 : @tp (state_pred Λ)) :
    (∀ n σ Θ κs i Ω, Persistent (I1 n σ Θ κs i Ω)) →
    (∀ n σ Θ κs i Ω, Persistent (I2 n σ Θ κs i Ω)) →
    snap_intro_law L1 I1 → sound_law I1 t1 →
    snap_intro_law L2 I2 → sound_law I2 t2 →
    sound_law (λ n σ Θ κs i Ω, ((∃ f o, event_obl i (n, Ω) k (obl_assigned f o)) ∗
                                 oblP_inv N k L1 L2 (until_disch k I2))%I)
      (tp_until t1 t2).
  Proof.
    intros Hpers1 Hpers2 Hintro1 Hsound1 Hintro2 Hsound2.
    unfold sound_law, snap_intro_law, threads_run in *.
    iIntros (s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    rewrite /ti_exist. iDestruct "TF" as "[(%&%&#EA) #TF]".
    iPoseProof (event_obl_model_history_interp_lookup with "[MI $EA]") as "%".
    { iDestruct "MI" as "[$ _]". }
    simpl in H. destruct H as (LUMHv1& LUOk1& _). pose proof LEO as LEO2. destruct LEO2. clear H0.
    assert (is_Some (Ω2 !! k)).
    { apply elem_of_dom. apply elem_of_dom_2 in LUOk1. set_solver + LUOk1 H. }
    clear H. destruct H0 as [x LUOk2]. destruct x; cycle 1.
    { clear Hsound1. iExists Ord.O. rewrite ti_until_unfold /ti_until_pre. iLeft.
      iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
      iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
      iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]".
      { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
        iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk2 in H. inv H. }
      { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
        iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk2 in H. inv H. }
      iDestruct "Var" as "(#Of& %&%&%&%&%&%& #EF& #HE& #TF2)".
      iPoseProof (event_obl_model_history_interp_lookup with "[MI $EF]") as "%".
      { iDestruct "MI" as "[$ _]". }
      simpl in H. destruct H as (LUMHi'& LUOk'& LEi'& LEn'& LEO').
      destruct (le_gt_dec v1 i'); cycle 1.
      { iPoseProof (event_obl_compare i' v1 with "[$EF $EA]") as "%". 1: lia.
        simpl in H. destruct H as (?&?&?). done. }
      iPoseProof (event_obl_compare v1 i' with "[$EA $EF]") as "%". 1: auto.
      simpl in H. destruct H as (LEn'2& LEO'2& _). rename l into LEv1.
      assert (n' = n) by lia. subst n'. clear LEn' LEn'2.
      iPoseProof (history_interp_hG_event_lookup with "[$HI $HE]") as "%".
      iPoseProof (history_interp_lookup with "HI") as "%". rewrite H in H0. inversion H0. clear H H0. subst σ' Θ' κs'.
      iPoseProof (Hsound2 with "[$HI $SIa $MI $WPs $TF2]") as "HA".
      1: eapply BEH. 1: eapply FS. 1,2,3,4,5: eauto.
      iMod ("ACC" with "[]") as "_".
      { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of EF HE TF2". }
      iModIntro. iFrame. }
    iClear "EA". clear dependent Ω1 f o v1. rename v2 into v, Ω2 into Ω, LUOk2 into LUOk.
    pose proof LB. specialize (H k). rewrite LUOk in H. inversion H. clear H. destruct y; last done. subst x.
    rename H1 into LUWk, H2 into LEwit. symmetry in LUWk.
    iExists wit. clear LUWk.
    (** Induction on wit. *)
    iRevert (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ fuel owner LUOk LEwit) "TF HI SIa MI WPs".
    iInduction wit as [w IH] using (well_founded_ind Ord.lt_well_founded).
    iIntros (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ fuel owner LUOk LEwit) "#TF HI SIa MI WPs".
    rewrite ti_until_unfold /ti_until_pre.
    iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
    iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
    iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]"; cycle 1.
    { iPoseProof (Hintro2 with "[$HI $MI $HQ]") as "#TFQ". iMod ("ACC" with "[Var HQ]") as "_".
      { iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame. }
      iModIntro. iLeft. iApply (Hsound2 with "[$HI $SIa $MI $WPs $TFQ]"); eauto. done. }
    { iDestruct "Var" as "[OF _]". iDestruct "MI" as "(MHI& S& MI)".
      iEval (unfold_opreds) in "OF". iDestruct "OF" as "(#OE& #OF)".
      iPoseProof (osat_lookup_discharged with "[$S $OE $OF]") as "%". rewrite LUOk in H. inv H. }
    iPoseProof (Hintro1 with "[$HI $MI $HP]") as "#TFP". iMod ("ACC" with "[Var HP]") as "_".
    { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
    iModIntro. iRight. iSplit.
    { iApply (Hsound1 with "[$HI $SIa $MI $WPs $TFP]"); eauto. done. }
    (** Fetch the scheduled thread and take a step. *)
    inversion BEH. clear BEH. subst n0 τf0.
    iPoseProof (history_interp_lookup with "HI") as "%LUhn". apply HIST in LUhn. destruct LUhn as (i'&LUhn).
    rewrite H1 in LUhn. inversion LUhn. clear LUhn. subst ρ1 i' κs.
    rename κs0 into κs, H1 into TRn, H3 into TRn1, H4 into BEH.
    iAssert ([∗ map] i ↦ e ∈ Θ, match to_val e with | Some _ => (thP_done i) | None => True end)%I as "#THs".
    { subst. iApply big_sepM_fmap. iApply (big_sepM_impl with "WPs").
      iIntros "!> %%% H". destruct x. simpl. destruct (to_val e); auto. iDestruct "H" as "[$ _]". }
    iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    destruct H2 as [TStep | TDone].
    + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TStep. clear TStep. inversion H. clear H. subst Θ0 σ ρ2. rename H1 into PStep, H0 into LUTi1.
      assert (LUTQi1 : ∃ Q, TQ !! i1 = Some (e1, Q)).
      { subst Θ. rewrite lookup_fmap_Some in LUTi1. destruct LUTi1 as (?&?&?). destruct x. subst. eauto. }
      destruct LUTQi1 as (Q& LUTQi1). iPoseProof (big_sepM_delete _ _ _ _ LUTQi1 with "WPs") as "[WP WPs]".
      pose proof (val_stuck _ _ _ _ _ _ _ _ PStep) as He1. rewrite He1.
      iPoseProof (lwp_fix_unfold_fix with "WP") as "WP". rewrite /lwp_pre He1 /lwp_step.
      iSpecialize ("WP" $! ctx_id). iEval (rewrite !ctx_id_apply) in "WP".
      iMod ("WP" with "[] [//] [$HI $SIa]") as "WP".
      { iPureIntro. apply _. }
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
      iMod (model_interp_gupd_steps with "WP MI") as "(WP& %g0& %v0& %Ω0 & %W0& %& MI)".
      2: eapply LB.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [OND LB0].
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv0".
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA0". 1,2: eauto.
      iDestruct "WP" as "[%NStuck WP]".
      iPoseProof ("WP" with "[//]") as "WP".
      iEval (rewrite !ctx_id_apply) in "WP". rewrite /mprog.
      iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
      unshelve epose proof (mprog_exists_step i1 Ω0 Ω2 W0 (n, τf) γ _ OTA0 OWinv0 LB0 FS ProgO).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
      iMod ("WP" $! W2 with "[]") as "[MI WP]".
      { iPureIntro. split; auto. }
      assert (∃ fuel0 owner0, Ω0 !! k = Some (obl_assigned fuel0 owner0) ∧ (fuel0 w≤ fuel) ∧
                              (fair_sched_fun γ owner0 fuel0 w≤ fair_sched_fun γ owner fuel)).
      { destruct OND. assert (is_Some (Ω0 !! k)).
        { apply elem_of_dom. apply elem_of_dom_2 in LUOk. set_solver + LUOk H. }
        destruct H1. specialize (H0 _ _ _ LUOk H1). destruct x; simpl in H0; [|done]. destruct H0.
        - destruct H0. subst. exists fuel0, owner0. split_and !; eauto.
          apply Hessenberg.le_add_l. apply Jacobsthal.le_mult_r. auto.
        - exists fuel0, owner0. split_and !; eauto. 1: eapply WFOCM.lt_le; eauto.
          eapply WFOCM.lt_le, fair_sched_fun_mon; auto. }
      destruct H as (fuel0&owner0&LUOk0& LEfuel0& FSLEfuel0).
      assert (∃ fuel' owner', Ω2 !! k = Some (obl_assigned fuel' owner')).
      { destruct ProgO. specialize (H0 k). rewrite LUOk0 in H0. inv H0. destruct y; by eauto. }
      destruct H as (fuel2&owner2&LUOk2).
      destruct (ts_emb_thread_active_or_not owner2 (n, τf)) as [TN2 | TA2].
      { iExFalso. iDestruct "MI" as "(MHI& S& T& A& G& W& %OWInv)".
        unfold ts_emb, thread_na in TN2. simpl in TN2. rewrite TRn in TN2.
        iPoseProof (othread_assigned_thread_elem with "[$S $T $A]") as "%INk". 1: eapply LUOk2.
        destruct TN2.
        { apply not_elem_of_dom in H. done. }
        destruct H as (?&?&?). destruct H0. destruct (decide (i1 = owner2)).
        { subst i1. rewrite LUTi1 in H. inv H. }
        assert (LUTQ2 : ∃ Q2, TQ !! owner2 = Some (x, Q2)).
        { subst Θ. rewrite lookup_fmap_Some in H. destruct H as (?&?&?). destruct x1. subst. eauto. }
        destruct LUTQ2 as (Q2& LUTQ2). assert (delete i1 TQ !! owner2 = Some (x, Q2)).
        { rewrite lookup_delete_ne; auto. }
        iPoseProof (big_sepM_delete _ _ _ _ H1 with "WPs") as "[WP' WPs]". rewrite H0.
        iDestruct "WP'" as "(#Term& HQ)". iPoseProof (othread_assigned_done_false with "[$S $T $A]") as "%"; eauto.
        unfold_opreds. auto. }
      (** Resume the step. *)
      rewrite /mphys. iMod ("WP" with "MI") as "[MI WP]". iModIntro.
      (** Checkpoint Ω2 is asssigend. *)
      iPoseProof (model_history_interp_event_obl_now with "[MI]") as "#EA".
      1: eapply LUOk2.
      { iDestruct "MI" as "[$ _]". }
      assert (HDrop : (fair_sched_fun γ2 owner2 fuel2 < fair_sched_fun γ owner fuel)%ord).
      { destruct ProgO as [StepO KeepO]. specialize (StepO k). rewrite LUOk0 LUOk2 in StepO.
        inv StepO. simpl in H1. destruct H1.
        - destruct H. subst i1. inv H0; inv H. apply fair_sched_fun_mon_gen; auto.
          eapply WFOCM.lt_le_lt; eauto.
        - eapply WFOCM.lt_le_lt; last eapply FSLEfuel0.
          destruct H. inv H0. specialize (FSrel owner2). unfold fscnt_next_rel_th in FSrel.
          rewrite decide_False in FSrel; cycle 1.
          { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
          rewrite decide_False in FSrel.
          { apply Hessenberg.lt_add_r. apply OrdArith.lt_from_nat. auto. }
          intros F. eapply (thread_active_and_not_false _ _ F TA2). }
      assert (HDropw : (fair_sched_fun γ2 owner2 fuel2 < w)%ord).
      { eapply Ord.lt_le_lt; last eapply LEwit. auto. }
      iExists _. iSplit; first eauto.
      iMod "WP". simpl.
      iMod (model_interp_mupd_steps with "WP MI") as "(WP& %g'& %v'& %Ω3& %W3& %& MI)".
      2: eapply LB2.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [LEO LB3]. iMod "WP" as "(HI& WP& Efs)".
      unfold trace_next in *. simpl in *. assert (TDisj : Θ ##ₘ efs).
      { eapply map_disjoint_dom_2, fork_thread_ids; eauto. }
      remember ((<[i1:=e2]> Θ) ∪ efs) as Θ2.
      replace (dom (<[i1:=e2]> Θ) ∪ dom efs) with (dom Θ2); cycle 1.
      { subst Θ2. rewrite dom_union_L. auto. }
      remember ((λ e, (e, fork_post)) <$> efs : gmap thread_id (expr Λ * (thread_id → val Λ → iProp Σ))) as TQefs.
      iAssert ([∗ map] j ↦ '(e, Q) ∈ TQefs, lwpupd j ⊤ e (match to_val e with
                                                          | Some v => lift_term j Q v
                                                          | None => lwp_fix s j ⊤ e (lift_term j Q)
                                                          end))%I with "[Efs]" as "Efs".
      { subst TQefs. iApply big_sepM_fmap. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% WP".
        destruct (to_val x) eqn:EQx.
        - rewrite lwp_fix_unfold_fix /lwp_pre EQx. iMod "WP".
          iApply sfmupd_lwpupd. iMod "WP". by iModIntro.
        - iApply "WP". }
      iMod (all_interp_lwpupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)".
      { subst Θ2 TQefs. rewrite -map_fmap_compose. unfold compose. simpl. rewrite map_fmap_id.
        apply map_union_subseteq_r. apply map_disjoint_insert_l_2; auto. apply not_elem_of_dom.
        apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. }
      1: auto. destruct H as [LEO2 LB4]. destruct (to_val e2) eqn:He2.
      (* iMod (all_interp_lwpupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)". *)
      (* { subst Θ2 TQefs. rewrite -map_fmap_compose. unfold compose. simpl. rewrite map_fmap_id. *)
      (*   apply map_union_subseteq_r. apply map_disjoint_insert_l_2; auto. apply not_elem_of_dom. *)
      (*   apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. } *)
      (* 1: auto. destruct H as [LEO2 LB4]. destruct (to_val e2) eqn:He2. *)
      * rewrite lwp_fix_unfold_fix /lwp_pre He2.
        iDestruct "HI" as "[HI SIa]".
        iMod (all_interp_sfgupd_steps with "WP HI MI") as "(WP& HI& %g3& %v3& %Ω5& %W5& %& MI)".
        2: eapply LB4.
        { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
        destruct H as [LEO3 LB5].
        (* iMod (all_interp_lwpupd_steps with "WP HI MI") as "(WP& HI& %g3& %v3& %Ω5& %W5& %& MI)". *)
        (* { subst Θ2. rewrite lookup_union_l. *)
        (*   - apply lookup_insert_eq. *)
        (*   - apply not_elem_of_dom. apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. } *)
        (* 1: eapply LB4. destruct H as [LEO3 LB5]. *)
        iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix s j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union.
          { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
            apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        assert (LEO5 : obls_le Ω2 Ω5).
        { etrans; first eauto. etrans; first eauto. apply obls_nd_obls_le; auto. }
        destruct (Ω5 !! k) eqn:LUOk5; cycle 1.
        { apply elem_of_dom_2 in LUOk2. destruct LEO5. apply not_elem_of_dom in LUOk5. set_solver + LUOk2 H LUOk5. }
        destruct o.
        { iPoseProof ("IH" $! (fair_sched_fun γ2 owner2 fuel2) with "[] [] [] [] [] [] [] [] TF HI SIa MI WPs") as "H".
          1: eauto. 1: eauto. 1: eauto. 1: eauto.
          { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
            - inv H. eapply HIST in LUh. eauto.
            - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
              inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
              destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
              rewrite H1 TRn1. eauto. }
          { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
          1: eauto.
          { iPureIntro. destruct LEO5. specialize (H0 _ _ _ LUOk2 LUOk5). destruct H0.
            - destruct H0. subst. apply Hessenberg.le_add_l, Jacobsthal.le_mult_r. auto.
            - eapply Ord.lt_le, fair_sched_fun_mon_gen. auto. }
          iModIntro. iFrame. }
        { clear Hsound1. iModIntro. rewrite ti_until_unfold /ti_until_pre. iLeft.
          iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
          iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
          iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]".
          { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
            iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk5 in H. inv H. }
          { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
            iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk5 in H. inv H. }
          iDestruct "Var" as "(#Of& %&%&%&%&%&%& #EF& #HE& #TF2)".
          iPoseProof (event_obl_model_history_interp_lookup with "[MI $EF]") as "%".
          { iDestruct "MI" as "[$ _]". }
          simpl in H. destruct H as (LUMHi'& LUOk'& LEi'& LEn'& LEO').
          destruct (le_gt_dec (S (S (v + v0))) i'); cycle 1.
          { iPoseProof (event_obl_compare i' (S (S (v + v0))) with "[$EF $EA]") as "%". 1: lia.
            simpl in H. destruct H as (?&?&?). done. }
          iPoseProof (event_obl_compare (S (S (v + v0))) i' with "[$EA $EF]") as "%". 1: auto.
          simpl in H. destruct H as (LEn'2& LEO'2& _). rename l into LEv1.
          assert (n' = S n) by lia. subst n'. clear LEn' LEn'2.
          iPoseProof (history_interp_hG_event_lookup with "[$HI $HE]") as "%".
          iPoseProof (history_interp_lookup with "HI") as "%". rewrite H in H0. inversion H0. clear H H0. subst σ' Θ' κs'.
          iPoseProof (Hsound2 with "[$HI $SIa $MI $WPs $TF2]") as "HA".
          1: eapply BEH. 1: eapply FS2. 1,2,3,4,5: eauto.
          { intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
            - inv H. eapply HIST in LUh. eauto.
            - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
              inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
              destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
              rewrite H1 TRn1. eauto. }
          { subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
          iMod ("ACC" with "[]") as "_".
          { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of EF HE TF2". }
          iModIntro. iFrame. }
      * iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix s j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union.
          { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
            apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iDestruct "HI" as "[HI SIa]".
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        assert (LEO4 : obls_le Ω2 Ω4).
        { etrans; first eauto. eauto. }
        destruct (Ω4 !! k) eqn:LUOk4; cycle 1.
        { apply elem_of_dom_2 in LUOk2. destruct LEO4. apply not_elem_of_dom in LUOk4. set_solver + LUOk2 H LUOk4. }
        destruct o.
        { iPoseProof ("IH" $! (fair_sched_fun γ2 owner2 fuel2) with "[] [] [] [] [] [] [] [] TF HI SIa MI WPs") as "H".
          1: eauto. 1: eauto. 1: eauto. 1: eauto.
          { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
            - inv H. eapply HIST in LUh. eauto.
            - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
              inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
              destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
              rewrite H1 TRn1. eauto. }
          { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
          1: eauto.
          { iPureIntro. destruct LEO4. specialize (H0 _ _ _ LUOk2 LUOk4). destruct H0.
            - destruct H0. subst. apply Hessenberg.le_add_l, Jacobsthal.le_mult_r. auto.
            - eapply Ord.lt_le, fair_sched_fun_mon_gen. auto. }
          iModIntro. iFrame. }
        { clear Hsound1. iModIntro. rewrite ti_until_unfold /ti_until_pre. iLeft.
          iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
          iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
          iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]".
          { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
            iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk4 in H. inv H. }
          { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
            iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk4 in H. inv H. }
          iDestruct "Var" as "(#Of& %&%&%&%&%&%& #EF& #HE& #TF2)".
          iPoseProof (event_obl_model_history_interp_lookup with "[MI $EF]") as "%".
          { iDestruct "MI" as "[$ _]". }
          simpl in H. destruct H as (LUMHi'& LUOk'& LEi'& LEn'& LEO').
          destruct (le_gt_dec (S (S (v + v0))) i'); cycle 1.
          { iPoseProof (event_obl_compare i' (S (S (v + v0))) with "[$EF $EA]") as "%". 1: lia.
            simpl in H. destruct H as (?&?&?). done. }
          iPoseProof (event_obl_compare (S (S (v + v0))) i' with "[$EA $EF]") as "%". 1: auto.
          simpl in H. destruct H as (LEn'2& LEO'2& _). rename l into LEv1.
          assert (n' = S n) by lia. subst n'. clear LEn' LEn'2.
          iPoseProof (history_interp_hG_event_lookup with "[$HI $HE]") as "%".
          iPoseProof (history_interp_lookup with "HI") as "%". rewrite H in H0. inversion H0. clear H H0. subst σ' Θ' κs'.
          iPoseProof (Hsound2 with "[$HI $SIa $MI $WPs $TF2]") as "HA".
          1: eapply BEH. 1: eapply FS2. 1,2,3,4,5: eauto.
          { intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
            - inv H. eapply HIST in LUh. eauto.
            - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
              inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
              destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
              rewrite H1 TRn1. eauto. }
          { subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
          iMod ("ACC" with "[]") as "_".
          { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of EF HE TF2". }
          iModIntro. iFrame. }
    + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TDone. clear TDone. inversion H. clear H. subst Θ0 σ1 ρ2.
      destruct H1 as (He1&<-&<-&->&->). destruct He1 as [v1 He1]. simpl in *.
      rewrite map_union_empty insert_id in TRn1. 2: auto.
      iPoseProof (history_interp_step with "HI") as "[SI ACC]". iMod ("ACC" with "SI") as "HI".
      pose proof (exists_fscnt_next _ _ FS). destruct H as (γ2& FS2& FSrel).
      unfold trace_next in *. simpl in *.
      assert (TNow : trace_thread (n, τf) = i1).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      assert (TNA : ts_emb (thread_na i1) (n, τf)).
      { unfold ts_emb, thread_na. simpl. rewrite TRn. right. eauto. }
      rewrite -TNow in TNA. pose proof (owit_inv_lb_step_na_turn _ _ _ _ _ TNA OTA LB FSrel) as LB2.
      iDestruct "MI" as "[MHI MI]". iMod (model_history_interp_step _ _ _ (S n) with "MHI") as "MHI".
      1: lia. 1: reflexivity.
      iPoseProof (history_interp_wf with "HI") as "%HistWF".
      assert (HDrop : (fair_sched_fun γ2 owner fuel < fair_sched_fun γ owner fuel)%ord).
      { apply Hessenberg.lt_add_r, OrdArith.lt_from_nat.
        specialize (FSrel owner). unfold fscnt_next_rel_th in FSrel.
        specialize (OTA k _ LUOk). simpl in OTA.
        rewrite decide_False in FSrel; cycle 1.
        { intros F. subst. eapply (thread_active_and_not_false _ _ TNA OTA). }
        rewrite decide_False in FSrel; auto.
        intros F. eapply (thread_active_and_not_false _ _ F OTA). }
      assert (HDropw : (fair_sched_fun γ2 owner fuel < w)%ord).
      { eapply Ord.lt_le_lt; last eapply LEwit. auto. }
      iApply fupd_mask_intro. 1: set_solver. iIntros "close".
      iExists _. iSplit; first eauto. iModIntro. iMod "close" as "_". iModIntro.
      iPoseProof ("IH" $! (fair_sched_fun γ2 owner fuel) with "[] [] [] [] [] [] [] [] TF HI SIa [$MHI $MI] WPs") as "H".
      1: eauto. 1: eauto. 1: eauto. 1: eauto.
      { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
        - inv H. eapply HIST in LUh. eauto.
        - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
          inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
          destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
          rewrite H2 TRn1. eauto. }
      1: eauto. 1: eauto. 1: done.
      iFrame.
  Qed.

End temporal.

Section temporal_connectives.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types A B : tfProp Λ Σ.

  Program Definition tfp_always N A : tfProp Λ Σ :=
    {| tfp_skel := tp_always (tfp_skel A);
       tfp_logic := inv N ⟦A⟧ₛ;
       tfp_snap _ _ _ _ _ _ := inv N ⟦A⟧ₛ;
       tfp_sound fp := sound_always (lantanaGS0 := LantanaG _ _ fp) N _ _ _ _
                         (tfp_snap_intro A) (tfp_sound A fp) |}.
  Next Obligation. iIntros (N A ?????????) "(_& _& $)". Qed.

  (** [A] until [B], using namespace [N] and obligation [k]. *)
  Program Definition tfp_until N k (b : bool) (q : Qp) A B : tfProp Λ Σ :=
    {| tfp_skel := tp_until (tfp_skel A) (tfp_skel B);
       tfp_logic := (oblP_assigned k b (q/2)%Qp ∗ oblP_inv N k ⟦A⟧ₛ ⟦B⟧ₛ (until_disch k (tfp_snap B)))%I;
       tfp_snap n σ Θ κs i Ω := ((∃ f o, event_obl i (n, Ω) k (obl_assigned f o)) ∗
                                 oblP_inv N k ⟦A⟧ₛ ⟦B⟧ₛ (until_disch k (tfp_snap B)))%I;
       tfp_sound fp := sound_until (lantanaGS0 := LantanaG _ _ fp) N k _ _ _ _ _ _ _ _
                         (tfp_snap_intro A) (tfp_sound A fp) (tfp_snap_intro B) (tfp_sound B fp) |}.
  Next Obligation.
    iIntros (N k b q A B h n σ Θ κs m i Ω W) "(HI& MI& [OA #TL])". iFrame "TL".
    iDestruct "MI" as "(MI& S& MI2)".
    iEval (unfold_opreds) in "OA". iDestruct "OA" as "(#OE& OA)".
    iPoseProof (osat_lookup_assigned with "[$S $OE $OA]") as "%H". destruct H as (?&?&?).
    iPoseProof (model_history_interp_event_obl_now with "MI") as "#ME". 1: eauto. eauto.
  Qed.

  Definition tfp_finally N k b q B : tfProp Λ Σ := tfp_until N k b q (tfp_pure True) B.

End temporal_connectives.

(** ** Notations *)
Notation "➢ π" := (tfp_atomic π) (at level 50, π at level 1) : tfp_scope.
Notation "'⌜' p '⌝'" := (tfp_pure p) : tfp_scope.
Notation "'⟨' p '⟩'" := (tfp_ghost p%I) : tfp_scope.
Infix "∧" := (tfp_and) : tfp_scope.
Infix "∨" := (tfp_or) : tfp_scope.
Infix "→" := (tfp_impl) : tfp_scope.
Infix "∗" := (tfp_sep) : tfp_scope.
Notation "∀ a .. z , P" := (tfp_forall _ (λ a, .. (tfp_forall _ (λ z, P%T)) ..)) : tfp_scope.
Notation "∃ a .. z , P" := (tfp_exist _ (λ a, .. (tfp_exist _ (λ z, P%T)) ..)) : tfp_scope.
(** Ghost quantifiers carry the skeleton [t] of their body. *)
Notation "'∃ˢ' x , P '@' t" := (tfp_gexist (λ x, P%T) t)
  (at level 200, x binder, P at level 200, t at level 200, right associativity) : tfp_scope.
Notation "'∀ˢ' x , P '@' t" := (tfp_gforall (λ x, P%T) t)
  (at level 200, x binder, P at level 200, t at level 200, right associativity) : tfp_scope.

(** ** Embedding of the syntactic [tf] *)
Section embed.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Program Definition tf_sem (Φ : tf (Π:=state_pred Λ) Σ) : tfProp Λ Σ :=
    {| tfp_skel := tf_to_tp Φ;
       tfp_logic := ⟦Φ⟧ₗ;
       tfp_snap n σ Θ κs i Ω := tf_intuit n σ Θ κs i Ω Φ |}.
  Next Obligation. intros Φ ?????????. apply tf_logic_tf_intuit. Qed.
  Next Obligation.
    iIntros (Φ fp s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "(HI& MI& WPs& TF)".
    iApply (lwp_fix_ti_logic (lantanaGS0 := LantanaG _ _ fp) with "[-]"); eauto. iExists Φ. iSplit; first done. iFrame.
  Qed.

  Lemma tf_sem_logic Φ : ⟦tf_sem Φ⟧ₛ = ⟦Φ⟧ₗ.
  Proof. done. Qed.
  Lemma tf_sem_skel Φ : tfp_skel (tf_sem Φ) = tf_to_tp Φ.
  Proof. done. Qed.

End embed.

(** ** Adequacy *)
Section adequacy.
  Context `{!lantanaGS Λ Σ}.

  Lemma lwp_ti_logic_tfp s h n σ Θ (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)) κs g v Ω W τf γ (Φ : tp) :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    owit_inv_lb (fair_sched_fun γ) Ω W →
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    ((history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗
      model_interp g v Ω W n (dom Θ) ∗
      (|={⊤}=>m ∃ (Φ' : tfProp Λ Σ), (⌜ tfp_skel Φ' = Φ ⌝) ∗ ⟦Φ'⟧ₛ ∗
                  (⟦Φ'⟧ₛ -∗ |={⊤}=>m [∗ map] i↦e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ v, lift_term i Ψ v }}))))
      ⊢ |={⊤}=> ti_logic Ord.lt Φ (n, τf).
  Proof.
    iIntros (BEH FS LB HIST) "([HI SIa]& MI& WPs)".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "((%Φ'& %HΦ& P& WPs)& HI& %&%&%&%& %H& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO1 LB1].
    iPoseProof (tfp_snap_intro Φ' with "[$HI $MI $P]") as "#TF".
    iPoseProof ("WPs" with "P") as "WPs".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "(WPs& HI& %&%&%&%& %H& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO2 LB2].
    iPoseProof (big_sepM2_alt with "WPs") as "[%Dom WPs]".
    remember (map_zip Θ Ψs) as TQ. assert (EQTQ : Θ = fst <$> TQ).
    { subst. rewrite fst_map_zip; auto. intro k. rewrite -!elem_of_dom Dom. auto. }
    iAssert ([∗ map] i↦'(e, Q) ∈ TQ,
               lwpupd i ⊤ e (match to_val e with
                             | Some v => (lift_term i Q) v
                             | None => lwp_fix s i ⊤ e (lift_term i Q)
                             end))%I with "[WPs]" as "WPs".
    { iApply (big_sepM_impl with "WPs"). iIntros "!> %%% H". destruct x.
      rewrite lwp_unfold_fix. iEval (rewrite lwp_fix_unfold_fix /lwp_pre) in "H".
      simpl. destruct (to_val e) eqn:He.
      - iMod "H". iApply sfmupd_lwpupd. iMod "H". by iModIntro.
      - rewrite lwp_fix_unfold_fix /lwp_pre He. iFrame. }
    iMod (all_interp_lwpupd_steps_gmap γ with "WPs [$HI $SIa] MI") as "(WPs& HI& %&%&%&%& %H& MI)".
    { subst Θ. done. }
    { auto. }
    destruct H as [LEO3 LB3].
    rewrite -HΦ. iModIntro.
    (* Make the instance a constructor application, as in the soundness law of [tfProp]. *)
    destruct lantanaGS0 as [Htemp Hsic fp].
    iApply (tfp_sound Φ' fp with "[$HI $MI $WPs $TF]").
    1,2: eauto. 1: lia. all: eauto. etrans; eauto.
  Qed.

End adequacy.

(** Same as [lwp_adequacy], with [tfProp] in place of [tf]. *)
Theorem lwp_adequacy_tfp (Σ : gFunctors) (Λ : language)
  `{!mupdGpreS Σ} `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))}
  s σ Θ i κs (Φ : tp) :
  ∀ (τ : trace Λ),
  behavior τ →
  fair_scheduling τ →
  (τ.1 = 0) →
  (τ.2 0 = (Θ, σ, i, κs)) →
  (∀ `{Htemporal : !temporalGS Λ Σ},
     ∃ (c : Ord.t),
     ⊢ |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                (fork_post : thread_id → val Λ → iProp Σ)
                (Ψs : gmap thread_id (H:=pos_countable) (thread_id → val Λ → iProp Σ)),
     let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
     state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
     (£ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
      |={⊤}=>m (∃ (Φ' : tfProp Λ Σ),
                  (⌜ tfp_skel Φ' = Φ ⌝) ∗ ⟦Φ'⟧ₛ ∗
                  (⟦Φ'⟧ₛ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))) →
  tp_trace Φ τ.
Proof.
  intros τ BEH FS INIT1 INIT2 Hwp.
  assert (iProp_sat
            (|==> ∃ (Hmupd : mupdGS Σ) (Hhist : histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))),
                let _ : temporalGS Λ Σ := TemporalG Hmupd Hhist in
                (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗
                wsat.wsat ∗ wsat.ownE ⊤ ∗
                |={⊤}=> ti_logic Ord.lt Φ τ)) as Hsat; cycle 1.
  { apply sat_bupd, sat_exists in Hsat. destruct Hsat as (Hmupd& Hsat). apply sat_exists in Hsat. destruct Hsat as (Hhist& Hsat).
    set (Htemp := TemporalG Hmupd Hhist : temporalGS Λ Σ).
    apply (ti_logic_tp_trace Ord.lt_well_founded emp). apply (sat_fupd ⊤).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono. 2: eapply Hsat. simpl. iIntros "($& $& $& $)". }
  assert (Hwp' : ⊢ ∀ Htemporal : temporalGS Λ Σ,
            ∃ (c : Ord.t),
            |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                     (fork_post : thread_id → val Λ → iProp Σ)
                     (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)),
            let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
            state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
            (£ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
             |={⊤}=>m (∃ (Φ' : tfProp Λ Σ), (⌜ tfp_skel Φ' = Φ ⌝) ∗ ⟦Φ'⟧ₛ ∗
                                     (⟦Φ'⟧ₛ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))).
  { iIntros (Htemp). destruct (Hwp Htemp) as [x Hx]. iExists x. iApply Hx. }
  eapply sat_wand; cycle 1.
  { eapply Hwp'. }
  apply (sat_mono True); cycle 1.
  { apply iProp_sat_intro. }
  iIntros "_ H".
  iMod (model_interp_alloc 0) as "(%Hmupd& R& W& WOE& MI)".
  iMod (history_interp_init σ Θ κs) as "(%Hhist& HI)".
  iExists Hmupd, Hhist.
  set (Htemp := TemporalG Hmupd Hhist : temporalGS Λ Σ).
  iDestruct ("H" $! Htemp) as "(%c& H)".
  iDestruct "R" as "(%x& R)".
  iMod (own_update _ (● x) with "R") as "[R LC]".
  { apply (auth_update_alloc x ((c : ordinal_ucmra.OrdUR) ⋅ x)).
    apply (op_local_update_discrete x ε c).
    intros ?. apply auth_valid_trivial. }
  iModIntro. iFrame "R W WOE". rewrite (right_id ε).
  iMod "H" as "(%Hsic& %fork_post& %Ψs& SI& SIa& WPs)".
  iMod ("HI" $! Hsic with "SI") as "HI". iDestruct "MI" as "(MHI& S& T& A& G& MI)".
  iMod (thP_carriers_alloc_threads (dom Θ) with "[$T $G]") as "(T& G& Ths)". 1: set_solver.
  iPoseProof ("WPs" with "LC Ths") as "WPs". rewrite union_empty_l_L.
  destruct τ as [n τf]. simpl in INIT1, INIT2. subst n.
  apply fair_scheduling_fscnt in FS. destruct FS as (γ& FS).
  set (Hlantana := LantanaG Htemp Hsic fork_post : lantanaGS Λ Σ).
  iApply (lwp_ti_logic_tfp (lantanaGS0:=Hlantana) with "[$HI $SIa $MHI $S $T $A $G $MI $WPs]").
  1,2: eauto. 1: apply map_Forall2_empty.
  { intros. rewrite lookup_cons in H0. destruct n'; last done. inv H0. rewrite INIT2. eauto. }
Qed.

(** The old adequacy theorem is the special case of embedded syntactic formulas. *)
Corollary lwp_adequacy_via_tfp (Σ : gFunctors) (Λ : language)
  `{!mupdGpreS Σ} `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))}
  s σ Θ i κs (Φ : tp) :
  ∀ (τ : trace Λ),
  behavior τ →
  fair_scheduling τ →
  (τ.1 = 0) →
  (τ.2 0 = (Θ, σ, i, κs)) →
  (∀ `{Htemporal : !temporalGS Λ Σ},
     ∃ (c : Ord.t),
     ⊢ |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                (fork_post : thread_id → val Λ → iProp Σ)
                (Ψs : gmap thread_id (H:=pos_countable) (thread_id → val Λ → iProp Σ)),
     let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
     state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
     (£ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
      |={⊤}=>m (∃ (Φ' : tf Σ),
                  (⌜ tf_to_tp Φ' = Φ ⌝) ∗ (⟦Φ'⟧ₗ) ∗
                  (⟦Φ'⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))) →
  tp_trace Φ τ.
Proof.
  intros τ BEH FS INIT1 INIT2 Hwp. eapply lwp_adequacy_tfp; [done..|].
  intros Htemp. destruct (Hwp Htemp) as [c Hc]. exists c.
  iMod Hc as (Hsic fork_post Ψs) "(SI& SIa& H)". iModIntro. iExists Hsic, fork_post, Ψs.
  iFrame "SI SIa". iIntros "LC Ths". iMod ("H" with "LC Ths") as (Φ' HΦ') "[HΦ' H]".
  iModIntro. iExists (tf_sem Φ'). by iFrame.
Qed.

(** ** Reduction lemmas and rules

    The connectives compute: [⟦·⟧ₛ] of each connective is its iProp counterpart by
    [reflexivity], so no [tf_red]-style rewriting is needed. *)
Definition tfp_discharged `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} k (B : tfProp Λ Σ) : iProp Σ :=
  until_disch k (tfp_snap B).

Section reduction.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types A B : tfProp Λ Σ.

  Lemma tfp_until_logic N k b q A B :
    ⟦tfp_until N k b q A B⟧ₛ = (oblP_assigned k b (q/2)%Qp ∗ oblP_inv N k ⟦A⟧ₛ ⟦B⟧ₛ (tfp_discharged k B))%I.
  Proof. done. Qed.
  Lemma tfp_always_logic N A : ⟦tfp_always N A⟧ₛ = inv N ⟦A⟧ₛ.
  Proof. done. Qed.
  Lemma tfp_gexist_logic {X} (Φ : X → tfProp Λ Σ) t :
    ⟦tfp_gexist Φ t⟧ₛ = (∃ x, ⌜tfp_skel (Φ x) = t⌝ ∗ ⟦Φ x⟧ₛ)%I.
  Proof. done. Qed.
  (** When all witnesses have skeleton [t], the guard disappears. *)
  Lemma tfp_gexist_logic_uniform {X} (Φ : X → tfProp Λ Σ) t :
    (∀ x, tfp_skel (Φ x) = t) → ⟦tfp_gexist Φ t⟧ₛ ⊣⊢ ∃ x, ⟦Φ x⟧ₛ.
  Proof.
    intros Ht. rewrite tfp_gexist_logic. iSplit.
    - iIntros "(%x& _& H)". by iExists x.
    - iIntros "(%x& H)". iExists x. by iFrame.
  Qed.
  Lemma tfp_gforall_logic_uniform {X} (Φ : X → tfProp Λ Σ) t :
    (∀ x, tfp_skel (Φ x) = t) → ⟦tfp_gforall Φ t⟧ₛ ⊣⊢ ∀ x, ⟦Φ x⟧ₛ.
  Proof.
    intros Ht. simpl. iSplit.
    - iIntros "H %x". by iApply "H".
    - iIntros "H %x _". iApply "H".
  Qed.

  Global Instance tfp_discharged_persistent k B : Persistent (tfp_discharged k B).
  Proof. rewrite /tfp_discharged. apply _. Qed.

End reduction.

Section proof.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  (** Always *)
  Global Instance tfp_always_persistent N P : Persistent (⟦tfp_always N P⟧ₛ).
  Proof. rewrite tfp_always_logic. apply _. Qed.

  (** For now, rewrite tfp_always_logic and use rules of inv. *)

  (** Until *)
  Lemma tfp_until_frac_split N k b q q1 q2 P Q :
    (q = q1 + q2)%Qp →
    ⊢ ⟦tfp_until N k b q P Q⟧ₛ -∗ (⟦tfp_until N k b q1 P Q⟧ₛ ∗ ⟦tfp_until N k b q2 P Q⟧ₛ).
  Proof.
    iIntros (He) "U". rewrite !tfp_until_logic He Qp.div_add_distr. iDestruct "U" as "([$ $]& #U)". auto.
  Qed.
  Lemma tfp_until_frac_add N k b1 b2 q1 q2 q P Q P' Q' :
    (q = q1 + q2)%Qp →
    ⟦tfp_until N k b1 q1 P Q⟧ₛ -∗ ⟦tfp_until N k b2 q2 P' Q'⟧ₛ -∗ ⟦tfp_until N k b1 q P Q⟧ₛ.
  Proof.
    intros Hq. subst q.
    rewrite !tfp_until_logic Qp.div_add_distr. iIntros "[Oa1 $] [Oa2 _]".
    iPoseProof (oblP_assigned_agree with "Oa1 Oa2") as "%". subst.
    by iCombine "Oa1 Oa2" as "Oa".
  Qed.

  Global Instance tfp_until_fractional N k b P Q : Fractional (λ q, ⟦tfp_until N k b q P Q⟧ₛ).
  Proof.
    intros p q. rewrite !tfp_until_logic. iSplit.
    - iIntros "(Oa& #OI)". iFrame "OI". rewrite !Qp.div_add_distr. iDestruct "Oa" as "[Oa Oa']". iFrame.
    - iIntros "((Oa1& #Oi)& Oa2& _)". iFrame "Oi". rewrite !Qp.div_add_distr. iCombine "Oa1 Oa2" as "$".
  Qed.
  Global Instance tfp_until_as_fractional N k b q P Q : AsFractional (⟦tfp_until N k b q P Q⟧ₛ) (λ q, ⟦tfp_until N k b q P Q⟧ₛ) q.
  Proof. split; [auto|apply _]. Qed.

  (** Update rules *)
  Lemma tfp_until_alloc E g K (b : bool) ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    crP_obls g ℓ1 K -∗
    |={E}=>g ∃ k, ⌜k ∉ K⌝ ∗ crP_obls g ℓ1 ({[k]} ∪ K) ∗
                 oblP_fuel k ℓ2 μ ∗ witP_layer k ℓ2 ∗
                 ∀ E' N (P Q : tfProp Λ Σ), ▷ (if b then ⟦Q⟧ₛ else ⟦P⟧ₛ) ={E'}=∗ (⟦tfp_until N k b 1 P Q⟧ₛ).
  Proof.
    iIntros (Ltl) "TG". iMod (obl_alloc_assigned with "TG") as "(%& $& $& Oa& $& $& ACC)". 1: auto.
    iIntros "!> %%%% H". rewrite tfp_until_logic. iMod ("ACC" with "H") as "ACC". iFrame. done.
  Qed.

  Lemma tfp_discharged_alloc E ℓ μ (Q : tfProp Λ Σ) :
    ⟦Q⟧ₛ -∗
    |={E}=>g ⟦Q⟧ₛ ∗ ∃ k, oblP_discharged k ∗
                        (∀ E' N (P : tfProp Λ Σ), |={E'}=> oblP_inv N k ⟦P⟧ₛ ⟦Q⟧ₛ (tfp_discharged k Q)) ∗ 
                        oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof.
    iIntros "HQ".
    unfold_sfgupd. rewrite /fgupd. iIntros (?????) "SI".
    (* unfold_sfmupd. rewrite /fmupd. iIntros (?????) "SI". *)
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    (* FIXME: proof without unfold everything? *)
    unfold_opreds. iApply gupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
    (* unfold_opreds. iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)". *)
    assert (NEW : ∃ k, Ω1 !! k = None).
    { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
    destruct NEW as (k& NEWk).
    assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
    iMod (osat_alloc_obl_discharged _ k (measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M) with "S") as "(S& #Gwf& #Ge& #Gu& Gf& %OStep)". 1: auto.
    iMod (owit_alloc_witness_discharged _ k (η (measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M)) with "[$W $Gu]") as "(W& #Ww)".
    { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
    iPoseProof (oassigned_add_obl with "[$A $Ge Gu]") as "A".
    { iRight. iFrame "Gu". }
    set (Ω2:=(<[k:=(obl_discharged)]> Ω1)).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 2. eauto. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iPoseProof (history_interp_hG_event_now with "SI") as "#HE".
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. econstructor 2. econstructor 2. auto. }
    iIntros (? [WStep GWI2]) "!>".
    unshelve epose proof (owit_inv_alloc_discharged Ω1 k W1 NinOk1 GWI W2 _ GWI2) as (NinWk1& WMon).
    { inv WStep; eauto. econstructor 2. apply wits_nd_step_wits_step. auto. }
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. iFrame. }
    iPoseProof (tfp_snap_intro Q with "[$SI $HI $S $O $A $G $W $HQ]") as "#HQi". 1: eauto.    
    rewrite /model_interp. iFrame "HI S O A G W". iSplitR; first eauto.
    iModIntro. iMod "close" as "_". iModIntro. iFrame "SI HQ". iExists k. iFrame "Ge Ww Gf Gu".
    iIntros (E' N P).
    rewrite /tfp_discharged.
    iMod (oblG_inv_alloc_discharged _ N _ _ ⟦P⟧ₛ ⟦Q⟧ₛ with "[$Gu]") as "#GVar"; cycle 1.
    { iFrame "GVar". done. }
    iFrame "Eo HE HQi".
  Qed.

  (** TODO: Timeless version *)
  Lemma tfp_until_to_true E N k (P Q : tfProp Λ Σ) :
    ↑N ⊆ E →
    ⟦tfp_until N k false 1 P Q⟧ₛ ={E,E ∖ ↑N}=∗
    ▷ (⟦P⟧ₛ ∗ ∀ E', |={E'}=>g ((▷ ⟦Q⟧ₛ) ={E ∖ ↑N,E}=∗ ⟦tfp_until N k true 1 P Q⟧ₛ)).
  Proof.
    rewrite !tfp_until_logic. iIntros (HM) "(Oa& #Oi)".
    iMod (obl_assigned_to_true with "Oi Oa") as "[H ACC]". 1: auto.
    iModIntro. iNext. iDestruct "H" as "[Oa $]".
    iIntros "%". iPoseProof ("ACC" with "Oa") as "ACC". iMod ("ACC" $! E') as "[Oa ACC]".
    iIntros "!> HQ". iMod ("ACC" with "HQ") as "_". iFrame. eauto.
  Qed.

  (** TODO: Timeless version *)
  Lemma tfp_until_true_to_discharge E N k (P Q : tfProp Λ Σ) :
    ↑N ⊆ E →
    ⟦tfp_until N k true 1 P Q⟧ₛ ={E,E ∖ ↑N}=∗
    ∀ g ℓ K,
    (⌜k ∈ K⌝) → crP_obls g ℓ K -∗
    ∀ E', ▷ (|={E'}=>m |={E ∖ ↑N,E}=> (⟦Q⟧ₛ ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)).
  Proof.
    rewrite tfp_until_logic. iIntros (HMask) "(Oa& #OI)".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: auto.
    iIntros "!> %%% %LUGk TG %". iDestruct ("H" with "Oa") as "[H ACC]".
    iNext. iDestruct "H" as "(Oa1& Oa2& HQ)". iCombine "Oa1 Oa2" as "Oa".
    unfold_sfmupd. rewrite /fmupd. iIntros (?????) "SI".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    (* FIXME: it would be better if we don't need to unfold everything and re-do the proof here... *)
    unfold_opreds. iDestruct "TG" as "(%& #Oe& Gg& Gt& Gw& #Gb& OS)".
    iDestruct "OI" as "(#Ge& Gvar)". iDestruct "Oa" as "(_& Gl)".
    iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
    iPoseProof (big_sepS_delete _ _ _ LUGk with "OS") as "[(_& Go& Oo) OS]".
    iPoseProof (osat_lookup_assigned with "[$S $Ge $Gl]") as "%LUO1l".
    iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
    destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&LUO1o).
    rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into a.
    iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%& Go1& Oo1& _) | #Gu])".
    { apply elem_of_dom. eauto. }
    2:{ iExFalso. iPoseProof (oblG_assigned_discharged_false with "[$Gl $Gu]") as "%". done. }
    iPoseProof (oblG_owner_agree _ i i1 with "[$Go $Go1]") as "%". destruct H as [<- _].
    iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
    iPoseProof (othread_elem with "[$O $Oe]") as "%Ini".
    iMod (ocarrier_delete_obl with "[$O $G $Gg $Oo]") as "(O& G& Gg& Go2)". 1,2: auto.
    iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'". iCombine "Go Go'" as "Go".
    iMod (osat_discharge with "[$S $Ge $Gl $Go]") as "(S& #Gu& %Gstep)".
    assert (LUW : ∃ b, W1 !! k = Some (witness_assigned b) ∧ (b <= η a)%ord).
    { specialize (GWI k). rewrite LUO1l in GWI. inv GWI. destruct y; try done. eauto. }
    destruct LUW as (b&LUW1& LEab).
    iPoseProof (owit_discharge with "[$W $Gu]") as "W". 1: eauto.
    iPoseProof (oassigned_add_obl _ k with "[$A $Ge]") as "A".
    { iRight. eauto. }
    set (Ω2:=(<[k:=(obl_discharged)]> Ω1)).
    assert (Gstep' : obl_step (obl_assigned a i) obl_discharged) by (by econstructor 2).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iPoseProof (history_interp_hG_event_now with "SI") as "#HE".
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
    iIntros (? [WStep GWI2]).
    pose proof (owit_inv_discharge _ _ _ _ _ LUO1l GWI Gstep' W2 WStep GWI2) as (?& LUW& WMon).
    rewrite LUW1 in LUW. inv LUW.
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)). 1: iFrame.
      apply elem_of_dom_2 in LUO1l. rewrite -union_difference_L; set_solver. }
    iPoseProof (tfp_snap_intro Q with "[$SI $HI $S $O $A $G $W $HQ]") as "#HQi". 1: eauto.
    rewrite /model_interp. iFrame "HI S O W A G".
    iApply fupd_intro. iSplitR; first eauto. iIntros "!>". iFrame "Oe Ge Gb Gu Gg Gt SI".
    iMod "close" as "_". iModIntro. iMod ("ACC" with "[]") as "_".
    { iNext. iRight. iRight. rewrite /tfp_discharged. iFrame "Ge Gu Eo HE HQi". }
    iModIntro. iFrame.
  Qed.

  Lemma tfp_until_discharge E N k (P Q : tfProp Λ Σ) :
    ↑N ⊆ E →
    ⟦tfp_until N k false 1 P Q⟧ₛ ={E,E ∖ ↑N}=∗
    ▷ (⟦P⟧ₛ ∗
       ∀ E', |={E'}=>g ((▷ ⟦Q⟧ₛ) ={E ∖ ↑N}=∗
                       ∀ g ℓ K, (⌜k ∈ K⌝) → crP_obls g ℓ K -∗
                                ∀ E'', ▷ (|={E''}=>m |={E ∖ ↑N,E}=> (⟦Q⟧ₛ ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)))).
  Proof.
    iIntros (HN) "Uk". iMod (tfp_until_to_true with "Uk") as "H". 1: auto.
    iModIntro. iNext. iDestruct "H" as "($& H)". iIntros (?).
    iMod ("H" $! E') as "H". iIntros "!> HQ". iMod ("H" with "HQ") as "H".
    iMod (tfp_until_true_to_discharge with "H") as "H". 1: auto.
    iIntros "!> %%% % TG". iPoseProof ("H" with "[//] TG") as "H".
    iIntros (?). iNext. iMod ("H" $! E'') as "H". iModIntro. iFrame.
  Qed.

  (** Access rules *)
  Lemma tfp_until_discharged_false N k b q P Q :
    ⟦tfp_until N k b q P Q⟧ₛ -∗ oblP_discharged k -∗ False.
  Proof.
    rewrite tfp_until_logic. iIntros "[Oa _] #Of".
    iPoseProof (oblP_assigned_discharged_false with "Oa Of") as "%". done.
  Qed.

  Lemma tfp_until_acc E N k b q P Q :
    ↑N ⊆ E →
    ⟦tfp_until N k b q P Q⟧ₛ ={E,E ∖ ↑N}=∗
    ▷ ((if b then ⟦Q⟧ₛ else ⟦P⟧ₛ) ∗ ((▷ if b then ⟦Q⟧ₛ else ⟦P⟧ₛ) ={E ∖ ↑N,E}=∗ ⟦tfp_until N k b q P Q⟧ₛ)).
  Proof.
    rewrite !tfp_until_logic. iIntros (Hmask) "(Oa& #OI)".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: set_solver.
    iPoseProof ("H" with "Oa") as "[H ACC]".
    iModIntro. iNext. iDestruct "H" as "(Oa& H)". destruct b.
    - iDestruct "H" as "(Oa2& $)". iIntros "HQ". iFrame "Oa OI". iApply "ACC".
      iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame.
    - iDestruct "H" as "(Oa2& $)". iIntros "HP". iFrame "Oa OI". iApply "ACC".
      iNext. iApply oblP_variant_unfold. iLeft. iFrame.
  Qed.

End proof.

(** ** The syntactic [tf] is a fragment

    [tf_native] translates [tf] structurally into the semantic connectives. It agrees with
    [tf_to_tp], [tf_logic] and [tf_intuit], so the connectives above faithfully implement
    the old semantics (compare [tf_sem], which reuses the old proofs as they are). *)
Section native.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Local Transparent tf_logic tf_intuit.
  (* [simpl] exposes some of these projections on one side of the equivalences only. *)
  Local Transparent temporal_mupdGS temporal_histGS mupd_invGS mupd_osatGS mupd_othreadGS
    mupd_ocarrierGS mupd_owitGS mupd_mhistGS.

  Fixpoint tf_native (Φ : tf (Π:=state_pred Λ) Σ) : tfProp Λ Σ :=
    match Φ with
    | tf_emp => tfp_emp
    | tf_atomic π => tfp_atomic π
    | tf_pure p => tfp_pure p
    | tf_ghost P => tfp_ghost P
    | tf_and P Q => tfp_and (tf_native P) (tf_native Q)
    | tf_or P Q => tfp_or (tf_native P) (tf_native Q)
    | tf_impl p Q => tfp_impl p (tf_native Q)
    | tf_forall A P => tfp_forall A (λ a, tf_native (P a))
    | tf_exist A P => tfp_exist A (λ a, tf_native (P a))
    | tf_sep P Q => tfp_sep (tf_native P) (tf_native Q)
    | tf_always N P => tfp_always N (tf_native P)
    | tf_until N k b q P Q => tfp_until N k b q (tf_native P) (tf_native Q)
    end.

  Lemma tf_native_skel Φ : tfp_skel (tf_native Φ) = tf_to_tp Φ.
  Proof. induction Φ; simpl; f_equal; auto; apply func_ext; auto. Qed.

  Lemma tf_native_logic_snap Φ :
    (⟦tf_native Φ⟧ₛ ≡ ⟦Φ⟧ₗ) ∧
    (∀ n σ Θ κs i Ω, tfp_snap (tf_native Φ) n σ Θ κs i Ω ≡ tf_intuit n σ Θ κs i Ω Φ).
  Proof.
    induction Φ as [| | | |P [IHP1 IHP2] Q [IHQ1 IHQ2]|P [IHP1 IHP2] Q [IHQ1 IHQ2]|p Q [IHQ1 IHQ2]
                    |A P IH|A P IH|P [IHP1 IHP2] Q [IHQ1 IHQ2]|N P [IHP1 IHP2]|N k b q P [IHP1 IHP2] Q [IHQ1 IHQ2]];
      simpl; split; intros; try done.
    all: try (f_equiv; done).
    all: try (by f_equiv; [apply IHP1 | apply IHQ1]).
    all: try (by f_equiv; [apply IHP2 | apply IHQ2]).
    all: try (by f_equiv; apply IHQ1).
    all: try (by f_equiv; apply IHQ2).
    all: try (by f_equiv; intros a; apply IH).
    (* always (snapshot): the instances of [inv] differ syntactically, so apply properness
       by unification rather than by type-class search *)
    all: try (by apply inv_proper).
    (* until: logic and snapshot *)
    all: apply bi.sep_proper; [reflexivity|].
    all: etrans; [apply oblP_inv_proper_1, IHP1|]; etrans; [apply oblP_inv_proper_2, IHQ1|].
    all: apply oblP_inv_proper_3; repeat f_equiv; apply IHQ2.
  Qed.

  Lemma tf_native_logic Φ : ⟦tf_native Φ⟧ₛ ⊣⊢ ⟦Φ⟧ₗ.
  Proof. apply (tf_native_logic_snap Φ). Qed.

End native.

(** ** Examples: ghost quantifiers over large types

    None of these can be written with [tf]: [tf_exist (tf Σ) _] and [tf_exist (iProp Σ) _]
    are universe inconsistencies. They live in the same file as [lwp_adequacy_tfp], so the
    universe constraints of the adequacy proof are checked together with them. *)
Section examples.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  (** Quantification over temporal formulas, ... *)
  Local Definition ex_self N (t : @tp (state_pred Λ)) : tfProp Λ Σ :=
    (∃ˢ R : tfProp Λ Σ, tfp_always N R @ tp_always t)%T.
  (** ... over families of them, ... *)
  Local Definition ex_family (t : @tp (state_pred Λ)) : tfProp Λ Σ :=
    (∃ˢ F : nat → tfProp Λ Σ, F 0 @ t)%T.
  (** ... an invariant whose temporal content may change over time, ... *)
  Local Definition ex_inv N (t : @tp (state_pred Λ)) : tfProp Λ Σ :=
    tfp_always N (∃ˢ R : tfProp Λ Σ, R @ t)%T.
  (** ... and over iProp, scoping over two temporal operators (pushing the quantifier into
      a single [⟨_⟩] is not possible here). *)
  Local Definition ex_iprop N1 N2 k : tfProp Λ Σ :=
    (∃ˢ Ψ : iProp Σ, tfp_always N1 ⟨Ψ⟩ ∗ tfp_finally N2 k false 1 ⟨Ψ⟩
      @ tp_and (tp_always tp_true) (tp_until (tp_pure True) tp_true))%T.

  Local Lemma ex_self_skel N t : tfp_skel (ex_self N t) = tp_always t.
  Proof. done. Qed.
  Local Lemma ex_self_logic N t :
    ⟦ex_self N t⟧ₛ ⊣⊢ ∃ R : tfProp Λ Σ, ⌜tp_always (tfp_skel R) = tp_always t⌝ ∗ inv N ⟦R⟧ₛ.
  Proof. done. Qed.
  Local Lemma ex_iprop_logic N1 N2 k :
    ⟦ex_iprop N1 N2 k⟧ₛ ⊣⊢ ∃ Ψ : iProp Σ, inv N1 Ψ ∗ ⟦tfp_finally N2 k false 1 ⟨Ψ⟩⟧ₛ.
  Proof. rewrite tfp_gexist_logic_uniform //. Qed.

  (** A temporal formula can be made abstract, keeping only its skeleton. *)
  Lemma tfp_always_abstract N (R : tfProp Λ Σ) :
    ⟦tfp_always N R⟧ₛ ⊢ ⟦∃ˢ R' : tfProp Λ Σ, tfp_always N R' @ tp_always (tfp_skel R)⟧ₛ.
  Proof. iIntros "H". iExists R. by iFrame. Qed.

End examples.
