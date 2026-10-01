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

Section laws.
  Context `{!lantanaGS Λ Σ}.

  Definition snap_intro_law (L : iProp Σ) (I : snapT Λ Σ) : Prop :=
    ∀ h n σ Θ κs m i Ω W,
      history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ L ⊢ I n σ Θ κs i Ω.

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

Record tfProp {Λ Σ} `{!lantanaGS Λ Σ} := TfProp {
  tfp_skel : @tp (state_pred Λ);
  tfp_logic : iProp Σ;
  tfp_snap : snapT Λ Σ;
  tfp_snap_persistent n σ Θ κs i Ω : Persistent (tfp_snap n σ Θ κs i Ω);
  tfp_snap_intro : snap_intro_law tfp_logic tfp_snap;
  tfp_sound : sound_law tfp_snap tfp_skel;
}.
Global Arguments tfProp Λ Σ {_}.
Global Arguments TfProp {Λ Σ _}.
Global Arguments tfp_skel {Λ Σ _}.
Global Arguments tfp_logic {Λ Σ _}.
Global Arguments tfp_snap {Λ Σ _}.
Global Existing Instance tfp_snap_persistent.

Declare Scope tfp_scope.
Delimit Scope tfp_scope with T.
Bind Scope tfp_scope with tfProp.

Notation "'⟦' Φ '⟧ₛ'" := (tfp_logic Φ%T) (format "'⟦' Φ '⟧ₛ'").

(** ** Connectives *)
Section connectives.
  Context `{!lantanaGS Λ Σ}.
  Implicit Types A B : tfProp Λ Σ.

  Program Definition tfp_emp : tfProp Λ Σ :=
    {| tfp_skel := tp_true; tfp_logic := (emp)%I; tfp_snap _ _ _ _ _ _ := (emp)%I |}.
  Next Obligation. iIntros (?????????) "_". done. Qed.
  Next Obligation. iIntros (??????????????????????) "_". done. Qed.

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
    iIntros (π s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
    unfold ti_atomic. iPoseProof (event_pred_history_interp_lookup with "[$HI $TF]") as "%H".
    destruct H as [H ?]. simpl. apply HIST in H. destruct H as [? H]. rewrite H. auto.
  Qed.

  Program Definition tfp_pure (p : Prop) : tfProp Λ Σ :=
    {| tfp_skel := tp_pure p; tfp_logic := (⌜p⌝)%I; tfp_snap _ _ _ _ _ _ := (⌜p⌝)%I |}.
  Next Obligation. iIntros (??????????) "(_& _& $)". Qed.
  Next Obligation. iIntros (???????????????????????) "(_& _& _& $)". Qed.

  (** Pure ghost: resources that are invisible in the trace. *)
  Program Definition tfp_ghost (P : iProp Σ) : tfProp Λ Σ :=
    {| tfp_skel := tp_true; tfp_logic := (P)%I; tfp_snap _ _ _ _ _ _ := (True)%I |}.
  Next Obligation. iIntros (??????????) "_". done. Qed.
  Next Obligation. iIntros (???????????????????????) "_". done. Qed.

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
    iIntros (A B s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
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
    iIntros (A B s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
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
    iIntros (p B s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
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
    iIntros (X Φ s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
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
    iIntros (X Φ s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)". simpl.
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
    iIntros (A B s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF1& #TF2)". simpl.
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
    iIntros (X Φ t s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)".
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
    iIntros (X Φ t s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)".
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
