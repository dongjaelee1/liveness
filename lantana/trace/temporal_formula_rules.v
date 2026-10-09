From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export temporal_formula_run.
From transfinite.stepindex Require Import ordinals.

(** * Rules for the temporal formulas [alwaysI], [untilI]

    [alwaysI N P] is a registered invariant, read as always [P]. [untilI N k q P Q] is [P]
    until [Q], controlled by the obligation [k]; [finallyI] is an until with left formula
    [True]; [untilI_done k Q] is a discharged until. Allocation, access and discharge are
    model updates [|={E}=>m] (temporal_formula.v). The guarantees [temporal_always] and
    [temporal_until] read the formulas on traces (temporal_formula_run.v). *)

(** ** Rules for [alwaysI] *)
Section always_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma alwaysI_guar_acc E N P G :
    ↑N ⊆ E → alwaysI_guar N P G ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. iIntros (?) "#H". iApply inv_acc; first done. by iApply alwaysI_guar_inv. Qed.

  Lemma alwaysI_as_acc E N P V :
    ↑N ⊆ E → alwaysI_as N P V ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. apply alwaysI_guar_acc. Qed.

  Lemma alwaysI_acc E N P :
    ↑N ⊆ E → alwaysI N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. apply alwaysI_as_acc. Qed.

  (** Proof mode integration: [iInv] opens these like invariants. *)

  Global Instance into_inv_alwaysI_guar N P G : IntoInv (alwaysI_guar N P G) N := {}.

  Global Instance into_acc_alwaysI_guar N P G E :
    IntoAcc (X := unit) (alwaysI_guar N P G)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". by iApply alwaysI_guar_acc.
  Qed.

  Global Instance into_inv_alwaysI_as N P V : IntoInv (alwaysI_as N P V) N := {}.

  Global Instance into_acc_alwaysI_as N P V E :
    IntoAcc (X := unit) (alwaysI_as N P V)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". by iApply alwaysI_as_acc.
  Qed.

  Global Instance into_inv_alwaysI N P : IntoInv (alwaysI N P) N := {}.

  Global Instance into_acc_alwaysI N P E :
    IntoAcc (X := unit) (alwaysI N P)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". by iApply alwaysI_acc.
  Qed.

  (** Registering an existing invariant, with a later-guarded guarantee of its content. *)

  Lemma alwaysI_register_guar E N P G :
    ↑N ⊆ E →
    inv N P -∗ ▷ (P ⊨ₜ G) -∗ |={E}=>m alwaysI_guar N P G.
  Proof.
    iIntros (HNE) "#Hinv #HG". iApply sfmupd_read_fupd. iIntros (h n σ Θ κs) "HI TI".
    iMod (inv_acc with "Hinv") as "[HP Hclose]"; first done.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    iIntros (g i Ω W) "MI".
    iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#C".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MI". iMod "close" as "_". iMod ("Hclose" with "HP") as "_".
    iMod (saved_ti_alloc (itrProp_internal G)) as (γ) "#Hγ".
    iMod (treg_st_register treg_handle (RAlways N γ) with "TI [] HI") as "(HI& TI& (%j& #Hj))".
    { iIntros (st) "_". simpl. iExists P, G. iFrame "Hγ Hinv HG". }
    iModIntro. iFrame "HI TI". rewrite alwaysI_guar_unfold. iExists j, n, γ, _. iFrame "Hj HE Hγ Hinv HG C".
  Qed.
  (** The same, read as a consequence [V] of the content. *)

  Lemma alwaysI_register E N P V :
    ↑N ⊆ E →
    inv N P -∗ □ (P -∗ V) -∗ |={E}=>m alwaysI_as N P V.
  Proof.
    iIntros (HNE) "#Hinv #HPV".
    iApply (alwaysI_register_guar with "Hinv []"); first done.
    iNext. iApply (temporal_mono with "HPV"). iApply temporal_sem.
  Qed.

  Lemma alwaysI_alloc_guar E N P G :
    ▷ (P ⊨ₜ G) -∗ ▷ P -∗ |={E}=>m alwaysI_guar N P G.
  Proof.
    iIntros "#HG HP". iApply sfmupd_read. iIntros (h n σ Θ κs g i Ω W) "HI TI MI".
    iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#C".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MI".
    iMod (saved_ti_alloc (itrProp_internal G)) as (γ) "#Hγ".
    iMod (inv_alloc N _ P with "HP") as "#Hinv".
    iMod (treg_st_register treg_handle (RAlways N γ) with "TI [] HI") as "(HI& TI& (%j& #Hj))".
    { iIntros (st) "_". simpl. iExists P, G. iFrame "Hγ Hinv HG". }
    iModIntro. iFrame "HI TI". rewrite alwaysI_guar_unfold. iExists j, n, γ, _. iFrame "Hj HE Hγ Hinv HG C".
  Qed.

  Lemma alwaysI_alloc E N P :
    ▷ P -∗ |={E}=>m alwaysI N P.
  Proof.
    iIntros "HP". iApply (alwaysI_alloc_guar with "[] HP").
    iNext. iApply temporal_sem.
  Qed.

  Lemma temporal_always_guar N P G : ⊢ alwaysI_guar N P G ⊨ₜ itrProp_always G.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& #A)". rewrite alwaysI_guar_unfold.
    iDestruct "A" as (j r γ st) "(#Hj& #HE& #Hγ& #Hinv& #HG& #AC)".
    iDestruct (history_interp_hG_event_lookup with "[$HI $HE]") as %Hr.
    iDestruct (history_interp_wf with "HI") as %[Hlen _].
    assert (Hrn : r ≤ n) by (apply lookup_lt_Some in Hr; lia).
    iApply tguar_intro.
    iIntros "!>" (Sys l h' g v' Ω' W' τf γ' σ' Θ' κs') "#ST %Hf #B Sys".
    destruct Hf as (BEH& FS& LB& HIST).
    iDestruct (bundle_always_cert with "B Hj Hγ []") as "#C"; first done.
    { iIntros (->). done. }
    rewrite /= trI_always_unfold /trI_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iApply ALC_intro. iMod "close" as "_". iModIntro.
    iSplit; [|iSplit; first done].
    - iApply (tguar_elim with "C ST [%] B Sys"). split_and!; done.
    - iApply (always_run with "ST Hj Hγ [%] Sys"). simpl.
      split_and!; [lia|by apply behavior_S|exact FS|done|done].
  Qed.

  Lemma temporal_always_as N P V : ⊢ alwaysI_as N P V ⊨ₜ itrProp_always (itrProp_sem V).
  Proof. apply temporal_always_guar. Qed.

  Lemma temporal_always N P : ⊢ alwaysI N P ⊨ₜ itrProp_always (itrProp_sem P).
  Proof. apply temporal_always_as. Qed.

  (** *** The until loop

      Once the obligation is discharged, the record of the right formula at the current
      position is at hand: step, and decide with it. *)

End always_rules.

(** ** Rules for [untilI], [finallyI] and [untilI_done] *)
Section until_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma untilI_guar_frac_split N k q q1 q2 P Q G1 G2 :
    (q = q1 + q2)%Qp →
    ⊢ untilI_guar N k q P Q G1 G2 -∗ (untilI_guar N k q1 P Q G1 G2 ∗ untilI_guar N k q2 P Q G1 G2).
  Proof.
    iIntros (He) "U". rewrite !untilI_guar_unfold He Qp.div_add_distr. iDestruct "U" as "([$ $]& #U)". auto.
  Qed.

  Lemma untilI_guar_frac_add N k q1 q2 q P Q G1 G2 P' Q' G1' G2' :
    (q = q1 + q2)%Qp →
    untilI_guar N k q1 P Q G1 G2 -∗ untilI_guar N k q2 P' Q' G1' G2' -∗ untilI_guar N k q P Q G1 G2.
  Proof.
    intros Hq. subst q.
    rewrite !untilI_guar_unfold Qp.div_add_distr. iIntros "[Oa1 $] [Oa2 _]".
    by iCombine "Oa1 Oa2" as "Oa".
  Qed.

  Lemma untilI_frac_split N k q q1 q2 P Q :
    (q = q1 + q2)%Qp →
    ⊢ untilI N k q P Q -∗ (untilI N k q1 P Q ∗ untilI N k q2 P Q).
  Proof. rewrite !untilI_guar_canonical. apply untilI_guar_frac_split. Qed.

  Lemma untilI_frac_add N k q1 q2 q P Q P' Q' :
    (q = q1 + q2)%Qp →
    untilI N k q1 P Q -∗ untilI N k q2 P' Q' -∗ untilI N k q P Q.
  Proof. rewrite !untilI_guar_canonical. apply untilI_guar_frac_add. Qed.

  (** Allocation. A strong until is allocated on a fresh obligation [k] ([obl_new], which
      gives its assignment token) with its left formula [P] ([untilI_guar_init]);
      [untilI_guar_alloc] does both, with the formulas chosen once [k] is known. A done until
      comes from discharging a strong until ([untilI_guar_discharge_done]), or from a fresh
      obligation with [Q] at hand ([untilI_done_guar_init]). Both guarantee the until
      ([temporal_until_guar], [temporal_until_done_guar]).

      A strong until registers, with later-guarded guarantees of its formulas, and records
      the left formula at the current position. *)
  Lemma untilI_guar_init E N (P Q : iProp Σ) G1 G2 k :
    oblP_assigned k 1 -∗ ▷ (P ⊨ₜ G1) -∗ ▷ (Q ⊨ₜ G2) -∗ ▷ P -∗
    |={E}=>m untilI_guar N k 1 P Q G1 G2.
  Proof.
    iIntros "[Oa Oa'] #HG1 #HG2 HC".
    iApply sfmupd_read. iIntros (h n σ Θ κs gm i Ω W) "HI TI MI".
    iPoseProof (temporal_elim_later_guar P G1 with "HG1 [$HC $HI $MI]") as "#C".
    iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "(#OE& Oa)".
    iPoseProof (osat_lookup_assigned with "[$S $OE $Oa]") as "%Hk". destruct Hk as (fu& o& Hk).
    iPoseProof (model_history_interp_event_obl_now with "MHI") as "#EA". 1: eauto.
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MHI S MI".
    iMod (oblP_inv_alloc_assigned E N k P (until_disch k G2) with "Oa' HC") as "#OI".
    iMod (saved_ti_alloc (itrProp_internal G1)) as (γP) "#HγP".
    iMod (saved_ti_alloc (itrProp_internal G2)) as (γQ) "#HγQ".
    iMod (treg_st_register treg_handle (RUntil N k γP γQ) with "TI [] HI") as "(HI& TI& (%j& #Hj))".
    { iIntros (st) "_". simpl. iExists P, G1, G2. iFrame "HγP HγQ OI HG1". }
    iModIntro. iFrame "HI TI". rewrite untilI_guar_unfold /untilI_guar_pers. iSplitL "Oa".
    { iEval (unfold_opreds). iFrame "OE Oa". }
    iExists j, n, γP, γQ, _, i, Ω, fu, o. iFrame "Hj HE HγP HγQ OI HG1 HG2 EA C".
  Qed.

  Lemma untilI_init E N (P Q : iProp Σ) k :
    oblP_assigned k 1 -∗ ▷ P -∗ |={E}=>m untilI N k 1 P Q.
  Proof.
    iIntros "Oa HP". rewrite untilI_guar_canonical.
    iApply (untilI_guar_init with "Oa [] [] HP"); iNext; iApply temporal_sem.
  Qed.

  (** The obligation and the strong until at once: [k] is a new child of [p], and the
      formulas are chosen once [k] is known. *)

  Lemma untilI_guar_alloc E p K ℓ μ :
    parP_le p ℓ -∗ parP_kids p K -∗
    |={E}=>m ∃ k, ⌜k ∉ K⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 ∀ E' N (P Q : iProp Σ) G1 G2,
                   ▷ (P ⊨ₜ G1) -∗ ▷ (Q ⊨ₜ G2) -∗ ▷ P -∗ |={E'}=>m untilI_guar N k 1 P Q G1 G2.
  Proof.
    iIntros "B Kp". iMod (obl_new with "B Kp") as (k) "(%Hk& Kp& Kk& Oa& F& W)".
    iModIntro. iExists k. iFrame "Kp Kk F W". iSplitR; first done.
    iIntros (E' N P Q G1 G2) "HG1 HG2 HP". iApply (untilI_guar_init with "Oa HG1 HG2 HP").
  Qed.

  Lemma untilI_alloc E p K ℓ μ :
    parP_le p ℓ -∗ parP_kids p K -∗
    |={E}=>m ∃ k, ⌜k ∉ K⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 ∀ E' N (P Q : iProp Σ), ▷ P -∗ |={E'}=>m untilI N k 1 P Q.
  Proof.
    iIntros "B Kp". iMod (obl_new with "B Kp") as (k) "(%Hk& Kp& Kk& Oa& F& W)".
    iModIntro. iExists k. iFrame "Kp Kk F W". iSplitR; first done.
    iIntros (E' N P Q) "HP". iApply (untilI_init with "Oa HP").
  Qed.

  (** A done until from a fresh obligation: [k], a childless child of [p], is discharged at
      once with [Q] at hand. *)

  Lemma untilI_done_guar_init E (Q : iProp Σ) G2 p K k :
    k ∈ K →
    oblP_assigned k 1 -∗ parP_kids p K -∗ oblP_kids k ∅ -∗ ▷ (Q ⊨ₜ G2) -∗ Q -∗
    |={E}=>m untilI_done_guar k Q G2 ∗ parP_kids p (K ∖ {[k]}).
  Proof.
    iIntros (Hk) "Oa Kp Kk #HG2 HQ".
    iMod (obl_discharge_leaf with "Kp Kk Oa") as "[$ #D]"; first done.
    iModIntro. rewrite untilI_done_guar_unfold. iFrame "HQ D HG2".
  Qed.

  Lemma untilI_done_init E (Q : iProp Σ) p K k :
    k ∈ K →
    oblP_assigned k 1 -∗ parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
    |={E}=>m untilI_done k Q ∗ parP_kids p (K ∖ {[k]}).
  Proof.
    iIntros (Hk) "Oa Kp Kk HQ". rewrite /untilI_done.
    iApply (untilI_done_guar_init with "Oa Kp Kk [] HQ"); first done. iNext. iApply temporal_sem.
  Qed.
  (** The same, with the children as [obl_new] returns them. *)

  Lemma untilI_done_init' E (Q : iProp Σ) p K k :
    k ∉ K →
    oblP_assigned k 1 -∗ parP_kids p ({[k]} ∪ K) -∗ oblP_kids k ∅ -∗ Q -∗
    |={E}=>m untilI_done k Q ∗ parP_kids p K.
  Proof.
    iIntros (Hk) "Oa Kp Kk HQ".
    iMod (untilI_done_init with "Oa Kp Kk HQ") as "[$ Kp]"; first set_solver.
    assert (({[k]} ∪ K) ∖ {[k]} = K) as -> by set_solver. done.
  Qed.

  (** The right formula and the discharged obligation of a done until. *)

  Lemma untilI_done_guar_elim k Q G2 : untilI_done_guar k Q G2 ⊢ Q ∗ oblP_discharged k.
  Proof. rewrite untilI_done_guar_unfold. iIntros "($& $& _)". Qed.

  Lemma untilI_done_elim k Q : untilI_done k Q ⊢ Q ∗ oblP_discharged k.
  Proof. apply untilI_done_guar_elim. Qed.

  (** A done until guarantees the until of any left reading, from its right formula: no
      run is needed. *)

  Lemma temporal_until_done_guar k Q G1 G2 : ⊢ untilI_done_guar k Q G2 ⊨ₜ itrProp_until G1 G2.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& U)". rewrite untilI_done_guar_unfold.
    iDestruct "U" as "(HQ& _& #HG2)".
    iApply (temporal_elim Q with "[] [$HI $MI $HQ]"). by iApply temporal_until_now.
  Qed.

  Lemma temporal_until_done k Q G1 : ⊢ untilI_done k Q ⊨ₜ itrProp_until G1 (itrProp_sem Q).
  Proof. apply temporal_until_done_guar. Qed.

  Lemma temporal_finally_done k Q : ⊢ untilI_done k Q ⊨ₜ itrProp_finally (itrProp_sem Q).
  Proof. apply temporal_until_done. Qed.

  Lemma temporal_until_done_valid k Q G1 G2 : (⊢ Q ⊨ₜ G2) → ⊢ untilI_done k Q ⊨ₜ itrProp_until G1 G2.
  Proof.
    intros HG2. iApply (temporal_weaken _ (itrProp_until G1 (itrProp_sem Q))).
    { apply itrProp_until_mono; [apply itrProp_le_refl|by apply itrProp_sem_le]. }
    iApply temporal_until_done.
  Qed.

  (** Discharge: [P] is taken out; once [Q] holds, [k] (a childless child of [p]) is
      discharged, the record of [G2] at the discharge is left in the invariant, and the
      until becomes a done until. *)

  Lemma untilI_guar_discharge_done E N k (P Q : iProp Σ) G1 G2 :
    ↑N ⊆ E →
    untilI_guar N k 1 P Q G1 G2 ={E,E ∖ ↑N}=∗
    ▷ (P ∗ ∀ p K, ⌜k ∈ K⌝ → parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
         ∀ E', |={E'}=>m |={E ∖ ↑N,E}=> (untilI_done_guar k Q G2 ∗ parP_kids p (K ∖ {[k]}))).
  Proof.
    rewrite untilI_guar_unfold. iIntros (HN) "(Oa& #U)".
    iPoseProof (untilI_guar_pers_inv with "U") as "#OI".
    iDestruct (untilI_guar_pers_temporal with "U") as "[_ #HG2]".
    iMod (oblP_inv_acc_assigned with "OI") as "H"; first done.
    iDestruct ("H" with "Oa") as "[H ACC]".
    iModIntro. iNext. iDestruct "H" as "(Oa1& Oa2& $)". iCombine "Oa1 Oa2" as "Oa".
    iIntros (p K Hk) "Kp Kk HQ %E'".
    iMod (obl_discharge_leaf with "Kp Kk Oa") as "[$ #D]"; first done.
    iDestruct (oblP_discharged_unfold with "D") as "[#Oe #Od]".
    iMod (sfmupd_read _ (Q ∗ until_disch k G2) with "[HQ]") as "[HQ #R]".
    { iIntros (h n σ Θ κs g i Ω W) "HI TI MI".
      iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#TQ".
      iDestruct "MI" as "(MHI& S& MI)".
      iDestruct (osat_lookup_discharged with "[$S $Oe $Od]") as %Hkd.
      iPoseProof (model_history_interp_event_obl_now with "MHI") as "#EF"; first exact Hkd.
      iFrame "MHI S MI". iModIntro. iFrame "HI TI HQ". iExists n, i, Ω. iFrame "EF TQ". }
    iModIntro. iMod ("ACC" with "[]") as "_".
    { iNext. rewrite oblP_variant_unfold. iRight. iFrame "D R". }
    iModIntro. rewrite untilI_done_guar_unfold. iFrame "HQ D HG2".
  Qed.

  Lemma untilI_discharge_done E N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    untilI N k 1 P Q ={E,E ∖ ↑N}=∗
    ▷ (P ∗ ∀ p K, ⌜k ∈ K⌝ → parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
         ∀ E', |={E'}=>m |={E ∖ ↑N,E}=> (untilI_done k Q ∗ parP_kids p (K ∖ {[k]}))).
  Proof. rewrite untilI_guar_canonical /untilI_done. apply untilI_guar_discharge_done. Qed.

  (** The same, with the done until taken apart: the usual case. *)

  Lemma untilI_guar_discharge E N k (P Q : iProp Σ) G1 G2 :
    ↑N ⊆ E →
    untilI_guar N k 1 P Q G1 G2 ={E,E ∖ ↑N}=∗
    ▷ (P ∗ ∀ p K, ⌜k ∈ K⌝ → parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
         ∀ E', |={E'}=>m |={E ∖ ↑N,E}=> (Q ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k)).
  Proof.
    iIntros (HN) "U". iMod (untilI_guar_discharge_done with "U") as "H"; first done.
    iModIntro. iNext. iDestruct "H" as "[$ H]".
    iIntros (p K Hk) "Kp Kk HQ %E'".
    iPoseProof ("H" $! p K Hk with "Kp Kk HQ") as "H".
    iMod ("H" $! E') as "H". iModIntro. iMod "H" as "[D $]".
    iModIntro. iApply (untilI_done_guar_elim with "D").
  Qed.

  Lemma untilI_discharge E N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    untilI N k 1 P Q ={E,E ∖ ↑N}=∗
    ▷ (P ∗ ∀ p K, ⌜k ∈ K⌝ → parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
         ∀ E', |={E'}=>m |={E ∖ ↑N,E}=> (Q ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k)).
  Proof. rewrite untilI_guar_canonical. apply untilI_guar_discharge. Qed.

  (** Access rules *)

  Lemma untilI_guar_discharged_false N k q P Q G1 G2 :
    untilI_guar N k q P Q G1 G2 -∗ oblP_discharged k -∗ False.
  Proof.
    rewrite !untilI_guar_unfold. iIntros "[Oa _] #Of".
    iPoseProof (oblP_assigned_discharged_false with "Oa Of") as "%". done.
  Qed.

  Lemma untilI_discharged_false N k q P Q :
    untilI N k q P Q -∗ oblP_discharged k -∗ False.
  Proof. rewrite untilI_guar_canonical. apply untilI_guar_discharged_false. Qed.

  Lemma untilI_guar_acc E N k q P Q G1 G2 :
    ↑N ⊆ E →
    untilI_guar N k q P Q G1 G2 ={E,E ∖ ↑N}=∗
    ▷ (P ∗ (▷ P ={E ∖ ↑N,E}=∗ untilI_guar N k q P Q G1 G2)).
  Proof.
    rewrite !untilI_guar_unfold. iIntros (Hmask) "(Oa& #U)".
    iPoseProof (untilI_guar_pers_inv with "U") as "#OI".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: set_solver.
    iPoseProof ("H" with "Oa") as "[H ACC]".
    iModIntro. iNext. iDestruct "H" as "(Oa& Oa2& $)". iIntros "HP". iFrame "Oa U". iApply "ACC".
    iNext. iApply oblP_variant_unfold. iLeft. iFrame.
  Qed.

  Lemma untilI_acc E N k q P Q :
    ↑N ⊆ E →
    untilI N k q P Q ={E,E ∖ ↑N}=∗
    ▷ (P ∗ (▷ P ={E ∖ ↑N,E}=∗ untilI N k q P Q)).
  Proof. rewrite untilI_guar_canonical. apply untilI_guar_acc. Qed.

  (** Discharge with the right formula at hand, using a later credit. *)

  Lemma untilI_guar_discharge_lc E N k p K P Q G1 G2 :
    ↑N ⊆ E → k ∈ K →
    £n 1 -∗ parP_kids p K -∗ oblP_kids k ∅ -∗ untilI_guar N k 1 P Q G1 G2 -∗ Q -∗
    |={E}=>m Q ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof.
    iIntros (Hmask Hk) "LC Kp Kk HU HQ".
    iMod (untilI_guar_discharge with "HU") as "HU"; first set_solver.
    iApply (lc_sfmupd_add_later with "LC"). iNext.
    iDestruct "HU" as "[_ HU]". iPoseProof ("HU" $! p K Hk with "Kp Kk HQ") as "HU".
    iMod ("HU" $! (E ∖ ↑N)) as "HU".
    iMod "HU" as "($& $& $)". done.
  Qed.

  (** Discharge a finally with its right formula at hand, using a later credit. *)

  Lemma finallyI_discharge E N k p K Q :
    ↑N ⊆ E → k ∈ K →
    £n 1 -∗ parP_kids p K -∗ oblP_kids k ∅ -∗ finallyI N k 1 Q -∗ Q -∗
    |={E}=>m Q ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof. rewrite /finallyI untilI_guar_canonical. apply untilI_guar_discharge_lc. Qed.

  (** The same, with the children as [untilI_alloc] returns them. *)

  Lemma finallyI_discharge' E N k p K (Q : iProp Σ) :
    ↑N ⊆ E → k ∉ K →
    £n 1 -∗ parP_kids p ({[k]} ∪ K) -∗ oblP_kids k ∅ -∗ finallyI N k 1 Q -∗ Q -∗
    |={E}=>m Q ∗ parP_kids p K ∗ oblP_discharged k.
  Proof.
    iIntros (HN Hk) "LC Kp Kk HF HQ".
    iMod (finallyI_discharge with "LC Kp Kk HF HQ") as "($& Kp& $)"; [done|set_solver|].
    assert (({[k]} ∪ K) ∖ {[k]} = K) as -> by set_solver. done.
  Qed.

  Lemma temporal_until_guar N k q P Q G1 G2 : ⊢ untilI_guar N k q P Q G1 G2 ⊨ₜ itrProp_until G1 G2.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& U)". rewrite untilI_guar_unfold /untilI_guar_pers.
    iDestruct "U" as "[Oa #U]".
    iDestruct "U" as (j r γP γQ st v Ω1 fu1 o1) "(#Hj& #HE& #HγP& #HγQ& #OI& _& _& #EA1& #AC)".
    iAssert (⌜∃ fu o, Ω !! k = Some (obl_assigned fu o)⌝)%I as %(fu& o& Hk).
    { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "[#Oe Oa]".
      iDestruct (osat_lookup_assigned with "[$S $Oe $Oa]") as %(?&?&?). eauto. }
    iPoseProof (model_interp_event_obl with "MI") as "#EA"; first exact Hk.
    iDestruct (history_interp_hG_event_lookup with "[$HI $HE]") as %Hr.
    iDestruct (history_interp_wf with "HI") as %[Hlen _].
    assert (Hrn : r ≤ n) by (apply lookup_lt_Some in Hr; lia).
    iApply tguar_intro.
    iIntros "!>" (Sys l h' g v' Ω' W' τf γ' σ' Θ' κs') "#ST %Hf #B Sys".
    destruct Hf as (BEH& FS& LB& HIST).
    (* the certificate of this until for [n]: from the bundle, or its allocation records *)
    iDestruct (bundle_until_cert with "B Hj HγP HγQ []") as "#C"; first done.
    { iIntros (->). iNext. by iLeft. }
    rewrite /= /trI_exist. iExists (Ord.S (Ord.S (fair_sched_ub fu))).
    rewrite trI_until_unfold /trI_until_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    rewrite (ALC_credits _ _ (Ord.from_nat 1) (|={∅,⊤}=> _)%I). iApply ALC_intro. iIntros "LC".
    iMod "close" as "_".
    iDestruct "C" as "[[TrecP|TrecQ]|(%n'& %i'& %Ω''& %Hn'& #EF& #TQ')]".
    - (* [P] at [n]: the obligation at [S n] decides *)
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first solve_ndisj.
      iMod (lc_fupd_elim_later with "LC Var") as "Var".
      iDestruct "Var" as "[[Oa' HP']|[Of R]]".
      + iAssert (⌜∃ fu' o', Ω' !! k = Some (obl_assigned fu' o')⌝)%I as %(fu'& o'& Hk').
        { iDestruct "Sys" as "(_& (_& S& _)& _)". iEval (unfold_opreds) in "Oa'". iDestruct "Oa'" as "[#Oe Oa']".
          iDestruct (osat_lookup_assigned with "[$S $Oe $Oa']") as %(?&?&?). eauto. }
        iAssert (⌜(fu' w≤ fu)⌝)%I as %Hfu.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EA]") as %(_& _& _& _& [_ Hle]).
          iPureIntro. specialize (Hle _ _ _ Hk Hk'). destruct Hle as [[? _]|?]; [done|by apply WFOCM.lt_le]. }
        iMod ("ACC" with "[Oa' HP']") as "_".
        { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
        iModIntro. iRight. iSplit.
        { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply Ord.le_lt_lt; first apply fair_sched_fun_ub.
          eapply Ord.le_lt_lt; [by apply fair_sched_ub_le_proper|apply Ord.S_lt]. }
        unfold trace_next. simpl.
        iApply (until_run with "ST Hj HγP HγQ OI [%] Sys").
        split_and!; [lia|by apply behavior_S|done|done|done|done].
      + iDestruct "R" as "(%n'& %i'& %Ω''& #EF& #TQ')".
        iAssert (⌜n' ≤ S n⌝)%I as %Hn'.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EF]") as %(_& _& _& ?& _). done. }
        iAssert (⌜n ≤ n'⌝)%I as %Hn.
        { destruct (le_gt_dec i' i) as [Hle|Hlt].
          - iDestruct (event_obl_compare i' i with "[$EF $EA]") as %(_& _& Hle'); first done. done.
          - iDestruct (event_obl_compare i i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
        iMod ("ACC" with "[Of]") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iFrame "Of". iExists n', i', Ω''. iFrame "EF TQ'". }
        iModIntro. destruct (decide (n' = n)) as [->|Hne].
        * iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
        * assert (n' = S n) as -> by lia.
          iRight. iSplit.
          { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
          iExists Ord.O. iSplit; first (iPureIntro; apply Ord.S_pos).
          unfold trace_next. simpl.
          iApply (until_run_discharged with "ST TQ' [%] Sys").
          split_and!; [by apply behavior_S|done|done|done].
    - (* [Q] at [n] *)
      iModIntro. iLeft. iApply (tguar_elim with "TrecQ ST [%] B Sys"). split_and!; done.
    - (* discharged before the check: the discharge was at [n] *)
      iAssert (⌜n ≤ n'⌝)%I as %Hn.
      { destruct (le_gt_dec i' i) as [Hle|Hlt].
        - iDestruct (event_obl_compare i' i with "[$EF $EA]") as %(_& _& Hle'); first done. done.
        - iDestruct (event_obl_compare i i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
      assert (n' = n) as -> by lia.
      iModIntro. iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
  Qed.

  Lemma temporal_until N k q P Q : ⊢ untilI N k q P Q ⊨ₜ itrProp_until (itrProp_sem P) (itrProp_sem Q).
  Proof. rewrite untilI_guar_canonical. apply temporal_until_guar. Qed.

  (** With valid guarantees of the contents. *)

  Lemma temporal_always_as_valid N P V G : (⊢ V ⊨ₜ G) → ⊢ alwaysI_as N P V ⊨ₜ itrProp_always G.
  Proof.
    intros HG. iApply (temporal_weaken _ (itrProp_always (itrProp_sem V))).
    { apply itrProp_always_mono. by apply itrProp_sem_le. }
    iApply temporal_always_as.
  Qed.

  Lemma temporal_always_valid N P G : (⊢ P ⊨ₜ G) → ⊢ alwaysI N P ⊨ₜ itrProp_always G.
  Proof. apply temporal_always_as_valid. Qed.

  Lemma temporal_until_valid N k q P Q G1 G2 :
    (⊢ P ⊨ₜ G1) → (⊢ Q ⊨ₜ G2) → ⊢ untilI N k q P Q ⊨ₜ itrProp_until G1 G2.
  Proof.
    intros HG1 HG2. iApply (temporal_weaken _ (itrProp_until (itrProp_sem P) (itrProp_sem Q))).
    { apply itrProp_until_mono; by apply itrProp_sem_le. }
    iApply temporal_until.
  Qed.

End until_rules.
