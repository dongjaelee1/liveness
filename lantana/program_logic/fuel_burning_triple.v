From iris.proofmode Require Import proofmode.
From lantana.program_logic Require Export lifting temporal_guarantee.

Definition fuel_burning_triple `{SI : sidx} `{!lantanaGS Λ Σ} : stuckness → thread_id → coPset -> gset ocid → gset ocid → iProp Σ → expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
  λ s i E G G' P e Q,
    (∀ (Φ : val Λ → iPropI Σ),
       (thP_carriers i G ∗ P) -∗
       (∀ v, thP_carriers i G' ∗ Q v -∗ Φ v) -∗
       lWP e @ s; i; E {{ v, Φ v }})%I.

Definition fuel_burning_triple_persistent `{SI : sidx} `{!lantanaGS Λ Σ} : stuckness → thread_id → coPset -> gset ocid → gset ocid → iProp Σ → expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
  λ s i E G G' P e Q,
    l{{{ thP_carriers i G ∗ P }}} e @ s; i; E l{{{v, RET v; thP_carriers i G' ∗ Q v }}}%I.

Section proof.
  Context `{SI : sidx} `{!lantanaGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types e : expr Λ.

  Local Lemma entails_persistent {A B : Type} (P : A → B → iProp Σ) :
    (⊢ (∃ (a : A), ∀ (b : B), P a b)%I) →
    Persistent (∃ (a : A), ∀ (b : B), P a b)%I.
  Proof.
    intros H. rewrite /Persistent. iIntros "_".
    iModIntro. eauto.
  Qed.

  Lemma fuel_burning_triple_entails_to_persistent s i E G1 G2 P e Q :
    (⊢ fuel_burning_triple s i E G1 G2 P e Q) →
    (⊢ fuel_burning_triple_persistent s i E G1 G2 P e Q).
  Proof.
    intros H. iIntros "% !> PRE POST". iApply (H with "PRE POST").
  Qed.

  Lemma measured_fuel_burning_triple_entails_to_persistent {A B : Type} s i E G1 G2
    (P : A → B → iProp Σ) e (Q : A → B → val Λ → iProp Σ) :
    (⊢ ∃ (a : A), ∀ (b : B), fuel_burning_triple s i E G1 G2 (P a b) e (λ v, Q a b v)) →
    (⊢ ∃ (a : A), ∀ (b : B), fuel_burning_triple_persistent s i E G1 G2 (P a b) e (Q a b)).
  Proof.
    intros H. iPoseProof H as (a) "#H".
    iExists a. iIntros "% % !> PRE POST". iApply ("H" with "PRE POST").
  Qed.

  Lemma fuel_burning_triple_persistent_entails s i E G1 G2 P e Q :
    fuel_burning_triple_persistent s i E G1 G2 P e Q
    ⊢ fuel_burning_triple s i E G1 G2 P e Q.
  Proof.
    iIntros "H". iIntros "% PRE POST". iApply ("H" with "PRE POST").
  Qed.

  Lemma fuel_burning_triple_persistent_iff s i E G1 G2 P e Q :
    fuel_burning_triple_persistent s i E G1 G2 P e Q
    ⊣⊢ □ fuel_burning_triple s i E G1 G2 P e Q.
  Proof.
    iSplit; iIntros "#H".
    - iIntros "!> % PRE POST". iApply ("H" with "PRE POST").
    - iIntros "% !> PRE POST". iApply ("H" with "PRE POST").
  Qed.

  Lemma fuel_burning_triple_carrier_alloc s i E G P e Q ℓ μ :
    (∀ g, fuel_burning_triple s i E ({[g]} ∪ G) G
            (P ∗ ⌜g ∉ G⌝ ∗ crP_obls g ℓ ∅ ∗ crP_fuel g ℓ μ)
            e
            Q)
    ⊢ fuel_burning_triple s i E G G
        P
        e
        Q.
  Proof.
    iIntros "H % (TG& HP) POST".
    iMod (carrier_alloc _ _ _ ℓ μ with "TG") as "(%& %& TG& Cg& Fg)".
    iPoseProof ("H" with "[$TG $HP $Cg $Fg]") as "WP". 1: auto.
    iApply ("WP" with "POST").
  Qed.

  Lemma fuel_burning_triple_wit_ind s i E G P e Q k ℓ1 ℓ2 μ :
    (□ fuel_burning_triple s i E G G
       (P ∗
        (witP_cred k 1 ={E}=∗ ([∗ set] g ∈ G, crP_fuel g ℓ2 μ) ∗ fuel_burning_triple s i E G G P e Q))
       e Q) ∧
    witP_layer k ℓ1 ∗ ⌜(ℓ1 < ℓ2)%ordi⌝
    ⊢ fuel_burning_triple s i E G G
        (P ∗ ([∗ set] g ∈ G, crP_fuel g ℓ2 (μ × ▽)%M))
        e Q.
  Proof.
    iIntros "(#H& #Wl& %LTl) % (TG& HP) POST".
    iDestruct "HP" as "[HP FS]".
    iRevert (Φ) "TG HP POST".
    iAssert (|==> ∀ Φ, (thP_carriers i G -∗ P -∗ (∀ v : val Λ, thP_carriers i G ∗ Q v -∗ Φ v) -∗ lWP e @ s; i; E {{ v, Φ v }}))%I with "[-]" as "HA"; cycle 1.
    { iMod "HA" as "HA". eauto. }
    iApply (wit_layer_ind with "[$Wl $FS]"). 1: auto.
    iIntros "!> IH !> % TG HP POST".
    iApply ("H" with "[$TG $HP IH] POST").
    iIntros "Wc". iMod ("IH" with "Wc") as "[Fs IH]".
    iFrame. iModIntro.
    iIntros "% (TG& HP) POST". iApply ("IH" with "TG HP POST").
  Qed.

End proof.

(** Untils are specific to ordinal step indices. *)
Section until.
  Context `{!lantanaGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types e : expr Λ.

  Lemma fuel_burning_triple_until_discharge s i E G P e Q N k (Φ Ψ : iProp Σ) `{!Atomic (stuckness_to_atomicity s) e} g ℓ K :
    TCEq (to_val e) None →
    ↑N ⊆ E →
    fuel_burning_triple s i (E ∖ ↑N) G G
      (P ∗ Φ)%I
      e
      (λ v, Q v ∗ Ψ ∗ crP_obls g ℓ K ∗ ⌜k ∈ K⌝)%I
    ⊢ fuel_burning_triple s i E G G
        (P ∗ untilT N k 1 Φ Ψ ∗ £ 2)%I
        e
        (λ v, Q v ∗ Ψ ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)%I.
  Proof.
    iIntros (He Hmask) "H % (TG& HP& HU& LC) POST".
    iMod (untilI_discharge with "HU") as "HUacc". 1: auto.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "HUacc" as "[HΦ HUacc]".
    iApply lwp_lwpupd.
    iPoseProof ("H" $! (λ v, |={E ∖ ↑N}=>m |={E ∖ ↑N,E}=> Φ0 v)%I with "[$TG $HP $HΦ]") as "Hwp".
    iApply lwp_mono.
    { iIntros (?) "H". iApply sfmupd_lwpupd. iApply "H". }
    iApply "Hwp". iIntros (v) "(TG& HQ& HΨ& Cg& %Ink)".
    iMod ("HUacc" with "HΨ") as ">HUacc".
    iPoseProof ("HUacc" with "[//] Cg") as "HUacc".
    iApply (lc_sfmupd_add_later with "LC"). iNext.
    iMod ("HUacc" $! _) as "HUacc". iModIntro.
    iMod "HUacc" as "(HΨ& Cg& #Od)".
    iApply ("POST" with "[$TG $HQ $HΨ $Cg]"). eauto.
  Qed.

  Lemma fuel_burning_triple_until_discharge_ex s i E G P e Q N k (Φ Ψ : iProp Σ) `{!Atomic (stuckness_to_atomicity s) e} :
    TCEq (to_val e) None →
    ↑N ⊆ E →
    fuel_burning_triple s i (E ∖ ↑N) G G
      (P ∗ Φ)%I
      e
      (λ v, ∃ g ℓ K, Q v ∗ Ψ ∗ crP_obls g ℓ K ∗ ⌜k ∈ K⌝)%I
    ⊢ fuel_burning_triple s i E G G
        (P ∗ untilT N k 1 Φ Ψ ∗ £ 2)%I
        e
        (λ v, ∃ g ℓ K, Q v ∗ Ψ ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)%I.
  Proof.
    iIntros (He Hmask) "H % (TG& HP& HU& LC) POST".
    iMod (untilI_discharge with "HU") as "HUacc". 1: auto.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "HUacc" as "[HΦ HUacc]".
    iApply lwp_lwpupd.
    iPoseProof ("H" $! (λ v, |={E ∖ ↑N}=>m |={E ∖ ↑N,E}=> Φ0 v)%I with "[$TG $HP $HΦ]") as "Hwp".
    iApply lwp_mono.
    { iIntros (?) "H". iApply sfmupd_lwpupd. iApply "H". }
    iApply "Hwp". iIntros (v) "(TG& %&%&%& HQ& HΨ& Cg& %Ink)".
    iMod ("HUacc" with "HΨ") as ">HUacc".
    iPoseProof ("HUacc" with "[//] Cg") as "HUacc".
    iApply (lc_sfmupd_add_later with "LC"). iNext.
    iMod ("HUacc" $! _) as "HUacc". iModIntro.
    iMod "HUacc" as "(HΨ& Cg& #Od)".
    iApply ("POST" with "[$TG $HQ $HΨ $Cg]"). eauto.
  Qed.

  (** Allocating an until registers it: the registry and a later credit are consumed. *)
  Lemma fuel_burning_triple_until_alloc s i E G P e Q g K ℓ1 ℓ2 μ N Φ Ψ :
    (∀ k, fuel_burning_triple s i E G G
            (P ∗ ⌜k ∉ K⌝ ∗ crP_obls g ℓ1 ({[k]} ∪ K) ∗
             untilT N k 1 Φ Ψ ∗ witP_layer k ℓ2 ∗ oblP_fuel k ℓ2 μ)
            e
            Q)
      ∧ ⌜(ℓ1 <= ℓ2)%ordi ∧ ↑tregN ⊆ E ∧ N ## tregN⌝
    ⊢ fuel_burning_triple s i E G G
        (P ∗ crP_obls g ℓ1 K ∗ Φ ∗ treg ∗ £n 1)
        e
        Q.
  Proof.
    iIntros "(H& %LEl& %HE& %HN) % (TG& HP) POST".
    iDestruct "HP" as "(HP& Cg& HΦ& #TR& LC)".
    iMod (untilI_alloc _ _ _ false _ ℓ2 μ with "Cg") as "(%& %& Cg& Of& #Wl& Acc)". 1: auto.
    iMod ("Acc" $! _ N Φ Ψ with "[] TR LC HΦ") as "HU".
    { iPureIntro. done. }
    iPoseProof ("H" with "[$TG $HP $Cg $HU $Wl $Of]") as "WP". 1: auto.
    iApply ("WP" with "POST").
  Qed.

End until.
