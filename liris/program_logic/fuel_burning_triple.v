From iris.proofmode Require Import proofmode.
From liris.program_logic Require Export lifting temporal_logic.

Definition fuel_burning_triple `{SI : indexT} `{!lirisGS Λ Σ} : stuckness → thread_id → coPset -> gset ocid → gset ocid → iProp Σ → expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
  λ s i E G G' P e Q,
    l{{{ thP_carriers i G ∗ P }}} e @ s; i; E l{{{v, RET v; thP_carriers i G' ∗ Q v }}}%I.

Section proof.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types e : expr Λ.

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
    iIntros "#H % !> (TG& HP) POST".
    iMod (carrier_alloc _ _ _ ℓ μ with "TG") as "(%& %& TG& Cg& Fg)".
    iPoseProof ("H" with "[$TG $HP $Cg $Fg]") as "WP". 1: auto.
    iApply ("WP" with "POST").
  Qed.

  Lemma fuel_burning_triple_until_discharge s i E G P e Q N k (Φ Ψ : tf Σ) `{!Atomic (stuckness_to_atomicity s) e} g ℓ K :
    TCEq (to_val e) None →
    ↑N ⊆ E →
    fuel_burning_triple s i (E ∖ ↑N) G G
      (P ∗ ⟦Φ⟧ₗ)%I
      e
      (λ v, Q v ∗ ⟦Ψ⟧ₗ ∗ crP_obls g ℓ K ∗ ⌜k ∈ K⌝)%I
    ⊢ fuel_burning_triple s i E G G
        (P ∗ ⟦untilP N k 1 Φ Ψ⟧ₗ ∗ £ 2)%I
        e
        (λ v, Q v ∗ ⟦Ψ⟧ₗ ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)%I.
  Proof.
    iIntros (He Hmask) "#H % !> (TG& HP& HU& LC) POST".
    iMod (tf_until_discharge with "HU") as "HUacc". 1: auto.
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

  Lemma fuel_burning_triple_until_discharge_ex s i E G P e Q N k (Φ Ψ : tf Σ) `{!Atomic (stuckness_to_atomicity s) e} :
    TCEq (to_val e) None →
    ↑N ⊆ E →
    fuel_burning_triple s i (E ∖ ↑N) G G
      (P ∗ ⟦Φ⟧ₗ)%I
      e
      (λ v, ∃ g ℓ K, Q v ∗ ⟦Ψ⟧ₗ ∗ crP_obls g ℓ K ∗ ⌜k ∈ K⌝)%I
    ⊢ fuel_burning_triple s i E G G
        (P ∗ ⟦untilP N k 1 Φ Ψ⟧ₗ ∗ £ 2)%I
        e
        (λ v, ∃ g ℓ K, Q v ∗ ⟦Ψ⟧ₗ ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)%I.
  Proof.
    iIntros (He Hmask) "#H % !> (TG& HP& HU& LC) POST".
    iMod (tf_until_discharge with "HU") as "HUacc". 1: auto.
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

  Lemma fuel_burning_triple_until_alloc s i E G P e Q g K ℓ1 ℓ2 μ N Φ Ψ :
    (∀ k, fuel_burning_triple s i E G G
            (P ∗ ⌜k ∉ K⌝ ∗ crP_obls g ℓ1 ({[k]} ∪ K) ∗
             ⟦untilP N k 1 Φ Ψ⟧ₗ ∗ witP_layer k ℓ2 ∗ oblP_fuel k ℓ2 μ)
            e
            Q)
      ∧ ⌜(ℓ1 <= ℓ2)%ordi⌝
    ⊢ fuel_burning_triple s i E G G
        (P ∗ crP_obls g ℓ1 K ∗ ⟦Φ⟧ₗ)
        e
        Q.
  Proof.
    iIntros "(#H& %LEl) % !> (TG& HP) POST".
    iDestruct "HP" as "(HP& Cg& HΦ)".
    iMod (tf_until_alloc _ _ _ false _ ℓ2 μ with "Cg") as "(%& %& Cg& Of& #Wl& Acc)". 1: auto.
    iMod ("Acc" $! _ N Φ Ψ with "HΦ") as "HU".
    iPoseProof ("H" with "[$TG $HP $Cg $HU $Wl $Of]") as "WP". 1: auto.
    iApply ("WP" with "POST").
  Qed.

End proof.
