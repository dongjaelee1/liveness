From iris.proofmode Require Import proofmode.
From liris.program_logic Require Export lifting temporal_logic.

Definition step_triple `{SI : indexT} `{!lirisGS Λ Σ} : stuckness → thread_id → coPset -> gset ocid → gset ocid → iProp Σ → expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
  λ s i E G G' P e Q,
    l{{{ thP_carriers i G ∗ P }}} e @ s; i; E l{{{v, RET v; thP_carriers i G' ∗ Q v }}}%I.

(** lwpupd should be inside the triple, and should be wrapped to be persistent. *)
(* Definition fuel_burning_triple `{SI : indexT} `{!lirisGS Λ Σ} : stuckness → thread_id → coPset -> gset ocid → gset ocid → iProp Σ → expr Λ -> (val Λ -> iProp Σ) -> iProp Σ := *)
(*   λ s i E G G' P e Q, *)
(*     lwpupd i E e (step_triple s i E G G' P e Q). *)

Section proof.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types e : expr Λ.

  Lemma step_triple_until_discharge s i E G P e Q N k (Φ Ψ : tf Σ) :
    ↑N ⊆ E →
    Atomic (stuckness_to_atomicity s) e →
    step_triple s i (E ∖ ↑N) G G
      (P ∗ ⟦Φ⟧ₗ)%I
      e
      (λ v, ∃ g ℓ K, Q v ∗ ⟦Ψ⟧ₗ ∗ crP_obls g ℓ K ∗ ⌜k ∈ K⌝)%I
    ⊢ step_triple s i E G G
        (P ∗ ⟦untilP N k 1 Φ Ψ⟧ₗ ∗ £ 2)%I
        e
        (λ v, Q v ∗ ∃ g ℓ K, ⟦Ψ⟧ₗ ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)%I.
  Proof.
    iIntros (Hmask Hatomic) "#H % !> (TG& HP& HU& LC) POST".
    iMod (tf_until_discharge with "HU") as "HUacc". 1: auto.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "HUacc" as "[HΦ HUacc]".
    iApply lwp_sfmupd.
    iPoseProof ("H" $! (λ v, |={E ∖ ↑N}=>m |={E ∖ ↑N,E}=> Φ0 v)%I with "[$TG $HP $HΦ]") as "Hwp".
    iApply "Hwp". iIntros (v) "(TG& %&%&%& HQ& HΨ& Cg& %Ink)".
    iMod ("HUacc" with "HΨ") as ">HUacc".
    iPoseProof ("HUacc" with "[//] Cg") as "HUacc".
    iApply (lc_sfmupd_add_later with "LC"). iNext.
    iMod ("HUacc" $! _) as "HUacc". iModIntro.
    iMod "HUacc" as "(HΨ& Cg& #Od)".
    iApply ("POST" with "[$TG $HQ $HΨ $Cg]"). eauto.
  Qed.

End proof.
