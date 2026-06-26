From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

Module Flag.

  Definition set : val :=
    λ: "x", "x" <- #1.

  Definition wait : val := 
    rec: "wait" "x" :=
      if: !"x" = #0
      then "wait" "x"
      else #1.

End Flag.

Section proof.
  Context `{!heapGS Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let N := nroot.@ "flag".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".

  Remark N_disj_1 : Na ## Np.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑Np ⊆ (⊤ : coPset) ∖ ↑Na.
  Proof. pose proof N_disj_1. set_solver. Qed.

  Definition flag_inv_tf (l : loc) k : tf Σ :=
    ((untilP Np k (1/2) (l ↦ #0) (l ↦ #1)) ∨ (⟨oblP_discharged k⟩ ∗ (l ↦ #1))).

  Definition is_flag_tf (l : loc) k ℓ : tf Σ :=
    ⟨witP_layer k ℓ⟩ ∗ alwaysP Na (flag_inv_tf l k).

  Definition is_flag (l : loc) k ℓ : iProp Σ :=
    (witP_layer k ℓ) ∗ ⟦alwaysP Na (flag_inv_tf l k)⟧ₗ.

  (** The main proofs. *)
  Global Instance is_flag_persistent l k ℓ : Persistent (is_flag l k ℓ).
  Proof. rewrite /is_flag. tf_red. apply _. Qed.

  Lemma is_flag_tf_red l k ℓ : ⟦is_flag_tf l k ℓ⟧ₗ = is_flag l k ℓ.
  Proof. rewrite /is_flag /is_flag_tf. tf_red. auto. Qed.

  Lemma Flag_set_spec :
    ⊢ ∃ μ, ∀ lc i l G g K k ℓ ℓg,
    l{{{ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g 0 μ) ∗
         crP_obls g ℓg K ∗ ⌜ k ∈ K ⌝ ∗
         (* The other half of the until ownership for the pointsto. *)
         ⟦untilP Np k (1/2) (l ↦ #0) (l ↦ #1)⟧ₗ ∗
         is_flag l k ℓ }}}
      Flag.set #l @ i
    l{{{ RET #(); £ lc ∗ thP_carriers i G ∗
                  crP_obls g ℓg (K ∖ {[k]}) ∗ oblP_discharged k }}}.
  Proof.
    iExists 10. iIntros (lc i l G g K k ℓ ℓg Φ) "!> HP HΦ".
    iDestruct "HP" as "(TG& GF& Gg& %Ink& HU& #is_flag)".
    iDestruct "is_flag" as "(#Wlk& HA)". iEval (do 2 tf_red) in "HA".
    rewrite /Flag.set.
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_bind (Store _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iInv "HA" as "inv". iDestruct "inv" as "[inv | inv]"; cycle 1.
    { iDestruct "inv" as "[>inv _]".
      iEval (rewrite tf_until_logic) in "HU". iDestruct "HU" as "[Oak _]".
      iPoseProof (oblP_assigned_discharged_false with "Oak inv") as "%". done. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iCombine "HU inv" as "inv".
    iMod (tf_until_discharge with "inv") as "inv".
    { apply N_subseteq_1. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "[Ptrl ACCinv]".
    iApply lwp_sfmupd.
    iEval (rewrite tf_atomic_logic) in "Ptrl".
    iApply (lwp_store _ ∅ 0 with "[$Ptrl $TG $GF1]"). 1: done.
    iIntros "((_& TG& _)& Ptrl)".
    iMod ("ACCinv" $! _) as "ACCinv".
    iApply sfmupd_fupd_acc. iMod ("ACCinv" with "Ptrl") as "ACCinv".
    iModIntro. 
    iPoseProof ("ACCinv" with "[] Gg") as "ACCinv".
    { iPureIntro. set_solver. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("ACCinv" $! _) as "ACCinv". iIntros "!> !>". iMod "ACCinv" as "(Ptrl& Gg& #Odk)".
    iIntros "!> !>". iSplitL "Ptrl".
    { iNext. iRight. iFrame. eauto. }
    iApply ("HΦ" with "[$Q_LC $TG $Gg $Odk]").
  Qed.

  Lemma Flag_wait_spec :
    ⊢ ∃ μ, ∀ lc i l G k ℓ,
    l{{{ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g (ℓ ⊕ 1)%ordi μ) ∗
         is_flag l k ℓ }}}
      Flag.wait #l @ i
    l{{{ RET #1; £ lc ∗ thP_carriers i G ∗ oblP_discharged k }}}.
  Proof.
    iExists ((1 × ▽) ⊕ 1)%M. iIntros (lc i l G k ℓ Φ) "!> HP HΦ".
    iDestruct "HP" as "(TG& GF& #is_flag)".
    iDestruct "is_flag" as "(#Wlk& HA)". iEval (do 2 tf_red) in "HA".
    rewrite /Flag.wait.
    iPoseProof (crP_fuel_add_set with "GF") as "[W_GF GF]".
    (* Liveness induction *)
    iPoseProof (wit_fuels_init with "Wlk") as "(%& Wf0)".
    iMod (wit_fuels_add_map with "Wf0 W_GF") as "Wf".
    { apply hessenberg.add_lt_l. rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
    iClear "Wf0". iInduction α as [α IH] using WFOCM.ind.
    iMod (crP_fuel_extend_set _ ℓ _ (10)%M with "GF") as "GF".
    { apply hessenberg.add_lt_l. rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure_lc 100.
    lwp_bind (Load _).
    iModIntro.
    iInv "HA" as "inv". iDestruct "inv" as "[inv | inv]".
    - (* Induction case. *)
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lwp_lc_later with "LC1"). iNext.
      iMod (tf_until_acc with "inv") as "inv".
      1: apply N_subseteq_1.
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lwp_lc_later with "LC1"). iNext.
      iDestruct "inv" as "(Ptrl& inv_acc)".
      iEval (rewrite tf_atomic_logic) in "Ptrl".
      iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_load _ ({[k]} : gset _) 0 with "[$TG $Ptrl $GF1]").
      { iApply big_sepS_singleton. eauto. }
      iIntros "[(_& TG& Rs) Ptrl]".
      iEval (rewrite big_sepS_singleton) in "Rs". iDestruct "Rs" as "[Wck | #Odk]"; cycle 1.
      { iMod ("inv_acc" with "[Ptrl]") as "H".
        { iNext. iFrame. }
        iPoseProof (tf_until_discharged_false with "H Odk") as "%". done. }
      iMod ("inv_acc" with "[Ptrl]") as "inv".
      { iNext. iFrame. }
      iModIntro. iModIntro. iSplitL "inv".
      { iFrame. }
      iModIntro; lwp_pure_one.
      (* rewrite bool_decide_false; cycle 1. *)
      (* { intro F. simplify_eq /=. } *)
      iModIntro; lwp_pure_one.
      (* iModIntro; lwp_pure_one. *)
      iModIntro.
      iMod (wit_fuels_decr with "Wf Wck") as "(%& %LTα& Wf'& Fkl')".
      iApply ("IH" $! α0 LTα with "TG HΦ [Fkl'] Wf'").
      rewrite map_union_empty. iPoseProof (big_sepM_gset_to_gmap with "Fkl'") as "H". iFrame.
    - (* k is discharged. *)
      iDestruct "inv" as ">(#Odk& Ptrl)".
      iEval (rewrite tf_atomic_logic) in "Ptrl".
      iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_load _ ∅ 0 with "[$TG $Ptrl $GF1]"). 1: done.
      iIntros "[(_& TG& _) Ptrl]".
      iModIntro. iSplitL "Ptrl".
      { iNext. iRight. iFrame. eauto. }
      iClear "LC". iModIntro. lwp_pure_lc lc.
      lwp_pures.
      iModIntro. lwp_finish.
      iModIntro. iApply ("HΦ" with "[$]").
  Qed.

  Lemma is_flag_init E l g K ℓ ℓg μ :
    (ℓg <= ℓ)%ordi →
    l ↦ #0 -∗
    crP_obls g ℓg K -∗
    |={E}=>m ∃ k, ⌜ k ∉ K ⌝ ∗ crP_obls g ℓg ({[k]} ∪ K) ∗ oblP_fuel k ℓ μ ∗
                 ⟦untilP Np k (1/2) (l ↦ #0) (l ↦ #1)⟧ₗ ∗ is_flag l k ℓ.
  Proof.
    iIntros (Hle) "Ptr Gg". rewrite /is_flag.
    iMod (tf_until_alloc _ _ _ false _ ℓ μ with "Gg") as "(%& $& $& $& $& H)". 1: auto.
    iMod ("H" $! _ Np (l ↦ #0)%F (l ↦ #1)%F with "[Ptr]") as "H".
    { iNext. iFrame. }
    iDestruct "H" as "[H1 H2]".
    do 2 tf_red.
    iMod (inv_alloc with "[H1]") as "$". 2: by iFrame.
    iNext. by iLeft.
  Qed.

End proof.

Section trace.

  (** Export to trace properties *)
  Definition is_flag_tp (l : loc) : tp :=
    (tp_always (((tp_until (l ↦ #0) (l ↦ #1)) ∨ (l ↦ #1))))%P.

  (** TODO: weaken the strict equality to semantics equivalence/implication. *)
  Definition is_flag_tp' (l : loc) : tp :=
    (tp_true ∧ tp_always (((tp_until (l ↦ #0) (l ↦ #1)) ∨ (tp_true ∧ (l ↦ #1)))))%P.

  Remark is_flag_tf_to_tp' `{!heapGS Σ} l k ℓ :
    tf_to_tp (is_flag_tf l k ℓ) = is_flag_tp' l.
  Proof. done. Qed.

  Remark is_flag_tp_impl l :
    ∀ τ, tp_trace (is_flag_tp' l) τ → tp_trace (is_flag_tp l) τ.
  Proof.
    simpl. unfold_trProp. intros. destruct τ. destruct H. intros. specialize (H0 _ H1).
    destruct H0.
    - destruct H0 as (?&?&?&?). left. eexists. split_and !; eauto.
    - destruct H0. right. eauto.
  Qed.

End trace.
