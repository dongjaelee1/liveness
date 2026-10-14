From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Import step_tactics.

(** * A flag: [set] writes [1] and [wait] spins until it reads [1]

    The cell is "[0] until [1]" (an until on the flag's obligation), so [wait] terminates. *)

Module Flag.

  Definition init : val :=
    λ: <>, ref #0.

  Definition set : val :=
    λ: "x", "x" <- #1.

  Definition wait : val :=
    rec: "wait" "x" :=
      if: !"x" ≠ #1
      then "wait" "x"
      else #1.

End Flag.

Section proof.
  Context `{!heapGS Σ}.

  Let N := nroot.@ "flag".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".

  Remark N_disj_1 : Na ## Np.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑Np ⊆ (⊤ : coPset) ∖ ↑Na.
  Proof. pose proof N_disj_1. set_solver. Qed.

  (** The flag is [0] until it is [1], after which it stays [1]. *)
  Definition flag_inv (l : loc) k : iProp Σ :=
    untilI Np k (1/2) (l ↦ #0) (l ↦ #1) ∨ (oblP_discharged k ∗ l ↦ #1).

  Definition is_flag (l : loc) k ℓ : iProp Σ :=
    witP_layer k ℓ ∗ alwaysI Na (flag_inv l k).

  Definition flag_tk (l : loc) k : iProp Σ :=
    untilI Np k (1/2) (l ↦ #0) (l ↦ #1).

  Definition flag_itrProp (l : loc) : itrProp heap_lang Σ :=
    (itrProp_true ∧ itrProp_always (itrProp_until (l ↦ #0) (l ↦ #1) ∨ (itrProp_true ∧ l ↦ #1)))%ITR.

  Lemma guar_is_flag l k ℓ : ⊢ is_flag l k ℓ ⊨ₜ flag_itrProp l.
  Proof. apply (into_guar _ _). Qed.

  Lemma guar_flag_tk l k : ⊢ flag_tk l k ⊨ₜ itrProp_until (l ↦ #0) (l ↦ #1).
  Proof. apply (into_guar _ _). Qed.

  (** Whenever the flag holds 0, it eventually holds 1: from the flag's guarantee on traces
      (the until gives the finally; in the other branch the cell holds 1, not 0). *)
  Definition flag_response (l : loc) : trProp heap_lang := (□ ((l ↦ #0) → ◇ (l ↦ #1)))%R.

  Lemma flag_response_ext l : itrProp_external (flag_itrProp l) ⊆ flag_response l.
  Proof.
    rewrite /flag_itrProp. etrans; first apply (itrProp_ext_of _ _).
    etrans; first apply tr_and_elim_r. apply tr_always_mono, tr_or_elim; apply tr_impl_intro.
    - etrans; [apply tr_and_elim_l|apply tr_until_finally].
    - etrans; [apply tr_and_mono; [apply tr_and_elim_r|reflexivity]|].
      etrans; first apply tr_pointsto_agree. apply tr_pure_elim. intros Heq. by simplify_eq.
  Qed.

  Lemma is_flag_response l k ℓ :
    ⊢ is_flag l k ℓ ⊨ₜ itrProp_cast (flag_itrProp l) (flag_response l) (flag_response_ext l).
  Proof. iApply guar_cast. iApply guar_is_flag. Qed.

  (** The main proofs. *)
  Global Instance is_flag_persistent l k ℓ : Persistent (is_flag l k ℓ).
  Proof. apply _. Qed.

  (** The until and the invariant are registered; the obligation of the flag is a new child
      of the parent [p]. *)
  Lemma is_flag_init E l p K ℓ μ :
    parP_le p ℓ -∗
    l ↦ #0 -∗
    parP_kids p K -∗
    |={E}=>m ∃ k, ⌜ k ∉ K ⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗ oblP_fuel k ℓ μ ∗
                 flag_tk l k ∗ is_flag l k ℓ.
  Proof.
    iIntros "B Ptr Kp". rewrite /is_flag /flag_tk /flag_inv.
    iMod (untilI_alloc _ _ _ ℓ μ with "B Kp") as "(%& $& $& $& $& $& H)".
    iMod ("H" $! _ Np (l ↦ #0)%I (l ↦ #1)%I with "[Ptr]") as "H".
    { iNext. iFrame. }
    iDestruct "H" as "[H1 H2]".
    iMod (alwaysI_alloc E Na _ with "[H1]") as "$"; last by iFrame.
    iNext. by iLeft.
  Qed.

  Lemma Flag_init_spec :
    ⊢ ∃ μ, ∀ lc i G p K ℓ m C,
    l{{{ thread_expr i C (Flag.init #()) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) ∗
         parP_le p ℓ ∗ parP_kids p K }}}
      Flag.init #() @ i
    l{{{ (x : loc) k, RET #x; thread_expr i C (#x) ∗ £ lc ∗ thP_kids i G ∗
                      (⌜k ∉ K⌝) ∗
                      parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                      oblP_fuel k ℓ m ∗
                      flag_tk x k ∗ is_flag x k ℓ }}}.
  Proof.
    iExists 10. iIntros (lc i G p K ℓ m C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& B& Cg)".
    rewrite /Flag.init.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc lc.
    iApply sfmupd_lwp_sfmupd.
    lwp_bind (AllocN _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (ptrx) "[TE ((_& TG& _)& Ptrx& _)]".
    iMod (is_flag_init _ ptrx _ _ (ℓ) m with "B Ptrx Cg") as "(%k& %Hk& Cg& Kk& Of& Ftk& #is_flag)".
    iApply ("HΦ" with "[$TE $LC $TG $Cg $Kk $Of $Ftk $is_flag]").
    iPureIntro. auto.
  Qed.

  Lemma Flag_set_spec :
    ⊢ ∃ μ, ∀ lc i l G p K k ℓ C,
    l{{{ thread_expr i C (Flag.set #(l : loc)) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) ∗
         parP_kids p K ∗ ⌜ k ∈ K ⌝ ∗ oblP_kids k ∅ ∗
         (* The other half of the until ownership for the pointsto. *)
         flag_tk l k ∗
         is_flag l k ℓ }}}
      Flag.set #l @ i
    l{{{ RET #(); thread_expr i C (#()) ∗ £ lc ∗ thP_kids i G ∗
                  parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k }}}.
  Proof.
    iExists 10. iIntros (lc i l G p K k ℓ C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Gg& %Ink& Kk& HU& #is_flag)".
    iDestruct "is_flag" as "(#Wlk& HA)".
    rewrite /Flag.set.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_bind (Store _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iInv "HA" as "inv". iDestruct "inv" as "[inv | inv]"; cycle 1.
    { iDestruct "inv" as "[>inv _]".
      iEval (rewrite /flag_tk !untilI_unfold) in "HU". iDestruct "HU" as "[Oak _]".
      iPoseProof (oblP_assigned_discharged_false with "Oak inv") as "%". done. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iCombine "HU inv" as "inv".
    iMod (untilI_discharge with "inv") as "inv".
    { apply N_subseteq_1. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "[Ptrl ACCinv]".
    iApply lwp_sfmupd.
    iApply (lwp_store _ ∅ 0 with "[$TE $Ptrl $TG $GF1]"). 1: done.
    iIntros "[TE ((_& TG& _)& Ptrl)]".
    iPoseProof ("ACCinv" $! p K Ink with "Gg Kk Ptrl") as "ACCinv".
    iMod ("ACCinv" $! _) as "ACCinv". iMod "ACCinv" as "(Ptrl& Gg& #Odk)".
    iApply fupd_sfmupd. iApply fupd_mask_intro; first solve_ndisj. iIntros "close".
    iMod "close" as "_". iModIntro. iModIntro. iSplitL "Ptrl".
    { iNext. iRight. iFrame. eauto. }
    iApply ("HΦ" with "[$TE $Q_LC $TG $Gg $Odk]").
  Qed.

  (** The same operations when the flag's obligation is a child of the calling thread itself. *)
  Lemma Flag_init_thread_spec :
    ⊢ ∃ μ, ∀ lc i G ℓ m C,
    l{{{ thread_expr i C (Flag.init #()) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) }}}
      Flag.init #() @ i
    l{{{ (x : loc) k, RET #x; thread_expr i C (#x) ∗ £ lc ∗
                      (⌜k ∉ G⌝) ∗
                      thP_kids i ({[k]} ∪ G) ∗ oblP_kids k ∅ ∗
                      oblP_fuel k ℓ m ∗
                      flag_tk x k ∗ is_flag x k ℓ }}}.
  Proof.
    iExists 10. iIntros (lc i G ℓ m C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF)".
    rewrite /Flag.init.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc lc.
    iApply sfmupd_lwp_sfmupd.
    lwp_bind (AllocN _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (ptrx) "[TE ((_& TG& _)& Ptrx& _)]".
    iMod (is_flag_init _ ptrx _ _ (ℓ) m with "[] Ptrx TG") as "(%k& %Hk& TG& Kk& Of& Ftk& #is_flag)".
    { iApply parP_le_thread. }
    iApply ("HΦ" with "[$TE $LC $TG $Kk $Of $Ftk $is_flag]").
    iPureIntro. auto.
  Qed.

  Lemma Flag_set_thread_spec :
    ⊢ ∃ μ, ∀ lc i l G k ℓ C,
    l{{{ thread_expr i C (Flag.set #(l : loc)) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) ∗
         ⌜ k ∈ G ⌝ ∗ oblP_kids k ∅ ∗
         flag_tk l k ∗
         is_flag l k ℓ }}}
      Flag.set #l @ i
    l{{{ RET #(); thread_expr i C (#()) ∗ £ lc ∗ thP_kids i (G ∖ {[k]}) ∗ oblP_discharged k }}}.
  Proof.
    iExists 10. iIntros (lc i l G k ℓ C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& %Ink& Kk& HU& #is_flag)".
    iDestruct "is_flag" as "(#Wlk& HA)".
    rewrite /Flag.set.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_bind (Store _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iInv "HA" as "inv". iDestruct "inv" as "[inv | inv]"; cycle 1.
    { iDestruct "inv" as "[>inv _]".
      iEval (rewrite /flag_tk !untilI_unfold) in "HU". iDestruct "HU" as "[Oak _]".
      iPoseProof (oblP_assigned_discharged_false with "Oak inv") as "%". done. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iCombine "HU inv" as "inv".
    iMod (untilI_discharge with "inv") as "inv".
    { apply N_subseteq_1. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "[Ptrl ACCinv]".
    iApply lwp_sfmupd.
    iApply (lwp_store _ ∅ 0 with "[$TE $Ptrl $TG $GF1]"). 1: done.
    iIntros "[TE ((_& TG& _)& Ptrl)]".
    iPoseProof ("ACCinv" $! (PThread i) G Ink with "TG Kk Ptrl") as "ACCinv".
    iMod ("ACCinv" $! _) as "ACCinv". iMod "ACCinv" as "(Ptrl& TG& #Odk)".
    iApply fupd_sfmupd. iApply fupd_mask_intro; first solve_ndisj. iIntros "close".
    iMod "close" as "_". iModIntro. iModIntro. iSplitL "Ptrl".
    { iNext. iRight. iFrame. eauto. }
    iApply ("HΦ" with "[$TE $Q_LC $TG $Odk]").
  Qed.

  Lemma Flag_wait_spec :
    ⊢ ∃ μ, ∀ lc i l G k ℓ C,
    l{{{ thread_expr i C (Flag.wait #(l : loc)) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g (ℓ ⊕ 1)%ordi μ) ∗
         is_flag l k ℓ }}}
      Flag.wait #l @ i
    l{{{ RET #1; thread_expr i C (#1) ∗ £ lc ∗ thP_kids i G ∗ oblP_discharged k }}}.
  Proof.
    iExists ((5 × ▽) ⊕ 5)%M. iIntros (lc i l G k ℓ C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& #is_flag)".
    iDestruct "is_flag" as "(#Wlk& HA)".
    rewrite /Flag.wait.
    iPoseProof (oblP_fuel_add_set with "GF") as "[W_GF GF]".
    (* Liveness induction *)
    iRevert "TE TG HΦ GF". iPoseProof (wit_layer_ind with "[$Wlk $W_GF]") as ">H".
    { apply hessenberg.add_lt_l. rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
    2:{ iApply "H". }
    iIntros "!> IH !> TE TG HΦ GF".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc 100.
    lwp_bind (Load _).
    iModIntro.
    iInv "HA" as "inv". iDestruct "inv" as "[inv | inv]".
    - (* Induction case. *)
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lwp_lc_later with "LC1"). iNext.
      iMod (untilI_acc with "inv") as "inv".
      1: apply N_subseteq_1.
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lwp_lc_later with "LC1"). iNext.
      iDestruct "inv" as "(Ptrl& inv_acc)".
      iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_load _ ({[k]} : gset _) 0 with "[$TE $TG $Ptrl $GF1]").
      { iApply big_sepS_singleton. eauto. }
      iIntros "[TE [(_& TG& Rs) Ptrl]]".
      iEval (rewrite big_sepS_singleton) in "Rs". iDestruct "Rs" as "[Wck | #Odk]"; cycle 1.
      { iMod ("inv_acc" with "[Ptrl]") as "H".
        { iNext. iFrame. }
        iPoseProof (untilI_discharged_false with "H Odk") as "%". done. }
      iMod ("inv_acc" with "[Ptrl]") as "inv".
      { iNext. iFrame. }
      iModIntro. iModIntro. iSplitL "inv".
      { iFrame. }
      iModIntro; lwp_pure_one.
      iModIntro; lwp_pure_one.
      iModIntro; lwp_pure_one.
      iModIntro.
      iMod ("IH" with "Wck") as "[GF' IH]". iApply ("IH" with "TE TG HΦ GF'").
    - (* k is discharged. *)
      iDestruct "inv" as ">(#Odk& Ptrl)".
      iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_load _ ∅ 0 with "[$TE $TG $Ptrl $GF1]"). 1: done.
      iIntros "[TE [(_& TG& _) Ptrl]]".
      iModIntro. iSplitL "Ptrl".
      { iNext. iRight. iFrame. eauto. }
      iClear "LC". iModIntro. lwp_pure_lc lc.
      lwp_pures.
      iModIntro. lwp_finish.
      iModIntro. iApply ("HΦ" with "[$]").
  Qed.

End proof.

Section trace.

  (** The flag at the level of traces: [0] until [1], and [1] from then on. *)
  Definition is_flag_tr (l : loc) : trProp heap_lang :=
    tr_always (tr_until (l ↦ #0) (l ↦ #1) ∨ (l ↦ #1))%R.
  Lemma flag_itrProp_impl {Σ : gFunctors} l : itrProp_external (flag_itrProp (Σ:=Σ) l) ⊆ is_flag_tr l.
  Proof.
    rewrite /flag_itrProp. etrans; first apply (itrProp_ext_of _ _).
    etrans; first apply tr_and_elim_r. apply tr_always_mono, tr_or_mono; [reflexivity|apply tr_and_elim_r].
  Qed.

  (** The guarantee does not say that the flag stays [1]: the run 0, 1, 0, 1, 1, ...
      satisfies it. The invariant describes each state, not the history (see flag_stable.v). *)
  Definition flag_run (l : loc) : nat → trace_state heap_lang :=
    λ n, ((∅, {| heap := {[l := Some (if decide (n = 0 ∨ n = 2) then #0 else #1)]};
                 used_proph_id := ∅ |}), 1%positive, []).

  Lemma flag_run_at l m v :
    tr_state (pointsto_sat l (DfracOwn 1) v) (m, flag_run l) ↔
    v = (if decide (m = 0 ∨ m = 2) then #0 else #1).
  Proof.
    rewrite /tr_state /ts_emb /ts_state /pointsto_sat /trace_now /flag_run /= lookup_insert_eq.
    split; [by intros [= ->]|by intros ->].
  Qed.

  Lemma flag_run_satisfies_guarantee {Σ : gFunctors} l : itrProp_external (flag_itrProp (Σ:=Σ) l) (0, flag_run l).
  Proof.
    split; first done. intros m _. cbn [itrProp_external itrProp_or itrProp_and itrProp_until itrProp_state itrProp_pure].
    rewrite /itrProp_true. cbn [itrProp_external itrProp_pure]. unfold tr_or, tr_and, tr_pure, tr_until. cbv beta iota.
    destruct (decide (m = 0 ∨ m = 2)) as [Hm|Hm].
    - left. exists (S m). split_and!; [lia| |].
      + apply flag_run_at. rewrite decide_False; [done|lia].
      + intros l' Hl'. apply flag_run_at. rewrite decide_True; [done|lia].
    - right. split; first done. apply flag_run_at. by rewrite decide_False.
  Qed.

  Lemma flag_run_goes_back l : ¬ tr_always (λ τ, tr_state (pointsto_sat l (DfracOwn 1) #1) τ →
      tr_always (tr_state (pointsto_sat l (DfracOwn 1) #1)) τ) (0, flag_run l).
  Proof.
    intros H. unfold tr_always in H. cbv beta iota in H. specialize (H 1 ltac:(lia)).
    assert (H1 : tr_state (pointsto_sat l (DfracOwn 1) #1) (1, flag_run l)).
    { apply flag_run_at. case_decide; [lia|done]. }
    specialize (H H1 2 ltac:(lia)). apply flag_run_at in H. case_decide; [done|lia].
  Qed.

End trace.
