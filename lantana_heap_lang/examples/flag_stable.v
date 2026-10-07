From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Import step_tactics.

(** * A flag that stays set: the flag of flag.v, with the set flag in a nested [alwaysI]

    The cell is "[0] until always [1]", the right formula being the invariant
    [alwaysI Nv (l ↦ #1)] that [set] allocates after its store. *)

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
  Let Nv := N.@ "value".

  Remark N_disj_1 : Na ## Np.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑Np ⊆ (⊤ : coPset) ∖ ↑Na.
  Proof. pose proof N_disj_1. set_solver. Qed.

  (** The flag is [0] until it is [1] forever: the set flag is an invariant of its own. *)
  Definition flag_inv (l : loc) k : iProp Σ :=
    untilI Np k (1/2) (l ↦ #0) (alwaysI Nv (l ↦ #1)) ∨ (oblP_discharged k ∗ alwaysI Nv (l ↦ #1)).

  Definition is_flag (l : loc) k ℓ : iProp Σ :=
    witP_layer k ℓ ∗ alwaysI Na (flag_inv l k).

  Definition flag_tk (l : loc) k : iProp Σ :=
    untilI Np k (1/2) (l ↦ #0) (alwaysI Nv (l ↦ #1)).

  Definition flag_itProp (l : loc) : itProp heap_lang Σ :=
    (itProp_true ∧ itProp_always (itProp_until (l ↦ #0) (itProp_always (l ↦ #1)) ∨
                            (itProp_true ∧ itProp_always (l ↦ #1))))%IT.

  Lemma is_flag_temporal l k ℓ : ⊢ is_flag l k ℓ ⊨ₜ flag_itProp l.
  Proof. apply (into_temporal _ _). Qed.

  Lemma flag_tk_temporal l k : ⊢ flag_tk l k ⊨ₜ itProp_until (l ↦ #0) (itProp_always (l ↦ #1)).
  Proof. apply (into_temporal _ _). Qed.

  (** Whenever the flag holds 0, it eventually holds 1 forever: a consequence of the flag's
      guarantee on traces (the until gives the finally; an always holds now), guaranteed
      along with it by the cast. Unlike in flag.v, the antecedent is not needed. *)
  Definition flag_response (l : loc) : trProp heap_lang := (□ ((l ↦ #0) → ◇ □ (l ↦ #1)))%R.

  Lemma flag_response_ext l : itProp_external (flag_itProp l) ⊆ flag_response l.
  Proof.
    rewrite /flag_itProp. etrans; first apply (itProp_ext_of _ _).
    etrans; first apply tr_and_elim_r. apply tr_always_mono, tr_or_elim; apply tr_impl_intro;
      (etrans; first apply tr_and_elim_l).
    - apply tr_until_finally.
    - etrans; [apply tr_and_elim_r|apply tr_finally_intro].
  Qed.

  Lemma is_flag_response l k ℓ :
    ⊢ is_flag l k ℓ ⊨ₜ itProp_cast (flag_itProp l) (flag_response l) (flag_response_ext l).
  Proof. iApply temporal_cast. iApply is_flag_temporal. Qed.

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
    iMod ("H" $! _ Np (l ↦ #0)%I (alwaysI Nv (l ↦ #1))%I with "[Ptr]") as "H".
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
    (* The set flag becomes an invariant: the right formula of the until. *)
    iMod (alwaysI_alloc _ Nv with "Ptrl") as "#Av".
    iPoseProof ("ACCinv" $! p K Ink with "Gg Kk Av") as "ACCinv".
    iMod ("ACCinv" $! _) as "ACCinv". iMod "ACCinv" as "(_& Gg& #Odk)".
    iApply fupd_sfmupd. iApply fupd_mask_intro; first solve_ndisj. iIntros "close".
    iMod "close" as "_". iModIntro. iModIntro. iSplitR.
    { iNext. iRight. iFrame "Odk Av". }
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
    (* The set flag becomes an invariant: the right formula of the until. *)
    iMod (alwaysI_alloc _ Nv with "Ptrl") as "#Av".
    iPoseProof ("ACCinv" $! (PThread i) G Ink with "TG Kk Av") as "ACCinv".
    iMod ("ACCinv" $! _) as "ACCinv". iMod "ACCinv" as "(_& TG& #Odk)".
    iApply fupd_sfmupd. iApply fupd_mask_intro; first solve_ndisj. iIntros "close".
    iMod "close" as "_". iModIntro. iModIntro. iSplitR.
    { iNext. iRight. iFrame "Odk Av". }
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
      iDestruct "inv" as "[>#Odk #Av]".
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lwp_lc_later with "LC1"). iNext.
      (* The set flag is read from its own invariant. *)
      iInv "Av" as ">Ptrl".
      iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_load _ ∅ 0 with "[$TE $TG $Ptrl $GF1]"). 1: done.
      iIntros "[TE [(_& TG& _) Ptrl]]".
      iModIntro. iSplitL "Ptrl"; first by iFrame.
      iModIntro. iSplitR.
      { iNext. iRight. iFrame "Odk Av". }
      iClear "LC". iModIntro. lwp_pure_lc lc.
      lwp_pures.
      iModIntro. lwp_finish.
      iModIntro. iApply ("HΦ" with "[$]").
  Qed.

End proof.

Section trace.

  (** The flag at the level of traces: [0] until [1] forever, or [1] forever. *)
  Definition is_flag_tr (l : loc) : trProp heap_lang :=
    tr_always (tr_until (l ↦ #0) (tr_always (l ↦ #1)) ∨ tr_always (l ↦ #1))%R.
  Lemma flag_itProp_impl {Σ : gFunctors} l : itProp_external (flag_itProp (Σ:=Σ) l) ⊆ is_flag_tr l.
  Proof.
    rewrite /flag_itProp. etrans; first apply (itProp_ext_of _ _).
    etrans; first apply tr_and_elim_r. apply tr_always_mono, tr_or_mono; [reflexivity|apply tr_and_elim_r].
  Qed.

  (** Unlike in flag.v, the guarantee says that once the flag is [1], it stays [1]. *)
  Definition flag_stays_tr (l : loc) : trProp heap_lang :=
    tr_always (l ↦ #1 → tr_always (l ↦ #1))%R.

  Lemma is_flag_tr_stays l : is_flag_tr l ⊆ flag_stays_tr l.
  Proof.
    apply tr_always_mono, tr_or_elim; apply tr_impl_intro; last apply tr_and_elim_l.
    etrans; [apply tr_and_mono; [apply tr_until_unfold|reflexivity]|].
    etrans; first apply tr_and_or_distr. apply tr_or_elim; first apply tr_and_elim_l.
    etrans; [apply tr_and_mono; [apply tr_and_elim_l|reflexivity]|].
    etrans; first apply tr_pointsto_agree. apply tr_pure_elim. intros Heq. by simplify_eq.
  Qed.

  Lemma flag_itProp_stays {Σ : gFunctors} l : itProp_external (flag_itProp (Σ:=Σ) l) ⊆ flag_stays_tr l.
  Proof. etrans; [apply flag_itProp_impl|apply is_flag_tr_stays]. Qed.

  (** The run 0, 1, 0, 1, 1, ... satisfies the guarantee of flag.v, but not this one. *)
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

  Lemma flag_run_goes_back l : ¬ flag_stays_tr l (0, flag_run l).
  Proof.
    intros H. unfold flag_stays_tr, tr_always, tr_impl in H. cbv beta iota in H.
    specialize (H 1 ltac:(lia)).
    assert (H1 : tr_state (pointsto_sat l (DfracOwn 1) #1) (1, flag_run l)).
    { apply flag_run_at. case_decide; [lia|done]. }
    specialize (H H1 2 ltac:(lia)). apply flag_run_at in H. case_decide; [done|lia].
  Qed.

  Lemma flag_run_violates_guarantee {Σ : gFunctors} l : ¬ itProp_external (flag_itProp (Σ:=Σ) l) (0, flag_run l).
  Proof. intros H. by eapply flag_run_goes_back, flag_itProp_stays. Qed.

End trace.
