From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Import step_tactics.

(** * Test: a discharge in the pre-step modality, with nested structures

    The commitment [◇ (x ↦ #1 ∗ alwaysI Na (y ↦ #7) ∗ ◇ (x ↦ #2))] is discharged in the
    pre-step modality of [x <- #2], which destroys [x ↦ #1]; adequacy records the nested
    always and until at the discharge position. *)

Module CertDischarge.

  Definition main : val :=
    λ: "x" "y",
      "x" <- #1;;
      "x" <- #2;;
      #().

End CertDischarge.

Section proof.
  Context `{!heapGS Σ}.

  Let Nq := nroot.@ "cert_discharge_q".
  Let Nf := nroot.@ "cert_discharge_f".
  Let Na := nroot.@ "cert_discharge_always".

  (** The right formula of the first commitment: the state at the discharge, a trace-visible
      invariant allocated in the same pre-step modality, and the second commitment. *)
  Definition cd_Q (x y : loc) kf : iProp Σ :=
    x ↦ #1 ∗ alwaysI Na (y ↦ #7) ∗ finallyI Nf kf 1 (x ↦ #2).

  Lemma cd_Q_temporal x y kf :
    ⊢ cd_Q x y kf ⊨ₜ (x ↦ #1 ∧ tprop_always (y ↦ #7) ∧ tprop_finally (x ↦ #2))%T.
  Proof. apply (into_temporal _ _). Qed.

  Lemma main_spec :
    ⊢ ∃ μ, ∀ i kq kf (x y : loc),
    l{{{ thread_expr i [] (CertDischarge.main #x #y) ∗ thP_kids i {[kq; kf]} ∗
         ([∗ set] g ∈ {[kq; kf]}, oblP_fuel g 0 μ) ∗
         ⌜kq ≠ kf⌝ ∗ oblP_kids kq ∅ ∗ oblP_kids kf ∅ ∗
         x ↦ #0 ∗ y ↦ #7 ∗
         finallyI Nq kq 1 (cd_Q x y kf) ∗ finallyI Nf kf 1 (x ↦ #2) }}}
      CertDischarge.main #x #y @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ lift_term i fork_post v }}}.
  Proof.
    iExists 10. iIntros (i kq kf x y Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& %Hkqf& Kkq& Kkf& Ptrx& Ptry& HQ& HF)".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    rewrite /CertDischarge.main /=.
    lwp_pure_lc 100.
    lwp_pures.
    (* x <- #1 *)
    lwp_bind (Store _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_store _ ∅ 0 with "[$TE $Ptrx $TG $GF1]"). 1: done.
    iIntros "[TE ((_& TG& _)& Ptrx)]".
    lwp_pures.
    (* x <- #2: the discharge happens in the pre-step modality of this bare lWP. *)
    lwp_bind (Store _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply sfmupd_lwp.
    iMod (alwaysI_alloc _ Na (y ↦ #7)%I with "[Ptry]") as "#HA"; first by iFrame.
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC2 LC]".
    iMod (finallyI_discharge with "LC2 TG Kkq HQ [Ptrx HF]") as "(HQ& TG& #Odq)".
    1: solve_ndisj. 1: set_solver.
    { rewrite /cd_Q. iFrame "Ptrx HF HA". }
    iPoseProof (oblP_fuels_remove_obl kq with "GF1") as "GF1".
    iPoseProof (oblP_fuels_remove_obl kq with "GF") as "GF".
    replace ({[kq; kf]} ∖ {[kq]}) with ({[kf]} : gset oid) by set_solver.
    iDestruct "HQ" as "(Ptrx& _& HF)".
    iModIntro.
    iApply (lwp_store _ ∅ 0 with "[$TE $Ptrx $TG $GF1]"). 1: done.
    iIntros "[TE ((_& TG& _)& Ptrx)]".
    lwp_pures.
    (* The nested commitment, then termination. *)
    iApply sfmupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC2 _]".
    iMod (finallyI_discharge with "LC2 TG Kkf HF Ptrx") as "(Ptrx& TG& #Odf)".
    1: solve_ndisj. 1: set_solver.
    replace ({[kf]} ∖ {[kf]}) with (∅ : gset oid) by set_solver.
    iMod (thread_terminate with "TG") as "#Td".
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. by iFrame "Td".
  Qed.

  Lemma main_pre Θ i (x y : loc) Φ Ψs :
    Θ = {[i := CertDischarge.main #x #y]} →
    Φ = (λ μ, (∃ kq kf, finallyI Nq kq 1 (cd_Q x y kf) ∗ finallyI Nf kf 1 (x ↦ #2) ∗
                        x ↦ #0 ∗ y ↦ #7 ∗
                        (thP_kids i {[kq; kf]} ∗ oblP_kids kq ∅ ∗ oblP_kids kf ∅ ∗ ⌜kq ≠ kf⌝ ∗
                         ([∗ set] g ∈ {[kq; kf]}, oblP_fuel g 0 μ)))%I) →
    Ψs = ({[i := fork_post]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗ x ↦ #0 -∗ y ↦ #7 -∗
     ([∗ set] i ∈ dom Θ, thP_kids i ∅) -∗
     |={⊤}=>m ∃ μ, (Φ μ ∗
                   (Φ μ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lWP e @ i; ⊤ {{ lift_term i Ψ }}))).
  Proof.
    iIntros (HT HP HQ) "TEs Ptrx Ptry TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (main_spec) as (μ) "main_spec".
    iMod (untilI_alloc _ _ _ 0 μ with "[] TGs") as "(%kf& %Hkf& TG1& Kkf& Ofkf& #Wlkf& Akf)".
    { iApply parP_le_thread. }
    iMod ("Akf" $! _ Nf True%I (x ↦ #2)%I with "[]") as "Ukf".
    { done. }
    iMod (untilI_alloc _ _ _ 0 μ with "[] TG1") as "(%kq& %Hkq& TG1& Kkq& Ofkq& #Wlkq& Akq)".
    { iApply parP_le_thread. }
    iMod ("Akq" $! _ Nq True%I (cd_Q x y kf) with "[]") as "Ukq".
    { done. }
    iModIntro. iExists μ. iSplitL "Ukq Ukf Ptrx Ptry TG1 Kkq Kkf Ofkq Ofkf".
    { subst Φ. rewrite !union_empty_r_L.
      replace ({[kq]} ∪ {[kf]}) with ({[kq; kf]} : gset oid) by set_solver.
      iExists kq, kf. iFrame "Ukq Ukf Ptrx Ptry TG1 Kkq Kkf".
      rewrite (big_sepS_union _ {[kq]} {[kf]}); last set_solver. rewrite !big_sepS_singleton.
      iFrame "Ofkq Ofkf". iPureIntro. set_solver. }
    iClear "Wlkq Wlkf". clear dependent kq kf.
    iIntros "HP". subst Φ.
    iDestruct "HP" as (kq kf) "(HQ& HF& Ptrx& Ptry& TG& Kkq& Kkf& %Hkqf& GF)".
    iEval (rewrite HT big_sepM_singleton) in "TEs".
    iPoseProof ("main_spec" $! i kq kf x y (λ v, lift_term i fork_post v)
                 with "[TEs TG Kkq Kkf GF Ptrx Ptry HQ HF]") as "WP".
    { iFrame "TEs TG Kkq Kkf GF Ptrx Ptry HQ HF". iPureIntro. done. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iIntros (?) "[_ $]". }
    by rewrite big_sepM2_empty.
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let x : loc := Loc 0.
  Let y : loc := Loc 1.
  Let Θ0 : thread_pool heap_lang := {[i := CertDischarge.main #x #y]}.
  Let σ0 : gmap loc (option val) := {[x := Some #0; y := Some #7]}.

  Let Nq := nroot.@ "cert_discharge_q".
  Let Nf := nroot.@ "cert_discharge_f".

  (** The final resources. *)
  Let Φ_P `{!heapGS Σ} : _ → iProp Σ :=
        λ μ,
          (∃ kq kf,
              finallyI Nq kq 1 (cd_Q x y kf) ∗ finallyI Nf kf 1 (x ↦ #2) ∗
              x ↦ #0 ∗ y ↦ #7 ∗
              (thP_kids i {[kq; kf]} ∗ oblP_kids kq ∅ ∗ oblP_kids kf ∅ ∗ ⌜kq ≠ kf⌝ ∗
               ([∗ set] g ∈ {[kq; kf]}, oblP_fuel g 0 μ)))%I.

  (** What they guarantee; the first commitment's right formula keeps its nested structures. *)
  Let G_main {Σ} : tprop heap_lang Σ :=
        (tprop_finally (x ↦ #1 ∧ tprop_always (y ↦ #7) ∧ tprop_finally (x ↦ #2)) ∧
         tprop_finally (x ↦ #2) ∧ x ↦ #0 ∧ y ↦ #7 ∧ tprop_true)%T.

  Lemma Φ_P_temporal `{!heapGS Σ} m : ⊢ Φ_P m ⊨ₜ G_main.
  Proof. apply (into_temporal _ _). Qed.

  (** At the level of traces: eventually [x] holds [1] while [y] holds [7] from then on,
      and later [x] holds [2]. *)
  Let R_main : trProp heap_lang :=
        (tr_eventually (x ↦ #1 ∧ tr_always (y ↦ #7) ∧ tr_eventually (x ↦ #2)) ∧
         tr_eventually (x ↦ #2))%R.

  Remark G_main_impl {Σ} τ : tprop_tr (G_main (Σ:=Σ)) τ → R_main τ.
  Proof. intros (H1& H2& _). split; [exact H1|exact H2]. Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          tregGS.tregΣ heap_lang;
          heap_stateΣ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := fork_post]}.

  Theorem cert_discharge_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    R_main τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_temporal Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] G_main R_main).
    { apply G_main_impl. }
    1,2,3,4: eauto.
    iIntros (?). exists (Ord.from_nat 2).
    iMod (gen_heap_init σ0) as "(%Hheap& HI& Ptrs& _)".
    iMod (thread_map_init Θ0) as "(%Hthread& TI& Tis)".
    iMod (proph_map_init ([] : list observation) (∅ : gset proph_id)) as "(%Hproph& PI)".
    iMod (inv_heap_init loc (option val) (⊤ : coPset)) as "(%Hinv_heap& >HHI)".
    set (Hheap_stateGS := @HeapStateGS Σ Hheap Hinv_heap Hproph Hthread).
    set (HHeapGS := @HeapGS Σ Htemporal Hheap_stateGS).
    set (HlantanaGS := @heapGS_lantanaGS Σ HHeapGS).
    iExists (lantana_state_interp_class), (@fork_post Σ), (@Ψs Σ).
    iSplitL "HI TI PI".
    { iDestruct "PI" as "[PI _]". by iFrame. }
    iSplitR; first done.
    iModIntro. iIntros "LC TGs".
    iAssert (x ↦ #0 ∗ y ↦ #7)%I with "[Ptrs]" as "[Ptrx Ptry]".
    { subst σ0. rewrite big_sepM_insert; last done. rewrite big_sepM_singleton.
      rewrite primitive_laws.pointsto_unseal /primitive_laws.pointsto_def. iFrame. }
    iMod (main_pre (heapGS0:=HHeapGS) Θ0 i x y (Φ_P (heapGS0:=HHeapGS))
           with "[Tis] Ptrx Ptry [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iModIntro. iExists (Φ_P μ). iFrame "HP H". iApply Φ_P_temporal.
  Qed.

End adequacy.
