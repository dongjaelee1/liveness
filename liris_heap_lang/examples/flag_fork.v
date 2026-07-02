From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

From liris.heap_lang.examples Require Export flag.

Module FlagFork.

  Definition main : val :=
    λ: <>,
      (* alloc a flag x and forks a set-thread and wait *)
      let: "x" := ref #0 in
      Fork (Flag.set "x");;
      Flag.wait "x";;
      #42.

End FlagFork.

Section proof.
  Context `{!heapGS Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let Nr := nroot.@ "flag_fork_ret".

  (** The main proofs. *)
  Lemma FlagFork_main_spec :
    ⊢ ∃ μ, ∀ i g kr,
    l{{{ thP_carriers i {[g]} ∗ ([∗ set] g ∈ {[g]}, crP_fuel g (1)%ordi μ) ∗
         crP_obls g 1 {[kr]} ∗
         ⟦finallyP Nr kr 1 (ret #42@i)⟧ₗ }}}
      FlagFork.main #() @ i
    l{{{ v, RET v; ⌜v = #42⌝ ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iExists (10 ⊕ μ_fs ⊕ μ_fw)%M. iIntros (i g kr Φ) "!> HP HΦ".
    iDestruct "HP" as "(TG& GF& Cg& HF)".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF GF_m]".
    iPoseProof (crP_fuel_add_set with "GF_m") as "[GF_fs GF_fw]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    rewrite /FlagFork.main /=.
    lwp_pure_lc 100.
    lwp_bind (AllocN _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ptrx) "((_& TG& _)& Ptrx& _)".
    lwp_pures.
    lwp_bind (Fork _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro. iApply lwp_fork. iModIntro. iFrame "TG GF1". iExists ∅. iSplitR; first done.
    iIntros (j) "TG _ TGj !> !>".
    iMod (carrier_alloc _ _ _ (0) (μ_fs)%M with "TGj") as "(%& _& TGj& Cgj& GFj)".
    iMod (is_flag_init _ ptrx _ _ (0) _ 0 with "Ptrx Cgj") as "(%k& _& Cgj& _& Ftk& #is_flag)". 1: done.
    rewrite !union_empty_r_L.
    iModIntro. iSplitR "TGj GFj Cgj Ftk".
    - iModIntro. lwp_pures.
      lwp_bind (Flag.wait _).
      iModIntro.
      iMod (crP_fuel_layer_mon_set _ ((0) ⊕ 1)%ordi with "GF_fw") as "GF_fw".
      { rewrite -hessenberg.add_from_nat. done. }
      iApply ("Flag_wait_spec" $! 0 with "[$TG $GF_fw $is_flag]").
      iIntros "(_& TG& #Od0)".
      lwp_pures.
      iApply lwpupd_retP. iIntros "PL".
      iMod (tf_until_discharge with "HF") as "HF". 1: set_solver.
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      iDestruct "HF" as "[_ HF]". iMod ("HF" $! _) as "HF".
      iMod ("HF" with "[PL]") as "HF".
      { iNext. iEval (rewrite tf_atomic_logic). iFrame. }
      iPoseProof ("HF" with "[] Cg") as "HF".
      { iPureIntro. set_solver. }
      iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      iMod ("HF" $! _) as "HF". iMod "HF" as "(PL& Gg& #Odkl)".
      iModIntro. iFrame "PL".
      replace ({[kr]} ∖ {[kr]} : gset _) with (∅ : oids) by set_solver.
      iMod (carrier_delete with "TG Gg") as "TG". 1: set_solver.
      iPoseProof (crP_fuels_remove_carrier g with "GF") as "GF".
      replace ({[g]} ∖ {[g]} : gset _) with (∅ : gset ocid) by set_solver.
      iModIntro. lwp_finish.
      iApply "HΦ". rewrite /lift_term. iMod (thread_terminate with "TG") as "$".
      iModIntro. eauto.
    - iModIntro.
      iApply lwp_sfmupd.
      iApply ("Flag_set_spec" $! 0 with "[$TGj GFj $Cgj $Ftk $is_flag]").
      {iSplit.
        - iApply big_sepS_singleton. iFrame.
        - iPureIntro. set_solver. }
      iIntros "(_& TG& Cg& #Od)".
      replace ({[k]} ∖ {[k]}) with (∅ : gset oid) by set_solver.
      iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
      replace ({[g0]} ∖ {[g0]}) with (∅ : gset ocid) by set_solver.
      iMod (thread_terminate with "TG") as "#Td".
      iModIntro. rewrite /lift_term. by iFrame "Td".
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := FlagFork.main #() ]} →
    Φ = (λ μ, (∃ g kr, finallyP Nr kr 1 (ret #42@i) ∗
                       ⟨thP_carriers i {[g]} ∗ crP_obls g 1 {[kr]} ∗
                        crP_fuel g 1 μ⟩)%F) →
    Ψs = ({[i := (λ _ v, ⌜v = #42⌝)%I]}) →
    (([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m ∃ μ, (⟦Φ μ⟧ₗ ∗
                   (⟦Φ μ⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof.
    iIntros (HT HP HQ) "TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (FlagFork_main_spec) as (μ) "main_spec".
    iMod (carrier_alloc _ _ _ 1 μ with "TGs") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (tf_until_alloc _ _ _ false 1 1 0 with "Gg1") as "(%kl1& %Hkl1& Gg1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nr (⌜True⌝)%F (ret #42@i)%F with "[]") as "Ukl1".
    { tf_red. done. }
    iModIntro. iExists μ. iSplitL "Ukl1 TG1 Gg1 Gf1 Ofkl1".
    { subst Φ.
      tf_red. iExists g1. tf_red. iExists kl1. tf_red.
      rewrite !union_empty_r_L. iFrame. }
    iClear "Wlkl1". clear dependent g1 kl1.
    iIntros "HP". subst Φ.
    iEval (tf_red) in "HP". iDestruct "HP" as "(%g1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%kl1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(HF& TG& Cg& GF)".
    iPoseProof ("main_spec" $! i g1 kl1 (λ v, lift_term i (λ _ v, ⌜v = #42⌝)%I v) with "[TG Cg GF HF]") as "WP".
    { iFrame. by iApply big_sepS_singleton. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iModIntro. eauto. iIntros (?) "(%& H)". rewrite /lift_term.
      iDestruct "H" as "[$ _]". eauto. }
    done.
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let Θ0 : thread_pool heap_lang := {[i := FlagFork.main #()]}.
  Let σ0 : gmap loc (option val) := ∅.

  Let Φ : tp :=
        (tp_finally (ret #42@i))%P.

  Let Φ' : tp :=
        (∃ (g : ocid) (kr : oid),
            tp_finally (ret #42@i) ∧
            tp_true)%P.

  Remark Φ_impl :
    ∀ τ, tp_trace Φ' τ → tp_trace Φ τ.
  Proof.
    simpl. unfold_trProp. intros. destruct τ. destruct H as (?&?&?&?).
    firstorder.
  Qed.

  Let Nr := nroot.@ "flag_fork_ret".

  Let Φ_tf `{!heapGS Σ} : _ → tf Σ :=
        λ μ,
          (∃ g kl,
              finallyP Nr kl 1 (ret #42@i) ∗
              ⟨thP_carriers i {[g]} ∗ crP_obls g 1 {[kl]} ∗
               crP_fuel g 1 μ⟩)%F.

  Lemma tf_to_tp_Φ `{!heapGS Σ} m :
    tf_to_tp (Φ_tf m) = Φ'.
  Proof. done. Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          heap_stateΣ
          ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := (λ _ v, ⌜v = #42⌝)%I]}.

  Theorem handoff_client_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    tp_trace Φ τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    apply Φ_impl.
    eapply (lwp_adequacy Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] Φ').
    1,2,3,4: eauto.
    iIntros (?). exists 0%ord.
    iMod (gen_heap_init σ0) as "(%Hheap& HI& Ptrs& _)".
    iMod (thread_map_init Θ0) as "(%Hthread& TI& Tis)".
    iMod (proph_map_init ([] : list observation) (∅ : gset proph_id)) as "(%Hproph& PI)".
    iMod (inv_heap_init loc (option val) (⊤ : coPset)) as "(%Hinv_heap& >HHI)".
    set (Hheap_stateGS := @HeapStateGS Σ Hheap Hinv_heap Hproph Hthread).
    set (HHeapGS := @HeapGS Σ Htemporal Hheap_stateGS).
    set (HlirisGS := @heapGS_lirisGS Σ HHeapGS).
    iExists (liris_state_interp_class), (@fork_post Σ), (@Ψs Σ).
    iSplitL "HI TI PI".
    { by iFrame. }
    iSplitL "Tis".
    { by iFrame. }
    iModIntro. iIntros "LC TGs".
    iMod (main_pre Θ0 i with "[TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iModIntro. iExists (Φ_tf μ). iFrame "HP". iSplit.
    { iPureIntro. apply tf_to_tp_Φ. }
    iFrame.
  Qed.

End adequacy.

(* Print Assumptions handoff_client_adequacy. *)
