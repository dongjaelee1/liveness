From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Export flag.
From lantana.heap_lang.examples Require Import step_tactics.

(** * A flag set by a forked thread: the main thread waits for it and returns [42] *)

Module FlagFork.

  Definition main : val :=
    λ: <>,
      let: "x" := Flag.init #() in
      Fork (Flag.set "x");;
      Flag.wait "x";;
      #42.

End FlagFork.

Section proof.
  Context `{!heapGS Σ}.

  Let Nr := nroot.@ "flag_fork_ret".
  Let Nc := nroot.@ "flag_fork_flag".

  (** The main proofs. Besides returning, the main thread commits to creating a flag. *)
  Lemma FlagFork_main_spec :
    ⊢ ∃ μ, ∀ i kr kc,
    l{{{ thread_expr i [] (FlagFork.main #()) ∗ thP_kids i {[kr; kc]} ∗ ([∗ set] g ∈ {[kr; kc]}, oblP_fuel g (1)%ordi μ) ∗
         ⌜kr ≠ kc⌝ ∗ oblP_kids kr ∅ ∗ oblP_kids kc ∅ ∗
         finallyI Nr kr 1 (exits #42@i) ∗
         finallyI Nc kc 1 (∃ x k ℓ, is_flag x k ℓ) }}}
      FlagFork.main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ ⌜v = #42⌝ ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof (Flag_init_thread_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (Flag_set_thread_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iExists (10 ⊕ μ_fi ⊕ μ_fw)%M. iIntros (i kr kc Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& %Hkrc& Kkr& Kkc& HF& HC)".
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF GF_m]".
    iPoseProof (oblP_fuel_add_set with "GF_m") as "[GF_fi GF_fw]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    rewrite /FlagFork.main /=.
    lwp_pure_lc 100.
    lwp_bind (Flag.init _).
    iMod (oblP_fuel_layer_mon_set _ (0)%ordi with "GF_fi") as "GF_fi".
    { apply ordArith.le_from_nat. lia. }
    iModIntro.
    (* The flag's obligation pays the steps until the fork, its move to the forked thread, and
       the forked thread. *)
    iApply ("Flag_init_spec" $! 0 _ _ 0 (9 ⊕ (1 ⊕ μ_fs))%M with "[$TE $TG $GF_fi]").
    iIntros "%x %k (TE& _& %Hk& TG& Kk& Of0& Ftk& #is_flag)".
    (* Keep the commitment: the flag exists. *)
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LCc LC]".
    iMod (finallyI_discharge with "LCc TG Kkc HC [is_flag]") as "(_& TG& _)".
    { set_solver. }
    { set_solver. }
    { iExists x, k, 0%ordi. iFrame "is_flag". }
    iPoseProof (oblP_fuels_remove_obl kc with "GF") as "GF".
    iPoseProof (big_sepS_delete _ _ kc with "GF_fw") as "[_ GF_fw]"; first set_solver.
    replace (({[k]} ∪ {[kr; kc]}) ∖ {[kc]}) with ({[k]} ∪ {[kr]} : gset oid) by set_solver.
    replace ({[kr; kc]} ∖ {[kc]}) with ({[kr]} : gset oid) by set_solver.
    iPoseProof (oblP_fuel_add with "Of0") as "[Of0 Fr]".
    iPoseProof (oblP_fuel_add with "Fr") as "[Mv GFj]".
    iPoseProof (oblP_fuels_add_obl with "Of0 GF") as "GF".
    lwp_pures.
    lwp_bind (Fork _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_fork {[k]} (oblP_kids k ∅ ∗ oblP_fuel k 0 μ_fs ∗ flag_tk x k)%I ({[k]} ∪ {[kr]}) ∅ 0
             with "[] [TE TG GF1 Mv Kk GFj Ftk]"); first set_solver.
    2:{ iFrame "TE TG GF1 Kk GFj Ftk". iSplitR; first by rewrite big_sepS_empty.
        rewrite big_sepS_singleton. iExists _. iFrame "Mv". }
    { iIntros (j Φ') "!> (TE& TG& Kk& GFj& Ftk) HΦ'".
      iApply lwp_sfmupd.
      iApply ("Flag_set_spec" $! 0 with "[$TE $TG GFj $Kk $Ftk $is_flag]").
      { iSplitL "GFj"; first by rewrite big_sepS_singleton. iPureIntro. set_solver. }
      iIntros "(TE& _& TG& #Od)".
      replace ({[k]} ∖ {[k]}) with (∅ : gset oid) by set_solver.
      iMod (thread_terminate with "TG") as "#Td".
      iModIntro. rewrite /lift_term. iApply "HΦ'". eauto. }
    iIntros "(TE& _& TG& _)".
    iPoseProof (oblP_fuels_remove_obl k with "GF") as "GF".
    replace (({[k]} ∪ {[kr]}) ∖ {[k]}) with ({[kr]} : oids) by set_solver.
    lwp_pures.
    lwp_bind (Flag.wait _).
    iModIntro.
    iMod (oblP_fuel_layer_mon_set _ ((0) ⊕ 1)%ordi with "GF_fw") as "GF_fw".
    { rewrite -hessenberg.add_from_nat. done. }
    iApply ("Flag_wait_spec" $! 0 with "[$TE $TG $GF_fw $is_flag]").
    iIntros "(TE& _& TG& #Od0)".
    do 2 (iModIntro; lwp_pure_one).
    iApply sfmupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC _]".
    iMod (thread_expr_terminate_finally with "TE LC TG Kkr HF") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. iFrame "Td". done.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := FlagFork.main #() ]} →
    Φ = (λ μ, (∃ kr kc, finallyI Nr kr 1 (exits #42@i) ∗
                        finallyI Nc kc 1 (∃ x k ℓ, is_flag x k ℓ) ∗
                        (thP_kids i {[kr; kc]} ∗ oblP_kids kr ∅ ∗ oblP_kids kc ∅ ∗ ⌜kr ≠ kc⌝ ∗
                         ([∗ set] g ∈ {[kr; kc]}, oblP_fuel g 1 μ)))%I) →
    Ψs = ({[i := (λ _ v, ⌜v = #42⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_kids i ∅) -∗
     |={⊤}=>m ∃ μ, (Φ μ ∗
                   (Φ μ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lWP e @ i; ⊤ {{ lift_term i Ψ }}))).
  Proof.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (FlagFork_main_spec) as (μ) "main_spec".
    iMod (untilI_alloc _ _ _ 1 μ with "[] TGs") as "(%kl1& %Hkl1& TG1& Kkl1& Ofkl1& #Wlkl1& Akl1)".
    { iApply parP_le_thread. }
    iMod ("Akl1" $! _ Nr True%I (exits #42@i)%I with "[]") as "Ukl1".
    { done. }
    iMod (untilI_alloc _ _ _ 1 μ with "[] TG1") as "(%kc& %Hkc& TG1& Kkc& Ofkc& #Wlkc& Akc)".
    { iApply parP_le_thread. }
    iMod ("Akc" $! _ Nc True%I (∃ x k ℓ, is_flag x k ℓ)%I with "[]") as "Ukc".
    { done. }
    iModIntro. iExists μ. iSplitL "Ukl1 Ukc TG1 Kkl1 Kkc Ofkl1 Ofkc".
    { subst Φ. rewrite !union_empty_r_L.
      replace ({[kc]} ∪ {[kl1]}) with ({[kl1; kc]} : gset oid) by set_solver.
      iExists kl1, kc. iFrame "Ukl1 Ukc TG1 Kkl1 Kkc".
      rewrite (big_sepS_union _ {[kl1]} {[kc]}); last set_solver. rewrite !big_sepS_singleton.
      iFrame "Ofkl1 Ofkc". iPureIntro. set_solver. }
    iClear "Wlkl1 Wlkc". clear dependent kl1 kc.
    iIntros "HP". subst Φ.
    iDestruct "HP" as (kl1 kc) "(HF& HC& TG& Kkr& Kkc& %Hkrc& GF)".
    iEval (rewrite HT big_sepM_singleton) in "TEs".
    iPoseProof ("main_spec" $! i kl1 kc (λ v, lift_term i (λ _ v, ⌜v = #42⌝)%I v) with "[TEs TG Kkr Kkc GF HF HC]") as "WP".
    { iFrame "∗ #". iPureIntro. done. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iIntros (?) "(_& %& H)". rewrite /lift_term.
      iDestruct "H" as "[$ _]". eauto. }
    done.
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let Θ0 : thread_pool heap_lang := {[i := FlagFork.main #()]}.
  Let σ0 : gmap loc (option val) := ∅.

  (** The main thread returns 42, and a flag gets created that is [0] until it is [1] and
      then stays [1]; in particular, the forked thread sets it. *)
  Let R_main : trProp heap_lang :=
        (tr_eventually (exits #42@i) ∧ tr_eventually (∃ x : loc, is_flag_tr x))%R.

  Let Nr := nroot.@ "flag_fork_ret".
  Let Nc := nroot.@ "flag_fork_flag".

  Let Φ_P `{!heapGS Σ} : _ → iProp Σ :=
        λ μ,
          (∃ kr kc,
              finallyI Nr kr 1 (exits #42@i) ∗
              finallyI Nc kc 1 (∃ x k ℓ, is_flag x k ℓ) ∗
              (thP_kids i {[kr; kc]} ∗ oblP_kids kr ∅ ∗ oblP_kids kc ∅ ∗ ⌜kr ≠ kc⌝ ∗
               ([∗ set] g ∈ {[kr; kc]}, oblP_fuel g 1 μ)))%I.

  Let G_main {Σ} : itrProp heap_lang Σ :=
        (itrProp_finally (exits #42@i) ∧ itrProp_finally (itrProp_exist (λ x : loc, flag_itrProp x)) ∧ itrProp_true)%ITR.

  Lemma Φ_P_temporal `{!heapGS Σ} m : ⊢ Φ_P m ⊨ₜ G_main.
  Proof. apply (into_temporal _ _). Qed.

  Remark G_main_impl {Σ} τ : itrProp_external (G_main (Σ:=Σ)) τ → R_main τ.
  Proof.
    intros (Hr& Hf& _). split; first exact Hr.
    destruct τ as [n τf]. destruct Hf as (m& Hm& [x Hx]& Hb).
    exists m. split_and!; [done| |done]. exists x. exact (flag_itrProp_impl x (m, τf) Hx).
  Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          tregGS.tregΣ heap_lang;
          heap_stateΣ
          ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := (λ _ v, ⌜v = #42⌝)%I]}.

  Theorem main_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    R_main τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_temporal Σ heap_lang (Build_state σ0 ∅) Θ0 i [] G_main (R_main)).
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
    iMod (main_pre (heapGS0:=HHeapGS) Θ0 i (Φ_P (heapGS0:=HHeapGS)) with "[Tis] [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iModIntro. iExists (Φ_P μ). iFrame "HP H". iApply Φ_P_temporal.
  Qed.

End adequacy.
