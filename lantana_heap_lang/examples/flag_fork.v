From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

From lantana.heap_lang.examples Require Export flag.

Module FlagFork.

  Definition main : val :=
    λ: <>,
      (* alloc a flag x and forks a set-thread and wait *)
      let: "x" := Flag.init #() in
      Fork (Flag.set "x");;
      Flag.wait "x";;
      #42.

End FlagFork.

Section proof.
  Context `{!heapGS Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let Nr := nroot.@ "flag_fork_ret".
  Let Nc := nroot.@ "flag_fork_flag".

  (** The main proofs. Besides returning, the main thread commits to creating a flag. *)
  Lemma FlagFork_main_spec :
    ⊢ ∃ μ, ∀ i g kr kc,
    l{{{ thread_expr i [] (FlagFork.main #()) ∗ thP_carriers i {[g]} ∗ ([∗ set] g ∈ {[g]}, crP_fuel g (1)%ordi μ) ∗
         crP_obls g 1 {[kr; kc]} ∗ ⌜kr ≠ kc⌝ ∗
         finallyT Nr kr 1 (exits #42@i) ∗
         finallyT Nc kc 1 (∃ x k ℓ, is_flag x k ℓ) }}}
      FlagFork.main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ ⌜v = #42⌝ ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof (Flag_init_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iExists (10 ⊕ μ_fi ⊕ μ_fw)%M. iIntros (i g kr kc Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Cg& %Hkrc& HF& HC)".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF GF_m]".
    iPoseProof (crP_fuel_add_set with "GF_m") as "[GF_fi GF_fw]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    rewrite /FlagFork.main /=.
    lwp_pure_lc 100.
    lwp_bind (Flag.init _).
    iMod (crP_fuel_layer_mon_set _ (0)%ordi with "GF_fi") as "GF_fi".
    { apply ordArith.le_from_nat. lia. }
    iMod (carrier_alloc _ _ _ 0 (μ_fi ⊕ 9)%M with "TG") as "(%& %Ning& TG& Cg0& Cf0)".
    iPoseProof (crP_fuel_add with "Cf0") as "[Cf_fi Cf0]".
    iModIntro.
    iApply ("Flag_init_spec" $! 0 _ _ _ _ 0 9 with "[$TE $TG GF_fi Cf_fi $Cg0]").
    { iApply big_sepS_union. 1: set_solver. rewrite !big_sepS_singleton. iFrame. }
    iIntros "% % (TE& _& TG& _& Cg0& Of0& Ftk& #is_flag)".
    rewrite union_empty_r_L.
    (* Keep the commitment: the flag exists. *)
    iPoseProof (tlc_split_nat 2 98 with "LC") as "[LCc LC]".
    iMod (finallyI_discharge with "LCc Cg HC [is_flag]") as "(_& Cg& _)".
    { set_solver. }
    { set_solver. }
    { iExists x, k, 0%ordi. iFrame "is_flag". }
    replace ({[kr; kc]} ∖ {[kc]}) with ({[kr]} : gset oid) by set_solver.
    iPoseProof (crP_fuels_add_carrier with "Cf0 GF") as "GF".
    lwp_pures.
    lwp_bind (Fork _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_fork 0 μ_fs {[k]} (flag_tk x k)%I _ ∅ 0 with
             "[] [$TE $TG $GF1 $Cg0 Of0 $Ftk]").
    1: set_solver.
    { iIntros (j g2 Φ') "!> (TE& TGj& GFj& Cgj& Ftk) HΦ'".
      iApply lwp_sfgupd.
      iApply ("Flag_set_spec" $! 0 with "[$TE $TGj GFj $Cgj $Ftk $is_flag]").
      { iFrame. iPureIntro. set_solver. }
      iIntros "(TE& _& TG& Cg& #Od)".
      replace ({[k]} ∖ {[k]}) with (∅ : gset oid) by set_solver.
      iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
      replace ({[g2]} ∖ {[g2]}) with (∅ : gset ocid) by set_solver.
      iMod (thread_terminate with "TG") as "#Td".
      iModIntro. rewrite /lift_term. iApply "HΦ'". eauto. }
    { iSplitR; first done.
      rewrite (oblP_fuel_eq _ _ _ (1 ⊕ 8)%M).
      - iPoseProof (oblP_fuel_add _ _ 1 8 with "Of0") as "[Of0 _]".
        iApply big_sepS_singleton. iFrame.
      - rewrite measure_rep_add !measure_rep_nat -Hessenberg.add_from_nat. simpl. done. }
    iIntros "[TE ((_& TG& _)& Cg0)]".
    replace ({[k]} ∖ {[k]}) with (∅ : oids) by set_solver.
    iMod (carrier_delete with "TG Cg0") as "TG". 1: set_solver.
    iPoseProof (crP_fuels_remove_carrier g0 with "GF") as "GF".
    replace ({[g0; g]} ∖ {[g0]}) with ({[g]} : oids) by set_solver.
    clear dependent g0.
    lwp_pures.
    lwp_bind (Flag.wait _).
    iModIntro.
    iMod (crP_fuel_layer_mon_set _ ((0) ⊕ 1)%ordi with "GF_fw") as "GF_fw".
    { rewrite -hessenberg.add_from_nat. done. }
    iApply ("Flag_wait_spec" $! 0 with "[$TE $TG $GF_fw $is_flag]").
    iIntros "(TE& _& TG& #Od0)".
    do 2 (iModIntro; lwp_pure_one).
    iApply lwpupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 2 96 with "LC") as "[LC _]".
    iMod (thread_expr_terminateT with "TE LC TG Cg HF") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. iFrame "Td". done.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := FlagFork.main #() ]} →
    Φ = (λ μ, (∃ g kr kc, finallyT Nr kr 1 (exits #42@i) ∗
                          finallyT Nc kc 1 (∃ x k ℓ, is_flag x k ℓ) ∗
                          (thP_carriers i {[g]} ∗ crP_obls g 1 {[kr; kc]} ∗ ⌜kr ≠ kc⌝ ∗
                           crP_fuel g 1 μ))%I) →
    Ψs = ({[i := (λ _ v, ⌜v = #42⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m ∃ μ, (Φ μ ∗
                   (Φ μ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (FlagFork_main_spec) as (μ) "main_spec".
    iMod (carrier_alloc _ _ _ 1 μ with "TGs") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (untilI_alloc _ _ _ false 1 1 0 with "Gg1") as "(%kl1& %Hkl1& Gg1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nr True%I (exits #42@i)%I with "[]") as "Ukl1".
    { done. }
    iMod (untilI_alloc _ _ _ false 1 1 0 with "Gg1") as "(%kc& %Hkc& Gg1& Ofkc& #Wlkc& Akc)". 1: done.
    iMod ("Akc" $! _ Nc True%I (∃ x k ℓ, is_flag x k ℓ)%I with "[]") as "Ukc".
    { done. }
    iModIntro. iExists μ. iSplitL "Ukl1 Ukc TG1 Gg1 Gf1 Ofkl1 Ofkc".
    { subst Φ. rewrite !union_empty_r_L.
      replace ({[kc]} ∪ {[kl1]}) with ({[kl1; kc]} : gset oid) by set_solver.
      iExists g1, kl1, kc. iFrame "Ukl1 Ukc TG1 Gf1 Gg1". iPureIntro. set_solver. }
    iClear "Wlkl1 Wlkc". clear dependent g1 kl1 kc.
    iIntros "HP". subst Φ.
    iDestruct "HP" as (g1 kl1 kc) "(HF& HC& TG& Cg& %Hkrc& GF)".
    iEval (rewrite HT big_sepM_singleton) in "TEs".
    iPoseProof ("main_spec" $! i g1 kl1 kc (λ v, lift_term i (λ _ v, ⌜v = #42⌝)%I v) with "[TEs TG Cg GF HF HC]") as "WP".
    { iFrame. iSplitL; [by iApply big_sepS_singleton|done]. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iModIntro. eauto. iIntros (?) "(_& %& H)". rewrite /lift_term.
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
  Let Φ : tp :=
        (tp_finally (exits #42@i) ∧ tp_finally (∃ x : loc, is_flag_tp x))%P.

  Let Nr := nroot.@ "flag_fork_ret".
  Let Nc := nroot.@ "flag_fork_flag".

  Let Φ_P `{!heapGS Σ} : _ → iProp Σ :=
        λ μ,
          (∃ g kr kc,
              finallyT Nr kr 1 (exits #42@i) ∗
              finallyT Nc kc 1 (∃ x k ℓ, is_flag x k ℓ) ∗
              (thP_carriers i {[g]} ∗ crP_obls g 1 {[kr; kc]} ∗ ⌜kr ≠ kc⌝ ∗ crP_fuel g 1 μ))%I.

  Let G_main {Σ} : tps heap_lang Σ :=
        (tps_finally (exits #42@i) ∧ tps_finally (tps_exist (λ x : loc, flag_tps x)) ∧ tps_true)%S.

  Lemma Φ_P_temporal `{!heapGS Σ} m : ⊢ Φ_P m ⊨ₜ G_main.
  Proof. apply (into_temporal _ _). Qed.

  Remark G_main_impl {Σ} τ : tps_tr (G_main (Σ:=Σ)) τ → tp_trace Φ τ.
  Proof.
    intros (Hr& Hf& _). split; first exact Hr.
    destruct τ as [n τf]. destruct Hf as (m& Hm& [x Hx]& Hb).
    exists m. split_and!; [done| |done]. exists x. exact (flag_tps_impl x (m, τf) Hx).
  Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
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
    tp_trace Φ τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_temporal Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] G_main (tp_trace Φ)).
    { apply G_main_impl. }
    1,2,3,4: eauto.
    iIntros (?). exists 0%ord.
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

(* Print Assumptions main_adequacy. *)
