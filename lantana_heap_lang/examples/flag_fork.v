From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.program_logic Require Export temporal_logic.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From lantana.heap_lang Require Import triple.
From lantana.program_logic Require Import adequacy_iris.
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

  (** The main proofs. *)

  (** The closed specification of [main], in the paper's format: it ends with no carriers. *)
  Lemma FlagFork_main_fbspec :
    ⊢ □ ∃ μ, ∀ i g kr,
    ⦃ fuels {[g]} (1)%ordi μ ∗ crP_obls g 1 {[kr]} ∗ ⟦finallyP Nr kr 1 (exits #42@i)⟧ₗ ⦄^{[g]}
      FlagFork.main #() @ i; []; ⊤
    ⦃ v, ⌜v = #42⌝ ⦄^∅.
  Proof.
    rewrite /fbtriple /fbtriple_gen. iModIntro.
    iPoseProof (Flag_init_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iExists (10 ⊕ μ_fi ⊕ μ_fw)%M. iIntros (i g kr Φ) "HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Cg& HF)".
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
    iPoseProof (tlc_split_nat 2 98 with "LC") as "[LC _]".
    iMod (thread_expr_exit with "TE LC TG Cg HF") as "[TE TG]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". by iFrame.
  Qed.

  (** The same specification in the form [FlagFork_pre] uses: the thread has terminated. *)
  Lemma FlagFork_main_spec :
    ⊢ ∃ μ, ∀ i g kr,
    l{{{ thread_expr i [] (FlagFork.main #()) ∗ thP_carriers i {[g]} ∗ ([∗ set] g ∈ {[g]}, crP_fuel g (1)%ordi μ) ∗
         crP_obls g 1 {[kr]} ∗
         ⟦finallyP Nr kr 1 (exits #42@i)⟧ₗ }}}
      FlagFork.main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ ⌜v = #42⌝ ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof FlagFork_main_fbspec as (μ) "#H". iExists μ. iIntros (i g kr).
    iApply (fbtriple_top_texan with "H"). iIntros (v) "[Td ->]". rewrite /lift_term. by iFrame.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := FlagFork.main #() ]} →
    Φ = (λ μ, (∃ g kr, finallyP Nr kr 1 (exits #42@i) ∗
                       ⟨thP_carriers i {[g]} ∗ crP_obls g 1 {[kr]} ∗
                        crP_fuel g 1 μ⟩)%F) →
    Ψs = ({[i := (λ _ v, ⌜v = #42⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m ∃ μ, (⟦Φ μ⟧ₗ ∗
                   (⟦Φ μ⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (FlagFork_main_spec) as (μ) "main_spec".
    iMod (carrier_alloc _ _ _ 1 μ with "TGs") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (tf_until_alloc _ _ _ false 1 1 0 with "Gg1") as "(%kl1& %Hkl1& Gg1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nr (⌜True⌝)%F (exits #42@i)%F with "[]") as "Ukl1".
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
    iEval (rewrite HT big_sepM_singleton) in "TEs".
    iPoseProof ("main_spec" $! i g1 kl1 (λ v, lift_term i (λ _ v, ⌜v = #42⌝)%I v) with "[TEs TG Cg GF HF]") as "WP".
    { iFrame. by iApply big_sepS_singleton. }
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

  Let Φ : tp :=
        (tp_finally (exits #42@i))%P.

  Let Φ' : tp :=
        (∃ (g : ocid) (kr : oid),
            tp_finally (exits #42@i) ∧
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
              finallyP Nr kl 1 (exits #42@i) ∗
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

  Theorem main_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    tp_trace Φ τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    apply Φ_impl.
    eapply (lwp_adequacy Σ heap_lang (Build_state σ0 ∅) Θ0 i [] Φ').
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
    { by iFrame. }
    iSplitR; first done.
    iModIntro. iIntros "LC TGs".
    iMod (main_pre Θ0 i with "[Tis] [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iModIntro. iExists (Φ_tf μ). iFrame "HP". iSplit.
    { iPureIntro. apply tf_to_tp_Φ. }
    iFrame.
  Qed.

  (** Safety: in every fair behavior, the scheduled thread is never stuck, and once [main]
      has returned, its value is [#42]. *)
  Theorem main_safety_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    safety_iris i (λ _ v, v = #42) τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_safety_iris Σ heap_lang (Build_state σ0 ∅) Θ0 i [] i).
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
    iModIntro. iSplit.
    { iPureIntro. eexists. split; first apply lookup_singleton_eq.
      intros v. iIntros "%Hv". by iPureIntro. }
    iSplitL "HI TI PI".
    { by iFrame. }
    iSplitR; first done.
    iIntros "LC TGs".
    iMod (main_pre Θ0 i with "[Tis] [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iApply ("H" with "HP").
  Qed.

  (** Liveness and safety together, over the same fair behaviors: [main] returns [#42], and no
      scheduled thread is ever stuck. *)
  Corollary main_liveness_safety :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    tp_trace Φ τ ∧ (safety_iris i (λ _ v, v = #42) τ).
  Proof.
    intros τ Beh FS Init1 Init2. split.
    - by apply main_adequacy.
    - by apply main_safety_adequacy.
  Qed.

End adequacy.

(* Print Assumptions main_adequacy. *)
