From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

From lantana.heap_lang.examples Require Export flag.

Section code.

  Definition X_loc : loc := Loc 0.
  Definition X : val := #X_loc.

  Definition writer : val :=
    λ: <>, let: "v" := Flag.set X in
          "v".

  Definition reader : val :=
    λ: <>, let: "v" := Flag.wait X in
          "v".

End code.

Section proof.
  Context `{!heapGS Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let N := nroot.@ "flag".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".

  Let Nl := nroot.@ "writer_return".

  Let l := X_loc.

  (** The main proofs. *)
  Lemma writer_spec :
    ⊢ ∃ μ, ∀ i g k kl,
    l{{{ thread_expr i [] (writer #()) ∗ thP_carriers i {[g]} ∗ crP_fuel g 0 μ ∗
         crP_obls g 0 {[k; kl]} ∗ ⌜k ≠ kl⌝ ∗
         (* Start with the other half of the until ownership for the pointsto. *)
         flag_tk l k ∗
         finallyT Nl kl 1 (exits #()@i) ∗
         is_flag l k 0 }}}
      writer #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof (Flag_set_spec) as (μ_s) "Flag_set_spec".
    iExists (4 ⊕ μ_s)%M. iIntros (i g k kl Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Gg& %Neqk& HU& HE& #is_flag)".
    iPoseProof (crP_fuel_add with "GF") as "[GF GF_s]".
    iPoseProof (crP_fuels_init {[g]} with "[GF]") as "GF".
    { iApply big_sepS_singleton. iFrame. }
    rewrite /writer /=.
    lwp_pure_one.
    lwp_bind (Flag.set X).
    iModIntro.
    iApply ("Flag_set_spec" $! 10 with "[$TE $TG GF_s $Gg $HU $is_flag]").
    { iSplit; last (iPureIntro; set_solver).
      iApply big_sepS_singleton. iFrame. }
    iIntros "(TE& LC& TG& Gg& #Od)".
    replace ({[k; kl]} ∖ {[k]}) with ({[kl]} : gset _) by set_solver.
    do 2 (iModIntro; lwp_pure_one).
    iApply sfmupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 2 8 with "LC") as "[LC _]".
    iMod (thread_expr_terminateT with "TE LC TG Gg HE") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. by iFrame "Td".
  Qed.

  Lemma reader_spec :
    ⊢ ∃ μ, ∀ i g k kl,
    l{{{ thread_expr i [] (reader #()) ∗ thP_carriers i {[g]} ∗ crP_fuel g 1 μ ∗
         crP_obls g 1 {[kl]} ∗
         finallyT Nl kl 1 (exits #1@i) ∗
         is_flag l k 0 }}}
      reader #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof (Flag_wait_spec) as (μ_w) "Flag_wait_spec".
    iExists (10 ⊕ μ_w)%M. iIntros (i g k kl Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Gg& HE& #is_flag)".
    iPoseProof (crP_fuel_add with "GF") as "[GF GF_w]".
    iPoseProof (crP_fuels_init {[g]} with "[GF]") as "GF".
    { iApply big_sepS_singleton. iFrame. }
    rewrite /reader /=.
    lwp_pure_one.
    lwp_bind (Flag.wait X).
    iModIntro. iApply ("Flag_wait_spec" $! 10 with "[$TE $TG GF_w $is_flag]").
    { iApply big_sepS_singleton. erewrite crP_fuel_layer_eq. 1: iFrame.
      rewrite hessenberg.add_O_l. done. }
    iIntros "(TE& LC& TG& #Od)".
    do 2 (iModIntro; lwp_pure_one).
    iApply sfmupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 2 8 with "LC") as "[LC _]".
    iMod (thread_expr_terminateT with "TE LC TG Gg HE") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. by iFrame "Td".
  Qed.

  Lemma flag_client_pre Θ i j Φ Ψs :
    i ≠ j →
    Θ = {[i := writer #(); j := reader #() ]} →
    Φ = (λ μ1 μ2, (∃ g1 g2 k kl1 kl2,
                      ⌜ k ≠ kl1 ⌝ ∗ is_flag l k 0 ∗ flag_tk l k ∗
                      finallyT Nl kl1 1 (exits #()@i) ∗
                      finallyT Nl kl2 1 (exits #1@j) ∗
                      (thP_carriers i {[g1]} ∗ crP_obls g1 0 {[k; kl1]} ∗
                       thP_carriers j {[g2]} ∗ crP_obls g2 1 ({[kl2]}) ∗
                       crP_fuel g1 0 μ1 ∗ crP_fuel g2 1 μ2))%I) →
    Ψs = ({[i := fork_post; j := fork_post]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗ (l ↦ #0) -∗
     ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m ∃ μ1 μ2, (Φ μ1 μ2 ∗
                       (Φ μ1 μ2 -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, (|={⊤}=>m (lWP e @ i; ⊤ {{ lift_term i Ψ }}))))).
  Proof.
    iIntros (Hij HT HP HQ) "TEs Ptrl TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    iPoseProof (big_sepS_union with "TGs") as "[TG1 TG2]".
    { set_solver. }
    rewrite !big_sepS_singleton.
    iPoseProof (writer_spec) as (μ1) "writer_spec".
    iPoseProof (reader_spec) as (μ2) "reader_spec".
    iMod (carrier_alloc _ _ _ 0 μ1 with "TG1") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (is_flag_init _ _ _ _ 0 _ μ1 with "Ptrl Gg1") as "(%k& %Hk& Gg1& Ofk& Uk& #is_flag)".
    1: done.
    iMod (untilI_alloc _ _ _ false 0 0 μ1 with "Gg1") as "(%kl1& %Hkl1& Gg1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nl True%I (exits #()@i)%I with "[]") as "Ukl1".
    { done. }
    iMod (carrier_alloc _ _ _ 1 μ2 with "TG2") as "(%g2& %Ning2& TG2& Gg2& Gf2)".    
    iMod (untilI_alloc _ _ _ false 1 1 1 with "Gg2") as "(%kl2& %Hkl2& Gg2& Ofkl2& #Wlkl2& Akl2)". 1: done.
    iMod ("Akl2" $! _ Nl True%I (exits #1@j)%I with "[]") as "Ukl2".
    { done. }
    iModIntro. iExists μ1, μ2. iSplitL "Uk Ukl1 Ukl2 TG1 Gg1 TG2 Gg2 Gf1 Gf2 Ofk Ofkl1 Ofkl2".
    { subst Φ.
      iExists g1, g2, k, kl1, kl2. iSplit.
      { iPureIntro. intros <-. set_solver. }
      iFrame "is_flag Uk".
      replace ({[kl1]} ∪ ({[k]} ∪ ∅)) with ({[k; kl1]} : gset _) by set_solver. rewrite !union_empty_r_L. iFrame. }
    iClear "is_flag Wlkl1 Wlkl2". clear dependent g1 g2 k kl1 kl2.
    iIntros "HP". subst Φ.
    iDestruct "HP" as (g1 g2 k kl1 kl2) "(%Hkne& #is_flag& Uk& Ukl1& Ukl2& TG1& Gg1& TG2& Gg2& Gf1& Gf2)".
    iEval (rewrite HT big_sepM_insert; last by rewrite lookup_singleton_ne) in "TEs".
    iDestruct "TEs" as "[TEi TEs]".
    iEval (rewrite big_sepM_singleton) in "TEs". iRename "TEs" into "TEj".
    iPoseProof ("writer_spec" $! i g1 k kl1 (λ v, lift_term i fork_post v) with "[TEi Uk Ukl1 TG1 Gg1 Gf1]") as "WP1".
    { iFrame. iSplit; eauto. }
    iPoseProof ("reader_spec" $! j g2 k kl2 (λ v, lift_term j fork_post v) with "[TEj Ukl2 TG2 Gg2 Gf2]") as "WP2".
    { iFrame. eauto. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { rewrite lookup_insert_ne; auto. }
    { rewrite lookup_insert_ne; auto. }
    iSplitL "WP1".
    { iApply "WP1". iModIntro. iIntros (?) "[_ $]". }
    rewrite big_sepM2_singleton. iApply "WP2". iModIntro. iIntros (?) "[_ $]".
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let j : thread_id := 2%positive.
  Let l : loc := X_loc.
  Let Θ0 : thread_pool heap_lang := {[i := writer #(); j := reader #()]}.
  Let σ0 : gmap loc (option val) := {[l := Some #0]}.

  Let R_main : trProp heap_lang :=
        (is_flag_tr l ∧ tr_until (l ↦ #0) (l ↦ #1) ∧
         tr_eventually (exits #()@i) ∧ tr_eventually (exits #1@j))%R.

  Let N := nroot.@ "flag".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".

  Let Nl := nroot.@ "writer_return".

  (** The final resources. *)
  Let Φ_P `{!heapGS Σ} : _ → _ → iProp Σ :=
        λ μ1 μ2,
          (∃ g1 g2 k kl1 kl2,
              ⌜ k ≠ kl1 ⌝ ∗ is_flag l k 0 ∗ flag_tk l k ∗
              finallyT Nl kl1 1 (exits #()@i) ∗
              finallyT Nl kl2 1 (exits #1@j) ∗
              (thP_carriers i {[g1]} ∗ crP_obls g1 0 {[k; kl1]} ∗
               thP_carriers j {[g2]} ∗ crP_obls g2 1 ({[kl2]}) ∗
               crP_fuel g1 0 μ1 ∗ crP_fuel g2 1 μ2))%I.

  (** What they guarantee: the pure and ghost parts guarantee nothing, and the quantified
      names do not show. *)
  Let G_client {Σ} : tps heap_lang Σ :=
        (tps_true ∧ flag_tps l ∧ tps_until (l ↦ #0) (l ↦ #1) ∧
         tps_finally (exits #()@i) ∧ tps_finally (exits #1@j) ∧ tps_true)%S.

  Lemma Φ_P_temporal `{!heapGS Σ} m1 m2 : ⊢ Φ_P m1 m2 ⊨ₜ G_client.
  Proof. apply (into_temporal _ _). Qed.

  Remark G_client_impl {Σ} τ : tps_tr (G_client (Σ:=Σ)) τ → R_main τ.
  Proof.
    intros (_& Hflag& Hu& Hf1& Hf2& _).
    split; [exact (flag_tps_impl l τ Hflag)|]. split; [exact Hu|]. split; [exact Hf1|exact Hf2].
  Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          tregGS.tregΣ heap_lang;
          heap_stateΣ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := fork_post; j := fork_post]}.

  Theorem flag_client_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    R_main τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_temporal Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] G_client (R_main)).
    { apply G_client_impl. }
    1,2,3,4: eauto.
    iIntros (?). exists (Ord.from_nat 4).
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
    iMod (flag_client_pre (heapGS0:=HHeapGS) Θ0 i j (Φ_P (heapGS0:=HHeapGS)) with "[Tis] [Ptrs] [TGs]") as "H".
    { subst i j. lia. }
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { subst σ0. rewrite big_sepM_singleton.
      by rewrite primitive_laws.pointsto_unseal /primitive_laws.pointsto_def. }
    { iFrame. }
    iDestruct "H" as (m1 m2) "(HP& H)".
    iModIntro. iExists (Φ_P m1 m2). iFrame "HP H". iApply Φ_P_temporal.
  Qed.

End adequacy.

(* Print Assumptions flag_client_adequacy. *)
