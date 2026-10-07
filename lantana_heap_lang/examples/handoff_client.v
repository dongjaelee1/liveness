From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.program_logic Require Export temporal_logic.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Export flag handoff.

Section code.

  Definition main : val :=
    λ: <>,
      let: "b" := ref NONE in
      Fork (Handoff.receive "b");;
      let: "x" := Flag.init #() in
      Handoff.send "b" Flag.set "x";;
      let: "v" := Flag.wait "x" in
      "v".

End code.

Section proof.
  Context `{!heapGS Σ, !handoffG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let Nl := nroot.@ "return".

  (** The main proofs. *)

  (** layers: set = 0 → task = 1 → flag obl = 1 → return obl = 2 *)
  Lemma main_spec :
    ⊢ ∃ μ, ∀ i g kl,
    l{{{ thread_expr i [] (main #()) ∗ thP_carriers i {[g]} ∗ crP_fuel g 2 μ ∗
         crP_obls g 2 {[kl]} ∗
         ⟦finallyP Nl kl 1 (exits #1@i)⟧ₗ }}}
      main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ lift_term i (λ _ v, ⌜v = #1⌝) v }}}.
  Proof using handoffG0.
    iPoseProof (Flag_init_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    iPoseProof (Handoff_send_spec) as (μ_hs) "Handoff_send_spec".
    iPoseProof (Handoff_receive_spec) as (μ_hr) "Handoff_receive_spec".
    iExists (20 ⊕ μ_fi ⊕ μ_hs ⊕ μ_fw)%M. iIntros (i g kl Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Cg& HF)".
    iPoseProof (crP_fuel_add with "GF") as "[GF GF_m]".
    iPoseProof (crP_fuel_add with "GF_m") as "[GF_fi GF_m]".
    iPoseProof (crP_fuel_add with "GF_m") as "[GF_hs GF_fw]".
    iPoseProof (crP_fuels_init {[g]} with "[GF]") as "GF".
    { iApply big_sepS_singleton. iFrame. }
    rewrite /main /=.
    lwp_pure_lc 100.
    lwp_pures.
    lwp_bind (AllocN _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (ptrb) "[TE ((_& TG& _)& Ptrb& _)]".
    lwp_pures.
    lwp_bind (Fork _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro. iApply lwp_fork_step. iModIntro. iFrame "TE TG GF1". iExists ∅. iSplitR; first done.
    iIntros (j) "TE TEj TG _ TGj !> !>".
    iMod (carrier_alloc _ _ _ 1 μ_hr with "TGj") as "(%& _& TGj& Cgj& GFj)".
    rewrite union_empty_r_L.
    iDestruct "Ptrb" as "[Ptrb Ptrb0]".
    iMod (is_handoff_initialize with "Ptrb0 Cgj") as "(%γh& #is_handoff& Gv)".
    iModIntro. iSplitR "TEj TGj GFj Gv"; cycle 1.
    { iRename "TEj" into "TE". lwp_bind (Handoff.receive _).
      iModIntro.
      iApply lwp_sfmupd.
      iApply ("Handoff_receive_spec" $! 0 with "[$TE $TGj GFj $Gv $is_handoff]").
      { iApply big_sepS_singleton. iFrame. }
      iIntros (?) "(TE& _& TGj)". iMod (thread_terminate with "TGj") as "TGj".
      rewrite /lift_term. iModIntro. by iFrame. }
    iModIntro.
    lwp_pures.
    lwp_bind (Flag.init _).
    iMod (carrier_alloc _ _ _ 1 (12 ⊕ μ_fi ⊕ μ_hs)%M with "TG") as "(%& %& TG& Cg0& GF0)".
    iPoseProof (crP_fuel_add with "GF0") as "[GF00 GF0]".
    iPoseProof (crP_fuel_add with "GF0") as "[GF0_fi GF0]".
    iMod (crP_fuel_layer_mon _ (0)%ordi with "GF_fi") as "GF_fi".
    { apply ordArith.le_from_nat. lia. }
    iMod (crP_fuel_layer_mon _ (0)%ordi with "GF0_fi") as "GF0_fi".
    { apply ordArith.le_from_nat. lia. }
    iModIntro.    
    iApply ("Flag_init_spec" $! 0 _ _ _ _ 1 1 with "[$TE $TG GF_fi GF0_fi $Cg0]").
    { iApply big_sepS_union. 1: set_solver. rewrite !big_sepS_singleton. iFrame. }
    iIntros "%ptrx % (TE& _& TG& _& Cg0& Of& HU& #is_flag)".
    rewrite union_empty_r_L.
    iPoseProof (crP_fuels_add_carrier with "GF00 GF") as "GF".
    lwp_pures.
    lwp_bind (Handoff.send _ _ _).
    (** Need carrier at layer 1 for Flag.set. *)
    iModIntro.
    iMod (crP_fuel_layer_mon _ 0 with "GF_hs") as "GF_hs".
    { apply ordArith.le_from_nat. lia. }
    iMod (crP_fuel_layer_mon _ 0 with "GF0") as "GF0".
    { apply ordArith.le_from_nat. lia. }
    iApply ("Handoff_send_spec" $! 0 _ _ Flag.set #ptrx _ _ {[k]} with "[$TE $TG GF_hs GF0 $Cg0 Of Ptrb HU $is_handoff]").
    { iSplitL "GF_hs GF0".
      { iApply (big_sepS_union_2 with "[GF0]").
        - iApply big_sepS_singleton. iFrame.
        - iApply big_sepS_singleton. iFrame. }
      iSplit.
      { iPureIntro. set_solver. }
      iSplitL "Of".
      { iApply big_sepS_singleton. iFrame. }
      iFrame "Ptrb". iExists 0. iExists (⟦untilP (nroot.@"flag".@"pointsto") k (1 / 2) (ptrx ↦ #0) (ptrx ↦ #1)⟧ₗ)%I.
      iSplit.
      { iPureIntro. apply ordArith.lt_from_nat. lia. }
      iFrame "HU". iExists μ_fs. iIntros (?????? ??) "!> (TE& TG& GF& Cg& %INk& HU) HΦ".
      iApply ("Flag_set_spec" $! lc with "[$TE $TG GF $Cg $HU $is_flag]").
      { iSplit.
        - iFrame.
        - iPureIntro. set_solver. }
      iIntros "(TE& LC& TG& Cg& _)". iApply ("HΦ" with "[$]"). }
    iIntros "(TE& _& TG& Cg0)".
    iMod (carrier_delete_fuels _ _ _ {[g]} with "TG Cg0 GF") as "[TG GF]". 1-3: set_solver.
    lwp_pures.
    lwp_bind (Flag.wait _).
    iModIntro. iApply ("Flag_wait_spec" $! 0 with "[$TE $TG GF_fw $is_flag]").
    { iApply big_sepS_singleton. erewrite crP_fuel_layer_eq. 1: iFrame.
      rewrite -hessenberg.add_from_nat. done. }
    iIntros "(TE& _& TG& #Odk)".
    do 2 (iModIntro; lwp_pure_one).
    iApply lwpupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 2 98 with "LC") as "[LC _]".
    iMod (thread_expr_terminate with "TE LC TG Cg HF") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. iFrame "Td". done.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := main #() ]} →
    Φ = (λ μ, (∃ g kl, finallyP Nl kl 1 (exits #1@i) ∗
                       ⟨thP_carriers i {[g]} ∗ crP_obls g 2 {[kl]} ∗
                        crP_fuel g 2 μ⟩)%F) →
    Ψs = ({[i := (λ _ v, ⌜v = #1⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m ∃ μ, (⟦Φ μ⟧ₗ ∗
                   (⟦Φ μ⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof using handoffG0.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (main_spec) as (μ) "main_spec".
    iMod (carrier_alloc _ _ _ 2 μ with "TGs") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (tf_until_alloc _ _ _ false 2 2 0 with "Gg1") as "(%kl1& %Hkl1& Gg1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nl (⌜True⌝)%F (exits #1@i)%F with "[]") as "Ukl1".
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
    iPoseProof ("main_spec" $! i g1 kl1 (λ v, lift_term i (λ _ v, ⌜v = #1⌝)%I v) with "[TEs TG Cg GF HF]") as "WP".
    { iFrame. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iModIntro. iIntros (?) "[_ $]". }
    done.
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let Θ0 : thread_pool heap_lang := {[i := main #()]}.
  Let σ0 : gmap loc (option val) := ∅.

  Let Φ : tp :=
        (tp_finally (exits #1@i))%P.

  Let Φ' : tp :=
        (∃ (g : ocid) (kl : oid),
            tp_finally (exits #1@i) ∧
            tp_true)%P.

  Remark Φ_impl :
    ∀ τ, tp_trace Φ' τ → tp_trace Φ τ.
  Proof.
    simpl. unfold_trProp. intros. destruct τ. destruct H as (?&?&?&?).
    firstorder.
  Qed.

  Let Nl := nroot.@ "return".

  Let Φ_tf `{!heapGS Σ} : _ → tf Σ :=
        λ μ,
          (∃ g kl,
              finallyP Nl kl 1 (exits #1@i) ∗
              ⟨thP_carriers i {[g]} ∗ crP_obls g 2 {[kl]} ∗
               crP_fuel g 2 μ⟩)%F.

  Lemma tf_to_tp_Φ `{!heapGS Σ} m :
    tf_to_tp (Φ_tf m) = Φ'.
  Proof. done. Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          heap_stateΣ;
          handoffΣ
          ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := (λ _ v, ⌜v = #1⌝)%I]}.

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
    set (HlantanaGS := @heapGS_lantanaGS Σ HHeapGS).
    iExists (lantana_state_interp_class), (@fork_post Σ), (@Ψs Σ).
    iSplitL "HI TI PI".
    { iDestruct "PI" as "[PI _]". by iFrame. }
    iSplitR; first done.
    iModIntro. iIntros "LC TGs".
    iMod (main_pre (heapGS0:=HHeapGS) (handoffG0:=HandoffG Σ _) Θ0 i with "[Tis] [TGs]") as "H".
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

End adequacy.

(* Print Assumptions handoff_client_adequacy. *)
