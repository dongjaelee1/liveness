From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

From liris.heap_lang.examples Require Export flag.

Section code.

  Definition X_loc : loc := Loc 0.
  Definition X : val := #X_loc.

  Definition writer : val :=
    λ: <>, let: "v" := Flag.set X in
          Label "exit" "v".

  Definition reader : val :=
    λ: <>, let: "v" := Flag.wait X in
          Label "exit" "v".

End code.

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

  Let Nl := nroot.@ "writer_label".

  Let l := X_loc.

  (** The main proofs. *)
  Lemma writer_spec :
    ⊢ ∃ μ, ∀ i g k kl,
    l{{{ thP_carriers i {[g]} ∗ crP_fuel g 0 μ ∗
         crP_obls g 0 {[k; kl]} ∗ ⌜k ≠ kl⌝ ∗
         (* Start with the other half of the until ownership for the pointsto. *)
         ⟦untilP Np k (1/2) (l ↦ #0) (l ↦ #1)⟧ₗ ∗
         ⟦finallyP Nl kl 1 (i ⤉ "exit", #())⟧ₗ ∗
         flag_inv l k 0 }}}
      writer #() @ i
    l{{{ v, RET v; lift_term i fork_post v }}}.
  Proof.
    iPoseProof (Flag_set_spec) as (μ_s) "Flag_set_spec".
    iExists (10 ⊕ μ_s)%M. iIntros (i g k kl Φ) "!> HP HΦ".
    iDestruct "HP" as "(TG& GF& Gg& %Neqk& HU& HE& #flag_inv)".
    iPoseProof (crP_fuel_add with "GF") as "[GF GF_s]".
    iPoseProof (crP_fuels_init {[g]} with "[GF]") as "GF".
    { iApply big_sepS_singleton. iFrame. }
    rewrite /writer /=.
    lwp_pure_one.
    lwp_bind (Flag.set X).
    iModIntro.
    iApply ("Flag_set_spec" $! 10 with "[$TG GF_s $Gg $HU $flag_inv]").
    { iSplit; last (iPureIntro; set_solver).
      iApply big_sepS_singleton. iFrame. }
    iIntros "(LC& TG& Gg& #Od)".
    replace ({[k; kl]} ∖ {[k]}) with ({[kl]} : gset _) by set_solver.
    do 2 (iModIntro; lwp_pure_one).
    iApply lwpupd_label. iIntros "PL".
    iApply sfmupd_fupd_acc.
    iMod (tf_until_discharge with "HE") as "HE". 1: set_solver.
    iModIntro.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iDestruct "HE" as "[_ HE]". iMod ("HE" $! _) as "HE".
    iMod ("HE" with "[PL]") as "HE".
    { iNext. iEval (rewrite tf_atomic_logic). iFrame. }
    iPoseProof ("HE" with "[] Gg") as "HE".
    { iPureIntro. set_solver. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("HE" $! _) as "HE". iModIntro. iMod "HE" as "(PL& Gg& #Odkl)".
    iModIntro. iFrame "PL".
    replace ({[kl]} ∖ {[kl]} : gset _) with (∅ : oids) by set_solver.
    iMod (carrier_delete with "TG Gg") as "TG". 1: set_solver.
    iPoseProof (crP_fuels_remove_carrier g with "GF") as "GF".
    replace ({[g]} ∖ {[g]} : gset _) with (∅ : gset ocid) by set_solver.
    lwp_pures.
    iModIntro. lwp_finish.
    iApply "HΦ". rewrite /lift_term. iMod (thread_terminate with "TG") as "$". by iModIntro.
  Qed.

  Lemma reader_spec :
    ⊢ ∃ μ, ∀ i g k kl,
    l{{{ thP_carriers i {[g]} ∗ crP_fuel g 1 μ ∗
         crP_obls g 1 {[kl]} ∗
         ⟦finallyP Nl kl 1 (i ⤉ "exit", #1)⟧ₗ ∗
         flag_inv l k 0 }}}
      reader #() @ i
    l{{{ v, RET v; lift_term i fork_post v }}}.
  Proof.
    iPoseProof (Flag_wait_spec) as (μ_w) "Flag_wait_spec".
    iExists (10 ⊕ μ_w)%M. iIntros (i g k kl Φ) "!> HP HΦ".
    iDestruct "HP" as "(TG& GF& Gg& HE& #flag_inv)".
    iPoseProof (crP_fuel_add with "GF") as "[GF GF_w]".
    iPoseProof (crP_fuels_init {[g]} with "[GF]") as "GF".
    { iApply big_sepS_singleton. iFrame. }
    rewrite /reader /=.
    lwp_pure_one.
    lwp_bind (Flag.wait X).
    iModIntro. iApply ("Flag_wait_spec" $! 10 with "[$TG GF_w $flag_inv]").
    { iApply big_sepS_singleton. erewrite crP_fuel_layer_eq. 1: iFrame.
      rewrite hessenberg.add_O_l. done. }
    iIntros "(LC& TG& #Od)".
    do 2 (iModIntro; lwp_pure_one).
    iApply lwpupd_label. iIntros "PL".
    iApply sfmupd_fupd_acc.
    iMod (tf_until_discharge with "HE") as "HE". 1: set_solver.
    iModIntro.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iDestruct "HE" as "[_ HE]". iMod ("HE" $! _) as "HE".
    iMod ("HE" with "[PL]") as "HE".
    { iNext. iEval (rewrite tf_atomic_logic). iFrame. }
    iPoseProof ("HE" with "[] Gg") as "HE".
    { iPureIntro. set_solver. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("HE" $! _) as "HE". iModIntro. iMod "HE" as "(PL& Gg& #Odkl)".
    iModIntro. iFrame "PL".
    replace ({[kl]} ∖ {[kl]} : gset _) with (∅ : oids) by set_solver.
    iMod (carrier_delete with "TG Gg") as "TG". 1: set_solver.
    iPoseProof (crP_fuels_remove_carrier g with "GF") as "GF".
    replace ({[g]} ∖ {[g]} : gset _) with (∅ : gset ocid) by set_solver.
    lwp_pures.
    iModIntro. lwp_finish.
    iApply "HΦ". rewrite /lift_term. iMod (thread_terminate with "TG") as "$". by iModIntro.
  Qed.

  Lemma flag_client_pre Θ i j Φ Ψs :
    i ≠ j →
    Θ = {[i := writer #(); j := reader #() ]} →
    Φ = (λ μ1 μ2, (∃ g1 g2 k kl1 kl2,
                      ⌜ k ≠ kl1 ⌝ ∗ flag_inv_tf l k 0 ∗
                      untilP Np k (1/2) (l ↦ #0) (l ↦ #1) ∗
                      finallyP Nl kl1 1 (i ⤉ "exit", #()) ∗
                      finallyP Nl kl2 1 (j ⤉ "exit", #1) ∗
                      ⟨thP_carriers i {[g1]} ∗ crP_obls g1 0 {[k; kl1]} ∗
                       thP_carriers j {[g2]} ∗ crP_obls g2 1 ({[kl2]}) ∗
                       crP_fuel g1 0 μ1 ∗ crP_fuel g2 1 μ2⟩)%F) →
    Ψs = ({[i := fork_post; j := fork_post]}) →
    ((l ↦ #0) -∗
     ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m ∃ μ1 μ2, (⟦Φ μ1 μ2⟧ₗ ∗
                       (⟦Φ μ1 μ2⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof.
    iIntros (Hij HT HP HQ) "Ptrl TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    iPoseProof (big_sepS_union with "TGs") as "[TG1 TG2]".
    { set_solver. }
    rewrite !big_sepS_singleton.
    iPoseProof (writer_spec) as (μ1) "writer_spec".
    iPoseProof (reader_spec) as (μ2) "reader_spec".
    iMod (carrier_alloc _ _ _ 0 μ1 with "TG1") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (flag_inv_init _ _ _ _ 0 _ μ1 with "Ptrl Gg1") as "(%k& %Hk& Gg1& Ofk& Uk& #flag_inv)". 1: done.
    iMod (tf_until_alloc _ _ _ false 0 0 μ1 with "Gg1") as "(%kl1& %Hkl1& Gg1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nl (⌜True⌝)%F (i ⤉ "exit",#())%F with "[]") as "Ukl1".
    { tf_red. done. }
    iMod (carrier_alloc _ _ _ 1 μ2 with "TG2") as "(%g2& %Ning2& TG2& Gg2& Gf2)".    
    iMod (tf_until_alloc _ _ _ false 1 1 1 with "Gg2") as "(%kl2& %Hkl2& Gg2& Ofkl2& #Wlkl2& Akl2)". 1: done.
    iMod ("Akl2" $! _ Nl (⌜True⌝)%F (j ⤉ "exit",#1)%F with "[]") as "Ukl2".
    { tf_red. done. }
    iModIntro. iExists μ1, μ2. iSplitL "Uk Ukl1 Ukl2 TG1 Gg1 TG2 Gg2 Gf1 Gf2 Ofk Ofkl1 Ofkl2".
    { subst Φ.
      tf_red. iExists g1. tf_red. iExists g2.
      tf_red. iExists k. tf_red. iExists kl1. tf_red. iExists kl2.
      rewrite -flag_inv_tf_red.
      tf_red. iSplit.
      { iPureIntro. intros <-. set_solver. }
      iFrame "flag_inv Uk".
      replace ({[kl1]} ∪ ({[k]} ∪ ∅)) with ({[k; kl1]} : gset _) by set_solver. rewrite !union_empty_r_L. iFrame. }
    iClear "flag_inv Wlkl1 Wlkl2". clear dependent g1 g2 k kl1 kl2.
    iIntros "HP". subst Φ.
    iEval (tf_red) in "HP". iDestruct "HP" as "(%g1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%g2& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%k& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%kl1& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%kl2& HP)".
    iEval (tf_red) in "HP". iDestruct "HP" as "(%Hkne& #flag_inv& Uk& Ukl1& Ukl2& TG1& Gg1& TG2& Gg2& Gf1& Gf2)".
    iPoseProof ("writer_spec" $! i g1 k kl1 (λ v, lift_term i fork_post v) with "[Uk Ukl1 TG1 Gg1 Gf1]") as "WP1".
    { iFrame. iSplit; eauto. }
    iPoseProof ("reader_spec" $! j g2 k kl2 (λ v, lift_term j fork_post v) with "[Ukl2 TG2 Gg2 Gf2]") as "WP2".
    { iFrame. eauto. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { rewrite lookup_insert_ne; auto. }
    { rewrite lookup_insert_ne; auto. }
    iSplitL "WP1".
    { iApply "WP1". iModIntro. eauto. }
    rewrite big_sepM2_singleton. iApply "WP2". iModIntro. eauto.
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let j : thread_id := 2%positive.
  Let l : loc := X_loc.
  Let Θ0 : thread_pool heap_lang := {[i := writer #(); j := reader #()]}.
  Let σ0 : gmap loc (option val) := {[l := Some #0]}.

  Let Φ : tp :=
        (flag_inv_tp l ∧
         tp_until (l ↦ #0) (l ↦ #1) ∧
         tp_finally (i ⤉ "exit", #()) ∧
         tp_finally (j ⤉ "exit", #1))%P.

  Let Φ' : tp :=
        (∃ (g1 g2 : ocid) (k kl1 kl2 : oid),
            ⌜ k ≠ kl1 ⌝ ∧ flag_inv_tp' l ∧
            tp_until (l ↦ #0) (l ↦ #1) ∧
            tp_finally (i ⤉ "exit", #()) ∧
            tp_finally (j ⤉ "exit", #1) ∧
            tp_true)%P.

  Remark Φ_impl :
    ∀ τ, tp_trace Φ' τ → tp_trace Φ τ.
  Proof.
    Local Opaque flag_inv_tp' flag_inv_tp.
    simpl. unfold_trProp. intros. destruct τ. destruct H as (?&?&?&?&?&?&?&?).
    split. 1: apply flag_inv_tp_impl; auto.
    firstorder.
    Local Transparent flag_inv_tp' flag_inv_tp.
  Qed.

  Let N := nroot.@ "flag".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".

  Let Nl := nroot.@ "writer_label".

  Let Φ_tf `{!heapGS Σ} : _ → _ → tf Σ :=
        λ μ1 μ2,
          (∃ g1 g2 k kl1 kl2,
              ⌜ k ≠ kl1 ⌝ ∗ flag_inv_tf l k 0 ∗
              untilP Np k (1/2) (l ↦ #0) (l ↦ #1) ∗
              finallyP Nl kl1 1 (i ⤉ "exit", #()) ∗
              finallyP Nl kl2 1 (j ⤉ "exit", #1) ∗
              ⟨thP_carriers i {[g1]} ∗ crP_obls g1 0 {[k; kl1]} ∗
               thP_carriers j {[g2]} ∗ crP_obls g2 1 ({[kl2]}) ∗
               crP_fuel g1 0 μ1 ∗ crP_fuel g2 1 μ2⟩)%F.

  Lemma tf_to_tp_Φ `{!heapGS Σ} m1 m2 :
    tf_to_tp (Φ_tf m1 m2) = Φ'.
  Proof. done. Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
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
    (* Set Printing All. *)
    iMod (flag_client_pre Θ0 i j with "[Ptrs] [TGs]") as "H".
    { subst i j. lia. }
    { done. }
    { reflexivity. }
    { reflexivity. }
    { subst σ0. rewrite big_sepM_singleton.
      by rewrite primitive_laws.pointsto_unseal /primitive_laws.pointsto_def. }
    { iFrame. }
    iDestruct "H" as (m1 m2) "(HP& H)".
    iModIntro. iExists (Φ_tf m1 m2). iFrame "HP". iSplit.
    { iPureIntro. apply tf_to_tp_Φ. }
    iFrame.
  Qed.

End adequacy.

(* Print Assumptions flag_client_adequacy. *)
