From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.

(** * A move below an obligation of the same layer is unsound

    With the non-strict [obl_move] (the new parent's layer may equal the payment layer), each
    iteration of a loop moves the old root below a fresh root at layer 0, paying its last unit
    at layer 0, and pays the step with the new root. Adequacy then gives "eventually False". *)

Class obl_move_nonstrict `(HGS : lantanaGS Λ Σ) `{!TemporalInterp Λ Σ} := {
    obl_move_le E p1 q K1 K2 k (ℓ ℓq : ord.t) :
      k ∈ K1 → (ℓq <= ℓ)%ordi →
      witP_layer q ℓq -∗ parP_kids p1 K1 -∗ oblP_kids q K2 -∗ oblP_fuel k ℓ 1 -∗
      |={E}=>m ⌜ k ∉ K2 ⌝ ∗ parP_kids p1 (K1 ∖ {[k]}) ∗ oblP_kids q ({[k]} ∪ K2);
  }.

Definition loop : val :=
  rec: "loop" <> :=
    "loop" #().

Section proof.
  Context `{!heapGS Σ} `{!@obl_move_nonstrict _ _ Σ _ _}.

  Lemma loop_spec i r C Φ :
    thread_expr i C (loop #()) -∗ thP_kids i {[r]} -∗ oblP_fuel r 0 1 -∗
    lWP (loop #()) @ i {{ Φ }}.
  Proof using Type*.
    iIntros "TE TG Fr".
    iLöb as "IH" forall (r).
    iApply sfmupd_lwp.
    iMod (obl_new _ (PThread i) {[r]} 0 2 with "[] TG") as "(%r'& %Hr'& TG& Kr'& _& Fr'& #Wr')".
    { iApply parP_le_thread. }
    iMod (obl_move_le _ (PThread i) r' ({[r']} ∪ {[r]}) ∅ r 0 0 with "Wr' TG Kr' Fr")
      as "(_& TG& _)".
    { set_solver. }
    { done. }
    replace (({[r']} ∪ {[r]}) ∖ {[r]}) with ({[r']} : gset oid) by set_solver.
    iPoseProof (oblP_fuel_add_nat 1 1 with "Fr'") as "[GF Fr']"; first done.
    iAssert (oblP_fuels {[r']} 1) with "[GF]" as "GF".
    { rewrite big_sepS_singleton. iExists _. iFrame. }
    iModIntro.
    rewrite /loop.
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, 1. iSplitR; first eauto. iIntros "TG GF _ LC TE".
    iModIntro.
    iApply (lwp_lc_later with "LC"). iNext.
    iApply ("IH" with "TE TG Fr'").
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let Θ0 : thread_pool heap_lang := {[i := loop #()]}.
  Let σ0 : gmap loc (option val) := ∅.
  Let N := nroot .@ "nonstrict".

  Let Φ_P `{!heapGS Σ} : iProp Σ :=
        (∃ x, untilI N x 1 True False ∗ (thP_kids i {[x]} ∗ oblP_fuel x 0 1))%I.

  Section G_main.
    Context `{!heapGS Σ}.
    Definition G_main : itrProp heap_lang Σ := ltac:(itrProp_of Φ_P).
  End G_main.

  Lemma Φ_P_temporal `{!heapGS Σ} : ⊢ Φ_P ⊨ₜ G_main.
  Proof. apply (into_temporal _ _). Qed.

  Remark G_main_false {Σ} τ : itrProp_external (G_main (Σ:=Σ)) τ → False.
  Proof.
    destruct τ as [n τf]. simpl. intros (Hu& _). destruct Hu as (m& _& HF& _). done.
  Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          tregGS.tregΣ heap_lang;
          heap_stateΣ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := fork_post]}.

  Theorem nonstrict_move_unsound :
    (∀ Λ0 Σ0 (HGS : lantanaGS Λ0 Σ0) (TI : TemporalInterp Λ0 Σ0), @obl_move_nonstrict _ Λ0 Σ0 HGS TI) →
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    False.
  Proof.
    intros NS τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_temporal Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] G_main (λ _, False)).
    { apply G_main_false. }
    1,2,3,4: eauto.
    iIntros (?). exists (2 : Ord.t)%ord.
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
    iEval (rewrite dom_singleton_L big_sepS_singleton) in "TGs".
    iMod (untilI_alloc _ _ _ 0 1 with "[] TGs") as "(%x& _& TG& _& Fx& _& Ax)".
    { iApply parP_le_thread. }
    iMod ("Ax" $! _ N True%I False%I with "[//]") as "Ux".
    rewrite union_empty_r_L.
    iModIntro. iExists (Φ_P (heapGS0:=HHeapGS)).
    iSplitR; first iApply Φ_P_temporal.
    iSplitL "Ux TG Fx".
    { iExists x. iFrame. }
    iIntros "(%x'& _& TG& Fx)". iModIntro.
    pose proof (NS heap_lang Σ HlantanaGS _) as HNS.
    rewrite /Θ0 /Ψs. iApply big_sepM2_singleton.
    iEval (rewrite big_sepM_singleton) in "Tis".
    iApply (loop_spec (heapGS0:=HHeapGS) i x' [] with "[Tis] TG Fx").
    rewrite /thread_expr /=. iFrame.
  Qed.

  (** The run of [loop]: thread [i] steps from [loop #()] to [loop #()] forever. It is a fair
      behavior, so the assumed rule is absurd. *)
  Lemma loop_prim_step σ tids :
    prim_step i (loop #()) σ tids [] (loop #()) σ ∅.
  Proof. apply ectx_language.base_prim_step. by econstructor. Qed.

  Let ρ0 : cfg heap_lang := (Θ0, Build_state σ0 ∅).
  Let loop_run : trace heap_lang := (0, λ _, (ρ0, i, [])).

  Lemma loop_run_behavior n : behavior (n, loop_run.2).
  Proof.
    revert n. cofix IH. intros n.
    eapply (behavior_step n _ ρ0 ρ0 i i [] []); [done| |done|apply IH].
    left. eapply (thread_step_atomic (loop #()) _ (loop #()) _ ∅ Θ0).
    - done.
    - rewrite /Θ0. by simplify_map_eq.
    - apply loop_prim_step.
    - rewrite /ρ0 /Θ0 insert_singleton right_id_L. done.
  Qed.

  Lemma loop_run_fair : fair_scheduling loop_run.
  Proof.
    intros m _ j. simpl. rewrite /ρ0 /Θ0.
    destruct (decide (j = i)) as [->|Hj].
    - right. split.
      + exists (loop #()). split; first by simplify_map_eq. done.
      + exists m. simpl. split; first lia. done.
    - left. left. by simplify_map_eq.
  Qed.

  Theorem nonstrict_move_absurd :
    (∀ Λ0 Σ0 (HGS : lantanaGS Λ0 Σ0) (TI : TemporalInterp Λ0 Σ0), @obl_move_nonstrict _ Λ0 Σ0 HGS TI) →
    False.
  Proof.
    intros NS. apply (nonstrict_move_unsound NS loop_run).
    - apply loop_run_behavior.
    - apply loop_run_fair.
    - done.
    - done.
  Qed.

End adequacy.
