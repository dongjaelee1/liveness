From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.program_logic Require Export temporal_logic.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Export flag task_queue.

Definition decr_reentrant : val :=
  (rec: "f" "a" :=
     let: "q" := Fst (Fst "a") in
     let: "x" := Snd (Fst "a") in
     let: "n" := Snd "a" in
     if: "n" ≤ #0%Z
     then Flag.set "x"
     else TaskQueue.put_task "q" "f" ("q", "x", "n" - #1%Z)).

Definition main : val :=
  λ: <>,
    let: "q" := TaskQueue.init #() in
    let: "x" := Flag.init #() in
    let: "n" := ChooseNat in
    decr_reentrant ("q", "x", "n");;
    let: "v" := Flag.wait "x" in
    "v".

Section proof.
  Context `{!heapGS Σ, !queueG Σ, !ticket_lockG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let Nl := nroot.@ "return".

  (** 1 < ℓq (by TaskQueue_put_task_spec, is_task *)
  Let ℓq : ord.t := (1 ⊕ 1)%ordi.
  Remark ℓq_cond : (1 < ℓq)%ordi.
  Proof. apply hessenberg.add_lt_l. apply ord.S_lt. Qed.

  Definition is_decr_reentrant (arg : val) γ (k : oid) : iProp Σ :=
    ∃ (ql : val) (x : loc) (n : Z),
      ⌜arg = (ql, #x, #n)%V⌝ ∧
      is_flag x k (ℓq ⊕ 1)%ordi ∗
      is_task_queue ql γ ℓq.

  (** The main proof. *)
  Global Instance is_decr_reentrant_persistent arg γ k : Persistent (is_decr_reentrant arg γ k).
  Proof. rewrite /is_decr_reentrant. apply _. Qed.

  Lemma decr_reentrant_spec :
    ⊢ ∃ μ, ∀ lc i G g k K γ ℓg (arg : val) C,
    l{{{ thread_expr i C (decr_reentrant arg) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g 1%ordi μ) ∗
         crP_obls g ℓg K ∗ ⌜k ∈ K⌝ ∗
         ∃ (ql : val) (x : loc) (n : Z),
           ⌜arg = (ql, #x, #n)%V⌝ ∗
           oblP_fuel k (ℓq ⊕ 1)%ordi (Z.to_nat n)%M ∗
           flag_tk x k ∗
           is_decr_reentrant arg γ k }}}
      decr_reentrant arg @ i
    l{{{ RET #(); thread_expr i C #() ∗ £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K ∖ {[k]}) }}}.
  Proof.
    unfold decr_reentrant.
    (** Lob to bootstrap the spec *)
    iLöb as "TASK".
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (TaskQueue_put_task_spec) as (μ_tp) "TaskQueue_put_task_spec".
    iExists (100 ⊕ (μ_fs ⊕ μ_tp))%M.
    iIntros (lc i G g k K γ ℓg arg C) "!> % (TE& TG& GF& Gg& %SubK& %&%&%& %Harg& Of& Ftk& #DRI) HΦ".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF Fm]".
    iPoseProof (crP_fuel_add_set with "Fm") as "[F_fs F_tp]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure_lc lc. iRename "LC" into "Q_LC".
    subst arg.
    lwp_pures.
    iDestruct "DRI" as "(%&%&%& %& is_flag& is_task_queue)".
    symmetry in H. simplify_eq /=.
    destruct (decide (n ≤ 0)%Z).
    - iClear "TASK TaskQueue_put_task_spec". rewrite bool_decide_eq_true_2; last done.
      iModIntro. lwp_pure_lc 100.
      lwp_bind (Flag.set _).
      iMod (crP_fuel_layer_mon_set _ 0 with "F_fs") as "F_fs".
      { apply ordArith.le_from_nat. lia. }
      iModIntro. iApply ("Flag_set_spec" $! 0 with "[$TE $TG $F_fs $Gg $Ftk $is_flag]").
      { auto. }
      iIntros "(TE& _& TG& Cg& #Od)". iApply ("HΦ" with "[$TE $Q_LC $TG $Cg]").
    - rewrite bool_decide_eq_false_2; last done.
      iModIntro. lwp_pure_lc 100.
      lwp_pures.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_lwpupd_add_later with "LC1"). iNext.
      lwp_bind (TaskQueue.put_task _ _ _).
      assert (Hn : Z.to_nat n = 1 + Z.to_nat (n - 1)) by lia.
      rewrite (oblP_fuel_eq k _ _ (1 ⊕ (Z.to_nat (n - 1)))%M); cycle 1.
      { rewrite measure_rep_add !measure_rep_nat -Hessenberg.add_from_nat Hn. done. }
      iPoseProof (oblP_fuel_add with "Of") as "[Of1 Of]".
      iModIntro. iApply ("TaskQueue_put_task_spec" $! 0 _ _ _ _ {[k]} γ ℓq with "[$TE $TG $F_tp $Gg Of1 Of Ftk]").
      { iClear "TaskQueue_put_task_spec". iSplit.
        { iPureIntro. set_solver. }
        iSplitL "Of1".
        { iApply big_sepS_singleton. iFrame. }
        rewrite /is_task_queue. iFrame "is_task_queue".
        rewrite /is_task. iDestruct "TASK" as (mt) "TASK".
        iExists 1%ordi, _. iSplit.
        (* iExists _, _, 1%ordi, _. iSplit. *)
        { iPureIntro. apply ℓq_cond. }
        (* { iPureIntro. split; first eauto. apply ℓq_cond. } *)
        iSplitL.
        { iCombine "Of Ftk" as "H". iApply "H". }
        iExists mt. iIntros (???????) "!> % (TE& TG& GF& Gg& %Hsub& OF& Ftk) HΦ".
        iApply ("TASK" $! lc0 with "[$TE $TG $GF $Gg $OF $Ftk]").
        { iSplit.
          { iPureIntro. set_solver. }
          iExists _. iSplit; first done. rewrite /is_decr_reentrant /is_task_queue.
          iFrame "is_flag is_task_queue". eauto. }
        iIntros "(TE& LC& TG& Gg)". iApply ("HΦ" with "[$TE $LC $TG $Gg]"). }
      iIntros "(TE& _& TG& Gg)". iApply ("HΦ" with "[$TE $Q_LC $TG $Gg]").
  Qed.

  (** The depth form of [decr_reentrant]'s specification, for clients. *)
  Lemma decr_reentrant_dspec :
    ⊢ ∀ lc i G g k K γ ℓg (arg : val) C,
    l{{{ thread_expr i C (decr_reentrant arg) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_dfuel g 1%ordi 1 1) ∗
         crP_obls g ℓg K ∗ ⌜k ∈ K⌝ ∗
         ∃ (ql : val) (x : loc) (n : Z),
           ⌜arg = (ql, #x, #n)%V⌝ ∗
           oblP_fuel k (ℓq ⊕ 1)%ordi (Z.to_nat n)%M ∗
           flag_tk x k ∗
           is_decr_reentrant arg γ k }}}
      decr_reentrant arg @ i
    l{{{ RET #(); thread_expr i C #() ∗ £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K ∖ {[k]}) }}}.
  Proof using queueG0 ticket_lockG0.
    iPoseProof (decr_reentrant_spec) as (μ) "#S".
    iIntros (lc i G g k K γ ℓg arg C Φ) "!> (TE& TG& GF& Gg& %Hk& HR) HΦ".
    iMod (crP_dfuel_to_fuel_set _ _ 0 μ with "GF") as "GF".
    iApply ("S" with "[$TE $TG $GF $Gg $HR //] HΦ").
  Qed.

  Lemma main_spec :
    ⊢ ∀ i g kl,
    l{{{ thread_expr i [] (main #()) ∗ thP_carriers i {[g]} ∗ ([∗ set] g ∈ {[g]}, crP_dfuel g (ℓq ⊕ 2)%ordi 2 1) ∗
         crP_obls g (ℓq ⊕ 2)%ordi {[kl]} ∗
         ⟦finallyP Nl kl 1 (exits #1@i)⟧ₗ }}}
      main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ lift_term i (λ _ v, ⌜v = #1⌝) v }}}.
  Proof using queueG0 ticket_lockG0.
    unfold main.
    iPoseProof (TaskQueue_init_dspec) as "#TaskQueue_init_dspec".
    iPoseProof (Flag_init_dspec) as "#Flag_init_dspec".
    iPoseProof (decr_reentrant_dspec) as "#decr_reentrant_dspec".
    iPoseProof (Flag_wait_dspec) as "#Flag_wait_dspec".
    iIntros (i g kl) "!> % (TE& TG& GF& Cg& HF) HΦ".
    (* One unit per call site (task queue init, flag init, decr, wait) and
       one for the local steps. The budgets of the callees never appear. *)
    iMod (crP_dfuel_depth_extend_nat_set _ _ 1 ((((1 ⊕ 1) ⊕ 1) ⊕ 1) ⊕ 1)%M with "GF") as "GF".
    iPoseProof (crP_dfuel_add_set with "GF") as "[GF GF_fw]".
    iPoseProof (crP_dfuel_add_set with "GF") as "[GF GF_d]".
    iPoseProof (crP_dfuel_add_set with "GF") as "[GF GF_fi]".
    iPoseProof (crP_dfuel_add_set with "GF") as "[GF GF_ti]".
    iMod (crP_dfuel_to_fuel_set _ _ 0 100 with "GF") as "GF".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure_lc 100.
    lwp_pures.
    lwp_bind (TaskQueue.init _).
    iMod (crP_dfuel_layer_extend_set _ 0 _ 1 _ 1 with "GF_ti") as "GF_ti".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.lt_from_nat. lia. }
    iModIntro. iApply ("TaskQueue_init_dspec" $! 0 _ _ ℓq with "[$TE $TG $GF_ti]").
    { iPureIntro. apply ord.lt_le, ℓq_cond. }
    iIntros (ql qγ) "(TE& _& TG& #ITQ)".
    lwp_pures.
    lwp_bind (Flag.init _).
    iMod (carrier_alloc_d _ _ _ (ℓq ⊕ 1)%ordi 1 ((1 ⊕ 1) ⊕ 1)%M with "TG")
      as "(%& %NinG& TG& Cg0& GF0)".
    iPoseProof (crP_dfuel_add with "GF0") as "[GF0 F_d0]".
    iPoseProof (crP_dfuel_add with "GF0") as "[GF0 F_init0]".
    iMod (crP_dfuel_to_fuel _ _ 0 97 with "GF0") as "GF0".
    iMod (crP_dfuel_layer_extend_set _ 0 _ 1 _ 1 with "GF_fi") as "F_init".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.lt_from_nat. lia. }
    iMod (crP_dfuel_layer_extend _ 0 _ 1 _ 1 with "F_init0") as "F_init0".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.lt_from_nat. lia. }
    iModIntro.
    iApply ("Flag_init_dspec" $! 0 _ _ _ _ _ (ℵ)%M with "[$TE $TG F_init F_init0 $Cg0]").
    { iApply big_sepS_union. 1: set_solver. rewrite !big_sepS_singleton. iFrame. }
    iIntros "%ptrx %k (TE& _& TG& _& Cg0& Of0& Ftk& #is_flag)".
    rewrite union_empty_r_L.
    iPoseProof (crP_fuels_add_carrier with "GF0 GF") as "GF".
    lwp_pures.
    lwp_bind (ChooseNat).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_choosenat _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iIntros (n) "(TE& _& TG& _)".
    lwp_pures.
    lwp_bind (decr_reentrant _).
    iMod (oblP_fuel_mon _ _ (n)%M with "Of0") as "Of0".
    { rewrite !measure_rep_nat measure_rep_large.
      etrans; first (eapply Ord.lt_le, Ord.omega_upperbound).
      rewrite Ord.omega_from_peano_lt_set.
      eapply Ord.lt_le, Ord.large_lt_from_wf_set. }
    iMod (crP_dfuel_layer_mon_set _ 1 with "GF_d") as "F_d".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.le_from_nat. lia. }
    iMod (crP_dfuel_layer_mon _ 1 with "F_d0") as "F_d0".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.le_from_nat. lia. }
    iModIntro.
    iApply ("decr_reentrant_dspec" $! 0 with "[$TE $TG F_d F_d0 $Cg0 Of0 $Ftk]").
    { iSplitR "Of0".
      { iApply big_sepS_union. 1: set_solver. rewrite !big_sepS_singleton. iFrame. }
      iSplitR.
      { iPureIntro. set_solver. }
      iExists ql, n. iSplitR; first done. replace (Z.to_nat n) with n by lia.
      iFrame. iFrame "ITQ is_flag". eauto. }
    iIntros "(TE& _& TG& Cg0)".
    iMod (carrier_delete_fuels _ _ _ {[g]} with "TG Cg0 GF") as "[TG GF]". 1-3: set_solver.
    lwp_pures.
    lwp_bind (Flag.wait _).
    iModIntro.
    iMod (crP_dfuel_layer_mon_set _ ((ℓq ⊕ 1) ⊕ 1)%ordi with "GF_fw") as "GF_fw".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.le_from_nat. lia. }
    iApply ("Flag_wait_dspec" $! 0 with "[$TE $TG $GF_fw $is_flag]").
    iIntros "(TE& _& TG& #Od0)".
    do 2 (iModIntro; lwp_pure_one).
    iApply lwpupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 2 98 with "LC") as "[LC _]".
    iMod (thread_expr_terminate with "TE LC TG Cg HF") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. iFrame "Td". done.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := main #() ]} →
    Φ = (∃ g kl, finallyP Nl kl 1 (exits #1@i) ∗
                 ⟨thP_carriers i {[g]} ∗ crP_obls g (ℓq ⊕ 2)%ordi {[kl]} ∗
                  crP_dfuel g (ℓq ⊕ 2)%ordi 2 1⟩)%F →
    Ψs = ({[i := (λ _ v, ⌜v = #1⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m (⟦Φ⟧ₗ ∗
              (⟦Φ⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof using queueG0 ticket_lockG0.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (main_spec) as "#main_spec".
    iMod (carrier_alloc_d _ _ _ (ℓq ⊕ 2)%ordi 2 1 with "TGs") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (tf_until_alloc _ _ _ false (ℓq ⊕ 2)%ordi (ℓq ⊕ 2)%ordi 0 with "Gg1") as "(%kl1& %Hkl1& Gg1& Ofkl1& #Wlkl1& Akl1)". 1: done.
    iMod ("Akl1" $! _ Nl (⌜True⌝)%F (exits #1@i)%F with "[]") as "Ukl1".
    { tf_red. done. }
    iModIntro. iSplitL "Ukl1 TG1 Gg1 Gf1 Ofkl1".
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
    { iFrame. iApply big_sepS_singleton. iFrame. }
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
  Let ℓq : ord.t := (1 ⊕ 1)%ordi.

  Let Φ_tf `{!heapGS Σ} : tf Σ :=
          (∃ g kl,
              finallyP Nl kl 1 (exits #1@i) ∗
              ⟨thP_carriers i {[g]} ∗ crP_obls g (ℓq ⊕ 2)%ordi {[kl]} ∗
               crP_dfuel g (ℓq ⊕ 2)%ordi 2 1⟩)%F.

  Lemma tf_to_tp_Φ `{!heapGS Σ} :
    tf_to_tp Φ_tf = Φ'.
  Proof. done. Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          heap_stateΣ;
          queueΣ;
          ticket_lockΣ
          ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := (λ _ v, ⌜v = #1⌝)%I]}.

  Theorem task_queue_client_adequacy :
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
    iMod (main_pre (heapGS0:=HHeapGS) (queueG0:=QueueG Σ _) Θ0 i with "[Tis] [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as "(HP& H)".
    iModIntro. iExists Φ_tf. iFrame "HP". iSplit.
    { iPureIntro. apply tf_to_tp_Φ. }
    iFrame.
  Qed.

End adequacy.

(* Print Assumptions task_queue_client_adequacy. *)
