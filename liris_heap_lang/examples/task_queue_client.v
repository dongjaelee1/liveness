From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From liris.heap_lang.examples Require Export flag task_queue.

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
    let: "x" := Flag.init in
    let: "n" := ChooseNat in
    decr_reentrant ("q", "x", "n");;
    let: "v" := Flag.wait "x" in
    Ret "v".

Section proof.
  Context `{!heapGS Σ, !queueG Σ, !ticket_lockG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let Nl := nroot.@ "label".

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
    ⊢ ∃ μ, ∀ lc i G g k K γ ℓg arg,
    l{{{ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g 1%ordi μ) ∗
         crP_obls g ℓg K ∗ ⌜k ∈ K⌝ ∗
         ∃ (ql : val) (x : loc) (n : Z),
           ⌜arg = (ql, #x, #n)%V⌝ ∗
           oblP_fuel k (ℓq ⊕ 1)%ordi (Z.to_nat n)%M ∗
           flag_tk x k ∗
           is_decr_reentrant arg γ k }}}
      decr_reentrant arg @ i
    l{{{ RET #(); £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K ∖ {[k]}) }}}.
  Proof.
    unfold decr_reentrant.
    (** Lob to bootstrap the spec *)
    iLöb as "TASK".
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (TaskQueue_put_task_spec) as (μ_tp) "TaskQueue_put_task_spec".
    iExists (100 ⊕ (μ_fs ⊕ μ_tp))%M.
    iIntros (lc i G g k K γ ℓg arg) "!> % (TG& GF& Gg& %SubK& %&%&%& %Harg& Of& Ftk& #DRI) HΦ".
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
      iModIntro. iApply ("Flag_set_spec" $! 0 with "[$TG $F_fs $Gg $Ftk $is_flag]").
      { auto. }
      iIntros "(_& TG& Cg& #Od)". iApply ("HΦ" with "[$Q_LC $TG $Cg]").
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
      iModIntro. iApply ("TaskQueue_put_task_spec" $! 0 _ _ _ _ {[k]} γ ℓq with "[$TG $F_tp $Gg Of1 Of Ftk]").
      { iClear "TaskQueue_put_task_spec". iSplit.
        { iPureIntro. set_solver. }
        iSplitL "Of1".
        { iApply big_sepS_singleton. iFrame. }
        rewrite /is_task_queue. iFrame "is_task_queue".
        rewrite /is_task. iDestruct "TASK" as (mt) "TASK".
        iExists _, _, 1%ordi, _. iSplit.
        { iPureIntro. split; first eauto. apply ℓq_cond. }
        iSplitL.
        { iCombine "Of Ftk" as "H". iApply "H". }
        iExists mt. iIntros (??????) "!> % (TG& GF& Gg& %Hsub& OF& Ftk) HΦ".
        iApply ("TASK" $! lc0 with "[$TG $GF $Gg $OF $Ftk]").
        { iSplit.
          { iPureIntro. set_solver. }
          iExists _. iSplit; first done. rewrite /is_decr_reentrant /is_task_queue.
          iFrame "is_flag is_task_queue". eauto. }
        iIntros "(LC& TG& Gg)". iApply ("HΦ" with "[$LC $TG $Gg]"). }
      iIntros "(_& TG& Gg)". iApply ("HΦ" with "[$Q_LC $TG $Gg]").
  Qed.

  Lemma main_spec :
    ⊢ ∃ μ, ∀ i g kl,
    l{{{ thP_carriers i {[g]} ∗ crP_fuel g (ℓq ⊕ 2)%ordi μ ∗
         crP_obls g (ℓq ⊕ 2)%ordi {[kl]} ∗
         ⟦finallyP Nl kl 1 (ret #1 @ i)⟧ₗ }}}
      main #() @ i
    l{{{ v, RET v; lift_term i (λ _ v, ⌜v = #1⌝) v }}}.
  Proof.

    TODO
    unfold main.
    iPoseProof (decr_reentrant_spec) as (md) "decr_reentrant_spec".
    (* Internal steps, func call, while loop *)
    iExists (100 ⊕ md ⊕ (100 × ▽))%M. iIntros (lc i G γ ql) "!> % (TG& GF& #ITQ) HΦ".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF GF2]".
    iPoseProof (crP_fuel_add_set with "GF2") as "[F_md GFloop]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_bind (AllocN _ _).
    iPoseProof (crP_fuels_add 98 1 with "GF") as "[GF GF1]". 1: lia.
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ptr_l) "((_& TG& _)& Ptr_l& _)".
    lwp_pures.
    lwp_bind (ChooseNat).
    iPoseProof (crP_fuels_add 95 1 with "GF") as "[GF GF1]". 1: lia.
    iModIntro. iApply (lwp_choosenat _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iIntros (n) "(_& TG& _)".
    lwp_pures.

    TODO
    

    
    lwp_pures.

    
    subst arg.
    lwp_pures.
    destruct (decide (n ≤ 0)%Z).
    - iClear "TASK TaskQueue_put_task_spec". rewrite bool_decide_eq_true_2; last done.
      lwp_pure_lc 100.
      lwp_bind (Store _ _).
      iDestruct "DRI" as "(%&%&%& %& Oik& Wlk& Inv& ITQ)". symmetry in H. simplify_eq.
      iModIntro.
      iEval (rewrite tf_always_logic) in "Inv".
      iMod (inv_acc with "Inv") as "[H ACCinv]". 1: set_solver.
      (* and we need a mupd after the step. *)
      iApply lwp_sfmupd.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lwp_lc_later with "LC1"). iNext.
      iEval (tf_red) in "H". iDestruct "H" as "[H | H]"; cycle 1.
      { iDestruct "H" as "(HF& _)".
        rewrite tf_until_logic. iDestruct "Huntil" as "(HA& _)".
        iPoseProof (oblP_assigned_discharged_false with "HA HF") as "%". done. }
      iCombine "Huntil H" as "Huntil".
      iMod (tf_until_discharge with "Huntil") as "ACCuntil". 1: apply N_subseteq_1.
      iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
      iApply (lwp_lc_later with "LC1"). iNext.
      iDestruct "ACCuntil" as "[Ptrl ACCuntil]". iEval (rewrite tf_atomic_logic) in "Ptrl".
      iPoseProof (crP_fuels_add 85 1 with "GF") as "[GF GF1]". 1: lia.
      iApply lwp_sfmupd.
      iApply (lwp_store _ ∅ 0 with "[$TG $GF1 $Ptrl]"). 1: done.
      iIntros "((_& TG& _)& Ptrl)".
      iMod ("ACCuntil" $! _ with "Ptrl") as ">ACCuntil".
      iPoseProof ("ACCuntil" with "[] Gg") as "ACCuntil".
      { iPureIntro. set_solver. }
      iPoseProof (tlc_split_nat 1 97 with "LC") as "[LC1 LC]".
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      iMod ("ACCuntil" $! _) as "ACCuntil". iModIntro.
      iMod "ACCuntil" as "(Ptrl& Gg& #Gfk)".
      do 2 iModIntro. iMod ("ACCinv" with "[Ptrl]") as "_".
      { iNext. tf_red. iRight. iFrame. eauto. }
      iModIntro. iApply ("HΦ" with "[$Q_LC $TG $Gg]").
    - rewrite bool_decide_eq_false_2; last done.
      lwp_pure_lc 100.
      lwp_pures.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_lwpupd_add_later with "LC1"). iNext.
      lwp_bind (TaskQueue.put_task _ _ _).
      assert (Hn : Z.to_nat n = 1 + Z.to_nat (n - 1)) by lia.
      rewrite (oblP_fuel_eq k _ _ (1 ⊕ (Z.to_nat (n - 1)))%M); cycle 1.
      { rewrite measure_rep_add !measure_rep_nat -Hessenberg.add_from_nat Hn. done. }
      iPoseProof (oblP_fuel_add with "OF") as "[OF1 OF]".
      iModIntro. iApply ("TaskQueue_put_task_spec" $! 0 _ _ _ _ _ {[k]} γ ℓq with "[$TG $F_put_task $Gg OF1 OF Huntil]").
      { iClear "TaskQueue_put_task_spec". iSplit.
        { iPureIntro. set_solver. }
        iSplitL "OF1".
        { iApply big_sepS_singleton. iFrame. }
        iDestruct "DRI" as "(%&%&%& %& Oik& Wlk& Inv& ITQ)". simplify_eq.
        rewrite /is_task_queue. iFrame "ITQ".
        rewrite /is_task. iDestruct "TASK" as (mt) "TASK".
        iExists _, _, ℵ%ordi, _, mt. iSplit.
        { iPureIntro. split; first eauto. apply ℓq_cond. }
        iSplitL.
        { iCombine "OF Huntil" as "H". iApply "H". }
        iIntros (???????) "!> % (TG& GF& Gg& %Hsub& OF& Huntil) HΦ".
        iApply ("TASK" $! lc0 with "[$TG $GF $Gg $OF $Huntil]").
        { iSplit.
          { iPureIntro. set_solver. }
          iExists _. iSplit; first done. iFrame "Oik Wlk Inv".
          rewrite /is_task_queue. iFrame "ITQ". eauto. }
        iIntros "(LC& TG& Gg)". iApply ("HΦ" with "[$LC $TG $Gg]"). }
      iIntros "(_& TG& Gg)". iApply ("HΦ" with "[$Q_LC $TG $Gg]").
  Qed.

  


  TODO
Definition main : val :=
  λ: "q", let: "l" := ref #0 in
          let: "n" := ChooseNat in
          decr_reentrant ("q", "l", "n");;
          (rec: "while" <> := if: !"l" = #1%Z
                             then Label "exit" #()
                             else "while" #()) #().

Definition main : val :=
  λ: <>,
    let: "q" := TaskQueue.init #() in
    main "q".
    
End proof.

Section adequacy.

  Definition mp_tp (l : loc) : tp :=
    (tp_always (((tp_until (l ↦ #0) (l ↦ #1)) ∨ (l ↦ #1))))%P.

  Definition mp_tp' (l : loc) : tp :=
    (tp_true ∧ tp_always (((tp_until (l ↦ #0) (l ↦ #1)) ∨ (tp_true ∧ (l ↦ #1)))))%P.

  (** TODO: weaken the strict equality to semantics equivalence/implication. *)
  Remark tf_to_tp_mp' `{!heapGS Σ} k l :
    tf_to_tp (mp_tf k l) = mp_tp' l.
  Proof. done. Qed.

  Remark mp_tp_impl l :
    ∀ τ, tp_trace (mp_tp' l) τ → tp_trace (mp_tp l) τ.
  Proof.
    simpl. unfold_trProp. simpl. intros. destruct τ. destruct H. intros. specialize (H0 _ H1).
    destruct H0.
    - destruct H0 as (?&?&?&?). left. eexists. split_and !; eauto.
    - destruct H0. right. eauto.
  Qed.

  Let i : thread_id := 1%positive.
  Let j : thread_id := 2%positive.
  Let l : loc := Loc 0.
  Let Θ0 : thread_pool heap_lang := {[i := writer #l; j := reader #l]}.
  Let σ0 : gmap loc (option val) := {[l := Some #0]}.

  Let Φ : tp :=
        (mp_tp l ∧
         tp_until (l ↦ #0) (l ↦ #1) ∧
         tp_finally (∃ v, (i ⤉ "exit", v) ∧ ⌜ v = #() ⌝) ∧
         tp_finally (∃ v, (j ⤉ "exit", v) ∧ ⌜ v = #() ⌝))%P.

  Let Φ' : tp :=
        (∃ (g1 g2 : ocid) (k kl1 kl2 : oid),
            ⌜ k ≠ kl1 ⌝ ∧ mp_tp' l ∧
            tp_until (l ↦ #0) (l ↦ #1) ∧
            tp_finally (∃ v, (i ⤉ "exit", v) ∧ ⌜ v = #() ⌝) ∧
            tp_finally (∃ v, (j ⤉ "exit", v) ∧ ⌜ v = #() ⌝) ∧
            tp_true)%P.

  Remark Φ_impl :
    ∀ τ, tp_trace Φ' τ → tp_trace Φ τ.
  Proof.
    Local Opaque mp_tp' mp_tp.
    simpl. unfold_trProp. simpl. intros. destruct τ. destruct H as (?&?&?&?&?&?&?&?).
    split. 1: apply mp_tp_impl; auto.
    firstorder.
    Local Transparent mp_tp' mp_tp.
  Qed.

  Let N := nroot.@ "message_passing".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".
  Let Nl := N.@ "label".

  Let Φ_tf `{!heapGS Σ} : tf Σ :=
        (∃ g1 g2 k kl1 kl2,
            ⌜ k ≠ kl1 ⌝ ∗ mp_tf k l ∗
            tf_until Np k false (1/2) (l ↦ #0) (l ↦ #1) ∗
            tf_finally Nl kl1 false 1 (∃ v, (i ⤉ "exit", v) ∗ ⌜ v = #() ⌝) ∗
            tf_finally Nl kl2 false 1 (∃ v, (j ⤉ "exit", v) ∗ ⌜ v = #() ⌝) ∗
            ⟨thP_carriers i {[g1]} ∗ crP_obls i g1 0 {[k; kl1]} ∗
             thP_carriers j {[g2]} ∗ crP_obls j g2 1 ({[kl2]}) ∗
             crP_fuel g1 0 10 ∗ crP_fuel g2 1 ((1 × ▽) ⊕ 1)%M⟩)%F.

  Lemma tf_to_tp_Φ `{!heapGS Σ} :
    tf_to_tp Φ_tf = Φ'.
  Proof. done. Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          heap_stateΣ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := fork_post; j := fork_post]}.

  Theorem mp_adequacy :
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
    iMod (mp_pre Θ0 i j l with "[Ptrs] [TGs]") as "H".
    { subst i j. lia. }
    { done. }
    { reflexivity. }
    { reflexivity. }
    { subst σ0. rewrite big_sepM_singleton.
      by rewrite primitive_laws.pointsto_unseal /primitive_laws.pointsto_def. }
    { iFrame. }
    iDestruct "H" as "(HP& H)".
    iModIntro. iExists Φ_tf. iFrame "HP". iSplit.
    { iPureIntro. apply tf_to_tp_Φ. }
    iFrame.
  Qed.

End adequacy.

(* Print Assumptions mp_adequacy. *)
