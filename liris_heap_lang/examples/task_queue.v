From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From iris.algebra Require Import reservation_map dfrac_agree mono_list gset.
From transfinite.base_logic.lib Require Import ghost_var ghost_map.
From liris.algebra Require Import list_of_sets.
From liris.heap_lang.examples Require Export queue.

Module TaskQueue.

  Definition put_task : val :=
    λ: "q" "f" "a",
      Queue.enqueue "q" ("f", "a").

  Definition run_task : val :=
    λ: "q",
      match: Queue.dequeue "q" with
        NONE => #()
      | SOME "fa" =>
          let: "f" := Fst "fa" in
          let: "a" := Snd "fa" in
          "f" "a"
      end.

  (** Infinite loop *)
  Definition worker : val := 
    rec: "worker" "q" :=
      run_task "q";;
      "worker" "q".

  (** Initializes a queue and Forks one worker thread *)
  Definition init : val :=
    λ: <>,
      let: "q" := Queue.init #() in
      Fork (worker "q");;
      "q".

End TaskQueue.

Section proof.
  Context `{!heapGS Σ, !queueG Σ, !ticket_lockG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pure_one := (iModIntro; lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (iModIntro; lwp_pure; post_lwp_lc n).

  (** ** Definitions *)
  Definition is_task (ℓ : ord.t) : val → oids → iProp Σ :=
    λ v B, (∃ f a m, ∀ lc i j G g K ℓt ℓg,
              ⌜(v = (f, a)%V) ∧ (ℓt < ℓ)%ordi⌝ ∧
              l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g ℓt m) ∗
                   ogP_obls j g ℓg K ∗ ⌜ B ⊆ K ⌝ }}}
                f a @ i
              l{{{ rv, RET rv; £ lc ∗ thP_groups i G ∗ ogP_obls j g ℓg (K ∖ B) }}})%I.

  (** The invariant *)
  (* The lt condition is not needed if use classical facts *)
  Definition is_task_queue (ql : val) (γ : queue_γ) (ℓ : ord.t) : iProp Σ :=
    (⌜(ord.O < ℓ)%ordi⌝) ∗ is_queue ql γ ℓ (is_task ℓ).

  (** ** Lemmas *)
  Global Instance is_task_queue_persistent ql γ ℓ : Persistent (is_task_queue ql γ ℓ).
  Proof. rewrite /is_task_queue. apply _. Qed.

  (** ** Program proofs *)
  (** FIXME: better notation for triples with this pattern *)
  Lemma TaskQueue_put_task_spec :
    ⊢ ∃ m, ∀ lc i j G g K B γ ℓ ℓ' (ql task_f task_a : val),
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g ℵ%ordi m) ∗
         ogP_obls j g ℓ' K ∗ ⌜B ⊆ K⌝ ∗ ([∗ set] b ∈ B, oblP_fuel b (ℓ ⊕ 1)%ordi 1) ∗
         is_task ℓ (task_f, task_a)%V B ∗ is_task_queue ql γ ℓ }}}
      TaskQueue.put_task ql task_f task_a @ i
    l{{{ RET #(); £ lc ∗ thP_groups i G ∗ ogP_obls j g ℓ' (K ∖ B) }}}.
  Proof.
    iPoseProof (Queue_enqueue_spec) as (m) "Queue_enqueue_spec".
    iExists (1 ⊕ m)%M. iIntros (lc i j G g K B γ ℓ ℓ' ql task_f task_a) "!> % (TG& GF& Gg& %Sub& OF& TASK& (%Hℓ& #IQ)) HΦ".
    rewrite /TaskQueue.put_task.
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF F_Queue_enqueue]".
    iMod (ogP_fuel_extend_set _ 0 _ (100)%M with "GF") as "GF".
    { unshelve etrans. 1: exact 1.
      { eapply ordArith.lt_from_nat. lia. }
      rewrite ord.from_nat_from_peano_lt. apply ord.large_lt_from_wf. }
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_pures.
    (** Queue enqueue *)
    lwp_bind (Queue.enqueue _ _).
    iModIntro. iApply ("Queue_enqueue_spec" $! 0 with "[$TG $F_Queue_enqueue $Gg $OF TASK $IQ]").
    { by iFrame. }
    iIntros "(_& TG& Gg)". iApply ("HΦ" with "[$Q_LC $TG $Gg]").
  Qed.

  Lemma TaskQueue_run_task_spec :
    ⊢ ∃ m, ∀ lc (b : bool) wi ni wg ng i j G g A γ ℓ (ql : val),
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g (ℵ ⊕ ℓ)%ordi m) ∗
         ogP_obls j g ℓ A ∗
         (if b
          then queue_worker γ wi wg ∗ ogP_obls ni ng ℓ ∅
          else True) ∗
         is_task_queue ql γ ℓ }}}
      TaskQueue.run_task ql @ i
    l{{{ rv, RET rv; £ lc ∗ thP_groups i G ∗ ogP_obls j g ℓ A ∗
                     (if b
                      then queue_worker γ ni ng ∗ ogP_obls wi wg ℓ ∅
                      else True) }}}.
  Proof.
    iPoseProof (Queue_dequeue_spec) as (m) "Queue_dequeue_spec".
    (** For internal steps, executing task, and calling dequeue *)
    iExists (1 ⊕ 1 ⊕ m)%M. iIntros (lc b wi ni wg ng i j G g A γ ℓ ql) "!> % (TG& GF& Gg& HW& (%Hℓ& #IQ)) HΦ".
    rewrite /TaskQueue.run_task.
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF F_m]".
    iPoseProof (ogP_fuel_add_set with "F_m") as "[F_task F_m]".
    iMod (ogP_fuel_extend_set _ 0 _ (100)%M with "GF") as "GF".
    { unshelve etrans. 1: exact 1.
      { eapply ordArith.lt_from_nat. lia. }
      unshelve eapply ord.lt_le_lt. 1: exact ℵ%ordi.
      { rewrite ord.from_nat_from_peano_lt. apply ord.large_lt_from_wf. }
      apply hessenberg.add_base_l. }
    assert (Hlayer : (ℵ < (ℵ ⊕ ℓ))%ordi).
    { apply hessenberg.add_lt_l; auto. }
    iMod (ogP_fuel_mon_gen_set _ ℵ%ordi _ m with "F_m") as "F_m". 1: auto.
    { apply measure_layer_le_proper. right. econstructor 1. auto. }      
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_bind (Queue.dequeue _).
    iModIntro. iApply ("Queue_dequeue_spec" $! 0 b with "[$TG $F_m $Gg $HW $IQ]").
    iIntros (x B) "(_& TG& Gg& %Hdisj& Hx& HW)". destruct x. 1,2,3: iPoseProof "Hx" as "%HF"; inversion HF.

    TODO


    lwp_pure.


    (** Need ql *)
    iDestruct "IQ" as "(%&%&%& %Hql& #IQ& #IFL)". simplify_eq.
    lwp_pures.
    (** Acquire lock *)
    lwp_bind (TicketLock.acquire tl).
    iModIntro.
    iApply ("TicketLock_acquire_spec" $! 0 (100 ⊕ mr)%M with "[$TG F_ma $IFL]").
    { iApply ogP_fuel_layer_eq_set. 2: iFrame. by rewrite hessenberg.add_O_l. }
    iIntros (gu ku) "(_& %Ningu& TG& Ggu& F_gu& F_ku& _& Lock& R)".
    iPoseProof (ogP_fuel_add with "F_gu") as "[F_gu F_mr_gu]".
    (* Prepare fuels for the unlock call. *)
    iMod (ogP_fuel_mon_gen_set _ 0 _ (mr)%M with "F_mr") as "F_mr".
    { right. unshelve etrans. 1: exact 1.
      { eapply ordArith.lt_from_nat. lia. }
      rewrite ord.from_nat_from_peano_lt. apply ord.large_lt_from_wf. }
    { apply measure_layer_le_proper. right. econstructor 1.
      unshelve etrans. 1: exact 1.
      { eapply ordArith.lt_from_nat. lia. }
      rewrite ord.from_nat_from_peano_lt. apply ord.large_lt_from_wf. }
    iPoseProof (big_sepS_union _ {[gu]} G with "[$F_mr F_mr_gu]") as "F_mr". 1: set_solver.
    { iApply big_sepS_singleton. auto. }
    rewrite (ogP_fuel_eq gu 0 _ (96 ⊕ 4)%M); cycle 1.
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add with "F_gu") as "[F_gu _]".
    iPoseProof (big_sepS_union _ {[gu]} G with "[$GF F_gu]") as "GF". 1: set_solver.
    { iApply big_sepS_singleton. auto. }
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (ogP_fuel_eq_set _ 0 _ (89 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    iDestruct "R" as "(%&%&%& Ptr_lh& Ptr_lt& Queue& QC)".    
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $Ptr_lh]"). 1: done.
    iIntros "((_& TG& _)& Ptr_lh)".
    lwp_pure_lc 100.
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (ogP_fuel_eq_set _ 0 _ (86 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    destruct vs as [ | [v B] vs'].
    - (* Queue is empty *)
      iDestruct "QC" as "(%Heq& QC_Ptr_lh)". subst lt.
      iModIntro.
      iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $QC_Ptr_lh]"). 1: done.
      iIntros "((_& TG& _)& QC_Ptr_lh)".
      lwp_pures.
      lwp_bind (TicketLock.release tl).
      iMod (inv_acc with "IQ") as "[qinv IQ_ACC]". 1: set_solver.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_lwpupd_add_later with "LC1"). iNext.
      iDestruct "qinv" as "(%&%&%& Queue0& Gvar& %Disj& Gq& Fq)".
      iPoseProof (own_valid_2 with "Queue Queue0") as "%".
      apply dfrac_agree_op_valid in H. destruct H as [_ ?]. apply leibniz_equiv in H. subst vs.
      iAssert (|={⊤ ∖ ↑Ni,⊤}=> if b then queue_worker γ ni ng ∗ ogP_obls wi wg ℓ ∅ else True)%I
        with "[IQ_ACC Queue0 Gvar Gq Fq HW]" as "IQ_ACC".
      { destruct b.
        - iDestruct "HW" as "(Gw& Gq1)". iPoseProof (ghost_var_agree with "Gvar Gw") as "%". simplify_eq.
          simpl. iMod (ghost_var_update_2 (ni, ng) with "Gvar Gw") as "[Gvar Gw]". 1: by rewrite Qp.div_2.
          iFrame "Gw Gq". iApply "IQ_ACC". iNext. iFrame. simpl. iFrame. iPureIntro. auto.
        - iApply "IQ_ACC". iNext. iFrame. iPureIntro. auto. }
      iModIntro. iMod "IQ_ACC" as "HW".
      iModIntro.
      iApply ("TicketLock_release_spec" with "[$TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC_Ptr_lh]").
      { iSplit. 1: iPureIntro; set_solver. iFrame. simpl. by iFrame. }
      (* FIXME: it would be nice if we don't get this evar *)
      Unshelve. 2: exact 0.
      iIntros "(_& TG& Ggu& _)".
      replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
      iMod (group_delete with "TG Ggu") as "TG". replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
      iPoseProof (big_sepS_union _ {[gu]} G with "GF") as "[_ GF]". 1: set_solver.
      lwp_pures.
      iModIntro. lwp_finish.
      iApply ("HΦ" $! _ ∅). rewrite union_empty_r_L. iFrame. by iModIntro.
    - simpl. iDestruct "QC" as "(%ln& QC_Ptr_lh& Hφ& QC)".
      iModIntro.
      iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $QC_Ptr_lh]"). 1: done.
      iIntros "((_& TG& _)& QC_Ptr_lh)".
      lwp_pures.
      lwp_bind (Store _ _).
      iModIntro.
      iPoseProof (ogP_fuel_eq_set _ 0 _ (79 ⊕ 1)%M with "GF") as "GF".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
      iApply (lwp_store _ ∅ 0 with "[$TG $GF1 $Ptr_lh]"). 1: done.
      iIntros "((_& TG& _)& Ptr_lh)".
      lwp_pures.
      lwp_bind (Free _).
      iModIntro.
      iPoseProof (ogP_fuel_eq_set _ 0 _ (76 ⊕ 1)%M with "GF") as "GF".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
      iApply (lwp_free _ ∅ 0 with "[$TG $GF1 $QC_Ptr_lh]"). 1: done.
      iIntros "(_& TG& _)".
      lwp_pures.
      lwp_bind (TicketLock.release tl).
      iMod (inv_acc with "IQ") as "[qinv IQ_ACC]". 1: set_solver.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_lwpupd_add_later with "LC1"). iNext.
      iDestruct "qinv" as "(%&%&%& Queue0& Gvar& %Disj& Gq& Fq)".
      iPoseProof (own_valid_2 with "Queue Queue0") as "%".
      apply dfrac_agree_op_valid in H. destruct H as [_ ?]. apply leibniz_equiv in H. subst vs.
      iMod (own_update_2 with "Queue Queue0") as "[Queue Queue0]".
      { eapply (dfrac_agree_update_2 _ _ _ _ (vs')). rewrite dfrac_op_own Qp.div_2. auto. }
      iAssert (|={⊤ ∖ ↑Ni}=>m |={⊤ ∖ ↑Ni,⊤}=> ogP_obls j g ℓ (A ∪ B) ∗ (if b then queue_worker γ ni ng ∗ ogP_obls wi wg ℓ ∅ else True))%I
        with "[IQ_ACC Queue0 Gvar Gq Fq HW Gg]" as "IQ_ACC".
      { destruct b.
        - iDestruct "HW" as "(Gw& Gq1)". iPoseProof (ghost_var_agree with "Gvar Gw") as "%". simplify_eq.
          rewrite !fmap_cons. iPoseProof (big_sepL_cons with "Fq") as "[FB Fq]".
          simpl.
          iAssert (([∗ list] k↦y ∈ vs'.*2, [∗ set] b ∈ y, oblP_fuel b ℓ (S k)) ∗
                   ([∗ list] k↦y ∈ vs'.*2, [∗ set] b ∈ y, oblP_fuel b ℓ 1))%I
            with "[Fq]" as "[Fq F]".
          { iApply big_sepL_sep. iApply (big_sepL_impl with "Fq"). iIntros "!> %% % H".
            iPoseProof (oblP_fuel_eq_set _ _ _ ((S k) ⊕ 1)%M with "H") as "H".
            { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat.
              replace (S (S k)) with (S k + 1) by lia. done. }
            iApply (oblP_fuel_add_set with "H"). }
          iMod (obl_offload_set with "Gq Gg FB") as "(Gq& Gg& %)". 1: set_solver. 1: by left.
          assert (B ## union_list_of_sets vs'.*2 ∧ disjoint_list_of_sets vs'.*2).
          { rewrite fmap_cons in Disj. apply disjoint_list_of_sets_cons_inv in Disj. auto. }
          destruct H0 as (DisjB& Disj').
          replace ((B ∪ union_list_of_sets vs'.*2) ∖ B) with (union_list_of_sets vs'.*2) by set_solver.
          iMod (ghost_var_update_2 (ni, ng) with "Gvar Gw") as "[Gvar Gw]". 1: by rewrite Qp.div_2.
          iAssert ([∗ set] b ∈ union_list_of_sets vs'.*2, oblP_fuel b ℓ 1)%I with "[F]" as "F".
          { iClear "TicketLock_acquire_spec TicketLock_release_spec IQ IFL".
            remember (vs'.*2) as l. clear dependent vs'. clear DisjB Disj'. iInduction l as [ | ]. 1: done.
            iPoseProof (big_sepL_cons with "F") as "[Fb F]".
            iPoseProof ("IHl" with "F") as "F".
            rewrite union_list_of_sets_cons. iApply (big_sepS_union_2 with "Fb F"). }
          iMod (obl_offload_set with "Gq Gq1 F") as "(Gq& Gq1& %)". 1: set_solver. 1: by left.
          replace (union_list_of_sets vs'.*2 ∖ union_list_of_sets vs'.*2) with (∅ : oids) by set_solver.
          rewrite union_empty_l_L. iFrame "Gg Gw Gq". iModIntro. iApply "IQ_ACC". iNext. iFrame. auto.
        - iClear "HW".
          rewrite !fmap_cons. iPoseProof (big_sepL_cons with "Fq") as "[FB Fq]".
          simpl.
          iAssert (([∗ list] k↦y ∈ vs'.*2, [∗ set] b ∈ y, oblP_fuel b ℓ (S k)) ∗
                   ([∗ list] k↦y ∈ vs'.*2, [∗ set] b ∈ y, oblP_fuel b ℓ 1))%I
            with "[Fq]" as "[Fq F]".
          { iApply big_sepL_sep. iApply (big_sepL_impl with "Fq"). iIntros "!> %% % H".
            iPoseProof (oblP_fuel_eq_set _ _ _ ((S k) ⊕ 1)%M with "H") as "H".
            { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat.
              replace (S (S k)) with (S k + 1) by lia. done. }
            iApply (oblP_fuel_add_set with "H"). }
          iMod (obl_offload_set with "Gq Gg FB") as "(Gq& Gg& %)". 1: set_solver. 1: by left.
          assert (B ## union_list_of_sets vs'.*2 ∧ disjoint_list_of_sets vs'.*2).
          { rewrite fmap_cons in Disj. apply disjoint_list_of_sets_cons_inv in Disj. auto. }
          destruct H0 as (DisjB& Disj').
          replace ((B ∪ union_list_of_sets vs'.*2) ∖ B) with (union_list_of_sets vs'.*2) by set_solver.
          iFrame "Gg". iModIntro. iApply "IQ_ACC". iNext. iFrame. auto. }
      iMod "IQ_ACC". iModIntro. iMod "IQ_ACC" as "HW".
      iModIntro.
      iApply ("TicketLock_release_spec" with "[$TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC]").
      { iSplit. 1: iPureIntro; set_solver. iFrame. }
      (* FIXME: it would be nice if we don't get this evar *)
      Unshelve. 2: exact 0.
      iIntros "(_& TG& Ggu& _)".
      replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
      iMod (group_delete with "TG Ggu") as "TG". replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
      iPoseProof (big_sepS_union _ {[gu]} G with "GF") as "[_ GF]". 1: set_solver.
      lwp_pures.
      iModIntro. lwp_finish.
      iApply "HΦ". iDestruct "HW" as "(Gg& HW)". iFrame. by iModIntro.
  Qed.

End proof.
