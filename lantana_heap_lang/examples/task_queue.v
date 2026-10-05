From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Export queue handoff.
From lantana.heap_lang.examples Require Import step_tactics.

(** * A task queue: a queue of tasks [f a] (as in the handoff), run by a forked worker thread *)

Module TaskQueue.

  Definition put_task : val :=
    λ: "q" "f" "a",
      Queue.enqueue "q" ("f", "a").

  Definition run_task : val :=
    λ: "q",
      match: Queue.dequeue "q" with
        NONE => #()
      | SOME "fa" =>
          (Fst "fa") (Snd "fa")
      end.

  Definition worker : val :=
    rec: "loop" "q" :=
      run_task "q";;
      "loop" "q".

  Definition init : val :=
    λ: <>,
      let: "q" := Queue.init #() in
      Fork (worker "q");;
      "q".

End TaskQueue.

Section proof.
  Context `{!heapGS Σ, !queueG Σ, !ticket_lockG Σ}.

  (** ** Definitions *)
  Definition is_task_queue (ql : val) (γ : queue_γ) (ℓ : ord.t) : iProp Σ :=
    is_queue ql γ ℓ (λ v B, ∃ f a, ⌜(v = (f, a)%V)⌝ ∗ is_task ℓ f a B)%I.

  (** ** Lemmas *)
  Global Instance is_task_queue_persistent ql γ ℓ : Persistent (is_task_queue ql γ ℓ).
  Proof. rewrite /is_task_queue. apply _. Qed.

  (** ** Program proofs *)
  Lemma TaskQueue_put_task_spec :
    ⊢ ∃ μ, ∀ lc i G p K B γ ℓ (ql task_f task_a : val) C,
    l{{{ thread_expr i C (TaskQueue.put_task ql task_f task_a) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 1%ordi μ) ∗
         parP_kids p K ∗ ⌜B ⊆ K⌝ ∗ ([∗ set] b ∈ B, oblP_fuel b (ℓ ⊕ 2)%ordi 1) ∗
         is_task ℓ task_f task_a B ∗ is_task_queue ql γ ℓ }}}
      TaskQueue.put_task ql task_f task_a @ i
    l{{{ RET #(); thread_expr i C (#()) ∗ £ lc ∗ thP_kids i G ∗ parP_kids p (K ∖ B) }}}.
  Proof.
    iPoseProof (Queue_enqueue_spec) as (m) "Queue_enqueue_spec".
    iExists (100 ⊕ m)%M. iIntros (lc i G p K B γ ℓ ql task_f task_a C) "!> % (TE& TG& GF& Gg& %Sub& OF& TASK& (%Hℓ& #IQ)) HΦ".
    rewrite /TaskQueue.put_task.
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF F_Queue_enqueue]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC TE".
    lwp_pures.
    lwp_bind (Queue.enqueue _ _).
    iModIntro. iApply ("Queue_enqueue_spec" $! 0 with "[$TE $TG $F_Queue_enqueue $Gg $OF TASK $IQ]").
    { by iFrame. }
    iIntros "(TE& _& TG& Gg)". iApply ("HΦ" with "[$TE $Q_LC $TG $Gg]").
  Qed.

  Lemma TaskQueue_run_task_spec :
    ⊢ ∃ μ, ∀ lc m (b : bool) wg i G γ ℓ (ql : val) C,
    l{{{ thread_expr i C (TaskQueue.run_task ql) ∗ thP_kids i G ∗
         (* For dequeue *)
         ([∗ set] g ∈ G, oblP_fuel g (1)%ordi μ) ∗
         (* For task *)
         ([∗ set] g ∈ G, oblP_fuel g (ℓ)%ordi 1) ∗
         (if b
          then queue_worker γ wg
          else True) ∗
         is_task_queue ql γ ℓ }}}
      TaskQueue.run_task ql @ i
      l{{{ rv, RET rv; thread_expr i C (of_val rv) ∗ £ lc ∗
                       (if b
                        then (∃ ng, thP_kids i ({[ng]} ∪ G) ∗ ⌜ng ∉ G⌝ ∗
                                    queue_worker γ ng ∗ oblP_kids wg ∅ ∗ oblP_assigned wg 1 ∗ oblP_fuel ng ℓ m)
                        else (thP_kids i G)) }}}.
  Proof.
    iPoseProof (Queue_dequeue_spec) as (m) "Queue_dequeue_spec".
    (** For internal steps and calling dequeue *)
    iExists (100 ⊕ m)%M. iIntros (lc μ b wg i G γ ℓ ql C) "!> % (TE& TG& GF& F_task& HW& #ITQ) HΦ".
    (* To make some iFrame faster *)
    unfold is_task_queue.
    rewrite /TaskQueue.run_task.
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF F_m]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC TE".
    lwp_bind (Queue.dequeue _).
    iModIntro. iApply ("Queue_dequeue_spec" $! 0 (μ ⊕ 100)%M b with "[$TE $TG $F_m $HW $ITQ]").
    iIntros (x) "(TE& _& Hx)".
    iAssert (⌜x = NONEV ∨ ∃ v, x = SOMEV v⌝)%I as "%Hcase".
    { destruct x; eauto. destruct x; auto. destruct l; auto. }
    destruct Hcase as [Hcase | Hcase].
    - subst x. destruct b.
      + iDestruct "Hx" as "(%& TG& %Ninng& Hw& Gwg& Awg& Fng)".
        iPoseProof (oblP_fuel_add with "Fng") as "[Fng Fng']".
        iPoseProof (oblP_fuel_add_nat 99 1 with "Fng'") as "[Fng' _]". 1: lia.
        iPoseProof (oblP_fuels_add_obl with "Fng' GF") as "GF".
        lwp_pures.
        iModIntro. lwp_finish. iModIntro.
        iApply "HΦ". iFrame. iPureIntro. auto.
      + iRename "Hx" into "TG".
        lwp_pures.
        iModIntro. lwp_finish. iModIntro.
        iApply "HΦ". iFrame.
    - destruct Hcase as (v& Hcase). subst x.
      iDestruct "Hx" as "(%&%& Htask& Gg& Ag& Fg& %Ning& HW)".
      iDestruct "Htask" as "(%&%&%& (%&%& %Htask& HP& %mt& TASK))".
      iPoseProof (oblP_fuel_add with "Fg") as "[_ Fg]".
      iPoseProof (oblP_fuel_add_nat 99 1 with "Fg") as "[Fg' Fg]". 1: lia.
      iPoseProof (oblP_fuels_add_obl with "Fg' GF") as "GF".
      iPoseProof (big_sepS_union _ {[g]} G with "[Fg $F_task]") as "F_task". 1: set_solver.
      { iApply big_sepS_singleton. iFrame. }
      destruct b.
      + iDestruct "HW" as "(%& TG& %HG& Qw& Gwg& Awg& Fng)". destruct HG as (Ninng& Neq).
        iPoseProof (oblP_fuel_add with "Fng") as "[Fng_Q Fng]".
        iPoseProof (oblP_fuel_add_nat 99 1 with "Fng") as "[Fng' Fng]". 1: lia.
        iPoseProof (oblP_fuels_add_obl with "Fng' GF") as "GF".
        iPoseProof (big_sepS_union _ {[ng]} ({[g]} ∪ G) with "[Fng $F_task]") as "F_task". 1: set_solver.
        { iApply big_sepS_singleton. iFrame. }
        replace ({[ng]} ∪ ({[g]} ∪ G)) with ({[g; ng]} ∪ G) by set_solver.
        subst v.
        lwp_pures.
        lwp_bind (f a).
        iMod (oblP_fuel_extend_set _ ℓt _ mt with "F_task") as "F_task".
        { eapply ord.lt_le_lt. 1: eauto. done. }
        iModIntro.
        iApply lwp_sfmupd.
        iApply ("TASK" $! 0 with "[$TE $TG $F_task $Gg $HP]").
        { iPureIntro. set_solver. }
        iIntros (?) "(TE& _& TG& Gg)". replace (B ∖ B) with (∅ : oids) by set_solver.
        iMod (obl_discharge_leaf with "TG Gg Ag") as "[TG _]". 1: set_solver.
        replace (({[g; ng]} ∪ G) ∖ {[g]}) with ({[ng]} ∪ G) by set_solver.
        iModIntro. iApply "HΦ". iFrame "TE Q_LC". iExists ng. iFrame. iPureIntro. set_solver.
      + iRename "HW" into "TG".
        subst v.
        lwp_pures.
        lwp_bind (f a).
        iMod (oblP_fuel_extend_set _ ℓt _ mt with "F_task") as "F_task".
        { eapply ord.lt_le_lt. 1: eauto. done. }
        iModIntro.
        iApply lwp_sfmupd.
        iApply ("TASK" $! 0 with "[$TE $TG $F_task $Gg $HP]").
        { iPureIntro. set_solver. }
        iIntros (?) "(TE& _& TG& Gg)". replace (B ∖ B) with (∅ : oids) by set_solver.
        iMod (obl_discharge_leaf with "TG Gg Ag") as "[TG _]". 1: set_solver.
        replace (({[g]} ∪ G) ∖ {[g]}) with G by set_solver.
        iModIntro. iApply "HΦ". iFrame.
  Qed.

  Lemma TaskQueue_worker_spec :
    ⊢ ∃ μ, ∀ (b : bool) i G γ ℓ (ql : val) C,
    l{{{ thread_expr i C (TaskQueue.worker ql) ∗ thP_kids i G ∗
         (if b
          then (∃ g, ⌜G = {[g]} ∧ (1 <= ℓ)%ordi⌝ ∧ (oblP_fuel g (ℓ)%ordi μ) ∗ queue_worker γ g)
          else (⌜G = ∅⌝)) ∗
         is_task_queue ql γ ℓ }}}
      TaskQueue.worker ql @ i
      l{{{ RET #(); False }}}.
  Proof.
    iPoseProof (TaskQueue_run_task_spec) as (mr) "TaskQueue_run_task_spec".
    (** For internal steps and executing [run_task] *)
    iExists (100 ⊕ mr ⊕ 1)%M. iIntros (b i G γ ℓ ql C) "!> % (TE& TG& HW& #ITQ) HΦ".
    iClear "HΦ".
    rewrite /TaskQueue.worker.
    destruct b.
    - iDestruct "HW" as "(%& %& GF& Qw)". destruct H as (->& Hlayer).
      iAssert ([∗ set] g ∈ {[g]}, oblP_fuel g (ℓ)%ordi _)%I with "[GF]" as "GF".
      { iApply big_sepS_singleton. iFrame. }
      iPoseProof (oblP_fuel_add_set with "GF") as "[GF F_mr]".
      iPoseProof (oblP_fuels_init with "GF") as "GF".
      (** Löb induction *)
      iRevert (g) "Qw F_mr TG GF TE". iLöb as "IH". iIntros (g) "HW F_mr TG GF TE".
      lwp_pure. simpl.
      iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
      lwp_bind (TaskQueue.run_task _).
      iPoseProof (oblP_fuel_add_set with "F_mr") as "[F_mr F_mr1]".
      iMod (oblP_fuel_mon_gen_set _ 1%ordi _ mr with "F_mr") as "F_mr". 1: auto.
      { by apply measure_rep_layer_le. }
      iModIntro.
      iApply ("TaskQueue_run_task_spec" $! 100 (102 ⊕ (mr ⊕ 1))%M true with "[$TE $TG $F_mr $F_mr1 $HW $ITQ]").
      iIntros (rv) "(TE& LC& (%& TG& %Ninng& Qw& Gg& Ag& Fng))".
      iMod (obl_discharge_leaf with "TG Gg Ag") as "[TG _]". 1: set_solver.
      replace ({[ng; g]} ∖ {[g]}) with ({[ng]} : gset oid) by set_solver.
      iClear "GF".
      iAssert (([∗ set] k ∈ {[ng]}, oblP_fuel k ℓ (102 ⊕ (mr ⊕ 1))%M))%I with "[Fng]" as "GF".
      { iApply big_sepS_singleton. iFrame. }
      iPoseProof (oblP_fuel_add_set with "GF") as "[GF F_mr]".
      iPoseProof (oblP_fuels_init with "GF") as "GF".
      do 2 (iModIntro; lwp_pure_one).
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      iModIntro. iApply ("IH" with "Qw F_mr TG GF TE").
    - iDestruct "HW" as "%". subst G.
      (** Löb induction *)
      iRevert "TG TE". iLöb as "IH". iIntros "TG TE".
      iAssert ([∗ set] g ∈ ∅, oblP_fuel g 0 100)%I as "GF''". 1: done.
      iPoseProof (oblP_fuels_init with "GF''") as "GF'".
      lwp_pure. simpl.
      iFrame "TG GF'". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
      iClear "GF' GF''".
      lwp_bind (TaskQueue.run_task _).
      iModIntro.
      iApply ("TaskQueue_run_task_spec" $! 100 (100 ⊕ (mr ⊕ 1))%M false 1%positive with "[$TE $TG $ITQ]").
      1: iSplit; done.
      iIntros (rv) "(TE& LC& TG)".
      iClear "GF".
      iAssert ([∗ set] g ∈ ∅, oblP_fuel g 0 100)%I as "GF''". 1: done.
      iPoseProof (oblP_fuels_init with "GF''") as "GF'".
      iModIntro. lwp_pure. simpl.
      iFrame "TG GF'". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
      iClear "GF' GF''".
      do 1 (iModIntro; lwp_pure_one).
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      iApply ("IH" with "TG TE").
  Qed.

  Lemma TaskQueue_init_spec :
    ⊢ ∃ μ, ∀ (lc : Ord.t) i G ℓ C,
    l{{{ thread_expr i C (TaskQueue.init #()) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) ∗ ⌜(1 <= ℓ)%ordi⌝ }}}
      TaskQueue.init #() @ i
    l{{{ ql γ, RET ql; thread_expr i C (of_val ql) ∗ £ lc ∗ thP_kids i G ∗ is_task_queue ql γ ℓ }}}.
  Proof.
    iPoseProof (Queue_init_spec) as (mqi) "Queue_init_spec".
    iPoseProof (TaskQueue_worker_spec) as (mtw) "TaskQueue_worker_spec".
    (** For internal steps and function calls *)
    iExists (100%nat ⊕ mqi)%M. iIntros (lc i G ℓ C) "!> % (TE& TG& GF& %Hlayer) HΦ".
    rewrite /TaskQueue.init.
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF GF_qi]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC TE".
    lwp_bind (Queue.init _).
    iModIntro.
    iApply ("Queue_init_spec" $! 0 (λ v B, ∃ f a, ⌜(v = (f, a)%V)⌝ ∗ is_task ℓ f a B)%I with "[$TE $TG $GF_qi]").
    iIntros (??) "(TE& _& TG& IQI)".
    lwp_pures.
    lwp_bind (Fork _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_fork_step). iModIntro. iFrame "TE TG GF1". iExists ∅. iSplitR; first done.
    iIntros (?) "TE TEj TG _ TGj !>". iModIntro.
    iMod (obl_new _ (PThread _) _ ℓ mtw with "[] TGj") as "(%& %Ning& TGj& Gg& Ag& Fg& #Wg)".
    { iApply parP_le_thread. }
    iMod (is_queue_initialize with "IQI Gg Wg Ag") as "[#IQ Qw]".
    iModIntro. iSplitR "TEj TGj Fg Qw".
    - iModIntro. lwp_pures.
      iModIntro. lwp_finish.
      rewrite /is_task_queue. iApply ("HΦ" with "[$TE $Q_LC $TG $IQ]").
    - rewrite /is_task_queue.
      iApply ("TaskQueue_worker_spec" $! true with "[$TEj $TGj $Fg $Qw $IQ]").
      { iPureIntro. split; auto. set_solver. }
      iIntros "%". done.
  Qed.

  (** ** Temporal guarantees *)
  (** A task queue guarantees what its queue does: the tasks ([is_task]) are Hoare triples
      with ghost resources, guaranteeing [tps_true]. That every task runs is expressed by
      obligations. *)
  Definition task_queue_tps (ql : val) : tps heap_lang Σ := queue_tps ql.

  Lemma is_task_queue_temporal ql γ ℓ : ⊢ is_task_queue ql γ ℓ ⊨ₜ task_queue_tps ql.
  Proof. rewrite /is_task_queue /task_queue_tps. apply (into_temporal _ _). Qed.

  Global Instance is_task_queue_into_temporal ql γ ℓ :
    IntoTemporal (is_task_queue ql γ ℓ) (task_queue_tps ql) | 0.
  Proof. apply is_task_queue_temporal. Qed.

End proof.

(** ** Progress of the task queue's lock, at the level of traces *)
Section trace.

  (** Every [put_task] or [run_task] that takes the queue's lock eventually releases it. *)
  Lemma task_queue_release_progress {Σ} ql τ :
    tps_tr (task_queue_tps (Σ:=Σ) ql) τ →
    ∃ lhptr ltptr next curr : loc,
      ql = (#lhptr, #ltptr, (#next, #curr))%V ∧ release_progress next curr τ.
  Proof. apply queue_release_progress. Qed.

End trace.
