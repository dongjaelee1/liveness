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
    λ: "q",
      (rec: "while" <> :=
         run_task "q";;
         "while" #()) #().

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
    λ v B, (∃ f a ℓt (P : iProp Σ) m,
               ⌜(v = (f, a)%V) ∧ (ℓt < ℓ)%ordi⌝ ∧
               P ∗
               ∀ lc i j G g K ℓg,
               l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, grP_fuel g ℓt m) ∗
                    grP_obls j g ℓg K ∗ ⌜ B ⊆ K ⌝ ∗ P }}}
                f a @ i
              l{{{ rv, RET rv; £ lc ∗ thP_groups i G ∗ grP_obls j g ℓg (K ∖ B) }}})%I.

  (** The invariant *)
  Definition is_task_queue (ql : val) (γ : queue_γ) (ℓ : ord.t) : iProp Σ :=
    is_queue ql γ ℓ (is_task ℓ).

  (** ** Lemmas *)
  Global Instance is_task_queue_persistent ql γ ℓ : Persistent (is_task_queue ql γ ℓ).
  Proof. rewrite /is_task_queue. apply _. Qed.

  (** ** Program proofs *)
  (** FIXME: better notation for triples with this pattern *)
  Lemma TaskQueue_put_task_spec :
    ⊢ ∃ m, ∀ lc i j G g K B γ ℓ ℓg (ql task_f task_a : val),
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, grP_fuel g ℵ%ordi m) ∗
         grP_obls j g ℓg K ∗ ⌜B ⊆ K⌝ ∗ ([∗ set] b ∈ B, oblP_fuel b (ℓ ⊕ 1)%ordi 1) ∗
         is_task ℓ (task_f, task_a)%V B ∗ is_task_queue ql γ ℓ }}}
      TaskQueue.put_task ql task_f task_a @ i
    l{{{ RET #(); £ lc ∗ thP_groups i G ∗ grP_obls j g ℓg (K ∖ B) }}}.
  Proof.
    iPoseProof (Queue_enqueue_spec) as (m) "Queue_enqueue_spec".
    iExists (100 ⊕ m)%M. iIntros (lc i j G g K B γ ℓ ℓg ql task_f task_a) "!> % (TG& GF& Gg& %Sub& OF& TASK& (%Hℓ& #IQ)) HΦ".
    rewrite /TaskQueue.put_task.
    iPoseProof (grP_fuel_add_set with "GF") as "[GF F_Queue_enqueue]".
    iPoseProof (grP_fuels_init with "GF") as "GF".
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
    ⊢ ∃ m, ∀ lc μ (b : bool) wi wg i G γ ℓ (ql : val),
    l{{{ thP_groups i G ∗
         (* For dequeue *)
         ([∗ set] g ∈ G, grP_fuel g (ℵ)%ordi m) ∗
         (* For task *)
         ([∗ set] g ∈ G, grP_fuel g (ℓ)%ordi 1) ∗
         (if b
          then queue_worker γ wi wg
          else True) ∗
         is_task_queue ql γ ℓ }}}
      TaskQueue.run_task ql @ i
      l{{{ rv, RET rv; £ lc ∗
                       (if b
                        then (∃ ng, thP_groups i ({[ng]} ∪ G) ∗ ⌜ng ∉ G⌝ ∗
                                    queue_worker γ i ng ∗ grP_obls wi wg ℓ ∅ ∗ grP_fuel ng ℓ μ)
                        else (thP_groups i G)) }}}.
  Proof.
    iPoseProof (Queue_dequeue_spec) as (m) "Queue_dequeue_spec".
    (** For internal steps and calling dequeue *)
    iExists (100 ⊕ m)%M. iIntros (lc μ b wi wg i G γ ℓ ql) "!> % (TG& GF& F_task& HW& #ITQ) HΦ".
    (* To make some iFrame faster *)
    unfold is_task_queue.
    rewrite /TaskQueue.run_task.
    iPoseProof (grP_fuel_add_set with "GF") as "[GF F_m]".
    iPoseProof (grP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_bind (Queue.dequeue _).
    iModIntro. iApply ("Queue_dequeue_spec" $! 0 (μ ⊕ 100)%M b with "[$TG $F_m $HW $ITQ]").
    iIntros (x) "(_& Hx)".
    iAssert (⌜x = NONEV ∨ ∃ v, x = SOMEV v⌝)%I as "%Hcase".
    { destruct x; eauto. destruct x; auto. destruct l; auto. }
    destruct Hcase as [Hcase | Hcase].
    - subst x. destruct b.
      + iDestruct "Hx" as "(%& TG& %Ninng& Hw& Gwg& Fng)".
        iPoseProof (grP_fuel_add with "Fng") as "[Fng Fng']".
        iPoseProof (grP_fuel_add_nat 99 1 with "Fng'") as "[Fng' _]". 1: lia.
        iPoseProof (grP_fuels_add_group with "Fng' GF") as "GF".
        lwp_pures.
        iModIntro. lwp_finish. iModIntro.
        iApply "HΦ". iFrame. iPureIntro. auto.
      + iRename "Hx" into "TG".
        lwp_pures.
        iModIntro. lwp_finish. iModIntro.
        iApply "HΦ". iFrame.
    - destruct Hcase as (v& Hcase). subst x.
      iDestruct "Hx" as "(%&%& Htask& Gg& Fg& %Ning& HW)".
      iDestruct "Htask" as "(%&%&%&%&%mt& %Htask& HP& TASK)".
      iPoseProof (grP_fuel_add with "Fg") as "[_ Fg]".
      iPoseProof (grP_fuel_add_nat 99 1 with "Fg") as "[Fg' Fg]". 1: lia.
      iPoseProof (grP_fuels_add_group with "Fg' GF") as "GF".
      iPoseProof (big_sepS_union _ {[g]} with "[Fg $F_task]") as "F_task". 1: set_solver.
      { iApply big_sepS_singleton. iFrame. }
      destruct b.
      + iDestruct "HW" as "(%& TG& %HG& Qw& Gwg& Fng)". destruct HG as (Ninng& Neq).
        iPoseProof (grP_fuel_add with "Fng") as "[Fng_Q Fng]".
        iPoseProof (grP_fuel_add_nat 99 1 with "Fng") as "[Fng' Fng]". 1: lia.
        iPoseProof (grP_fuels_add_group with "Fng' GF") as "GF".
        iPoseProof (big_sepS_union _ {[ng]} with "[Fng $F_task]") as "F_task". 1: set_solver.
        { iApply big_sepS_singleton. iFrame. }
        replace ({[ng]} ∪ ({[g]} ∪ G)) with ({[g; ng]} ∪ G) by set_solver.
        destruct Htask as (->& Hltask).
        lwp_pures.
        lwp_bind (f a).
        iMod (grP_fuel_extend_set _ ℓt _ mt with "F_task") as "F_task".
        { eapply ord.lt_le_lt. 1: eauto. done. }
        iModIntro.
        iApply lwp_sfmupd.
        iApply ("TASK" $! 0 with "[$TG $F_task $Gg $HP]").
        { iPureIntro. set_solver. }
        iIntros (?) "(_& TG& Gg)". replace (B ∖ B) with (∅ : oids) by set_solver.
        iMod (group_delete with "TG Gg") as "TG". replace (({[g; ng]} ∪ G) ∖ {[g]}) with ({[ng]} ∪ G) by set_solver.
        iModIntro. iApply "HΦ". iFrame "Q_LC". iExists ng. iFrame. iPureIntro. set_solver.
      + iRename "HW" into "TG".
        destruct Htask as (->& Hltask).
        lwp_pures.
        lwp_bind (f a).
        iMod (grP_fuel_extend_set _ ℓt _ mt with "F_task") as "F_task".
        { eapply ord.lt_le_lt. 1: eauto. done. }
        iModIntro.
        iApply lwp_sfmupd.
        iApply ("TASK" $! 0 with "[$TG $F_task $Gg $HP]").
        { iPureIntro. set_solver. }
        iIntros (?) "(_& TG& Gg)". replace (B ∖ B) with (∅ : oids) by set_solver.
        iMod (group_delete with "TG Gg") as "TG". replace (({[g]} ∪ G) ∖ {[g]}) with G by set_solver.
        iModIntro. iApply "HΦ". iFrame.
  Qed.

  Lemma TaskQueue_worker_spec :
    ⊢ ∃ m, ∀ (b : bool) i G γ ℓ (ql : val),
    l{{{ thP_groups i G ∗
         (if b
          then (∃ g, ⌜G = {[g]} ∧ (ℵ <= ℓ)%ordi⌝ ∧ (grP_fuel g (ℓ)%ordi m) ∗ queue_worker γ i g)
          (* then (∃ g, ([∗ set] g ∈ G, grP_fuel g (ℓ)%ordi m) ∗ queue_worker γ i g ∗ ⌜G = {[g]} ∧ (ℵ <= ℓ)%ordi⌝) *)
          else (⌜G = ∅⌝)) ∗
         is_task_queue ql γ ℓ }}}
      TaskQueue.worker ql @ i
      l{{{ RET #(); False }}}.
  Proof.
    iPoseProof (TaskQueue_run_task_spec) as (mr) "TaskQueue_run_task_spec".
    (** For internal steps and executing run_task *)
    iExists (100 ⊕ mr ⊕ 1)%M. iIntros (b i G γ ℓ ql) "!> % (TG& HW& #ITQ) HΦ".
    iClear "HΦ".
    rewrite /TaskQueue.worker.
    destruct b.
    - iDestruct "HW" as "(%& %& GF& Qw)". destruct H as (->& Hlayer).
      iAssert ([∗ set] g ∈ {[g]}, grP_fuel g (ℓ)%ordi _)%I with "[GF]" as "GF".
      { iApply big_sepS_singleton. iFrame. }
      iPoseProof (grP_fuel_add_set with "GF") as "[GF F_mr]".
      iPoseProof (grP_fuels_init with "GF") as "GF".
      lwp_pure. simpl.
      iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _".
      lwp_pure_one.
      (** Lob (co-)induction *)
      iRevert (g) "Qw F_mr TG GF". iLöb as "IH". iIntros (g) "HW F_mr TG GF".
      lwp_pures.
      lwp_bind (TaskQueue.run_task _).
      iPoseProof (grP_fuel_add_set with "F_mr") as "[F_mr F_mr1]".
      iMod (grP_fuel_mon_gen_set _ ℵ%ordi _ mr with "F_mr") as "F_mr". 1: auto.
      { apply measure_rep_layer_le_proper. apply classicOrd.le_eq_or_lt in Hlayer. destruct Hlayer.
        - right. econstructor 1. auto.
        - left. split; auto. }
      iModIntro.
      iApply ("TaskQueue_run_task_spec" $! 100 (100 ⊕ (mr ⊕ 1))%M true with "[$TG $F_mr $F_mr1 $HW $ITQ]").
      iIntros (rv) "(LC& (%& TG& %Ninng& Qw& Gg& Fng))".
      iMod (group_delete with "TG Gg") as "TG". replace ({[ng; g]} ∖ {[g]}) with ({[ng]} : gset ogid) by set_solver.
      iClear "GF".
      iAssert (([∗ set] k ∈ {[ng]}, grP_fuel k ℓ (100 ⊕ (mr ⊕ 1))%M))%I with "[Fng]" as "GF".
      { iApply big_sepS_singleton. iFrame. }
      iPoseProof (grP_fuel_add_set with "GF") as "[GF F_mr]".
      iPoseProof (grP_fuels_init with "GF") as "GF".
      do 2 lwp_pure_one.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_lwpupd_add_later with "LC1"). iNext.
      iApply ("IH" with "Qw F_mr TG GF").
    - iDestruct "HW" as "%". subst G.
      iAssert ([∗ set] g ∈ ∅, grP_fuel g 0 100)%I as "GF''". 1: done.
      iPoseProof (grP_fuels_init with "GF''") as "GF'".
      lwp_pure. simpl.
      iFrame "TG GF'". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _".
      iClear "GF' GF''".
      lwp_pure_one.
      (** Lob (co-)induction *)
      iRevert "TG GF". iLöb as "IH". iIntros "TG GF".
      lwp_pures.
      lwp_bind (TaskQueue.run_task _).
      iModIntro.
      iApply ("TaskQueue_run_task_spec" $! 100 (100 ⊕ (mr ⊕ 1))%M false 1%positive 1%positive with "[$TG $ITQ]").
      1: iSplit; done.
      iIntros (rv) "(LC& TG)".
      iClear "GF".
      iAssert ([∗ set] g ∈ ∅, grP_fuel g 0 100)%I as "GF''". 1: done.
      iPoseProof (grP_fuels_init with "GF''") as "GF'".
      iModIntro. lwp_pure. simpl.
      iFrame "TG GF'". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _".
      iClear "GF' GF''".
      do 1 lwp_pure_one.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_lwpupd_add_later with "LC1"). iNext.
      iApply ("IH" with "TG GF").
  Qed.

  Lemma TaskQueue_init_spec :
    ⊢ ∃ m, ∀ (lc : Ord.t) i G ℓ,
    l{{{ thP_groups i G ∗ grP_fuels G m ∗ ⌜(ℵ <= ℓ)%ordi⌝ }}}
      TaskQueue.init #() @ i
    l{{{ ql γ, RET ql; £ lc ∗ thP_groups i G ∗ is_task_queue ql γ ℓ }}}.
  Proof.
    iPoseProof (Queue_init_spec) as (mqi) "Queue_init_spec".
    iPoseProof (TaskQueue_worker_spec) as (mtw) "TaskQueue_worker_spec".
    (** For internal steps and function calls *)
    iExists (100%nat ⊕ mqi)%M. iIntros (lc i G ℓ) "!> % (TG& GF& %Hlayer) HΦ".
    rewrite /TaskQueue.init.
    iPoseProof (grP_fuels_add_gen with "GF") as "[GF GF_qi]".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_bind (Queue.init _).
    iModIntro.
    iApply ("Queue_init_spec" $! 0 (is_task ℓ) with "[$TG $GF_qi]").
    iIntros (??) "(_& TG& IQI)".
    lwp_pures.
    lwp_bind (Fork _).
    iPoseProof (grP_fuels_add 96 1 with "GF") as "[GF GF1]". 1: lia.
    iModIntro.
    iApply (lwp_fork). iModIntro. iFrame "TG GF1". iExists ∅. iSplitR; first done.
    iIntros (?) "TG _ TGj !>". iModIntro.
    iMod (group_alloc _ _ _ ℓ mtw with "TGj") as "(%& %Ning& TGj& Gg& Fg)".
    iMod (is_queue_initialize with "IQI Gg") as "[#IQ Qw]".
    iModIntro. iSplitR "TGj Fg Qw".
    - iModIntro. lwp_pures.
      iModIntro. lwp_finish.
      rewrite /is_task_queue. iApply ("HΦ" with "[$Q_LC $TG $IQ]").
    - iModIntro. rewrite /is_task_queue.
      iApply ("TaskQueue_worker_spec" $! true with "[$TGj $Fg $Qw $IQ]").
      { iPureIntro. split; auto. set_solver. }
      iIntros "%". done.
  Qed.

End proof.
