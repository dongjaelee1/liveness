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
    λ v B, (∃ f a ℓt m,
               ⌜(v = (f, a)%V) ∧ (ℓt < ℓ)%ordi⌝ ∧
               ∀ lc i j G g K ℓg,
              l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g ℓt m) ∗ ogP_obls j g ℓg K ∗ ⌜ B ⊆ K ⌝ }}}
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
    iExists (100 ⊕ m)%M. iIntros (lc i j G g K B γ ℓ ℓ' ql task_f task_a) "!> % (TG& GF& Gg& %Sub& OF& TASK& (%Hℓ& #IQ)) HΦ".
    rewrite /TaskQueue.put_task.
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF F_Queue_enqueue]".
    iPoseProof (ogP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_pures.
    (** Queue enqueue *)
    lwp_bind (Queue.enqueue _ _).
    iModIntro. iApply ("Queue_enqueue_spec" $! 0 with "[$TG $F_Queue_enqueue $Gg $OF TASK $IQ]").
    { by iFrame. }
    iIntros "(_& TG& Gg)". iApply ("HΦ" with "[$Q_LC $TG $Gg]").
  Qed.

  TODO

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
    iExists (100 ⊕ 1 ⊕ m)%M. iIntros (lc b wi ni wg ng i j G g A γ ℓ ql) "!> % (TG& GF& Gg& HW& (%Hℓ& #IQ)) HΦ".
    rewrite /TaskQueue.run_task.
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF F_m]".
    iPoseProof (ogP_fuel_add_set with "F_m") as "[F_task F_m]".
    iPoseProof (ogP_fuels_init with "GF") as "GF".
    assert (Hlayer : (ℵ < (ℵ ⊕ ℓ))%ordi).
    { apply hessenberg.add_lt_l; auto. }
    iMod (ogP_fuel_mon_gen_set _ ℵ%ordi _ m with "F_m") as "F_m". 1: auto.
    { apply measure_layer_le_proper. right. econstructor 1. auto. }      
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_bind (Queue.dequeue _).
    iModIntro. iApply ("Queue_dequeue_spec" $! 0 b with "[$TG $F_m $Gg $HW $IQ]").
    iIntros (x B) "(_& TG& Gg& %Hdisj& Hx& HW)".
    iAssert (⌜x = NONEV ∨ ∃ v, x = SOMEV v⌝)%I as "%Hcase".
    { destruct x; eauto. destruct x; auto. destruct l; auto. }
    destruct Hcase as [Hcase | Hcase].
    - subst x. iPoseProof "Hx" as "%". subst B. rewrite union_empty_r_L.
      lwp_pures.
      iModIntro. lwp_finish. iModIntro.
      iApply "HΦ". iFrame.
    - destruct Hcase as (v& Hcase). subst x.
      iDestruct "Hx" as "(%&%&%&%mt& (%FA& %Hll)& Hx)". subst v.
      lwp_pures.
      lwp_bind (f a).
      iMod (ogP_fuel_extend_set _ ℓt _ mt with "F_task") as "F_task".
      { eapply ord.lt_le_lt. 1: eauto. eapply hessenberg.add_base_r. }
      iModIntro.
      iApply ("Hx" $! 0 with "[$TG $F_task $Gg]").
      { iPureIntro. set_solver. }
      iIntros (?) "(_& TG& Gg)". replace ((A ∪ B) ∖ B) with A by set_solver.
      iApply "HΦ". iFrame.
  Qed.

  Lemma TaskQueue_worker_spec :
    ⊢ ∃ m, ∀ (b : bool) i G γ ℓ (ql : val),
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g (ℵ ⊕ ℓ)%ordi m) ∗
         (if b
          then ∃ g, queue_worker γ i g ∗ ⌜G = {[g]}⌝
          else ⌜G = ∅⌝) ∗
         is_task_queue ql γ ℓ }}}
      TaskQueue.worker ql @ i
    l{{{ RET #(); False }}}.
  Proof.
    iPoseProof (TaskQueue_run_task_spec) as (mr) "TaskQueue_run_task_spec".
    (** For internal steps and executing run_task *)
    iExists (100 ⊕ mr)%M. iIntros (b i G γ ℓ ql) "!> % (TG& GF& HW& #ITQ) HΦ".
    rewrite /TaskQueue.worker.
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF F_mr]".
    iPoseProof (ogP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _".
    lwp_pure_one.
    (** Lob (co-)induction *)
    iClear "HΦ".
    iRevert (G) "HW F_mr TG GF". iLöb as "IH". iIntros (G) "HW F_mr TG GF".
    lwp_pures.
    lwp_bind (TaskQueue.run_task _).
    destruct b.
    - iDestruct "HW" as "(%& QW& %HG)". subst G.


      TODO

    
    lwp_pures.
    lwp_pures.
    iModIntro. iApply ("Queue_dequeue_spec" $! 0 b with "[$TG $F_m $Gg $HW $IQ]").
    iIntros (x B) "(_& TG& Gg& %Hdisj& Hx& HW)".
    iAssert (⌜x = NONEV ∨ ∃ v, x = SOMEV v⌝)%I as "%Hcase".
    { destruct x; eauto. destruct x; auto. destruct l; auto. }
    destruct Hcase as [Hcase | Hcase].
    - subst x. iPoseProof "Hx" as "%". subst B. rewrite union_empty_r_L.
      lwp_pures.
      iModIntro. lwp_finish. iModIntro.
      iApply "HΦ". iFrame.
    - destruct Hcase as (v& Hcase). subst x.
      iDestruct "Hx" as "(%&%&%&%mt& (%FA& %Hll)& Hx)". subst v.
      lwp_pures.
      lwp_bind (f a).
      iMod (ogP_fuel_extend_set _ ℓt _ mt with "F_task") as "F_task".
      { eapply ord.lt_le_lt. 1: eauto. eapply hessenberg.add_base_r. }
      iModIntro.
      iApply ("Hx" $! 0 with "[$TG $F_task $Gg]").
      { iPureIntro. set_solver. }
      iIntros (?) "(_& TG& Gg)". replace ((A ∪ B) ∖ B) with A by set_solver.
      iApply "HΦ". iFrame.
  Qed.

End proof.
