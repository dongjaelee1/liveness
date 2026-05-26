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
From liris.heap_lang.examples Require Export ticket_lock.

Module Queue.
  (** References:
    Iron (https://gitlab.mpi-sws.org/iris/iron/-/blob/master/theories/heap_lang/lib/queue.v)
    Transfinite Iris (https://gitlab.mpi-sws.org/iris/transfinite/-/blob/master/theories/examples/termination/eventloop.v)
   *)

  (** Use a ticket lock. *)
  Definition init : val :=
    λ: <>,
      let: "node" := ref NONE in
      let: "hd" := ref "node" in
      let: "tl" := ref "node" in
      let: "lock" := TicketLock.init #() in
      ("hd", "tl", "lock").

  Definition enqueue : val :=
    λ: "q" "x",
      let: "lock" := Snd "q" in
      TicketLock.acquire "lock";;
      let: "tptr" := Snd (Fst "q") in
      let: "t" := !"tptr"  in
      let: "newt" := ref NONE in
      "t" <- SOME ("x", "newt");;
      "tptr" <- "newt";;
      TicketLock.release "lock".

  Definition dequeue : val :=
    λ: "q",
      let: "lock" := Snd "q" in
      TicketLock.acquire "lock";;
      let: "hptr" := Fst (Fst "q") in
      let: "h" := !"hptr" in
      match: !"h" with
        NONE =>
          (* Empty queue. *)
          TicketLock.release "lock";;
          NONE
      | SOME "node" =>
          let: "newh" := Snd "node" in
          "hptr" <- "newh";;
          Free "h";;
          TicketLock.release "lock";;
          SOME (Fst "node")
      end.

End Queue.

(** ** A queue's spec with a liveness guarantee: any element can be associated with some obligations. *)
(** The CMRA we need. *)
Class queueGpreS (Σ : gFunctors) : Set :=
  QueueGpreS {
      queueGpreS_queue : inG Σ (dfrac_agreeR (list (val* oids)));
      #[local] queueGpreS_data_inG :: ghost_varG Σ (thread_id * ogid);
    }.

Class queueG Σ :=
  QueueG {
      #[local] queue_inG :: queueGpreS Σ;
    }.

Definition queueΣ : gFunctors :=
    #[GFunctor (dfrac_agreeR (list (val * oids))); ghost_varΣ (thread_id * ogid)].

Global Instance subG_queueΣ {Σ} : subG queueΣ Σ → queueGpreS Σ.
Proof. solve_inG. Qed.

Record queue_γ :=
  QueueName {
      queue_ticketlock_γ : ticketlock_γ;
      queue_γq : gname;
      queue_γd : gname;
    }.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
(** FIXME: why do we need this? Is there a more consistent way of doing this?
           ticket lock inG is also here, doesn't look great. *)
Local Existing Instances queue_inG queueGpreS_queue queueGpreS_data_inG tlock_config_inG.

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

  Let N := nroot.@"queue".
  Let Ni := N.@"invariant".

  Local Definition qG_queue γ (l : list (val * oids)) q : iProp Σ :=
    own γ (to_dfrac_agree (DfracOwn q) l).

  Definition queue_worker γ i g : iProp Σ :=
    ghost_var (queue_γd γ) (1/2)%Qp (i, g).

  Local Fixpoint queue_contents (lh lt : loc) (vs : list (val * oids)) (φ : val → oids → iProp Σ) : iProp Σ :=
    match vs with
    | [] => (⌜lh = lt⌝ ∗ lh ↦ NONEV)
    | (v, B) :: vs => (∃ l : loc, lh ↦ SOMEV (v, #l) ∗ φ v B ∗ queue_contents l lt vs φ)
    end%I.

  (* Mostly protects ghost resources + sync using qG_queue *)
  Local Definition queue_inv (ℓ : ord.t) γq γd : iProp Σ :=
    (∃ (vs : list (val * oids)) (i : thread_id) (g : ogid),
        qG_queue γq vs (1/2)%Qp ∗
        ghost_var γd (1/2)%Qp (i, g) ∗
        (* FIXME: library for pairwise disjointedness *)
        ⌜ disjoint_list_of_sets (vs.*2) ⌝ ∗
        ogP_obls i g ℓ (union_list_of_sets (vs.*2)) ∗
        ([∗ list] n ↦ B ∈ (vs.*2), [∗ set] b ∈ B, oblP_fuel b (ℓ)%ordi (S n)%M))%I.

  (* Mostly protects physical resources + sync using qG_queue *)
  Local Definition queue_lock (φ : val → oids → iProp Σ) γq (lhptr ltptr : loc) : iProp Σ :=
    (∃ (lh lt : loc) (vs : list (val * oids)),
        lhptr ↦ #lh ∗
        ltptr ↦ #lt ∗
        qG_queue γq vs (1/2)%Qp ∗
        queue_contents lh lt vs φ)%I.

  (** The invariant *)
  Definition is_queue (ql : val) (γ : queue_γ) (ℓ : ord.t) (φ : val → oids → iProp Σ) : iProp Σ :=
    ∃ (lhptr ltptr : loc) (tl : val),
      ⌜ql = (#lhptr, #ltptr, tl)%V⌝ ∧
      inv Ni (queue_inv ℓ (queue_γq γ) (queue_γd γ)) ∗
      (queue_ticketlock_γ γ) ↪LOCK□ 0 ∗
      is_fair_lock tl (queue_ticketlock_γ γ) (queue_lock φ (queue_γq γ) lhptr ltptr).

  (** Enables delayed initialization after picking a worker thread. *)
  Definition is_queue_init (ql :val) (γ : queue_γ) (φ : val → oids → iProp Σ) : iProp Σ :=
    (∃ (lhptr ltptr : loc) (tl : val),
        ⌜ql = (#lhptr, #ltptr, tl)%V⌝ ∧
        qG_queue (queue_γq γ) [] (1/2)%Qp ∗
        ghost_var (queue_γd γ) 1 (inhabitant, inhabitant) ∗
        (queue_ticketlock_γ γ) ↪LOCK□ 0 ∗
        is_fair_lock tl (queue_ticketlock_γ γ) (queue_lock φ (queue_γq γ) lhptr ltptr))%I.

  (** ** Lemmas *)

  Global Instance is_queue_persistent ql γ ℓ φ : Persistent (is_queue ql γ ℓ φ).
  Proof. rewrite /is_queue. apply _. Qed.

  Lemma is_queue_initialize E ql γ (ℓ : ord.t) (φ : val → oids → iProp Σ) i g :
    is_queue_init ql γ φ -∗ ogP_obls i g ℓ ∅ ={E}=∗ is_queue ql γ ℓ φ ∗ queue_worker γ i g.
  Proof.
    iIntros "(%&%&%& %Hq& Qvs& GVd& #FL) Go".
    rewrite /is_queue.
    iMod (ghost_var_update (i, g) with "GVd") as "[GVd $]".
    iMod (inv_alloc Ni _ (queue_inv ℓ (queue_γq γ) (queue_γd γ)) with "[Qvs GVd Go]") as "#Invq".
    { iNext. rewrite /queue_inv. iFrame. iSplitR.
      { iPureIntro. intros. done. }
      iSplitL; last done. iFrame. }
    iModIntro. iFrame "FL Invq". auto.
  Qed.

  (** ** Program proofs *)
  (** FIXME: better notation for triples with this pattern *)
  Lemma Queue_init_spec :
    ⊢ ∃ m, ∀ lc φ i G,
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ∃ ℓ, ogP_fuel g ℓ m) }}}
      Queue.init #() @ i
    l{{{ ql γ, RET ql; £ lc ∗ thP_groups i G ∗ is_queue_init ql γ φ }}}.
  Proof.
    iPoseProof (TicketLock_init_spec) as (m) "TicketLock_init_spec".
    iExists (20 ⊕ m)%M. iIntros (lc φ i G) "!> % (TG& GF) HΦ".
    rewrite /Queue.init.
    iPoseProof (ogP_fuels_add_gen with "GF") as "[GF F_TicketLock]".
    lwp_lam. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_pures.
    (** Alloc node ptr *)
    lwp_bind (AllocN _ _).
    iPoseProof (ogP_fuels_add 17 1 with "GF") as "[GF GF1]". 1: lia.
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ptr_node) "((_& TG& _)& Ptr_node& _)".
    lwp_pures.
    (** Alloc hd ptr *)
    lwp_bind (AllocN _ _).
    iPoseProof (ogP_fuels_add 14 1 with "GF") as "[GF GF1]". 1: lia.
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (lhptr) "((_& TG& _)& Ptr_hd& _)".
    lwp_pures.
    (** Alloc tl ptr *)
    lwp_bind (AllocN _ _).
    iPoseProof (ogP_fuels_add 11 1 with "GF") as "[GF GF1]". 1: lia.
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ltptr) "((_& TG& _)& Ptr_tl& _)".
    lwp_pures.
    (** Init TicketLock *)
    (** FIXME: better tactic for function calls *)
    lwp_bind (TicketLock.init #()).
    iMod (own_alloc (to_dfrac_agree (DfracOwn (1/2)) ([] : list (val * oids)) ⋅ to_dfrac_agree (DfracOwn (1/2)) ([] : list (val * oids)))) as (γq) "[HQvs HQvs0]".
    { rewrite -dfrac_agree_op. done. }
    iModIntro.
    iApply ("TicketLock_init_spec" $! 0 0 with "[$TG $F_TicketLock]").
    iIntros (tl γtl) "(_& TG& CF& IFL)".
    iMod (lock_config_persist with "CF") as "#CF".
    iMod ("IFL" $! _ (queue_lock φ γq lhptr ltptr)%I with "[Ptr_node Ptr_hd Ptr_tl HQvs0]") as "#IFL".
    { iFrame. eauto. }
    lwp_pures.
    iModIntro. lwp_finish.
    iMod (ghost_var_alloc (inhabitant : thread_id, inhabitant : ogid)) as (γd) "Gv".
    iApply ("HΦ" $! _ (QueueName γtl γq γd)).
    iModIntro. iFrame "TG Q_LC".
    rewrite /is_queue_init. iFrame "HQvs Gv CF IFL". auto.
  Qed.

  Lemma queue_contents_enqueue lh lt vs φ :
    queue_contents lh lt vs φ -∗
    (lt ↦ NONEV ∗
     (∀ v B (l : loc), lt ↦ SOMEV (v, #l) -∗ φ v B -∗ l ↦ NONEV -∗ queue_contents lh l (vs ++ [(v, B)]) φ)).
  Proof.
    revert lh lt φ. induction vs; iIntros (???) "H"; simpl.
    { iDestruct "H" as "(%& Ptr_lh)". subst. iFrame. iIntros (???) "Ptr_lt Hφ Ptr_l".
      iExists l. iFrame. auto. }
    destruct a as (v&B). iDestruct "H" as "(%& Ptr_lh& Hφ& QC)".
    iPoseProof (IHvs with "QC") as "($& ACC)".
    iIntros (???) "Ptr_lt Hφ0 Ptr_l0". iFrame "Ptr_lh Hφ".
    iApply ("ACC" with "Ptr_lt Hφ0 Ptr_l0").
  Qed.

  (** TODO: LAT-style spec that enables the client to put ogP_obls in some invariant. *)
  Lemma Queue_enqueue_spec :
    ⊢ ∃ m, ∀ lc i j G g K B φ γ ℓ ℓ' (ql x : val),
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g ℵ%ordi m) ∗
         ogP_obls j g ℓ' K ∗
         ⌜ B ⊆ K ⌝ ∗ ([∗ set] b ∈ B, oblP_fuel b (ℓ ⊕ 1)%ordi 1) ∗
         φ x B ∗
         is_queue ql γ ℓ φ }}}
      Queue.enqueue ql x @ i
    l{{{ RET #(); £ lc ∗ thP_groups i G ∗ ogP_obls j g ℓ' (K ∖ B) }}}.
  Proof.
    iPoseProof (TicketLock_acquire_spec) as (ma) "TicketLock_acquire_spec".
    iPoseProof (TicketLock_release_spec) as (mr) "TicketLock_release_spec".
    iExists (100 ⊕ ma ⊕ mr)%M. iIntros (lc i j G g K B φ γ ℓ ℓ' ql x) "!> % (TG& Fs& GB& %SubBK& FB& Hφ& #IQ) HΦ".
    rewrite /Queue.enqueue.
    iPoseProof (ogP_fuel_add_set with "Fs") as "[GF F_m]".
    iPoseProof (ogP_fuel_add_set with "F_m") as "[F_ma F_mr]".
    iPoseProof (ogP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_pures.
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
    iPoseProof (ogP_fuels_init with "F_mr") as "F_mr".
    iPoseProof (ogP_fuels_add_group with "F_mr_gu F_mr") as "F_mr".
    rewrite (ogP_fuel_eq gu 0 _ (94 ⊕ 6)%M); cycle 1.
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add with "F_gu") as "[F_gu _]".
    iPoseProof (ogP_fuels_add_group with "F_gu GF") as "GF".
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (ogP_fuels_add 87 1 with "GF") as "[GF GF1]". 1: lia.
    iDestruct "R" as "(%&%&%& Ptr_lh& Ptr_lt& Queue& QC)".    
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $Ptr_lt]"). 1: done.
    iIntros "((_& TG& _)& Ptr_lt)".
    lwp_pures.
    lwp_bind (AllocN _ _).
    iPoseProof (ogP_fuels_add 83 1 with "GF") as "[GF GF1]". 1: lia.
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ptr_newt) "((_& TG& _)& Ptr_newt& _)".
    lwp_pure_lc 100.
    lwp_pures.
    (** Physical enqueue *)
    lwp_bind (Store _ _).
    iPoseProof (queue_contents_enqueue with "QC") as "(QC_Ptr_lt& QC_ACC)".
    iModIntro.
    iPoseProof (ogP_fuels_add 78 1 with "GF") as "[GF GF1]". 1: lia.
    iApply (lwp_store _ ∅ 0 with "[$TG $GF1 $QC_Ptr_lt]"). 1: done.
    iIntros "((_& TG& _)& QC_Ptr_lt)".
    iPoseProof ("QC_ACC" with "QC_Ptr_lt Hφ Ptr_newt") as "QC".
    lwp_pures.
    lwp_bind (Store _ _).
    iModIntro.
    iPoseProof (ogP_fuels_add 75 1 with "GF") as "[GF GF1]". 1: lia.
    iApply (lwp_store _ ∅ 0 with "[$TG $GF1 $Ptr_lt]"). 1: done.
    iIntros "((_& TG& _)& Ptr_lt)".
    lwp_pures.
    iMod (inv_acc with "IQ") as "[qinv IQ_ACC]". 1: set_solver.
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lc_lwpupd_add_later with "LC1"). iNext.
    iDestruct "qinv" as "(%&%&%& Queue0& Gvar& %Disj& Gq& Fq)".
    iPoseProof (own_valid_2 with "Queue Queue0") as "%".
    apply dfrac_agree_op_valid in H. destruct H as [_ ?]. apply leibniz_equiv in H. subst vs0.
    iMod (own_update_2 with "Queue Queue0") as "[Queue Queue0]".
    { eapply (dfrac_agree_update_2 _ _ _ _ (vs ++ [(x, B)])). rewrite dfrac_op_own Qp.div_2. auto. }
    iMod (oblP_fuel_extend_set _ ℓ _ (1 ⊕ ℵ)%M with "FB") as "FB".
    { apply hessenberg.add_lt_l. apply ord.S_lt. }
    iPoseProof (oblP_fuel_add_set with "FB") as "[FB FBq]".
    iMod (obl_offload_set with "GB Gq FB") as "(GB& Gq& %HGdisj)". 1: set_solver. 1: done.
    iMod (oblP_fuel_mon_set _ _ (S (length (vs.*2)))%M with "FBq") as "FBq".
    { rewrite !measure_nat measure_large. apply Ord.lt_le. unshelve etrans. 1: exact ω%ord.
      - apply Ord.omega_upperbound.
      - rewrite Ord.omega_from_peano_lt_set. apply Ord.large_lt_from_wf_set. }
    iModIntro.
    iMod ("IQ_ACC" with "[Queue0 Gvar Gq Fq FBq]") as "_".
    { iNext. iFrame "Queue0 Gvar". iSplit.
      { iPureIntro. rewrite fmap_app. apply disjoint_list_of_sets_app_disjoint_iff. simpl. split_and !; auto.
        { apply disjoint_list_of_sets_singleton. }
        rewrite union_empty_r_L. auto. }
      iSplitL "Gq".
      { rewrite fmap_app union_list_of_sets_app union_list_of_sets_singleton. iFrame. }
      rewrite fmap_app. simpl. iApply big_sepL_app. iFrame.
      iApply big_sepL_singleton. iApply oblP_fuel_eq_set. 2: iFrame.
      replace (length vs.*2 + 0)%nat with (length vs.*2)%nat by lia. done. }
    iModIntro.
    iApply lwp_sfmupd.
    iApply ("TicketLock_release_spec" with "[$TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC]").
    { iSplit. 1: iPureIntro; set_solver. iFrame. }
    (* FIXME: it would be nice if we don't get this evar *)
    Unshelve. 2: exact 0.
    iIntros "(_& TG& Ggu& _)".
    replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
    iMod (group_delete with "TG Ggu") as "TG". replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
    replace (B ∖ B) with (∅ : oids) by set_solver.
    iApply ("HΦ" with "[$Q_LC $TG $GB]").
  Qed.

  (** TODO: LAT-style spec that enables the client to put ogP_obls in some invariant. *)
  Lemma Queue_dequeue_spec :
    ⊢ ∃ m, ∀ lc μ (b : bool) wi wg i G φ γ ℓ (ql : val),
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g ℵ%ordi m) ∗
         (if b
          then queue_worker γ wi wg
          else True) ∗
         is_queue ql γ ℓ φ }}}
      Queue.dequeue ql @ i
      l{{{ x, RET x; £ lc ∗
                     (match x with
                      | NONEV =>
                          (if b
                           then (∃ ng, thP_groups i ({[ng]} ∪ G) ∗ ⌜ng ∉ G⌝ ∗
                                       queue_worker γ i ng ∗ ogP_obls wi wg ℓ ∅ ∗ ogP_fuel ng ℓ μ)
                           else (thP_groups i G))
                      | SOMEV v =>
                          (∃ g B, φ v B ∗ ogP_obls i g ℓ B ∗ ogP_fuel g ℓ μ ∗
                                  (if b
                                   then (∃ ng, thP_groups i ({[g; ng]} ∪ G) ∗ ⌜g ∉ G ∧ ng ∉ G ∧ g ≠ ng⌝ ∗
                                               queue_worker γ i ng ∗ ogP_obls wi wg ℓ ∅ ∗ ogP_fuel ng ℓ μ)
                                   else (thP_groups i ({[g]} ∪ G) ∗ ⌜g ∉ G⌝)))
                      | _ => (False)
                      end)
      }}}.
  Proof.
    iPoseProof (TicketLock_acquire_spec) as (ma) "TicketLock_acquire_spec".
    iPoseProof (TicketLock_release_spec) as (mr) "TicketLock_release_spec".
    iExists (100 ⊕ ma ⊕ mr)%M. iIntros (lc μ b wi wg i G φ γ ℓ ql) "!> % (TG& GF& HW& #IQ) HΦ".
    rewrite /Queue.dequeue.
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF F_m]".
    iPoseProof (ogP_fuel_add_set with "F_m") as "[F_ma F_mr]".
    iPoseProof (ogP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
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
    iPoseProof (ogP_fuels_init with "F_mr") as "F_mr".
    iPoseProof (ogP_fuels_add_group with "F_mr_gu F_mr")as "F_mr".
    rewrite (ogP_fuel_eq gu 0 _ (96 ⊕ 4)%M); cycle 1.
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add with "F_gu") as "[F_gu _]".
    iPoseProof (ogP_fuels_add_group with "F_gu GF") as "GF".
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (ogP_fuels_add 89 1 with "GF") as "[GF GF1]". 1: lia.
    iDestruct "R" as "(%&%&%& Ptr_lh& Ptr_lt& Queue& QC)".    
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $Ptr_lh]"). 1: done.
    iIntros "((_& TG& _)& Ptr_lh)".
    lwp_pure_lc 100.
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (ogP_fuels_add 86 1 with "GF") as "[GF GF1]". 1: lia.
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
      destruct b.
      + iPoseProof (ghost_var_agree with "Gvar HW") as "%". simplify_eq. simpl.
        iMod (group_alloc _ _ _ ℓ (μ ⊕ 83 ⊕ mr)%M with "TG") as "(%ng& %Ninng& TG& Gng& Fng)".
        iMod (ghost_var_update_2 (i, ng) with "Gvar HW") as "[Gvar HW]". 1: by rewrite Qp.div_2.
        iModIntro. iMod ("IQ_ACC" with "[Queue0 Gvar Fq Gng]") as "_".
        { iNext. iFrame. simpl. iFrame. iPureIntro. auto. }
        iPoseProof (ogP_fuel_add with "Fng") as "[Fng Fng']".
        iPoseProof (ogP_fuel_add with "Fng'") as "[Fng' Fng_mr]".
        iPoseProof (ogP_fuels_add_group with "Fng_mr F_mr") as "F_mr".
        iModIntro.
        iApply ("TicketLock_release_spec" $! 0 with "[$TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC_Ptr_lh]").
        { iSplit. 1: iPureIntro; set_solver. iFrame. simpl. by iFrame. }
        iIntros "(_& TG& Ggu& _)".
        replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
        iMod (group_delete with "TG Ggu") as "TG".
        replace (({[ng]} ∪ ({[gu]} ∪ G)) ∖ {[gu]}) with ({[ng]} ∪ G) by set_solver.
        iPoseProof (ogP_fuels_remove_group gu with "GF") as "GF".
        replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
        iPoseProof (ogP_fuels_add_group with "Fng' GF")as "GF".
        lwp_pures.
        iModIntro. lwp_finish.
        iApply ("HΦ"). iFrame. iModIntro. iPureIntro. set_solver.
      + iModIntro. iMod ("IQ_ACC" with "[Queue0 Gvar Fq Gq]") as "_".
        { iNext. iFrame. simpl. auto. }
        iModIntro.
        iApply ("TicketLock_release_spec" $! 0 with "[$TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC_Ptr_lh]").
        { iSplit. 1: iPureIntro; set_solver. iFrame. simpl. by iFrame. }
        iIntros "(_& TG& Ggu& _)".
        replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
        iMod (group_delete with "TG Ggu") as "TG".
        iPoseProof (ogP_fuels_remove_group gu with "GF") as "GF".
        replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
        lwp_pures.
        iModIntro. lwp_finish.
        iApply ("HΦ"). iFrame. by iModIntro.
    - simpl. iDestruct "QC" as "(%ln& QC_Ptr_lh& Hφ& QC)".
      iModIntro.
      iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $QC_Ptr_lh]"). 1: done.
      iIntros "((_& TG& _)& QC_Ptr_lh)".
      lwp_pures.
      lwp_bind (Store _ _).
      iModIntro.
      iPoseProof (ogP_fuels_add 79 1 with "GF") as "[GF GF1]". 1: lia.
      iApply (lwp_store _ ∅ 0 with "[$TG $GF1 $Ptr_lh]"). 1: done.
      iIntros "((_& TG& _)& Ptr_lh)".
      lwp_pures.
      lwp_bind (Free _).
      iModIntro.
      iPoseProof (ogP_fuels_add 76 1 with "GF") as "[GF GF1]". 1: lia.
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
      iAssert (|={⊤ ∖ ↑Ni}=>m |={⊤ ∖ ↑Ni,⊤}=> ogP_obls j g ℓ (A ∪ B) ∗ ⌜A ## B⌝ ∗ (if b then queue_worker γ ni ng ∗ ogP_obls wi wg ℓ ∅ else True))%I
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
          rewrite union_empty_l_L. iFrame "Gg Gw Gq". iModIntro. iMod ("IQ_ACC" with "[-]"); last by iModIntro.
          iNext. iFrame. iPureIntro. auto.
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
          iFrame "Gg". iModIntro. iMod ("IQ_ACC" with "[-]"); last by iModIntro. iNext. iFrame. auto. }
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
