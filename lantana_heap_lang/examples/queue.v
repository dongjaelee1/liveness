From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From iris.algebra Require Import reservation_map dfrac_agree mono_list gset.
From transfinite.base_logic.lib Require Import ghost_var ghost_map.
From lantana.algebra Require Import list_of_sets.
From lantana.heap_lang.examples Require Export ticket_lock.

Module Queue.
  (** References:
    Iron (https://gitlab.mpi-sws.org/iris/iron/-/blob/master/theories/heap_lang/lib/queue.v)
    Transfinite Iris (https://gitlab.mpi-sws.org/iris/transfinite/-/blob/master/theories/examples/termination/eventloop.v)
   *)

  (** Use a ticket lock. *)
  Definition init : val :=
    λ: <>,
      let: "node" := ref NONE in
      (ref "node", ref "node", TicketLock.init #()).

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
          "hptr" <- (Snd "node");;
          Free "h";;
          TicketLock.release "lock";;
          SOME (Fst "node")
      end.

End Queue.

(** ** A queue's spec with a liveness guarantee: any element can be associated with some obligations. *)
(** The CMRA we need. *)
Class queueGpreS (Σ : gFunctors) : Set :=
  QueueGpreS {
      queueGpreS_queue : inG Σ (dfrac_agreeR (list (val * oids)));
      #[local] queueGpreS_data_inG :: ghost_varG Σ (ocid);
    }.

Class queueG Σ :=
  QueueG {
      #[local] queue_inG :: queueGpreS Σ;
    }.

Definition queueΣ : gFunctors :=
    #[GFunctor (dfrac_agreeR (list (val * oids))); ghost_varΣ (ocid)].

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
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

  Ltac lwp_pure_one := (iModIntro; lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

  Ltac lwp_pure_lc n := (iModIntro; lwp_pure; post_lwp_lc n).

  (** ** Definitions *)

  Let N := nroot.@"queue".
  Let Ni := N.@"invariant".

  Local Definition qG_queue γ (l : list (val * oids)) q : iProp Σ :=
    own γ (to_dfrac_agree (DfracOwn q) l).

  Definition queue_worker γ (g : ocid) : iProp Σ :=
    ghost_var_frac (queue_γd γ) (1/2)%Qp (g).

  Local Fixpoint queue_contents (lh lt : loc) (vs : list (val * oids)) (φ : val → oids → iProp Σ) : iProp Σ :=
    match vs with
    | [] => (⌜lh = lt⌝ ∗ lh ↦ NONEV)
    | (v, B) :: vs => (∃ l : loc, lh ↦ SOMEV (v, #l) ∗ φ v B ∗ queue_contents l lt vs φ)
    end%I.

  (* Mostly protects ghost resources + sync using qG_queue *)
  Local Definition queue_inv (ℓ : ord.t) γq γd : iProp Σ :=
    (∃ (vs : list (val * oids)) (g : ocid),
        qG_queue γq vs (1/2)%Qp ∗
        ghost_var_frac γd (1/2)%Qp (g) ∗
        ⌜ disjoint_list_of_sets (vs.*2) ⌝ ∗
        crP_obls g ℓ (union_list_of_sets (vs.*2)) ∗
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
      (queue_ticketlock_γ γ) ↪LOCK_AL□ ∗
      (queue_ticketlock_γ γ) ↪LOCK_CF□ 0 ∗
      is_fair_lock_alive tl (queue_ticketlock_γ γ) (queue_lock φ (queue_γq γ) lhptr ltptr).

  (** Enables delayed initialization after picking a worker thread. *)
  Definition is_queue_init (ql :val) (γ : queue_γ) (φ : val → oids → iProp Σ) : iProp Σ :=
    (∃ (lhptr ltptr : loc) (tl : val),
        ⌜ql = (#lhptr, #ltptr, tl)%V⌝ ∧
        qG_queue (queue_γq γ) [] (1/2)%Qp ∗
        ghost_var_frac (queue_γd γ) 1 (inhabitant : ocid) ∗
        (queue_ticketlock_γ γ) ↪LOCK_AL□ ∗
        (queue_ticketlock_γ γ) ↪LOCK_CF□ 0 ∗
        is_fair_lock_alive tl (queue_ticketlock_γ γ) (queue_lock φ (queue_γq γ) lhptr ltptr))%I.

  (** ** Lemmas *)

  Global Instance is_queue_persistent ql γ ℓ φ : Persistent (is_queue ql γ ℓ φ).
  Proof. rewrite /is_queue. apply _. Qed.

  Lemma is_queue_initialize E ql γ (ℓ : ord.t) (φ : val → oids → iProp Σ) g :
    is_queue_init ql γ φ -∗ crP_obls g ℓ ∅ ={E}=∗ is_queue ql γ ℓ φ ∗ queue_worker γ g.
  Proof.
    iIntros "(%&%&%& %Hq& Qvs& GVd& #FL) Go".
    rewrite /is_queue.
    iMod (ghost_var_update (g) with "GVd") as "[GVd $]".
    iMod (inv_alloc Ni _ (queue_inv ℓ (queue_γq γ) (queue_γd γ)) with "[Qvs GVd Go]") as "#Invq".
    { iNext. rewrite /queue_inv. iFrame. iSplitR.
      { iPureIntro. intros. done. }
      iSplitL; last done. iFrame. }
    iModIntro. iFrame "FL Invq". auto.
  Qed.

  (** ** Program proofs *)
  (** FIXME: better notation for triples with this pattern *)
  Lemma Queue_init_spec :
    ⊢ ∃ μ, ∀ lc φ i G C,
    l{{{ thread_expr i C (Queue.init #()) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g 0 μ) ∗ treg }}}
      Queue.init #() @ i
    l{{{ ql γ, RET ql; thread_expr i C (of_val ql) ∗ £ lc ∗ thP_carriers i G ∗ is_queue_init ql γ φ }}}.
  Proof.
    iPoseProof (TicketLock_init_spec) as (m) "TicketLock_init_spec".
    iExists (20 ⊕ m)%M. iIntros (lc φ i G C) "!> % (TE& TG& GF& #TR) HΦ".
    rewrite /Queue.init.
    iPoseProof (crP_fuel_add_set with "GF") as "[GF F_TicketLock]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_lam. simpl.
    iFrame "TG GF". iExists ∅, (lc ⊕ Ord.from_nat 3)%ord. iSplitR; first eauto. iIntros "TG GF _ Q_LC TE".
    iPoseProof (tlc_split with "Q_LC") as "[Q_LC LC]".
    iPoseProof (tlc_split_one 3 2 with "LC") as "[LC LC1]"; first done.
    lwp_pures.
    (** Alloc node ptr *)
    lwp_bind (AllocN _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (ptr_node) "[TE ((_& TG& _)& Ptr_node& _)]".
    lwp_pures.
    (** Init TicketLock *)
    (** FIXME: better tactic for function calls *)
    lwp_bind (TicketLock.init #()).
    iMod (own_alloc (to_dfrac_agree (DfracOwn (1/2)) ([] : list (val * oids)) ⋅ to_dfrac_agree (DfracOwn (1/2)) ([] : list (val * oids)))) as (γq) "[HQvs HQvs0]".
    { rewrite -dfrac_agree_op. done. }
    iModIntro.
    iApply ("TicketLock_init_spec" $! 0 0 with "[$TE $TG $F_TicketLock]").
    iIntros (tl γtl) "(TE& _& TG& AL& CF& IFL)".
    iMod (lock_alive_persist with "AL") as "#AL".
    iMod (lock_config_persist with "CF") as "#CF".
    (** Alloc tl ptr *)
    lwp_bind (AllocN _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (ltptr) "[TE ((_& TG& _)& Ptr_tl& _)]".
    (** Alloc hd ptr *)
    lwp_bind (AllocN _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (lhptr) "[TE ((_& TG& _)& Ptr_hd& _)]".
    lwp_pures.
    iApply lwp_sfmupd.
    iMod ("IFL" $! _ (queue_lock φ γq lhptr ltptr) with "[] TR LC [Ptr_node Ptr_hd Ptr_tl HQvs0]") as "#IFL".
    { iPureIntro. set_solver. }
    { iFrame. eauto. }
    iMod (is_fair_lock_register_alive ⊤ with "IFL AL LC1") as "#IFLA"; [set_solver|set_solver|].
    iModIntro. lwp_finish.
    iMod (ghost_var_alloc (inhabitant : ocid)) as (γd) "Gv".
    iApply ("HΦ" $! _ (QueueName γtl γq γd)).
    iModIntro. iFrame "TE TG Q_LC".
    rewrite /is_queue_init. iFrame "HQvs Gv IFLA". iModIntro. eauto.
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

  (** TODO: LAT-style spec that enables the client to put crP_obls in some invariant. *)
  Lemma Queue_enqueue_spec :
    ⊢ ∃ μ, ∀ lc i G g K B φ γ ℓ ℓg (ql x : val) C,
    l{{{ thread_expr i C (Queue.enqueue ql x) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g 1%ordi μ) ∗
         crP_obls g ℓg K ∗
         ⌜ B ⊆ K ⌝ ∗ ([∗ set] b ∈ B, oblP_fuel b (ℓ ⊕ 1)%ordi 1) ∗
         φ x B ∗
         is_queue ql γ ℓ φ }}}
      Queue.enqueue ql x @ i
    l{{{ RET #(); thread_expr i C (#()) ∗ £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K ∖ B) }}}.
  Proof.
    iPoseProof (TicketLock_acquire_spec) as (ma) "TicketLock_acquire_spec".
    iPoseProof (TicketLock_release_spec) as (mr) "TicketLock_release_spec".
    iExists (100 ⊕ ma ⊕ mr)%M. iIntros (lc i G g K B φ γ ℓ ℓg ql x C) "!> % (TE& TG& Fs& GB& %SubBK& FB& Hφ& #IQ) HΦ".
    rewrite /Queue.enqueue.
    iPoseProof (crP_fuel_add_set with "Fs") as "[GF F_m]".
    iPoseProof (crP_fuel_add_set with "F_m") as "[F_ma F_mr]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC TE".
    lwp_pures.
    (** Need ql *)
    iDestruct "IQ" as "(%lhptr&%ltptr&%tl& %Hql& #IQ& #IFLA)". simplify_eq.
    iAssert (queue_ticketlock_γ γ ↪LOCK_AL□ ∗ queue_ticketlock_γ γ ↪LOCK_CF□ 0 ∗
             is_fair_lock tl (queue_ticketlock_γ γ) (queue_lock φ (queue_γq γ) lhptr ltptr))%I as "#IFL".
    { iDestruct "IFLA" as "($& $& IFLA)". iApply (is_fair_lock_alive_is_fair_lock with "IFLA"). }
    lwp_pures.
    (** Acquire lock *)
    lwp_bind (TicketLock.acquire tl).
    iModIntro.
    iApply ("TicketLock_acquire_spec" $! 0 (100 ⊕ mr)%M with "[] [$TE $TG F_ma $IFL]").
    { iPureIntro. set_solver. }
    { iApply crP_fuel_layer_eq_set. 2: iFrame. by rewrite hessenberg.add_O_l. }
    iIntros (gu ku) "(TE& _& %Ningu& TG& Ggu& F_gu& F_ku& _& _& Lock& R)".
    iPoseProof (crP_fuel_add with "F_gu") as "[F_gu F_mr_gu]".
    (* Prepare fuels for the unlock call. *)
    (* iPoseProof (crP_fuels_init with "F_mr") as "F_mr". *)
    (* iPoseProof (crP_fuels_add_carrier with "F_mr_gu F_mr") as "F_mr". *)
    iMod (crP_fuel_layer_mon_set _ 0 with "F_mr") as "F_mr".
    { apply ordArith.le_from_nat. lia. }
    iPoseProof (big_sepS_union_2 with "[F_mr_gu] F_mr") as "F_mr".
    { iApply big_sepS_singleton. iFrame. }
    rewrite (crP_fuel_eq gu 0 _ (94 ⊕ 6)%M); cycle 1.
    { rewrite measure_rep_add !measure_rep_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (crP_fuel_add with "F_gu") as "[F_gu _]".
    iPoseProof (crP_fuels_add_carrier with "F_gu GF") as "GF".
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iDestruct "R" as "(%&%&%& Ptr_lh& Ptr_lt& Queue& QC)".    
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $Ptr_lt]"). 1: done.
    iIntros "[TE ((_& TG& _)& Ptr_lt)]".
    lwp_pures.
    lwp_bind (AllocN _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (ptr_newt) "[TE ((_& TG& _)& Ptr_newt& _)]".
    lwp_pure_lc 100.
    lwp_pures.
    (** Physical enqueue *)
    lwp_bind (Store _ _).
    iPoseProof (queue_contents_enqueue with "QC") as "(QC_Ptr_lt& QC_ACC)".
    iModIntro.
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_store _ ∅ 0 with "[$TE $TG $GF1 $QC_Ptr_lt]"). 1: done.
    iIntros "[TE ((_& TG& _)& QC_Ptr_lt)]".
    iPoseProof ("QC_ACC" with "QC_Ptr_lt Hφ Ptr_newt") as "QC".
    lwp_pures.
    lwp_bind (Store _ _).
    iModIntro.
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_store _ ∅ 0 with "[$TE $TG $GF1 $Ptr_lt]"). 1: done.
    iIntros "[TE ((_& TG& _)& Ptr_lt)]".
    lwp_pures.
    iMod (inv_acc with "IQ") as "[qinv IQ_ACC]". 1: set_solver.
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lc_lwpupd_add_later with "LC1"). iNext.
    iDestruct "qinv" as "(%&%& Queue0& Gvar& %Disj& Gq& Fq)".
    iPoseProof (own_valid_2 with "Queue Queue0") as "%".
    apply dfrac_agree_op_valid in H. destruct H as [_ ?]. apply leibniz_equiv in H. subst vs0.
    iMod (own_update_2 with "Queue Queue0") as "[Queue Queue0]".
    { eapply (dfrac_agree_update_2 _ _ _ _ (vs ++ [(x, B)])). rewrite dfrac_op_own Qp.div_2. auto. }
    iMod (oblP_fuel_extend_set _ ℓ _ (1 ⊕ ℵ)%M with "FB") as "FB".
    { apply hessenberg.add_lt_l. apply ord.S_lt. }
    iPoseProof (oblP_fuel_add_set with "FB") as "[FB FBq]".
    iMod (obl_offload_set with "GB Gq FB") as "(GB& Gq& %HGdisj)". 1: set_solver. 1: done.
    iMod (oblP_fuel_mon_set _ _ (S (length (vs.*2)))%M with "FBq") as "FBq".
    { rewrite !measure_rep_nat measure_rep_large. apply Ord.lt_le. unshelve etrans. 1: exact ω%ord.
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
    iDestruct "IFL" as "(AL& CF& IFL)".
    iApply ("TicketLock_release_spec" with "[] [$TE $TG $F_mr $Ggu $Lock $IFL Ptr_lh Ptr_lt Queue QC]").
    { iPureIntro. set_solver. }
    { iSplit. 1: iPureIntro; set_solver. iFrame. eauto. }
    (* FIXME: it would be nice if we don't get this evar *)
    Unshelve. 2: exact 0.
    iIntros "(TE& _& TG& Ggu& _)".
    replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
    iMod (carrier_delete with "TG Ggu") as "TG". 1: set_solver.
    replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
    replace (B ∖ B) with (∅ : oids) by set_solver.
    iApply ("HΦ" with "[$TE $Q_LC $TG $GB]").
  Qed.

  (** TODO: LAT-style spec that enables the client to put crP_obls in some invariant. *)
  Lemma Queue_dequeue_spec :
    ⊢ ∃ μ, ∀ lc m (b : bool) wg i G φ γ ℓ (ql : val) C,
    l{{{ thread_expr i C (Queue.dequeue ql) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g 1%ordi μ) ∗
         (if b
          then queue_worker γ wg
          else True) ∗
         is_queue ql γ ℓ φ }}}
      Queue.dequeue ql @ i
      l{{{ x, RET x; thread_expr i C (of_val x) ∗ £ lc ∗
                     (match x with
                      | NONEV =>
                          (if b
                           then (∃ ng, thP_carriers i ({[ng]} ∪ G) ∗ ⌜ng ∉ G⌝ ∗
                                       queue_worker γ ng ∗ crP_obls wg ℓ ∅ ∗ crP_fuel ng ℓ m)
                           else (thP_carriers i G))
                      | SOMEV v =>
                          (∃ g B, φ v B ∗ crP_obls g ℓ B ∗ crP_fuel g ℓ m ∗ ⌜g ∉ G⌝ ∗
                                  (if b
                                   then (∃ ng, thP_carriers i ({[g; ng]} ∪ G) ∗ ⌜ng ∉ G ∧ g ≠ ng⌝ ∗
                                               queue_worker γ ng ∗ crP_obls wg ℓ ∅ ∗ crP_fuel ng ℓ m)
                                   else (thP_carriers i ({[g]} ∪ G))))
                      | _ => (False)
                      end)
      }}}.
  Proof.
    iPoseProof (TicketLock_acquire_spec) as (ma) "TicketLock_acquire_spec".
    iPoseProof (TicketLock_release_spec) as (mr) "TicketLock_release_spec".
    iExists (100 ⊕ ma ⊕ mr)%M. iIntros (lc μ b wg i G φ γ ℓ ql C) "!> % (TE& TG& GF& HW& #IQ) HΦ".
    rewrite /Queue.dequeue.
    iPoseProof (crP_fuel_add_set with "GF") as "[GF F_m]".
    iPoseProof (crP_fuel_add_set with "F_m") as "[F_ma F_mr]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC TE".
    (** Need ql *)
    iDestruct "IQ" as "(%lhptr&%ltptr&%tl& %Hql& #IQ& #IFLA)". simplify_eq.
    iAssert (queue_ticketlock_γ γ ↪LOCK_AL□ ∗ queue_ticketlock_γ γ ↪LOCK_CF□ 0 ∗
             is_fair_lock tl (queue_ticketlock_γ γ) (queue_lock φ (queue_γq γ) lhptr ltptr))%I as "#IFL".
    { iDestruct "IFLA" as "($& $& IFLA)". iApply (is_fair_lock_alive_is_fair_lock with "IFLA"). }
    lwp_pures.
    (** Acquire lock *)
    lwp_bind (TicketLock.acquire tl).
    iModIntro.
    iApply ("TicketLock_acquire_spec" $! 0 (100 ⊕ mr)%M with "[] [$TE $TG F_ma $IFL]").
    { iPureIntro. set_solver. }
    { iApply crP_fuel_layer_eq_set. 2: iFrame. by rewrite hessenberg.add_O_l. }
    iIntros (gu ku) "(TE& _& %Ningu& TG& Ggu& F_gu& F_ku& _& _& Lock& R)".
    iPoseProof (crP_fuel_add with "F_gu") as "[F_gu F_mr_gu]".
    (* Prepare fuels for the unlock call. *)
    iMod (crP_fuel_layer_mon_set _ 0 with "F_mr") as "F_mr".
    { apply ordArith.le_from_nat. lia. }
    iPoseProof (big_sepS_union_2 with "[F_mr_gu] F_mr") as "F_mr".
    { iApply big_sepS_singleton. iFrame. }
    (* iPoseProof (crP_fuels_init with "F_mr") as "F_mr". *)
    (* iPoseProof (crP_fuels_add_carrier with "F_mr_gu F_mr")as "F_mr". *)
    rewrite (crP_fuel_eq gu 0 _ (96 ⊕ 4)%M); cycle 1.
    { rewrite measure_rep_add !measure_rep_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (crP_fuel_add with "F_gu") as "[F_gu _]".
    iPoseProof (crP_fuels_add_carrier with "F_gu GF") as "GF".
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iDestruct "R" as "(%&%&%& Ptr_lh& Ptr_lt& Queue& QC)".    
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $Ptr_lh]"). 1: done.
    iIntros "[TE ((_& TG& _)& Ptr_lh)]".
    lwp_pure_lc 100.
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    destruct vs as [ | [v B] vs'].
    - (* Queue is empty *)
      iDestruct "QC" as "(%Heq& QC_Ptr_lh)". subst lt.
      iModIntro.
      iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $QC_Ptr_lh]"). 1: done.
      iIntros "[TE ((_& TG& _)& QC_Ptr_lh)]".
      lwp_pures.
      lwp_bind (TicketLock.release tl).
      iMod (inv_acc with "IQ") as "[qinv IQ_ACC]". 1: set_solver.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_lwpupd_add_later with "LC1"). iNext.
      iDestruct "qinv" as "(%&%& Queue0& Gvar& %Disj& Gq& Fq)".
      iPoseProof (own_valid_2 with "Queue Queue0") as "%".
      apply dfrac_agree_op_valid in H. destruct H as [_ ?]. apply leibniz_equiv in H. subst vs.
      destruct b.
      + iPoseProof (ghost_var_agree with "Gvar HW") as "%". simplify_eq. simpl.
        iMod (carrier_alloc _ _ _ ℓ (μ ⊕ 83 ⊕ mr)%M with "TG") as "(%ng& %Ninng& TG& Gng& Fng)".
        iMod (ghost_var_update_2 (ng) with "Gvar HW") as "[Gvar HW]". 1: by rewrite Qp.div_2.
        iModIntro. iMod ("IQ_ACC" with "[Queue0 Gvar Fq Gng]") as "_".
        { iNext. iFrame. simpl. iFrame. iPureIntro. auto. }
        iPoseProof (crP_fuel_add with "Fng") as "[Fng Fng']".
        iPoseProof (crP_fuel_add with "Fng'") as "[Fng' Fng_mr]".
        iMod (crP_fuel_layer_mon _ 0 with "Fng_mr") as "Fng_mr".
        { apply ord.O_bot. }
        iPoseProof (big_sepS_union_2 with "[Fng_mr] F_mr") as "F_mr".
        { iApply big_sepS_singleton. iFrame. }
        (* iPoseProof (crP_fuels_add_carrier with "Fng_mr F_mr") as "F_mr". *)
        iModIntro.
        iDestruct "IFL" as "(AL& CF& IFL)".
        iApply ("TicketLock_release_spec" $! 0 with "[] [$TE $TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC_Ptr_lh]").
        { iPureIntro. set_solver. }
        { iSplit. 1: iPureIntro; set_solver. iFrame. simpl. iFrame. eauto. }
        iIntros "(TE& _& TG& Ggu& _)".
        replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
        iMod (carrier_delete with "TG Ggu") as "TG". 1: set_solver.
        replace (({[ng]} ∪ ({[gu]} ∪ G)) ∖ {[gu]}) with ({[ng]} ∪ G) by set_solver.
        iPoseProof (crP_fuels_remove_carrier gu with "GF") as "GF".
        replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
        iPoseProof (crP_fuels_add_carrier with "Fng' GF")as "GF".
        lwp_pures.
        iModIntro. lwp_finish.
        iApply ("HΦ"). iFrame. iModIntro. iPureIntro. set_solver.
      + iModIntro. iMod ("IQ_ACC" with "[Queue0 Gvar Fq Gq]") as "_".
        { iNext. iFrame. simpl. auto. }
        iModIntro.
        iDestruct "IFL" as "(AL& CF& IFL)".
        iApply ("TicketLock_release_spec" $! 0 with "[] [$TE $TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC_Ptr_lh]").
        { iPureIntro. set_solver. }
        { iSplit. 1: iPureIntro; set_solver. iFrame. simpl. iFrame. eauto. }
        iIntros "(TE& _& TG& Ggu& _)".
        replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
        iMod (carrier_delete with "TG Ggu") as "TG". 1: set_solver.
        iPoseProof (crP_fuels_remove_carrier gu with "GF") as "GF".
        replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
        lwp_pures.
        iModIntro. lwp_finish.
        iApply ("HΦ"). iFrame. by iModIntro.
    - simpl. iDestruct "QC" as "(%ln& QC_Ptr_lh& Hφ& QC)".
      iModIntro.
      iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $QC_Ptr_lh]"). 1: done.
      iIntros "[TE ((_& TG& _)& QC_Ptr_lh)]".
      lwp_pures.
      lwp_bind (Store _ _).
      iModIntro.
      iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_store _ ∅ 0 with "[$TE $TG $GF1 $Ptr_lh]"). 1: done.
      iIntros "[TE ((_& TG& _)& Ptr_lh)]".
      lwp_pures.
      lwp_bind (Free _).
      iModIntro.
      iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
      iApply (lwp_free _ ∅ 0 with "[$TE $TG $GF1 $QC_Ptr_lh]"). 1: done.
      iIntros "(TE& _& TG& _)".
      lwp_pures.
      lwp_bind (TicketLock.release tl).
      iMod (inv_acc with "IQ") as "[qinv IQ_ACC]". 1: set_solver.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_lwpupd_add_later with "LC1"). iNext.
      iDestruct "qinv" as "(%&%& Queue0& Gvar& %Disj& Gq& Fq)".
      iPoseProof (own_valid_2 with "Queue Queue0") as "%".
      apply dfrac_agree_op_valid in H. destruct H as [_ ?]. apply leibniz_equiv in H. subst vs.
      iMod (own_update_2 with "Queue Queue0") as "[Queue Queue0]".
      { eapply (dfrac_agree_update_2 _ _ _ _ (vs')). rewrite dfrac_op_own Qp.div_2. auto. }
      destruct b.
      + iPoseProof (ghost_var_agree with "Gvar HW") as "%". simplify_eq.
        rewrite !fmap_cons. iPoseProof (big_sepL_cons with "Fq") as "[FB Fq]".
        simpl.
        iAssert (([∗ list] k↦y ∈ vs'.*2, [∗ set] b ∈ y, oblP_fuel b ℓ (S k)) ∗
                 ([∗ list] k↦y ∈ vs'.*2, [∗ set] b ∈ y, oblP_fuel b ℓ 1))%I
          with "[Fq]" as "[Fq F]".
        { iApply big_sepL_sep. iApply (big_sepL_impl with "Fq"). iIntros "!> %% % H".
          iPoseProof (oblP_fuel_eq_set _ _ _ ((S k) ⊕ 1)%M with "H") as "H".
          { rewrite measure_rep_add !measure_rep_nat. rewrite -Hessenberg.add_from_nat.
            replace (S (S k)) with (S k + 1) by lia. done. }
          iApply (oblP_fuel_add_set with "H"). }
        iMod (carrier_alloc _ _ _ ℓ (μ ⊕ 76 ⊕ mr)%M with "TG") as "(%g& %Ning& TG& Gg& Fg)".
        iMod (obl_offload_set with "Gq Gg FB") as "(Gq& Gg& %)". 1: set_solver. 1: done.
        assert (B ## union_list_of_sets vs'.*2 ∧ disjoint_list_of_sets vs'.*2).
        { rewrite fmap_cons in Disj. apply disjoint_list_of_sets_cons_inv in Disj. auto. }
        destruct H0 as (DisjB& Disj').
        replace ((B ∪ union_list_of_sets vs'.*2) ∖ B) with (union_list_of_sets vs'.*2) by set_solver.
        iMod (carrier_alloc _ _ _ ℓ (μ ⊕ 76 ⊕ mr)%M with "TG") as "(%ng& %Ninng& TG& Gng& Fng)".
        iMod (ghost_var_update_2 (ng) with "Gvar HW") as "[Gvar HW]". 1: by rewrite Qp.div_2.
        iAssert ([∗ set] b ∈ union_list_of_sets vs'.*2, oblP_fuel b ℓ 1)%I with "[F]" as "F".
        { iClear "TicketLock_acquire_spec TicketLock_release_spec IQ IFL".
          remember (vs'.*2) as l. clear dependent vs'. clear DisjB Disj'. iInduction l as [ | ]. 1: done.
          iPoseProof (big_sepL_cons with "F") as "[Fb F]".
          iPoseProof ("IHl" with "F") as "F".
          rewrite union_list_of_sets_cons. iApply (big_sepS_union_2 with "Fb F"). }
        iMod (obl_offload_set with "Gq Gng F") as "(Gq& Gng& %)". 1: set_solver. 1: done.
        replace (union_list_of_sets vs'.*2 ∖ union_list_of_sets vs'.*2) with (∅ : oids) by set_solver.
        rewrite !union_empty_l_L.
        iModIntro. iMod ("IQ_ACC" with "[Queue0 Gvar Gng Fq]") as "_".
        { iNext. iFrame. iPureIntro. auto. }
        iModIntro.
        iPoseProof (crP_fuel_add with "Fg") as "(Fg_Q& Fg)".
        iPoseProof (crP_fuel_add with "Fg") as "(Fg& Fg_mr)".
        iPoseProof (crP_fuel_add with "Fng") as "(Fng_Q& Fng)".
        iPoseProof (crP_fuel_add with "Fng") as "(Fng& Fng_mr)".
        iMod (crP_fuel_layer_mon _ 0 with "Fg_mr") as "Fg_mr".
        { apply ord.O_bot. }
        iPoseProof (big_sepS_union_2 with "[Fg_mr] F_mr") as "F_mr".
        { iApply big_sepS_singleton. iFrame. }
        iMod (crP_fuel_layer_mon _ 0 with "Fng_mr") as "Fng_mr".
        { apply ord.O_bot. }
        iPoseProof (big_sepS_union_2 with "[Fng_mr] F_mr") as "F_mr".
        { iApply big_sepS_singleton. iFrame. }
        (* iPoseProof (crP_fuels_add_carrier with "Fg_mr F_mr") as "F_mr". *)
        (* iPoseProof (crP_fuels_add_carrier with "Fng_mr F_mr") as "F_mr". *)
        iDestruct "IFL" as "(AL& CF& IFL)".
        iApply ("TicketLock_release_spec" $! 0 with "[] [$TE $TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC]").
        { iPureIntro. set_solver. }
        { iSplit. 1: iPureIntro; set_solver. iFrame. eauto. }
        iIntros "(TE& _& TG& Ggu& _)".
        replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
        iMod (carrier_delete with "TG Ggu") as "TG". 1: set_solver.
        iPoseProof (crP_fuels_add_carrier with "Fg GF") as "GF".
        iPoseProof (crP_fuels_add_carrier with "Fng GF") as "GF".
        iPoseProof (crP_fuels_remove_carrier gu with "GF") as "GF".
        replace (({[ng]} ∪ ({[g]} ∪ ({[gu]} ∪ G))) ∖ {[gu]}) with (({[ng]} ∪ ({[g]} ∪ G))) by set_solver.
        lwp_pures.
        iModIntro. lwp_finish.
        iModIntro. iApply "HΦ". iFrame "TE Q_LC".
        iExists g. iFrame. iSplit.
        { iPureIntro. set_solver. }
        iSplit.
        { replace ({[ng]} ∪ ({[g]} ∪ G)) with ({[g; ng]} ∪ G) by set_solver. iFrame. }
        { iPureIntro. split_and !; set_solver. }
      + rename g into ng. rewrite !fmap_cons. iPoseProof (big_sepL_cons with "Fq") as "[FB Fq]".
        simpl.
        iAssert (([∗ list] k↦y ∈ vs'.*2, [∗ set] b ∈ y, oblP_fuel b ℓ (S k)) ∗
                 ([∗ list] k↦y ∈ vs'.*2, [∗ set] b ∈ y, oblP_fuel b ℓ 1))%I
          with "[Fq]" as "[Fq F]".
        { iApply big_sepL_sep. iApply (big_sepL_impl with "Fq"). iIntros "!> %% % H".
          iPoseProof (oblP_fuel_eq_set _ _ _ ((S k) ⊕ 1)%M with "H") as "H".
          { rewrite measure_rep_add !measure_rep_nat. rewrite -Hessenberg.add_from_nat.
            replace (S (S k)) with (S k + 1) by lia. done. }
          iApply (oblP_fuel_add_set with "H"). }
        iMod (carrier_alloc _ _ _ ℓ (μ ⊕ 76 ⊕ mr)%M with "TG") as "(%g& %Ning& TG& Gg& Fg)".
        iMod (obl_offload_set with "Gq Gg FB") as "(Gq& Gg& %)". 1: set_solver. 1: done.
        assert (B ## union_list_of_sets vs'.*2 ∧ disjoint_list_of_sets vs'.*2).
        { rewrite fmap_cons in Disj. apply disjoint_list_of_sets_cons_inv in Disj. auto. }
        destruct H0 as (DisjB& Disj').
        replace ((B ∪ union_list_of_sets vs'.*2) ∖ B) with (union_list_of_sets vs'.*2) by set_solver.
        rewrite !union_empty_l_L.
        iModIntro. iMod ("IQ_ACC" with "[Queue0 Gvar Gq Fq]") as "_".
        { iNext. iFrame. iPureIntro. auto. }
        iModIntro.
        iPoseProof (crP_fuel_add with "Fg") as "(Fg_Q& Fg)".
        iPoseProof (crP_fuel_add with "Fg") as "(Fg& Fg_mr)".
        iMod (crP_fuel_layer_mon _ 0 with "Fg_mr") as "Fg_mr".
        { apply ord.O_bot. }
        iPoseProof (big_sepS_union_2 with "[Fg_mr] F_mr") as "F_mr".
        { iApply big_sepS_singleton. iFrame. }
        (* iPoseProof (crP_fuels_add_carrier with "Fg_mr F_mr") as "F_mr". *)
        iDestruct "IFL" as "(AL& CF& IFL)".
        iApply ("TicketLock_release_spec" $! 0 with "[] [$TE $TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC]").
        { iPureIntro. set_solver. }
        { iSplit. 1: iPureIntro; set_solver. iFrame. eauto. }
        iIntros "(TE& _& TG& Ggu& _)".
        replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
        iMod (carrier_delete with "TG Ggu") as "TG". 1: set_solver.
        iPoseProof (crP_fuels_add_carrier with "Fg GF") as "GF".
        iPoseProof (crP_fuels_remove_carrier gu with "GF") as "GF".
        replace (({[g]} ∪ ({[gu]} ∪ G)) ∖ {[gu]}) with (({[g]} ∪ G)) by set_solver.
        lwp_pures.
        iModIntro. lwp_finish.
        iModIntro. iApply "HΦ". iFrame "TE Q_LC".
        iExists g. iFrame. iPureIntro. set_solver.
  Qed.

  (** ** Temporal guarantees *)
  (** The queue has no trace content beyond its lock's: [queue_inv] is ghost state, and the
      lock resource [queue_lock] is the [R] of the lock, to which the lock's guarantee gives
      [tps_true]. Since [is_queue] keeps [γ ↪LOCK_AL□], its lock cannot be deleted, so the
      queue guarantees what a lock that cannot be deleted guarantees
      ([is_fair_lock_alive_temporal]). *)
  Definition queue_tps (ql : val) : tps heap_lang Σ :=
    (∃ (lhptr ltptr : loc) (tl : val), ⌜ql = (#lhptr, #ltptr, tl)%V⌝ ∧ alive_fair_lock_tps tl)%S.

  Lemma is_queue_temporal ql γ ℓ φ : ⊢ is_queue ql γ ℓ φ ⊨ₜ queue_tps ql.
  Proof.
    iApply (temporal_mono (∃ (lhptr ltptr : loc) (tl : val), ⌜ql = (#lhptr, #ltptr, tl)%V⌝ ∧
      is_fair_lock_alive tl (queue_ticketlock_γ γ) (queue_lock φ (queue_γq γ) lhptr ltptr))%I with "[]").
    { iIntros "!> (%&%&%& %& _& _& _& #IFL)". iExists _, _, _. iSplit; first done.
      iFrame "#". }
    iApply (into_temporal _ _).
  Qed.

  Global Instance is_queue_into_temporal ql γ ℓ φ :
    IntoTemporal (is_queue ql γ ℓ φ) (queue_tps ql) | 0.
  Proof. apply is_queue_temporal. Qed.

  Lemma is_queue_init_temporal ql γ φ : ⊢ is_queue_init ql γ φ ⊨ₜ queue_tps ql.
  Proof.
    iApply (temporal_mono (∃ (lhptr ltptr : loc) (tl : val), ⌜ql = (#lhptr, #ltptr, tl)%V⌝ ∧
      is_fair_lock_alive tl (queue_ticketlock_γ γ) (queue_lock φ (queue_γq γ) lhptr ltptr))%I with "[]").
    { iIntros "!> (%&%&%& %& _& _& _& _& #IFL)". iExists _, _, _. iSplit; first done.
      iFrame "#". }
    iApply (into_temporal _ _).
  Qed.

End proof.

(** ** Progress of the queue's lock, at the level of traces *)
Section trace.

  (** The queue's lock makes release progress ([release_progress]): every [enqueue] or
      [dequeue] that takes the lock eventually releases it. *)
  Lemma queue_release_progress {Σ} ql τ :
    tps_tr (queue_tps (Σ:=Σ) ql) τ →
    ∃ lhptr ltptr next curr : loc,
      ql = (#lhptr, #ltptr, (#next, #curr))%V ∧ release_progress next curr τ.
  Proof.
    intros (lhptr & ltptr & tl & -> & Htl).
    destruct (alive_fair_lock_release_progress (Σ:=Σ) tl τ Htl) as (next & curr & -> & Hrp).
    by exists lhptr, ltptr, next, curr.
  Qed.

End trace.
