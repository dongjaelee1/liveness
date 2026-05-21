From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From iris.algebra Require Import reservation_map dfrac_agree mono_list gset.
From transfinite.base_logic.lib Require Import ghost_var ghost_map.

From liris.heap_lang.examples Require Import ticket_lock.

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

  (* FIXME: move to other file *)
  Definition put_task : val :=
    λ: "q" "f" "a",
      enqueue "q" ("f", "a").

  Definition run_task : val :=
    λ: "q",
      match: dequeue "q" with
        NONE => #()
      | SOME "fa" =>
          let: "f" := Fst "fa" in
          let: "a" := Snd "fa" in
          "f" "a"
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
  gFunctors.app
    #[GFunctor (dfrac_agreeR (list (val * oids)))]
    (ghost_varΣ (thread_id * ogid)).

Global Instance subG_queueΣ {Σ} : subG queueΣ Σ → queueGpreS Σ.
Proof. solve_inG. Qed.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances queue_inG queueGpreS_queue queueGpreS_data_inG.

Section proof.
  Context `{!heapGS Σ, !queueG Σ, !ticket_lockG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pures := repeat (iModIntro; lwp_pure; post_lwp).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (iModIntro; lwp_pure; post_lwp_lc n).

  (** ** Definitions *)

  Let N := nroot.@"queue".
  Let Ni := N.@"invariant".

  Record queue_γ :=
    QueueName {
        queue_ticketlock_γ : ticketlock_γ;
        queue_γq : gname;
        queue_γd : gname;
      }.

  Definition qG_queue γ (l : list (val * oids)) q : iProp Σ :=
    own γ (to_dfrac_agree (DfracOwn q) l).

  Fixpoint queue_contents (lh lt : loc) (vs : list (val * oids)) (φ : val → oids → iProp Σ) : iProp Σ :=
    match vs with
    | [] => (⌜lh = lt⌝ ∗ lh ↦ NONEV)
    | (v, B) :: vs => (∃ l : loc, lh ↦ SOMEV (v, #l) ∗ φ v B ∗ queue_contents l lt vs φ)
    end%I.

  (* Mostly protects ghost resources + sync using qG_queue *)
  Local Definition queue_inv (ℓ : ord.t) γq γd : iProp Σ :=
    (∃ (vs : list (val * oids)) (i : thread_id) (g : ogid),
        qG_queue γq vs (1/2)%Qp ∗
        ghost_var γd (1/2)%Qp (i, g) ∗
        ogP_obls i g ℓ (foldr (λ B A, B ∪ A) ∅ (vs.*2)) ∗
        ([∗ list] n ↦ B ∈ (vs.*2), [∗ set] b ∈ B, oblP_fuel b (ℓ)%ordi (n ⊕ 1)%M))%I.

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
      is_fair_lock tl (queue_ticketlock_γ γ) 0 (queue_lock φ (queue_γq γ) lhptr ltptr).

  (** Enables delayed initialization after picking a worker thread. *)
  Definition is_queue_init (ql :val) (γ : queue_γ) (φ : val → oids → iProp Σ) : iProp Σ :=
    (∃ (lhptr ltptr : loc) (tl : val),
        ⌜ql = (#lhptr, #ltptr, tl)%V⌝ ∧
        qG_queue (queue_γq γ) [] (1/2)%Qp ∗
        ghost_var (queue_γd γ) 1 (inhabitant, inhabitant) ∗
        is_fair_lock tl (queue_ticketlock_γ γ) 0 (queue_lock φ (queue_γq γ) lhptr ltptr))%I.

  (** ** Lemmas *)

  Global Instance is_queue_persistent ql γ ℓ φ : Persistent (is_queue ql γ ℓ φ).
  Proof. rewrite /is_queue. apply _. Qed.

  Lemma is_queue_initialize E ql γ (ℓ : ord.t) (φ : val → oids → iProp Σ) i g :
    is_queue_init ql γ φ -∗ ogP_obls i g ℓ ∅ ={E}=∗ is_queue ql γ ℓ φ ∗ ghost_var (queue_γd γ) (1/2)%Qp (i, g).
  Proof.
    iIntros "(%&%&%& %Hq& Qvs& GVd& #FL) Go".
    rewrite /is_queue.
    iMod (ghost_var_update (i, g) with "GVd") as "[GVd $]".
    iMod (inv_alloc Ni _ (queue_inv ℓ (queue_γq γ) (queue_γd γ)) with "[Qvs GVd Go]") as "#Invq".
    { iNext. rewrite /queue_inv. iFrame. iSplitL; last done. iFrame. }
    iModIntro. iFrame "FL Invq". auto.
  Qed.

  (** ** Program proofs *)
  (** FIXME: better notation for triples with this pattern *)
  Lemma Queue_init_spec :
    ⊢ ∃ m, ∀ i G φ lc,
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g 0 m) }}}
      Queue.init #() @ i
    l{{{ ql γ, RET ql; £ lc ∗ thP_groups i G ∗ is_queue_init ql γ φ }}}.
  Proof.
    iPoseProof (TicketLock_init_spec) as (m) "TicketLock_init_spec".
    iExists (20 ⊕ m)%M. iIntros (i G φ lc) "!> % (TG& GF) HΦ".
    rewrite /Queue.init.
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF F_TicketLock]".
    lwp_lam. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_pures.
    (** Alloc node ptr *)
    iPoseProof (ogP_fuel_eq_set _ 0 _ (17 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    lwp_bind (AllocN _ _).
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ptr_node) "((_& TG& _)& Ptr_node& _)".
    lwp_pures.
    (** Alloc hd ptr *)
    iPoseProof (ogP_fuel_eq_set _ 0 _ (14 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    lwp_bind (AllocN _ _).
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (lhptr) "((_& TG& _)& Ptr_hd& _)".
    lwp_pures.
    (** Alloc tl ptr *)
    iPoseProof (ogP_fuel_eq_set _ 0 _ (11 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    lwp_bind (AllocN _ _).
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ltptr) "((_& TG& _)& Ptr_tl& _)".
    lwp_pures.
    (** Init TicketLock *)
    (** FIXME: better tactic for function calls *)
    lwp_bind (TicketLock.init #()).
    iMod (own_alloc (to_dfrac_agree (DfracOwn (1/2)) ([] : list (val * oids)) ⋅ to_dfrac_agree (DfracOwn (1/2)) ([] : list (val * oids)))) as (γq) "[HQvs HQvs0]".
    { rewrite -dfrac_agree_op. done. }
    iModIntro.
    iApply ("TicketLock_init_spec" $! _ _ 0 (queue_lock φ γq lhptr ltptr)%I 0
             with "[$TG $F_TicketLock Ptr_node Ptr_hd Ptr_tl HQvs0]").
    { iFrame. eauto. }
    iIntros (tl γtl) "(_& TG& #IFL)".
    lwp_pures.
    iModIntro. lwp_finish.
    iMod (ghost_var_alloc (inhabitant : thread_id, inhabitant : ogid)) as (γd) "Gv".
    iApply ("HΦ" $! _ (QueueName γtl γq γd)).
    iModIntro. iFrame "TG Q_LC".
    rewrite /is_queue_init. iFrame "HQvs Gv IFL". auto.
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
    ⊢ ∃ m, ∀ i G g B φ lc γ ℓ ℓ' (ql x : val),
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g ℵ%ordi m) ∗
         ogP_obls i g ℓ' B ∗ ([∗ set] b ∈ B, oblP_fuel b (ℓ ⊕ 1)%ordi 1) ∗
         φ x B ∗
         is_queue ql γ ℓ φ }}}
      Queue.enqueue ql x @ i
    l{{{ RET #(); £ lc ∗ thP_groups i G ∗ ogP_obls i g ℓ' ∅ }}}.
  Proof.
    iPoseProof (TicketLock_acquire_spec) as (ma) "TicketLock_acquire_spec".
    iPoseProof (TicketLock_release_spec) as (mr) "TicketLock_release_spec".
    iExists (1 ⊕ ma ⊕ mr)%M. iIntros (i G g B φ lc γ ℓ ℓ' ql x) "!> % (TG& Fs& GB& FB& Hφ& #IQ) HΦ".
    rewrite /Queue.enqueue.
    iPoseProof (ogP_fuel_add_set with "Fs") as "[GF F_m]".
    iPoseProof (ogP_fuel_add_set with "F_m") as "[F_ma F_mr]".
    iMod (ogP_fuel_extend_set _ 0 _ (100)%M with "GF") as "GF".
    { unshelve etrans. 1: exact 1.
      { eapply ordArith.lt_from_nat. lia. }
      rewrite ord.from_nat_from_peano_lt. apply ord.large_lt_from_wf. }
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ Q_LC".
    lwp_pures.
    (** Need ql *)
    iDestruct "IQ" as "(%&%&%& %Hql& #IQ& #IFL)". simplify_eq.
    lwp_pures.
    (** Acquire lock *)
    lwp_bind (TicketLock.acquire tl).
    iModIntro.
    iApply ("TicketLock_acquire_spec" $! _ _ _ _ _ _ (100 ⊕ mr)%M 0 with "[$TG F_ma $IFL]").
    { iApply ogP_fuel_layer_eq_set. 2: iFrame. by rewrite hessenberg.add_O_l. }
    iIntros (gu ku) "(_& %Ningu& TG& Ggu& F_gu& F_ku& Lock& R)".
    iPoseProof (ogP_fuel_add with "F_gu") as "[F_gu F_mr_gu]".
    rewrite (ogP_fuel_eq gu 0 _ (94 ⊕ 6)%M); cycle 1.
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add with "F_gu") as "[F_gu _]".
    iPoseProof (big_sepS_union _ {[gu]} G with "[$GF F_gu]") as "GF". 1: set_solver.
    { iApply big_sepS_singleton. auto. }
    lwp_pures.
    iPoseProof (ogP_fuel_eq_set _ 0 _ (87 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    iDestruct "R" as "(%&%&%& Ptr_lh& Ptr_lt& Queue& QC)".    
    lwp_bind (Load _).
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $Ptr_lt]"). 1: done.
    iIntros "((_& TG& _)& Ptr_lt)".
    lwp_pures.
    iPoseProof (ogP_fuel_eq_set _ 0 _ (83 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    lwp_bind (AllocN _ _).
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (ptr_newt) "((_& TG& _)& Ptr_newt& _)".
    lwp_pure_lc 100.
    lwp_pures.
    (** Physical enqueue *)
    lwp_bind (Store _ _).
    iPoseProof (queue_contents_enqueue with "QC") as "(QC_Ptr_lt& QC_ACC)".
    iModIntro.
    iPoseProof (ogP_fuel_eq_set _ 0 _ (78 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    iApply (lwp_store _ ∅ 0 with "[$TG $GF1 $QC_Ptr_lt]"). 1: done.
    iIntros "((_& TG& _)& QC_Ptr_lt)".
    iPoseProof ("QC_ACC" with "QC_Ptr_lt Hφ Ptr_newt") as "QC".
    lwp_pures.
    lwp_bind (Store _ _).
    iModIntro.
    iPoseProof (ogP_fuel_eq_set _ 0 _ (75 ⊕ 1)%M with "GF") as "GF".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (ogP_fuel_add_set with "GF") as "[GF GF1]".
    iApply (lwp_store _ ∅ 0 with "[$TG $GF1 $Ptr_lt]"). 1: done.
    iIntros "((_& TG& _)& Ptr_lt)".
    lwp_pures.
    iMod (inv_acc with "IQ") as "[qinv IQ_ACC]". 1: set_solver.
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lc_lwpupd_add_later with "LC1"). iNext.
    iDestruct "qinv" as "(%&%&%& Queue0& Gvar& Gq& Fq)".
    iPoseProof (own_valid_2 with "Queue Queue0") as "%".
    apply dfrac_agree_op_valid in H. destruct H as [_ ?]. apply leibniz_equiv in H. subst vs0.
    iMod (own_update_2 with "Queue Queue0") as "[Queue Queue0]".
    { eapply (dfrac_agree_update_2 _ _ _ _ (vs ++ [(x, B)])). rewrite dfrac_op_own Qp.div_2. auto. }
    iMod (oblP_fuel_extend_set _ ℓ _ (1 ⊕ ℵ)%M with "FB") as "FB".
    { apply hessenberg.add_lt_l. apply ord.S_lt. }
    iPoseProof (oblP_fuel_add_set with "FB") as "[FB FBq]".
    iMod (obl_offload_set with "GB Gq FB") as "(GB& Gq& %HG)". 1: set_solver. 1: by left.
    iMod (oblP_fuel_mon_set _ _ (length (vs.*2) ⊕ 1)%M with "FBq") as "FBq".
    { rewrite measure_add !measure_nat measure_large. apply Ord.lt_le. unshelve etrans. 1: exact ω%ord.
      - rewrite -Hessenberg.add_from_nat. apply Ord.omega_upperbound.
      - rewrite Ord.omega_from_peano_lt_set. apply Ord.large_lt_from_wf_set. }
    iModIntro.
    iMod ("IQ_ACC" with "[Queue0 Gvar Gq Fq FBq]") as "_".
    { iNext. iFrame "Queue0 Gvar". iSplitL "Gq".
      - rewrite fmap_app foldr_snoc. simpl.
        replace (foldr (λ B0 A : oids, B0 ∪ A) ∅ vs.*2 ∪ B) with (foldr (λ B0 A : oids, B0 ∪ A) (B ∪ ∅) vs.*2).
        1: iFrame.
        set (gB := λ A, A ∪ B).
        replace (B ∪ ∅) with (gB ∅) by set_solver.
        replace (foldr (λ B0 A : oids, B0 ∪ A) ∅ vs.*2 ∪ B) with (gB (foldr (λ B0 A : oids, B0 ∪ A) ∅ vs.*2)) by set_solver.
        eapply foldr_comm_acc. intros. subst gB. simpl. set_solver.
      - rewrite fmap_app. simpl. iApply big_sepL_app. iFrame.
        iApply big_sepL_singleton. iApply oblP_fuel_eq_set. 2: iFrame.
        rewrite !measure_add. replace (length vs.*2 + 0)%nat with (length vs.*2)%nat by lia. done. }
    iModIntro.
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
    iApply lwp_sfmupd.
    iApply ("TicketLock_release_spec" with "[$TG $F_mr $Ggu $IFL $Lock Ptr_lh Ptr_lt Queue QC]").
    { iSplit. 1: iPureIntro; set_solver. iFrame. }
    (* FIXME: it would be nice if we don't get this evar *)
    Unshelve. 2: exact 0.
    iIntros "(_& TG& Ggu)".
    replace ({[ku]} ∖ {[ku]}) with (∅ : oids) by set_solver.
    iMod (group_delete with "TG Ggu") as "TG". replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
    replace (B ∖ B) with (∅ : oids) by set_solver.
    iApply ("HΦ" with "[$Q_LC $TG $GB]").
  Qed.



    TODO


    (* Also dequeue_main for the main (bounded) worker, or a nice representation for both cases *)
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

End proof.



(* old stuff *)
Variant queue_op : Set :=
  | op_enq (v : val)
  | op_deq (v : option val) (w : positive) (k : oid)
.

Canonical Structure queue_opO : ofe := leibnizO queue_op.

(** The CMRA we need. *)
Class lqueueGpreS (Σ : gFunctors) : Set :=
  LqueueGpreS {
      lqueueGpreS_queue : inG Σ (dfrac_agreeR (list val));
      lqueueGpreS_log : inG Σ (mono_listUR (queue_op));
      lqueueGpreS_workers : inG Σ (reservation_mapUR (mono_listUR (oid)));
    }.

Class lqueueG Σ :=
  LqueueG {
      #[local] lqueue_inG :: lqueueGpreS Σ;
      lqueue_queue_name : gname;
      lqueue_log_name : gname;
      lqueue_workers_name : gname;
    }.

Definition lqueueΣ : gFunctors :=
  #[GFunctor (dfrac_agreeR (list val)); GFunctor (mono_listUR (queue_op)); (GFunctor (reservation_mapUR (mono_listUR (oid))))].

Global Instance subG_lqueueΣ {Σ} : subG lqueueΣ Σ → lqueueGpreS Σ.
Proof. solve_inG. Qed.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances lqueue_inG lqueueGpreS_queue lqueueGpreS_log lqueueGpreS_workers.

Section defs.
  Context `{!heapGS Σ, !lqueueG Σ, !ticket_lockG Σ}.

  Definition lqG_queue (l : list val) q : iProp Σ :=
    own lqueue_queue_name (to_dfrac_agree (DfracOwn q) l).

  Definition lqG_log (l : list queue_op) : iProp Σ :=
    own lqueue_log_name (●ML l).

  Definition lqG_log_p (l : list queue_op) : iProp Σ :=
    own lqueue_log_name (◯ML l).

  Definition lqG_worker (w : positive) (l : list (oid)) (q : Qp) : iProp Σ :=
    own lqueue_workers_name (reservation_map_data w (●ML{#q} l)).

  Definition lqG_worker_p (w : positive) (l : list (oid)) : iProp Σ :=
    own lqueue_workers_name (reservation_map_data w (◯ML l)).

  Local Definition lqG_worker_token (E : coPset) : iProp Σ :=
    own lqueue_workers_name (reservation_map_token (A:=(mono_listUR (oid))) E).

  Fixpoint queue_contents (lh lt : loc) (vs : list val) (φ : val → iProp Σ) : iProp Σ :=
    match vs with
    | [] => ⌜lh = lt⌝
    | v :: vs => ∃ l : loc, lh ↦ SOMEV (v, #l) ∗ φ v ∗ queue_contents l lt vs φ
  end%I.

  Let N := nroot.@"live_queue".
  Let Nwe := N.@"worker_eventually".
  Let Ni := N.@"invariant".

  Definition lq_inv (ℓ : layer) : iProp Σ :=
    (∃ (vs : list val) (log : list queue_op) (ws : gmap positive (list oid)),
        lqG_queue vs (1/2)%Qp ∗
        lqG_log log ∗
        lqG_worker_token (⊤ ∖ gset_to_coPset (dom ws)) ∗
        (⌜ ∃ w, is_Some (ws !! w) ⌝) ∗
        ([∗ map] w ↦ ks ∈ ws,
           lqG_worker w ks (1/2)%Qp ∗
           ∃ ks_p k, (⌜ks = ks_p ++ [k]⌝) ∗
                     ([∗ list] k ∈ ks_p, oblP_fulfilled k) ∗
                     (oblP_id k ∗ witP_layer k ℓ ∗ ⟦tf_eventually Nwe k false (1/2) (⌜ True ⌝)⟧ₗ))
    )%I.

  Definition lq (ℓ : layer) (φ : val → iProp Σ) γt γa lnc ℓ : iProp Σ :=
    inv Ni (lq_inv ℓ) ∗
    is_fair_lock γt γa lnc ℓ (⟨∃ lh lt vs, queue_contents lh lt vs φ ∗ lqG_queue vs (1/2)%Qp⟩).

End defs.

TODO

(**
  - lock invariant holds queue_contents
  - the problem: when a client enqueues a task,
    it needs to get some obligation that can eventually lead to
    fulfilling whatever obligation client specifies with the task.
    1. the queue makes progress and eventually the task is dequeued by some worker
    2. the worker runs the task, and the task requires some obligation to fulfill P as a precondition
    3. so the client waits on "eventually (eventually P)"
       - no one knows which worker will take the task, so a client waits for "eventually (# > my task #)"
         + no one worker thread is responsible for this, but concurrent workers have their local views
         + need to ensure that to dequeue a task, worker must also increase its view.
         + when the queue is empty, all task # until know should have been dequeued.
       - we need "always (task with # is done ∨ eventually (task with # starts ∧ eventually P))"

worker proto: always (∃ k, eventually k (queue is empty ∨ pop and run a task))

 *) 

Class queueG Σ := {
  queueG_inG :: inG Σ (prodR fracR (agreeR (listO valO)));
  queueG_dequeue_inG :: inG Σ (exclR unitO);
  queueG_enqueue_inG :: inG Σ (authR (optionUR (exclR locO)))
}.

Record queue_name := QueueName {
  queue_fcinv_name : fcinv_name;
  queue_own_name : gname;
  queue_dequeue_name : gname;
  queue_enqueue_name : gname;
}.

(*
Definition queueΣ : gFunctors := #[GFunctor queueCmra; GFunctor fracR;
  GFunctor (exclR unitO); fcinvΣ].

Instance subG_queueΣ {Σ} : subG queueΣ Σ → queueG Σ.
Proof. solve_inG. Qed.
*)

Definition queue_own_def `{queueG Σ} (γ : queue_name)
    (q : Qp) (xs : list val) : ironProp Σ :=
  (<affine> ⎡ own (queue_own_name γ) (q, to_agree xs) ⎤)%I.
Definition queue_own_aux `{queueG Σ} : seal (queue_own_def). by eexists. Qed.
Definition queue_own `{queueG Σ} := unseal queue_own_aux.
Definition queue_own_eq `{queueG Σ} : queue_own = _ := seal_eq queue_own_aux.

Notation "γ ⤇{ q } xs" := (queue_own γ q xs)
  (at level 20, q at level 50, format "γ  ⤇{ q }  xs") : bi_scope.

Definition queue_inv `{heapGS Σ, queueG Σ} (γ : queue_name)
    (lhptr ltptr : loc) : ironProp Σ :=
  (∃ (lh lt : loc) (vs : list val),
    γ ⤇{1/2} vs ∗
    lhptr ↦{1/2} #lh ∗
    <affine> ⎡ own (queue_enqueue_name γ) (● (Excl' lt)) ⎤ ∗
    match vs with
    | [] => <affine> ⌜ lh = lt ⌝
    | v :: vs => ∃ l : loc,
       (lh ↦{1} SOMEV (v, #l)
        ∨ <affine> ⎡ own (queue_dequeue_name γ) (Excl ()) ⎤ ∗
        lh ↦{1/2} SOMEV (v, #l)) ∗
       queue_contents l lt vs
    end ∗
    lt ↦ NONEV)%I.

Definition is_queue `{heapGS Σ, queueG Σ} (N : namespace)
    (γ : queue_name) (q : val) : ironProp Σ :=
  (∃ lhptr ltptr : loc,
    ⌜q = (#lhptr, #ltptr)%V⌝ ∧
    fcinv N (queue_fcinv_name γ) (queue_inv γ lhptr ltptr))%I.

Definition queue_cancel_own `{heapGS Σ, queueG Σ}
    (γ : queue_name) (p : frac) : ironProp Σ :=
  fcinv_cancel_own (queue_fcinv_name γ) p.

Definition enqueue_handle `{heapGS Σ, queueG Σ}
    (γ : queue_name) (q : val) : ironProp Σ :=
  (∃ lhptr ltptr lt : loc,
    ⌜q = (#lhptr, #ltptr)%V⌝ ∧
    fcinv_own (queue_fcinv_name γ) (1/2) ∗
    <affine> ⎡ own (queue_enqueue_name γ) (◯ (Excl' lt)) ⎤ ∗
    ltptr ↦ #lt)%I.

Definition dequeue_handle `{heapGS Σ, queueG Σ}
    (γ: queue_name) (q : val) : ironProp Σ :=
  (∃ (lhptr ltptr : loc) v,
    ⌜q = (#lhptr, #ltptr)%V⌝ ∧
    fcinv_own (queue_fcinv_name γ) (1/2) ∗
    lhptr ↦{1/2} v ∗
    <affine> ⎡ own (queue_dequeue_name γ) (Excl ()) ⎤)%I.

Section queue_own.
  Context `{!queueG Σ}.

  Global Instance queue_own_affine γ q vs : Affine (queue_own γ q vs).
  Proof. rewrite queue_own_eq. apply _. Qed.
  Global Instance queue_own_uniform `{heapGS Σ} γ q vs : Uniform (queue_own γ q vs).
  Proof. apply affine_uniform, _. Qed.

  Global Instance queue_own_fractional γ vs : Fractional (λ q, queue_own γ q vs).
  Proof.
    rewrite queue_own_eq /queue_own_def=> p q; iSplit.
    - iIntros "[$$]".
    - iIntros "[H1 H2]". by iSplitL "H1".
  Qed.
  Global Instance makeElem_as_fractional γ vs q :
    AsFractional (γ ⤇{q} vs) (λ q, queue_own γ q vs) q.
  Proof. split. done. apply _. Qed.

  Global Instance queue_own_timeless γ p vs : Timeless (γ ⤇{p} vs).
  Proof. rewrite queue_own_eq. apply fracPred_at_timeless_alt. apply _. Qed.

  Lemma queue_own_agree γ p q vs ws : γ ⤇{p} vs -∗ γ ⤇{q} ws -∗ ⌜vs = ws⌝.
  Proof.
    rewrite queue_own_eq /queue_own_def; iIntros "H1 H2".
    by iCombine "H1 H2" gives %[_ ?%to_agree_op_inv_L].
  Qed.
  Lemma queue_own_update γ vs vs' : γ ⤇{1} vs ==∗ γ ⤇{1} vs'.
  Proof.
    rewrite queue_own_eq /queue_own_def. iIntros "H".
    iMod (own_update with "H") as "$"; last by auto.
    by apply cmra_update_exclusive.
  Qed.
  Lemma queue_own_update_2 γ vs vs' vs'' :
    γ ⤇{1/2} vs -∗ γ ⤇{1/2} vs' ==∗ γ ⤇{1} vs''.
  Proof.
    iIntros "H1 H2". iDestruct (queue_own_agree with "H1 H2") as %->.
    iCombine "H1 H2" as "H". by iApply queue_own_update.
  Qed.
End queue_own.

Section queue_spec.
  Context `{!heapGS Σ, !queueG Σ} (N : namespace).
  Implicit Types E : coPset.
  Implicit Types P Q : ironProp Σ.

  Instance queue_contents_uniform lh lt vs : Uniform (queue_contents lh lt vs).
  Proof. revert lh. induction vs; apply _. Qed.
  Instance queue_inv_uniform γ lhptr ltptr :
    Uniform (queue_inv γ lhptr ltptr).
  Proof. repeat (apply exist_uniform=> ?); case_match; apply _. Qed.

  Global Instance is_queue_persistent γ q : Persistent (is_queue N γ q).
  Proof. apply _. Qed.
  Global Instance is_queue_affine γ q : Affine (is_queue N γ q).
  Proof. apply _. Qed.
  Global Instance is_queue_uniform γ q : Uniform (is_queue N γ q).
  Proof. apply affine_uniform, _. Qed.

  Global Instance enqueue_handle_uniform γ q : Uniform (enqueue_handle γ q).
  Proof. apply _. Qed.
  Global Instance dequeue_handle_uniform γ q : Uniform (dequeue_handle γ q).
  Proof. apply _. Qed.

  Lemma new_queue_spec E :
    ↑N ⊆ E →
    {{{ emp }}}
      new_queue #() @ E
    {{{ q γ, RET q; <affine> is_queue N γ q ∗ queue_cancel_own γ 1 ∗
          enqueue_handle γ q ∗ dequeue_handle γ q ∗ γ ⤇{1/2} [] }}}.
  Proof.
    iIntros (? Φ) "_ HΦ". iApply iron_wp_fupd. wp_lam. wp_alloc l as "Hl"; wp_let.
    wp_alloc ltptr as "Hltptr". wp_alloc lhptr as "Hlhptr". 
    iDestruct "Hlhptr" as "[Hlhptr Hlhptr']".
    iMod (own_alloc (1%Qp, to_agree [])) as (γ) "[Hγ Hγ']"; first done.
    iMod (own_alloc (Excl ())) as (γd) "Hγd"; first done.
    iMod (own_alloc (● (Excl' l) ⋅ ◯ (Excl' l))) as (γe) "[Hγe Hγe']";
      first by apply auth_both_valid_discrete.
    iMod (fcinv_alloc_named _ N (λ γinv, queue_inv (QueueName γinv γ γd γe) lhptr ltptr)
      with "[Hlhptr' Hγ' Hl Hγe]") as (γinv) "(#? & Hγc & [Hγinv Hγinv'])".
    { iIntros "!>" (γinv).
      iExists l, l, []. rewrite queue_own_eq /=. iFrame; auto. }
    wp_pures. iModIntro. iApply ("HΦ" $! _ (QueueName γinv γ γd γe)). iSplitR.
    { iExists lhptr, ltptr; auto. }
    iFrame "Hγc". iSplitL "Hγinv Hltptr Hγe'".
    { iExists lhptr, ltptr, l. iFrame; auto. }
    iSplitL "Hγinv' Hlhptr Hγd".
    { iExists lhptr, ltptr. iFrame; auto. }
    by rewrite queue_own_eq.
  Qed.

  Lemma dequeue_spec E Φ q γ :
    ↑N ⊆ E →
    is_queue N γ q -∗ dequeue_handle γ q -∗
    (∀ vs, γ ⤇{1/2} vs ={E∖↑N}=∗
       match vs with
       | [] => γ ⤇{1/2} [] ∗ ▷ (dequeue_handle γ q -∗ Φ NONEV)
       | v :: vs' => γ ⤇{1/2} vs' ∗ ▷ (dequeue_handle γ q -∗ Φ (SOMEV v))
       end) -∗
    WP dequeue q @ E {{ Φ }}.
  Proof.
    iIntros (?) "Hq Hh Hupd".
    iDestruct "Hq" as (lhptr ltptr ->) "#?".
    iDestruct "Hh" as (?? l ?%eq_sym) "(Hγinv & Hlhptr & Hγd)"; simplify_eq.
    wp_lam. wp_load. wp_let. wp_bind (! _)%E.
    iMod (fcinv_acc _ N with "[$] Hγinv") as "(H & Hγinv & Hclose)"; first done.
    iDestruct "H" as (lh lt vs) "(>Hvs & >Hlhptr' & >Hγe & Hlist & >Hlt)".
    iDestruct (pointsto_agree with "Hlhptr Hlhptr'") as %->; simpl.
    destruct vs as [|v vs'].
    { iDestruct "Hlist" as ">->".
      wp_load. iMod ("Hupd" with "Hvs") as "[Hvs HΦ]".
      iMod ("Hclose" with "[Hvs Hlhptr' Hlt Hγe]") as "_".
      { iExists lt, lt, []. iFrame; auto. }
      iModIntro. wp_pures. iApply "HΦ". iExists lhptr, ltptr. eauto with iFrame. }
    iDestruct "Hlist" as (l') "[>[[Hlh Hlh']|[Hγd' ?]] Hlist]"; last first.
    { iCombine "Hγd Hγd'" gives %[]. }
    wp_load.
    iMod ("Hclose" with "[Hvs Hlhptr' Hlh' Hγd Hlt Hlist Hγe]") as "_".
    { iExists lh, lt, (v :: vs'). iNext. iFrame "Hvs Hlhptr' Hlt Hγe".
      iExists l'. auto with iFrame. }
    clear vs'. iModIntro. wp_match. wp_proj. wp_let. wp_bind (_ <- _)%E.
    iMod (fcinv_acc _ N with "[$] Hγinv") as "(H & Hγinv & Hclose)"; first done.
    iDestruct "H" as (lh' lt' vs) "(>Hvs & >Hlhptr' & >Hγe & Hlist & >Hlt)".
    iDestruct (pointsto_agree with "Hlhptr Hlhptr'") as %?%eq_sym; simplify_eq.
    destruct vs as [|v' vs'].
    { iDestruct "Hlist" as ">->".
      iDestruct (pointsto_agree with "Hlh Hlt") as %[=]. }
    iDestruct "Hlist" as (lh') "[>[Hlh'|[Hγd Hlh']] Hlist]".
    { by iCombine "Hlh Hlh'" gives %[]. }
    iDestruct (pointsto_agree with "Hlh Hlh'") as %?; simplify_eq.
    iCombine "Hlh Hlh'" as "Hlh"; iCombine "Hlhptr Hlhptr'" as "Hlhptr".
    wp_store. iDestruct "Hlhptr" as "[Hlhptr Hlhptr']".
    iMod ("Hupd" with "Hvs") as "[Hvs HΦ]".
    iMod ("Hclose" with "[Hvs Hlhptr' Hlt Hγe Hlist]") as "_".
    { iExists lh', lt', vs'. iNext. iFrame "Hvs Hlhptr' Hlt Hγe".
      destruct vs' as [|v'' vs'']=> //=.
      iDestruct "Hlist" as (l) "[Hlh Hlist]". auto with iFrame. }
    iModIntro. wp_seq. wp_apply (iron_wp_free with "Hlh"). iIntros "_"; wp_seq.
    wp_pures. iApply "HΦ". iExists lhptr, ltptr. eauto with iFrame.
  Qed.

  Lemma enqueue_spec E Φ q v γ :
    ↑N ⊆ E →
    is_queue N γ q -∗ enqueue_handle γ q -∗
    (∀ vs,
      γ ⤇{1/2} vs ={E∖↑N}=∗
      γ ⤇{1/2} (vs ++ [v]) ∗ ▷ (enqueue_handle γ q -∗ Φ #())) -∗
    WP enqueue q v @ E {{ Φ }}.
  Proof.
    iIntros (?) "Hq Hh Hupd". iDestruct "Hq" as (lhptr ltptr ->) "#?".
    iDestruct "Hh" as (?? lt ?%eq_sym)
      "(Hγinv & Hγe' & Hltptr)"; simplify_eq.
    wp_lam. wp_load. wp_alloc ltn as "Hltn"; wp_let. wp_pures. wp_bind (_ <- _)%E.
    iMod (fcinv_acc _ N with "[$] Hγinv") as "(H & Hγinv & Hclose)"; first done.
    iDestruct "H" as (lh lt' vs) "(>Hvs & >Hlhptr' & >Hγe & Hlist & >Hlt')".
    iCombine "Hγe Hγe'"
      gives %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hγe Hγe'") as "[Hγe Hγe']".
    { by apply auth_update, option_local_update,
        (exclusive_local_update _ (Excl ltn)). }
    wp_store. iMod ("Hupd" with "Hvs") as "[Hvs HΦ]".
    iMod ("Hclose" with "[Hvs Hlhptr' Hγe Hlist Hlt' Hltn]") as "_".
    { iNext. iExists lh, ltn, (vs ++ [v]). iFrame "Hvs Hlhptr' Hγe Hltn".
      destruct vs as [|v' vs]; simpl.
      { iDestruct "Hlist" as "->". eauto with iFrame. }
      iDestruct "Hlist" as (l) "[Hlh Hlist]". iExists l; iFrame "Hlh".
      iInduction vs as [|w ws] "IH" forall (l); simpl.
      { iDestruct "Hlist" as "->". eauto with iFrame. }
      iDestruct "Hlist" as (l') "[Hl Hlist]". iExists l'. iFrame "Hl".
      by iApply ("IH" with "[$]"). }
    iModIntro. wp_seq. wp_store. iApply "HΦ".
    iExists lhptr, ltptr, ltn. iFrame; auto.
  Qed.

  Lemma delete_spec E Φ q γ :
    ↑N ⊆ E →
    is_queue N γ q -∗
    queue_cancel_own γ 1 -∗
    enqueue_handle γ q -∗ dequeue_handle γ q -∗
    γ ⤇{1/2} [] -∗
    (γ ⤇{1} [] ={E}=∗ ▷ Φ #()) -∗
    WP delete q @ E {{ Φ }}.
  Proof.
    iIntros (?) "Hq Hγc Heh Hdh Hvs HΦ". iDestruct "Hq" as (lhptr ltptr ->) "#?".
    iDestruct "Heh" as (?? lt ?%eq_sym) "(Hγinv & Hγe' & Hltptr)"; simplify_eq.
    iDestruct "Hdh" as (?? v' ?%eq_sym) "(Hγinv' & Hlhptr & Hγd)"; simplify_eq.
    iMod (fcinv_cancel with "[$] Hγc [$Hγinv $Hγinv']") as "H"; first done.
    iDestruct "H" as (lh lt' vs) "(>Hvs' & >Hlhptr' & >Hγe & Hlist & >Hlt)".
    iCombine "Hγe Hγe'"
      gives %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    iDestruct (pointsto_agree with "Hlhptr Hlhptr'") as %?; simplify_eq.
    iCombine "Hlhptr Hlhptr'" as "Hlhptr".
    iDestruct (queue_own_agree with "Hvs Hvs'") as %<-; iCombine "Hvs Hvs'" as "Hvs".
    iDestruct "Hlist" as ">->".
    iMod ("HΦ" with "Hvs") as "HQ".
    wp_lam. wp_load. by do 3 wp_free.
  Qed.

  Lemma delete_all_spec E Φ Ψ (f : val) q γ (vs : list val) :
    ↑N ⊆ E →
    is_queue N γ q -∗
    queue_cancel_own γ 1 -∗
    enqueue_handle γ q -∗ dequeue_handle γ q -∗
    γ ⤇{1/2} vs -∗
    ▷ ([∗ list] v ∈ vs, WP f (of_val v) @ E {{ _, Ψ v }}) -∗
    ▷ (γ ⤇{1} [] -∗ ([∗ list] v ∈ vs, Ψ v) ={E}=∗ Φ #()) -∗
    WP delete_all f q @ E {{ Φ }}.
  Proof.
    iIntros (?) "#Hq Hγc Heh Hdh Hvs Hf HΦ".
    iInduction vs as [|v vs] "IH"; wp_lam; wp_pures.
    - wp_apply (dequeue_spec _ with "Hq Hdh"); first done.
      iIntros (vs) "Hvs'". iDestruct (queue_own_agree with "Hvs' Hvs") as %->.
      iIntros "!> {$Hvs'} !> Hdh /=". wp_let. wp_match.
      wp_apply (delete_spec with "Hq Hγc Heh Hdh Hvs"); first done.
      iIntros "Hvs". iMod ("HΦ" with "Hvs [//]") as "$"; auto.
    - iDestruct "Hf" as "[Hfv Hf]".
      wp_apply (dequeue_spec _ with "Hq Hdh"); first done.
      iIntros (vs') "Hvs'". iDestruct (queue_own_agree with "Hvs' Hvs") as %->.
      iMod (queue_own_update_2 _ _ _ vs with "Hvs Hvs'") as "[Hvs $]".
      iIntros "!> !> Hdh". wp_let. wp_match.
      wp_apply (iron_wp_wand with "Hfv"); iIntros (w) "HΨ"; wp_seq.
      iApply ("IH" with "Hγc Heh Hdh Hvs Hf"). iNext. iIntros "Hvs HΨs".
      iApply ("HΦ" with "[$]"). iFrame.
  Qed.
End queue_spec.
