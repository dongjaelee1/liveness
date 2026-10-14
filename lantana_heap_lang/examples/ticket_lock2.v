From lantana.algebra Require Import auth_mra.
From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_map.
From lantana.heap_lang.examples Require Import step_tactics.
(* Re-imported so that Lantana's [£] shadows upstream Iris' ['£' n]. *)
From lantana.base_logic Require Import later_credits.

(** * A starvation-free ticket lock

    Each ticket comes with an unlock obligation, allocated by its acquiring thread, so that
    every pending ticket is eventually served ([fair_lock_starvation_free]). *)

Module TicketLock.
  (** https://en.wikipedia.org/wiki/Ticket_lock *)

  (* next = next_ticket, curr = now_serving *)
  Definition init : val :=
    λ: <>, (ref #0, ref #0).

  Definition acquire : val :=
    λ: "lnc",
      let: "next" := Fst "lnc" in
      let: "curr" := Snd "lnc" in
      let: "my_ticket" := FAA "next" #1 in
      (rec: "while" <> := if: !"curr" = "my_ticket"
                         then #()
                         else "while" #()) #().

  Definition release : val :=
    λ: "lnc",
      let: "curr" := Snd "lnc" in
      "curr" <- !"curr" + #1.

End TicketLock.

(** The CMRA we need. *)
Class ticket_lockG Σ :=
  TLockG {
      #[local] tlock_ticketG :: ghost_mapG Σ Z (oid);
      #[local] tlock_ackG :: ghost_mapG Σ Z (bool);
      #[local] tlock_config_inG :: inG Σ (auth_mraUR (ord.le));
    }.

Definition ticket_lockΣ : gFunctors :=
  #[ghost_mapΣ Z (oid); ghost_mapΣ Z (bool); GFunctor (auth_mraUR (ord.le))].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

Record ticketlock_γ :=
  TicketLockName {
      ticketlock_γt : gname;
      ticketlock_γa : gname;
      ticketlock_γc : gname;
    }.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Let N := nroot.@"ticket_lock".
  Let N_inv := N.@"inv".
  Let N_eventually := N.@"eventually".

  Remark N_disj_1 : N_eventually ## N_inv.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑N_eventually ⊆ (⊤ : coPset) ∖ ↑N_inv.
  Proof. pose proof N_disj_1. set_solver. Qed.

  (** ** Definitions *)

  Local Definition lock_inv γt γa γc (next curr : loc) (R : iProp Σ) : iProp Σ :=
    ∃ (n c : Z) (tickets : gmap Z oid) (acks : gmap Z bool),
      next ↦ #n ∗
      curr ↦{#(1/2)} #c ∗
      (ghost_map_auth_frac γt 1 tickets ∗ ghost_map_auth_frac γa 1 acks) ∗
      (⌜(dom tickets = dom acks)%Z⌝) ∗
      (⌜(0 ≤ c ≤ n)%Z⌝) ∗
      (⌜ ∀ t, t ∈ dom tickets ↔ (0 ≤ t ≤ n)%Z ⌝) ∗
      (** Finished or waiting threads *)
      ([∗ map] t ↦ κ ∈ tickets,
         (** We need auth_mra_know to sync what other threads know about the configuration *)
         (∃ ℓ, t ↪[γt]□ κ ∗ witP_layer κ (ℓ ⊕ (Z.to_nat t%Z))%ordi ∗ (own γc (◯AM[ord.le] ℓ))) ∗
         ((⌜(0 ≤ t ≤ c)%Z⌝ ∧ oblP_discharged κ) ∨
            (⌜((c + 1)%Z ≤ t ≤ n)%Z⌝ ∧ finallyI N_eventually κ (1/2) (curr ↦{#(1/2)} #t%Z ∗ R)))) ∗
      (** Acknowledgement *)
      ([∗ map] t ↦ a ∈ acks,
         ((⌜(0 ≤ t ≤ c)%Z⌝ ∧ t ↪[γa]□ true) ∨
            (⌜ (t = c + 1)%Z ⌝) ∨
            (⌜((c + 1)%Z < t ≤ n)%Z⌝ ∧ t ↪[γa]{#1/2} false))) ∗
      ((⌜(c = n)⌝ ∧ curr ↦{#(1/2)} #c%Z ∗ R) ∨
         (⌜(c < n)%Z⌝ ∧ (((c + 1)%Z ↪[γa]{#1/2} false ∗ curr ↦{#(1/2)} #c%Z ∗ R) ∨ ((c + 1)%Z ↪[γa]□ true)))).

  Local Definition lock_token_def (tl : val) (γ : ticketlock_γ) κu (R : iProp Σ) : iProp Σ :=
    ∃ (next curr : loc) (u : Z),
      (⌜tl = (#next, #curr)%V⌝) ∧ (curr ↦{#(1/2)} #u%Z) ∗
      ((u + 1)%Z ↪[(ticketlock_γt γ)]□ (κu)) ∗
      finallyI N_eventually κu (1/2) (curr ↦{#(1/2)} #(u + 1)%Z ∗ R).
  Local Definition lock_token_aux : seal (@lock_token_def). Proof. by eexists. Qed.
  Definition lock_token := lock_token_aux.(unseal).
  Local Definition lock_token_unseal :
    @lock_token = @lock_token_def := lock_token_aux.(seal_eq).

  Definition is_fair_lock (tl : val) (γ : ticketlock_γ) (R : iProp Σ) : iProp Σ :=
    ∃ (next curr : loc),
      (⌜tl = (#next, #curr)%V⌝) ∧
      alwaysI N_inv (lock_inv (ticketlock_γt γ) (ticketlock_γa γ) (ticketlock_γc γ) next curr R).

  Definition own_fair_lock_level (γ : ticketlock_γ) (ℓ : ord.t) (dq : dfrac) :=
    own (ticketlock_γc γ) (auth_mra_auth ord.le dq ℓ).

  Notation "γ ↪LOCK dq l" :=
    (own_fair_lock_level γ l dq)%I
      (at level 20, dq custom dfrac at level 1, format "γ  ↪LOCK dq  l") : bi_scope.

  (** ** Properties *)
  Global Instance is_fair_lock_persistent tl γ R : Persistent (is_fair_lock tl γ R).
  Proof. rewrite /is_fair_lock. apply _. Qed.

  Lemma lock_reconfig γ ℓ1 ℓ2 :
    (ℓ1 <= ℓ2)%ordi →
    γ ↪LOCK ℓ1 ==∗ γ ↪LOCK ℓ2.
  Proof.
    iIntros (LE). iIntros "H". iApply (own_update with "H").
    (* FIXME: [apply] leaves the class argument of [auth_mra_update] as a goal. *)
    apply auth_mra_update; auto. apply _.
  Qed.

  Lemma lock_config_persist γ dq ℓ :
    (γ ↪LOCK{dq} ℓ) ==∗ γ ↪LOCK□ ℓ.
  Proof. iIntros "H". iApply (own_update with "H"). apply auth_mra_auth_persist. Qed.

  (** ** Program proofs *)
  Lemma TicketLock_init_spec :
    ⊢ ∃ m, ∀ lc ℓ i G C,
    l{{{ thread_expr i C (TicketLock.init #()) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ m) }}}
      TicketLock.init #() @ i
    l{{{ tl γ, RET tl; thread_expr i C (of_val tl) ∗ £ lc ∗ thP_kids i G ∗ γ ↪LOCK ℓ ∗
                       (∀ E R, R -∗ |={E}=>m is_fair_lock tl γ R) }}}.
  Proof.
    iExists 4.
    iIntros (lc ℓ i G C) "!> %Φ (TE& TG& GF) HΦ".
    rewrite /TicketLock.init.
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
    lwp_bind (AllocN _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (curr) "[TE ((_& TG& _)& Ptr_curr& _)]".
    lwp_bind (AllocN _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (next) "[TE ((_& TG& _)& Ptr_next& _)]".
    iModIntro; lwp_pure_lc lc. iRename "LC" into "QLC".
    iMod (obl_alloc_discharged _ (ℓ ⊕ Z.to_nat 0)%ordi) as "(%κu& #Ofk& #Wlk& OAcc)".
    iDestruct "Ptr_curr" as "[Ptr_curr Ptr_curr0]".
    iMod (ghost_map_alloc ({[0%Z := (κu)]} : gmap Z (oid))) as "(%γt& GMAt& GMEt)".
    iMod (ghost_map_alloc ({[0%Z := true]} : gmap Z bool)) as "(%γa& GMAa& GMEa)".
    rewrite !big_sepM_singleton.
    iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
    iMod (ghost_map_elem_persist with "GMEa") as "#GMEa".
    iMod (own_alloc (●AM[ord.le] ℓ)) as "(%γc& CF)".
    { apply auth_mra_auth_valid. }
    iAssert (own (γc) (◯AM[ord.le] ℓ))%I as "#CFl".
    { iAssert (own γc (●AM[ord.le] ℓ) ∗ own (γc) (◯AM[ord.le] ℓ))%I with "[CF]" as "[_ $]".
      rewrite -own_op -auth_mra_auth_know_op. done. }
    iModIntro. lwp_finish.
    iModIntro.
    iApply ("HΦ" $! _ (TicketLockName γt γa γc)). iFrame "TE TG QLC CF".
    iIntros (??) "HR".
    iMod (alwaysI_alloc _ N_inv (lock_inv γt γa γc next curr R) with "[Ptr_next Ptr_curr0 Ptr_curr GMAt GMAa HR]") as "#Ak".
    { iNext. rewrite /lock_inv. iExists 0, 0, {[0%Z := (κu)]}, {[0%Z := true]}.
      iFrame "Ptr_next Ptr_curr0 GMAt GMAa". iSplit. 1: done. iSplit. 1: iPureIntro; lia. iSplit.
      { iPureIntro. intros. rewrite dom_singleton_L elem_of_singleton. split; intros.
        - subst. lia.
        - lia. }
      iSplitR.
      { rewrite big_sepM_singleton. iFrame "GMEt Wlk CFl". iLeft. iFrame "Ofk". iPureIntro. lia. }
      iSplitR.
      { rewrite big_sepM_singleton. iLeft. iFrame "GMEa". iPureIntro. lia. }
      iLeft. iFrame. done. }
    iModIntro. rewrite /is_fair_lock. iExists next, curr. iSplitR; first done. iFrame "#".
  Qed.

  (** FIXME: ordi notation levels *)
  Lemma TicketLock_acquire_spec :
    ⊢ ∃ m, ∀ lc μ i G tl γ dq ℓ R C,
    l{{{ thread_expr i C (TicketLock.acquire (tl : val)) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g (ℓ ⊕ ℵ)%ordi m) ∗
         γ ↪LOCK{dq} ℓ ∗
         is_fair_lock tl γ R }}}
      TicketLock.acquire tl @ i
    l{{{ κu, RET #(); thread_expr i C (#()) ∗
         £ lc ∗
         (⌜ κu ∉ G ⌝) ∗
         thP_kids i ({[κu]} ∪ G) ∗
         oblP_kids κu ∅ ∗
         oblP_fuel κu ℓ μ ∗
         γ ↪LOCK{dq} ℓ ∗ lock_token tl γ κu R ∗ R }}}.
  Proof.
    iExists 1.
    iIntros (lc μ i G tl γ dq ℓ R C) "!> % (TE& TG& Fs& CF& #IFL) HΦ".
    rewrite /TicketLock.acquire.
    iAssert (|==>[∗ set] g ∈ G, oblP_fuel g (ℓ ⊕ ω)%ordi (100 ⊕ 1)%M)%I with "[Fs]" as ">Fs".
    { rewrite -big_sepS_bupd. iApply (big_sepS_impl with "Fs"). iIntros "!> %% GF".
      iApply (oblP_fuel_extend with "GF").
      apply hessenberg.lt_add_r. rewrite ord.omega_from_peano_lt_set. apply ord.large_lt_from_wf_set. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[GF Fsloop]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_lam. simpl.
    iFrame "TG GF". iExists ∅, 100. iSplitR; first eauto. iIntros "TG GF _ LC TE".
    iDestruct "IFL" as "(%&%& %& #INV)". subst tl.
    lwp_pures.
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    lwp_bind (FAA _ _).
    (* The atomic FAA, in the invariant; a model update follows the step. *)
    iModIntro. iMod (alwaysI_acc with "INV") as "[H ACCinv]". 1: set_solver.
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& (GMAt& GMAa)& %EqDom& %Boundc& %Domt& HMt& HMa& Hc)".
    iApply (lwp_faa _ ∅ 0 with "[$TE $TG $GF1 $PtrNext]"). 1: done.
    iIntros "[TE ((_& TG& _)& PtrNext)]".
    (** The unlock obligation: a child of this thread, above the obligations of the earlier
        tickets; its fuel pays the steps of the loop. *)
    iMod (untilI_alloc _ _ _ (ℓ ⊕ Z.to_nat (n + 1)%Z)%ordi ((50 ⊕ (50 × ▽)) ⊕ 1)%M with "[] TG")
      as "(%κu& %Ningu0& TG& Kku& OGF& #Wlku& ALLOC)".
    { iApply parP_le_thread. }
    iMod ("ALLOC" $! _ N_eventually True%I (curr ↦{#1 / 2} #(n + 1) ∗ R)%I with "[//]") as "[GUku GUku1]".
    iPoseProof (oblP_fuel_add with "OGF") as "[GF' QGF]".
    iMod (oblP_fuel_extend _ ℓ _ μ with "QGF") as "QGF".
    { apply hessenberg.add_lt_l. rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
    (* Update tickets map to relate κu with my ticket. *)
    iMod (ghost_map_insert_persist (n + 1)%Z (κu) with "GMAt") as "[GMAt #GMEtku]".
    { apply not_elem_of_dom. intros IN. apply Domt in IN. lia. }
    iMod (ghost_map_insert (n + 1)%Z false with "GMAa") as "[GMAa [GMEaku GMEaku1]]".
    { apply not_elem_of_dom. rewrite -EqDom. intros IN. apply Domt in IN. lia. }
    iAssert (own (ticketlock_γc γ) (◯AM[ord.le] ℓ))%I as "#CFl".
    { iAssert (γ ↪LOCK{dq} ℓ ∗ own (ticketlock_γc γ) (◯AM[ord.le] ℓ))%I with "[CF]" as "[_ $]".
      rewrite -own_op -auth_mra_auth_know_op. done. }
    (* Close inv. *)
    iModIntro. iMod ("ACCinv" with "[$PtrNext $PtrCurr $GMAt $GMAa HMt HMa Hc GUku1 GMEaku1]") as "_".
    { iNext. iSplit.
      { iPureIntro. rewrite !dom_insert_L EqDom. done. }
      iSplit.
      { iPureIntro. lia. }
      iSplit.
      { iPureIntro. intros. rewrite dom_insert_L. split; intros.
        - apply elem_of_union in H. destruct H.
          + apply elem_of_singleton in H. subst. lia.
          + apply Domt in H. lia.
        - apply elem_of_union. destruct (decide (t = (n + 1)%Z)).
          + subst. left. apply elem_of_singleton. lia.
          + right. apply Domt. lia. }
      iSplitL "HMt GUku1".
      { iApply big_sepM_insert.
        { apply not_elem_of_dom. intros IN. apply Domt in IN. lia. }
        iSplitR "HMt".
        - iFrame "GMEtku Wlku CFl". iRight. iFrame. iPureIntro. lia.
        - iApply (big_sepM_impl with "HMt"). iIntros "!> %%% H".
          iDestruct "H" as "($& [H | H])".
          + by iLeft.
          + iRight. iDestruct "H" as "(%& $)". iPureIntro. lia. }
      iDestruct "Hc" as "[Hc | Hc]".
      - iDestruct "Hc" as "(%& PtrCurr1& HR)". subst. iSplitL "HMa".
        + iApply big_sepM_insert.
          { apply not_elem_of_dom. rewrite -EqDom. intros IN. apply Domt in IN. lia. }
          iSplitR "HMa".
          { iRight. iLeft. done. }
          iApply (big_sepM_impl with "HMa"). iIntros "!> %%% H". iDestruct "H" as "[$ | [$ | H]]".
          iRight. iRight. iDestruct "H" as "[% $]". iPureIntro. lia.
        + iRight. iSplitR. 1: iPureIntro; lia. iLeft. iFrame.
      - iDestruct "Hc" as "(%& Hc)". iSplitL "HMa GMEaku1".
        + iApply big_sepM_insert.
          { apply not_elem_of_dom. rewrite -EqDom. intros IN. apply Domt in IN. lia. }
          iSplitR "HMa".
          { iRight. iRight. iFrame. iPureIntro. lia. }
          iApply (big_sepM_impl with "HMa"). iIntros "!> %%% H". iDestruct "H" as "[$ | [$ | H]]".
          iRight. iRight. iDestruct "H" as "[% $]". iPureIntro. lia.
        + iRight. iFrame. iPureIntro. lia. }
    iIntros "!> !>".
    rename n into my. assert (Hmy : (0 ≤ my)%Z) by lia.
    clear dependent c tickets acks.
    (* Update fuels. *)
    iPoseProof (oblP_fuel_add with "GF'") as "[GF' GFloop]".
    iMod (oblP_fuel_extend_set _ (ℓ ⊕ Z.to_nat (my + 1))%ordi _ (50 × ▽)%M with "Fsloop") as "Fsloop".
    { apply hessenberg.lt_add_r. apply ord.omega_upperbound. }
    iPoseProof (big_sepS_insert _ G κu with "[$Fsloop $GFloop]") as "Fsloop". 1: auto.
    iPoseProof (oblP_fuels_add 42 50 with "GF") as "[_ GF]".
    iPoseProof (oblP_fuels_add_obl with "GF' GF") as "GF".
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
    do 2 (iModIntro; lwp_pure_one).
    (** Set up induction. *)
    iModIntro.
    iApply fupd_lwp. iInv "INV" as "H".
    iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& (GMAt& GMAa)& %EqDom& %Boundc& %Domt& HMt& HMa& Hc)".
    iPoseProof (ghost_map_lookup with "GMAt GMEtku") as "%LUt".
    (* Retrieve previous witness *)
    assert (LUt' : is_Some (tickets !! my)).
    { apply elem_of_dom. apply Domt. apply elem_of_dom_2, Domt in LUt. lia. }
    destruct LUt' as [κp LUt'].
    iPoseProof (big_sepM_delete _ _ _ _ LUt' with "HMt") as "[(#Hkp& Hmt) HMt]".
    iPoseProof (big_sepM_delete _ _ _ _ LUt' with "[Hmt $HMt]") as "HMt".
    { iSplit; first eauto. iFrame. }
    iSplitL "PtrNext PtrCurr GMAt GMAa HMt HMa Hc".
    { iFrame. eauto. }
    iIntros "!> !>". iDestruct "Hkp" as "(%& #Mtkp& #Wlkp& #CFlp)".
    clear dependent n c tickets acks.
    (** Witness induction. *)
    remember ({[κu]} ∪ G) as G'.
    iAssert (⌜(ℓ0 <= ℓ)%ordi⌝)%I as "%Hcf".
    { iCombine "CF CFlp" gives %?. apply auth_mra_both_dfrac_valid in H. 2: apply _. destruct H. auto. }
    iPoseProof (wit_fuels_init with "Wlkp") as "(%& WFs0)".
    iMod (wit_fuels_add_map _ _ _ _ G' (ℓ ⊕ Z.to_nat (my + 1))%ordi (50)%M
           with "WFs0 Fsloop") as "WFs".
    { unshelve eapply ord.le_lt_lt. 1: exact (ℓ ⊕ Z.to_nat my)%ordi.
      - apply hessenberg.le_add_l. auto.
      - apply hessenberg.lt_add_r. apply ordArith.lt_from_nat. lia. }
    iClear "WFs0". rewrite map_union_empty. iRevert "WFs TE".
    iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
    iIntros "WFs TE".
    (* Execute loop body. *)
    lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
    lwp_bind (Load _).
    (* The atomic load, in the invariant; a model update follows the step. *)
    iModIntro. iMod (alwaysI_acc with "INV") as "[H ACCinv]". 1: set_solver.
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 97 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& (GMAt& GMAa)& %EqDom& %Boundc& %Domt& HMt& HMa& Hc)".
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_load _ {[κp]} 98%ord with "[$TE $TG $GF1 $PtrCurr]").
    { rewrite big_sepS_singleton. eauto. }
    iIntros "[TE ((LC'& TG& Wc)& PtrCurr)]". iEval (rewrite big_sepS_singleton) in "Wc".
    (* Two cases: it's my turn, or not. *)
    destruct (decide (my = c)).
    - iClear "Wlkp Mtkp IHα WFs LC' Wc". clear dependent κp. subst c.
      iPoseProof (ghost_map_lookup with "GMAt GMEtku") as "%LUt".
      iPoseProof (ghost_map_lookup with "GMAa GMEaku") as "%LUa".
      assert (Boundmy : (my + 1 ≤ n)%Z).
      { apply elem_of_dom_2 in LUt. apply Domt in LUt. lia. }
      iDestruct "Hc" as "[Hc | Hc]".
      { iDestruct "Hc" as "(%& _)". subst n. lia. }
      iDestruct "Hc" as "(%Boundmy1& [Hc | Hc])"; cycle 1.
      { iPoseProof (ghost_map_elem_agree with "GMEaku Hc") as "%". done. }
      iDestruct "Hc" as "(GMEaku1& PtrCurr1& HR)".
      iCombine "GMEaku GMEaku1" as "GMEa". iMod (ghost_map_update true with "GMAa GMEa") as "[GMAa GMEa]".
      iMod (ghost_map_elem_persist with "GMEa") as "#GMEa".
      iModIntro. iMod ("ACCinv" with "[PtrNext GMAt HMt HMa PtrCurr1 GMAa]") as "_".
      { replace (<[(my + 1)%Z:=true]> acks) with (<[(my + 1)%Z:=true]> (delete (my + 1)%Z acks)); cycle 1.
        { rewrite insert_delete_eq. auto. }
        iNext. iFrame "PtrNext GMAt PtrCurr1 GMAa HMt". iSplitR.
        { iPureIntro. rewrite EqDom insert_delete_eq dom_insert_lookup_L; auto. }
        iSplitR. 1: auto. iSplitR. 1: auto.
        iSplitL "HMa".
        { iPoseProof (big_sepM_delete _ _ _ _ LUa with "HMa") as "[Hma HMa]". iApply big_sepM_insert.
          { rewrite lookup_delete_eq. auto. }
          iFrame. }
        iRight. iSplit; first auto. iRight. auto. }
      clear dependent tickets acks n α.
      iModIntro.
      iModIntro. lwp_pure. simpl.
      iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
      rewrite bool_decide_eq_true_2; last done.
      iModIntro. lwp_pure. simpl.
      iFrame "TG GF". iExists ∅, lc. iSplitR; first eauto. iIntros "TG GF _ QLC TE".
      iModIntro. lwp_finish.
      subst G'.
      iApply ("HΦ" with "[$TE $TG $Kku $QGF PtrCurr $HR GUku $QLC $CF]"). iSplit. 1: by iPureIntro.
      rewrite lock_token_unseal /lock_token_def. iFrame "PtrCurr GUku". eauto.
    - (* Not my turn, proceed to induction. *)
      iDestruct "Wc" as "[Wc | #Gfkp]"; cycle 1.
      { iPoseProof (ghost_map_lookup with "GMAt Mtkp") as "%LUt".
        iExFalso. iPoseProof (big_sepM_delete _ _ _ _ LUt with "HMt") as "[Hmt _]".
        iDestruct "Hmt" as "(_& [Hmt | Hmt])"; cycle 1.
        { iDestruct "Hmt" as "(_& Ukp)". iEval (rewrite /finallyI untilI_unfold) in "Ukp".
          iDestruct "Ukp" as "(Oa& _)". iPoseProof (oblP_assigned_discharged_false with "Oa Gfkp")as "%". done. }
        iDestruct "Hmt" as "(%Boundmy& _)". assert (Boundmy1 : (0 ≤ my < c)%Z) by lia.
        iPoseProof (ghost_map_lookup with "GMAa GMEaku") as "%LUa".
        iPoseProof (big_sepM_delete _ _ _ _ LUa with "HMa") as "[Hma _]".
        iDestruct "Hma" as "[Hma | [%Hma | Hma]]".
        - iDestruct "Hma" as "(%& GMEa)". iPoseProof (ghost_map_elem_agree with "GMEaku GMEa") as "%". done.
        - lia.
        - iDestruct "Hma" as "(%& _)". lia. }
      iModIntro. iMod ("ACCinv" with "[PtrNext GMAt HMt HMa PtrCurr GMAa Hc]") as "_".
      { iNext. iFrame. iSplitR. 1: auto. iSplitR; auto. }
      iModIntro.
      iModIntro. lwp_pure. simpl.
      iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
      rewrite bool_decide_eq_false_2; cycle 1.
      { intro. inv H. }
      iModIntro. lwp_pure. simpl.
      iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
      iMod (wit_fuels_decr with "WFs Wc") as "(%& %LTα& WFs& Fs')".
      iClear "GF LC". iAssert (|==> ([∗ set] k ∈ G', oblP_fuel k 0 47))%I with "[Fs']" as ">Fs".
      { rewrite -big_sepS_bupd big_sepM_gset_to_gmap. iApply (big_sepS_impl with "Fs'").
        iIntros "!> %% F". iApply (oblP_fuel_mon_gen with "F").
        - apply ord.O_bot.
        - rewrite !measure_rep_nat. apply OrdArith.le_from_nat. lia. }
      iPoseProof (oblP_fuels_init with "Fs") as "Fs".
      iApply ("IHα" $! α0 LTα with "CF HΦ Kku GUku QGF GMEaku TG Fs LC' WFs TE").
  Qed.

  Lemma TicketLock_release_spec :
    ⊢ ∃ m, ∀ lc i G tl γ R κu C,
    l{{{ thread_expr i C (TicketLock.release (tl : val)) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ m) ∗
         ⌜ κu ∈ G ⌝ ∗ oblP_kids κu ∅ ∗
         lock_token tl γ κu R ∗ R ∗
         is_fair_lock tl γ R }}}
      TicketLock.release tl @ i
    l{{{ RET #(); thread_expr i C (#()) ∗
         £ lc ∗
         thP_kids i (G ∖ {[κu]}) }}}.
  Proof.
    iExists 100.
    iIntros (lc i G tl γ R κu C) "!> % (TE& TG& GF& %LUkl& Kku& LT& HR& #IFL) HΦ".
    rewrite /TicketLock.release.
    lwp_lam. simpl.
    iFrame "TG GF". iExists ∅, 100. iSplitR; first eauto. iIntros "TG GF _ LC TE".
    rewrite lock_token_unseal /lock_token_def.
    iDestruct "LT" as "(%& %& %& %& PtrCurr0& #GMEtku& GEku)".
    subst tl.
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $PtrCurr0]"). 1: done.
    iIntros "[TE ((_& TG& _)& PtrCurr0)]".
    iModIntro. lwp_pure. simpl.
    iFrame "TG GF". iExists ∅, 0. iSplitR; first eauto. iIntros "TG GF _ _ TE".
    (* Update curr and unlock κl. *)
    iDestruct "IFL" as "(%&%& %& #INV)". symmetry in H. inv H.
    (* The atomic store, in the invariant; a model update follows the step. *)
    iModIntro.
    iMod (alwaysI_acc with "INV") as "[H ACCinv]". 1: set_solver.
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& (GMAt& GMAa)& %EqDom& %Boundc& %Domt& HMt& HMa& Hc)".
    iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". inversion H. subst u. clear H.
    (* FIXME: [iCombine] does not combine the dfrac parts here, hence [pointsto_agree]. *)
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_store _ ∅ lc with "[$TE $TG $GF1 PtrCurr PtrCurr0]").
    { iSplitR; first done. iSplitL "PtrCurr"; iFrame. }
    iIntros "[TE ((QLC& TG& _)& [PtrCurr PtrCurr0])]".
    iPoseProof (ghost_map_lookup with "GMAt GMEtku") as "%LUt".
    iPoseProof (big_sepM_delete _ _ _ _ LUt with "HMt") as "[Hmt HMt]".
    iDestruct "Hmt" as "(Hmt1& [Hmt2 | Hmt2])".
    { iDestruct "Hmt2" as "(%& #Of)". lia. }
    iDestruct "Hmt2" as "(%Boundc1& GEku1)". iCombine "GEku GEku1" as "GEku".
    iApply sfmupd_fupd_acc.
    iMod (untilI_discharge with "GEku") as "H".
    1: apply N_subseteq_1.
    iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iModIntro.
    iDestruct "H" as "(_& H)".
    iPoseProof ("H" $! (PThread i) G LUkl with "TG Kku [PtrCurr0 HR]") as "H".
    { iFrame. }
    iMod ("H" $! _) as "H". iApply fupd_sfmupd_elim. iMod "H" as "(H& TG& #Ofk)".
    iDestruct "H" as "(PtrCurr0& HR)".
    iApply fupd_mask_intro; first solve_ndisj. iIntros "close". iModIntro. iMod "close" as "_". iModIntro.
    iMod ("ACCinv" with "[$PtrNext $GMAt $GMAa HMa Hc PtrCurr0 $PtrCurr Hmt1 HMt HR]") as "_".
    { iNext. iSplitR. 1: auto. iSplitR. 1: iPureIntro; lia. iSplitR. 1: auto. iSplitL "Hmt1 HMt".
      { iApply (big_sepM_delete _ _ _ _ LUt). iSplitR "HMt".
        - iFrame. iLeft. iSplit; auto. iPureIntro. lia.
        - iApply (big_sepM_impl with "HMt"). iIntros "!> %% % H". iDestruct "H" as "($& [H | H])".
          + iDestruct "H" as "(%& H)". iLeft. iFrame. iPureIntro. lia.
          + iDestruct "H" as "(%& H)". assert (Neq : k ≠ (c + 1)%Z).
            { intros ->. rewrite lookup_delete_eq in H. done. }
            iRight. iFrame. iPureIntro. lia. }
      destruct (decide (c + 1 = n)%Z).
      - subst n. iDestruct "Hc" as "[Hc | (_& [Hc | #Hc])]".
        { iDestruct "Hc" as "(%& _)". lia. }
        { iDestruct "Hc" as "(_& PtrCurr& _)".
          iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". inv H. lia. }
        iSplitR "PtrCurr0 HR".
        + iApply (big_sepM_impl with "HMa"). iIntros "!> %%% H". iDestruct "H" as "[H | [% | H]]".
          * iDestruct "H" as "(%& H)". iLeft. iFrame. iPureIntro. lia.
          * subst. iLeft. iFrame "Hc". iPureIntro. lia.
          * iDestruct "H" as "(%& _)". lia.
        + iLeft. iFrame. iPureIntro. lia.
      - iDestruct "Hc" as "[Hc | (_& [Hc | #Hc])]".
        { iDestruct "Hc" as "(%& _)". lia. }
        { iDestruct "Hc" as "(_& PtrCurr& _)".
          iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". inv H. lia. }
        assert (LUt2 : is_Some (acks !! (c + 2)%Z)).
        { apply elem_of_dom. rewrite -EqDom. apply Domt. lia. }
        destruct LUt2 as [a LUt2]. iPoseProof (big_sepM_delete _ _ _ _ LUt2 with "HMa") as "[Hma HMa]".
        iDestruct "Hma" as "[Hma | [% | Hma]]".
        { iDestruct "Hma" as "[% _]". lia. }
        { lia. }
        iDestruct "Hma" as "(%& GMEa)". iSplitL "HMa".
        { iApply (big_sepM_delete _ _ _ _ LUt2). iSplitR.
          - iRight. iLeft. iPureIntro. lia.
          - iApply (big_sepM_impl with "HMa"). iIntros "!> %%% H". iDestruct "H" as "[(%& H) | [% | (%& H)]]".
            + iLeft. iFrame. iPureIntro. lia.
            + subst. iLeft. iFrame "Hc". iPureIntro. lia.
            + iRight. iRight. iFrame. iPureIntro. assert (Neq : k ≠ (c + 2)%Z).
              { intros ->. rewrite lookup_delete_eq in H0. done. }
              lia. }
        iRight. iSplit. 1: iPureIntro; lia.
        iLeft. replace (c + 1 + 1)%Z with (c + 2)%Z by lia. iFrame. }
    iApply ("HΦ" with "[$TE $TG $QLC]").
  Qed.

  (** ** Temporal guarantees *)
  (** The guarantee of [lock_inv], as inferred: [itrProp_true] for ghost state and [R]; the
      pending tickets [c + 1 ≤ t ≤ n] carry [finally curr ↦ t]. *)
  Definition lock_inv_itrProp (next curr : loc) : itrProp heap_lang Σ :=
    (∃ (n c : Z) (tickets : gmap Z oid) (acks : gmap Z bool),
       next ↦ #n ∧ curr ↦{#1/2} #c ∧ (itrProp_true ∧ itrProp_true) ∧
       ⌜dom tickets = dom acks⌝ ∧ ⌜(0 ≤ c ≤ n)%Z⌝ ∧ ⌜∀ t, t ∈ dom tickets ↔ (0 ≤ t ≤ n)%Z⌝ ∧
       (∀ (t : Z) (κ : oid), ⌜tickets !! t = Some κ⌝ →
          (itrProp_true ∧ itrProp_true ∧ itrProp_true) ∧
          (⌜(0 ≤ t ≤ c)%Z⌝ ∧ itrProp_true ∨
           ⌜(c + 1 ≤ t ≤ n)%Z⌝ ∧ itrProp_finally (curr ↦{#1/2} #t ∧ itrProp_true))) ∧
       (∀ (t : Z) (a : bool), ⌜acks !! t = Some a⌝ →
          ⌜(0 ≤ t ≤ c)%Z⌝ ∧ itrProp_true ∨ ⌜t = (c + 1)%Z⌝ ∨ ⌜(c + 1 < t ≤ n)%Z⌝ ∧ itrProp_true) ∧
       (⌜c = n⌝ ∧ curr ↦{#1/2} #c ∧ itrProp_true ∨
        ⌜(c < n)%Z⌝ ∧ (itrProp_true ∧ curr ↦{#1/2} #c ∧ itrProp_true ∨ itrProp_true)))%ITR.

  Definition fair_lock_itrProp (tl : val) : itrProp heap_lang Σ :=
    (∃ next curr : loc, ⌜tl = (#next, #curr)%V⌝ ∧ itrProp_always (lock_inv_itrProp next curr))%ITR.

  Lemma guar_is_fair_lock tl γ R : ⊢ is_fair_lock tl γ R ⊨ₜ fair_lock_itrProp tl.
  Proof. apply (into_guar _ _). Qed.

  (** Clients see the lock's guarantee, not its invariant. *)
  Global Instance into_guar_is_fair_lock tl γ R :
    IntoGuar (is_fair_lock tl γ R) (fair_lock_itrProp tl) | 0.
  Proof. apply guar_is_fair_lock. Qed.


  (** The guarantee of a lock token: the holder releases the lock. *)
  Definition lock_token_itrProp (tl : val) : itrProp heap_lang Σ :=
    (∃ (next curr : loc) (u : Z), ⌜tl = (#next, #curr)%V⌝ ∧ curr ↦{#1/2} #u ∧ itrProp_true ∧
       itrProp_finally (curr ↦{#1/2} #(u + 1) ∧ itrProp_true))%ITR.

  Lemma guar_lock_token tl γ κu R : ⊢ lock_token tl γ κu R ⊨ₜ lock_token_itrProp tl.
  Proof. rewrite lock_token_unseal. apply (into_guar _ _). Qed.

  Global Instance into_guar_lock_token tl γ κu R :
    IntoGuar (lock_token tl γ κu R) (lock_token_itrProp tl) | 0.
  Proof. apply guar_lock_token. Qed.

End proof.

(** ** Starvation freedom, at the level of traces *)
Section trace.

  (** [l ↦ v] in the current state of the trace. *)
  Definition tr_pointsto (l : loc) (v : val) : trProp heap_lang :=
    tr_state (pointsto_sat l (DfracOwn 1) v).

  (** Starvation freedom of the ticket lock [(next, curr)]: whenever [next ↦ n] and
      [curr ↦ c], every ticket [t] with [c < t ≤ n] is eventually served. *)
  Definition starvation_free (next curr : loc) : trProp heap_lang :=
    (□ (∀ n c t : Z, tr_pointsto next #n → tr_pointsto curr #c → ⌜(c < t ≤ n)%Z⌝ →
                     ◇ tr_pointsto curr #t))%R.

  (** From the invariant's reading: the atoms fix [n] and [c], the pure facts give ticket
      [t] its obligation, whose branch for pending tickets is the finally. *)
  Lemma lock_inv_itrProp_starvation_free {Σ} next curr :
    itrProp_external (itrProp_always (lock_inv_itrProp (Σ:=Σ) next curr)) ⊆ starvation_free next curr.
  Proof.
    rewrite /lock_inv_itrProp. etrans; first apply (itrProp_ext_of _ _). apply tr_always_mono.
    intros τ (n' & c' & tickets & acks & Hn' & Hc' & _ & _ & Hb%tr_pure_at & Hdom%tr_pure_at & Htk & _)
      n c t Hn Hc Ht%tr_pure_at.
    pose proof (tr_pointsto_agree next _ _ _ _ τ (conj Hn' Hn)) as [= <-].
    pose proof (tr_pointsto_agree curr _ _ _ _ τ (conj Hc' Hc)) as [= <-].
    assert (is_Some (tickets !! t)) as [κ Hκ] by (apply elem_of_dom, Hdom; lia).
    destruct (Htk t κ Hκ) as [_ [[?%tr_pure_at _]|[_ Hfin]]]; first lia.
    refine (tr_finally_mono _ _ _ τ Hfin). etrans; [apply tr_and_elim_l|apply tr_pointsto_frac].
  Qed.

  (** The trace property of a fair lock: starvation freedom of its two cells. *)
  Definition fair_lock_sf (tl : val) : trProp heap_lang :=
    (∃ next curr : loc, ⌜tl = (#next, #curr)%V⌝ ∧ starvation_free next curr)%R.

  Lemma fair_lock_starvation_free {Σ} tl : itrProp_external (fair_lock_itrProp (Σ:=Σ) tl) ⊆ fair_lock_sf tl.
  Proof.
    rewrite /fair_lock_itrProp. etrans; first apply (itrProp_ext_of _ _).
    apply tr_exist_mono => next. apply tr_exist_mono => curr.
    apply tr_and_mono; [reflexivity|apply (lock_inv_itrProp_starvation_free (Σ:=Σ))].
  Qed.

  (** The holder of a lock token (serving ticket [u]) eventually releases the lock. *)
  Definition lock_token_tr (tl : val) : trProp heap_lang :=
    (∃ (next curr : loc) (u : Z), ⌜tl = (#next, #curr)%V⌝ ∧ tr_pointsto curr #u ∧
       ◇ tr_pointsto curr #(u + 1))%R.

  Lemma lock_token_releases {Σ} tl : itrProp_external (lock_token_itrProp (Σ:=Σ) tl) ⊆ lock_token_tr tl.
  Proof.
    rewrite /lock_token_itrProp. etrans; first apply (itrProp_ext_of _ _).
    apply tr_exist_mono => next. apply tr_exist_mono => curr. apply tr_exist_mono => u.
    apply tr_and_mono; first reflexivity. apply tr_and_mono; first apply tr_pointsto_frac.
    etrans; first apply tr_and_elim_r. apply tr_finally_mono.
    etrans; [apply tr_and_elim_l|apply tr_pointsto_frac].
  Qed.

End trace.

(** Starvation freedom as a guarantee: the lock's guarantee, cast to its trace property. *)
Section guarantee.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Lemma is_fair_lock_starvation_free tl γ R :
    ⊢ is_fair_lock tl γ R ⊨ₜ itrProp_cast (fair_lock_itrProp tl) (fair_lock_sf tl) (fair_lock_starvation_free tl).
  Proof. iApply guar_cast. iApply guar_is_fair_lock. Qed.
End guarantee.

Global Notation "γ ↪LOCK dq l" :=
  (own_fair_lock_level γ l dq)%I
    (at level 20, dq custom dfrac at level 1, format "γ  ↪LOCK dq  l") : bi_scope.
