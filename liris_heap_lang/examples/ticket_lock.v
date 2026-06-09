From iris.proofmode Require Import proofmode.
From liris.algebra Require Import auth_mra.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_map.

(** FIXME: move to more general directory *)
Section FIXME.

  Global Program Instance ordinal_auth_mra_class : auth_mra_class ord.le ord.eq :=
    Build_auth_mra_class ord.t _ _ _ _ _ _.
  Next Obligation.
    repeat intro. split; auto.
  Qed.

  Definition dfrac_div (dq : dfrac) (q : Qp) : dfrac :=
    match dq with
    | DfracOwn p => DfracOwn (p / q)
    | DfracDiscarded => DfracDiscarded
    | DfracBoth p => DfracBoth (p / q)
    end.

  Lemma dfrac_div_half dq : dq = (dfrac_div dq 2) ⋅ (dfrac_div dq 2).
  Proof.
    destruct dq; simpl.
    - by rewrite dfrac_op_own Qp.div_2.
    - done.
    - unfold op. unfold cmra_op. simpl. rewrite Qp.div_2. auto.
  Qed.

End FIXME.

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
      #[local] tlock_ticketG :: ghost_mapG Σ Z (option (positive * ogid * ord.t * measurable_syntax));
      #[local] tlock_oblG :: ghost_mapG Σ Z (option oid);
      #[local] tlock_config_inG :: inG Σ (auth_mraUR (ord.le));
    }.

Definition ticket_lockΣ : gFunctors :=
  #[ghost_mapΣ Z (option (positive * ogid * ord.t * measurable_syntax));
    ghost_mapΣ Z (option oid);
    GFunctor (auth_mraUR (ord.le))
    ].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

Record ticketlock_γ :=
  TicketLockName {
      ticketlock_γt : gname;
      ticketlock_γo : gname;
      ticketlock_γc : gname;
    }.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let N := nroot.@"ticket_lock".
  Let N_inv := N.@"inv".
  Let N_ev := N.@"ev".

  Remark N_disj_1 : N_ev ## N_inv.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑N_ev ⊆ (⊤ : coPset) ∖ ↑N_inv.
  Proof. pose proof N_disj_1. set_solver. Qed.

  (** ** Definitions *)
  (** We can define the tf counterparts for these definitions
      if we want to extract top level trace properties of library functions. *)

  Local Definition lock_inv γt γo γc (next curr : loc) (R : tf Σ) : iProp Σ :=
    ∃ (n c : Z)
      (tickets : gmap Z (option (positive * ogid * ord.t * measurable_syntax)))
      (obls : gmap Z (option oid)),
      next ↦ #n ∗
      curr ↦{#(1/2)} #c ∗
      ghost_map_auth γt 1 tickets ∗
      ghost_map_auth γo 1 obls ∗
      (⌜(dom tickets = dom obls)%Z⌝) ∗
      (⌜(0 ≤ c ≤ n)%Z⌝) ∗
      (⌜ ∀ t, t ∈ dom tickets ↔ (0 ≤ t ≤ n)%Z ⌝) ∗
      (** Finished or waiting threads *)
      (* We need auth_mra_know to sync what other threads know about the configuration *)
      ([∗ set] t ∈ dom tickets,
         ((∃ κ, ⌜(0 ≤ t ≤ c)%Z⌝ ∧
                t ↪[γt]□ (None : option (positive * ogid * ord.t * measurable_syntax)) ∗
                t ↪[γo]□ (Some κ) ∗
                oblP_discharged κ) ∨
            (⌜ (t = c + 1)%Z ⌝) ∨
            (∃ i g ℓ μ, ⌜((c + 1)%Z < t ≤ n)%Z⌝ ∧
                        t ↪[γt]{#1/2} (Some (i, g, ℓ, μ)) ∗
                        t ↪[γo] (None : option oid) ∗
                        (own γc (◯AM[ord.le] ℓ)) ∗ grP_obls i g ℓ ∅))) ∗
      ((⌜(c = n)⌝ ∧ curr ↦{#(1/2)} #c%Z ∗ ⟦R⟧ₗ) ∨
         (⌜(c < n)%Z⌝ ∧
          (* Allocates new obligation on behalf of next owner. *)
          ∃ ℓ κ, (own γc (◯AM[ord.le] ℓ)) ∗ witP_layer κ ℓ ∗ (c + 1)%Z ↪[γo]□ (Some κ) ∗
                 ⟦tf_eventually N_ev κ false (1/2) (curr ↦{#(1/2)} #(c + 1)%Z ∗ R)⟧ₗ ∗
                 ((∃ i g μ, (c + 1)%Z ↪[γt]{#1/2} (Some (i, g, ℓ, μ)) ∗
                            ⟦tf_eventually N_ev κ false (1/2) (curr ↦{#(1/2)} #(c + 1)%Z ∗ R)⟧ₗ ∗
                            grP_obls i g ℓ {[κ]} ∗ oblP_fuel κ ℓ μ ∗
                            curr ↦{#(1/2)} #c%Z ∗ ⟦R⟧ₗ) ∨
                    (* Current owner acquired the lock. *)
                    ((c + 1)%Z ↪[γt]□ (None : option (positive * ogid * ord.t * measurable_syntax)))))).

  Local Definition lock_token_def (tl : val) (γ : ticketlock_γ) κu (R : tf Σ) : iProp Σ :=
    ∃ (next curr : loc) (u : Z),
      (⌜tl = (#next, #curr)%V⌝) ∧ (curr ↦{#(1/2)} #u%Z) ∗
      ((u + 1)%Z ↪[(ticketlock_γt γ)]□ (None : option (positive * ogid * ord.t * measurable_syntax))) ∗
      ((u + 1)%Z ↪[(ticketlock_γo γ)]□ (Some κu)) ∗
      ⟦tf_eventually N_ev κu false (1/2) (curr ↦{#(1/2)} #(u + 1)%Z ∗ R)⟧ₗ.
  Local Definition lock_token_aux : seal (@lock_token_def). Proof. by eexists. Qed.
  Definition lock_token := lock_token_aux.(unseal).
  Local Definition lock_token_unseal :
    @lock_token = @lock_token_def := lock_token_aux.(seal_eq).

  Definition is_fair_lock (tl : val) (γ : ticketlock_γ) (R : tf Σ) : iProp Σ :=
    ∃ (next curr : loc),
      (⌜tl = (#next, #curr)%V⌝) ∧
      inv N_inv (lock_inv (ticketlock_γt γ) (ticketlock_γo γ) (ticketlock_γc γ) next curr R).

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
    (* FIXME: typeclass not solved *)
    apply auth_mra_update; auto. apply _.
  Qed.

  Lemma lock_config_persist γ dq ℓ :
    (γ ↪LOCK{dq} ℓ) ==∗ γ ↪LOCK□ ℓ.
  Proof. iIntros "H". iApply (own_update with "H"). apply auth_mra_auth_persist. Qed.

  (** ** Remark: Properties we want from a modular spec with liveness:
         1. Hide implementation details, e.g., # of lines, internal data structure.
         2. Robust against implementation changes, especially # of fuels.
         3. Consistent format for different libraries.

         'grP_fuel g 1 1' is a good abstraction for trivially terminating functions.
         ord.large is a good abstraction for more complex functions.
         Ref: https://en.wikipedia.org/wiki/Hartogs_number *)
  (** ** Remark: Spec we want for a function that trivially terminates (w/o witness induction):
         "flat layer"=0. A possible format is ∃ μ in front of the spec, as in TicketLock_init_sepc. *)

  (** ** Program proofs *)
  Lemma TicketLock_init_spec :
    ⊢ ∃ μ, ∀ lc ℓ i G,
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ∃ ℓ, grP_fuel g ℓ μ) }}}
      TicketLock.init #() @ i
    l{{{ tl γ, RET tl; £ lc ∗ thP_groups i G ∗ γ ↪LOCK ℓ ∗ (∀ E R, ⟦R⟧ₗ ={E}=∗ is_fair_lock tl γ R) }}}.
  Proof.
    iExists 10.
    iIntros (lc ℓ i G) "!> %Φ (TG& GF) HΦ".
    rewrite /TicketLock.init.
    lwp_pure_one.
    lwp_bind (AllocN _ _).
    iPoseProof (grP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (curr) "((_& TG& _)& Ptr_curr& _)".
    lwp_bind (AllocN _ _).
    iPoseProof (grP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TG $GF1]"). 1: done.
    iModIntro. iIntros (next) "((_& TG& _)& Ptr_next& _)".
    iModIntro. lwp_pure_lc lc. iRename "LC" into "QLC".
    iMod (obl_alloc_discharged _ (ℓ)%ordi 0) as "(%κu& #Ofk& _& #Wlk& OAcc)".
    iDestruct "Ptr_curr" as "[Ptr_curr Ptr_curr0]".
    iMod (ghost_map_alloc ({[0%Z := None]} : gmap Z (option (positive * ogid * ord.t * measurable_syntax)))) as "(%γt& GMAt& GMEt)".
    iMod (ghost_map_alloc ({[0%Z := (Some κu)]} : gmap Z (option oid))) as "(%γo& GMAo& GMEo)".
    rewrite !big_sepM_singleton.
    iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
    iMod (ghost_map_elem_persist with "GMEo") as "#GMEo".
    iMod (own_alloc (●AM[ord.le] ℓ)) as "(%γc& CF)".
    { apply auth_mra_auth_valid. }
    iAssert (own (γc) (◯AM[ord.le] ℓ))%I as "#CFl".
    { iAssert (own γc (●AM[ord.le] ℓ) ∗ own (γc) (◯AM[ord.le] ℓ))%I with "[CF]" as "[_ $]".
      rewrite -own_op -auth_mra_auth_know_op. done. }
    iModIntro. lwp_finish.
    iModIntro.
    iApply ("HΦ" $! _ (TicketLockName γt γo γc)). iFrame "TG QLC CF".
    iIntros (??) "HR".
    iMod (inv_alloc N_inv _ (lock_inv γt γo γc next curr R) with "[Ptr_next Ptr_curr0 Ptr_curr GMAt GMAo HR]") as "#Ak".
    { iNext. rewrite /lock_inv. iExists 0, 0, {[0%Z := (None)]}, {[0%Z := (Some κu)]}.
      iFrame "Ptr_next Ptr_curr0 GMAt GMAo". iSplit. 1: done. iSplit. 1: done. iSplit.
      { iPureIntro. intros. rewrite dom_singleton_L elem_of_singleton. split; intros.
        - subst. lia.
        - lia. }
      iSplitR.
      { rewrite dom_singleton_L big_sepS_singleton. iLeft. eauto. }
      iLeft. iFrame. iPureIntro. lia. }
    iModIntro. rewrite /is_fair_lock. iExists next, curr. iSplitR; first done. eauto.
  Qed.

  (** FIXME: ordi notation levels *)
  Lemma TicketLock_acquire_spec :
    ⊢ ∃ μ, ∀ lc m i G tl γ dq ℓ R,
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, grP_fuel g (ℓ ⊕ 1)%ordi μ) ∗
         γ ↪LOCK{dq} ℓ ∗
         is_fair_lock tl γ R }}}
      TicketLock.acquire tl @ i
    l{{{ gu κu, RET #();
         £ lc ∗
         (⌜ gu ∉ G ⌝) ∗
         thP_groups i ({[gu]} ∪ G) ∗
         grP_obls i gu ℓ {[κu]} ∗
         grP_fuel gu ℓ m ∗
         oblP_fuel κu ℓ m ∗
         γ ↪LOCK{dq} ℓ ∗ lock_token tl γ κu R ∗ ⟦R⟧ₗ }}}.
  Proof.
    iExists (100 ⊕ (((50 ⊕ (50 × ▽)) × ℵ) ⊕ (50 × ▽)))%M.
    iIntros (lc m i G tl γ dq ℓ R) "!> % (TG& Fs& CF& #IFL) HΦ".
    iPoseProof (grP_fuel_add_set with "Fs") as "[GF Fsloop]".
    iPoseProof (grP_fuels_init with "GF") as "GF".
    rewrite /TicketLock.acquire.
    (* argument *)
    lwp_pure_lc 100.
    (* get fst and snd of the argument *)
    iDestruct "IFL" as "(%&%& %& #INV)". subst tl.
    (* fst *)
    lwp_pures.
    (* FAA *)
    lwp_bind (FAA _ _).
    iPoseProof (grP_fuels_add 1 with "GF") as "[GF1 GF]".
    (* Atomic step of FAA, *)
    iModIntro. iMod (inv_acc with "INV") as "[H ACCinv]". 1: set_solver.
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    (** FIXME: better rules for tlc / later credits. *)
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    iApply (lwp_faa _ ∅ 0 with "[$TG $GF1 $PtrNext]"). 1: done.
    iIntros "((_& TG& _)& PtrNext)".
    (** Alloc a new group to receive new unlock obligation *)
    iMod (group_alloc _ _ _ (ℓ)%ordi (50 ⊕ m)%M with "TG") as "(%gu& %Ningu& TG& Gg& Gf)".
    iPoseProof (grP_fuel_add with "Gf") as "[Gf Q_Gf]".
    (* Update maps. *)
    iMod (ghost_map_insert (n + 1)%Z (Some (i, gu, ℓ, m)) with "GMAt") as "[GMAt GMEt]".
    { apply not_elem_of_dom. intros IN. apply Domt in IN. lia. }
    iMod (ghost_map_insert (n + 1)%Z (None) with "GMAo") as "[GMAo GMEo]".
    { apply not_elem_of_dom. intros IN. rewrite -EqDom in IN. apply Domt in IN. lia. }
    iAssert (own (ticketlock_γc γ) (◯AM[ord.le] ℓ))%I as "#CFl".
    { iAssert (γ ↪LOCK{dq} ℓ ∗ own (ticketlock_γc γ) (◯AM[ord.le] ℓ))%I with "[CF]" as "[_ $]".
      rewrite -own_op -auth_mra_auth_know_op. done. }
    (** Close inv; two cases: my turn, or not. *)
    iDestruct "Hc" as "[Hc | Hc]".
    { (* My turn *)
      iDestruct "Hc" as "(%& PtrCurr0& HR)". subst c.
      (* Unlock obligation *)
      iMod (tf_until_alloc _ _ _ _ false _ (ℓ)%ordi (m)%M with "Gg")
        as "(%κu& %LUku& Gg& OGF& #Wlku& ALLOC)". 1: done.
      iMod ("ALLOC" $! _ N_ev ⌜True⌝%F (curr ↦{#1 / 2} #(n + 1) ∗ R)%F with "[//]") as "[GUku GUku0]".
      rewrite union_empty_r_L.
      iMod (ghost_map_update (None) with "GMAt GMEt") as "[GMAt GMEt]".
      iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
      iMod (ghost_map_update (Some κu) with "GMAo GMEo") as "[GMAo GMEo]".
      iMod (ghost_map_elem_persist with "GMEo") as "#GMEo".
      rewrite !insert_insert_eq.
      iModIntro.
      iMod ("ACCinv" with "[$PtrNext $PtrCurr $GMAt $GMAo HMt GUku]") as "_".
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
        assert (Hnin : (n + 1)%Z ∉ dom tickets).
        { specialize (Domt (n + 1)%Z). intro F. apply Domt in F. lia. }
        iSplitL "HMt".
        { rewrite dom_insert_L. iApply big_sepS_union. 1: set_solver.
          iSplitR "HMt".
          - iApply big_sepS_singleton. iRight. iLeft. done.
          - iApply (big_sepS_impl with "HMt"). iIntros "!> %% H".
            iDestruct "H" as "[$ | [$ | H]]".
            iDestruct "H" as "(%&%&%&%& %& _)". lia. }
        iRight. iSplit.
        { iPureIntro. lia. }
        iFrame "CFl Wlku GMEo GUku". iRight. eauto. }
      iIntros "!> !>".
      rename n into my. assert (Hmy : (0 ≤ my)%Z) by lia.
      clear dependent tickets obls. clear Boundc LUku.
      iClear "Fsloop".
      (* Update fuels. *)
      iPoseProof (grP_fuels_add_nat 50 with "GF") as "[GF _]". 1: done.
      iPoseProof (grP_fuels_add_group with "Gf GF") as "GF".
      lwp_pure_one.
      do 2 (iModIntro; lwp_pure_one).
      (** The while loop. *)
      (* Execute loop body. *)
      lwp_pures.
      lwp_bind (Load _).
      (* Atomic step of Load, *)
      iModIntro.
      iPoseProof (grP_fuels_add 1 with "GF") as "[GF1 GF]". 1: eauto.
      iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $PtrCurr0]"). 1: done.
      iIntros "((_& TG& _)& PtrCurr0)".
      iClear "LC".
      iModIntro. lwp_pure_lc lc.
      rewrite bool_decide_eq_true_2; last done.
      lwp_pures.
      iModIntro. lwp_finish.
      iApply ("HΦ" with "[$TG $Gg $Q_Gf $OGF PtrCurr0 $HR GUku0 $LC $CF]"). iSplit. 1: set_solver.
      rewrite lock_token_unseal /lock_token_def. iFrame "PtrCurr0 GUku0". eauto. }
    (* Not my turn. *)
    iDestruct "GMEt" as "[GMEt0 GMEt]".
    iModIntro.
    iMod ("ACCinv" with "[$PtrNext $PtrCurr $GMAt $GMAo HMt Hc Gg GMEt GMEo]") as "_".
    { iDestruct "Hc" as "(%LTc& Hc)". iNext. iSplit.
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
      assert (Hnin : (n + 1)%Z ∉ dom tickets).
      { specialize (Domt (n + 1)%Z). intro F. apply Domt in F. lia. }
      iSplitL "HMt Gg GMEt GMEo".
      { rewrite dom_insert_L. iApply big_sepS_union. 1: set_solver.
        iSplitR "HMt".
        - iApply big_sepS_singleton. iRight. iRight. iFrame "Gg GMEt GMEo CFl". iPureIntro. lia.
        - iApply (big_sepS_impl with "HMt"). iIntros "!> %% H".
          iDestruct "H" as "[$ | [$ | H]]".
          do 2 iRight. iDestruct "H" as "(%&%&%&%& %& $& $& $)". iPureIntro. lia. }
      iRight. iSplit.
      { iPureIntro. lia. }
      iFrame. }
    iIntros "!> !>".
    rename n into my. assert (Hmy : (0 ≤ my)%Z) by lia.
    clear dependent c tickets obls.
    (* Update fuels. *)
    iPoseProof (grP_fuels_add_nat 50 with "GF") as "[GF _]". 1: done.
    iPoseProof (grP_fuels_add_group with "Gf GF") as "GF".
    lwp_pure_one.
    do 2 (iModIntro; lwp_pure_one).
    (** My turn or need induction. *)
    iModIntro.
    iApply fupd_lwp. iInv "INV" as "H".
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    iPoseProof (ghost_map_lookup with "GMAt GMEt0") as "%LUt".
    iDestruct "Hc" as "[Hc | Hc]".
    { iExFalso. iDestruct "Hc" as "(%& _)". subst c.
      pose proof LUt as INt. apply elem_of_dom_2 in INt. apply Domt in INt.
      assert (Elemt : (my + 1)%Z ∈ dom tickets) by (apply elem_of_dom; eauto).
      iPoseProof (big_sepS_delete _ _ _ Elemt with "HMt") as "[Ht _]".
      iDestruct "Ht" as "[Ht | Ht]".
      - iDestruct "Ht" as "(%&%& #GMEt1& _)". iCombine "GMEt0 GMEt1" gives %?. by destruct H0.
      - iDestruct "Ht" as "[% | (%&%&%&%&%& _)]". 1: lia. 1: lia. }
    (** Two cases: my turn, or not. *)
    iDestruct "Hc" as "(%LTc& Hc)".
    destruct (decide (my = c)).
    { (* My turn. *)
      subst c. iDestruct "Hc" as "(%&%κu& _& #Wl& #GMEo& HE0& Hc)".
      iDestruct "Hc" as "[Hc | #GMEt1]"; cycle 1.
      { iCombine "GMEt0 GMEt1" gives %?. by destruct H. }
      iDestruct "Hc" as "(%&%&%& GMEt& HE& Gg& Of& PtrCurr0& HR)".
      iCombine "GMEt GMEt0" as "GMEt" gives %?. destruct H as [_ H]. simplify_eq.
      replace (DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2)) with (DfracOwn 1); cycle 1.
      { rewrite dfrac_op_own Qp.div_2. done. }
      iMod (ghost_map_update (None) with "GMAt GMEt") as "[GMAt GMEt]".
      iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
      iModIntro.
      iSplitL "PtrNext PtrCurr GMAt GMAo HMt HE".
      { iNext. iFrame "PtrNext PtrCurr GMAt GMAo". iSplit.
        { iPureIntro. rewrite dom_insert_lookup_L; eauto. }
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
        iSplitL "HMt".
        { rewrite dom_insert_lookup_L; eauto. }
        iRight. iSplit.
        { iPureIntro. lia. }
        iFrame "CFl Wl GMEo". iFrame. iRight. eauto. }
      iIntros "!>".
      clear dependent tickets n obls.
      iClear "Fsloop".
      (* Update fuels. *)
      lwp_pure_one.
      (* Execute loop body. *)
      lwp_pures.
      lwp_bind (Load _).
      (* Atomic step of Load, *)
      iModIntro.
      iPoseProof (grP_fuels_add 1 with "GF") as "[GF1 GF]". 1: eauto.
      iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $PtrCurr0]"). 1: done.
      iIntros "((_& TG& _)& PtrCurr0)".
      iClear "LC".
      iModIntro. lwp_pure_lc lc.
      rewrite bool_decide_eq_true_2; last done.
      lwp_pures.
      iModIntro. lwp_finish.
      iApply ("HΦ" with "[$TG $Gg $Q_Gf $Of PtrCurr0 $HR HE0 $LC $CF]"). iSplit. 1: set_solver.
      rewrite lock_token_unseal /lock_token_def. iFrame "PtrCurr0 HE0". eauto. }
    (* Not my turn, induction. *)
    iDestruct "Hc" as "(%ℓ0&%& #CFl0& #Wl0& #GMEo0& Hc)".
    assert (Hc : (0 ≤ c)%Z) by lia.
    assert (Elemt : (my + 1)%Z ∈ dom tickets) by (apply elem_of_dom; eauto).
    iAssert (⌜(c < my)%Z⌝)%I as "%LTmy".
    { iPoseProof (big_sepS_delete _ _ _ Elemt with "HMt") as "[H _]".
      iDestruct "H" as "[H | [% | H]]".
      - iDestruct "H" as "(%& %& GMEt1& _)". iCombine "GMEt0 GMEt1" gives %?. by destruct H0.
      - lia.
      - iDestruct "H" as "(%&%&%&%& %& _)". iPureIntro. lia. }
    iModIntro.
    iSplitL "PtrNext PtrCurr GMAt GMAo HMt Hc".
    { iNext. iFrame "PtrNext PtrCurr GMAt GMAo". iSplit.
      1: eauto.
      iSplit.
      { iPureIntro. lia. }
      iSplit.
      { auto.  }
      iSplitL "HMt".
      { iFrame. }
      iRight. iSplit.
      { iPureIntro. lia. }
      iFrame "CFl0 Wl0 GMEo0". iFrame. }
    iIntros "!>".
    clear dependent tickets n obls. clear Hmy n0. rename c into prev.
    iAssert (⌜(ℓ0 <= ℓ)%ordi⌝)%I as "%Hcf".
    { iCombine "CF CFl0" gives %?. apply auth_mra_both_dfrac_valid in H. 2: apply _. by destruct H. }
    iPoseProof (grP_fuel_add_set with "Fsloop") as "[Fsloop1 Fsloop]".
    (** Nest 1: Embed induction. *)
    remember (Z.to_nat (my - prev)%Z) as ν.
    iPoseProof (embed_fuels_init (lt_wf) ν) as "EFs0".
    iMod (embed_fuels_add_map with "EFs0 Fsloop1") as "EFs". rewrite map_union_empty.
    iClear "EFs0". iRevert (κ ℓ0 Hcf gu Ningu prev Hc LTmy Heqν) "CFl0 Wl0 Q_Gf GMEt0 TG GF GMEo0 EFs".
    iInduction ν as [ν IHν] using (well_founded_induction lt_wf).
    iIntros (κ ℓ0 Hcf gu Ningu prev Hc LTmy Heqν) "#CFl0 #Wl0 Q_Gf GMEt0 TG GF #GMEo0 EFs".
    (** Nest 2: Witness induction. *)
    iPoseProof (wit_fuels_init with "Wl0") as "(%& WFs0)".
    iMod (wit_fuels_add_map with "WFs0 Fsloop") as "WFs".
    { eapply ord.le_lt_lt. 1: eauto. apply hessenberg.add_lt_l.
      rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
    rewrite map_union_empty.
    iClear "WFs0". iRevert (gu Ningu) "Q_Gf GMEt0 TG GF WFs".
    iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
    iIntros (gu Ningu) "Q_Gf GMEt0 TG GF WFs".
    (* Execute loop body. *)
    lwp_pure_one.
    lwp_bind (Load _).
    (* Atomic step of Load, *)
    iModIntro. iMod (inv_acc with "INV") as "[H ACCinv]". 1: set_solver.
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    (** TODO: better rules for tlc / later credits. *)
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    iPoseProof (grP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_load _ {[κ]} 98%ord with "[$TG $GF1 $PtrCurr]").
    { rewrite big_sepS_singleton. eauto. }
    iIntros "((LC'& TG& Wc)& PtrCurr)". iEval (rewrite big_sepS_singleton) in "Wc".
    (* Two cases: it's my turn, or not. *)
    destruct (decide (my = c)).
    { (* My turn *)
      iClear "CFl CFl0 Wl0 IHν GMEo0 IHα EFs WFs LC' Wc". clear dependent κ prev. subst c.
      iPoseProof (ghost_map_lookup with "GMAt GMEt0") as "%LUt".
      assert (Boundmy : (my + 1 ≤ n)%Z).
      { apply elem_of_dom_2 in LUt. apply Domt in LUt. lia. }
      iDestruct "Hc" as "[Hc | Hc]".
      { iDestruct "Hc" as "(%& _)". subst n. lia. }
      iDestruct "Hc" as "(_& %&%κu& #CFl& #Wl& #GMEo& HE0& [Hc | GMEt1])"; cycle 1.
      { iCombine "GMEt0 GMEt1" gives %?. by destruct H. }
      iDestruct "Hc" as "(%&%&%& GMEt1& HE& Gg& Ofk& PtrCurr0& HR)".
      iCombine "GMEt1 GMEt0" as "GMEt" gives %?. destruct H as [_ H]. simplify_eq.
      replace (DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2)) with (DfracOwn 1); cycle 1.
      { rewrite dfrac_op_own Qp.div_2. done. }
      iMod (ghost_map_update (None) with "GMAt GMEt") as "[GMAt GMEt]".
      iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
      iModIntro.
      iMod ("ACCinv" with "[$PtrNext $PtrCurr $GMAt $GMAo HMt HE]") as "_".
      { iNext. iSplit.
        { iPureIntro. rewrite dom_insert_lookup_L; eauto. }
        iSplit.
        { iPureIntro. lia. }
        iSplit.
        { rewrite dom_insert_lookup_L; eauto. }
        iSplitL "HMt".
        { rewrite dom_insert_lookup_L; eauto. }
        iRight. iSplit.
        { iPureIntro. lia. }
        iFrame "CFl Wl GMEo". iFrame. iRight. eauto. }
      iIntros "!>".
      clear dependent tickets n obls.
      iClear "LC".
      iModIntro. lwp_pure_lc lc.
      rewrite bool_decide_eq_true_2; last done.
      lwp_pures.
      iModIntro. lwp_finish.
      iApply ("HΦ" with "[$TG $Gg $Q_Gf $Ofk PtrCurr0 $HR HE0 $LC $CF]"). iSplit. 1: set_solver.
      rewrite lock_token_unseal /lock_token_def. iFrame "PtrCurr0 HE0". eauto. }
    { (* Inductive cases: prev still holding, or new owner. *)
      (* Must refresh my group. *)
      iPoseProof (ghost_map_lookup with "GMAt GMEt0") as "%LUt".
      assert (Boundmy : (my + 1 ≤ n)%Z).
      { apply elem_of_dom_2 in LUt. apply Domt in LUt. lia. }
      assert (Elemt : (my + 1)%Z ∈ dom tickets) by (apply elem_of_dom; eauto).
      iPoseProof (big_sepS_delete _ _ _ Elemt with "HMt") as "[H HMt]".
      iDestruct "H" as "[H | [% | H]]".
      { iDestruct "H" as "(%&%& GMEt1& _)". iCombine "GMEt0 GMEt1" gives %?. by destruct H0. }
      { lia. }
      iDestruct "H" as "(%&%&%&%& %& GMEt1& GMEo& _& Gg)".
      iCombine "GMEt1 GMEt0" as "GMEt" gives %?. destruct H0 as [_ H0]. simplify_eq.
      iMod (group_delete with "TG Gg") as "TG".
      iPoseProof (grP_fuels_remove_group gu with "GF") as "GF".
      replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
      rename gu into gu_prev, LUt into LUt_prev. iClear "Q_Gf". clear Ningu.
      iMod (group_alloc _ _ _ (ℓ)%ordi (45 ⊕ 47 ⊕ m)%M with "TG") as "(%gu& %Ningu& TG& Gg& Gf)".
      iPoseProof (grP_fuel_add with "Gf") as "[Gf Q_Gf]".
      iPoseProof (grP_fuel_add with "Q_Gf") as "[Loop_Gf Q_Gf]".
      (* Update tickets map. *)
      replace (DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2)) with (DfracOwn 1); cycle 1.
      { rewrite dfrac_op_own Qp.div_2. done. }      
      iMod (ghost_map_update (Some (i, gu, ℓ, m)) with "GMAt GMEt") as "[GMAt [GMEt GMEt0]]".
      iPoseProof (grP_fuels_add_group with "Gf GF") as "GF".
      iDestruct "Wc" as "[Wc | #Gdk]".
      - iModIntro. iMod ("ACCinv" with "[PtrNext GMAt GMAo HMt PtrCurr Hc Gg GMEt GMEo]") as "_".
        { iNext. iFrame "PtrNext GMAt GMAo PtrCurr Hc". iSplit.
          { iPureIntro. rewrite dom_insert_lookup_L; eauto. }
          iSplit.
          1: eauto.
          iSplit.
          { iPureIntro. rewrite dom_insert_lookup_L; eauto. }
          rewrite dom_insert_lookup_L; last eauto.
          assert (Temp : (dom tickets) = ((dom tickets ∖ {[(my + 1)%Z]}) ∪ {[(my + 1)%Z]})).
          { rewrite difference_union_L. set_solver. }
          iEval (rewrite Temp).
          iApply big_sepS_union. 1: set_solver. iFrame "HMt".
          iApply big_sepS_singleton. do 2 iRight. iFrame. eauto. }
        iModIntro.
        iModIntro. lwp_pure_one.
        rewrite bool_decide_eq_false_2; cycle 1.
        { intro. inv H. }
        iModIntro. lwp_pure_one.
        iMod (wit_fuels_decr with "WFs Wc") as "(%& %LTα& WFs& Fs')".
        iClear "GF LC".
        iAssert (grP_fuels ({[gu]} ∪ G) 47)%I with "[Loop_Gf Fs']" as "Fs".
        { iApply big_sepS_union. 1: set_solver. iSplitL "Loop_Gf".
          - iApply grP_fuels_init. iApply big_sepS_singleton. iFrame.
          - iPoseProof (big_sepM_gset_to_gmap with "Fs'") as "H".
            iPoseProof (grP_fuel_eq_set _ _ _ (47 ⊕ 3)%M with "H") as "H".
            { rewrite measure_add !measure_nat -Hessenberg.add_from_nat.
              replace 50 with (47 + 3) by lia. done. }
            iPoseProof (grP_fuel_add_set _ _ 47 with "H") as "[H _]".
            iApply grP_fuels_init. iFrame. }
        iApply ("IHα" $! α0 LTα with "CF HΦ LC' EFs [//] Q_Gf GMEt0 TG Fs WFs").
      - iPoseProof (ghost_map_lookup with "GMAo GMEo0") as "%LUp".
        iAssert (⌜(prev < c)%Z⌝)%I as "%Hpc".
        { iClear "IHν IHα". destruct (decide (prev = c)).
          { subst c. iDestruct "Hc" as "[(%& _) | Hc]".
            { subst n. lia. }
            iDestruct "Hc" as "(%& %&%& _& _& #GMEo1& HE& _)".
            iPoseProof (ghost_map_elem_agree with "GMEo0 GMEo1") as "%". simplify_eq.
            iPoseProof (tf_until_discharged_false with "HE Gdk") as "%". done. }
          assert (Elemp : (prev + 1)%Z ∈ (dom tickets ∖ {[(my + 1)%Z]})).
          { apply elem_of_dom_2 in LUp. rewrite -EqDom in LUp.
            assert ((prev + 1)%Z ≠ (my + 1)%Z) by lia. set_solver. }
          iPoseProof (big_sepS_delete _ _ _ Elemp with "HMt") as "[H _]".
          iDestruct "H" as "[H | [% | H]]".
          - iDestruct "H" as "(%& %& _)". iPureIntro. lia.
          - exfalso. lia.
          - iDestruct "H" as "(%&%&%&%& %& _& GMEo1& _)".
            iCombine "GMEo0 GMEo1" gives %HF. by destruct HF. }
        iDestruct "Hc" as "[(%& _) | Hc]".
        { exfalso. lia. }
        iDestruct "Hc" as "(%& %&%& #CFl1& #Wl1& #GMEo1& Hc)".
        iModIntro. iMod ("ACCinv" with "[PtrNext GMAt GMAo HMt PtrCurr Hc Gg GMEt GMEo]") as "_".
        { iNext. iFrame "PtrNext GMAt GMAo PtrCurr". iSplit.
          { iPureIntro. rewrite dom_insert_lookup_L; eauto. }
          iSplit.
          1: eauto.
          iSplit.
          { iPureIntro. rewrite dom_insert_lookup_L; eauto. }
          iSplitR "Hc".
          { rewrite dom_insert_lookup_L; last eauto.
            assert (Temp : (dom tickets) = ((dom tickets ∖ {[(my + 1)%Z]}) ∪ {[(my + 1)%Z]})).
            { rewrite difference_union_L. set_solver. }
            iEval (rewrite Temp).
            iApply big_sepS_union. 1: set_solver. iFrame "HMt".
            iApply big_sepS_singleton. do 2 iRight. iFrame. eauto. }
          iRight. iSplit; first auto. iFrame "CFl1 Wl1 GMEo1 Hc". }
        iModIntro.
        iModIntro. lwp_pure_one.
        rewrite bool_decide_eq_false_2; cycle 1.
        { intro. inv H. }
        iModIntro. lwp_pure_one.
        assert (LTn : (Z.to_nat (my - c)%Z) < Z.to_nat (my - prev)) by lia.
        iMod (embed_fuels_decr _ _ (Z.to_nat (my - c)%Z) with "EFs") as "(EFs& Fs')". 1: auto.
        iClear "GF LC IHα".
        iPoseProof (big_sepM_gset_to_gmap with "Fs'") as "Fs'".
        iPoseProof (grP_fuel_add_set with "Fs'") as "[Fs0 Fs1]".
        iAssert (grP_fuels ({[gu]} ∪ G) 47)%I with "[Loop_Gf Fs0]" as "Fs".
        { iPoseProof (grP_fuels_init with "Fs0") as "Fs0".
          iPoseProof (grP_fuels_add 47 with "Fs0") as "[Fs0 _]".
          iApply (grP_fuels_add_group with "Loop_Gf Fs0"). }
        iAssert (⌜(ℓ1 <= ℓ)%ordi⌝)%I as "%Hcf1".
        { iCombine "CF CFl1" gives %?. apply auth_mra_both_dfrac_valid in H1.
          2: apply _. by destruct H1. }
        iApply ("IHν" $! _ LTn with "CF HΦ LC' Fs1 [//] [//] [] [] [//] CFl1 Wl1 Q_Gf GMEt0 TG Fs GMEo1 EFs").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
    }
  Qed.

  Lemma TicketLock_release_spec :
    ⊢ ∃ μ, ∀ lc i j G tl γ R κu gu ℓu K,
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ∃ ℓ, grP_fuel g ℓ μ) ∗
         grP_obls j gu ℓu K ∗ ⌜ κu ∈ K ⌝ ∗
         lock_token tl γ κu R ∗ ⟦R⟧ₗ ∗
         is_fair_lock tl γ R }}}
      TicketLock.release tl @ i
    l{{{ RET #();
         £ lc ∗
         thP_groups i G ∗
         grP_obls j gu ℓu (K ∖ {[κu]}) }}}.
  Proof.
    iExists 100.
    iIntros (lc i j G tl γ R κu gu ℓu K) "!> % (TG& GF& Gg& %LUkl& LT& HR& #IFL) HΦ".
    rewrite /TicketLock.release.
    lwp_pure_lc 100.
    rewrite lock_token_unseal /lock_token_def.
    iDestruct "LT" as "(%& %& %& %& PtrCurr0& #GMEtku& #GMEo& GEku)".
    subst tl.
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (grP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TG $GF1 $PtrCurr0]"). 1: done.
    iIntros "((_& TG& _)& PtrCurr0)".
    lwp_pures.
    (* Update curr and unlock κl. *)
    iDestruct "IFL" as "(%&%& %& #INV)". symmetry in H. simplify_eq /=.
    (* Atomic step of Store, *)
    iModIntro.
    iMod (inv_acc with "INV") as "[H ACCinv]". 1: set_solver.
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". symmetry in H. simplify_eq /=.
    (* FIXME: does not combine the dfrac part. *)
    (* iCombine "PtrCurr PtrCurr0" as "PtrCurr" gives %?. destruct H as [_ ->]. *)
    iPoseProof (grP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_store _ ∅ lc with "[$TG $GF1 PtrCurr PtrCurr0]").
    { iSplitR; first done. iSplitL "PtrCurr"; iFrame. }
    iIntros "((QLC& TG& _)& [PtrCurr PtrCurr0])".
    iPoseProof (ghost_map_lookup with "GMAt GMEtku") as "%LUt".
    assert (LEc : ((c + 1) ≤ n)%Z).
    { apply elem_of_dom_2, Domt in LUt. lia. }
    iDestruct "Hc" as "[(%& _) | (_& %&%& #CFl& #Wl& #GMEo0& HE& Hc)]".
    { lia. }
    iClear "Hc".
    iPoseProof (ghost_map_elem_agree with "GMEo0 GMEo") as "%". simplify_eq /=. iClear "GMEo0".
    iCombine "GEku HE" as "GEku".
    (** We need a sfmupd later. *)
    iApply sfmupd_trans.
    iApply sfmupd_fupd_acc.
    iMod (tf_until_discharge with "GEku") as "H".
    1: apply N_subseteq_1.
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iModIntro.
    iDestruct "H" as "(_& H)". iMod ("H" $! _) as "H". iApply fupd_sfmupd_elim.
    iMod ("H" with "[PtrCurr0 HR] [//] Gg") as "H".
    { iNext. tf_red. rewrite tf_atomic_logic. iFrame. }
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iModIntro. iMod ("H" $! _) as "H". iModIntro. iMod "H" as "(H& Gg& #Ofk)".
    iModIntro.
    iEval (tf_red) in "H". iDestruct "H" as "(PtrCurr0& HR)".
    (** Two cases: there is a waiting thread, or not. *)
    destruct (decide (c + 1 = n)%Z).
    - (* No waiting thread. *)
      subst n. clear LEc.
      iModIntro. iMod ("ACCinv" with "[$PtrNext $GMAt $GMAo PtrCurr0 $PtrCurr HMt HR]") as "_".
      { iNext. iSplitR. 1: auto. iSplitR. 1: iPureIntro; lia. iSplitR. 1: auto. iSplitL "HMt".
        { iApply (big_sepS_impl with "HMt"). iIntros "!> %% [H | [% | H]]".
          - iDestruct "H" as "(%&%& H1& H2& H3)". iLeft. iFrame. iPureIntro. lia.
          - iLeft. simplify_eq /=. iFrame "GMEtku GMEo Ofk". iPureIntro. lia.
          - iDestruct "H" as "(%&%&%&%& %& _)". lia. }
        iLeft. iFrame. eauto. }
      iApply ("HΦ" with "[$TG $Gg $QLC]").
    - (* There is a waiting thread; create an unlock obligation for it. *)
      assert (LUt1 : (c + 2)%Z ∈ dom tickets).
      { apply Domt. lia. }
      iPoseProof (big_sepS_delete _ _ _ LUt1 with "HMt") as "[H HMt]".
      iDestruct "H" as "[H | [% | H]]".
      { iDestruct "H" as "(%& %& _)". lia. }
      { lia. }
      iDestruct "H" as "(%&%&%&%& %Hc1& GMEt1& GMEo1& #CFl1& Gg1)".
      (* Unlock obligation *)
      iMod (tf_until_alloc _ _ _ _ false _ (ℓ0)%ordi (μ)%M with "Gg1")
        as "(%κu1& %LUku1& Gg1& OGF1& #Wlku1& ALLOC)". 1: done.
      iMod ("ALLOC" $! _ N_ev ⌜True⌝%F (curr ↦{#1 / 2} #(c + 2) ∗ R)%F with "[//]") as "[GUku GUku0]".
      rewrite union_empty_r_L.
      iMod (ghost_map_update (Some κu1) with "GMAo GMEo1") as "[GMAo GMEo1]".
      iMod (ghost_map_elem_persist with "GMEo1") as "#GMEo1".
      iModIntro. iMod ("ACCinv" with "[$PtrNext $GMAt $GMAo PtrCurr0 $PtrCurr HMt GMEt1 Gg1 OGF1 GUku GUku0 HR]") as "_".
      { iNext. iSplitR.
        { iPureIntro. rewrite dom_insert_lookup_L; eauto. apply elem_of_dom. by rewrite -EqDom. }
        iSplitR. 1: iPureIntro; lia. iSplitR. 1: auto. iSplitL "HMt".
        { iApply (big_sepS_delete _ _ _ LUt1). iSplitR "HMt".
          - iRight. iLeft. iPureIntro. lia.
          - iApply (big_sepS_impl with "HMt"). iIntros "!> %% [H | [% | H]]".
            + iDestruct "H" as "(%&%& H1& H2& H3)". iLeft. iFrame. iPureIntro. lia.
            + iLeft. simplify_eq /=. iFrame "GMEtku GMEo Ofk". iPureIntro. lia.
            + iDestruct "H" as "(%&%&%&%& %& H)". iRight. iRight. iFrame. iPureIntro.
              destruct (decide (x = (c + 2)%Z)).
              { subst. set_solver. }
              lia. }
        iRight. iSplit. 1: iPureIntro; lia.
        replace (c + 1 + 1)%Z with (c + 2)%Z by lia.
        iFrame "CFl1 Wlku1 GMEo1 GUku0". iLeft. iFrame. }
      iApply ("HΦ" with "[$TG $Gg $QLC]").
  Qed.

End proof.

Global Notation "γ ↪LOCK dq l" :=
  (own_fair_lock_level γ l dq)%I
    (at level 20, dq custom dfrac at level 1, format "γ  ↪LOCK dq  l") : bi_scope.
