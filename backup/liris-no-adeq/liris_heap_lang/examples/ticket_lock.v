From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_rules.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import token ghost_map.

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
      #[local] tlock_ticketG :: ghost_mapG Σ Z gl_id;
    }.

Definition ticket_lockΣ : gFunctors :=
  #[(ghost_mapΣ Z gl_id)].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Let N := nroot.@"ticket_lock".
  Let N_inv := N.@"inv".
  Let N_eventually := N.@"eventually".

  Remark N_disj_1 : N_eventually ## N_inv.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑N_eventually ⊆ (⊤ : coPset) ∖ ↑N_inv.
  Proof. pose proof N_disj_1. set_solver. Qed.

  (** Definitions *)
  Local Definition lock_proto γt (next curr : loc) (ℓ : layer) (R : iProp Σ) : iProp Σ :=
    ∃ (n c : Z) (tickets : gmap Z gl_id),
      next ↦ #n ∗
      curr ↦{#(1/2)} #c ∗
      ghost_map_auth γt 1 tickets ∗
      (⌜(0 ≤ c ≤ n)%Z⌝) ∗
      (⌜ ∀ t, t ∈ dom tickets → (t ≤ n)%Z ⌝) ∗
      ([∗ map] t ↦ κ ∈ tickets, (⌜(t ≤ c)%Z⌝ → gl_done κ 0)) ∗
      ∃ κu, gl κu 0 ∗
            n ↪[γt]□ κu ∗
            gl_eventually N_eventually κu (curr ↦{#(1/2)} #n%Z ∗ gl_current κu 0 (1/2)%Qp ∗ R) ∗
            gl_current κu 0 (1/2)%Qp ∗
            (⌜(c < n)%Z⌝ → wit_layer κu 0 (ℓ ⊕ (Z.to_nat n%Z))%ordi).

  Definition lock_token γt (lnc : val) κu (R : iProp Σ) : iProp Σ :=
    ∃ (next curr : loc) (u : Z),
      (⌜lnc = (#next, #curr)%V⌝) ∧ (curr ↦{#(1/2)} #u%Z) ∗ (u + 1)%Z ↪[γt]□ κu ∗
      gl_eventually N_eventually κu (curr ↦{#(1/2)} #(u + 1)%Z ∗ gl_current κu 0 (1/2)%Qp ∗ R).

  Definition is_fair_lock γt (lnc : val) (ℓ : layer) (R : iProp Σ) : iProp Σ :=
    ∃ (next curr : loc), (⌜lnc = (#next, #curr)%V⌝) ∧
                         ∃ κ, gl_done κ 0 ∗ gl_always N_inv κ (lock_proto γt next curr ℓ R).

  (** Properties *)
  Global Instance is_fair_lock_persistent γt lnc ℓ R : Persistent (is_fair_lock γt lnc ℓ R).
  Proof. rewrite /is_fair_lock. apply _. Qed.

  (** Program proofs *)
  Local Lemma init_spec i q G ℓ (R : iProp Σ) lc :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ([∗ set] k ∈ dom G, gl_fuel k 1 ▽%M) ∗
         R }}}
      TicketLock.init #() @ i
    l{{{ γt lnc, RET lnc;
         thread_exec i q ∗ th_obls i G 1 ∗ £ lc ∗
         is_fair_lock γt lnc ℓ R }}}.
  Proof.
    iIntros (Φ) "(Tx& TG& Fs& HR) HΦ".
    rewrite /TicketLock.init.
    iMod (gl_fuel_extend_set _ 0 _ 4%M with "Fs") as "Fs".
    { apply ordArith.lt_from_nat. lia. }
    iPoseProof (gl_fuel_eq_set _ 0 _ (3 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    lwp_bind (AllocN _ _).
    iPoseProof (gl_fuel_eq_set _ 0 _ (2 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_alloc _ ∅ 0 with "[$Tx $TG $F]"). 1: done.
    iIntros (curr) "((_& Tx& TG& _)& Ptr_curr& _)".
    lwp_bind (AllocN _ _).
    iPoseProof (gl_fuel_eq_set _ 0 _ (1 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_alloc _ ∅ 0 with "[$Tx $TG $F]"). 1: done.
    iIntros (next) "((_& Tx& TG& _)& Ptr_next& _)".
    iPoseProof (gl_fuel_eq_set _ 0 _ (0 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_pair. simpl.
    iFrame "Tx TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> Tx TG _ !> QLC !>".
    lwp_finish.
    iMod (gl_until_done_alloc) as "(%κu& #Gk& [Gck1 Gck2]& #Gdk& ACC)".
    iDestruct "Ptr_curr" as "[Ptr_curr Ptr_curr0]".
    iMod (gl_always_alloc) as "(%κ& _& _& #Gda& ACC2)".
    iMod ("ACC" $! _ N_eventually True%I (curr ↦{#(1/2)} #(0)%Z ∗ gl_current κu 0 (1/2)%Qp ∗ R)%I
           with "[$Ptr_curr0 $Gck2 $HR]") as "#GU".
    iMod (ghost_map_alloc ({[0%Z := κu]} : gmap Z gl_id)) as "(%γt& GMAt& GMEt)".
    rewrite big_sepM_singleton. iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
    iApply ("HΦ" $! γt). iFrame "Tx TG QLC".
    rewrite /is_fair_lock. iExists next, curr. iSplitR; first done.
    iFrame "Gda". iMod ("ACC2" $! _ _ _ with "[-]") as "$"; last done.
    iNext. rewrite /lock_proto. iFrame "Ptr_next Ptr_curr GMAt Gk Gck1 GU GMEt".
    iSplitR; first done. iSplitR.
    { iPureIntro. rewrite dom_singleton_L. intros. set_solver. }
    iSplitR.
    { rewrite big_sepM_singleton. eauto. }
    iIntros "%". lia.
  Qed.

  (** FIXME: ordi notation levels *)
  Local Lemma acquire_spec i q G γt lnc ℓ R μ lc :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ([∗ set] k ∈ dom G, gl_fuel k ((ℓ ⊕ (ω ⊕ 1)))%ordi ▽%M) ∗
         is_fair_lock γt lnc ℓ R }}}
      TicketLock.acquire lnc @ i
    l{{{ κu, RET #();
         thread_exec i q ∗ th_obls i (<[κu:=0]>G) 1 ∗ £ lc ∗
         (⌜ G !! κu = None ⌝) ∗ gl_fuel κu ℓ μ ∗
         lock_token γt lnc κu R ∗ R }}}.
  Proof.
    iIntros (Φ) "(Tx& TG& Fs& #IFL) HΦ".
    rewrite /TicketLock.acquire.
    iAssert (|==>[∗ set] k ∈ dom G, gl_fuel k (ℓ ⊕ ω)%ordi (100 ⊕ ▽)%M)%I with "[Fs]" as ">Fs".
    { rewrite -big_sepS_bupd. iApply (big_sepS_impl with "Fs"). iIntros "!> %% GF".
      iApply (gl_fuel_extend with "GF"). rewrite -hessenberg.add_assoc. apply hessenberg.add_lt_l.
      rewrite ord.from_nat_1. apply ord.S_pos. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs Fsloop]".
    iPoseProof (gl_fuel_eq_set _ 0 _ (99 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    (* argument *)
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 100. iSplitR; first done. iIntros "!> Tx TG _ !> LC !>".
    (* get fst and snd of the argument *)
    (* fst *)
    iDestruct "IFL" as "(%&%& %& %κa& #Gdka& #INV)". subst lnc.
    iPoseProof (gl_fuel_eq_set _ 0 _ (98 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_proj. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    iPoseProof (gl_fuel_eq_set _ 0 _ (97 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_let. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    iPoseProof (gl_fuel_eq_set _ 0 _ (96 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    (* snd *)
    iPoseProof (gl_fuel_eq_set _ 0 _ (95 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_proj. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    iPoseProof (gl_fuel_eq_set _ 0 _ (94 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_let. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    iPoseProof (gl_fuel_eq_set _ 0 _ (93 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    (* FAA *)
    iPoseProof (gl_fuel_eq_set _ 0 _ (92 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_bind (FAA _ _).
    (** FIXME: Make IntoAcc instances for temporal acc rules? *)
    (* iInv "INV" as "H". *)
    iMod (gl_always_acc with "Gdka INV") as "[H ACC]". 1: set_solver.
    (** TODO: better rules for tlc / later credits. *)
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lifting.lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%& PtrNext& PtrCurr& GMAt& %Boundc& %Domt& #HMt& %κp& #Gkp& #GMEtkp& #GEkp& Gckp& Wlkp)".
    iApply lwp_sfgupd.
    iApply (lwp_faa _ ∅ 0 with "[$Tx $TG $F $PtrNext]").
    1: done.
    iIntros "((_& Tx& TG& _)& PtrNext)".
    (* Alloc a new ghost lock for eventually unlock *)
    iMod (gl_until_alloc _ _ _ _ (ℓ ⊕ Z.to_nat (n + 1)%Z)%ordi ((50 ⊕ (50 × ▽)) ⊕ ▽)%M with "TG")
      as "(%κu& %LUku& TG& Gcku& #Glku& #Gku& GF& #Wlku& ALLOC)".
    iMod ("ALLOC" $! _ N_eventually True%I (curr ↦{#1 / 2} #(n + 1) ∗ gl_current κu 0 (1 / 2) ∗ R)%I with "[//]") as "#GUku".
    iPoseProof (gl_fuel_add with "GF") as "[GF QGF]".
    iMod (gl_fuel_extend _ ℓ _ μ with "QGF") as "QGF".
    { apply hessenberg.add_lt_l. rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
    (* Update tickets map to relate κu with my ticket. *)
    iMod (ghost_map_insert_persist (n + 1)%Z κu with "GMAt") as "[GMAt #GMEtku]".
    { apply not_elem_of_dom. intros IN. apply Domt in IN. lia. }
    (* Two cases: c < n (need to loop) or c = n (acquire right away). *)
    assert (CASE : (c < n)%Z ∨ (c = n)) by lia. destruct CASE as [LTc | <-].
    - assert (LTn : (0 < n)%Z) by lia.
      iPoseProof ("Wlkp" with "[//]") as "#Wlkp".
      (* Close the always. *)
      iModIntro.
      iMod ("ACC" with "[PtrNext PtrCurr GMAt Gcku]") as "_".
      { iNext. iUnfold lock_proto. iFrame "PtrNext PtrCurr GMAt Gcku Gku GUku GMEtku". iSplitR.
        { iPureIntro. lia. }
        iSplitR.
        { iPureIntro. rewrite dom_insert_L. intros. apply elem_of_union in H. destruct H.
          - set_solver.
          - apply Domt in H. lia. }
        iSplitR.
        { rewrite big_sepM_insert.
          - iFrame "HMt". iIntros "%". lia.
          - apply not_elem_of_dom. intros IN. apply Domt in IN. lia. }
        replace (n + 1 - 1)%Z with n by lia. eauto. }
      iModIntro.
      iClear "HMt Glku Gku Wlku". clear dependent c tickets. rename n into my.
      (* Update th_obls's fuels. *)
      iPoseProof (gl_fuel_add with "GF") as "[GF GFloop]".
      iMod (gl_fuel_mon_set _ (ℓ ⊕ Z.to_nat (my + 1))%ordi _ (50 × ▽)%M with "Fsloop") as "Fsloop".
      { etrans; first eapply η_mono. apply measure_extend. apply hessenberg.lt_add_r. apply ord.omega_upperbound. }
      iPoseProof (big_sepS_insert _ (dom G) κu with "[$Fsloop $GFloop]") as "Fsloop".
      { apply not_elem_of_dom; auto. }
      iPoseProof (gl_fuel_eq_set _ _ 0 _ (42 ⊕ 50)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[_ Fs]".
      iPoseProof (big_sepS_insert _ (dom G) κu with "[$Fs GF]") as "Fs".
      { apply not_elem_of_dom; auto. }
      { erewrite gl_fuel_eq. 1: eauto. rewrite !measure_nat. done. }
      rewrite -!(dom_insert_L G κu 0).
      iPoseProof (gl_fuel_eq_set _ 0 _ (49 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_let. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (48 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_lam. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (47 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_closure. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      (* Witness induction. *)
      remember (<[κu:=0]> G) as G'. rewrite -!HeqG'.
      iPoseProof (wit_fuels_init with "Wlkp") as "(%& WFs0)".
      iMod (wit_fuels_add_map _ _ _ _ _ ((λ _, ((ℓ ⊕ Z.to_nat (my + 1))%ordi, 50 : measurable_syntax)) <$> G')
             with "WFs0 [Fsloop]") as "WFs".
      { rewrite big_sepM_fmap -big_sepM_dom. iApply (big_sepM_impl with "Fsloop"). iIntros "!> %%% F".
        iFrame. iPureIntro. apply hessenberg.lt_add_r. apply ordArith.lt_from_nat. lia. }
      iClear "Wlkp WFs0". rewrite map_union_empty. iRevert "WFs".
      iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
      iIntros "WFs".
      iPoseProof (gl_fuel_eq_set _ 0 _ (46 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_lam. simpl.
      iFrame "Tx TG F". iExists _, ({[ κp := 0 ]}), 99. iSplitR.
      { rewrite big_sepM_singleton. auto. }
      iIntros "!> Tx TG WDp !> LC2 !>". rewrite (big_sepM_singleton _ κp).
      lwp_bind (Load _).
      iMod (gl_always_acc with "Gdka INV") as "[H ACC]". 1: set_solver.
      (** TODO: better rules for tlc / later credits. *)
      iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
      iApply (lifting.lwp_lc_later with "LC1"). iNext.
      iDestruct "H" as "(%&%&%& PtrNext& PtrCurr& GMAt& %Boundc& %Domt& #HMt& H)".
      (* Two cases: it's my turn, or not. *)
      destruct (decide (my = c)).
      + iClear "Gkp IHα WFs WDp LC2". subst c.
        iPoseProof (ghost_map_lookup with "GMAt GMEtkp") as "%LUmy".
        iPoseProof (big_sepM_lookup _ _ my κp with "HMt") as "Gdkp0". 1: auto.
        iPoseProof ("Gdkp0" with "[//]") as "#Gdkp". iClear "Gdkp0".
        iMod (gl_until_retrieve with "Gckp Gdkp GEkp") as "[HU ACC2]".
        { apply N_subseteq_1. }
        (** TODO: better rules for tlc / later credits. *)
        iPoseProof (tlc_split_nat 1 97 with "LC") as "[LC1 LC]".
        iApply (lifting.lwp_lc_later with "LC1"). iNext.        
        iDestruct "HU" as "(Gc1& PtrCurr0& Gc2& HR)". iCombine "Gc1 Gc2" as "Gc".
        (* FIXME: find a better way to eliminate modality after forall. *)
        iPoseProof ("ACC2" with "Gc") as "ACC2". iMod ("ACC2" $! _) as "ACC2".
        iPoseProof (gl_fuel_eq_set _ 0 _ (45 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr]"). 1: done.
        iIntros "((_& Tx& TG& _)& PtrCurr)".
        iMod "ACC2" as "_". iModIntro. iMod ("ACC" with "[PtrNext GMAt H PtrCurr]") as "_".
        { iNext. iUnfold lock_proto. iFrame. eauto. }
        iModIntro. iClear "GMEtkp GEkp HMt Gdkp". clear dependent tickets n.
        iPoseProof (gl_fuel_eq_set _ 0 _ (44 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_op. simpl.
        iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
        rewrite bool_decide_eq_true_2; last done.
        iPoseProof (gl_fuel_eq_set _ 0 _ (43 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_if_true. simpl.
        iFrame "Tx TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> Tx TG _ !> QLC !>".
        lwp_finish.
        subst G'. iApply ("HΦ" with "[$Tx $TG $QLC $QGF PtrCurr0 $HR]"). iSplit; auto.
        iUnfold lock_token. iFrame "PtrCurr0 GUku". eauto.
      + (* Not my turn, proceed to induction. *)
        iPoseProof (gl_fuel_eq_set _ 0 _ (45 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr]"). 1: done.
        iIntros "((_& Tx& TG& _)& PtrCurr)". iMod ("ACC" with "[PtrNext GMAt H PtrCurr]") as "_".
        { iNext. iUnfold lock_proto. iFrame. eauto. }
        iModIntro. iClear "HMt". clear dependent n tickets.
        iPoseProof (gl_fuel_eq_set _ 0 _ (44 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_op. simpl.
        iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
        rewrite bool_decide_eq_false_2; cycle 1.
        { intro. inv H. }
        iPoseProof (gl_fuel_eq_set _ 0 _ (43 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_if_false. simpl.
        iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
        (* Two cases: κp is not done (do induction), or done. *)
        iDestruct "WDp" as "[Wkp | #Gdkp]".
        { iMod (wit_fuels_decr with "WFs Wkp") as "(%& %LTα& WFs& Fs')".
          iClear "Fs LC". iAssert (|==> ([∗ set] k ∈ dom G', gl_fuel k 0 47))%I with "[Fs']" as ">Fs".
          { rewrite -big_sepS_bupd big_sepM_fmap big_sepM_dom. iApply (big_sepS_impl with "Fs'").
            iIntros "!> %% F". iApply (gl_fuel_mon with "F").
            rewrite !measure_nat. apply OrdArith.le_from_nat. lia. }
          iApply ("IHα" $! α0 LTα with "HΦ Gckp LC2 QGF Fs Tx TG WFs").
        }
        iPoseProof (gl_fuel_eq_set _ 0 _ (42 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_lam. simpl.
        iFrame "Tx TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
        lwp_bind (Load _).
        (** TODO: better rules sfgupd and fupd masks. *)
        iMod (gl_until_retrieve with "Gckp Gdkp GEkp") as "[HU ACC2]".
        { set_solver. }
        (** TODO: better rules for tlc / later credits. *)
        iPoseProof (tlc_split_nat 1 97 with "LC") as "[LC1 LC]".
        iApply (lifting.lwp_lc_later with "LC1"). iNext.
        iDestruct "HU" as "(Gc1& PtrCurr0& Gc2& HR)". iCombine "Gc1 Gc2" as "Gc".
        (* FIXME: find a better way to eliminate modality after forall. *)
        iPoseProof ("ACC2" with "Gc") as "ACC2". iMod ("ACC2" $! _) as "ACC2".
        iPoseProof (gl_fuel_eq_set _ 0 _ (41 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr0]"). 1: done.
        iIntros "((_& Tx& TG& _)& PtrCurr0)".
        iMod "ACC2" as "_". iModIntro.
        iClear "Gkp GMEtkp GEkp IHα Gdkp WFs LC2". clear dependent α c.
        iPoseProof (gl_fuel_eq_set _ 0 _ (40 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_op. simpl.
        iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
        rewrite bool_decide_eq_true_2; last done.
        iPoseProof (gl_fuel_eq_set _ 0 _ (39 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_if_true. simpl.
        iFrame "Tx TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> Tx TG _ !> QLC !>".
        lwp_finish.
        subst G'. iApply ("HΦ" with "[$Tx $TG $QLC $QGF PtrCurr0 $HR]"). iSplit; auto.
        iUnfold lock_token. iFrame "PtrCurr0 GUku". eauto.
    - iPoseProof (ghost_map_lookup with "GMAt GMEtkp") as "%LUmy".
      iPoseProof (big_sepM_lookup _ _ c κp with "HMt") as "Gdkp0".
      { rewrite lookup_insert_ne in LUmy; auto. lia. }
      iPoseProof ("Gdkp0" with "[//]") as "#Gdkp". iClear "Gdkp0".
      iApply sfgupd_fupd_acc.
      iMod (gl_until_retrieve with "Gckp Gdkp GEkp") as "[HU ACC2]".
      { apply N_subseteq_1. }
      (** TODO: better rules for tlc / later credits. *)
      iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
      iApply (lc_fupd_add_later with "LC1"). iNext. iModIntro.
      iDestruct "HU" as "(Gc1& PtrCurr0& Gc2& HR)". iCombine "Gc1 Gc2" as "Gc".
      (* FIXME: find a better way to eliminate modality after forall. *)
      iPoseProof ("ACC2" with "Gc") as "ACC2". iMod ("ACC2" $! _) as "ACC2".
      iModIntro. iMod "ACC2" as "_". iModIntro. iMod ("ACC" with "[PtrCurr PtrNext Gcku GMAt]") as "_".
      { iNext. iUnfold lock_proto. iFrame. iSplitR.
        { iPureIntro. lia. }
        iSplitR.
        { iPureIntro. intros. rewrite dom_insert_L in H. apply elem_of_union in H. destruct H.
          - set_solver.
          - apply Domt in H. lia. }
        iSplitR.
        { rewrite big_sepM_insert.
          - iFrame "HMt". iIntros "%". lia.
          - apply not_elem_of_dom. intros IN. apply Domt in IN. lia. }
        eauto. }
      iClear "HMt Gkp GMEtkp GEkp Glku Gku Wlku Gdkp Fsloop Wlkp". clear dependent tickets κp.
      iModIntro.
      iPoseProof (gl_fuel_add with "GF") as "[GF _]".
      iPoseProof (gl_fuel_eq_set _ _ 0 _ (42 ⊕ 50)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[_ Fs]".
      iPoseProof (big_sepS_insert _ (dom G) κu with "[$Fs GF]") as "Fs".
      { apply not_elem_of_dom; auto. }
      { erewrite gl_fuel_eq. 1: eauto. rewrite !measure_nat. done. }
      rewrite -!(dom_insert_L G κu 0).
      iPoseProof (gl_fuel_eq_set _ 0 _ (49 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_let. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (48 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_lam. simpl.
      iFrame "Tx TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (47 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_closure. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (46 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_lam. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      lwp_bind (Load _).
      iPoseProof (gl_fuel_eq_set _ 0 _ (45 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr0]"). 1: done.
      iIntros "((_& Tx& TG& _)& PtrCurr0)".
      iPoseProof (gl_fuel_eq_set _ 0 _ (44 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_op. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      rewrite bool_decide_eq_true_2; last done.
      iPoseProof (gl_fuel_eq_set _ 0 _ (43 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_if_true. simpl.
      iFrame "Tx TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> Tx TG _ !> QLC !>".
      lwp_finish.
      iApply ("HΦ" with "[$Tx $TG $QLC $QGF PtrCurr0 $HR]"). iSplit; auto.
      iUnfold lock_token. iFrame "PtrCurr0 GUku". eauto.
  Qed.

  Local Lemma release_spec i q G γt lnc ℓ R κu lc :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ⌜ G !! κu = Some 0 ⌝ ∗ ([∗ set] k ∈ dom G, gl_fuel k 1 ▽%M) ∗
         is_fair_lock γt lnc ℓ R ∗
         lock_token γt lnc κu R ∗ R }}}
      TicketLock.release lnc @ i
    l{{{ RET #();
         thread_exec i q ∗ th_obls i (delete κu G) 1 ∗ £ lc}}}.
  Proof.
    iIntros (Φ) "(Tx& TG& %LUkl& Fs& #IFL& LT& HR) HΦ".
    rewrite /TicketLock.release.
    iMod (gl_fuel_extend_set _ 0 _ 100%M with "Fs") as "Fs".
    { apply ordArith.lt_from_nat. lia. }
    iPoseProof (gl_fuel_eq_set _ 0 _ (99 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 100. iSplitR; first done. iIntros "!> Tx TG _ !> LC !>".
    iDestruct "LT" as "(%& %& %& %& PtrCurr0& #GMEtku& #GEku)".
    subst lnc.
    iPoseProof (gl_fuel_eq_set _ 0 _ (98 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_proj. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    iPoseProof (gl_fuel_eq_set _ 0 _ (97 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_let. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    iPoseProof (gl_fuel_eq_set _ 0 _ (96 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    lwp_bind (Load _).
    iPoseProof (gl_fuel_eq_set _ 0 _ (95 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr0]"). 1: done.
    iIntros "((_& Tx& TG& _)& PtrCurr0)".
    iPoseProof (gl_fuel_eq_set _ 0 _ (94 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_op. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    (* Update curr and unlock κl. *)
    iDestruct "IFL" as "(%&%& %& %κa& #Gdka& #INV)". symmetry in H. inv H.
    (** FIXME: Make IntoAcc instances for temporal acc rules? *)
    (* iInv "INV" as "H". *)
    iMod (gl_always_acc with "Gdka INV") as "[H ACC]". 1: set_solver.
    (** TODO: better rules for tlc / later credits. *)
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lifting.lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%& PtrNext& PtrCurr& GMAt& %Boundc& %Domt& #HMt& H)".
    iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". inversion H. subst u. clear H.
    (* FIXME: does not combine the dfrac part. *)
    (* iCombine "PtrCurr PtrCurr0" as "PtrCurr" gives %?. destruct H as [_ ->]. *)
    iApply lwp_sfgupd.
    iPoseProof (gl_fuel_eq_set _ 0 _ (93 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_store _ ∅ lc with "[$Tx $TG $F PtrCurr PtrCurr0]").
    { iSplitR; first done. iSplitL "PtrCurr"; iFrame. }
    iIntros "((QLC& Tx& TG& _)& [PtrCurr PtrCurr0])".
    iApply sfgupd_fupd_acc.
    iMod (gl_until_fulfill with "TG GEku") as "[HU ACC2]".
    1: apply N_subseteq_1. 1: auto.
    iModIntro.
    iDestruct "HU" as ">(TG& GL& _)". iPoseProof ("ACC2" with "TG GL") as "ACC2".
    iMod ("ACC2" $! _) as "((TG& Gcku& #Gdku)& ACC2)".
    iModIntro. iMod ("ACC2" with "[$PtrCurr0 $Gcku $HR]") as "_".
    iModIntro. iMod ("ACC" with "[PtrNext GMAt H PtrCurr]") as "_".
    { iPoseProof (ghost_map_lookup with "GMAt GMEtku") as "%LUku".
      iNext. iUnfold lock_proto. iExists n, (c + 1)%Z, tickets. iFrame. iSplitR.
      { iPureIntro. apply elem_of_dom_2, Domt in LUku. lia. }
      iSplitR.
      { iPureIntro. intros. apply Domt in H. lia. }
      iSplitR.
      { iApply (big_sepM_impl with "HMt"). iIntros "!> %%% H %".
        assert ((k ≤ c)%Z ∨ (k = c + 1)%Z) by lia. destruct H1.
        - iApply "H". auto.
        - subst. rewrite LUku in H. inv H. eauto. }
      iDestruct "H" as "(%& $& $& $& $& H)".
      iIntros "%". iApply "H". iPureIntro. lia.
    }
    iApply ("HΦ" with "[$Tx $TG $QLC]").
  Qed.

End proof.
