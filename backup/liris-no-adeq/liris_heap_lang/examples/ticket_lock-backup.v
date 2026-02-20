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

Local Definition heldT : Type := (bool).
Local Definition wonT : Type := (gl_id * bool).

(** The CMRA we need. *)
Class ticket_lockG Σ :=
  TLockG {
      #[local] tlock_heldG :: ghost_mapG Σ Z heldT;
      #[local] tlock_wonG :: ghost_mapG Σ Z wonT;
    }.

Definition ticket_lockΣ : gFunctors :=
  #[(ghost_mapΣ Z heldT); (ghost_mapΣ Z wonT)].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Let N := nroot.@"ticket_lock".
  Let N_inv := N.@"inv".
  Let N_state := N.@"state".
  Let N_held := N.@"held".

  Remark N_disj_1 : N_state ## N_inv.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_disj_2 : N_held ## N_inv.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑N_state ⊆ (⊤ : coPset) ∖ ↑N_inv.
  Proof. pose proof N_disj_1. set_solver. Qed.
  Remark N_subseteq_2 : ↑N_held ⊆ (⊤ : coPset) ∖ ↑N_inv.
  Proof. pose proof N_disj_2. set_solver. Qed.

  (** Definitions *)
  Local Definition lock_state kl γw ℓ (curr : loc) (c : Z) : iProp Σ :=
    gl kl (Z.to_nat c) ∗
    wit_layer kl (Z.to_nat c) (ℓ)%ordi ∗
    gl_variant N_state kl (Z.to_nat c) (curr ↦{#(1/2)} #(c - 1)%Z) (curr ↦{#(1/2)} #c) (∃ (κx : gl_id), c%Z ↪[γw]□ (κx, true)).

  Definition eventually_release kl γw ℓ (lnc : val) (ν : nat) : iProp Σ :=
    ∃ (next curr : loc) c κh, ⌜lnc = (#next, #curr)%V⌝ ∧ ⌜ (ν = Z.to_nat (c + 1)%Z) ⌝ ∗
                              (c%Z ↪[γw]□ (κh, true)) ∗ lock_state kl γw ℓ curr (c + 1)%Z.

  Local Definition lock_eventually_held kh kl γh γw ℓ (my : Z) (curr : loc) : iProp Σ :=
    gl kh 0 ∗
    wit_layer kh 0 (ℓ ⊕ (Z.to_nat my))%ordi ∗
    gl_variant N_held kh 0 (my ↪[γh]{#(1/2)} (false)) (my ↪[γh]□ (true) ∗ lock_state kl γw ℓ curr (my + 1)%Z) False.

  Local Definition lock_inv (next curr : loc) (γh γw : gname) (κl : gl_id) (ℓ : layer) (R : iProp Σ) : iProp Σ :=
    ∃ (n c : Z) (held : gmap Z heldT) (won : gmap Z wonT),
      (⌜ (0 ≤ c ≤ n)%Z ∧ (held !! c = Some true → (c < n)%Z) ⌝) ∗
      (⌜ ∀ (x : Z), (n ≤ x)%Z → (held !! x = None) ⌝) ∗
      (⌜ ∀ (x : Z), (held !! x = None) → ((x < 0)%Z ∨ (n ≤ x)%Z)⌝) ∗
      (⌜ ∀ (x : Z), (0 ≤ x < c)%Z → held !! x = Some true ⌝) ∗
      (⌜ ∀ (x : Z), (c < x < n)%Z → held !! x = Some false ⌝) ∗
      (⌜ held = snd <$> won ⌝) ∗
      next ↦ #n ∗
      curr ↦{#(1/2)} #c ∗
      ghost_map_auth γh 1 held ∗
      ghost_map_auth γw 1 won ∗
      gl_layers κl (λ v, (ℓ)%ordi) ∗
      (match held !! c with
       | Some true =>
           lock_state κl γw ℓ curr (c + 1)
       | _ =>
           gl_done κl (Z.to_nat c) ∗
           gl_current κl (Z.to_nat c) ∗
           lock_state κl γw ℓ curr c ∗
           R
       end) ∗
      ([∗ map] x ↦ '(κh, b) ∈ won,
         lock_eventually_held κh κl γh γw ℓ x curr ∗
         match b with
         | false => (x ↪[γh]{#(1/2)} (false))
         | true => (x ↪[γh]□ (true)) ∗ x ↪[γw]□ (κh, true)
         end
      ).

  Definition is_fair_lock (lnc : val) (γh γw : gname) (κl : gl_id) (ℓ : layer) (R : iProp Σ) : iProp Σ :=
    ∃ (next curr : loc), ⌜lnc = (#next, #curr)%V⌝ ∧
                         inv N_inv (lock_inv next curr γh γw κl ℓ R).

  (** Properties *)
  Global Instance lock_state_persistent kl γw ℓ curr c : Persistent (lock_state kl γw ℓ curr c).
  Proof. rewrite /lock_state. apply _. Qed.
  Global Instance eventually_release_persistent kl γw ℓ lnc ν : Persistent (eventually_release kl γw ℓ lnc ν).
  Proof. rewrite /eventually_release. apply _. Qed.
  Global Instance lock_eventually_held_persistent kh kl γh γw ℓ my curr : Persistent (lock_eventually_held kh kl γh γw ℓ my curr).
  Proof. rewrite /lock_eventually_held. apply _. Qed.
  Global Instance is_fair_lock_persistent lnc γh γw κl ℓ R : Persistent (is_fair_lock lnc γh γw κl ℓ R).
  Proof. rewrite /is_fair_lock. apply _. Qed.

  (** Program proofs *)
  Local Lemma init_spec i q G ℓ (R : iProp Σ) lc :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ([∗ set] k ∈ dom G, gl_fuel k 1 ▽%M) ∗
         R }}}
      TicketLock.init #() @ i
    l{{{ lnc γh γw κl, RET lnc;
         thread_exec i q ∗ th_obls i G 1 ∗ £ lc ∗
         is_fair_lock lnc γh γw κl ℓ R }}}.
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
    iMod (ghost_map_alloc (∅ : gmap Z wonT)) as "(%γw& GMAw& _)".
    iMod (ghost_map_alloc (∅ : gmap Z heldT)) as "(%γh& GMAh& _)".
    iDestruct "Ptr_curr" as "[Ptr_curr0 Ptr_curr]".
    iMod (gl_alloc_done _ (λ _, ℓ) 0 N_state (Z.to_nat 0%Z)
            (curr ↦{#(1/2)} #(0 - 1)%Z) (curr ↦{#(1/2)} #0%Z) (∃ κx, 0%Z ↪[γw]□ (κx, true))
           with "Ptr_curr") as "(%κl& Glkl& Gkl& Gckl& Gdkl& _& GVkl& Wlkl& _)".
    iMod (inv_alloc N_inv _ (lock_inv next curr γh γw κl ℓ R) with "[- HΦ Tx TG QLC]") as "INV".
    { rewrite /lock_inv. iExists 0, 0, ∅, ∅.
      iSplitR; first done. iSplitR; first done. iSplitR.
      { iPureIntro. intros. lia. }
      iSplitR.
      { iPureIntro. intros. lia. }
      iSplitR.
      { iPureIntro. intros. lia. }
      iSplitR; first done. rewrite /lock_state.
      iFrame "Glkl Ptr_next Ptr_curr0 GMAh GMAw Gdkl Gckl Gkl Wlkl GVkl HR".
      rewrite big_sepM_empty. done. }
    iApply ("HΦ" $! _ γh γw κl with "[-]"). iFrame "Tx TG QLC".
    rewrite /is_fair_lock. iFrame. done.
  Qed.

  Local Lemma acquire_my_turn i q G κl γw ℓ R μ curr (c : Z) ν :
    G !! κl = None →
    l{{{ thread_exec i q ∗ th_obls i (<[κl:=ν]> G) 1 ∗
         ([∗ set] k ∈ dom (<[κl:=ν]> G), gl_fuel k 0 10) ∗
         gl_variant N_state κl ν (curr ↦{#(1/2)} #c) (curr ↦{#(1/2)} #(c + 1)%Z) (∃ κx, (c + 1)%Z ↪[γw]□ (κx, true)) ∗
         gl_fuel κl ℓ μ ∗ R }}}
      (rec: "while" <> := if: ! #curr = #c then #() else "while" #())%V #() @ i
    l{{{ RET #();
         thread_exec i q ∗ th_obls i (<[κl:=ν]>G) 1 ∗ ⌜ G !! κl = None ⌝ ∗
         gl_fuel κl ℓ μ ∗ R }}}.
  Proof.
    iIntros (NinGkl Φ) "(Tx& TG& Fs& #GVkl& Gfkl& HR) HΦ".
    iPoseProof (gl_fuel_eq_set _ 0 _ (9 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    iPoseProof (gl_fuel_eq_set _ 0 _ (8 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_bind (Load _).
    iMod (gl_variant_acc_own with "TG GVkl") as "[>(TG& GLkl& PtrCurr) ACC]".
    1: set_solver.
    { by rewrite lookup_insert_eq. }
    iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr]"). 1: done.
    iIntros "((_& Tx& TG& _)& PtrCurr)". iMod ("ACC" with "[GLkl PtrCurr]") as "_".
    { rewrite gl_variant_cases_unfold. iNext. iLeft; iLeft. iFrame. }
    iModIntro.
    iPoseProof (gl_fuel_eq_set _ 0 _ (7 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_op. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    rewrite bool_decide_eq_true_2; last done.
    iPoseProof (gl_fuel_eq_set _ 0 _ (6 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_if_true. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    lwp_finish.
    iApply ("HΦ" with "[$Tx $TG $Gfkl $HR]"). auto.
  Qed.

  (** FIXME: ordi notation levels *)
  Local Lemma acquire_spec i q G lnc γh γw κl ℓ R μ lc :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ([∗ set] k ∈ dom G, ∃ l, ⌜ ((ℓ ⊕ ω) < l)%ordi ⌝ ∗ gl_fuel k l ▽%M) ∗
         is_fair_lock lnc γh γw κl ℓ R }}}
      TicketLock.acquire lnc @ i
      l{{{ ν, RET #();
           thread_exec i q ∗ th_obls i (<[κl:=ν]>G) 1 ∗ £ lc ∗
           ⌜ G !! κl = None ⌝ ∗ eventually_release κl γw ℓ lnc ν ∗
           gl_fuel κl ℓ μ ∗ R }}}.
  Proof.
    iIntros (Φ) "(Tx& TG& Fs& #IFL) HΦ".
    rewrite /TicketLock.acquire.
    iAssert (|==>[∗ set] k ∈ dom G, gl_fuel k (ℓ ⊕ ω)%ordi (100 ⊕ ▽)%M)%I with "[Fs]" as ">Fs".
    { rewrite -big_sepS_bupd. iApply (big_sepS_impl with "Fs"). iIntros "!> %% (%& %& GF)".
      iApply (gl_fuel_extend with "GF"). auto. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs Fsloop]".
    iPoseProof (gl_fuel_eq_set _ 0 _ (99 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    (* argument *)
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 100. iSplitR; first done. iIntros "!> Tx TG _ !> LC !>".
    (* get fst and snd of the argument *)
    (* fst *)
    iDestruct "IFL" as "(%&%&%& #INV)". subst lnc.
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
    iInv "INV" as "H".
    (** TODO: better rules for tlc / later credits. *)
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lifting.lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& %HI1& %HI2& %HI3& %HI4& %HI5& %HI6& PtrNext& H)".
    iApply lwp_sfgupd.
    iApply (lwp_faa _ ∅ 0 with "[$Tx $TG $F $PtrNext]").
    1: done.
    iIntros "((_& Tx& TG& _)& PtrNext)".
    (* Alloc a new ghost lock for the eventual held *)
    iDestruct "H" as "(PtrCurr& GMAh& GMAw& #Glkl& Hc& HM)".
    iMod (ghost_map_insert n%Z false with "GMAh") as "[GMAh GMEh]".
    { eapply HI2. lia. }
    iDestruct "GMEh" as "[GMEh0 GMEh]".
    iMod (gl_alloc_obl _ _ _ _ (λ _, (ℓ ⊕ Z.to_nat (n)%Z)%ordi) (50 ⊕ (50 × ▽) ⊕ (50 × ▽))%M N_held 0
            ((n)%Z ↪[γh]{#(1/2)%Qp} false)
            ((n)%Z ↪[γh]□ true ∗ lock_state κl γw ℓ curr (n + 1)%Z)
            False with "TG GMEh0")
      as "(%κh& %NinGkh& TG& #Glkh& #Gkh& Fkh& #GVkh& #Wlkh& _)".
    assert (HDom : dom held = dom won).
    { subst. rewrite dom_fmap_L. auto. }
    iMod (ghost_map_insert (n)%Z (κh, false) with "GMAw") as "[GMAw GMEw]".
    { rewrite -not_elem_of_dom -HDom not_elem_of_dom. eapply HI2. lia. }
    (* Two cases: n = c (acquire right away) or n ≠ c (need to loop). *)
    destruct (decide (n = c)).
    - subst n. assert (HcNone : held !! c = None).
      { apply HI2. lia. }
      assert (MyPos : (0 ≤ c)%Z) by lia.
      rewrite HcNone. iDestruct "Hc" as "(#Gdkl& Gckl& (#Gkl& #Wlkl& #GVkl)& HR)".
      (** TODO: better interface for fupd-sfgupd-fupd? *)
      iApply sfgupd_trans.
      (* Lock the ghost lock κl. *)
      iApply (sfgupd_fupd_acc).
      iMod (gl_lock _ _ _ _ _ _ (100 ⊕ μ)%M N_state _ (Z.to_nat (c + 1)%Z) _ _ _
              (curr ↦{#(1/2)} #c) (curr ↦{#(1/2)} #(c + 1)%Z) (∃ κx, (c + 1)%Z ↪[γw]□ (κx, true))
             with "Gckl Gdkl GVkl") as "(>H& ACC)".
      { apply Z2Nat.inj_lt; lia. }
      { apply N_subseteq_1. }
      iDestruct "H" as "(Gckl& PtrCurr0)".
      iMod (ghost_map_update (κh, true) with "GMAw GMEw") as "[GMAw GMEw]".
      iMod (ghost_map_elem_persist with "GMEw") as "#GMEw".
      iModIntro. iPoseProof ("ACC" with "TG Gckl Glkl") as "ACC". iMod ("ACC" $! _) as "ACC".
      iModIntro. iDestruct ("ACC") as "((TG& %NinGkl& #Gkl2& Gfkl& #Wlkl2& _)& GVkl2& ACC)".
      iMod ("GVkl2" $! _ with "PtrCurr0") as "#GVkl2".
      iMod ("ACC" with "[$GMEw]") as "_".
      apply lookup_insert_None in NinGkl. destruct NinGkl as [NinGkl Nekhl].
      (* Set hold = true. *)
      iModIntro. iApply (sfgupd_fupd_acc).
      iMod (gl_unlock with "TG GVkh") as "(>H& ACC)".
      { apply N_subseteq_2. }
      { rewrite lookup_insert_ne; auto. by rewrite lookup_insert_eq. }
      iDestruct "H" as "(TG& GLkh& GMEh2)". iCombine "GMEh GMEh2" as "GMEh".
      iMod (ghost_map_update true with "GMAh GMEh") as "[GMAh GMEh]".
      iMod (ghost_map_elem_persist with "GMEh") as "#GMEh".
      iModIntro. iPoseProof ("ACC" with "TG GLkh") as "ACC". iMod ("ACC" $! _) as "((TG& Gckh& #Gdkh)& ACC)".
      iModIntro. iMod ("ACC" with "[$GMEh]") as "_".
      { iEval (rewrite /lock_state). replace (c + 1 - 1)%Z with c by lia. eauto. }
      rewrite (delete_insert_ne _ κh κl); last eauto. rewrite (delete_insert_id G κh); last eauto.
      rewrite (insert_insert_eq held c). rewrite (insert_insert_eq won c).
      iIntros "!> !>". iSplitL "HM PtrNext PtrCurr GMAw GMAh Gckh".
      { iEval (rewrite /lock_inv). iNext. iExists (c + 1)%Z, c, (<[c:=true]> held), (<[c:=(κh, true)]> won).
        iSplitR. 1: iPureIntro; lia. iSplitR.
        { iPureIntro. intros. destruct (decide (c = x)).
          - subst. lia.
          - rewrite lookup_insert_ne; eauto. eapply HI2. lia. }
        iSplitR.
        { iPureIntro. intros. destruct (decide (c = x)).
          - subst. rewrite lookup_insert_eq in H. done.
          - rewrite lookup_insert_ne in H; eauto. apply HI3 in H. destruct H; auto. right. lia. }
        iSplitR.
        { iPureIntro. intros. destruct (decide (c = x)).
          - subst. lia.
          - rewrite lookup_insert_ne; eauto. }
        iSplitR.
        { iPureIntro. intros. lia. }
        iSplitR.
        { iPureIntro. rewrite fmap_insert. simpl. rewrite HI6. done. }
        iFrame "PtrNext PtrCurr GMAw GMAh Glkl". iSplitL "".
        { rewrite lookup_insert_eq /lock_state. replace (c + 1 - 1)%Z with c by lia. eauto. }
        iApply (big_sepM_insert).
        { rewrite -not_elem_of_dom -HDom not_elem_of_dom. auto. }
        iFrame. rewrite /lock_eventually_held. eauto.
      }
      iClear "Glkl Glkh Gkh GVkh Wlkh Gdkl Gkl Wlkl GVkl GMEh Gdkh Fkh".
      clear dependent held won. clear NinGkh Nekhl.
      (* Update th_obls' fuels. *)
      iMod (gl_fuel_mon_split _ 0 ℓ _ 92 (μ)%M with "Gfkl") as "[F Gfkl]".
      { rewrite measure_add !measure_nat. apply Hessenberg.le_add_l. apply OrdArith.le_from_nat. lia. }
      iPoseProof (big_sepS_insert _ (dom G) κl with "[$Fs $F]") as "Fs".
      { apply not_elem_of_dom; auto. }
      rewrite -(dom_insert_L G κl (Z.to_nat (c + 1))).
      iPoseProof (gl_fuel_eq_set _ 0 _ (91 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_let. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (90 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_lam. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (89 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_closure. simpl.
      iFrame "Tx TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> Tx TG _ !> QLC !>".
      iMod (gl_fuel_mon_set _ 0 _ 10 with "Fs") as "Fs".
      { rewrite !measure_nat. apply OrdArith.le_from_nat. lia. }
      iApply (acquire_my_turn _ _ _ _ _ _ R with "[$Tx $TG $Fs $GVkl2 $Gfkl $HR]").
      1: auto.
      iIntros "(Tx& TG& %& GF& HR)". iApply "HΦ". iFrame. iSplitR; eauto.
      iUnfold eventually_release. iExists _, _, _, _. iSplitR; first done. iSplitR; first done.
      iUnfold lock_state. replace (c + 1 - 1)%Z with c by lia. eauto.
    - rename n0 into NotMyTurn. assert (MyPos : (0 < n)%Z) by lia.
      (* Get the promise of my previous owner. *)
      assert (Prev : is_Some (won !! (n - 1)%Z)).
      { destruct (won !! (n - 1)%Z) eqn:?; eauto.
        rewrite -not_elem_of_dom -HDom not_elem_of_dom in Heqo. apply HI3 in Heqo. lia. }
      destruct Prev as ((κp& b)& Prev). iPoseProof (big_sepM_lookup_acc _ _ (n - 1)%Z with "HM") as "[Hm HM]".
      1: eauto.
      simpl. iDestruct "Hm" as "(#pLEH& Hm)". iPoseProof ("HM" with "[Hm]") as "HM".
      { iFrame. eauto. }
      (* Close the invariant. *)
      iIntros "!> !>". iSplitL "Hc HM PtrNext PtrCurr GMAh GMEh GMAw".
      { rewrite /lock_inv /lock_eventually_held.
        iExists (n + 1)%Z, c, (<[(n)%Z:=false]> held), (<[(n)%Z:=(κh, false)]> won). iSplitR.
        { iPureIntro; lia. }
        iSplitR.
        { iPureIntro. intros. destruct (decide (n = x)).
          - subst. lia.
          - rewrite lookup_insert_ne; eauto. eapply HI2. lia. }
        iSplitR.
        { iPureIntro. intros. destruct (decide (n = x)).
          - subst. rewrite lookup_insert_eq in H. done.
          - rewrite lookup_insert_ne in H; auto. apply HI3 in H. destruct H; eauto. lia. }
        iSplitR.
        { iPureIntro. intros. destruct (decide (n = x)).
          - subst. lia.
          - rewrite lookup_insert_ne; eauto. }
        iSplitR.
        { iPureIntro. intros. destruct (decide (n = x)).
          - subst. rewrite lookup_insert_eq. auto.
          - rewrite lookup_insert_ne; eauto. eapply HI5. lia. }
        iSplitR.
        { iPureIntro. rewrite fmap_insert HI6. done. }
        rewrite (lookup_insert_ne held n c); last auto.
        iFrame "PtrNext PtrCurr GMAh GMAw Glkl Hc". iNext. iApply big_sepM_insert.
        { rewrite -not_elem_of_dom -HDom not_elem_of_dom. apply HI2. lia. }
        iFrame "HM". iFrame "GMEh". eauto.
      }
      iClear "Glkl Glkh Gkh GVkh Wlkh". clear dependent held won c b. rename n into my.
      (* Update th_obls' fuels. *)
      iPoseProof (gl_fuel_add with "Fkh") as "[Fkh1 Fkh2]".
      iMod (gl_fuel_mon_set _ (ℓ ⊕ Z.to_nat my)%ordi _ ((50 × ▽) ⊕ (50 × ▽))%M with "Fsloop") as "Fsloop".
      { etrans; first eapply η_mono. apply measure_extend. apply hessenberg.lt_add_r. apply ord.omega_upperbound. }
      iPoseProof (big_sepS_insert _ (dom G) κh with "[$Fsloop $Fkh2]") as "Fsloop".
      { apply not_elem_of_dom; auto. }
      rewrite -(dom_insert_L G κh 0). iPoseProof (gl_fuel_add_set with "Fsloop") as "[Fsloop1 Fsloop2]".
      iPoseProof (gl_fuel_eq_set _ _ 0 _ (42 ⊕ 50)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs2 Fs]".
      iPoseProof (big_sepS_insert _ (dom G) κh with "[$Fs Fkh1]") as "Fs".
      { apply not_elem_of_dom; auto. }
      { erewrite gl_fuel_eq. 1: eauto. rewrite !measure_nat. done. }
      rewrite -(dom_insert_L G κh 0).
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
      (* First witness induction. *)
      remember (<[κh:=0]> G) as G'. rewrite -!HeqG'.
      iDestruct "pLEH" as "(#Gkp& #Wlkp& #GVkp)".
      iPoseProof (wit_fuels_init with "Wlkp") as "(%& WFs0)".
      iMod (wit_fuels_add_map _ _ _ _ _ ((λ _, ((ℓ ⊕ Z.to_nat my)%ordi, 50 : measurable_syntax)) <$> G')
             with "WFs0 [Fsloop1]") as "WFs".
      { rewrite big_sepM_fmap -big_sepM_dom. iApply (big_sepM_impl with "Fsloop1"). iIntros "!> %%% F".
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
      iInv "INV" as "H". iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
      iApply (lifting.lwp_lc_later with "LC1"). iNext.
      iDestruct "H" as "(%&%&%&%& %HI1& %HI2& %HI3& %HI4& %HI5& %HI6& PtrNext& PtrCurr& H)".
      (* Two cases: it's my turn, or not. *)
      destruct (decide (my = c)).
      + iClear "Gkp GVkp IHα WFs WDp Fsloop2 Fs". clear dependent κp.
        subst c. iDestruct "H" as "(GMAh& GMAw& #Glkl& Hc& HM)".
        iPoseProof (ghost_map_lookup with "GMAw GMEw") as "%LUw".
        assert (LUh : held !! my = Some false).
        { rewrite HI6 lookup_fmap LUw. done. }
        rewrite LUh. iDestruct "Hc" as "(#Gdkl& Gckl& (#Gkl& #Wlkl& #GVkl)& HR)".
        iMod (gl_lock _ _ _ _ _ _ (42 ⊕ μ)%M _ _ (Z.to_nat (my + 1)%Z) _ _ _
                (curr ↦{#1 / 2} #(my)) (curr ↦{#1 / 2} #(my + 1)%Z) (∃ κx : gl_id, (my + 1)%Z ↪[γw]□ (κx, true))
               with "Gckl Gdkl GVkl") as "[H ACC]".
        { lia. }
        { apply N_subseteq_1. }
        iDestruct "H" as ">(Gckl& PtrCurr0)".
        iMod (ghost_map_update (κh, true) with "GMAw GMEw") as "[GMAw GMEw]".
        iMod (ghost_map_elem_persist with "GMEw") as "#GMEw".
        iPoseProof ("ACC" with "TG Gckl Glkl") as "ACC".
        iMod ("ACC" $! _) as "((TG& %NinGkl& #Gkl2& Fkl& #Wlkl2& _)& GVkl2& ACC)".
        iMod ("GVkl2" $! _ with "PtrCurr0") as "#GVkl2". iMod ("ACC" with "[$GMEw]") as "_".
        subst G'. apply lookup_insert_None in NinGkl. destruct NinGkl as [NinGkl Nekhl].
        (* Set hold = true. *)
        iPoseProof (big_sepM_delete _ _ my with "HM") as "[Hm HM]".
        1: eauto.
        simpl. iDestruct "Hm" as "((#Gkh& #Wlkh& #GVkh)& GMEh)".
        iMod (gl_unlock with "TG GVkh") as "(>H& ACC)".
        { apply N_subseteq_2. }
        { rewrite lookup_insert_ne; auto. by rewrite lookup_insert_eq. }
        iDestruct "H" as "(TG& GLkh& GMEh2)". iCombine "GMEh GMEh2" as "GMEh".
        iMod (ghost_map_update true with "GMAh GMEh") as "[GMAh GMEh]".
        iMod (ghost_map_elem_persist with "GMEh") as "#GMEh".
        iPoseProof ("ACC" with "TG GLkh") as "ACC". iMod ("ACC" $! _) as "((TG& Gckh& #Gdkh)& ACC)".
        iMod ("ACC" with "[$GMEh]") as "_".
        { iEval (rewrite /lock_state). replace (my + 1 - 1)%Z with my by lia. eauto. }
        rewrite (delete_insert_ne _ κh κl); last eauto. rewrite (delete_insert_id G κh); last eauto.
        (* Update fuels *)
        iPoseProof (gl_fuel_add with "Fkl") as "[Fkl QFkl]".
        rewrite (gl_fuel_eq _ _ 0%ordi 42 42); cycle 1.
        { rewrite !measure_nat. done. }
        iPoseProof (big_sepS_insert _ (dom G) κl with "[$Fs2 $Fkl]") as "Fs".
        { apply not_elem_of_dom; auto. }
        rewrite -(dom_insert_L G κl (Z.to_nat (my + 1))).
        iPoseProof (gl_fuel_eq_set _ 0 _ (41 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr]"). 1: done.
        iIntros "((_& Tx& TG& _)& PtrCurr)".
        iApply fupd_mask_intro_subseteq.
        { pose proof N_disj_2. set_solver. }
        iApply fupd_mask_intro_subseteq.
        { pose proof N_disj_1. set_solver. }
        iModIntro. iSplitL "PtrNext PtrCurr GMAh GMAw HM".
        { iNext. iUnfold lock_inv. iExists _, _, (<[my:=true]>(held)), (<[my:=(κh, true)]> (won)).
          iFrame "PtrNext PtrCurr GMAh GMAw Glkl". iSplitR.
          { iPureIntro. destruct HI1. split; first lia. intros _. destruct (decide (my = n)).
            - subst n. rewrite HI2 in LUh; done.
            - lia. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. apply HI2 in H. rewrite LUh in H. done.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. rewrite lookup_insert_eq in H. done.
            - rewrite lookup_insert_ne in H; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. rewrite lookup_insert_eq. done.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. lia.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. rewrite fmap_insert HI6. done. }
          rewrite lookup_insert_eq. iSplitR.
          { iUnfold lock_state. replace (my + 1 - 1)%Z with my by lia. eauto. }
          replace (<[my:=(κh, true)]> won) with (<[my:=(κh, true)]> (delete my won)).
          { iApply big_sepM_insert.
            { by rewrite lookup_delete_eq. }
            iFrame "HM". iUnfold lock_eventually_held. eauto. }
          apply insert_delete_eq.
        }
        iClear "Glkl Gdkl Gkl Wlkl GVkl Gkh Wlkh GVkh GMEh Gdkh Gckh".
        clear dependent held won n. clear NinGkh Nekhl.
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
        iApply ("HΦ" with "[$Tx $TG $QFkl $HR $QLC]"). iSplit; auto.
        iUnfold eventually_release. iExists _, _, _, _. iSplitR; first done. iSplitR; first done.
        iUnfold lock_state. replace (my + 1 - 1)%Z with my by lia. eauto.
      + iPoseProof (gl_fuel_eq_set _ 0 _ (45 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr]"). 1: done.
        iIntros "((_& Tx& TG& _)& PtrCurr)". iModIntro. iSplitL "PtrNext PtrCurr H".
        { iEval (rewrite /lock_inv). iFrame. eauto. }
        clear dependent held won.
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
          iApply ("IHα" $! α0 LTα with "HΦ LC2 GMEw Fsloop2 Fs2 Fs Tx TG WFs").
        }
        (* We do second induction: now wait for the previous owner to release the lock. *)
        iApply fupd_lwp.
        iMod (gl_variant_acc_done with "Gdkp GVkp") as "[[H | H] ACC]".
        { set_solver. }
        2:{ iDestruct "H" as ">(_& %)". done. }
        iPoseProof (tlc_split_nat 1 97 with "LC") as "[LC1 LC]".
        iApply (lc_fupd_add_later with "LC1"). iNext. replace (my - 1 + 1)%Z with my by lia.
        iDestruct "H" as "(#pGMEh& (#Gkl& #Wlkl& #GVkl))".
        iMod ("ACC" with "[]") as "_".
        { iApply gl_variant_cases_unfold. iLeft. iRight. iUnfold lock_state. iNext. eauto. }
        iModIntro.
        (* Second witness induction. *)
        iClear "Gkp GVkp IHα Gdkp pGMEh WFs LC". clear dependent κp α c n.
        iPoseProof (wit_fuels_init with "Wlkl") as "(%& WFs0)".
        iMod (wit_fuels_add_map _ _ _ _ _ ((λ _, ((ℓ ⊕ Z.to_nat my)%ordi, 50 : measurable_syntax)) <$> G')
               with "WFs0 [Fsloop2]") as "WFs".
        { rewrite big_sepM_fmap -big_sepM_dom. iApply (big_sepM_impl with "Fsloop2"). iIntros "!> %%% F".
          iFrame. iPureIntro. apply hessenberg.add_lt_l.
          rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
        iClear "Wlkl WFs0". iRename "LC2" into "LC". rewrite map_union_empty. iRevert "WFs".
        iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
        iIntros "WFs".
        iPoseProof (gl_fuel_eq_set _ 0 _ (42 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_lam. simpl.
        iFrame "Tx TG F". iExists _, ({[ κl := (Z.to_nat my) ]}), 99. iSplitR.
        { rewrite big_sepM_singleton. auto. }
        iIntros "!> Tx TG WDp !> LC2 !>". rewrite (big_sepM_singleton _ κl).
        lwp_bind (Load _).
        iInv "INV" as "H". iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
        iApply (lifting.lwp_lc_later with "LC1"). iNext.
        iDestruct "H" as "(%&%&%&%& %HI1& %HI2& %HI3& %HI4& %HI5& %HI6& PtrNext& PtrCurr& H)".
        (* Two cases: it's my turn, or not. *)
        destruct (decide (my = c)).
      * iClear "Gkl GVkl IHα WFs WDp Fs".
        subst c. iDestruct "H" as "(GMAh& GMAw& #Glkl& Hc& HM)".
        iPoseProof (ghost_map_lookup with "GMAw GMEw") as "%LUw". assert (LUh : held !! my = Some false).
        { rewrite HI6 lookup_fmap LUw. done. }
        rewrite LUh. iDestruct "Hc" as "(#Gdkl& Gckl& (#Gkl& #Wlkl& #GVkl)& HR)".
        iMod (gl_lock _ _ _ _ _ _ (42 ⊕ μ)%M _ _ (Z.to_nat (my + 1)%Z) _ _ _
                (curr ↦{#1 / 2} #(my)) (curr ↦{#1 / 2} #(my + 1)%Z) (∃ κx : gl_id, (my + 1)%Z ↪[γw]□ (κx, true))
               with "Gckl Gdkl GVkl") as "[H ACC]".
        { lia. }
        { apply N_subseteq_1. }
        iDestruct "H" as ">(Gckl& PtrCurr0)".
        iMod (ghost_map_update (κh, true) with "GMAw GMEw") as "[GMAw GMEw]".
        iMod (ghost_map_elem_persist with "GMEw") as "#GMEw".
        iPoseProof ("ACC" with "TG Gckl Glkl") as "ACC".
        iMod ("ACC" $! _) as "((TG& %NinGkl& #Gkl2& Fkl& #Wlkl2& _)& GVkl2& ACC)".
        iMod ("GVkl2" $! _ with "PtrCurr0") as "#GVkl2". iMod ("ACC" with "[$GMEw]") as "_".
        subst G'. apply lookup_insert_None in NinGkl. destruct NinGkl as [NinGkl Nekhl].
        (* Set hold = true. *)
        iPoseProof (big_sepM_delete _ _ my with "HM") as "[Hm HM]".
        1: eauto.
        simpl. iDestruct "Hm" as "((#Gkh& #Wlkh& #GVkh)& GMEh)".
        iMod (gl_unlock with "TG GVkh") as "(>H& ACC)".
        { apply N_subseteq_2. }
        { rewrite lookup_insert_ne; auto. by rewrite lookup_insert_eq. }
        iDestruct "H" as "(TG& GLkh& GMEh2)". iCombine "GMEh GMEh2" as "GMEh".
        iMod (ghost_map_update true with "GMAh GMEh") as "[GMAh GMEh]".
        iMod (ghost_map_elem_persist with "GMEh") as "#GMEh".
        iPoseProof ("ACC" with "TG GLkh") as "ACC". iMod ("ACC" $! _) as "((TG& Gckh& #Gdkh)& ACC)".
        iMod ("ACC" with "[$GMEh]") as "_".
        { iEval (rewrite /lock_state). replace (my + 1 - 1)%Z with my by lia. eauto. }
        rewrite (delete_insert_ne _ κh κl); last eauto. rewrite (delete_insert_id G κh); last eauto.
        (* Update fuels *)
        iPoseProof (gl_fuel_add with "Fkl") as "[Fkl QFkl]".
        rewrite (gl_fuel_eq _ _ 0%ordi 42 42); cycle 1.
        { rewrite !measure_nat. done. }
        iPoseProof (big_sepS_insert _ (dom G) κl with "[$Fs2 $Fkl]") as "Fs".
        { apply not_elem_of_dom; auto. }
        rewrite -(dom_insert_L G κl (Z.to_nat (my + 1))).
        iPoseProof (gl_fuel_eq_set _ 0 _ (41 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr]"). 1: done.
        iIntros "((_& Tx& TG& _)& PtrCurr)".
        iApply fupd_mask_intro_subseteq.
        { pose proof N_disj_2. set_solver. }
        iApply fupd_mask_intro_subseteq.
        { pose proof N_disj_1. set_solver. }
        iModIntro. iSplitL "PtrNext PtrCurr GMAh GMAw HM".
        { iNext. iUnfold lock_inv. iExists _, _, (<[my:=true]>(held)), (<[my:=(κh, true)]> (won)).
          iFrame "PtrNext PtrCurr GMAh GMAw Glkl". iSplitR.
          { iPureIntro. destruct HI1. split; first lia. intros _. destruct (decide (my = n)).
            - subst n. rewrite HI2 in LUh; done.
            - lia. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. apply HI2 in H. rewrite LUh in H. done.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. rewrite lookup_insert_eq in H. done.
            - rewrite lookup_insert_ne in H; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. rewrite lookup_insert_eq. done.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. lia.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. rewrite fmap_insert HI6. done. }
          rewrite lookup_insert_eq. iSplitR.
          { iUnfold lock_state. replace (my + 1 - 1)%Z with my by lia. eauto. }
          replace (<[my:=(κh, true)]> won) with (<[my:=(κh, true)]> (delete my won)).
          { iApply big_sepM_insert.
            { by rewrite lookup_delete_eq. }
            iFrame "HM". iUnfold lock_eventually_held. eauto. }
          apply insert_delete_eq.
        }
        iClear "Glkl Gdkl Gkl Wlkl GVkl Gkh Wlkh GVkh GMEh Gdkh Gckh".
        clear dependent held won n. clear NinGkh Nekhl.
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
        iApply ("HΦ" with "[$Tx $TG $QFkl $HR $QLC]"). iSplit; auto.
        iUnfold eventually_release. iExists _, _, _, _. iSplitR; first done. iSplitR; first done.
        iUnfold lock_state. replace (my + 1 - 1)%Z with my by lia. eauto.
      * iPoseProof (gl_fuel_eq_set _ 0 _ (41 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr]"). 1: done.
        iIntros "((_& Tx& TG& _)& PtrCurr)". iModIntro. iSplitL "PtrNext PtrCurr H".
        { iEval (rewrite /lock_inv). iFrame. eauto. }
        clear dependent held won n.
        iPoseProof (gl_fuel_eq_set _ 0 _ (40 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_op. simpl.
        iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
        rewrite bool_decide_eq_false_2; cycle 1.
        { intro. inv H. }
        iPoseProof (gl_fuel_eq_set _ 0 _ (39 ⊕ 1)%M with "Fs") as "Fs".
        { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
        iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
        lwp_if_false. simpl.
        iFrame "Tx TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> Tx TG _ !> QLC !>".
        (* Two cases: κl is not done (do induction), or done (my turn). *)
        iDestruct "WDp" as "[Wklp | #Gdkl]".
        { iMod (wit_fuels_decr with "WFs Wklp") as "(%& %LTα& WFs& Fs')".
          iClear "Fs LC". iAssert (|==> ([∗ set] k ∈ dom G', gl_fuel k 0 43))%I with "[Fs']" as ">Fs".
          { rewrite -big_sepS_bupd big_sepM_fmap big_sepM_dom. iApply (big_sepS_impl with "Fs'").
            iIntros "!> %% F". iApply (gl_fuel_mon with "F").
            rewrite !measure_nat. apply OrdArith.le_from_nat. lia. }
          iApply ("IHα" $! α0 LTα with "HΦ GMEw Fs2 LC2 Fs Tx TG WFs").
        }
        iClear "IHα WFs LC2". clear dependent c α.
        iApply sfgupd_elim_lwp. iApply (sfgupd_fupd_acc).
        iMod (inv_acc with "INV") as "[H ACC]". 1: set_solver.
        iPoseProof (tlc_split_nat 1 97 with "LC") as "[LC1 LC]".
        iApply (lc_fupd_add_later with "LC1"). iNext.
        iDestruct "H" as "(%&%&%&%& %HI1& %HI2& %HI3& %HI4& %HI5& %HI6& PtrNext& PtrCurr& GMAh& GMAw& #Glkl& Hc& HM)".
        iModIntro.
        (* Find out that c = my. *)
        iApply (sfgupd_fupd_acc).
        iMod (gl_variant_acc_done with "Gdkl GVkl") as "[[H | H] ACC2]".
        { apply N_subseteq_1. }
        2:{ iDestruct "H" as ">(_& %& #GMEw2)". iCombine "GMEw GMEw2" as "GMEw" gives %?. destruct H. done. }
        iMod "H". iPoseProof (pointsto_agree with "PtrCurr H") as "%Valc". inversion Valc. subst c. clear Valc.
        iMod ("ACC2" with "[H]") as "_".
        { iApply gl_variant_cases_unfold. iLeft. iRight. iNext. iFrame. auto. }
        iPoseProof (ghost_map_lookup with "GMAw GMEw") as "%LUw". assert (LUh : held !! my = Some false).
        { rewrite HI6 lookup_fmap LUw. done. }
        rewrite LUh. iDestruct "Hc" as "(_& Gckl& _& HR)".
        (* Lock the ghost lock κl. *)
        iMod (gl_lock _ _ _ _ _ _ (42 ⊕ μ)%M N_state _ (Z.to_nat (my + 1)%Z) _ _ _
                (curr ↦{#(1/2)} #my) (curr ↦{#(1/2)} #(my + 1)%Z) (∃ κx, (my + 1)%Z ↪[γw]□ (κx, true))
               with "Gckl Gdkl GVkl") as "(>H& ACC2)".
        { apply Z2Nat.inj_lt; lia. }
        { apply N_subseteq_1. }
        iDestruct "H" as "(Gckl& PtrCurr0)".
        iMod (ghost_map_update (κh, true) with "GMAw GMEw") as "[GMAw GMEw]".
        iMod (ghost_map_elem_persist with "GMEw") as "#GMEw".
        (* FIXME: Some fupd mask circus is going on here. *)
        iModIntro. iApply sfgupd_trans.
        iPoseProof ("ACC2" with "TG Gckl Glkl") as "ACC2".
        iModIntro. iMod (("ACC2" $! _)) as "((TG& %NinGkl& #Gkl2& Gfkl& #Wlkl2& _)& GVkl2& ACC2)".
        iMod ("GVkl2" $! _ with "PtrCurr0") as "#GVkl2".
        iApply sfgupd_fupd_acc. iMod ("ACC2" with "[$GMEw]") as "_". iModIntro.
        subst G'. apply lookup_insert_None in NinGkl. destruct NinGkl as [NinGkl Nekhl].
        (* Set hold = true. *)
        iPoseProof (big_sepM_delete _ _ my with "HM") as "[Hm HM]".
        1: eauto.
        simpl. iDestruct "Hm" as "((#Gkh& #Wlkh& #GVkh)& GMEh)".
        iApply (sfgupd_fupd_acc).
        iMod (gl_unlock with "TG GVkh") as "(>H& ACC2)".
        { apply N_subseteq_2. }
        { rewrite lookup_insert_ne; auto. by rewrite lookup_insert_eq. }
        iDestruct "H" as "(TG& GLkh& GMEh2)". iCombine "GMEh GMEh2" as "GMEh".
        iMod (ghost_map_update true with "GMAh GMEh") as "[GMAh GMEh]".
        iMod (ghost_map_elem_persist with "GMEh") as "#GMEh".
        iModIntro. iPoseProof ("ACC2" with "TG GLkh") as "ACC2". iMod ("ACC2" $! _) as "((TG& Gckh& #Gdkh)& ACC2)".
        iModIntro. iMod ("ACC2" with "[$GMEh]") as "_".
        { iEval (rewrite /lock_state). replace (my + 1 - 1)%Z with my by lia. eauto. }
        rewrite (delete_insert_ne _ κh κl); last eauto. rewrite (delete_insert_id G κh); last eauto.
        iModIntro. iApply fupd_mask_intro.
        { pose proof N_disj_2. set_solver. }
        iIntros "close". iMod "close" as "_". iModIntro.
        iMod ("ACC" with "[PtrNext PtrCurr GMAh GMAw HM]") as "_".
        { iNext. iUnfold lock_inv. iExists _, _, (<[my:=true]>(held)), (<[my:=(κh, true)]> (won)).
          iFrame "PtrNext PtrCurr GMAh GMAw Glkl". iSplitR.
          { iPureIntro. destruct HI1. split; first lia. intros _. destruct (decide (my = n)).
            - subst n. rewrite HI2 in LUh; done.
            - lia. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. apply HI2 in H. rewrite LUh in H. done.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. rewrite lookup_insert_eq in H. done.
            - rewrite lookup_insert_ne in H; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. rewrite lookup_insert_eq. done.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. intros. destruct (decide (my = x)).
            - subst. lia.
            - rewrite lookup_insert_ne; eauto. }
          iSplitR.
          { iPureIntro. rewrite fmap_insert HI6. done. }
          rewrite lookup_insert_eq. iSplitR.
          { iUnfold lock_state. replace (my + 1 - 1)%Z with my by lia. eauto. }
          replace (<[my:=(κh, true)]> won) with (<[my:=(κh, true)]> (delete my won)).
          { iApply big_sepM_insert.
            { by rewrite lookup_delete_eq. }
            iFrame "HM". iUnfold lock_eventually_held. eauto. }
          apply insert_delete_eq.
        }
        iModIntro. iClear "Gkl GVkl Gdkl Glkl Gkh Wlkh GVkh GMEh Gdkh Fs Gckh".
        clear dependent held won n. clear NinGkh Nekhl.
        iPoseProof (gl_fuel_add with "Gfkl") as "[F QF]".
        iAssert (|==>([∗ set] k ∈ dom (<[κl:=Z.to_nat (my + 1)%Z]> G), gl_fuel k 0 10))%I with "[Fs2 F]" as ">Fs".
        { rewrite -big_sepS_bupd dom_insert_L big_sepS_union.
          2:{ apply not_elem_of_dom in NinGkl. set_solver. }
          rewrite big_sepS_singleton. iSplitL "F".
          - iApply (gl_fuel_mon with "F"). rewrite !measure_nat. apply OrdArith.le_from_nat. lia.
          - iApply (big_sepS_impl with "Fs2"). iIntros "!> %% F".
            iApply (gl_fuel_mon with "F"). rewrite !measure_nat. apply OrdArith.le_from_nat. lia. }
        iApply (acquire_my_turn _ _ _ _ _ _ R with "[$Tx $TG $Fs $GVkl2 $QF $HR]").
        1: auto.
        iIntros "(Tx& TG& %& GF& HR)". iApply "HΦ". iFrame. iSplitR; eauto.
        iUnfold eventually_release. iExists _, _, _, _. iSplitR; first done. iSplitR; first done.
        iUnfold lock_state. replace (my + 1 - 1)%Z with my by lia. eauto.
  Qed.

  Local Lemma release_spec i q G lnc γh γw κl ℓ R ν lc :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ⌜ G !! κl = Some ν ⌝ ∗ ([∗ set] k ∈ dom G, gl_fuel k 1 ▽%M) ∗
         is_fair_lock lnc γh γw κl ℓ R ∗
         eventually_release κl γw ℓ lnc ν ∗ R }}}
      TicketLock.release lnc @ i
    l{{{ RET #();
         thread_exec i q ∗ th_obls i (delete κl G) 1 ∗ £ lc}}}.
  Proof.
    iIntros (Φ) "(Tx& TG& %LUkl& Fs& #IFL& #ER& HR) HΦ".
    rewrite /TicketLock.release.
    iMod (gl_fuel_extend_set _ 0 _ 100%M with "Fs") as "Fs".
    { apply ordArith.lt_from_nat. lia. }
    iPoseProof (gl_fuel_eq_set _ 0 _ (99 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "Tx TG F". iExists _, ∅, 100. iSplitR; first done. iIntros "!> Tx TG _ !> LC !>".
    iDestruct "IFL" as "(%&%&%& #INV)". subst lnc.
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
    (* Lookup eventually_release to load from curr. *)
    iDestruct "ER" as "(%&%&%&%&%&%& #GMEw& (#Gkl& #Wlkl& #GVkl))". symmetry in H. inv H.
    lwp_bind (Load _).
    iMod (gl_variant_acc_own with "TG GVkl") as "[>(TG& GLkl& PtrCurr) ACC]".
    1: set_solver.
    1: eauto.
    iPoseProof (gl_fuel_eq_set _ 0 _ (95 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_load _ ∅ 0 with "[$Tx $TG $F $PtrCurr]"). 1: done.
    iIntros "((_& Tx& TG& _)& PtrCurr)". iMod ("ACC" with "[GLkl PtrCurr]") as "_".
    { rewrite gl_variant_cases_unfold. iNext. iLeft; iLeft. iFrame. }
    iModIntro.
    replace (c + 1 - 1)%Z with c by lia.
    iPoseProof (gl_fuel_eq_set _ 0 _ (94 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    lwp_op. simpl.
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    (* Update curr and unlock κl. *)
    iInv "INV" as "H".
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lifting.lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& %HI1& %HI2& %HI3& %HI4& %HI5& %HI6& PtrNext& PtrCurr& GMAh& GMAw& #Glkl& Hc& HM)".
    iMod (gl_unlock with "TG GVkl") as "[H ACC]".
    1: apply N_subseteq_1.
    1: auto.
    iDestruct "H" as ">(TG& GLkl& PtrCurr0)".
    iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". inversion H. subst c0. clear H.
    (* FIXME: does not combine the dfrac part. *)
    (* iCombine "PtrCurr PtrCurr0" as "PtrCurr" gives %?. destruct H as [_ ->]. *)
    iPoseProof (gl_fuel_eq_set _ 0 _ (93 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
    iApply lwp_sfgupd.
    iApply (lwp_store _ ∅ lc with "[$Tx $TG $F PtrCurr PtrCurr0]").
    { iSplitR; first done. iSplitL "PtrCurr"; iFrame. }
    iIntros "((QLC& Tx& TG& _)& [PtrCurr PtrCurr0])".
    iPoseProof ("ACC" with "TG GLkl") as "ACC". iMod ("ACC" $! _) as "((TG& Gckl& #Gdkl)& ACC)".
    iModIntro. iMod ("ACC" with "PtrCurr0") as "_".
    iIntros "!> !>".
    iPoseProof (ghost_map_lookup with "GMAw GMEw") as "%LUw".
    iSplitL "HR PtrNext GMAh GMAw Hc HM PtrCurr Gckl".
    { iUnfold lock_inv. iNext. iExists _, _, held, won. iFrame "PtrNext PtrCurr GMAh GMAw Glkl HM".
      iClear "Hc". assert (LUhc' : held !! (c + 1)%Z ≠ Some true).
      { intro LUhc'. destruct HI1. destruct (decide (n ≤ c + 1)%Z).
        { apply HI2 in l. rewrite LUhc' in l. done. }
        destruct (decide (c < c + 1 < n)%Z).
        { apply HI5 in a. rewrite LUhc' in a. done. }
        lia. }
      iSplitR.
      { iPureIntro. destruct HI1. assert (LUh : held !! c = Some true).
        { subst. rewrite lookup_fmap LUw. done. }
        apply H0 in LUh. split; first lia. intros. rewrite H1 in LUhc'. done. }
      iSplitR; first eauto. iSplitR; first eauto. iSplitR.
      { iPureIntro. intros. destruct (decide (x = c)).
        { subst. rewrite lookup_fmap LUw. done. }
        apply HI4. lia. }
      iSplitR.
      { iPureIntro. intros. apply HI5. lia. }
      iSplitR; first eauto.
      destruct (held !! (c + 1)%Z) as [[ | ] | ] eqn:LUhc; first done.
      (* FIXME: two same proofs. *)
      1,2: iFrame. 1,2: iUnfold lock_state. 1,2: replace (c + 1 - 1)%Z with c by lia; eauto.
    }
    iApply ("HΦ" with "[$Tx $TG $QLC]").
  Qed.

End proof.
