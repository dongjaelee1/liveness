From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export weakestpre.
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
    λ: "curr",
      "curr" <- !"curr" + #1.

End TicketLock.

Local Definition tl_data : Type := (gl_id).

(** The CMRA we need. *)
Class ticket_lockG Σ :=
  TLockG {
      #[local] tlock_heldG :: ghost_mapG Σ Z bool;
      #[local] tlock_dataG :: ghost_mapG Σ Z tl_data;
    }.

Definition ticket_lockΣ : gFunctors :=
  #[(ghost_mapΣ Z bool); (ghost_mapΣ Z tl_data)].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Let N := nroot.@"ticket_lock".
  Let N_inv := N.@"inv".
  Let N_state := N.@"state".
  Let N_held := N.@"held".

  (** Definitions *)
  Local Definition lock_state k ℓ (curr : loc) (c : Z) : iProp Σ :=
    gl k (Z.to_nat c) ∗
    wit_layer k (Z.to_nat c) (ℓ)%ordi ∗
    gl_variant N_state k (Z.to_nat c) (curr ↦ #(c - 1)%Z) (curr ↦ #c) True.

  Local Definition lock_eventually_held kh kl γh ℓ (my : Z) (curr : loc) : iProp Σ :=
    gl kh 0 ∗
    wit_layer kh 0 (ℓ ⊕ (Z.to_nat my))%ordi ∗
    gl_variant N_held kh 0 (my ↪[γh]{#(1/2)} false) (my ↪[γh]□ true ∗ lock_state kl ℓ curr (my + 1)%Z) False.

  Local Definition lock_inv (next curr : loc) (γh γd : gname) (κl : gl_id) (ℓ : layer) (R : iProp Σ) : iProp Σ :=
    ∃ (n c : Z) (held : gmap Z bool) (data : gmap Z tl_data),
      (⌜ (0 ≤ c ≤ n)%Z ⌝) ∗
      (⌜ ∀ (x : Z), (n ≤ x)%Z → (held !! x = None) ⌝) ∗
      (⌜ ∀ (x : Z), (held !! x = None) → ((x < 0)%Z ∨ (n ≤ x)%Z)⌝) ∗
      (⌜ ∀ (x : Z), (0 ≤ x < c)%Z → held !! x = Some true ⌝) ∗
      (⌜ ∀ (x : Z), (c < x < n)%Z → held !! x = Some false ⌝) ∗
      (⌜ dom held = dom data ⌝) ∗
      next ↦ #n ∗
      ghost_map_auth γh 1 held ∗
      ghost_map_auth γd 1 data ∗
      gl_layers κl (λ v, (ℓ)%ordi) ∗
      (match held !! c with
       | Some true =>
           lock_state κl ℓ curr (c + 1)
       | _ =>
           gl_done κl (Z.to_nat c) ∗
           gl_current κl (Z.to_nat c) ∗
           lock_state κl ℓ curr c ∗
           R
       end) ∗
      ([∗ map] x ↦ h ∈ held,
         ∃ κx, x ↪[γd]□ κx ∗
               lock_eventually_held κx κl γh ℓ x curr ∗
               match h with
               | false => (x ↪[γh]{#(1/2)} false)
               | true => (x ↪[γh]□ true) ∗ gl_current κx 0
               end
      ).

  Local Definition is_fair_lock (lnc : val) (γh γd : gname) (κl : gl_id) (ℓ : layer) (R : iProp Σ) : iProp Σ :=
    ∃ (next curr : loc), ⌜lnc = (#next, #curr)%V⌝ ∧
                         inv N_inv (lock_inv next curr γh γd κl ℓ R).

  (** Properties *)
  Global Instance lock_state_persistent k ℓ curr c : Persistent (lock_state k ℓ curr c).
  Proof. rewrite /lock_state. apply _. Qed.
  Global Instance lock_eventually_held_persistent kh kl γh ℓ my curr : Persistent (lock_eventually_held kh kl γh ℓ my curr).
  Proof. rewrite /lock_eventually_held. apply _. Qed.
  Global Instance is_fair_lock_persistent lnc γh γd κl ℓ R : Persistent (is_fair_lock lnc γh γd κl ℓ R).
  Proof. rewrite /is_fair_lock. apply _. Qed.

  (** Program proofs *)
  Local Lemma init_spec i q G ℓ (R : iProp Σ) :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ([∗ set] k ∈ dom G, gl_fuel k 1 ▽%M) ∗
         R }}}
      TicketLock.init #() @ i
    l{{{ lnc γh γd κl, RET lnc;
         thread_exec i q ∗ th_obls i G 1 ∗
         is_fair_lock lnc γh γd κl ℓ R }}}.
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
    iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
    lwp_finish.
    iMod (ghost_map_alloc (∅ : gmap Z bool)) as "(%γh& GMAh& _)".
    iMod (ghost_map_alloc (∅ : gmap Z tl_data)) as "(%γd& GMAd& _)".
    iMod (gl_alloc_done _ (λ _, ℓ) 0 N_state (Z.to_nat 0%Z) (curr ↦ #(0 - 1)%Z) (curr ↦ #0%Z) True with "Ptr_curr")
      as "(%κl& Glkl& Gkl& Gckl& Gdkl& _& GVkl& Wlkl& _)".
    iMod (inv_alloc N_inv _ (lock_inv next curr γh γd κl ℓ R) with "[- HΦ Tx TG]") as "INV".
    { rewrite /lock_inv. iExists 0, 0, ∅, ∅.
      iSplitR; first done. iSplitR; first done. iSplitR.
      { iPureIntro. intros. lia. }
      iSplitR.
      { iPureIntro. intros. lia. }
      iSplitR.
      { iPureIntro. intros. lia. }
      iSplitR; first done. rewrite /lock_state.
      iFrame "Glkl Ptr_next GMAh GMAd Gdkl Gckl Gkl Wlkl GVkl HR".
      rewrite big_sepM_empty. done. }
    iApply ("HΦ" $! _ γh γd κl with "[-]"). iFrame "Tx TG".
    rewrite /is_fair_lock. iFrame. done.
  Qed.

  Local Lemma acquire_my_turn i q G κl ℓ R μ curr (c : Z) ν :
    G !! κl = None →
    l{{{ thread_exec i q ∗ th_obls i (<[κl:=ν]> G) 1 ∗
         ([∗ set] k ∈ dom (<[κl:=ν]> G), gl_fuel k 0 10) ∗
         gl_variant N_state κl ν (curr ↦ #c) (curr ↦ #(c + 1)%Z) True ∗
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
  Local Lemma acquire_spec i q G lnc γh γd κl ℓ R μ :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ([∗ set] k ∈ dom G, ∃ l, ⌜ ((ℓ ⊕ ω) < l)%ordi ⌝ ∗ gl_fuel k l ▽%M) ∗
         is_fair_lock lnc γh γd κl ℓ R }}}
      TicketLock.acquire lnc @ i
      l{{{ ν, RET #();
           thread_exec i q ∗ th_obls i (<[κl:=ν]>G) 1 ∗ ⌜ G !! κl = None ⌝ ∗
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
    (* Alloc a new ghost lock *)
    iDestruct "H" as "(GMAh& GMAd& #Glkl& Hc& HM)".
    iMod (ghost_map_insert n%Z false with "GMAh") as "[GMAh GMEh]".
    { eapply HI2. lia. }
    iDestruct "GMEh" as "[GMEh0 GMEh]".
    iMod (gl_alloc_obl _ _ _ _ (λ _, (ℓ ⊕ Z.to_nat (n)%Z)%ordi) (10 ⊕ (10 × ▽) ⊕ (10 × ▽))%M N_held 0
            ((n)%Z ↪[γh]{#(1/2)%Qp} false)
            ((n)%Z ↪[γh]□ true ∗ lock_state κl ℓ curr (n + 1)%Z)
            False with "TG GMEh0")
      as "(%κh& %NinGkh& TG& #Glkh& #Gkh& Fkh& #GVkh& #Wlkh& _)".
    iMod (ghost_map_insert (n)%Z κh with "GMAd") as "[GMAd GMEd]".
    { rewrite -not_elem_of_dom -HI6 not_elem_of_dom. eapply HI2. lia. }
    iMod (ghost_map_elem_persist with "GMEd") as "#GMEd".
    (* Two cases: n = c (acquire right away) or n ≠ c (need to loop). *)
    destruct (decide (n = c)).
    - subst n. assert (HcNone : held !! c = None).
      { apply HI2. lia. }
      rewrite HcNone. iDestruct "Hc" as "(#Gdkl& Gckl& (#Gkl& #Wlkl& #GVkl)& HR)".
      (** TODO: better interface for fupd-sfgupd-fupd? *)
      iApply sfgupd_trans.
      (* Lock the ghost lock κl. *)
      iApply (sfgupd_fupd_acc).
      iMod (gl_lock _ _ _ _ _ _ _ (100 ⊕ μ)%M N_state _ (Z.to_nat (c + 1)%Z) _ _ _ (curr ↦ #c) (curr ↦ #(c + 1)%Z) True
             with "Gckl Gdkl GVkl") as "(>H& ACC)".
      { apply Z2Nat.inj_lt; lia. }
      { assert (N_state ## N_inv). 1: by apply ndot_ne_disjoint. set_solver. }
      iDestruct "H" as "(Gckl& PtrCurr)".
      iModIntro. iMod ("ACC" with "TG Gckl Glkl [//] PtrCurr") as "ACC".
      iModIntro. iMod ("ACC") as "(TG& %NinGkl& #Gkl2& Gfkl& #GVkl2& #Wlkl2& _)".
      apply lookup_insert_None in NinGkl. destruct NinGkl as [NinGkl Nekhl].
      (* Set hold = true. *)
      iModIntro. iApply (sfgupd_fupd_acc).
      iMod (gl_unlock with "TG GVkh") as "(>H& ACC)".
      { assert (N_held ## N_inv). 1: by apply ndot_ne_disjoint. set_solver. }
      { rewrite lookup_insert_ne; auto. by rewrite lookup_insert_eq. }
      iDestruct "H" as "(TG& GLkh& GMEh2)". iCombine "GMEh GMEh2" as "GMEh".
      iMod (ghost_map_update true with "GMAh GMEh") as "[GMAh GMEh]".
      iMod (ghost_map_elem_persist with "GMEh") as "#GMEh".
      iModIntro. iMod ("ACC" with "TG GLkh [$GMEh]") as "ACC".
      { iEval (rewrite /lock_state). replace (c + 1 - 1)%Z with c by lia. eauto. }
      iModIntro. iMod "ACC" as "(TG& Gckh& #Gdkh)".
      rewrite (delete_insert_ne _ κh κl); last eauto. rewrite (delete_insert_id G κh); last eauto.
      rewrite (insert_insert_eq held c).
      iIntros "!> !>". iSplitL "HM PtrNext GMAd GMAh Gckh".
      { iEval (rewrite /lock_inv). iNext. iExists (c + 1)%Z, c, (<[c:=true]> held), (<[c:=κh]> data).
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
        { iPureIntro. rewrite !dom_insert_L HI6. set_solver. }
        iFrame "PtrNext GMAd GMAh Glkl". iSplitL "".
        { rewrite lookup_insert_eq /lock_state. replace (c + 1 - 1)%Z with c by lia. eauto. }
        iApply (big_sepM_insert); first eauto. iFrame.
        rewrite /lock_eventually_held. eauto.
      }
      iClear "Glkl Glkh Gkh GVkh Wlkh GMEd Gdkl Gkl Wlkl GVkl GMEh Gdkh Fkh".
      clear dependent held data κh. clear HI1.
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
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iMod (gl_fuel_mon_set _ 0 _ 10 with "Fs") as "Fs".
      { rewrite !measure_nat. apply OrdArith.le_from_nat. lia. }
      iApply (acquire_my_turn _ _ _ _ _ R with "[$Tx $TG $Fs $GVkl2 $Gfkl $HR]").
      1: auto.
      iApply "HΦ".
    - rename n0 into NotMyTurn. assert (MyPos : (0 < n)%Z) by lia.
      (* Get the promise of my previous owner. *)
      assert (Prev : is_Some (held !! (n - 1)%Z)).
      { destruct (held !! (n - 1)%Z) eqn:?; eauto. apply HI3 in Heqo. lia. }
      destruct Prev as (b& Prev). iPoseProof (big_sepM_lookup_acc _ _ (n - 1)%Z with "HM") as "[Hm HM]".
      1: eauto.
      iDestruct "Hm" as "(%κp& #pGMEd& #pLEH& Hm)". iPoseProof ("HM" with "[Hm]") as "HM".
      { iFrame. eauto. }
      (* Close the invariant. *)
      iIntros "!> !>". iSplitL "Hc HM PtrNext GMAh GMEh GMAd".
      { rewrite /lock_inv /lock_eventually_held.
        iExists (n + 1)%Z, c, (<[(n)%Z:=false]> held), (<[(n)%Z:=κh]> data). iSplitR.
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
        { iPureIntro. rewrite !dom_insert_L HI6. set_solver. }
        rewrite (lookup_insert_ne held n c); last auto.
        iFrame "PtrNext GMAh GMAd Glkl Hc". iNext. iApply big_sepM_insert.
        { apply HI2. lia. }
        iFrame "HM". iFrame "GMEd GMEh". eauto.
      }
      iClear "Glkl Glkh Gkh GVkh Wlkh". clear dependent held data c b.
      (* Update th_obls' fuels. *)
      iPoseProof (gl_fuel_add with "Fkh") as "[Fkh1 Fkh2]".
      iMod (gl_fuel_mon_set _ (ℓ ⊕ Z.to_nat n)%ordi _ ((10 × ▽) ⊕ (10 × ▽))%M with "Fsloop") as "Fsloop".
      { etrans; first eapply η_mono. apply measure_extend. apply hessenberg.lt_add_r. apply ord.omega_upperbound. }
      iPoseProof (big_sepS_insert _ (dom G) κh with "[$Fsloop $Fkh2]") as "Fsloop".
      { apply not_elem_of_dom; auto. }
      rewrite -(dom_insert_L G κh 0). iPoseProof (gl_fuel_add_set with "Fsloop") as "[Fsloop1 Fsloop2]".
      iPoseProof (gl_fuel_eq_set _ _ 0 _ (82 ⊕ 10)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. reflexivity. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs2 Fs]".
      iPoseProof (big_sepS_insert _ (dom G) κh with "[$Fs Fkh1]") as "Fs".
      { apply not_elem_of_dom; auto. }
      { erewrite gl_fuel_eq. 1: eauto. rewrite !measure_nat. done. }
      rewrite -(dom_insert_L G κh 0).
      iPoseProof (gl_fuel_eq_set _ 0 _ (9 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_let. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (8 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_lam. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      iPoseProof (gl_fuel_eq_set _ 0 _ (7 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (gl_fuel_add_set with "Fs") as "[Fs F]".
      lwp_closure. simpl.
      iFrame "Tx TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> Tx TG _ !> _ !>".
      (* First witness induction. *)
      remember (<[κh:=0]> G) as G'. rewrite -!HeqG'.
      iDestruct "pLEH" as "(#Gkp& #Wlkp& #GVkp)".
      iPoseProof (wit_fuels_init with "Wlkp") as "(%& WFs0)".
      iMod (wit_fuels_add_map _ _ _ _ _ ((λ _, ((ℓ ⊕ Z.to_nat n)%ordi, 10 : measurable_syntax)) <$> G')
             with "WFs0 [Fsloop1]") as "WFs".
      { rewrite big_sepM_fmap -big_sepM_dom. iApply (big_sepM_impl with "Fsloop1"). iIntros "!> %%% F".
        iFrame. iPureIntro. apply hessenberg.lt_add_r. apply ordArith.lt_from_nat. lia. }
      iClear "Wlkp WFs0 Fs". rewrite map_union_empty. iRevert "WFs".
      iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
      iIntros "WFs".

      TODO
      

      
      iApply fupd_lwp. iInv "INV" as "H".
      (* TODO: better lc interface *)
      iPoseProof (tlc_split_nat 98 1 with "LC") as "[LC LC1]". iApply (lc_fupd_elim_later with "LC1"). iNext.
      iDestruct "H" as "(%n'& %c& %& %& %HI1& %HI2& %HI3& %HI4& %HI5& PtrNext& GMAh& GMAd& #Glkl& Hc& HM)".
      

  Abort.

  Local Lemma release_spec i q G κu ν γ lk R :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ⌜ G !! κu = Some ν ⌝ ∗ ([∗ map] k ↦ v ∈ G, gl_fuel k 1 ▽%M) ∗
         is_lock γ lk R ∗ locked γ ∗ R }}}
      TicketLock.release lk @ i
    l{{{ RET #(); thread_exec i q ∗
                  th_obls i (delete κu G) 1}}}.
  Proof.
  Abort.



  Lemma mp_writer_spec i l :
    l{{{ ∃ k, mp k l ∗
              thread_exec i 1 ∗ th_obls i (<[k:=0]>∅) 1 ∗
              gl_fuel k 0 10 }}}
      writer #l @ i
    l{{{ RET #(); lift_term i fork_post #() }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    (* iApply lwp_sfgupd. *)
    iDestruct "HP" as "(%& (#Gwfk& #Gk& #Wkv& #GVkv)& Tx& TG& Gfk)".
    rewrite /writer /=.
    iMod (gl_fuel_lt k 0 _ 9 with "Gfk") as "[Gfk Gfk1]".
    { rewrite !measure_nat. apply OrdArith.lt_from_nat. lia. }
    (* Pure steps *)
    lwp_lam. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done.
    iSplitL "Gfk1".
    { iModIntro. rewrite big_sepM_singleton. iFrame. }
    iIntros "!> Tx TG _ !> _ !>".
    lwp_finish.
    rewrite (gl_fuel_eq k 0 0 9 (8 ⊕ 1)%M); cycle 1.
    { rewrite measure_add !measure_nat. rewrite -Hessenberg.add_from_nat. reflexivity. }
    iPoseProof (gl_fuel_add with "Gfk") as "[Gfk Gfk1]".
    lwp_bind (Store _ _).
    iMod (gl_unlock with "TG GVkv") as "[>(TG& Glk& VP) ACC]".
    { set_solver. }
    { rewrite lookup_insert_eq. auto. }
    iApply lwp_sfgupd.
    iApply (lwp_store _ ∅ 0 with "[$VP $Tx $TG Gfk1]").
    { rewrite !big_sepM_singleton. iFrame. by iApply big_sepM_empty. }
    iIntros "[(_& Tx& TG& _) ptl]".
    iPoseProof ("ACC" with "TG Glk ptl") as ">ACC".
    iModIntro. iMod "ACC" as "(TG& Gc& #Gd)". iModIntro.
    (* simpl. *)
    lwp_pure.
    simpl. iFrame "Tx". iExists ⊤, ∅, ∅, 0. iSplitR; first done. iModIntro. iSplitL "TG".
    { rewrite delete_insert_id; auto. }
    iSplitR; first done. iIntros "Tx TG _ !> _ !>".
    lwp_pure.
    simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
    iSplitR; first done. iIntros "Tx TG _ !> _ !>".
    iApply (lwp_exit with "TG Tx [HΦ]").
    iModIntro. iIntros "#Tt1 #Tt2". iIntros "!>".
    iApply "HΦ". rewrite /lift_term. iFrame "Tt1".
    rewrite -thread_term_unfold. auto.
  Qed.

  Lemma mp_reader_spec i l :
    l{{{ ∃ k, mp k l ∗
              thread_exec i 1 ∗ th_obls i ∅ 1 }}}
      reader #l @ i
    l{{{ RET #(); lift_term i fork_post #() }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iDestruct "HP" as "(%& (#Gwfk& #Gk& #Wkv& #GVkv)& Tx& TG)".
    rewrite /reader /=.
    (* Liveness induction *)
    iPoseProof (wit_fuels_init with "Wkv") as "(%& Wkvfs)".
    iStopProof. induction α using WFOCM.ind. rename x into α, H into IHα.
    iIntros "(#(Gwfk& Gk& Wkv& GVkv& Wkvfs)& Tx& TG& HΦ)".
    (* Pure steps *)
    lwp_rec. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
    iSplitR; first done. iIntros "Tx TG _ !> _ !>".
    lwp_bind (Load _).
    iMod (gl_variant_acc with "GVkv") as "[>PQR ACC]". 1: set_solver.
    iDestruct "PQR" as "[[HP | HQ] | HR]"; cycle -1.
    { iDestruct "HR" as "[_ %]". done. }
    - iDestruct "HP" as "[Glk ptr]".
      iApply (lwp_load _ (<[k:=0]>∅) 0 with "[$ptr $Tx $TG]").
      { rewrite big_sepM_singleton. iSplitR; first done. auto. }
      iIntros "[(_& Tx& TG& Rs) ptr]".
      rewrite big_sepM_singleton. iDestruct "Rs" as "[Wck | #Gdk]"; cycle 1.
      { iPoseProof (gl_locked_done_false with "Glk Gdk") as "%". done. }
      iMod ("ACC" with "[Glk ptr]") as "_".
      { iModIntro. iApply gl_variant_cases_unfold. iLeft. iLeft. iFrame. }
      iModIntro.
      lwp_let. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_lam. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_op. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_if. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      iMod (wit_fuels_spend_one with "Wkvfs Wck") as "(%& %LTα& #Wkvfs'& _)".
      iApply (IHα α0 LTα). iFrame. iModIntro. auto.
    - iDestruct "HQ" as "[#Gdk ptr]".
      iApply (lwp_load _ ∅ 0 with "[$ptr $Tx $TG]").
      { iSplit; done. }
      iIntros "[(_& Tx& TG& _) ptr]".
      iMod ("ACC" with "[ptr]") as "_".
      { iModIntro. iApply gl_variant_cases_unfold. iLeft. iRight. iFrame. auto. }
      iModIntro.
      lwp_let. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_lam. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_op. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      lwp_if. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first done. iIntros "Tx TG _ !> _ !>".
      iApply (lwp_exit with "TG Tx [HΦ]").
      iModIntro. iIntros "#Tt1 #Tt2". iIntros "!>".
      iApply "HΦ". rewrite /lift_term. iFrame "Tt1".
      rewrite -thread_term_unfold. auto.
  Qed.

  Lemma mp_pre i l E G q :
    th_obls i G q ∗ l ↦ #0
    ⊢ |={E}=>g ∃ k, ⌜ G !! k = None ⌝ ∗ th_obls i (<[k:=0]>G) q ∗ gl_fuel k 0 10 ∗ mp k l.
  Proof.
    rewrite /mp /mp_proto. iIntros "[TG ptr]".
    iMod (gl_alloc_obl _ _ _ _ 0 10 N 0 (l ↦ #0) with "TG ptr") as "(%& %& TG& #Gwf& #Gl& Gf& #GV& #Wit& _)".
    iFrame "Gwf Gl GV Wit". iFrame. auto.
  Qed.

End proof.
