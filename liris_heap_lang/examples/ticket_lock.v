From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
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
      #[local] tlock_ticketG :: ghost_mapG Σ Z (oid);
      #[local] tlock_ackG :: ghost_mapG Σ Z (bool);
    }.

Definition ticket_lockΣ : gFunctors :=
  #[(ghost_mapΣ Z (oid)); (ghost_mapΣ Z (bool))].

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
  Local Definition lock_proto_tf γt γa (next curr : loc) (ℓ : ord.t) (R : tf Σ) : tf Σ :=
    (∃ (n c : Z) (tickets : gmap Z oid) (acks : gmap Z bool),
        next ↦ #n ∗
        (* Thread with ticket t establishes curr ↦ t (so curr = t-1 when acquires the lock). *)
        curr ↦{#(1/2)} #c ∗
        ⟨ghost_map_auth γt 1 tickets ∗ ghost_map_auth γa 1 acks⟩ ∗
        (⌜(dom tickets = dom acks)%Z⌝) ∗
        (⌜(0 ≤ c ≤ n)%Z⌝) ∗
        (⌜ ∀ t, t ∈ dom tickets ↔ (0 ≤ t ≤ n)%Z ⌝) ∗
        ([^tf_sep map] t ↦ κ ∈ tickets,
           ⟨oblP_id κ ∗ t ↪[γt]□ κ ∗ witP_layer κ (ℓ ⊕ (Z.to_nat t%Z))%ordi⟩ ∗
           ((⌜(0 ≤ t ≤ c)%Z⌝ ∧ ⟨oblP_fulfilled κ⟩) ∨
              (⌜((c + 1)%Z ≤ t ≤ n)%Z⌝ ∧ tf_eventually N_eventually κ false (1/2) (curr ↦{#(1/2)} #t%Z ∗ R)))) ∗
        (* Thread acks its turn and acquires the lock and resources. *)
        ([^tf_sep map] t ↦ a ∈ acks,
           ((⌜(0 ≤ t ≤ c)%Z⌝ ∧ ⟨t ↪[γa]□ true⟩) ∨
              (⌜ (t = c + 1)%Z ⌝) ∨
              (⌜((c + 1)%Z < t ≤ n)%Z⌝ ∧ ⟨t ↪[γa]{#1/2} false⟩))) ∗
        ((⌜(c = n)⌝ ∧ curr ↦{#(1/2)} #c%Z ∗ R) ∨
           (⌜(c < n)%Z⌝ ∧ ((⟨(c + 1)%Z ↪[γa]{#1/2} false⟩ ∗ curr ↦{#(1/2)} #c%Z ∗ R) ∨ (⟨(c + 1)%Z ↪[γa]□ true⟩)))))%F.

  TODO

  Definition lock_token_tf γt (lnc : val) κu (R : tf Σ) : tf Σ :=
    (∃ (next curr : loc) (u : Z),
        (⌜lnc = (#next, #curr)%V⌝) ∧ (curr ↦{#(1/2)} #u%Z) ∗ ⟨(u + 1)%Z ↪[γt]□ κu⟩ ∗
        tf_eventually N_eventually κu false (1/2) (curr ↦{#(1/2)} #(u + 1)%Z ∗ R))%F.

  Definition is_fair_lock_tf γt γa (lnc : val) (ℓ : layer) (R : tf Σ) : tf Σ :=
    (∃ (next curr : loc), (⌜lnc = (#next, #curr)%V⌝) ∧
                          tf_always N_inv (lock_proto_tf γt γa next curr ℓ R))%F.

  (* Reduction to iProp. *)
  Local Definition lock_proto γt γa (next curr : loc) (ℓ : layer) (R : tf Σ) : iProp Σ :=
    ∃ (n c : Z) (tickets : gmap Z oid) (acks : gmap Z bool),
      next ↦ #n ∗
      curr ↦{#(1/2)} #c ∗
      (ghost_map_auth γt 1 tickets ∗ ghost_map_auth γa 1 acks) ∗
      (⌜(dom tickets = dom acks)%Z⌝) ∗
      (⌜(0 ≤ c ≤ n)%Z⌝) ∗
      (⌜ ∀ t, t ∈ dom tickets ↔ (0 ≤ t ≤ n)%Z ⌝) ∗
      ([∗ map] t ↦ κ ∈ tickets,
         (oblP_id κ ∗ t ↪[γt]□ κ ∗ witP_layer κ (ℓ ⊕ (Z.to_nat t%Z))%ordi) ∗
         ((⌜(0 ≤ t ≤ c)%Z⌝ ∧ oblP_fulfilled κ) ∨
            (⌜((c + 1)%Z ≤ t ≤ n)%Z⌝ ∧ ⟦tf_eventually N_eventually κ false (1/2) (curr ↦{#(1/2)} #t%Z ∗ R)⟧ₗ))) ∗
      ([∗ map] t ↦ a ∈ acks,
         ((⌜(0 ≤ t ≤ c)%Z⌝ ∧ t ↪[γa]□ true) ∨
            (⌜ (t = c + 1)%Z ⌝) ∨
            (⌜((c + 1)%Z < t ≤ n)%Z⌝ ∧ t ↪[γa]{#1/2} false))) ∗
      ((⌜(c = n)⌝ ∧ curr ↦{#(1/2)} #c%Z ∗ ⟦R⟧ₗ) ∨
         (⌜(c < n)%Z⌝ ∧ (((c + 1)%Z ↪[γa]{#1/2} false ∗ curr ↦{#(1/2)} #c%Z ∗ ⟦R⟧ₗ) ∨ ((c + 1)%Z ↪[γa]□ true)))).

  Local Definition lock_token_def γt (lnc : val) κu (R : tf Σ) : iProp Σ :=
    ∃ (next curr : loc) (u : Z),
      (⌜lnc = (#next, #curr)%V⌝) ∧ (curr ↦{#(1/2)} #u%Z) ∗ ((u + 1)%Z ↪[γt]□ κu) ∗
      ⟦tf_eventually N_eventually κu false (1/2) (curr ↦{#(1/2)} #(u + 1)%Z ∗ R)⟧ₗ.
  Local Definition lock_token_aux : seal (@lock_token_def). Proof. by eexists. Qed.
  Definition lock_token := lock_token_aux.(unseal).
  Local Definition lock_token_unseal :
    @lock_token = @lock_token_def := lock_token_aux.(seal_eq).

  Definition is_fair_lock γt γa (lnc : val) (ℓ : layer) (R : tf Σ) : iProp Σ :=
    ∃ (next curr : loc), (⌜lnc = (#next, #curr)%V⌝) ∧
                         inv N_inv (lock_proto γt γa next curr ℓ R).

  Lemma lock_proto_red γt γa next curr ℓ R :
    ⟦lock_proto_tf γt γa next curr ℓ R⟧ₗ ⊣⊢ lock_proto γt γa next curr ℓ R.
  Proof.
    rewrite /lock_proto_tf /lock_proto.
    tf_red. do 2 f_equiv. tf_red. do 2 f_equiv. tf_red. do 2 f_equiv. tf_red. do 2 f_equiv.
    tf_red. rewrite !tf_atomic_logic. f_equiv. 1: done. f_equiv. 1: done. do 5 f_equiv.
    { rewrite tf_big_opM_interp. do 3 f_equiv. do 3 tf_red. f_equiv. }
    tf_red. do 1 f_equiv.
    { rewrite tf_big_opM_interp. do 3 f_equiv. do 2 tf_red. f_equiv. }
    tf_red. rewrite !tf_atomic_logic. do 2 f_equiv. 1: done. do 2 f_equiv. done.
  Qed.

  Lemma lock_token_red γt lnc κu R :
    ⟦lock_token_tf γt lnc κu R⟧ₗ ⊣⊢ lock_token γt lnc κu R.
  Proof.
    rewrite /lock_token_tf lock_token_unseal /lock_token_def.
    tf_red. do 2 f_equiv. tf_red. do 2 f_equiv. tf_red. do 2 f_equiv.
    tf_red. rewrite !tf_atomic_logic. f_equiv. f_equiv. done.
  Qed.

  Lemma is_fair_lock_red γt γa lnc ℓ R :
    ⟦is_fair_lock_tf γt γa lnc ℓ R⟧ₗ ⊣⊢ is_fair_lock γt γa lnc ℓ R.
  Proof.
    rewrite /is_fair_lock_tf /is_fair_lock.
    tf_red. do 2 f_equiv. tf_red. do 2 f_equiv. tf_red. f_equiv. rewrite lock_proto_red. done.
  Qed.

  (** Properties *)
  Global Instance is_fair_lock_persistent γt γa lnc ℓ R : Persistent (is_fair_lock γt γa lnc ℓ R).
  Proof. rewrite /is_fair_lock. apply _. Qed.

  (** Program proofs *)
  Local Lemma init_spec i G ℓ (R : tf Σ) lc :
    l{{{ thP_obls i G 1 ∗ ([∗ set] k ∈ G, oblP_fuel k 1 ▽%M) ∗ ⟦R⟧ₗ }}}
      TicketLock.init #() @ i
    l{{{ γt γa lnc, RET lnc; thP_obls i G 1 ∗ £ lc ∗ ⟦is_fair_lock_tf γt γa lnc ℓ R⟧ₗ }}}.
  Proof.
    iIntros (Φ) "(TG& Fs& HR) HΦ".
    rewrite /TicketLock.init.
    iMod (oblP_fuel_extend_set _ 0 _ 4%M with "Fs") as "Fs".
    { apply ordArith.lt_from_nat. lia. }
    iPoseProof (oblP_fuel_eq_set _ 0 _ (3 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !>".
    lwp_bind (AllocN _ _).
    iPoseProof (oblP_fuel_eq_set _ 0 _ (2 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_alloc _ ∅ 0 with "[$TG $F]"). 1: done.
    iModIntro. iIntros (curr) "((_& TG& _)& Ptr_curr& _)".
    lwp_bind (AllocN _ _).
    iPoseProof (oblP_fuel_eq_set _ 0 _ (1 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_alloc _ ∅ 0 with "[$TG $F]"). 1: done.
    iModIntro. iIntros (next) "((_& TG& _)& Ptr_next& _)".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (0 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    iModIntro. lwp_pair. simpl.
    iFrame "TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> TG _ !> QLC !> !>".
    iMod (obl_alloc_fulfilled _ (ℓ ⊕ Z.to_nat 0)%ordi 0) as "(%κu& #Ofk& #Ok& OAcc& #Olk& _& #Wlk)".
    iDestruct "Ptr_curr" as "[Ptr_curr Ptr_curr0]".
    iMod (ghost_map_alloc ({[0%Z := κu]} : gmap Z oid)) as "(%γt& GMAt& GMEt)".
    iMod (ghost_map_alloc ({[0%Z := true]} : gmap Z bool)) as "(%γa& GMAa& GMEa)".
    rewrite !big_sepM_singleton.
    iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
    iMod (ghost_map_elem_persist with "GMEa") as "#GMEa".
    iMod (inv_alloc N_inv _ ⟦lock_proto_tf γt γa next curr ℓ R⟧ₗ with "[Ptr_next Ptr_curr0 Ptr_curr GMAt GMAa HR]") as "#Ak".
    { iNext. rewrite lock_proto_red. rewrite /lock_proto. iExists 0, 0, {[0%Z := κu]}, {[0%Z := true]}.
      iFrame "Ptr_next Ptr_curr0 GMAt GMAa". iSplitR. 1: done. iSplitR. 1: iPureIntro; lia. iSplitR.
      { iPureIntro. intros. rewrite dom_singleton_L elem_of_singleton. split; intros.
        - subst. lia.
        - lia. }
      iSplitR.
      { rewrite big_sepM_singleton. iFrame "Ok GMEt Wlk". iLeft. iFrame "Ofk". iPureIntro. lia. }
      iSplitR.
      { rewrite big_sepM_singleton. iLeft. iFrame "GMEa". iPureIntro. lia. }
      iLeft. iFrame. done. }
    iModIntro. lwp_finish.
    iApply ("HΦ" $! γt γa). iFrame "TG QLC".
    rewrite is_fair_lock_red /is_fair_lock. iExists next, curr. iSplitR; first done.
    rewrite lock_proto_red. eauto.
  Qed.

  (** FIXME: ordi notation levels *)
  Local Lemma acquire_spec i G γt γa lnc ℓ R μ lc :
    l{{{ thP_obls i G 1 ∗ ([∗ set] k ∈ G, oblP_fuel k ((ℓ ⊕ (ω ⊕ 1)))%ordi ▽%M) ∗
         is_fair_lock γt γa lnc ℓ R }}}
      TicketLock.acquire lnc @ i
      l{{{ κu, RET #();
           thP_obls i ({[κu]} ∪ G) 1 ∗ £ lc ∗
           (⌜ κu ∉ G ⌝) ∗ oblP_fuel κu ℓ μ ∗
           lock_token γt lnc κu R ∗ ⟦R⟧ₗ }}}.
  Proof.
    iIntros (Φ) "(TG& Fs& #IFL) HΦ".
    rewrite /TicketLock.acquire.
    iAssert (|==>[∗ set] k ∈ G, oblP_fuel k (ℓ ⊕ ω)%ordi (100 ⊕ ▽)%M)%I with "[Fs]" as ">Fs".
    { rewrite -big_sepS_bupd. iApply (big_sepS_impl with "Fs"). iIntros "!> %% GF".
      iApply (oblP_fuel_extend with "GF"). rewrite -hessenberg.add_assoc. apply hessenberg.add_lt_l.
      rewrite ord.from_nat_1. apply ord.S_pos. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs Fsloop]".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (99 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    (* argument *)
    lwp_lam. simpl.
    iFrame "TG F". iExists _, ∅, 100. iSplitR; first done. iIntros "!> TG _ !> LC !> !> !>".
    (* get fst and snd of the argument *)
    (* fst *)
    iDestruct "IFL" as "(%&%& %& #INV)". subst lnc.
    iPoseProof (oblP_fuel_eq_set _ 0 _ (98 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_proj. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (97 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_let. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (96 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    (* snd *)
    iPoseProof (oblP_fuel_eq_set _ 0 _ (95 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_proj. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (94 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_let. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (93 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !>".
    (* FAA *)
    iPoseProof (oblP_fuel_eq_set _ 0 _ (92 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_bind (FAA _ _).
    (* Atomic step of FAA, *)
    iModIntro. iMod (inv_acc with "INV") as "[H ACCinv]". 1: set_solver.
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    (** TODO: better rules for tlc / later credits. *)
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& (GMAt& GMAa)& %EqDom& %Boundc& %Domt& HMt& HMa& Hc)".
    iApply (lwp_faa _ ∅ 0 with "[$TG $F $PtrNext]"). 1: done.
    iIntros "((_& TG& _)& PtrNext)".
    (* Alloc a new ghost lock for eventual unlock *)
    iMod (tf_until_alloc _ _ _ _ false (ℓ ⊕ Z.to_nat (n + 1)%Z)%ordi ((50 ⊕ (50 × ▽)) ⊕ ▽)%M with "TG")
      as "(%κu& %LUku& TG& #Glku& #Gku& GF& #Wlku& ALLOC)".
    iMod ("ALLOC" $! _ N_eventually ⌜True⌝%F (curr ↦{#1 / 2} #(n + 1) ∗ R)%F with "[//]") as "[GUku GUku1]".
    iPoseProof (oblP_fuel_add with "GF") as "[GF QGF]".
    iMod (oblP_fuel_extend _ ℓ _ μ with "QGF") as "QGF".
    { apply hessenberg.add_lt_l. rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
    (* Update tickets map to relate κu with my ticket. *)
    iMod (ghost_map_insert_persist (n + 1)%Z κu with "GMAt") as "[GMAt #GMEtku]".
    { apply not_elem_of_dom. intros IN. apply Domt in IN. lia. }
    iMod (ghost_map_insert (n + 1)%Z false with "GMAa") as "[GMAa [GMEaku GMEaku1]]".
    { apply not_elem_of_dom. rewrite -EqDom. intros IN. apply Domt in IN. lia. }
    (* Close inv. *)
    iModIntro. iMod ("ACCinv" with "[$PtrNext $PtrCurr $GMAt $GMAa HMt HMa Hc GUku1 GMEaku1]") as "_".
    { iNext. iSplitR.
      { iPureIntro. rewrite !dom_insert_L EqDom. done. }
      iSplitR.
      { iPureIntro. lia. }
      iSplitR.
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
        - iFrame "Gku GMEtku Wlku". iRight. iFrame. iPureIntro. lia.
        - iApply (big_sepM_impl with "HMt"). iIntros "!> %%% H". iDestruct "H" as "($& [H | H])".
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
    iPoseProof (oblP_fuel_add with "GF") as "[GF GFloop]".
    iMod (oblP_fuel_mon_set _ (ℓ ⊕ Z.to_nat (my + 1))%ordi _ (50 × ▽)%M with "Fsloop") as "Fsloop".
    { etrans; first eapply η_mono. apply measure_extend. apply hessenberg.lt_add_r. apply ord.omega_upperbound. }
    iPoseProof (big_sepS_insert _ G κu with "[$Fsloop $GFloop]") as "Fsloop". 1: auto.
    iPoseProof (oblP_fuel_eq_set _ _ 0 _ (42 ⊕ 50)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. reflexivity. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[_ Fs]".
    iPoseProof (big_sepS_insert _ (G) κu with "[$Fs GF]") as "Fs". 1: auto.
    { erewrite oblP_fuel_eq. 1: eauto. rewrite !measure_nat. done. }
    iPoseProof (oblP_fuel_eq_set _ 0 _ (49 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_let. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (48 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (47 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_closure. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    (* Set up induction. *)
    iApply fupd_lwp. iInv "INV" as "H".
    iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& (GMAt& GMAa)& %EqDom& %Boundc& %Domt& HMt& HMa& Hc)".
    iPoseProof (ghost_map_lookup with "GMAt GMEtku") as "%LUt".
    assert (LUt' : is_Some (tickets !! my)).
    { apply elem_of_dom. apply Domt. apply elem_of_dom_2, Domt in LUt. lia. }
    destruct LUt' as [κp LUt']. iPoseProof (big_sepM_delete _ _ _ _ LUt' with "HMt") as "[(#Hkp& Hmt) HMt]".
    iPoseProof (big_sepM_delete _ _ _ _ LUt' with "[Hmt $HMt]") as "HMt".
    { iSplitR; first eauto. iFrame. }
    iSplitL "PtrNext PtrCurr GMAt GMAa HMt HMa Hc".
    { iFrame. eauto. }
    iIntros "!> !>". iDestruct "Hkp" as "(#Okp& #Mtkp& #Wlkp)".
    clear dependent n c tickets acks.
    (* Witness induction. *)
    remember ({[κu]} ∪ G) as G'.
    iPoseProof (wit_fuels_init with "Wlkp") as "(%& WFs0)".
    iMod (wit_fuels_add_map _ _ _ _ (gset_to_gmap ((ℓ ⊕ Z.to_nat (my + 1))%ordi, ms_nat 50) G')
           with "WFs0 [Fsloop]") as "WFs".
    { rewrite big_sepM_gset_to_gmap. iApply (big_sepS_impl with "Fsloop"). iIntros "!> %% F".
      iFrame. iPureIntro. apply hessenberg.lt_add_r. apply ordArith.lt_from_nat. lia. }
    iClear "Wlkp WFs0". rewrite map_union_empty. iRevert "WFs".
    iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
    iIntros "WFs".
    (* Execute loop body. *)
    iPoseProof (oblP_fuel_eq_set _ 0 _ (46 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !>".
    lwp_bind (Load _).
    (* Atomic step of Load, *)
    iModIntro. iMod (inv_acc with "INV") as "[H ACCinv]". 1: set_solver.
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    (** TODO: better rules for tlc / later credits. *)
    iPoseProof (tlc_split_nat 1 97 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& (GMAt& GMAa)& %EqDom& %Boundc& %Domt& HMt& HMa& Hc)".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (45 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_load _ {[κp]} 98%ord with "[$TG $F $PtrCurr]").
    { rewrite big_sepS_singleton. eauto. }
    iIntros "((LC'& TG& Wc)& PtrCurr)". iEval (rewrite big_sepS_singleton) in "Wc".
    (* Two cases: it's my turn, or not. *)
    destruct (decide (my = c)).
    - iClear "Okp Mtkp IHα WFs LC' Wc". clear dependent κp. subst c.
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
      iModIntro. iModIntro.
      iPoseProof (oblP_fuel_eq_set _ 0 _ (44 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
      lwp_op. simpl.
      iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
      rewrite bool_decide_eq_true_2; last done.
      iPoseProof (oblP_fuel_eq_set _ 0 _ (43 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
      lwp_if_true. simpl.
      iFrame "TG F". iExists _, ∅, lc. iSplitR; first done. iIntros "!> TG _ !> QLC !> !> !>".
      lwp_finish.
      subst G'. iApply ("HΦ" with "[$TG $QLC $QGF PtrCurr $HR GUku]"). iSplit; first auto.
      rewrite lock_token_unseal /lock_token_def. iFrame "PtrCurr GUku". eauto.
    - (* Not my turn, proceed to induction. *)
      iDestruct "Wc" as "[Wc | #Gfkp]"; cycle 1.
      { iPoseProof (ghost_map_lookup with "GMAt Mtkp") as "%LUt".
        iExFalso. iPoseProof (big_sepM_delete _ _ _ _ LUt with "HMt") as "[Hmt _]".
        iDestruct "Hmt" as "(_& [Hmt | Hmt])"; cycle 1.
        { iDestruct "Hmt" as "(_& Ukp)". iEval (rewrite /tf_eventually tf_until_logic) in "Ukp".
          iDestruct "Ukp" as "(Oa& _)". iPoseProof (oblP_assigned_fulfilled_false with "Oa Gfkp")as "%". done. }
        iDestruct "Hmt" as "(%Boundmy& _)". assert (Boundmy1 : (0 ≤ my < c)%Z) by lia.
        iPoseProof (ghost_map_lookup with "GMAa GMEaku") as "%LUa".
        iPoseProof (big_sepM_delete _ _ _ _ LUa with "HMa") as "[Hma _]".
        iDestruct "Hma" as "[Hma | [%Hma | Hma]]".
        - iDestruct "Hma" as "(%& GMEa)". iPoseProof (ghost_map_elem_agree with "GMEaku GMEa") as "%". done.
        - lia.
        - iDestruct "Hma" as "(%& _)". lia. }
      iModIntro. iMod ("ACCinv" with "[PtrNext GMAt HMt HMa PtrCurr GMAa Hc]") as "_".
      { iNext. iFrame. iSplitR. 1: auto. iSplitR; auto. }
      iModIntro. iModIntro.
      iPoseProof (oblP_fuel_eq_set _ 0 _ (44 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
      lwp_op. simpl.
      iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
      rewrite bool_decide_eq_false_2; cycle 1.
      { intro. inv H. }
      iPoseProof (oblP_fuel_eq_set _ 0 _ (43 ⊕ 1)%M with "Fs") as "Fs".
      { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
      iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
      lwp_if_false. simpl.
      iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
      iMod (wit_fuels_decr with "WFs Wc") as "(%& %LTα& WFs& Fs')".
      iClear "Fs LC". iAssert (|==> ([∗ set] k ∈ G', oblP_fuel k 0 47))%I with "[Fs']" as ">Fs".
      { rewrite -big_sepS_bupd big_sepM_gset_to_gmap. iApply (big_sepS_impl with "Fs'").
        iIntros "!> %% F". iApply (oblP_fuel_mon with "F").
        rewrite !measure_nat. apply OrdArith.le_from_nat. lia. }
      iApply ("IHα" $! α0 LTα with "HΦ GUku QGF GMEaku Fs TG LC' WFs").
  Qed.

  Local Lemma release_spec i G γt γa lnc ℓ R κu lc :
    l{{{ thP_obls i G 1 ∗ ⌜ κu ∈ G ⌝ ∗ ([∗ set] k ∈ G, oblP_fuel k 1 ▽%M) ∗
         is_fair_lock γt γa lnc ℓ R ∗
         lock_token γt lnc κu R ∗ ⟦R⟧ₗ }}}
      TicketLock.release lnc @ i
    l{{{ RET #();
         thP_obls i (G ∖ {[κu]}) 1 ∗ £ lc}}}.
  Proof.
    iIntros (Φ) "(TG& %LUkl& Fs& #IFL& LT& HR) HΦ".
    rewrite /TicketLock.release.
    iMod (oblP_fuel_extend_set _ 0 _ 100%M with "Fs") as "Fs".
    { apply ordArith.lt_from_nat. lia. }
    iPoseProof (oblP_fuel_eq_set _ 0 _ (99 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "TG F". iExists _, ∅, 100. iSplitR; first done. iIntros "!> TG _ !> LC !> !> !>".
    rewrite lock_token_unseal /lock_token_def.
    iDestruct "LT" as "(%& %& %& %& PtrCurr0& #GMEtku& GEku)".
    subst lnc.
    iPoseProof (oblP_fuel_eq_set _ 0 _ (98 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_proj. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (97 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_let. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (96 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    lwp_lam. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !>".
    lwp_bind (Load _).
    iPoseProof (oblP_fuel_eq_set _ 0 _ (95 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TG $F $PtrCurr0]"). 1: done.
    iIntros "((_& TG& _)& PtrCurr0)".
    iPoseProof (oblP_fuel_eq_set _ 0 _ (94 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    iModIntro. lwp_op. simpl.
    iFrame "TG F". iExists _, ∅, 0. iSplitR; first done. iIntros "!> TG _ !> _ !> !> !>".
    (* Update curr and unlock κl. *)
    iDestruct "IFL" as "(%&%& %& #INV)". symmetry in H. inv H.
    (* Atomic step of Store, *)
    iMod (inv_acc with "INV") as "[H ACCinv]". 1: set_solver.
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "(%&%&%&%& PtrNext& PtrCurr& (GMAt& GMAa)& %EqDom& %Boundc& %Domt& HMt& HMa& Hc)".
    iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". inversion H. subst u. clear H.
    (* FIXME: does not combine the dfrac part. *)
    (* iCombine "PtrCurr PtrCurr0" as "PtrCurr" gives %?. destruct H as [_ ->]. *)
    iPoseProof (oblP_fuel_eq_set _ 0 _ (93 ⊕ 1)%M with "Fs") as "Fs".
    { rewrite measure_add !measure_nat -Hessenberg.add_from_nat. done. }
    iPoseProof (oblP_fuel_add_set with "Fs") as "[Fs F]".
    iApply (lwp_store _ ∅ lc with "[$TG $F PtrCurr PtrCurr0]").
    { iSplitR; first done. iSplitL "PtrCurr"; iFrame. }
    iIntros "((QLC& TG& _)& [PtrCurr PtrCurr0])".
    iPoseProof (ghost_map_lookup with "GMAt GMEtku") as "%LUt".
    iPoseProof (big_sepM_delete _ _ _ _ LUt with "HMt") as "[Hmt HMt]".
    iDestruct "Hmt" as "(Hmt1& [Hmt2 | Hmt2])".
    { iDestruct "Hmt2" as "(%& #Of)". lia. }
    iDestruct "Hmt2" as "(%Boundc1& GEku1)". iCombine "GEku GEku1" as "GEku".
    iApply sfmupd_fupd_acc.
    iMod (tf_until_fulfill_full with "GEku") as "H".
    1: apply N_subseteq_1.
    iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC1 LC]".
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iModIntro.
    iDestruct "H" as "(_& H)". iMod ("H" $! _) as "H". iApply fupd_sfmupd_elim.
    iMod ("H" with "[PtrCurr0 HR] [//] TG") as "H".
    { iNext. tf_red. rewrite tf_atomic_logic. iFrame. }
    iPoseProof (tlc_split_nat 1 97 with "LC") as "[LC1 LC]".
    iApply (lc_fupd_add_later with "LC1"). iNext.
    iModIntro. iMod ("H" $! _) as "H". iModIntro. iMod "H" as "(H& TG& #Ofk)".
    iEval (tf_red) in "H". iDestruct "H" as "(PtrCurr0& HR)".
    iModIntro. iMod ("ACCinv" with "[$PtrNext $GMAt $GMAa HMa Hc PtrCurr0 $PtrCurr Hmt1 HMt HR]") as "_".
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
    iApply ("HΦ" with "[$TG $QLC]").
  Qed.

End proof.
