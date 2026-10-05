From lantana.algebra Require Import auth_mra.
From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From iris.algebra.lib Require Import dfrac_agree.
From transfinite.base_logic.lib Require Import ghost_var ghost_map mono_Z.
From lantana.heap_lang.examples Require Import step_tactics.
From lantana.heap_lang.examples Require ticket_lock.
(* Re-activate Lantana's [£] (upstream Iris also declares ['£' n] at the same level). *)
From lantana.base_logic Require Import later_credits.

(** * The ticket lock of ticket_lock.v, whose guarantee records that [next] never decreases

    The same code and specs. The lock invariant holds half of [next]'s points-to and the other
    half is in the mono cell, an invariant registered once for every value [v] that [next]
    reaches, with the reading "[next ≥ v], or [next] freed": [delete] frees [next]
    ([lwp_free_freed]) and leaves half of its freed points-to in the cell. A lock that cannot
    be deleted has [next ↦ n] at every position, so [next] never decreases, and the lock is
    starvation free with no hypothesis about [next] ([alive_fair_lock_starvation_free]). *)

(** The code is that of ticket_lock.v. *)
Module TicketLock := ticket_lock.TicketLock.

(** The CMRA we need: that of ticket_lock.v and the lower bounds of [next]. *)
Class ticket_lock_monoG Σ :=
  TLockMonoG {
      #[local] tlock_ticketG :: ghost_mapG Σ Z (option (oid * ord.t * measure));
      #[local] tlock_oblG :: ghost_mapG Σ Z (option oid);
      #[local] tlock_tokenG :: ghost_varG Σ (Z);
      #[local] tlock_config_inG :: inG Σ (auth_mraUR (ord.le));
      (* FIXME: update ghost_var_frac in param Iris and use that. *)
      #[local] tlock_alive_inG :: inG Σ (dfrac_agreeR unit);
      #[local] tlock_monoG :: mono_ZG Σ;
    }.

Definition ticket_lock_monoΣ : gFunctors :=
  #[ghost_mapΣ Z (option (oid * ord.t * measure));
    ghost_mapΣ Z (option oid);
    ghost_varΣ (Z);
    GFunctor (auth_mraUR (ord.le));
    GFunctor (dfrac_agreeR unit);
    mono_ZΣ
    ].

Global Instance subG_ticket_lock_monoΣ {Σ} : subG ticket_lock_monoΣ Σ → ticket_lock_monoG Σ.
Proof. intros. constructor; [solve_inG..|constructor; solve_inG]. Qed.

Record ticketlock_γ :=
  TicketLockName {
      ticketlock_γt : gname;
      ticketlock_γo : gname;
      ticketlock_γk : gname;
      ticketlock_γc : gname;
      ticketlock_γa : gname;
      ticketlock_γm : gname;
    }.

Section proof.
  Context `{!heapGS Σ, !ticket_lock_monoG Σ}.

  Let N := nroot.@"ticket_lock".
  Let N_inv := N.@"inv".
  Let N_ev := N.@"ev".
  Let N_tk := N.@"token".
  Let N_mono := N.@"mono".

  Remark N_disj_1 : N_ev ## N_inv.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 (E : coPset) : (↑N ⊆ E) → ↑N_ev ⊆ E ∖ ↑N_inv.
  Proof. intros. pose proof N_disj_1. pose proof (nclose_subseteq N "ev"). set_solver. Qed.
  Remark N_inv_subseteq (E : coPset) : (↑N ⊆ E) → ↑N_inv ⊆ E.
  Proof. intros. etrans; last eapply H. apply nclose_subseteq. Qed.
  Remark N_mono_subseteq (E : coPset) : (↑N ⊆ E) → ↑N_mono ⊆ E ∖ ↑N_inv.
  Proof.
    intros. assert (N_mono ## N_inv) by by apply ndot_ne_disjoint.
    pose proof (nclose_subseteq N "mono"). set_solver.
  Qed.

  (** ** Definitions *)
  (** The trace properties these definitions guarantee are inferred below
      ([is_fair_lock_temporal]); see also section [trace]. *)

  Definition own_fair_lock_alive (γ : ticketlock_γ) (dq : dfrac) :=
    own (ticketlock_γa γ) (to_dfrac_agree dq tt).

  Notation "γ ↪LOCK_AL dq" :=
    (own_fair_lock_alive γ dq)%I
      (at level 20, dq custom dfrac at level 1, format "γ  ↪LOCK_AL dq") : bi_scope.

  Definition own_fair_lock_layer (γ : ticketlock_γ) (ℓ : ord.t) (dq : dfrac) :=
    own (ticketlock_γc γ) (auth_mra_auth ord.le dq ℓ).

  Notation "γ ↪LOCK_CF dq l" :=
    (own_fair_lock_layer γ l dq)%I
      (at level 20, dq custom dfrac at level 1, format "γ  ↪LOCK_CF dq  l") : bi_scope.

  (** *** The mono cell
      An invariant with half of [next]'s points-to (half of its freed points-to once the lock
      is deleted) and the authority over the lower bounds of [next]. It is registered again
      each time [next] reaches a value [v], with the reading [next_ge_tps next v]: the proof
      that the content guarantees this reading is given at registration, from the lower
      bound [γm ↪◯MZ v] at hand ([mono_inv_temporal]).

      A chain of always-invariants, one per value, each pointing to the next, would not do:
      at a position, the guarantee of [link v] would rest on that of [link (v+1)], available
      only one step of the logic later (its certificate is later-guarded, and the in-logic
      reading of [□ G] starts with [⊳ ⊚]). The chain grows without bound, so the reading would
      have to absorb any number of steps at one position; such a reading is valid by Löb
      induction, hence true on every trace (cf. [tps_guarded_prefix_tr]). *)
  Local Definition mono_inv γm (next : loc) : iProp Σ :=
    ∃ w : Z, γm ↪●MZ w ∗ (next ↦{#1/2} #w ∨ freed next (1/2)).

  (** [next ≥ v], or [next] has been freed. *)
  Definition next_ge_tps (next : loc) (v : Z) : tps heap_lang Σ :=
    ((∃ w : Z, ⌜(v ≤ w)%Z⌝ ∧ next ↦ #w) ∨ freed_tps next)%S.

  (** The registration of the mono cell for the value [v]. *)
  Local Definition next_ge γm (next : loc) (v : Z) : iProp Σ :=
    alwaysI_guar N_mono (mono_inv γm next) (next_ge_tps next v).

  Local Lemma mono_inv_temporal γm next v :
    γm ↪◯MZ v -∗ mono_inv γm next ⊨ₜ next_ge_tps next v.
  Proof.
    iIntros "#Lb".
    iApply (temporal_mono ((∃ w : Z, ⌜(v ≤ w)%Z⌝ ∗ next ↦{#1/2} #w) ∨ freed next (1/2))%I with "[]").
    { iIntros "!> (%w& A& [P|F])"; last by iRight.
      iDestruct (mono_Z_auth_lb_own_valid with "A Lb") as %[_ ?]. iLeft. iExists w. by iFrame. }
    iApply temporal_or; last iApply freed_temporal.
    iApply temporal_exist. iIntros (w). iApply temporal_sep; first iApply temporal_pure.
    iApply (temporal_weaken _ (tps_atomic (pred_pointsto next (DfracOwn (1/2)) #w))).
    { intros ? τ. done. }
    iApply (temporal_atomic (pred_pointsto next (DfracOwn (1/2)) #w)).
  Qed.

  (** Allocation of the cell, with its first registration. *)
  Local Lemma next_ge_alloc E γm next v :
    γm ↪◯MZ v -∗ ▷ mono_inv γm next -∗ |={E}=>m next_ge γm next v.
  Proof.
    iIntros "#Lb HI". iApply (alwaysI_alloc_guar with "[] HI").
    iNext. by iApply mono_inv_temporal.
  Qed.

  (** A new registration, with a new lower bound (the invariant is that of an earlier one). *)
  Local Lemma next_ge_register E γm next v v' :
    ↑N_mono ⊆ E →
    next_ge γm next v' -∗ γm ↪◯MZ v -∗ |={E}=>m next_ge γm next v.
  Proof.
    iIntros (HN) "#NG #Lb". iApply (alwaysI_register_guar with "[] []"); first done.
    - by iApply alwaysI_guar_inv.
    - iNext. by iApply mono_inv_temporal.
  Qed.

  Local Definition lock_token_inv γo γk (curr : loc) (R : iProp Σ) : iProp Σ :=
    ∃ (c : Z),
      (ghost_var_frac γk 1 (c)) ∨
        (∃ κ, ghost_var_frac γk (1/2) (c) ∗
              (curr ↦{#(1/2 + 1/2/2)} #c) ∗
              ((c + 1)%Z ↪[γo]□ (Some κ)) ∗
              finallyI N_ev κ (1/2) (curr ↦{#(1/2 + 1/2/2)} #(c + 1)%Z ∗ R)).

  (** The alive branch of the lock invariant, as a notation (so that proofs about the
      invariant's content are unchanged). *)
  Local Notation lock_inv_alive γt γo γc γm next curr R :=
    ((∃ (n c : Z)
         (tickets : gmap Z (option (oid * ord.t * measure)))
         (obls : gmap Z (option oid)),
          next ↦{#1/2} #n ∗ next_ge γm next n ∗
          curr ↦{#(1/2/2)} #c ∗
          ghost_map_auth_frac γt 1 tickets ∗
          ghost_map_auth_frac γo 1 obls ∗
          (⌜(dom tickets = dom obls)%Z⌝) ∗
          (⌜(0 ≤ c ≤ n)%Z⌝) ∗
          (⌜ ∀ t, t ∈ dom tickets ↔ (0 ≤ t ≤ n)%Z ⌝) ∗
          (** Finished or waiting threads *)
          (* We need auth_mra_know to sync what other threads know about the configuration *)
          ([∗ set] t ∈ dom tickets,
             ((∃ κ, ⌜(0 ≤ t ≤ c)%Z⌝ ∧
                    t ↪[γt]□ (None : option (oid * ord.t * measure)) ∗
                    t ↪[γo]□ (Some κ) ∗
                    oblP_discharged κ) ∨
                (⌜ (t = c + 1)%Z ⌝) ∨
                (∃ g ℓ μ, ⌜((c + 1)%Z < t ≤ n)%Z⌝ ∧
                            t ↪[γt]{#1/2} (Some (g, ℓ, μ)) ∗
                            t ↪[γo] (None : option oid) ∗
                            (own γc (◯AM[ord.le] ℓ)) ∗ oblP_kids g ∅ ∗ witP_layer g ℓ))) ∗
          ((⌜(c = n)⌝ ∧ curr ↦{#(1/2 + 1/2/2)} #c%Z ∗ R) ∨
             (⌜(c < n)%Z⌝ ∧
              (* Allocates new obligation on behalf of next owner. *)
              ∃ ℓ κ, (own γc (◯AM[ord.le] ℓ)) ∗ witP_layer κ ℓ ∗ (c + 1)%Z ↪[γo]□ (Some κ) ∗
                     finallyI N_ev κ (1/2) (curr ↦{#(1/2 + 1/2/2)} #(c + 1)%Z ∗ R) ∗
                     ((∃ g μ, (c + 1)%Z ↪[γt]{#1/2} (Some (g, ℓ, μ)) ∗
                                finallyI N_ev κ (1/2) (curr ↦{#(1/2 + 1/2/2)} #(c + 1)%Z ∗ R) ∗
                                oblP_kids g {[κ]} ∗ oblP_kids κ ∅ ∗ oblP_fuel κ ℓ μ ∗
                                curr ↦{#(1/2 + 1/2/2)} #c%Z ∗ R) ∨
                        (* Current owner acquired the lock. *)
                        ((c + 1)%Z ↪[γt]□ (None : option (oid * ord.t * measure))))))))%I.

  Local Definition lock_inv γt γo γc γa γm (next curr : loc) (R : iProp Σ) : iProp Σ :=
    (own γa (to_dfrac_agree (DfracOwn 1) tt)) ∨ lock_inv_alive γt γo γc γm next curr R.

  Definition is_fair_lock (tl : val) (γ : ticketlock_γ) (R : iProp Σ) : iProp Σ :=
    ∃ (next curr : loc),
      (⌜tl = (#next, #curr)%V⌝) ∧
      alwaysI N_inv (lock_inv (ticketlock_γt γ) (ticketlock_γo γ) (ticketlock_γc γ) (ticketlock_γa γ) (ticketlock_γm γ) next curr R) ∗
      alwaysI N_tk (lock_token_inv (ticketlock_γo γ) (ticketlock_γk γ) curr R).

  (** A lock that cannot be deleted (its holder keeps [γ ↪LOCK_AL□]): the lock invariant is
      registered under its alive branch, so that the trace sees it. *)
  Definition is_fair_lock_alive (tl : val) (γ : ticketlock_γ) (R : iProp Σ) : iProp Σ :=
    is_fair_lock tl γ R ∗
    ∃ (next curr : loc),
      (⌜tl = (#next, #curr)%V⌝) ∧
      alwaysI_as N_inv (lock_inv (ticketlock_γt γ) (ticketlock_γo γ) (ticketlock_γc γ) (ticketlock_γa γ) (ticketlock_γm γ) next curr R)
        (lock_inv_alive (ticketlock_γt γ) (ticketlock_γo γ) (ticketlock_γc γ) (ticketlock_γm γ) next curr R).

  (** The alive lock is the lock. (Use this rather than framing the one against the other:
      unifying the two definitions' bodies does not terminate in reasonable time.) *)
  Lemma is_fair_lock_alive_is_fair_lock tl γ R : is_fair_lock_alive tl γ R ⊢ is_fair_lock tl γ R.
  Proof. iIntros "[$ _]". Qed.

  Local Definition lock_token_def (γ : ticketlock_γ) κu : iProp Σ :=
    ∃ (c : Z), ghost_var_frac (ticketlock_γk γ) (1/2) (c) ∗
               ((c + 1)%Z ↪[(ticketlock_γt γ)]□ (None : option (oid * ord.t * measure))) ∗
               ((c + 1)%Z ↪[(ticketlock_γo γ)]□ (Some κu)).
  Local Definition lock_token_aux : seal (@lock_token_def). Proof. by eexists. Qed.
  Definition lock_token := lock_token_aux.(unseal).
  Local Definition lock_token_unseal :
    @lock_token = @lock_token_def := lock_token_aux.(seal_eq).

  (** ** Properties *)
  Global Instance is_fair_lock_persistent tl γ R : Persistent (is_fair_lock tl γ R).
  Proof. rewrite /is_fair_lock. apply _. Qed.

  Lemma lock_alive_persist γ dq :
    (γ ↪LOCK_AL{dq}) ==∗ γ ↪LOCK_AL□.
  Proof. iIntros "H". iApply (own_update with "H"). apply dfrac_agree_persist. Qed.

  Lemma lock_reconfig γ ℓ1 ℓ2 :
    (ℓ1 <= ℓ2)%ordi →
    γ ↪LOCK_CF ℓ1 ==∗ γ ↪LOCK_CF ℓ2.
  Proof.
    iIntros (LE). iIntros "H". iApply (own_update with "H").
    (* FIXME: [apply] leaves the class argument of [auth_mra_update] as a goal. *)
    apply auth_mra_update; auto. apply _.
  Qed.

  Lemma lock_config_persist γ dq ℓ :
    (γ ↪LOCK_CF{dq} ℓ) ==∗ γ ↪LOCK_CF□ ℓ.
  Proof. iIntros "H". iApply (own_update with "H"). apply auth_mra_auth_persist. Qed.

  Lemma lock_config_valid γ dq1 dq2 ℓ1 ℓ2 :
    γ ↪LOCK_CF{dq1} ℓ1 -∗ γ ↪LOCK_CF{dq2} ℓ2 -∗ ⌜(✓ (dq1 ⋅ dq2)) ∧ (ℓ1 == ℓ2)%ordi⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %HCF.
    unshelve eapply auth_mra_auth_dfrac_op_valid in HCF.
    (* FIXME: the class arguments are not inferred; they are given by hand. *)
    1: exact ord.eq. 2,3,4,5: apply ordinal_auth_mra_class.
    eauto.
  Qed.

  (** ** The shape of the specs
      A modular spec with liveness should hide implementation details (number of steps,
      internal data), be robust against implementation changes (in particular, of the fuel),
      and have the same format across libraries. [oblP_fuel g 1 1] suits trivially terminating
      functions, [ord.large] more complex ones (cf. Hartogs numbers). A function that
      terminates without witness induction has layer 0 and an [∃ μ] in front of its spec, as
      [TicketLock_init_spec]. *)

  (** ** Program proofs *)
  (** TODO: LAT-style specs, for a better interaction with user invariants. *)
  Lemma TicketLock_init_spec :
    ⊢ ∃ μ, ∀ lc ℓ i G (E : coPset) C,
    l{{{ thread_expr i C (TicketLock.init #()) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) }}}
      TicketLock.init #() @ i; E
    l{{{ tl γ, RET tl; thread_expr i C (of_val tl) ∗ £ lc ∗
                       thP_kids i G ∗ γ ↪LOCK_AL ∗ γ ↪LOCK_CF ℓ ∗
                       (∀ E R, R -∗ |={E}=>m is_fair_lock tl γ R) }}}.
  Proof.
    iExists 10.
    iIntros (lc ℓ i G E C) "!> %Φ (TE& TG& GF) HΦ".
    rewrite /TicketLock.init.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_one.
    lwp_bind (AllocN _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (curr) "[TE ((_& TG& _)& Ptr_curr& _)]".
    lwp_bind (AllocN _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_alloc _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iModIntro. iIntros (next) "[TE ((_& TG& _)& Ptr_next& _)]".
    iModIntro. lwp_pure_lc lc. iRename "LC" into "QLC".
    iMod (obl_alloc_discharged _ (ℓ)%ordi) as "(%κu& #Ofk& #Wlk& OAcc)".
    iDestruct "Ptr_curr" as "[[Ptr_curr Ptr_curr1] Ptr_curr0]".
    iCombine "Ptr_curr0 Ptr_curr1" as "Ptr_curr0".
    iMod (ghost_map_alloc ({[0%Z := None]} : gmap Z (option (oid * ord.t * measure)))) as "(%γt& GMAt& GMEt)".
    iMod (ghost_map_alloc ({[0%Z := (Some κu)]} : gmap Z (option oid))) as "(%γo& GMAo& GMEo)".
    rewrite !big_sepM_singleton.
    iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
    iMod (ghost_map_elem_persist with "GMEo") as "#GMEo".
    iMod (own_alloc (to_dfrac_agree (DfracOwn 1) tt)) as "(%γa& AL)".
    { done. }
    iMod (own_alloc (●AM[ord.le] ℓ)) as "(%γc& CF)".
    { apply auth_mra_auth_valid. }
    iAssert (own (γc) (◯AM[ord.le] ℓ))%I as "#CFl".
    { iAssert (own γc (●AM[ord.le] ℓ) ∗ own (γc) (◯AM[ord.le] ℓ))%I with "[CF]" as "[_ $]".
      rewrite -own_op -auth_mra_auth_know_op. done. }
    iMod (ghost_var_alloc (0 : Z)) as "(%γk& GV)".
    iMod (mono_Z_own_alloc 0) as "(%γm& Auth& #Lb)"; first done.
    iDestruct "Ptr_next" as "[Ptr_next Ptr_next0]".
    iModIntro. lwp_finish.
    iModIntro.
    iApply ("HΦ" $! _ (TicketLockName γt γo γk γc γa γm)). iFrame "TE TG QLC AL CF".
    iIntros (??) "HR".
    (* The mono cell, registered for [0]. *)
    iMod (next_ge_alloc _ γm next 0 with "Lb [Ptr_next0 Auth]") as "#NG".
    { iNext. iExists 0. iFrame. }
    iMod (alwaysI_alloc _ N_inv (lock_inv γt γo γc γa γm next curr R) with "[Ptr_next Ptr_curr Ptr_curr0 GMAt GMAo HR]") as "#Ak".
    { iNext. rewrite /lock_inv. iRight. iExists 0, 0, {[0%Z := (None)]}, {[0%Z := (Some κu)]}.
      iFrame "Ptr_next NG Ptr_curr GMAt GMAo". iSplit. 1: done. iSplit. 1: done. iSplit.
      { iPureIntro. intros. rewrite dom_singleton_L elem_of_singleton. split; intros.
        - subst. lia.
        - lia. }
      iSplitR.
      { rewrite dom_singleton_L big_sepS_singleton. iLeft. eauto. }
      iLeft. iFrame. iPureIntro. lia. }
    iMod (alwaysI_alloc _ N_tk (lock_token_inv γo γk curr R) with "[$GV]") as "#IK".
    iModIntro. rewrite /is_fair_lock. iExists next, curr. iSplitR; first done. iFrame "#".
  Qed.

  (** FIXME: ordi notation levels *)
  Lemma TicketLock_acquire_spec :
    ⊢ ∃ μ, ∀ lc m i G tl γ dq1 dq2 ℓ R (E : coPset) (MASK : ↑N ⊆ E) C,
    l{{{ thread_expr i C (TicketLock.acquire (tl : val)) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g (ℓ ⊕ 1)%ordi μ) ∗
         γ ↪LOCK_AL{dq1} ∗
         γ ↪LOCK_CF{dq2} ℓ ∗
         is_fair_lock tl γ R }}}
      TicketLock.acquire tl @ i; E
    l{{{ κu, RET #(); thread_expr i C (#()) ∗
         £ lc ∗
         (⌜ κu ∉ G ⌝) ∗
         thP_kids i ({[κu]} ∪ G) ∗
         oblP_kids κu ∅ ∗
         oblP_fuel κu ℓ m ∗
         γ ↪LOCK_AL{dq1} ∗ γ ↪LOCK_CF{dq2} ℓ ∗ lock_token γ κu ∗ R }}}.
  Proof.
    iExists (100 ⊕ (((50 ⊕ (50 × ▽)) × ℵ) ⊕ (50 × ▽)))%M.
    iIntros (lc m i G tl γ dq1 dq2 ℓ R E MASK C) "!> % (TE& TG& Fs& AL& CF& #IFL) HΦ".
    iPoseProof (oblP_fuel_add_set with "Fs") as "[GF Fsloop]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    rewrite /TicketLock.acquire.
    (* argument *)
    lwp_pure_lc 100.
    (* get fst and snd of the argument *)
    iDestruct "IFL" as "(%&%& %& #INV& #ITK)". subst tl.
    (* fst *)
    lwp_pures.
    (* FAA *)
    lwp_bind (FAA _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    (* Atomic step of FAA, *)
    iModIntro. iMod (alwaysI_acc with "INV") as "[H ACCinv]".
    { apply N_inv_subseteq. auto. }
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "[H | H]".
    { iCombine "AL H" gives %HAL. rewrite dfrac_agree_op_valid in HAL. destruct HAL.
      apply dfrac_valid_own_r in H. done. }
    iDestruct "H" as "(%&%&%&%& PtrNext& #NG& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    (* The mono cell, open for the step, holds the other half of [next]. *)
    iMod (alwaysI_guar_acc with "NG") as "[HJ CloseJ]".
    { apply N_mono_subseteq. auto. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "HJ" as "(%w& Auth& [PtrNext0 | Fr])"; last first.
    { iDestruct (freed_pointsto_false with "Fr PtrNext") as %[]. }
    iDestruct (pointsto_agree with "PtrNext PtrNext0") as %[= <-].
    iApply (lwp_faa _ ∅ 0 with "[$TE $TG $GF1 PtrNext PtrNext0]").
    { iSplitR; first done. iCombine "PtrNext PtrNext0" as "$". }
    iIntros "[TE ((_& TG& _)& [PtrNext PtrNext0])]".
    (* [next] has increased: close the cell and register it for [n + 1]. *)
    iMod (mono_Z_own_update (n + 1) with "Auth") as "[Auth #Lb]"; first lia.
    iMod ("CloseJ" with "[Auth PtrNext0]") as "_".
    { iNext. iExists (n + 1)%Z. iFrame. }
    iModIntro.
    iMod (next_ge_register _ _ _ (n + 1) with "NG Lb") as "#NG1".
    { apply N_mono_subseteq. auto. }
    iClear "NG Lb".
    (** A new container, at the lock's layer, to receive the unlock obligation *)
    iMod (obl_new _ (PThread i) G ℓ (50 ⊕ m)%M with "[] TG") as "(%gu& %Ningu& TG& Gg& Agu& Gf& #Wgu)".
    { iApply parP_le_thread. }
    iPoseProof (oblP_fuel_add with "Gf") as "[Gf Q_Gf]".
    (* Update maps. *)
    iMod (ghost_map_insert (n + 1)%Z (Some (gu, ℓ, m)) with "GMAt") as "[GMAt GMEt]".
    { apply not_elem_of_dom. intros IN. apply Domt in IN. lia. }
    iMod (ghost_map_insert (n + 1)%Z (None) with "GMAo") as "[GMAo GMEo]".
    { apply not_elem_of_dom. intros IN. rewrite -EqDom in IN. apply Domt in IN. lia. }
    iAssert (own (ticketlock_γc γ) (◯AM[ord.le] ℓ))%I as "#CFl".
    { iAssert (γ ↪LOCK_CF{dq2} ℓ ∗ own (ticketlock_γc γ) (◯AM[ord.le] ℓ))%I with "[CF]" as "[_ $]".
      rewrite -own_op -auth_mra_auth_know_op. done. }
    (** Close inv; two cases: my turn, or not. *)
    iDestruct "Hc" as "[Hc | Hc]".
    { (* My turn *)
      iDestruct "Hc" as "(%& PtrCurr0& HR)". subst c.
      (* Unlock obligation *)
      iMod (untilI_alloc _ _ _ ℓ m with "[] Gg")
        as "(%κu& %LUku& Gg& Kk& OGF& #Wlku& ALLOC)".
      { iApply (parP_le_obl with "Wgu"). reflexivity. }
      iMod ("ALLOC" $! _ N_ev True%I (curr ↦{#1/2 + 1/2/2} #(n + 1) ∗ R)%I with "[//]") as "[GUku GUku0]".
      rewrite union_empty_r_L.
      iMod (ghost_map_update (None) with "GMAt GMEt") as "[GMAt GMEt]".
      iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
      iMod (ghost_map_update (Some κu) with "GMAo GMEo") as "[GMAo GMEo]".
      iMod (ghost_map_elem_persist with "GMEo") as "#GMEo".
      rewrite !insert_insert_eq.
      iModIntro.
      iMod ("ACCinv" with "[PtrNext PtrCurr GMAt GMAo HMt GUku]") as "_".
      { iNext. iRight. iFrame "PtrNext NG1 PtrCurr GMAt GMAo". iSplit.
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
            iDestruct "H" as "(%&%&%& %& _)". lia. }
        iRight. iSplit.
        { iPureIntro. lia. }
        iFrame "CFl Wlku GMEo GUku". iRight. eauto. }
      iIntros "!> !>". iClear "NG1".
      rename n into my. assert (Hmy : (0 ≤ my)%Z) by lia.
      clear dependent tickets obls. clear Boundc LUku.
      iClear "Fsloop".
      (* Update fuels. *)
      iPoseProof (oblP_fuels_add_nat 50 with "GF") as "[GF _]". 1: done.
      iPoseProof (oblP_fuels_add_obl with "Gf GF") as "GF".
      lwp_pure_one.
      do 2 (iModIntro; lwp_pure_one).
      (** The while loop. *)
      (* Execute loop body. *)
      lwp_pures.
      lwp_bind (Load _).
      (* Atomic step of Load, *)
      iModIntro.
      iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]". 1: eauto.
      iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $PtrCurr0]"). 1: done.
      iIntros "[TE ((_& TG& _)& PtrCurr0)]".
      iRename "LC" into "LC1".
      iModIntro. lwp_pure_lc lc.
      rewrite bool_decide_eq_true_2; last done.
      lwp_pures.
      iModIntro. lwp_finish.
      (* The unlock obligation moves up to the thread; the container is discharged. *)
      iMod (obl_move_up _ (PThread i) ({[gu]} ∪ G) gu {[κu]} κu with "TG Gg") as "(%Hku& TG& Gg)".
      { set_solver. }
      { set_solver. }
      replace ({[κu]} ∖ {[κu]}) with (∅ : gset oid) by set_solver.
      iMod (obl_discharge_leaf with "TG Gg Agu") as "[TG _]"; first set_solver.
      replace (({[κu]} ∪ ({[gu]} ∪ G)) ∖ {[gu]}) with ({[κu]} ∪ G) by set_solver.
      iApply sfmupd_fupd_acc.
      iInv "ITK" as "H".
      iPoseProof (tlc_split_nat 1 with "LC1") as "[LC1 _]". 1: eauto.
      iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
      iDestruct "H" as "(%& [GV | (%& GV& PtrCurr1& GMEo1& HE1)])"; cycle 1.
      { iCombine "PtrCurr0 PtrCurr1" gives %HPC. destruct HPC. done. }
      iMod (ghost_var_update (my) with "GV") as "[GV0 GV]".
      iModIntro. iSplitL "GV GUku0 PtrCurr0".
      { iNext. iExists _. iRight. iFrame. eauto. }
      iApply ("HΦ" with "[$TE $TG $Kk $OGF $HR $LC $AL $CF GV0]"). iSplit. 1: set_solver.
      rewrite lock_token_unseal /lock_token_def. iFrame "GV0". eauto. }
    (* Not my turn. *)
    iDestruct "GMEt" as "[GMEt0 GMEt]".
    iModIntro.
    iMod ("ACCinv" with "[PtrNext PtrCurr GMAt GMAo HMt Hc Gg GMEt GMEo]") as "_".
    { iDestruct "Hc" as "(%LTc& Hc)". iNext. iRight. iFrame "PtrNext NG1 PtrCurr GMAt GMAo". iSplit.
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
        - iApply big_sepS_singleton. iRight. iRight. iFrame "Gg GMEt GMEo CFl Wgu". iPureIntro. lia.
        - iApply (big_sepS_impl with "HMt"). iIntros "!> %% H".
          iDestruct "H" as "[$ | [$ | H]]".
          do 2 iRight. iDestruct "H" as "(%&%&%& %& $& $& $)". iPureIntro. lia. }
      iRight. iSplit.
      { iPureIntro. lia. }
      iFrame. }
    iIntros "!> !>". iClear "NG1".
    rename n into my. assert (Hmy : (0 ≤ my)%Z) by lia.
    clear dependent c tickets obls.
    (* Update fuels. *)
    iPoseProof (oblP_fuels_add_nat 50 with "GF") as "[GF _]". 1: done.
    iPoseProof (oblP_fuels_add_obl with "Gf GF") as "GF".
    lwp_pure_one.
    do 2 (iModIntro; lwp_pure_one).
    (** My turn or need induction. *)
    iModIntro.
    iApply fupd_lwp. iInv "INV" as "H".
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "[H | H]".
    { iCombine "AL H" gives %HAL. rewrite dfrac_agree_op_valid in HAL. destruct HAL.
      apply dfrac_valid_own_r in H. done. }
    iDestruct "H" as "(%&%&%&%& PtrNext& #NG& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    iPoseProof (ghost_map_lookup with "GMAt GMEt0") as "%LUt".
    iDestruct "Hc" as "[Hc | Hc]".
    { iExFalso. iDestruct "Hc" as "(%& _)". subst c.
      pose proof LUt as INt. apply elem_of_dom_2 in INt. apply Domt in INt.
      assert (Elemt : (my + 1)%Z ∈ dom tickets) by (apply elem_of_dom; eauto).
      iPoseProof (big_sepS_delete _ _ _ Elemt with "HMt") as "[Ht _]".
      iDestruct "Ht" as "[Ht | Ht]".
      - iDestruct "Ht" as "(%&%& #GMEt1& _)". iCombine "GMEt0 GMEt1" gives %?. by destruct H0.
      - iDestruct "Ht" as "[% | (%&%&%&%& _)]". 1: lia. 1: lia. }
    (** Two cases: my turn, or not. *)
    iDestruct "Hc" as "(%LTc& Hc)".
    destruct (decide (my = c)).
    { (* My turn. *)
      subst c. iDestruct "Hc" as "(%&%κu& _& #Wl& #GMEo& HE0& Hc)".
      iDestruct "Hc" as "[Hc | #GMEt1]"; cycle 1.
      { iCombine "GMEt0 GMEt1" gives %?. by destruct H. }
      iDestruct "Hc" as "(%&%& GMEt& HE& Gg& Kk& Of& PtrCurr0& HR)".
      iCombine "GMEt GMEt0" as "GMEt" gives %?. destruct H as [_ H]. simplify_eq.
      replace (DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2)) with (DfracOwn 1); cycle 1.
      { rewrite dfrac_op_own Qp.div_2. done. }
      iMod (ghost_map_update (None) with "GMAt GMEt") as "[GMAt GMEt]".
      iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
      iModIntro.
      iSplitL "PtrNext PtrCurr GMAt GMAo HMt HE".
      { iNext. iRight. iFrame "PtrNext NG PtrCurr GMAt GMAo". iSplit.
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
      iClear "NG". clear dependent tickets n obls.
      iClear "Fsloop".
      (* Update fuels. *)
      lwp_pure_one.
      (* Execute loop body. *)
      lwp_pures.
      lwp_bind (Load _).
      (* Atomic step of Load, *)
      iModIntro.
      iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]". 1: eauto.
      iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $PtrCurr0]"). 1: done.
      iIntros "[TE ((_& TG& _)& PtrCurr0)]".
      iRename "LC" into "LC1".
      iModIntro. lwp_pure_lc lc.
      rewrite bool_decide_eq_true_2; last done.
      lwp_pures.
      iModIntro. lwp_finish.
      (* The unlock obligation moves up to the thread; the container is discharged. *)
      iMod (obl_move_up _ (PThread i) ({[gu]} ∪ G) gu {[κu]} κu with "TG Gg") as "(%Hku& TG& Gg)".
      { set_solver. }
      { set_solver. }
      replace ({[κu]} ∖ {[κu]}) with (∅ : gset oid) by set_solver.
      iMod (obl_discharge_leaf with "TG Gg Agu") as "[TG _]"; first set_solver.
      replace (({[κu]} ∪ ({[gu]} ∪ G)) ∖ {[gu]}) with ({[κu]} ∪ G) by set_solver.
      iApply sfmupd_fupd_acc.
      iInv "ITK" as "H".
      iPoseProof (tlc_split_nat 1 with "LC1") as "[LC1 _]". 1: eauto.
      iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
      iDestruct "H" as "(%& [GV | (%& GV& PtrCurr1& GMEo1& HE1)])"; cycle 1.
      { iCombine "PtrCurr0 PtrCurr1" gives %HPC. destruct HPC. done. }
      iMod (ghost_var_update (my) with "GV") as "[GV GV0]".
      iModIntro. iSplitL "GV0 HE0 PtrCurr0".
      { iNext. iExists _. iRight. iFrame. eauto. }
      iApply ("HΦ" with "[$TE $TG $Kk $Of $HR $LC $AL $CF GV]"). iSplit. 1: set_solver.
      rewrite lock_token_unseal /lock_token_def. iFrame. eauto. }
    (* Not my turn, induction. *)
    iDestruct "Hc" as "(%ℓ0&%& #CFl0& #Wl0& #GMEo0& Hc)".
    assert (Hc : (0 ≤ c)%Z) by lia.
    assert (Elemt : (my + 1)%Z ∈ dom tickets) by (apply elem_of_dom; eauto).
    iAssert (⌜(c < my)%Z⌝)%I as "%LTmy".
    { iPoseProof (big_sepS_delete _ _ _ Elemt with "HMt") as "[H _]".
      iDestruct "H" as "[H | [% | H]]".
      - iDestruct "H" as "(%& %& GMEt1& _)". iCombine "GMEt0 GMEt1" gives %?. by destruct H0.
      - lia.
      - iDestruct "H" as "(%&%&%& %& _)". iPureIntro. lia. }
    iModIntro.
    iSplitL "PtrNext PtrCurr GMAt GMAo HMt Hc".
    { iNext. iRight. iFrame "PtrNext NG PtrCurr GMAt GMAo". iSplit.
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
    iClear "NG". clear dependent tickets n obls. clear Hmy n0. rename c into prev.
    iAssert (⌜(ℓ0 <= ℓ)%ordi⌝)%I as "%Hcf".
    { iCombine "CF CFl0" gives %?. apply auth_mra_both_dfrac_valid in H. 2: apply _. by destruct H. }
    iPoseProof (oblP_fuel_add_set with "Fsloop") as "[Fsloop1 Fsloop]".
    (** Nest 1: Embed induction. *)
    remember (Z.to_nat (my - prev)%Z) as ν.
    iPoseProof (embed_fuels_init (lt_wf) ν) as "EFs0".
    iMod (embed_fuels_add_map with "EFs0 Fsloop1") as "EFs". rewrite map_union_empty.
    iClear "EFs0". iRevert (κ ℓ0 Hcf gu Ningu prev Hc LTmy Heqν) "CFl0 Wl0 Wgu Q_Gf Agu GMEt0 TG GF GMEo0 EFs TE".
    iInduction ν as [ν IHν] using (well_founded_induction lt_wf).
    iIntros (κ ℓ0 Hcf gu Ningu prev Hc LTmy Heqν) "#CFl0 #Wl0 #Wgu Q_Gf Agu GMEt0 TG GF #GMEo0 EFs TE".
    (** Nest 2: Witness induction. *)
    iPoseProof (wit_fuels_init with "Wl0") as "(%& WFs0)".
    iMod (wit_fuels_add_map with "WFs0 Fsloop") as "WFs".
    { eapply ord.le_lt_lt. 1: eauto. apply hessenberg.add_lt_l.
      rewrite -ord.from_nat_O. apply ordArith.lt_from_nat. lia. }
    rewrite map_union_empty.
    iClear "WFs0". iRevert (gu Ningu) "Wgu Q_Gf Agu GMEt0 TG GF WFs TE".
    iInduction α as [α IHα] using (well_founded_induction Ord.lt_well_founded).
    iIntros (gu Ningu) "#Wgu Q_Gf Agu GMEt0 TG GF WFs TE".
    (* Execute loop body. *)
    lwp_pure_one.
    lwp_bind (Load _).
    (* Atomic step of Load, *)
    iModIntro. iMod (alwaysI_acc with "INV") as "[H ACCinv]".
    { apply N_inv_subseteq. auto. }
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "[H | H]".
    { iCombine "AL H" gives %HAL. rewrite dfrac_agree_op_valid in HAL. destruct HAL.
      apply dfrac_valid_own_r in H. done. }
    iDestruct "H" as "(%&%&%&%& PtrNext& #NG& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_load _ {[κ]} 97%ord with "[$TE $TG $GF1 $PtrCurr]").
    { rewrite big_sepS_singleton. eauto. }
    iIntros "[TE ((LC'& TG& Wc)& PtrCurr)]". iEval (rewrite big_sepS_singleton) in "Wc".
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
      iDestruct "Hc" as "(%&%& GMEt1& HE& Gg& Kk& Ofk& PtrCurr0& HR)".
      iCombine "GMEt1 GMEt0" as "GMEt" gives %?. destruct H as [_ H]. simplify_eq.
      replace (DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2)) with (DfracOwn 1); cycle 1.
      { rewrite dfrac_op_own Qp.div_2. done. }
      iMod (ghost_map_update (None) with "GMAt GMEt") as "[GMAt GMEt]".
      iMod (ghost_map_elem_persist with "GMEt") as "#GMEt".
      iModIntro.
      iMod ("ACCinv" with "[PtrNext PtrCurr GMAt GMAo HMt HE]") as "_".
      { iNext. iRight. iFrame "PtrNext NG PtrCurr GMAt GMAo". iSplit.
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
      iClear "NG". clear dependent tickets n obls.
      iRename "LC" into "LC1".
      iModIntro. lwp_pure_lc lc.
      rewrite bool_decide_eq_true_2; last done.
      lwp_pures.
      iModIntro. lwp_finish.
      (* The unlock obligation moves up to the thread; the container is discharged. *)
      iMod (obl_move_up _ (PThread i) ({[gu]} ∪ G) gu {[κu]} κu with "TG Gg") as "(%Hku& TG& Gg)".
      { set_solver. }
      { set_solver. }
      replace ({[κu]} ∖ {[κu]}) with (∅ : gset oid) by set_solver.
      iMod (obl_discharge_leaf with "TG Gg Agu") as "[TG _]"; first set_solver.
      replace (({[κu]} ∪ ({[gu]} ∪ G)) ∖ {[gu]}) with ({[κu]} ∪ G) by set_solver.
      iApply sfmupd_fupd_acc.
      iInv "ITK" as "H".
      iPoseProof (tlc_split_nat 1 with "LC1") as "[LC1 _]". 1: eauto.
      iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
      iDestruct "H" as "(%& [GV | (%& GV& PtrCurr1& GMEo1& HE1)])"; cycle 1.
      { iCombine "PtrCurr0 PtrCurr1" gives %HPC. destruct HPC. done. }
      iMod (ghost_var_update (my) with "GV") as "[GV GV0]".
      iModIntro. iSplitL "GV0 HE0 PtrCurr0".
      { iNext. iExists _. iRight. iFrame. eauto. }
      iApply ("HΦ" with "[$TE $TG $Kk $Ofk $HR $LC $AL $CF GV]"). iSplit. 1: set_solver.
      rewrite lock_token_unseal /lock_token_def. iFrame. eauto. }
    { (* Inductive cases: prev still holding, or new owner. *)
      (* Must refresh my container. *)
      iPoseProof (ghost_map_lookup with "GMAt GMEt0") as "%LUt".
      assert (Boundmy : (my + 1 ≤ n)%Z).
      { apply elem_of_dom_2 in LUt. apply Domt in LUt. lia. }
      assert (Elemt : (my + 1)%Z ∈ dom tickets) by (apply elem_of_dom; eauto).
      iPoseProof (big_sepS_delete _ _ _ Elemt with "HMt") as "[H HMt]".
      iDestruct "H" as "[H | [% | H]]".
      { iDestruct "H" as "(%&%& GMEt1& _)". iCombine "GMEt0 GMEt1" gives %?. by destruct H0. }
      { lia. }
      iDestruct "H" as "(%&%&%& %& GMEt1& GMEo& _& Gg& _)".
      iCombine "GMEt1 GMEt0" as "GMEt" gives %?. destruct H0 as [_ H0]. simplify_eq.
      iMod (obl_discharge_leaf with "TG Gg Agu") as "[TG _]". 1: set_solver.
      iPoseProof (oblP_fuels_remove_obl gu with "GF") as "GF".
      replace (({[gu]} ∪ G) ∖ {[gu]}) with G by set_solver.
      rename gu into gu_prev, LUt into LUt_prev. iClear "Q_Gf Wgu". clear Ningu.
      iMod (obl_new _ (PThread i) G ℓ (45 ⊕ 47 ⊕ m)%M with "[] TG") as "(%gu& %Ningu& TG& Gg& Agu& Gf& #Wgu)".
      { iApply parP_le_thread. }
      iPoseProof (oblP_fuel_add with "Gf") as "[Gf Q_Gf]".
      iPoseProof (oblP_fuel_add with "Q_Gf") as "[Loop_Gf Q_Gf]".
      (* Update tickets map. *)
      replace (DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2)) with (DfracOwn 1); cycle 1.
      { rewrite dfrac_op_own Qp.div_2. done. }
      iMod (ghost_map_update (Some (gu, ℓ, m)) with "GMAt GMEt") as "[GMAt [GMEt GMEt0]]".
      iPoseProof (oblP_fuels_add_obl with "Gf GF") as "GF".
      iDestruct "Wc" as "[Wc | #Gdk]".
      - iModIntro. iMod ("ACCinv" with "[PtrNext GMAt GMAo HMt PtrCurr Hc Gg GMEt GMEo]") as "_".
        { iNext. iRight. iFrame "PtrNext NG GMAt GMAo PtrCurr Hc". iSplit.
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
          iApply big_sepS_singleton. do 2 iRight. iFrame "Wgu". iFrame. eauto. }
        iModIntro.
        iModIntro. lwp_pure_one.
        rewrite bool_decide_eq_false_2; cycle 1.
        { intro. inv H. }
        iModIntro. lwp_pure_one.
        iMod (wit_fuels_decr with "WFs Wc") as "(%& %LTα& WFs& Fs')".
        iClear "GF LC".
        iAssert (oblP_fuels ({[gu]} ∪ G) 47)%I with "[Loop_Gf Fs']" as "Fs".
        { iApply big_sepS_union. 1: set_solver. iSplitL "Loop_Gf".
          - iApply oblP_fuels_init. iApply big_sepS_singleton. iFrame.
          - iPoseProof (big_sepM_gset_to_gmap with "Fs'") as "H".
            iPoseProof (oblP_fuel_eq_set _ _ _ (47 ⊕ 3)%M with "H") as "H".
            { rewrite measure_rep_add !measure_rep_nat -Hessenberg.add_from_nat.
              replace 50 with (47 + 3) by lia. done. }
            iPoseProof (oblP_fuel_add_set _ _ 47 with "H") as "[H _]".
            iApply oblP_fuels_init. iFrame. }
        iApply ("IHα" $! α0 LTα with "AL CF HΦ LC' EFs [//] Wgu Q_Gf Agu GMEt0 TG Fs WFs TE").
      - iPoseProof (ghost_map_lookup with "GMAo GMEo0") as "%LUp".
        iAssert (⌜(prev < c)%Z⌝)%I as "%Hpc".
        { iClear "IHν IHα". destruct (decide (prev = c)).
          { subst c. iDestruct "Hc" as "[(%& _) | Hc]".
            { subst n. lia. }
            iDestruct "Hc" as "(%& %&%& _& _& #GMEo1& HE& _)".
            iPoseProof (ghost_map_elem_agree with "GMEo0 GMEo1") as "%". simplify_eq.
            iPoseProof (untilI_discharged_false with "HE Gdk") as "%". done. }
          assert (Elemp : (prev + 1)%Z ∈ (dom tickets ∖ {[(my + 1)%Z]})).
          { apply elem_of_dom_2 in LUp. rewrite -EqDom in LUp.
            assert ((prev + 1)%Z ≠ (my + 1)%Z) by lia. set_solver. }
          iPoseProof (big_sepS_delete _ _ _ Elemp with "HMt") as "[H _]".
          iDestruct "H" as "[H | [% | H]]".
          - iDestruct "H" as "(%& %& _)". iPureIntro. lia.
          - exfalso. lia.
          - iDestruct "H" as "(%&%&%& %& _& GMEo1& _)".
            iCombine "GMEo0 GMEo1" gives %HF. by destruct HF. }
        iDestruct "Hc" as "[(%& _) | Hc]".
        { exfalso. lia. }
        iDestruct "Hc" as "(%& %&%& #CFl1& #Wl1& #GMEo1& Hc)".
        iModIntro. iMod ("ACCinv" with "[PtrNext GMAt GMAo HMt PtrCurr Hc Gg GMEt GMEo]") as "_".
        { iNext. iRight. iFrame "PtrNext NG GMAt GMAo PtrCurr". iSplit.
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
            iApply big_sepS_singleton. do 2 iRight. iFrame "Wgu". iFrame. eauto. }
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
        iPoseProof (oblP_fuel_add_set with "Fs'") as "[Fs0 Fs1]".
        iAssert (oblP_fuels ({[gu]} ∪ G) 47)%I with "[Loop_Gf Fs0]" as "Fs".
        { iPoseProof (oblP_fuels_init with "Fs0") as "Fs0".
          iPoseProof (oblP_fuels_add 47 with "Fs0") as "[Fs0 _]".
          iApply (oblP_fuels_add_obl with "Loop_Gf Fs0"). }
        iAssert (⌜(ℓ1 <= ℓ)%ordi⌝)%I as "%Hcf1".
        { iCombine "CF CFl1" gives %?. apply auth_mra_both_dfrac_valid in H1.
          2: apply _. by destruct H1. }
        iApply ("IHν" $! _ LTn with "AL CF HΦ LC' Fs1 [//] [//] [] [] [//] CFl1 Wl1 Wgu Q_Gf Agu GMEt0 TG Fs GMEo1 EFs TE").
        { iPureIntro. lia. }
        { iPureIntro. lia. }
    }
  Qed.

  Lemma TicketLock_release_spec :
    ⊢ ∃ μ, ∀ lc i G tl γ dq R κu (E : coPset) (MASK : ↑N ⊆ E) C,
    l{{{ thread_expr i C (TicketLock.release (tl : val)) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) ∗
         ⌜ κu ∈ G ⌝ ∗ oblP_kids κu ∅ ∗
         lock_token γ κu ∗ R ∗
         γ ↪LOCK_AL{dq} ∗
         is_fair_lock tl γ R }}}
      TicketLock.release tl @ i; E
    l{{{ RET #(); thread_expr i C (#()) ∗
         £ lc ∗
         thP_kids i (G ∖ {[κu]}) ∗
         γ ↪LOCK_AL{dq} }}}.
  Proof.
    iExists 100.
    iIntros (lc i G tl γ dq R κu E MASK C) "!> % (TE& TG& GF& %LUkl& Kku& LT& HR& AL& #IFL) HΦ".
    rewrite /TicketLock.release.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc 100.
    rewrite lock_token_unseal /lock_token_def.
    iDestruct "LT" as "(%& GV& #GMEtku& #GMEo)".
    iDestruct "IFL" as "(%&%& %& #INV& #ITK)".
    subst tl.
    (** Exchange token. *)
    iApply sfmupd_fupd_l. iInv "ITK" as "H".
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(%& [TK | (%& GV0& PtrCurr0& #GMEo0& GEku)])".
    { iCombine "GV TK" gives %HTK. destruct HTK. done. }
    iCombine "GV0 GV" as "GV" gives %?. destruct H as [_ ->].
    iCombine "GMEo GMEo0" gives %?. destruct H as [_ ?]. simplify_eq /=. iClear "GMEo0".
    iModIntro. iSplitL "GV".
    { iNext. iExists _. iLeft. iFrame. }
    iModIntro.
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $PtrCurr0]"). 1: done.
    iIntros "[TE ((_& TG& _)& PtrCurr0)]".
    lwp_pures.
    (* Atomic step of Store, *)
    iModIntro.
    iMod (alwaysI_acc with "INV") as "[H ACCinv]".
    { apply N_inv_subseteq. auto. }
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "[H | H]".
    { iCombine "AL H" gives %HAL. rewrite dfrac_agree_op_valid in HAL. destruct HAL.
      apply dfrac_valid_own_r in H. done. }
    iDestruct "H" as "(%&%&%&%& PtrNext& #NG& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". simplify_eq /=.
    (* FIXME: [iCombine] does not combine the dfrac parts here, hence [pointsto_agree]. *)
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_store _ ∅ lc with "[$TE $TG $GF1 PtrCurr PtrCurr0]").
    { iSplitR; first done. iDestruct "PtrCurr0" as "[PtrCurr1 PtrCurr0]".
      iCombine "PtrCurr1 PtrCurr0 PtrCurr" as "$". }
    iIntros "[TE ((QLC& TG& _)& [[PtrCurr PtrCurr1] PtrCurr0])]".
    iCombine "PtrCurr0 PtrCurr1" as "PtrCurr0".
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
    iMod (untilI_discharge with "GEku") as "H".
    { apply N_subseteq_1. set_solver. }
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iModIntro.
    iDestruct "H" as "(_& H)".
    iPoseProof ("H" $! (PThread i) G LUkl with "TG Kku [PtrCurr0 HR]") as "H".
    { iFrame. }
    iMod ("H" $! _) as "H". iApply fupd_sfmupd_elim. iMod "H" as "(H& TG& #Ofk)".
    iApply fupd_mask_intro; first solve_ndisj. iIntros "close". iModIntro. iMod "close" as "_".
    iDestruct "H" as "(PtrCurr0& HR)".
    (** Two cases: there is a waiting thread, or not. *)
    destruct (decide (c + 1 = n)%Z).
    - (* No waiting thread. *)
      subst n. clear LEc.
      iModIntro. iMod ("ACCinv" with "[PtrNext GMAt GMAo PtrCurr0 PtrCurr HMt HR]") as "_".
      { iNext. iRight. iFrame "PtrNext NG PtrCurr GMAt GMAo".
        iSplitR. 1: auto. iSplitR. 1: iPureIntro; lia. iSplitR. 1: auto. iSplitL "HMt".
        { iApply (big_sepS_impl with "HMt"). iIntros "!> %% [H | [% | H]]".
          - iDestruct "H" as "(%&%& H1& H2& H3)". iLeft. iFrame. iPureIntro. lia.
          - iLeft. simplify_eq /=. iFrame "GMEtku GMEo Ofk". iPureIntro. lia.
          - iDestruct "H" as "(%&%&%& %& _)". lia. }
        iLeft. iFrame. eauto. }
      iApply fupd_sfmupd. iApply fupd_mask_intro; first solve_ndisj. iIntros "close".
      iMod "close" as "_". iModIntro. iApply ("HΦ" with "[$TE $TG $QLC $AL]").
    - (* There is a waiting thread; create an unlock obligation for it. *)
      assert (LUt1 : (c + 2)%Z ∈ dom tickets).
      { apply Domt. lia. }
      iPoseProof (big_sepS_delete _ _ _ LUt1 with "HMt") as "[H HMt]".
      iDestruct "H" as "[H | [% | H]]".
      { iDestruct "H" as "(%& %& _)". lia. }
      { lia. }
      iDestruct "H" as "(%&%&%& %Hc1& GMEt1& GMEo1& #CFl1& Gg1& #Wg1)".
      (* Unlock obligation, in the waiting container at its own layer *)
      iModIntro.
      iMod (untilI_alloc _ _ _ ℓ0 μ with "[] Gg1")
        as "(%κu1& %LUku1& Gg1& Kku1& OGF1& #Wlku1& ALLOC)".
      { iApply (parP_le_obl with "Wg1"). reflexivity. }
      iMod ("ALLOC" $! _ N_ev True%I (curr ↦{#1/2 + 1/2/2} #(c + 2) ∗ R)%I with "[//]") as "[GUku GUku0]".
      rewrite union_empty_r_L.
      iMod (ghost_map_update (Some κu1) with "GMAo GMEo1") as "[GMAo GMEo1]".
      iMod (ghost_map_elem_persist with "GMEo1") as "#GMEo1".
      iModIntro. iMod ("ACCinv" with "[PtrNext GMAt GMAo PtrCurr0 PtrCurr HMt GMEt1 Gg1 Kku1 OGF1 GUku GUku0 HR]") as "_".
      { iNext. iRight. iFrame "PtrNext NG PtrCurr GMAt GMAo". iSplitR.
        { iPureIntro. rewrite dom_insert_lookup_L; eauto. apply elem_of_dom. by rewrite -EqDom. }
        iSplitR. 1: iPureIntro; lia. iSplitR. 1: auto. iSplitL "HMt".
        { iApply (big_sepS_delete _ _ _ LUt1). iSplitR "HMt".
          - iRight. iLeft. iPureIntro. lia.
          - iApply (big_sepS_impl with "HMt"). iIntros "!> %% [H | [% | H]]".
            + iDestruct "H" as "(%&%& H1& H2& H3)". iLeft. iFrame. iPureIntro. lia.
            + iLeft. simplify_eq /=. iFrame "GMEtku GMEo Ofk". iPureIntro. lia.
            + iDestruct "H" as "(%&%&%& %& H)". iRight. iRight. iFrame. iPureIntro.
              destruct (decide (x = (c + 2)%Z)).
              { subst. set_solver. }
              lia. }
        iRight. iSplit. 1: iPureIntro; lia.
        replace (c + 1 + 1)%Z with (c + 2)%Z by lia.
        iFrame "CFl1 Wlku1 GMEo1 GUku0". iLeft. iFrame. }
      iApply ("HΦ" with "[$TE $TG $QLC $AL]").
  Qed.

  Lemma TicketLock_delete_spec :
    ⊢ ∃ μ, ∀ lc i G tl γ R κu (E : coPset) (MASK : ↑N ⊆ E) C,
    l{{{ thread_expr i C (TicketLock.delete (tl : val)) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) ∗
         ⌜ κu ∈ G ⌝ ∗ oblP_kids κu ∅ ∗
         lock_token γ κu ∗ R ∗
         γ ↪LOCK_AL ∗
         is_fair_lock tl γ R }}}
      TicketLock.delete tl @ i; E
    l{{{ RET #(); thread_expr i C (#()) ∗ £ lc ∗ thP_kids i (G ∖ {[κu]}) ∗ R }}}.
  Proof.
    iExists 100.
    iIntros (lc i G tl γ R κu E MASK C) "!> % (TE& TG& GF& %LUkl& Kku& LT& HR& AL& #IFL) HΦ".
    rewrite /TicketLock.delete.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc 100.
    rewrite lock_token_unseal /lock_token_def.
    iDestruct "LT" as "(%& GV& #GMEtku& #GMEo)".
    iDestruct "IFL" as "(%&%& %& #INV& #ITK)".
    subst tl.
    (** Exchange token. *)
    iApply sfmupd_fupd_l. iInv "ITK" as "H".
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iDestruct "H" as "(%& [TK | (%& GV0& PtrCurr0& #GMEo0& GEku)])".
    { iCombine "GV TK" gives %HTK. destruct HTK. done. }
    iCombine "GV0 GV" as "GV" gives %?. destruct H as [_ ->].
    iCombine "GMEo GMEo0" gives %?. destruct H as [_ ?]. simplify_eq /=. iClear "GMEo0".
    iModIntro. iSplitL "GV".
    { iNext. iExists _. iLeft. iFrame. }
    iModIntro.
    lwp_pures.
    lwp_bind (Load _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_load _ ∅ 0 with "[$TE $TG $GF1 $PtrCurr0]"). 1: done.
    iIntros "[TE ((_& TG& _)& PtrCurr0)]".
    lwp_pures.
    (* Atomic step of Store, *)
    lwp_bind (Store _ _).
    iModIntro.
    iMod (alwaysI_acc with "INV") as "[H ACCinv]".
    { apply N_inv_subseteq. auto. }
    (* and we need a mupd after the step. *)
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "H" as "[H | H]".
    { iCombine "AL H" gives %HAL. rewrite dfrac_agree_op_valid in HAL. destruct HAL.
      apply dfrac_valid_own_r in H. done. }
    iDestruct "H" as "(%&%&%&%& PtrNext& #NG& PtrCurr& GMAt& GMAo& %EqDom& %Boundc& %Domt& HMt& Hc)".
    iPoseProof (pointsto_agree with "PtrCurr PtrCurr0") as "%". simplify_eq /=.
    (* FIXME: [iCombine] does not combine the dfrac parts here, hence [pointsto_agree]. *)
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_store _ ∅ lc with "[$TE $TG $GF1 PtrCurr PtrCurr0]").
    { iSplitR; first done. iDestruct "PtrCurr0" as "[PtrCurr1 PtrCurr0]".
      iCombine "PtrCurr1 PtrCurr0 PtrCurr" as "$". }
    iIntros "[TE ((QLC& TG& _)& [[PtrCurr PtrCurr1] PtrCurr0])]".
    iCombine "PtrCurr0 PtrCurr1" as "PtrCurr0".
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
    iMod (untilI_discharge with "GEku") as "H".
    { apply N_subseteq_1. set_solver. }
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_later with "LC1"). iNext.
    iModIntro.
    iDestruct "H" as "(_& H)".
    iPoseProof ("H" $! (PThread i) G LUkl with "TG Kku [PtrCurr0 HR]") as "H".
    { iFrame. }
    iMod ("H" $! _) as "H". iApply fupd_sfmupd_elim. iMod "H" as "(H& TG& #Ofk)".
    iApply fupd_mask_intro; first solve_ndisj. iIntros "close". iModIntro. iMod "close" as "_".
    iDestruct "H" as "(PtrCurr0& HR)".
    iPoseProof (oblP_fuels_remove_obl κ with "GF") as "GF".
    (** Return full CF to the invariant. *)
    iModIntro. iMod ("ACCinv" with "[AL]") as "_".
    { iNext. iLeft. iFrame. }
    iDestruct "PtrCurr0" as "[PtrCurr1 PtrCurr0]". iCombine "PtrCurr1 PtrCurr PtrCurr0" as "PtrCurr".
    iClear "HMt GMAt GMAo". clear dependent tickets obls.
    iApply fupd_sfmupd. iApply fupd_mask_intro; first solve_ndisj. iIntros "close".
    iMod "close" as "_". iModIntro.
    lwp_pures.
    lwp_bind (Free _).
    (* The mono cell, open for the step, keeps half of [next]'s freed points-to. *)
    iModIntro. iMod (alwaysI_guar_acc with "NG") as "[HJ CloseJ]".
    { etrans; last apply MASK. apply nclose_subseteq. }
    iApply lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 with "LC") as "[LC1 LC]".
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "HJ" as "(%w& Auth& [PtrNext0 | Fr])"; last first.
    { iDestruct (freed_pointsto_false with "Fr PtrNext") as %[]. }
    iDestruct (pointsto_agree with "PtrNext PtrNext0") as %[= <-].
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_free_freed _ ∅ 0 with "[$TE $TG $GF1 PtrNext PtrNext0]").
    { iSplitR; first done. iCombine "PtrNext PtrNext0" as "$". }
    iIntros "(TE& (_& TG& _)& Fr)".
    iEval (rewrite -Qp.half_half freed_split) in "Fr". iDestruct "Fr" as "[Fr _]".
    iModIntro. iMod ("CloseJ" with "[Auth Fr]") as "_".
    { iNext. iExists n. iFrame. }
    iModIntro.
    lwp_pures.
    lwp_bind (Free _).
    iModIntro.
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iApply (lwp_free _ ∅ 0 with "[$TE $TG $GF1 $PtrCurr]"). 1: done.
    iIntros "(TE& _& TG& _)".
    iApply ("HΦ" with "[$]").
  Qed.

  (** ** Temporal guarantees *)
  (** The trace property guaranteed by the right disjunct of [lock_inv] (the lock is alive),
      as inferred by [IntoTemporal]: [tps_true] for ghost state, [R] and the ghost facts
      about the ticket maps (whose quantifiers are therefore ghost). If a ticket is pending
      ([c < n]), the until allocated on behalf of the next owner carries
      [finally curr ↦ c + 1]. The registration of the mono cell for [n] carries
      [□ next_ge_tps next n]. *)
  Definition lock_inv_alive_tps (next curr : loc) : tps heap_lang Σ :=
    (∃ n c : Z,
       next ↦{#(1/2)} #n ∧ tps_always (next_ge_tps next n) ∧
       curr ↦{#(1/2/2)} #c ∧ tps_true ∧ tps_true ∧ tps_true ∧
       ⌜(0 ≤ c ≤ n)%Z⌝ ∧ tps_true ∧ tps_true ∧
       (⌜c = n⌝ ∧ curr ↦{#(1/2 + 1/2/2)} #c ∧ tps_true ∨
        ⌜(c < n)%Z⌝ ∧
          (tps_true ∧ tps_true ∧ tps_true ∧
           tps_finally (curr ↦{#(1/2 + 1/2/2)} #(c + 1) ∧ tps_true) ∧
           ((tps_true ∧ tps_finally (curr ↦{#(1/2 + 1/2/2)} #(c + 1) ∧ tps_true) ∧
             tps_true ∧ tps_true ∧ tps_true ∧ curr ↦{#(1/2 + 1/2/2)} #c ∧ tps_true) ∨ tps_true))))%S.

  (** The trace property guaranteed by [lock_inv]. Its left disjunct (the lock has been
      deleted) is ghost state, so this property alone says nothing about the trace. *)
  Definition lock_inv_tps (next curr : loc) : tps heap_lang Σ :=
    (tps_true ∨ lock_inv_alive_tps next curr)%S.

  (** The trace property guaranteed by [lock_token_inv]: either nobody holds the lock (ghost
      state), or its holder will increment [curr]. As it stands, it says nothing about the
      trace either (the left disjunct). *)
  Definition lock_token_inv_tps (curr : loc) : tps heap_lang Σ :=
    (∃ c : Z, tps_true ∨
       tps_true ∧ curr ↦{#(1/2 + 1/2/2)} #c ∧ tps_true ∧
       tps_finally (curr ↦{#(1/2 + 1/2/2)} #(c + 1) ∧ tps_true))%S.

  (** The trace property guaranteed by [is_fair_lock]. Since the lock can be deleted
      ([TicketLock_delete_spec]), it is vacuous at the level of traces; see
      [is_fair_lock_alive_temporal] for a lock that cannot be deleted. *)
  Definition fair_lock_tps (tl : val) : tps heap_lang Σ :=
    (∃ next curr : loc, ⌜tl = (#next, #curr)%V⌝ ∧
       tps_always (lock_inv_tps next curr) ∧ tps_always (lock_token_inv_tps curr))%S.

  Lemma is_fair_lock_temporal tl γ R : ⊢ is_fair_lock tl γ R ⊨ₜ fair_lock_tps tl.
  Proof. apply (into_temporal _ _). Qed.

  (** Clients see the lock's guarantee, not its invariant. *)
  Global Instance is_fair_lock_into_temporal tl γ R :
    IntoTemporal (is_fair_lock tl γ R) (fair_lock_tps tl) | 0.
  Proof. apply is_fair_lock_temporal. Qed.

  (** The trace property guaranteed by a lock that cannot be deleted. *)
  Definition alive_fair_lock_tps (tl : val) : tps heap_lang Σ :=
    (fair_lock_tps tl ∧
     ∃ next curr : loc, ⌜tl = (#next, #curr)%V⌝ ∧ tps_always (lock_inv_alive_tps next curr))%S.

  (** A persistent [γ ↪LOCK_AL□] (as the queue keeps) rules out deletion, hence the left
      disjunct of [lock_inv]: the lock invariant is registered under its alive branch. *)
  Lemma is_fair_lock_register_alive E tl γ R :
    ↑N_inv ⊆ E →
    is_fair_lock tl γ R -∗ γ ↪LOCK_AL□ -∗ |={E}=>m is_fair_lock_alive tl γ R.
  Proof.
    iIntros (HN) "(%next& %curr& %Htl& #I& #K) #AL".
    iMod (alwaysI_register E N_inv _
            (lock_inv_alive (ticketlock_γt γ) (ticketlock_γo γ) (ticketlock_γc γ) (ticketlock_γm γ) next curr R)%I
            with "[] []") as "#IA"; [done| | |].
    { by iApply alwaysI_inv. }
    { iIntros "!> [H|$]". iCombine "AL H" gives %HAL. rewrite dfrac_agree_op_valid in HAL.
      destruct HAL as [H _]. apply dfrac_valid_own_r in H. done. }
    iModIntro. iSplitR.
    { iExists next, curr. iSplit; first done. iFrame "I K". }
    iExists next, curr. iSplit; first done. iFrame "IA".
  Qed.

  Lemma is_fair_lock_alive_temporal tl γ R :
    ⊢ is_fair_lock_alive tl γ R ⊨ₜ alive_fair_lock_tps tl.
  Proof. apply (into_temporal _ _). Qed.

  Global Instance is_fair_lock_alive_into_temporal tl γ R :
    IntoTemporal (is_fair_lock_alive tl γ R) (alive_fair_lock_tps tl) | 0.
  Proof. apply is_fair_lock_alive_temporal. Qed.

  (** [lock_token] is ghost state: the holder's [finally] lives in [lock_token_inv]. *)

End proof.

(** ** Progress of the lock, at the level of traces
    The notions of ticket_lock.v: release progress, [next] never decreases, starvation
    freedom. *)
Section trace.
  Local Notation tr_pointsto := ticket_lock.tr_pointsto.

  Lemma lock_inv_alive_tps_release_progress {Σ} next curr τ :
    tps_tr (tps_always (lock_inv_alive_tps (Σ:=Σ) next curr)) τ →
    ticket_lock.release_progress next curr τ.
  Proof.
    destruct τ as [k τf]. intros Hal m Hm n c Hn Hc Hlt.
    destruct (Hal m Hm) as (n' & c' & Hn' & _ & Hc' & _ & _ & _ & Hb & _ & _ & Hcase).
    simpl in *. unfold tr_pointsto, tr_atomic, ts_emb, ts_atomic, tr_pure in *. simpl in *.
    destruct (τf m) as [[[Θ σ] ?] ?]. simpl in *.
    rewrite Hn in Hn'. rewrite Hc in Hc'. simplify_eq.
    destruct Hcase as [[? _] | [_ (_ & _ & _ & Hfin & _)]]; [lia|].
    destruct Hfin as (m' & Hm' & [Hcur _] & _). exists m'. split_and!; [done|done|].
    intros. done.
  Qed.

  (** [next] never decreases: at every position the alive branch has [next ↦ n] and the
      registration of the mono cell for [n], which gives [next ≥ n] or [next] freed from then
      on; [next] is not freed, since the alive branch has [next ↦ n'] at every position. *)
  Lemma lock_inv_alive_tps_next_monotone {Σ} next curr τ :
    tps_tr (tps_always (lock_inv_alive_tps (Σ:=Σ) next curr)) τ → ticket_lock.next_monotone next τ.
  Proof.
    destruct τ as [k τf]. intros Hal m Hm n Hn m' Hm'.
    destruct (Hal m Hm) as (n0 & c0 & Hn0 & Hge & _).
    destruct (Hal m' ltac:(simpl in *; lia)) as (n1 & c1 & Hn1 & _).
    destruct (Hge m' Hm') as [(w & Hw & Hnw) | Hfr].
    - assert (n = n0) as ->.
      { simpl in *. unfold tr_pointsto, tr_atomic, ts_emb, ts_atomic in *. simpl in *.
        destruct (τf m) as [[[Θ σ] ?] ?]. simpl in *. rewrite Hn in Hn0. by simplify_eq. }
      exists w. split; [exact Hnw|done].
    - exfalso. simpl in *. unfold tr_atomic, ts_emb, ts_atomic in *. simpl in *.
      destruct (τf m') as [[[Θ σ] ?] ?]. simpl in *. by rewrite Hn1 in Hfr.
  Qed.

  (** A lock that cannot be deleted makes release progress, and [next] never decreases. *)
  Lemma alive_fair_lock_release_progress {Σ} tl τ :
    tps_tr (alive_fair_lock_tps (Σ:=Σ) tl) τ →
    ∃ next curr : loc, tl = (#next, #curr)%V ∧ ticket_lock.release_progress next curr τ.
  Proof.
    intros (_ & next & curr & Htl & Hal). exists next, curr. split; first done.
    by eapply (lock_inv_alive_tps_release_progress (Σ:=Σ)).
  Qed.

  Lemma alive_fair_lock_next_monotone {Σ} tl τ :
    tps_tr (alive_fair_lock_tps (Σ:=Σ) tl) τ →
    ∃ next curr : loc, tl = (#next, #curr)%V ∧ ticket_lock.next_monotone next τ.
  Proof.
    intros (_ & next & curr & Htl & Hal). exists next, curr. split; first done.
    by eapply (lock_inv_alive_tps_next_monotone (Σ:=Σ)).
  Qed.

  (** Hence a lock that cannot be deleted is starvation free, with no hypothesis about
      [next] (compare [ticket_lock.release_progress_starvation_free]). *)
  Lemma alive_fair_lock_starvation_free {Σ} tl τ :
    tps_tr (alive_fair_lock_tps (Σ:=Σ) tl) τ →
    ∃ next curr : loc, tl = (#next, #curr)%V ∧ ticket_lock.starvation_free next curr τ.
  Proof.
    intros (_ & next & curr & Htl & Hal). exists next, curr. split; first done.
    apply ticket_lock.release_progress_starvation_free.
    - by eapply (lock_inv_alive_tps_release_progress (Σ:=Σ)).
    - by eapply (lock_inv_alive_tps_next_monotone (Σ:=Σ)).
  Qed.

End trace.

Global Notation "γ ↪LOCK_AL dq" :=
  (own_fair_lock_alive γ dq)%I
    (at level 20, dq custom dfrac at level 1, format "γ  ↪LOCK_AL dq") : bi_scope.

Global Notation "γ ↪LOCK_CF dq l" :=
  (own_fair_lock_layer γ l dq)%I
    (at level 20, dq custom dfrac at level 1, format "γ  ↪LOCK_CF dq  l") : bi_scope.
