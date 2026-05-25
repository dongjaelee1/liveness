From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_var ghost_map.

From liris.heap_lang.examples Require Import ticket_lock extended_int.

Module LockCouplingSet.
  (** https://www.cs.toronto.edu/~azadeh/resources/papers/tada-live.pdf
      Fig 27 and 28

      Each node is a contiguous block of three cells:
        offset 0: lock      (a [TicketLock] value)
        offset 1: value     (NONE for the tail sentinel = +∞, SOME z otherwise)
        offset 2: next      (location of the successor; unused on the tail)

      The set is represented by a pointer to its head sentinel.  The head's
      value is never compared, so we pick an arbitrary placeholder. *)

  Definition getLock : val := λ: "x", !("x" +ₗ #0).
  Definition getVal : val := λ: "x", !("x" +ₗ #1).
  Definition nextRef : val := λ: "x", "x" +ₗ #2.

  Definition lockNode : val :=
    λ: "x", TicketLock.acquire (getLock "x").

  Definition unlockNode : val :=
    λ: "x", TicketLock.release (getLock "x").

  Definition newNode : val :=
    λ: "value" "next",
      let: "n" := AllocN #3 #0 in
      "n" +ₗ #0 <- TicketLock.init #();;
      "n" +ₗ #1 <- "value";;
      "n" +ₗ #2 <- "next";;
      "n".

  Definition makeSet : val :=
    λ: <>,
      let: "tail" := newNode (Int.into_val +∞) #(Loc 0) in
      let: "head" := newNode (Int.into_val -∞) "tail" in
      "head".

  (** Traverse the list hand-over-hand, starting from a locked [curr], until
      we find a successor [next] with value ≥ v.  Returns the locked pair
      (curr, next) where curr.next = next. *)
  Definition locate : val :=
    λ: "x" "e",
      lockNode "x";;
      (rec: "loop" "curr" :=
         let: "next" := !(nextRef "curr") in
         if: Int.lt (getVal "next") "e" then
           lockNode "next";;
           unlockNode "curr";;
           "locate" "next" "e"
         else ("curr", "next")) "x".

  Definition member : val :=
    λ: "head" "v",
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      let: "contains" := ~ (Int.lt "v" (getVal "next")) in
      unlockNode "curr";;
      "contains".

  Definition add : val :=
    λ: "head" "v",
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      (if: Int.lt "v" (getVal "next") then
         nextRef "curr" <- newNode "v" "next"
       else #());;
      unlockNode "curr".

  Definition remove : val :=
    λ: "head" "v",
      let: "p" := locate "head" "v" in
      let: "curr" := Fst "p" in
      let: "next" := Snd "p" in
      (if: Int.lt "v" (getVal "next") then #() else
         lockNode "next";;
         nextRef "curr" <- !(nextRef "next");;
         unlockNode "next");;
      unlockNode "curr".

End LockCouplingSet.

Section ticket_lock.
  Context `{!heapGS Σ} `{!ticket_lockG Σ}.
  (* FIXME: extremely messy. *)
  Global Instance is_fair_lock_ne lk γlk : NonExpansive (is_fair_lock lk γlk).
  Proof.
  Admitted.

End ticket_lock.

Class lcsG Σ :=
  {
    lcs_lockG :: ticket_lockG Σ;
  }.

Record lcs_names :=
  {
    set_gn : gname;
  }.


Section proof.
  Context `{!heapGS Σ} `{!lcsG Σ}.

  Definition lockΔ : ord.t := ℵ%ordi.

  (* Includes element a and b, unless they are infinite, and excludes everything
     in between. *)
  Local Axiom own_interval : ∀ (γ : lcs_names) (a : Int.t) (b : Int.t), iProp Σ.

  Axiom own_set : ∀ (γ : lcs_names) (s : gset Z), iProp Σ.

  Local Axiom alloc_set : ⊢ |==> ∃ γ, own_set γ ∅ ∗ own_interval γ -∞ +∞.

  Local Axiom own_interval_not_NegInf : ∀ γ a b,
    own_interval γ a b ⊢ ⌜ b ≠ Int.NegInf ⌝.

  Definition is_node_pre
      (is_node : loc -d> lcs_names -d> Int.t -d> ticketlock_γ -d> iPropO Σ) :
      loc -d> lcs_names -d> Int.t -d> ticketlock_γ -d> iPropO Σ :=
    λ n γ v γlk,
      (∃ lk,
          (n +ₗ 1) ↦□ (Int.into_val v) ∗
          (n +ₗ 0) ↦□ lk ∗
          is_fair_lock lk γlk (
              ∃ ℓ (n' : loc) v',
                γlk ↪LOCK{#1/2} ℓ ∗
                (n +ₗ 2) ↦ #n' ∗
                (n' +ₗ 1) ↦□ (Int.into_val v') ∗
                own_interval γ v v' ∗
                (match v' with
                 | +∞ => True
                 | -∞ => False
                 | _ => (∃ γlk' ℓ',
                           ▷ is_node n' γ v' γlk' ∗
                           γlk' ↪LOCK{#1/2} ℓ' ∗
                           ⌜ ((ℓ' ⊕ lockΔ) < ℓ)%ordi ⌝)
                 end)
                (* TODO: own ghost state for range. *)
      ))%I.

  Ltac solve_contractive :=
    solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv | (eapply dist_lt; last eassumption)]).

  Local Instance is_node_pre_contractive : Contractive is_node_pre.
  Proof.
    (* solve_contractive. *) (* TODO: probably the match statement. *)
  Admitted.

  Definition is_node : loc → lcs_names → Int.t → ticketlock_γ → iProp Σ := fixpoint is_node_pre.

  Lemma is_node_unfold n γ v γlk : is_node n γ v γlk ⊣⊢ is_node_pre is_node n γ v γlk.
  Proof. apply (fixpoint_unfold is_node_pre n γ). Qed.

  Instance is_node_persistent n γ v γlk : Persistent (is_node n γ v γlk).
  Proof. rewrite is_node_unfold. apply _. Qed.

  Definition is_set (root : loc) γ : iProp Σ :=
    ∃ γlk,
      γlk ↪LOCK□ (ℵ × lockΔ)%ordi ∗
      is_node root γ Int.NegInf γlk.

  Import LockCouplingSet.

  Ltac post_wp :=
    iFrame; iExists ∅, 0; iSplitR; [by eauto | iIntros "Hg Hfuel _ _"; iModIntro; simpl].

  Ltac post_wp_bind :=
    iFrame; iExists ∅, 0; iSplitR; [by eauto | iIntros "Hg Hfuel _ _"; simpl].

  Ltac lwp_pures := lwp_pure; repeat (post_wp; lwp_pure); post_wp_bind.

  Tactic Notation "lOneFuel" open_constr(Hfuel) "as" open_constr(Hdestruct) :=
    iDestruct (ogP_fuel_eq_set _ _ _ (1⊕(_:nat))%M with Hfuel) as Hfuel;
    [ rewrite measure_add !measure_nat -Hessenberg.add_from_nat // | ];
    iDestruct (ogP_fuel_add_set with Hfuel) as Hdestruct.

  Local Lemma lwp_newNode :
    ⊢ ∃ m,
      ∀ ℓ i G (next : loc) γ v v',
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g 0 m) ∗
         (match v' with
           | +∞ => (next +ₗ 1) ↦□ (Int.into_val +∞)
           | _ => (∃ γlk' ℓ',
                     is_node next γ v' γlk' ∗
                     γlk' ↪LOCK{#1/2} ℓ' ∗
                     ⌜ ((ℓ' ⊕ lockΔ) < ℓ)%ordi ⌝)
           end) ∗
         own_interval γ v v'
      }}}
     newNode (Int.into_val v) #next @ i
    l{{{ s γlk, RET #s; thP_groups i G ∗ is_node s γ v γlk ∗ γlk ↪LOCK{#1/2} ℓ }}}.
  Proof.
    iDestruct (TicketLock_init_spec) as (mi) "TicketLock_init_spec".
    iExists (100 ⊕ mi ⊕ mi)%M.
    iIntros.
    iIntros (?) "!# (Hg & Hfuel & Hn' & Hown) HΦ".
    iDestruct (own_interval_not_NegInf with "Hown") as "%".

    iDestruct (ogP_fuel_add_set with "Hfuel") as "[Hfuel HlockFuel]".
    lwp_lam. post_wp. lwp_pures. lwp_bind (AllocN _ _).
    iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_allocN _ ∅ 0 with "[$Hg $Hf //]"); first done.
    iIntros (n) "[(_ & Hg & _) (Hn & _)]". iModIntro.
    lwp_pures.

    lwp_bind (TicketLock.init _).
    iModIntro.
    iDestruct (ogP_fuel_add_set with "HlockFuel") as "[Hlock HlockFuel]".
    iApply ("TicketLock_init_spec" $! 0 ℓ with "[$]").
    iIntros (lk γlk) "(_ & Hg & Hlk & Hlk_inv) !>".
    lwp_pures.

    rewrite !array_cons. rewrite Loc.add_0 Loc.add_assoc /=.
    iDestruct "Hn" as "(lk & val & next & _)".

    lwp_bind (_ <- _)%E. iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_store _ ∅ 0 with "[$Hg $Hf $lk //]").
    iIntros "[(_ & Hg & _) lk]". iMod (pointsto_persist with "lk") as "#lk".
    iModIntro. lwp_pures.

    lwp_bind (_ <- _)%E. iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_store _ ∅ 0 with "[$Hg $Hf $val //]").
    iIntros "[(_ & Hg & _) val]". iMod (pointsto_persist with "val") as "#val".
    iModIntro. lwp_pures.

    lwp_bind (_ <- _)%E. iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_store _ ∅ 0 with "[$Hg $Hf $next //]").
    iIntros "[(_ & Hg & _) next]".
    iModIntro. lwp_pures.

    iModIntro. lwp_finish. iApply "HΦ".
    iEval (rewrite is_node_unfold).
    iDestruct "Hlk" as "[Hlk ?]". iFrame.
    iMod ("Hlk_inv" with "[-]") as "#H".
    2:{ iModIntro. iFrame "#". rewrite Loc.add_0. iFrame "#". }
    iFrame "∗#%".
    destruct v'; try done.
    - iDestruct "Hn'" as (??) "(#Hn' & $ & %Hℓ)".
      iDestruct (is_node_unfold with "Hn'") as (lk') "(#? & _)".
      iFrame "#". iFrame "∗#%".
    - iFrame.
  Qed.

  Local Lemma lwp_newNode_tail :
    ⊢ ∃ m,
        ∀ i G,
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g 0 m) }}}
     newNode (Int.into_val +∞) #(Loc 0) @ i
    l{{{ n, RET #n; thP_groups i G ∗ (n +ₗ 1) ↦□ (Int.into_val +∞) }}}.
  Proof using lcsG0.
    iDestruct (TicketLock_init_spec) as (mi) "TicketLock_init_spec".
    iExists (100 ⊕ mi ⊕ mi)%M.
    iIntros. iIntros (?) "!# (Hg & Hfuel) HΦ".

    iDestruct (ogP_fuel_add_set with "Hfuel") as "[Hfuel HlockFuel]".

    lwp_lam. post_wp. lwp_pures. lwp_bind (AllocN _ _).
    iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_allocN _ ∅ 0 with "[$Hg $Hf //]"); first done.
    iIntros (n) "[(_ & Hg & _) (Hn & _)]". iModIntro.
    lwp_pures.

    lwp_bind (TicketLock.init _).
    iModIntro.
    iDestruct (ogP_fuel_add_set with "HlockFuel") as "[Hlock HlockFuel]".
    iApply ("TicketLock_init_spec" $! 0 0 with "[$]").
    iIntros (lk γlk) "(_ & Hg & Hlk & Hlk_inv) !>".
    lwp_pures.

    rewrite !array_cons. rewrite Loc.add_0 Loc.add_assoc /=.
    iDestruct "Hn" as "(lk & val & next & _)".

    lwp_bind (_ <- _)%E. iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_store _ ∅ 0 with "[$Hg $Hf $lk //]").
    iIntros "[(_ & Hg & _) lk]". iMod (pointsto_persist with "lk") as "#lk".
    iModIntro. lwp_pures.

    lwp_bind (_ <- _)%E. iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_store _ ∅ 0 with "[$Hg $Hf $val //]").
    iIntros "[(_ & Hg & _) val]". iMod (pointsto_persist with "val") as "#val".
    iModIntro. lwp_pures.

    lwp_bind (_ <- _)%E. iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_store _ ∅ 0 with "[$Hg $Hf $next //]").
    iIntros "[(_ & Hg & _) next]".
    iModIntro. lwp_pures.

    iModIntro. lwp_finish. iApply "HΦ". iModIntro.
    iFrame "∗#".
  Qed.

  Opaque Int.into_val.
  Lemma lwp_makeSet i G :
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g 1 1) }}}
     makeSet #() @ i
    l{{{ s γ, RET #s; thP_groups i G ∗ is_set s γ ∗ own_set γ ∅ }}}.
  Proof.
    iIntros (?) "(Hg & Hfuel) HΦ".
    iDestruct lwp_newNode_tail as (mnt) "lwp_newNode_tail".
    iDestruct lwp_newNode as (mn) "lwp_newNode".

    iMod (ogP_fuel_extend_set _ 0 _ (100 ⊕ mnt ⊕ mn)%M with "Hfuel") as "Hfuel".
    { apply ordArith.lt_from_nat. lia. }

    iDestruct (ogP_fuel_add_set with "Hfuel") as "[Hfuel HcallFuel]".
    lwp_lam. post_wp_bind.

    lwp_bind (newNode _ _). iModIntro.
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[Hf HcallFuel]".
    iApply ("lwp_newNode_tail" with "[$Hg $Hf]").
    iIntros (n') "(Hg & #Hn')". iModIntro. lwp_pures.

    lwp_bind (newNode _ _). iModIntro.
    iMod alloc_set as (γ) "[Hset Hown]".
    iApply ("lwp_newNode" with "[$Hg $HcallFuel $Hown]").
    { iFrame "#". }
    iIntros (n γlk) "(Hg & Hn & ?)". iModIntro. lwp_pures. iModIntro.
    lwp_finish. iApply "HΦ". iFrame.
    iMod (lock_config_persist with "[$]") as "#$". done.
  Qed.

  Lemma lwp_locate i G s γ (e : Z) :
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g 1 1) ∗
         is_set s γ }}}
     locate #s (Int.into_val e) @ i
    l{{{ s, RET #s; is_node s γ }}}.
  Proof.
    iIntros (?) "(Hg & Hfuel & #Hs) HΦ".
    iDestruct (TicketLock_acquire_spec) as (ma) "TicketLock_acquire_spec".
    iDestruct (TicketLock_release_spec) as (mr) "TicketLock_release_spec".

    iMod (ogP_fuel_extend_set _ 0 _ (100⊕ma⊕mr)%M with "Hfuel") as "Hfuel".
    { apply ordArith.lt_from_nat. lia. }
    rewrite /is_set is_node_unfold.
    iDestruct "Hs" as  (???) "(#lock & #val & #Hlock)".

    (* TODO: instance for splitting. *)
    iDestruct (ogP_fuel_add_set with "Hfuel") as "[Hfuel HlockFuel]".

    lwp_lam. post_wp. lwp_pures. iModIntro. lwp_lam. post_wp. lwp_lam. post_wp.
    lwp_pures. lwp_bind (! _)%E. iModIntro.

    lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
    iIntros "[(_ & Hg & _) _]". lwp_bind (TicketLock.acquire lk). iModIntro.

    iDestruct (ogP_fuel_add_set with "HlockFuel") as "[HacqFuel HrelFuel]".
    (* TODO: lock should abstract away the gap `ℵ` into an opaque defn like
       "lockΔ : ord.t" or something. *)
    iApply ("TicketLock_acquire_spec" with "[$Hg]").
    { iFrame "#". }
    Search ℵ%M.

    lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_lockNode with "[$]"). iModIntro.
    iIntros "Hg !>". lwp_pures.
  Qed.

End proof.
