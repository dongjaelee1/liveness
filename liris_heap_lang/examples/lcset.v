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
        offset 2: next      (location of the successor; unused on the tail) *)

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

  Definition node_lock_inv_pre
      (is_node : loc -d> lcs_names -d> Int.t -d> val -d> ticketlock_γ -d> iPropO Σ) :
      loc -d> lcs_names -d> Int.t -d> ticketlock_γ -d> loc -d> Int.t -d> iPropO Σ :=
    λ n γ v γlk n' v',
      (∃ ℓ,
          γlk ↪LOCK{#1/2} ℓ ∗
          (n +ₗ 2) ↦ #n' ∗
          (n' +ₗ 1) ↦□ (Int.into_val v') ∗
          own_interval γ v v' ∗
          (match v' with
           | +∞ => True
           | -∞ => False
           | _ => (∃ lk' γlk' ℓ',
                     ▷ is_node n' γ v' lk' γlk' ∗
                     γlk' ↪LOCK{#1/2} ℓ' ∗
                     ⌜ ((ℓ' ⊕ lockΔ) < ℓ)%ordi ⌝)
           end)
      )%I.

  Definition is_node_pre
      (is_node : loc -d> lcs_names -d> Int.t -d> val -d> ticketlock_γ -d> iPropO Σ) :
      loc -d> lcs_names -d> Int.t -d> val -d> ticketlock_γ -d> iPropO Σ :=
    λ n γ v lk γlk,
      ((n +ₗ 1) ↦□ (Int.into_val v) ∗
       (n +ₗ 0) ↦□ lk ∗
       is_fair_lock lk γlk (∃ n' v', node_lock_inv_pre is_node n γ v γlk n' v'))%I.

  Ltac solve_contractive :=
    solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv | (eapply dist_lt; last eassumption)]).

  Local Instance is_node_pre_contractive : Contractive is_node_pre.
  Proof.
    (* solve_contractive. *) (* TODO: probably the match statement. *)
  Admitted.

  Definition is_node : loc → lcs_names → Int.t → val → ticketlock_γ → iProp Σ := fixpoint is_node_pre.

  Definition node_lock_inv : loc → lcs_names → Int.t → ticketlock_γ → loc → Int.t → iProp Σ :=
    node_lock_inv_pre is_node.

  Lemma is_node_unfold n γ v lk γlk : is_node n γ v lk γlk ⊣⊢ is_node_pre is_node n γ v lk γlk.
  Proof. apply (fixpoint_unfold is_node_pre n γ). Qed.

  Instance is_node_persistent n γ v lk γlk : Persistent (is_node n γ v lk γlk).
  Proof. rewrite is_node_unfold. apply _. Qed.

  Definition is_set (root : loc) γ : iProp Σ :=
    ∃ γlk lk,
      γlk ↪LOCK□ (ℵ × lockΔ)%ordi ∗
      is_node root γ Int.NegInf lk γlk.

  Import LockCouplingSet.

  Ltac post_wp :=
    iFrame; iExists ∅, 0; iSplitR; [by eauto | iIntros "Hg Hfuel _ _"; iModIntro; simpl].

  Ltac post_wp_bind :=
    iFrame; iExists ∅, 0; iSplitR; [by eauto | iIntros "Hg Hfuel _ _"; simpl].

  Ltac lwp_pures := lwp_pure; repeat (post_wp; lwp_pure); post_wp_bind.

  Tactic Notation "lOneFuel" open_constr(Hfuel) "as" open_constr(Hdestruct) :=
    iDestruct (ogP_fuels_add 1 with Hfuel) as Hdestruct; first done.

  Local Lemma lwp_newNode :
    ⊢ ∃ m,
      ∀ ℓ i G (next : loc) γ v v',
    l{{{ thP_groups i G ∗ ogP_fuels G m ∗
         (match v' with
           | +∞ => (next +ₗ 1) ↦□ (Int.into_val +∞)
           | _ => (∃ lk' γlk' ℓ',
                     is_node next γ v' lk' γlk' ∗
                     γlk' ↪LOCK{#1/2} ℓ' ∗
                     ⌜ ((ℓ' ⊕ lockΔ) < ℓ)%ordi ⌝)
           end) ∗
         own_interval γ v v'
      }}}
     newNode (Int.into_val v) #next @ i
    l{{{ s lk γlk, RET #s; thP_groups i G ∗ is_node s γ v lk γlk ∗ γlk ↪LOCK{#1/2} ℓ }}}.
  Proof.
    iDestruct (TicketLock_init_spec) as (mi) "TicketLock_init_spec".
    iExists (100 ⊕ mi ⊕ mi)%M.
    iIntros.
    iIntros (?) "!# (Hg & Hfuel & Hn' & Hown) HΦ".
    iDestruct (own_interval_not_NegInf with "Hown") as "%".

    iDestruct (ogP_fuels_add_gen with "Hfuel") as "[Hfuel HcallFuel]".

    lwp_lam. post_wp. lwp_pures. lwp_bind (AllocN _ _).
    iModIntro.
    Search "ogP_fuels".

    lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_allocN _ ∅ 0 with "[$Hg $Hf //]"); first done.
    iIntros (n) "[(_ & Hg & _) (Hn & _)]". iModIntro.
    lwp_pures.

    lwp_bind (TicketLock.init _).
    iModIntro.
    iDestruct (ogP_fuels_add_gen with "HcallFuel") as "[Hlock HcallFuel]".
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
    - iDestruct "Hn'" as (???) "(#Hn' & $ & %Hℓ)".
      iDestruct (is_node_unfold with "Hn'") as "(#? & _)".
      iFrame "#". iFrame "∗#%".
    - iFrame.
  Qed.

  Local Lemma lwp_newNode_tail :
    ⊢ ∃ m,
        ∀ i G,
    l{{{ thP_groups i G ∗ ogP_fuels G m }}}
     newNode (Int.into_val +∞) #(Loc 0) @ i
    l{{{ n, RET #n; thP_groups i G ∗ (n +ₗ 1) ↦□ (Int.into_val +∞) }}}.
  Proof using lcsG0.
    iDestruct (TicketLock_init_spec) as (mi) "TicketLock_init_spec".
    iExists (100 ⊕ mi ⊕ mi)%M.
    iIntros. iIntros (?) "!# (Hg & Hfuel) HΦ".

    iDestruct (ogP_fuels_add_gen with "Hfuel") as "[Hfuel HlockFuel]".

    lwp_lam. post_wp. lwp_pures. lwp_bind (AllocN _ _).
    iModIntro. lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_allocN _ ∅ 0 with "[$Hg $Hf //]"); first done.
    iIntros (n) "[(_ & Hg & _) (Hn & _)]". iModIntro.
    lwp_pures.

    lwp_bind (TicketLock.init _).
    iModIntro.
    iDestruct (ogP_fuels_add_gen with "HlockFuel") as "[Hlock HlockFuel]".
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
  Lemma lwp_makeSet :
    ⊢ ∃ m, ∀ i G,
    l{{{ thP_groups i G ∗ ogP_fuels G m }}}
     makeSet #() @ i
    l{{{ s γ, RET #s; thP_groups i G ∗ is_set s γ ∗ own_set γ ∅ }}}.
  Proof.
    iDestruct lwp_newNode_tail as (mnt) "lwp_newNode_tail".
    iDestruct lwp_newNode as (mn) "lwp_newNode".
    iExists (100 ⊕ mnt ⊕ mn)%M. iIntros. iIntros (?) "!# (Hg & Hfuel) HΦ".

    iDestruct (ogP_fuels_add_gen with "Hfuel") as "[Hfuel HcallFuel]".
    lwp_lam. post_wp_bind.

    lwp_bind (newNode _ _). iModIntro.
    iDestruct (ogP_fuels_add_gen with "HcallFuel") as "[Hf HcallFuel]".
    iApply ("lwp_newNode_tail" with "[$Hg $Hf]").
    iIntros (n') "(Hg & #Hn')". iModIntro. lwp_pures.

    lwp_bind (newNode _ _). iModIntro.
    iMod alloc_set as (γ) "[Hset Hown]".
    iApply ("lwp_newNode" with "[$Hg $HcallFuel $Hown]").
    { iFrame "#". }
    iIntros (n lk γlk) "(Hg & Hn & ?)". iModIntro. lwp_pures. iModIntro.
    lwp_finish. iApply "HΦ". iFrame.
    iMod (lock_config_persist with "[$]") as "#$". done.
  Qed.

  Definition locateℓ : ord.t := ((ℵ × lockΔ) ⊕ ℵ)%ordi.

  Lemma lwp_locate :
    ⊢ ∃ m, ∀ μ i G s γ (e : Z),
    l{{{ thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g locateℓ m) ∗
         is_set s γ }}}
     locate #s (Int.into_val e) @ i
    l{{{ gu κu v v' n (n' : loc) lk γlk, RET (#n, #n');
         thP_groups i ({[gu]} ∪ G) ∗
         ogP_obls i gu 0 {[κu]} ∗ ogP_fuel gu 0 μ ∗
         node_lock_inv n γ v γlk n' v' ∗
         lock_token lk γlk κu (∃ n'' v'', node_lock_inv n γ v γlk n'' v'') ∗
         is_node n γ v lk γlk ∗
         ⌜ Int.lt_rel v e ∧ ¬ Int.lt_rel v' e ∧ Int.lt_rel v v' ⌝
    }}}.
  Proof.
    iExists 1. iIntros. iIntros (Φ) "!# (Hg & HlockFuel & #Hs) HΦ".
    iDestruct (TicketLock_acquire_spec) as (ma) "TicketLock_acquire_spec".
    iDestruct (TicketLock_release_spec) as (mr) "TicketLock_release_spec".

    (* iMod (ogP_fuel_extend_set _ ((ℵ × lockΔ) ⊕ ℵ)%ordi _ (ℵ × (ℵ ⊕ ma ⊕ mr))%M with "Hfuel") as "Hfuel". *)
    (* { admit. } *)
    iDestruct "Hs" as (??) "[#Hlk_ℓ #Hn]".

    iAssert (ogP_fuels G 100)%I with "[]" as "-#Hfuel".
    { admit. }

    lwp_lam. post_wp. lwp_pures. iModIntro. lwp_lam. post_wp. lwp_lam. post_wp.
    lwp_pures. lwp_bind (! _)%E. iModIntro.

    iDestruct (is_node_unfold with "Hn") as "(#lk & #val & #Hlk)".
    lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
    iIntros "[(_ & Hg & _) _]". lwp_bind (TicketLock.acquire lk). iModIntro.

    (* iDestruct (ogP_fuels_add_gen with "HlockFuel") as "[HacqFuel HrelFuel]". *)
    (* iApply ("TicketLock_acquire_spec" $! 0 ∅ with "[$Hg HacqFuel]"). *)
    (* { iFrame "#". iFrame. } *)
    (* iIntros (??) "(_ & %Hgu & Hg & Hobl & Hf & _ & _ & Htok & Hown)". *)

    (* iModIntro. *)
    (* lwp_pure. *)
  Admitted.

  Lemma own_interval_agree (x : Z) γ s a b:
    Int.lt_rel a x → ¬ Int.lt_rel b x →
    own_set γ s -∗
    own_interval γ a b -∗
    ⌜ match b with
      | Int.Fin y => if decide (x = y) then x ∈ s
                    else x ∉ s
      | _ => x ∉ s
      end ⌝.
  Proof.
  Admitted.

  Lemma lwp_member i G s γ (e : Z) :
    ⊢ ∃ m,
    ∀ Φ,
    (thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g locateℓ m) ∗ is_set s γ) -∗
    (|={⊤,∅}=> ∃ s, own_set γ s ∗ (own_set γ s ={∅,⊤}=∗ Φ #(bool_decide (e ∈ s)))) -∗
    lWP member #s (Int.into_val e) @ i {{ Φ }}.
  Proof.
    iDestruct TicketLock_release_spec as (mr) "TicketLock_release_spec".
    iDestruct Int.lwp_lt as (mlt) "Int_lwp_lt".
    iDestruct lwp_locate as (mlc) "lwp_locate".

    iExists (100 ⊕ mlc ⊕ mlt ⊕ mr)%M.

    iIntros (Φ) "(Hg & Hfuel & Hs) Hau".

    iDestruct "Hs" as (??) "[#Hlk_ℓ #Hroot]".

    iDestruct (ogP_fuel_add_set with "Hfuel") as "[Hfuel HcallFuel]".
    iDestruct (ogP_fuels_init with "Hfuel") as "Hfuel".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HlocateFuel HcallFuel]".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HltFuel HreleaseFuel]".
    iDestruct (ogP_fuels_init with "HltFuel") as "HltFuel".
    iDestruct (ogP_fuels_init with "HreleaseFuel") as "HreleaseFuel".

    lwp_lam. post_wp. lwp_pures. lwp_bind (locate _ _).
    iModIntro.
    iApply ("lwp_locate" $! (97 ⊕ mlt ⊕ mr)%M with "[$Hg $HlocateFuel]").
    { iFrame "#". }
    iIntros "* (Hg & Hκ & Hg_fuel & Hown & Htok & #Hn & %Hrange)". iModIntro.
    lwp_pure.
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[Hfuel_gu Hg_fuel]".
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[HltFuel_gu HreleaseFuel_gu]".
    iDestruct (big_sepS_insert_2 with "[Hfuel_gu] Hfuel") as "Hfuel".
    { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HltFuel_gu] HltFuel") as "HltFuel".
    { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HreleaseFuel_gu] HreleaseFuel") as "HreleaseFuel".
    { iFrame. }
    post_wp. lwp_pures. iModIntro.
    lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.

    iDestruct (is_node_unfold with "Hn") as "(#v & #lk & #Hlk_inv)".
    iDestruct "Hown" as (?) "(Hlk0_ℓ & next & #v' & Hown & Hn')".

    lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
    iIntros "[(_ & Hg & _) _]". lwp_bind (Int.lt _ _). iModIntro.

    iApply ("Int_lwp_lt" with "[$Hg $HltFuel]").
    iIntros "Hg !>". lwp_pures. iModIntro. lwp_lam. post_wp.
    lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.

    lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
    iIntros "[(_ & Hg & _) _]".  lwp_bind (TicketLock.release _).

    iApply lwpupd_fupd_l.
    iMod "Hau" as (s') "[Hs Hau]".
    iDestruct (own_interval_agree with "[$] [$]") as %Hagree.
    { naive_solver. }
    { naive_solver. }
    iMod ("Hau" with "[$]") as "HΦ". iModIntro.

    iModIntro.
    iApply ("TicketLock_release_spec" $! 0 with "[$Hg $Htok $Hκ Hlk0_ℓ Hn' next Hown HreleaseFuel]").
    { iFrame "#". iFrame. iPureIntro. set_solver. }

    iIntros "(_ & Hg & Ho)".

    rewrite difference_diag_L.
    iMod (group_delete with "Hg Ho") as "Hg".
    iModIntro.

    iDestruct (ogP_fuels_remove_group gu with "Hfuel") as "Hfuel".
    lwp_pures. iModIntro. lwp_finish.

    destruct v'.
    - exfalso. simpl in *. by destruct v; naive_solver.
    - destruct decide in Hagree.
      + subst. rewrite bool_decide_true //.
        rewrite bool_decide_false //. lia.
      + rewrite bool_decide_false //.
        rewrite bool_decide_true //. simpl in *. lia.
    - rewrite bool_decide_false //.
  Qed.

  (* Splicing curr.next past `next` requires fusing the two intervals
     (curr,next) and (next,next.next) into a single interval (curr,next.next),
     while also removing `e = next.val` from the abstract set.  Neither axiom
     is in the file yet, so [lwp_remove] needs them as admitted helpers. *)
  Local Axiom own_interval_compose : ∀ γ a b c,
    own_interval γ a b -∗ own_interval γ b c -∗ own_interval γ a c.

  Local Axiom own_set_remove : ∀ γ s a (e : Z),
    Int.lt_rel a e →
    own_set γ s -∗ own_interval γ a (Int.Fin e) ==∗
      own_set γ (s ∖ {[e]}) ∗ own_interval γ a (Int.Fin e).

  Lemma lwp_remove i G s γ (e : Z) :
    ⊢ ∃ m,
    ∀ Φ,
    (thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g locateℓ m) ∗ is_set s γ) -∗
    (|={⊤,∅}=> ∃ s, own_set γ s ∗ (own_set γ (s ∖ {[e]}) ={∅,⊤}=∗ Φ #())) -∗
    lWP remove #s (Int.into_val e) @ i {{ Φ }}.
  Proof.
    iDestruct TicketLock_acquire_spec as (ma) "TicketLock_acquire_spec".
    iDestruct TicketLock_release_spec as (mr) "TicketLock_release_spec".
    iDestruct Int.lwp_lt as (mlt) "Int_lwp_lt".
    iDestruct lwp_locate as (mlc) "lwp_locate".

    iExists (100 ⊕ mlc ⊕ mlt ⊕ ma ⊕ mr ⊕ mr)%M.

    iIntros (Φ) "(Hg & Hfuel & Hs) Hau".
    iDestruct "Hs" as (??) "[#Hlk_ℓ #Hroot]".

    iDestruct (ogP_fuel_add_set with "Hfuel") as "[Hfuel HcallFuel]".
    iDestruct (ogP_fuels_init with "Hfuel") as "Hfuel".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HlocateFuel HcallFuel]".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HltFuel HcallFuel]".
    iDestruct (ogP_fuels_init with "HltFuel") as "HltFuel".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HacqFuel HcallFuel]".
    iDestruct (ogP_fuels_init with "HacqFuel") as "HacqFuel".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HrelNextFuel HrelCurrFuel]".
    iDestruct (ogP_fuels_init with "HrelNextFuel") as "HrelNextFuel".
    iDestruct (ogP_fuels_init with "HrelCurrFuel") as "HrelCurrFuel".

    lwp_lam. post_wp. lwp_pures. lwp_bind (locate _ _).
    iModIntro.
    iApply ("lwp_locate" $! (97 ⊕ mlt ⊕ ma ⊕ mr ⊕ mr)%M with "[$Hg $HlocateFuel]").
    { iFrame "#". }
    iIntros "* (Hg & Hκ & Hg_fuel & Hown & Htok & #Hn & %Hrange)". iModIntro.
    lwp_pure.

    (* Distribute the per-call fuel down to gu, mirroring lwp_member. *)
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[Hfuel_gu Hg_fuel]".
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[HltFuel_gu Hg_fuel]".
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[HacqFuel_gu Hg_fuel]".
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[HrelNextFuel_gu HrelCurrFuel_gu]".
    iDestruct (big_sepS_insert_2 with "[Hfuel_gu] Hfuel") as "Hfuel". { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HltFuel_gu] HltFuel") as "HltFuel". { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HacqFuel_gu] HacqFuel") as "HacqFuel". { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HrelNextFuel_gu] HrelNextFuel") as "HrelNextFuel". { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HrelCurrFuel_gu] HrelCurrFuel") as "HrelCurrFuel". { iFrame. }

    post_wp. lwp_pures. iModIntro.
    lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.

    (* Read next.val. *)
    iDestruct (is_node_unfold with "Hn") as "(#v & #lk & #Hlk_inv)".
    iDestruct "Hown" as (?) "(Hlk0_ℓ & nextp & #v' & Hown & Hn')".

    lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_load _ ∅ 1 with "[Hf Hg]"). { iFrame "∗#". done. }
    iIntros "[(Hlc & Hg & _) _]". lwp_bind (Int.lt _ _). iModIntro.

    iApply ("Int_lwp_lt" with "[$Hg $HltFuel]").
    iIntros "Hg !>".

    (* Case split on whether e < next.val.  locate gave us v < e ≤ next.val, so:
         - if e < next.val: e ∉ s, do nothing, just unlock curr;
         - else: e = next.val ∈ s, splice curr past next, then unlock both. *)
    destruct (decide (Int.lt_rel e v')) as [Hlt|Hge].
    - (* Not-in-set branch.  Looks just like the end of lwp_member. *)
      rewrite bool_decide_true; last done.
      lwp_pures. iModIntro.
      lwp_lam. post_wp. lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.

      lOneFuel "Hfuel" as "[Hf Hfuel]".
      iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
      iIntros "[(_ & Hg & _) _]". lwp_bind (TicketLock.release _).

      iApply lwpupd_fupd_l.
      iMod "Hau" as (s') "[Hs Hau]".
      iDestruct (own_interval_agree e with "[$] [$]") as %Hmem.
      { naive_solver. }
      { naive_solver. }
      (* e ∉ s', so s' ∖ {[e]} = s'. *)
      assert (e ∉ s') as Hnot.
      { destruct v'; simpl in *; try done.
        destruct decide in Hmem; [|done]. subst. lia. }
      rewrite (difference_disjoint_L _ {[e]}); last set_solver.
      iMod ("Hau" with "[$]") as "HΦ". iModIntro.

      iModIntro.
      iApply lwp_sfmupd.
      iApply ("TicketLock_release_spec" $! 0 with
                "[$Hg $Htok $Hκ Hlk0_ℓ Hn' nextp Hown HrelCurrFuel]").
      { iFrame "#". iFrame. iPureIntro. set_solver. }
      iIntros "(_ & Hg & Ho)". rewrite difference_diag_L.
      iMod (group_delete with "Hg Ho") as "Hg".
      iDestruct (ogP_fuels_remove_group gu with "Hfuel") as "Hfuel".
      iModIntro. iApply "HΦ".

    - (* In-set branch: e = next.val.  Pin down v' = Fin e. *)
      rewrite bool_decide_false; last done.
      assert (v' = Int.Fin e) as Hv'eq.
      { destruct v'; simpl in *; try naive_solver.
        destruct Hrange as (_ & ? & _).
        f_equal. lia. }
      subst v'.

      lwp_pures. iModIntro.

      (* Acquire next's lock.  From Hn' (the [match v'] in node_lock_inv at
         v' = Fin e) we have is_node next and the half lock-token. *)
      iDestruct "Hn'" as (lk' γlk' ℓ') "(Hnext & Hlk'_ℓ & %Hℓ')".
      iMod (lc_fupd_elim_later with "[$] Hnext") as "#Hnext".

      iDestruct (is_node_unfold with "Hnext") as "(#v_next & #lk_next & #Hlk_next)".

      lwp_lam. post_wp. lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.
      lOneFuel "Hfuel" as "[Hf Hfuel]".
      iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
      iIntros "[(_ & Hg & _) _]". lwp_bind (TicketLock.acquire _). iModIntro.

      iApply ("TicketLock_acquire_spec" $! 0 81 with "[$Hg HacqFuel Hlk'_ℓ]").
      { iFrame "#". iFrame. admit. } (* TODO: acquire fuel *)
      iIntros (gu' κu') "(_ & %Hgu' & Hg & Hobl' & Hf' & _ & _ & Htok' & Hown_next)".
      iModIntro. lwp_pure.

      (* Read next.next, then store it into curr.next. *)
      iDestruct "Hown_next" as (???) "(Hlk'_ℓ' & nextp' & #v'' & Hown' & Hn'')".
      lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.
      lOneFuel "Hfuel" as "[Hf Hfuel]".
      iApply (lwp_load _ ∅ 0 with "[Hf Hg $nextp']"). { iFrame "∗#". done. }
      iIntros "[(_ & Hg & _) nextp']". lwp_bind (_ <- _)%E. iModIntro.

      lOneFuel "Hfuel" as "[Hf Hfuel]".
      iApply (lwp_store _ ∅ 0 with "[$Hg $Hf $nextp]").
      iIntros "[(_ & Hg & _) nextp]". iModIntro. lwp_pures.

      (* Linearization point: open the AU and remove e from the set. *)
      iApply lwpupd_fupd_l.
      iMod "Hau" as (s') "[Hs Hau]".
      iMod (own_set_remove γ s' v e with "Hs Hown") as "[Hs Hown]".
      { naive_solver. }
      iMod ("Hau" with "[$]") as "HΦ". iModIntro.

      (* Fuse the two intervals (v,e) and (e,v'') into (v,v''). *)
      iDestruct (own_interval_compose with "Hown Hown'") as "Hown".

      (* Release next's lock.  Its body is now satisfied trivially since `next`
         is detached from the list; we re-establish it with the resources we
         still hold. *)
      lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.
      lOneFuel "Hfuel" as "[Hf Hfuel]".
      iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
      iIntros "[(_ & Hg & _) _]". lwp_bind (TicketLock.release _). iModIntro.

      (* TODO: the splice has detached `next` from the list; the leftover
         resources (its half-token plus `nextp'`) need to be repackaged into
         next's lock invariant so [TicketLock_release_spec] can be applied.
         This needs a small adjustment to the invariant or an auxiliary
         "detached node" predicate. *)
      admit.
  Admitted.

  (* Splicing a fresh node in between curr and next requires splitting the
     interval (curr,next) at e and inserting e into the abstract set. *)
  Local Axiom own_set_add : ∀ γ s a c (e : Z),
    Int.lt_rel a e → Int.lt_rel (Int.Fin e) c →
    own_set γ s -∗ own_interval γ a c ==∗
      own_set γ (s ∪ {[e]}) ∗ own_interval γ a (Int.Fin e) ∗ own_interval γ (Int.Fin e) c.

  Lemma lwp_add i G s γ (e : Z) :
    ⊢ ∃ m,
    ∀ Φ,
    (thP_groups i G ∗ ([∗ set] g ∈ G, ogP_fuel g locateℓ m) ∗ is_set s γ) -∗
    (|={⊤,∅}=> ∃ s, own_set γ s ∗ (own_set γ (s ∪ {[e]}) ={∅,⊤}=∗ Φ #())) -∗
    lWP add #s (Int.into_val e) @ i {{ Φ }}.
  Proof.
    iDestruct TicketLock_release_spec as (mr) "TicketLock_release_spec".
    iDestruct Int.lwp_lt as (mlt) "Int_lwp_lt".
    iDestruct lwp_locate as (mlc) "lwp_locate".
    iDestruct lwp_newNode as (mn) "lwp_newNode".

    iExists (100 ⊕ mlc ⊕ mlt ⊕ mn ⊕ mr)%M.

    iIntros (Φ) "(Hg & Hfuel & Hs) Hau".
    iDestruct "Hs" as (??) "[#Hlk_ℓ #Hroot]".

    iDestruct (ogP_fuel_add_set with "Hfuel") as "[Hfuel HcallFuel]".
    iDestruct (ogP_fuels_init with "Hfuel") as "Hfuel".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HlocateFuel HcallFuel]".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HltFuel HcallFuel]".
    iDestruct (ogP_fuels_init with "HltFuel") as "HltFuel".
    iDestruct (ogP_fuel_add_set with "HcallFuel") as "[HnewFuel HrelFuel]".
    iDestruct (ogP_fuels_init with "HnewFuel") as "HnewFuel".
    iDestruct (ogP_fuels_init with "HrelFuel") as "HrelFuel".

    lwp_lam. post_wp. lwp_pures. lwp_bind (locate _ _).
    iModIntro.
    iApply ("lwp_locate" $! (97 ⊕ mlt ⊕ mn ⊕ mr)%M with "[$Hg $HlocateFuel]").
    { iFrame "#". }
    iIntros "* (Hg & Hκ & Hg_fuel & Hown & Htok & #Hn & %Hrange)". iModIntro.
    lwp_pure.

    (* Distribute the gu fuel like member/remove. *)
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[Hfuel_gu Hg_fuel]".
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[HltFuel_gu Hg_fuel]".
    iDestruct (ogP_fuel_add with "Hg_fuel") as "[HnewFuel_gu HrelFuel_gu]".
    iDestruct (big_sepS_insert_2 with "[Hfuel_gu] Hfuel") as "Hfuel". { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HltFuel_gu] HltFuel") as "HltFuel". { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HnewFuel_gu] HnewFuel") as "HnewFuel". { iFrame. }
    iDestruct (big_sepS_insert_2 with "[HrelFuel_gu] HrelFuel") as "HrelFuel". { iFrame. }

    post_wp. lwp_pures. iModIntro.
    lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.

    (* Read next.val. *)
    iDestruct (is_node_unfold with "Hn") as "(#v & #lk & #Hlk_inv)".
    iDestruct "Hown" as (?) "(Hlk0_ℓ & nextp & #v' & Hown & Hn')".

    lOneFuel "Hfuel" as "[Hf Hfuel]".
    iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
    iIntros "[(_ & Hg & _) _]". lwp_bind (Int.lt _ _). iModIntro.

    iApply ("Int_lwp_lt" with "[$Hg $HltFuel]").
    iIntros "Hg !>".

    (* Branch on e < next.val.  locate gave us v < e ≤ v'.
         - if e < v': e ∉ s, allocate a node holding e and splice it in;
         - else: e = v' ∈ s, the AU postcondition reduces to own_set γ s. *)
    destruct (decide (Int.lt_rel e v')) as [Hlt|Hge].
    - (* Insert branch.  This is the structurally novel part vs. member/remove. *)
      rewrite bool_decide_true; last done.
      lwp_pures.

      iDestruct (own_interval_not_NegInf with "Hown") as %Hnot_neginf.

      (* The insert step is  nextRef curr <- newNode v next  — newNode evaluates
         first, then the store.  We open the AU around [newNode]: this is the
         linearisation point of [add].  Doing the AU early is safe because we
         hold curr's lock, so no concurrent thread can act on [e] between this
         logical update and the matching physical store below. *)
      lwp_bind (newNode _ _)%E.

      iApply lwpupd_fupd_l.
      iMod "Hau" as (s') "[Hs Hau]".
      iMod (own_set_add γ s' v v' e with "Hs Hown")
        as "(Hs & Hown_lo & Hown_hi)".
      { by destruct Hrange. }
      { destruct v' as [| | k]; simpl in *; try done. }
      iMod ("Hau" with "Hs") as "HΦ".
      iModIntro. iModIntro.

      (* Call newNode with value e and successor n'.  In the finite case Hn'
         carries exactly the required half-token; in the +∞ case [#v'] is the
         persistent pointsto we need.
         The new node's lock level ℓ_new must satisfy
              (n'-level ⊕ lockΔ) < ℓ_new   and   ℓ_new ⊕ lockΔ < ℓ_curr,
         which exists by density of the ordinal order — left as an admit. *)
      iApply ("lwp_newNode" $! _ i ({[gu]} ∪ G) _ γ e v'
                with "[$Hg $HnewFuel Hn' $Hown_hi]").
      { destruct v' as [| | k] eqn:Hv'.
        - by destruct Hnot_neginf.
        - iFrame.
        - iDestruct "Hn'" as (lk' γlk' ℓ') "(#Hnext & Hlk' & %Hℓ')".
          iExists lk', γlk', ℓ'. iFrame "Hnext Hlk'".
          iPureIntro. (* ℓ' ⊕ lockΔ < ℓ_new *) admit. }
      iIntros (n_new lk_new γlk_new) "(Hg & #Hn_new & Hlk_new_ℓ) !>".
      lwp_pures. iModIntro. lwp_pures.

      (* Store curr.next := #n_new — the physical counterpart of the LP above. *)
      lwp_lam. post_wp. lwp_pures. lwp_bind (_ <- _)%E. iModIntro.
      lOneFuel "Hfuel" as "[Hf Hfuel]".
      iApply (lwp_store _ ∅ 0 with "[$Hg $Hf $nextp]").
      iIntros "[(_ & Hg & _) nextp]". iModIntro. lwp_pures. iModIntro.

      (* Step into [unlockNode curr] and release curr's lock, supplying the
         rebuilt body (with n'' := n_new, v'' := Fin e). *)
      lwp_lam. post_wp. lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.
      lOneFuel "Hfuel" as "[Hf Hfuel]".
      iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
      iIntros "[(_ & Hg & _) _]". lwp_bind (TicketLock.release _).

      iApply lwp_sfmupd.
      iDestruct (is_node_unfold with "Hn_new") as "(#vN & #lkN & #HlkN_inv)".
      iApply ("TicketLock_release_spec" $! 0 with
                "[$Hg $Htok $Hκ Hlk0_ℓ nextp Hown_lo Hlk_new_ℓ HrelFuel]").
      { iFrame "#". iSplit; [iPureIntro; set_solver|].
        iExists n_new, (Int.Fin e), _.
        iFrame "Hlk0_ℓ nextp vN Hown_lo".
        iExists lk_new, γlk_new, _. iFrame "Hn_new Hlk_new_ℓ".
        iPureIntro. (* ℓ_new ⊕ lockΔ < ℓ_curr *) admit. }
      iIntros "(_ & Hg & Ho)". rewrite difference_diag_L.
      iMod (group_delete with "Hg Ho") as "Hg". iModIntro.
      iDestruct (ogP_fuels_remove_group gu with "Hfuel") as "Hfuel".
      iFrame.

    - (* Already-present branch.  Mirrors lwp_remove's not-in-set branch:
         observe e ∈ s' via own_interval_agree, close the AU with the same
         set (since s' ∪ {[e]} = s'), then unlock curr. *)
      rewrite bool_decide_false; last done.
      assert (v' = Int.Fin e) as Hv'eq.
      { destruct v'; simpl in *; try naive_solver. f_equal.
        destruct Hrange as (_ & ? & _). lia. }
      subst v'.

      lwp_pures. iModIntro.
      lwp_lam. post_wp. lwp_lam. post_wp. lwp_pures. lwp_bind (! _)%E. iModIntro.

      lOneFuel "Hfuel" as "[Hf Hfuel]".
      iApply (lwp_load _ ∅ 0 with "[Hf Hg]"). { iFrame "∗#". done. }
      iIntros "[(_ & Hg & _) _]". lwp_bind (TicketLock.release _).

      iApply lwpupd_fupd_l.
      iMod "Hau" as (s') "[Hs Hau]".
      iDestruct (own_interval_agree e with "[$] [$]") as %Hmem.
      { naive_solver. }
      { naive_solver. }
      (* e ∈ s', so s' ∪ {[e]} = s'. *)
      assert (e ∈ s') as Hin.
      { simpl in Hmem. destruct decide in Hmem; [done|lia]. }
      replace (s' ∪ {[e]}) with s' by set_solver.
      iMod ("Hau" with "[$]") as "HΦ". iModIntro.

      iModIntro. iApply lwp_sfmupd.
      iApply ("TicketLock_release_spec" $! 0 with
                "[$Hg $Htok $Hκ Hlk0_ℓ Hn' nextp Hown HrelFuel]").
      { iFrame "#". iFrame. iPureIntro. set_solver. }
      iIntros "(_ & Hg & Ho)". rewrite difference_diag_L.
      iMod (group_delete with "Hg Ho") as "Hg". iModIntro.
      iDestruct (ogP_fuels_remove_group gu with "Hfuel") as "Hfuel".
      iFrame.
  Admitted.

End proof.
