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
    λ: "next" "curr",
      let: "my_ticket" := FAA "next" #1 in
      let: "try_lock" :=
        (rec: "while" <> := if: !"curr" = "my_ticket"
                           then #()
                           else "while"
        ) in
      "try_lock".

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

  Local Definition lock_state k ℓ (curr : loc) (c : Z) : iProp Σ :=
    gl k (Z.to_nat c) ∗
    wit_layer k (Z.to_nat c) (ℓ)%ordi ∗
    gl_variant N_state k (Z.to_nat c) (curr ↦ #(c - 1)%Z) (curr ↦ #c) True.

  Local Definition lock_eventually_held k γh ℓ (my : Z) : iProp Σ :=
    gl k 0 ∗
    wit_layer k 0 (ℓ ⊕ (Z.to_nat my))%ordi ∗
    gl_variant N_held k 0 (my ↪[γh]{#(1/2)} false) (my ↪[γh]□ true) False.

  Local Definition lock_inv (next curr : loc) (γh γd : gname) (κl : gl_id) (ℓ : layer) (R : iProp Σ) : iProp Σ :=
    ∃ (n c : Z) (held : gmap Z bool) (data : gmap Z tl_data),
      (⌜ (c <= n)%Z ⌝) ∗
      (⌜ ∀ (x : Z), (n <= x)%Z ↔ held !! x = None ⌝) ∗
      (⌜ ∀ (x : Z), (x < c)%Z → held !! x = Some true ⌝) ∗
      (⌜ dom held = dom data ⌝) ∗
      gl_layers κl (λ v, (ℓ)%ordi) ∗
      next ↦ #n ∗
      ghost_map_auth γh 1 held ∗
      ghost_map_auth γd 1 data ∗
      (match held !! c with
       | None =>
           gl_done κl (Z.to_nat c) ∗
           gl_current κl (Z.to_nat c) ∗
           lock_state κl ℓ curr c ∗
           R
       | Some false =>
           gl_done κl (Z.to_nat c) ∗
           gl_current κl (Z.to_nat c) ∗
           lock_state κl ℓ curr c ∗
           R
       | Some true =>
           lock_state κl ℓ curr (c + 1)
       end) ∗
      ([∗ map] x ↦ h ∈ held,
         ∃ κx, x ↪[γd]□ κx ∗
               lock_eventually_held κx γh ℓ x ∗
               match h with
               | false => (x ↪[γh]{#(1/2)} false)
               | true => (x ↪[γh]□ true)
               end
      ).

  Local Definition is_fair_lock (lnc : val) (γh γd : gname) (κl : gl_id) (ℓ : layer) (R : iProp Σ) : iProp Σ :=
    ∃ (next curr : loc), ⌜lnc = (#next, #curr)%V⌝ ∧
                         inv N_inv (lock_inv next curr γh γd κl ℓ R).


  TODO: pers, timeless, etc..

  Local Lemma init_spec i q G (R : iProp Σ) :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ([∗ map] k ↦ v ∈ G, gl_fuel k 1 ▽%M) ∗
         R }}}
      TicketLock.init #() @ i
    l{{{ lks γ, RET lks; thread_exec i q ∗ th_obls i G 1 ∗
                       is_lock γ lks R }}}.
  Proof.
  Abort.

  (** FIXME: ordi notation levels *)
  Local Lemma acquire_spec i q G ℓ μ γ lk R :
    l{{{ thread_exec i q ∗
         th_obls i G 1 ∗ ([∗ map] k ↦ v ∈ G, ∃ l, ⌜ ((ℓ ⊕ ω) < l)%ordi ⌝ ∗ gl_fuel k l ▽%M) ∗
         is_lock γ lk R }}}
      TicketLock.acquire lk @ i
    l{{{ κu ν, RET #(); thread_exec i q ∗
                        th_obls i (<[κu:=ν]>G) 1 ∗ ⌜ G !! κu = None ⌝ ∗
                        gl_fuel κu ℓ μ ∗
                        locked γ ∗ R }}}.
  Proof.
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
