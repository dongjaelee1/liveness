From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export weakestpre.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic Require Import lib.token.

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

(** The CMRA we need. *)
Class ticket_lockG Σ := TLockG { #[local] tlock_tokG :: tokenG Σ }.

Definition ticket_lockΣ : gFunctors := #[tokenΣ].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Let N := nroot .@ "ticket_lock".

  Local Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    ∃ b : bool, l ↦ #b ∗ if b then True else token γ ∗ R.

  (* lks = (next, curr) *)
  Local Definition is_lock (γ : gname) (lks : val) (R : iProp Σ) : iProp Σ :=
    ∃ l: loc, ⌜lks = (#l, #l)%V⌝ ∧ inv N (lock_inv γ l R).

  Local Definition locked (γ : gname) : iProp Σ := token γ.

  Local Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" gives %?. Qed.

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
