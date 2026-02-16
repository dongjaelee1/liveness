From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export weakestpre.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

(* From liris.heap_lang.lib Require Import par. *)

Definition writer : val :=
  λ: "l", "l" <- #1;;
          Exit #().

Definition reader : val := 
  rec: "reader" "l" :=
    let: "n" := !"l" in
    if: "n" = #1
    then Exit #()
    else "reader" "l".

Section mp_proof.
  Context `{!heapGS Σ}.
  Let N := nroot .@ "message_passing".

  Let ℓs : layers := (λ _, 0).

  Definition mp_proto (k : gl_id) (v : ghost_lock_version) (l : loc) : iProp Σ :=
    gl_layers k ℓs ∗ gl k v ∗ wit_layer k v 0 ∗
    gl_variant N k v (l ↦ #0) (l ↦ #1) (False).

  Definition mp (k : gl_id) (l : loc) : iProp Σ :=
    mp_proto k 0 l.

  (** The main proofs. *)
  Global Instance mp_proto_persistent k v l : Persistent (mp_proto k v l).
  Proof. apply _. Qed.
  Global Instance mp_persistent k l : Persistent (mp k l).
  Proof. apply _. Qed.

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
    { iModIntro. rewrite insert_empty dom_singleton_L big_sepS_singleton. iFrame. }
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
    { rewrite insert_empty dom_singleton_L big_sepS_singleton. iFrame. done. }
    iIntros "[(_& Tx& TG& _) ptl]".
    iPoseProof ("ACC" with "TG Glk") as "ACC".
    iMod ("ACC" $! _) as "((TG& Gc& #Gd)& ACC)".
    iModIntro. iMod ("ACC" with "ptl") as "_". iModIntro.
    (* simpl. *)
    lwp_pure.
    simpl. iFrame "Tx". iExists ⊤, ∅, ∅, 0. iSplitR; first done. iModIntro. iSplitL "TG".
    { rewrite delete_insert_id; auto. }
    iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
    lwp_pure.
    simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
    iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
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
    iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
    lwp_bind (Load _).
    iMod (gl_variant_acc with "GVkv") as "[>PQR ACC]". 1: set_solver.
    iDestruct "PQR" as "[[HP | HQ] | HR]"; cycle -1.
    { iDestruct "HR" as "[_ %]". done. }
    - iDestruct "HP" as "[Glk ptr]".
      iApply (lwp_load _ (<[k:=0]>∅) 0 with "[$ptr $Tx $TG]").
      { rewrite big_sepM_singleton dom_empty_L. iSplitR; first done. auto. }
      iIntros "[(_& Tx& TG& Rs) ptr]".
      rewrite big_sepM_singleton. iDestruct "Rs" as "[Wck | #Gdk]"; cycle 1.
      { iPoseProof (gl_locked_done_false with "Glk Gdk") as "%". done. }
      iMod ("ACC" with "[Glk ptr]") as "_".
      { iModIntro. iApply gl_variant_cases_unfold. iLeft. iLeft. iFrame. }
      iModIntro.
      lwp_let. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
      lwp_lam. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
      lwp_op. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
      lwp_if. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
      iMod (wit_fuels_decr with "Wkvfs Wck") as "(%& %LTα& #Wkvfs'& _)".
      iApply (IHα α0 LTα). iFrame. iModIntro. auto.
    - iDestruct "HQ" as "[#Gdk ptr]".
      iApply (lwp_load _ ∅ 0 with "[$ptr $Tx $TG]").
      { rewrite dom_empty_L. iSplit; done. }
      iIntros "[(_& Tx& TG& _) ptr]".
      iMod ("ACC" with "[ptr]") as "_".
      { iModIntro. iApply gl_variant_cases_unfold. iLeft. iRight. iFrame. auto. }
      iModIntro.
      lwp_let. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
      lwp_lam. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
      lwp_op. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
      lwp_if. simpl. iFrame "Tx TG". iExists ⊤, ∅, 0. iSplitR; first done. iModIntro.
      iSplitR; first by rewrite dom_empty_L. iIntros "Tx TG _ !> _ !>".
      iApply (lwp_exit with "TG Tx [HΦ]").
      iModIntro. iIntros "#Tt1 #Tt2". iIntros "!>".
      iApply "HΦ". rewrite /lift_term. iFrame "Tt1".
      rewrite -thread_term_unfold. auto.
  Qed.

  Lemma mp_pre i l E G q :
    th_obls i G q ∗ l ↦ #0
    ⊢ |={E}=>g ∃ k, ⌜ G !! k = None ⌝ ∗ th_obls i (<[k:=0]>G) q ∗ gl_current k 0 (1/2)%Qp ∗ gl_fuel k 0 10 ∗ mp k l.
  Proof.
    rewrite /mp /mp_proto. iIntros "[TG ptr]".
    iMod (gl_alloc_obl _ _ _ _ ℓs 10 N 0 (l ↦ #0) with "TG ptr") as "(%& %& TG& Gc& #Gwf& #Gl& Gf& #GV& #Wit& _)".
    iFrame "Gwf Gl GV Wit". iFrame. auto.
  Qed.

End mp_proof.
