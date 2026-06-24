From iris.proofmode Require Import proofmode.
From liris.base_logic Require Export invariants.
From liris.program_logic Require Export temporal_logic.
From liris.heap_lang Require Export lang.
From liris.heap_lang Require Import notation.
From liris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_var.

Module Handover.

  (** Put x at buffer b *)
  Definition send : val :=
    λ: "b" "f" "a", "b" <- SOME ("f", "a").

  (** Checks until the buffer b contains SOME x *)
  Definition receive : val := 
    rec: "wait" "b" :=
      match: !"b" with
        NONE => "wait" "b"
      | SOME "x" => (Fst "x") (Snd "x")
      end.

End Handover.

(** The CMRA we need. *)
Class handoverGpreS (Σ : gFunctors) : Set :=
  HandoverGpreS {
      #[local] handoverGpreS_data_inG :: ghost_varG Σ (ocid);
    }.

Class handoverG Σ :=
  HandoverG {
      #[local] handover_inG :: handoverGpreS Σ;
    }.

Definition handoverΣ : gFunctors :=
    #[ghost_varΣ (ocid)].

Global Instance subG_handoverΣ {Σ} : subG handoverΣ Σ → handoverGpreS Σ.
Proof. solve_inG. Qed.

Record handover_γ :=
  HandoverName {
      handover_γd : gname;
    }.

(* Local Existing Instances handover_inG handoverGpreS_data_inG. *)

Section proof.
  Context `{!heapGS Σ, !handoverG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let N := nroot.@ "handover".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".

  Remark N_disj_1 : Na ## Np.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑Np ⊆ (⊤ : coPset) ∖ ↑Na.
  Proof. pose proof N_disj_1. set_solver. Qed.

  (** ** Definitions *)
  Definition is_task (ℓ : ord.t) : val → val → oids → iProp Σ :=
    λ f a K, (∃ ℓt (P : iProp Σ),
               ⌜(ℓt < ℓ)%ordi⌝ ∧
               P ∗
               ∃ μ, ∀ lc i G g K' ℓg,
               l{{{ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g ℓt μ) ∗
                    crP_obls g ℓg K' ∗ ⌜ K ⊆ K' ⌝ ∗ P }}}
                f a @ i
              l{{{ rv, RET rv; £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K' ∖ K) }}})%I.

  Definition handover_inv (b : loc) γd ℓ : iProp Σ :=
    ∃ g, (b ↦{#(1/2)} NONEV ∗ ghost_var γd (1/2)%Qp g ∗ crP_obls g ℓ ∅) ∨
           (∃ (f a : val) K, b ↦ SOMEV (f, a) ∗ ghost_var γd (1/2)%Qp (g) ∗
                             crP_obls g ℓ K ∗ is_task ℓ f a K) ∨
           (∃ (f a : val), b ↦ SOMEV (f, a) ∗ ghost_var γd (1)%Qp g).

  Definition is_handover (b : loc) (γ : handover_γ) ℓ : iProp Σ :=
    ⟦alwaysP Na (⟨handover_inv b (handover_γd γ) ℓ⟩)⟧ₗ.

  (** The main proofs. *)
  Global Instance handover_inv_persistent b γ ℓ : Persistent (is_handover b γ ℓ).
  Proof. rewrite /is_handover. tf_red. apply _. Qed.

  Lemma is_handover_initialize E b ℓ g :
     b ↦{#(1/2)} NONEV -∗ crP_obls g ℓ ∅
    ={E}=∗ ∃ γ, is_handover b γ ℓ ∗ ghost_var (handover_γd γ) (1/2)%Qp g.
  Proof.
    iIntros "Ptr Co".
    iMod (ghost_var_alloc g) as "(%& [Gv Gv0])".
    iExists (HandoverName γ). iFrame "Gv0".
    rewrite /is_handover. simpl.
    iMod (inv_alloc Na _ (handover_inv b γ ℓ) with "[Ptr Co Gv]") as "#Inv".
    { iNext. rewrite /handover_inv. iExists g. iLeft. iFrame. }
    eauto.
  Qed.

  Lemma Handover_send_spec :
    ⊢ ∃ μ, ∀ lc i (b : loc) (f a : val) G g K K' γ ℓ ℓg,
    l{{{ thP_carriers i G ∗ ([∗ set] g ∈ G, ∃ ℓ, crP_fuel g ℓ μ) ∗
         crP_obls g ℓg K' ∗ ⌜ K ⊆ K' ⌝ ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ%ordi 1) ∗
         b ↦{#(1/2)} NONEV ∗
         is_task ℓ f a K ∗ is_handover b γ ℓ }}}
      Handover.send #b f a @ i
    l{{{ RET #(); £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K' ∖ K) }}}.
  Proof.
    iExists 20. iIntros (lc i b f a G g K K' γ ℓ ℓg Φ) "!> HP HΦ".
    iDestruct "HP" as "(TG& GF& Cg& %SubK& OFK& Ptrb& is_task& #handover_inv)".
    rewrite /is_handover. iEval (do 2 tf_red) in "handover_inv".
    rewrite /Handover.send.
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_pures.
    lwp_bind (Store _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iInv "handover_inv" as "inv".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "(%& [inv | [inv | inv]])".
    - iDestruct "inv" as "(Ptrb0& Gv& Cg0)".
      iApply lwp_sfmupd.
      iCombine "Ptrb Ptrb0" as "Ptrb".
      iApply (lwp_store _ ∅ 0 with "[$Ptrb $TG $GF1]"). 1: done.
      iIntros "((_& TG& _)& Ptrb)".
      iMod (obl_offload_set with "Cg Cg0 OFK") as "(Cg& Cg0& %DisjK)". 1: auto. 1: done.
      rewrite union_empty_l_L. iModIntro. iModIntro. iSplitR "HΦ Q_LC TG Cg".
      { iNext. iExists _. iRight. iLeft. iFrame. }
      iApply "HΦ". iFrame.
    - iDestruct "inv" as "(%&%&%& Ptrb0& _)". iCombine "Ptrb Ptrb0" gives %?. destruct H. done.
    - iDestruct "inv" as "(%&%& Ptrb0& _)". iCombine "Ptrb Ptrb0" gives %?. destruct H. done.
  Qed.

  Lemma Handover_receive_spec :
    ⊢ ∃ μ, ∀ lc i b G g γ ℓ,
    l{{{ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g ℓ μ) ∗
         ⌜G = {[g]}⌝ ∗ ghost_var (handover_γd γ) (1/2)%Qp g ∗
         is_handover b γ ℓ }}}
      Handover.receive #b @ i
    l{{{ v, RET v; £ lc ∗ thP_carriers i ∅ }}}.
  Proof.
    (** For internal steps and executing run_task *)
    iExists (10 ⊕ 1)%M. iIntros (lc i b G g γ ℓ Φ) "!> HP HΦ".
    iDestruct "HP" as "(TG& GF& %EQg& Gv& #handover_inv)".
    rewrite /Handover.receive.
    iPoseProof (crP_fuel_add_set with "GF") as "[GF F_task]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    (** Lob (co-)induction *)
    iRevert (g G EQg) "TG GF Gv F_task". iLöb as "IH". iIntros (g G EQg) "TG GF Gv F_task".
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_bind (Load _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    (** Cases. *)
    rewrite /is_handover. iEval (do 2 tf_red) in "handover_inv".
    iInv "handover_inv" as "inv".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "(%& [inv | [inv | inv]])".
    - iDestruct "inv" as "(Ptrb& Gv0& Cg)".
      iApply lwp_sfmupd.
      iApply (lwp_load _ ∅ 0 with "[$Ptrb $TG $GF1]"). 1: done.
      iIntros "((_& TG& _)& Ptrb)".
      iCombine "Gv Gv0" gives %H. destruct H as [_ <-]. subst.
      iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
      replace ({[g]} ∖ {[g]}) with (∅ : gset ocid) by set_solver.
      iMod (carrier_alloc _ _ _ ℓ (15 ⊕ 1)%M with "TG") as "(%g'& _& TG& Cg'& Gf)".
      iMod (ghost_var_update_2 g' with "Gv Gv0") as "(Gv& Gv0)". 1: by rewrite Qp.div_2.
      iClear "F_task GF". clear g.
      rewrite union_empty_r_L.
      iAssert ([∗ set] g ∈ {[g']}, crP_fuel g (ℓ)%ordi _)%I with "[Gf]" as "GF".
      { iApply big_sepS_singleton. iFrame. }      
      iPoseProof (crP_fuel_add_set with "GF") as "[GF F_task]".
      iPoseProof (crP_fuels_init with "GF") as "GF".
      iModIntro. iModIntro. iSplitL "Ptrb Gv0 Cg'".
      { iNext. iExists _. iLeft. iFrame. }
      do 3 (iModIntro; lwp_pure_one).
      iPoseProof (crP_fuels_add 2 with "GF") as "[_ GF]".
      iModIntro. iApply ("IH" with "HΦ [] TG GF Gv F_task"). done.
    - iDestruct "inv" as "(%&%&%& Ptrb& Gv0& Cg& is_task)".
      iApply (lwp_load _ ∅ 0 with "[$Ptrb $TG $GF1]"). 1: done.
      iIntros "((_& TG& _)& Ptrb)".
      iCombine "Gv Gv0" as "Gv" gives %H. destruct H as [_ <-]. subst.
      iModIntro. iSplitL "Ptrb Gv".
      { iNext. iExists _. iRight. iRight. iFrame. }
      lwp_pures.
      lwp_bind (f a).
      iDestruct "is_task" as "(%&%& %Hlt& HP& %& task)".
      iModIntro.
      iMod (crP_fuel_extend_set _ ℓt _ μ with "F_task") as "F_task". 1: eauto.
      iApply lwp_sfmupd.
      iApply ("task" $! 0 with "[$TG $F_task $Cg $HP]"). 1: eauto.
      iIntros (?) "(_& TG& Cg)". replace (K ∖ K) with (∅ : gset ocid) by set_solver.
      iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
      replace ({[g]} ∖ {[g]}) with (∅ : gset ocid) by set_solver.
      iApply ("HΦ" with "[$Q_LC $TG]").
    - iDestruct "inv" as "(%&%& _& Gv0)".
      iCombine "Gv Gv0" gives %H. destruct H as [? _]. done.
  Qed.

End proof.
