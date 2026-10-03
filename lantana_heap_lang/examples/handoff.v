From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_var.
(* Re-activate Lantana's [£] (upstream Iris also declares ['£' n] at the same level). *)
From lantana.base_logic Require Import later_credits.

Module Handoff.

  (** Put x at buffer b *)
  Definition send : val :=
    λ: "b" "f" "a", "b" <- SOME ("f", "a").

  (** Checks until the buffer b contains SOME x *)
  Definition receive : val := 
    rec: "loop" "b" :=
      match: !"b" with
        NONE => "loop" "b"
      | SOME "x" => (Fst "x") (Snd "x")
      end.

End Handoff.

(** The CMRA we need. *)
Class handoffGpreS (Σ : gFunctors) : Set :=
  HandoffGpreS {
      #[local] handoffGpreS_data_inG :: ghost_varG Σ (ocid);
    }.

Class handoffG Σ :=
  HandoffG {
      #[local] handoff_inG :: handoffGpreS Σ;
    }.

Definition handoffΣ : gFunctors :=
    #[ghost_varΣ (ocid)].

Global Instance subG_handoffΣ {Σ} : subG handoffΣ Σ → handoffGpreS Σ.
Proof. solve_inG. Qed.

Record handoff_γ :=
  HandoffName {
      handoff_γd : gname;
    }.

Section proof.
  Context `{!heapGS Σ, !handoffG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let N := nroot.@ "handoff".
  Let Na := N.@ "always".
  Let Np := N.@ "pointsto".

  Remark N_disj_1 : Na ## Np.
  Proof. by apply ndot_ne_disjoint. Qed.
  Remark N_subseteq_1 : ↑Np ⊆ (⊤ : coPset) ∖ ↑Na.
  Proof. pose proof N_disj_1. set_solver. Qed.
  Remark Na_disj_treg : Na ## tregN.
  Proof. solve_ndisj. Qed.

  (** ** Definitions *)
  Definition is_task (ℓ : ord.t) : val → val → oids → iProp Σ :=
    λ f a K, (∃ ℓt (P : iProp Σ),
               ⌜(ℓt < ℓ)%ordi⌝ ∧
               P ∗
               ∃ μ, ∀ lc i G g K' ℓg C,
               l{{{ thread_expr i C (f a) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g ℓt μ) ∗
                    crP_obls g ℓg K' ∗ ⌜ K ⊆ K' ⌝ ∗ P }}}
                f a @ i
              l{{{ rv, RET rv; thread_expr i C (of_val rv) ∗ £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K' ∖ K) }}})%I.

  Definition handoff_inv (b : loc) γd ℓ : iProp Σ :=
    ∃ g, (b ↦{#(1/2)} NONEV ∗ ghost_var_frac γd (1/2)%Qp g ∗ crP_obls g ℓ ∅) ∨
           (∃ (f a : val) K, b ↦ SOMEV (f, a) ∗ ghost_var_frac γd (1/2)%Qp (g) ∗
                             crP_obls g ℓ K ∗ is_task ℓ f a K) ∨
           (∃ (f a : val), b ↦ SOMEV (f, a) ∗ ghost_var_frac γd (1)%Qp g).

  Definition is_handoff (b : loc) (γ : handoff_γ) ℓ : iProp Σ :=
    alwaysI Na (handoff_inv b (handoff_γd γ) ℓ).

  (** What the handoff exports: the cell always holds [NONE] or a task [SOME (f, a)]; the
      task's resources and the carriers have no trace content. *)
  Definition handoff_inv_tps (b : loc) : tps heap_lang Σ :=
    ((b ↦{#1/2} NONEV ∧ tps_true) ∨
     (∃ f a : val, b ↦ SOMEV (f, a) ∧ tps_true) ∨
     (∃ f a : val, b ↦ SOMEV (f, a) ∧ tps_true))%S.

  Lemma is_handoff_temporal b γ ℓ : ⊢ is_handoff b γ ℓ ⊨ₜ tps_always (handoff_inv_tps b).
  Proof. apply (into_temporal _ _). Qed.

  (** The main proofs. *)
  Global Instance handoff_inv_persistent b γ ℓ : Persistent (is_handoff b γ ℓ).
  Proof. rewrite /is_handoff. apply _. Qed.

  (** The invariant is registered: a model update, with the registry and a credit. *)
  Lemma is_handoff_initialize E b ℓ g :
    ↑tregN ⊆ E →
    treg -∗ £n 1 -∗ b ↦{#(1/2)} NONEV -∗ crP_obls g ℓ ∅ -∗
    |={E}=>g ∃ γ, is_handoff b γ ℓ ∗ ghost_var_frac (handoff_γd γ) (1/2)%Qp g.
  Proof.
    iIntros (HE) "#TR LC Ptr Co".
    iMod (ghost_var_alloc g) as "(%& [Gv Gv0])".
    iExists (HandoffName γ). iFrame "Gv0".
    rewrite /is_handoff. simpl.
    iMod (alwaysI_alloc E Na (handoff_inv b γ ℓ) with "TR LC [Ptr Co Gv]") as "#Inv"; [done|apply Na_disj_treg| |].
    { iNext. rewrite /handoff_inv. iExists g. iLeft. iFrame. }
    eauto.
  Qed.

  Lemma Handoff_send_spec :
    ⊢ ∃ μ, ∀ lc i (b : loc) (f a : val) G g K K' γ ℓ ℓg C,
    l{{{ thread_expr i C (Handoff.send #b f a) ∗ thP_carriers i G ∗ ([∗ set] g ∈ G, crP_fuel g 0 μ) ∗
         crP_obls g ℓg K' ∗ ⌜ K ⊆ K' ⌝ ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ%ordi 1) ∗
         b ↦{#(1/2)} NONEV ∗
         is_task ℓ f a K ∗ is_handoff b γ ℓ }}}
      Handoff.send #b f a @ i
    l{{{ RET #(); thread_expr i C (#()) ∗ £ lc ∗ thP_carriers i G ∗ crP_obls g ℓg (K' ∖ K) }}}.
  Proof.
    iExists 20. iIntros (lc i b f a G g K K' γ ℓ ℓg C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Cg& %SubK& OFK& Ptrb& is_task& #handoff_inv)".
    rewrite /is_handoff /Handoff.send.
    iPoseProof (crP_fuels_init with "GF") as "GF".
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_pures.
    lwp_bind (Store _ _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iInv "handoff_inv" as "inv".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "(%& [inv | [inv | inv]])".
    - iDestruct "inv" as "(Ptrb0& Gv& Cg0)".
      iApply lwp_sfmupd.
      iCombine "Ptrb Ptrb0" as "Ptrb".
      iApply (lwp_store _ ∅ 0 with "[$TE $Ptrb $TG $GF1]"). 1: done.
      iIntros "(TE& (_& TG& _)& Ptrb)".
      iMod (obl_offload_set with "Cg Cg0 OFK") as "(Cg& Cg0& %DisjK)". 1: auto. 1: done.
      rewrite union_empty_l_L. iModIntro. iModIntro. iSplitR "TE HΦ Q_LC TG Cg".
      { iNext. iExists _. iRight. iLeft. iFrame. }
      iApply "HΦ". iFrame.
    - iDestruct "inv" as "(%&%&%& Ptrb0& _)". iCombine "Ptrb Ptrb0" gives %?. destruct H. done.
    - iDestruct "inv" as "(%&%& Ptrb0& _)". iCombine "Ptrb Ptrb0" gives %?. destruct H. done.
  Qed.

  Lemma Handoff_receive_spec :
    ⊢ ∃ μ, ∀ lc i b g γ ℓ C,
    l{{{ thread_expr i C (Handoff.receive #(b : loc)) ∗ thP_carriers i {[g]} ∗ ([∗ set] g ∈ {[g]}, crP_fuel g ℓ μ) ∗
         ghost_var_frac (handoff_γd γ) (1/2)%Qp g ∗
         is_handoff b γ ℓ }}}
      Handoff.receive #b @ i
    l{{{ v, RET v; thread_expr i C (of_val v) ∗ £ lc ∗ thP_carriers i ∅ }}}.
  Proof.
    (** For internal steps and executing run_task *)
    iExists (10 ⊕ 1)%M. iIntros (lc i b g γ ℓ C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Gv& #handoff_inv)".
    rewrite /Handoff.receive.
    iPoseProof (crP_fuel_add_set with "GF") as "[GF F_task]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    (** Lob (co-)induction *)
    iRevert (g) "TE TG GF Gv F_task". iLöb as "IH". iIntros (g) "TE TG GF Gv F_task".
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_bind (Load _).
    iPoseProof (crP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    (** Cases. *)
    rewrite /is_handoff.
    iInv "handoff_inv" as "inv".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "(%& [inv | [inv | inv]])".
    - iDestruct "inv" as "(Ptrb& Gv0& Cg)".
      iApply lwp_sfmupd.
      iApply (lwp_load _ ∅ 0 with "[$TE $Ptrb $TG $GF1]"). 1: done.
      iIntros "(TE& (_& TG& _)& Ptrb)".
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
      iModIntro. iApply ("IH" with "HΦ TE TG GF Gv F_task").
    - iDestruct "inv" as "(%&%&%& Ptrb& Gv0& Cg& is_task)".
      iApply (lwp_load _ ∅ 0 with "[$TE $Ptrb $TG $GF1]"). 1: done.
      iIntros "(TE& (_& TG& _)& Ptrb)".
      iCombine "Gv Gv0" as "Gv" gives %H. destruct H as [_ <-]. subst.
      iModIntro. iSplitL "Ptrb Gv".
      { iNext. iExists _. iRight. iRight. iFrame. }
      lwp_pures.
      lwp_bind (f a).
      iDestruct "is_task" as "(%&%& %Hlt& HP& %& task)".
      iModIntro.
      iMod (crP_fuel_extend_set _ ℓt _ μ with "F_task") as "F_task". 1: eauto.
      iApply lwp_sfgupd.
      (* iApply lwp_sfmupd. *)
      iApply ("task" $! 0 with "[$TE $TG $F_task $Cg $HP]"). 1: eauto.
      iIntros (?) "(TE& _& TG& Cg)". replace (K ∖ K) with (∅ : gset ocid) by set_solver.
      iMod (carrier_delete with "TG Cg") as "TG". 1: set_solver.
      replace ({[g]} ∖ {[g]}) with (∅ : gset ocid) by set_solver.
      iApply ("HΦ" with "[$TE $Q_LC $TG]").
    - iDestruct "inv" as "(%&%& _& Gv0)".
      iCombine "Gv Gv0" gives %H. destruct H as [? _]. done.
  Qed.

End proof.

(** ** The handoff cell, at the level of traces *)
Section trace.

  (** The cell [b] holds [v] in the current state of the trace (any fraction). *)
  Definition tr_cell (b : loc) (v : val) : trProp heap_lang :=
    λ τ, ∃ dq, tr_atomic (pred_pointsto b dq v) τ.

  (** At all times the cell is empty or holds a task. *)
  Definition handoff_tr (b : loc) : trProp heap_lang :=
    tr_always (λ τ, tr_cell b NONEV τ ∨ ∃ f a : val, tr_cell b (SOMEV (f, a)) τ).

  Lemma handoff_inv_tps_tr {Σ} b τ :
    tps_tr (tps_always (handoff_inv_tps (Σ:=Σ) b)) τ → handoff_tr b τ.
  Proof.
    destruct τ as [k τf]. intros Hal m Hm. destruct (Hal m Hm) as [[Hb _]|[(f & a & Hb & _)|(f & a & Hb & _)]].
    - left. exists (DfracOwn (1/2)). exact Hb.
    - right. exists f, a, (DfracOwn 1). exact Hb.
    - right. exists f, a, (DfracOwn 1). exact Hb.
  Qed.

End trace.
