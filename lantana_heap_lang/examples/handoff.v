From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export temporal_laws lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_var.
From lantana.heap_lang.examples Require Import step_tactics.
(* Re-imported so that Lantana's [£] shadows upstream Iris' ['£' n]. *)
From lantana.base_logic Require Import later_credits.

(** * A handoff cell: [send] puts a task [f a] into the cell, and [receive] waits for a task
    and runs it. A task comes with the obligations it discharges. *)

Module Handoff.

  Definition send : val :=
    λ: "b" "f" "a", "b" <- SOME ("f", "a").

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
      #[local] handoffGpreS_data_inG :: ghost_varG Σ (oid);
    }.

Class handoffG Σ :=
  HandoffG {
      #[local] handoff_inG :: handoffGpreS Σ;
    }.

Definition handoffΣ : gFunctors :=
    #[ghost_varΣ (oid)].

Global Instance subG_handoffΣ {Σ} : subG handoffΣ Σ → handoffGpreS Σ.
Proof. solve_inG. Qed.

Record handoff_γ :=
  HandoffName {
      handoff_γd : gname;
    }.

Section proof.
  Context `{!heapGS Σ, !handoffG Σ}.

  Let N := nroot.@ "handoff".
  Let Na := N.@ "always".

  (** ** Definitions *)
  (** A task [f a] that discharges the obligations [K], using fuel at layer [ℓt] for the
      children of the running thread. The obligations [K] are children of some parent [p]. *)
  Definition task_at (ℓt : ord.t) (μ : measure) (P : iProp Σ) (f a : val) (K : oids) : iProp Σ :=
    ∀ lc i G p K' C,
      l{{{ thread_expr i C (f a) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g ℓt μ) ∗
           parP_kids p K' ∗ ⌜ K ⊆ K' ⌝ ∗ P }}}
        f a @ i
      l{{{ rv, RET rv; thread_expr i C (of_val rv) ∗ £ lc ∗ thP_kids i G ∗ parP_kids p (K' ∖ K) }}}.

  Definition is_task (ℓ : ord.t) : val → val → oids → iProp Σ :=
    λ f a K, (∃ ℓt (P : iProp Σ), ⌜(ℓt < ℓ)%ordi⌝ ∧ P ∗ ∃ μ, task_at ℓt μ P f a K)%I.

  (** The receiver [g]'s inbox. A sent task waits in a container [c] below the inbox, at the
      layer [ℓt] of the task's fuel; [c] holds the task's obligations and the fuel of the
      receiver for running it. *)
  Definition handoff_task (g : oid) (ℓ : ord.t) (f a : val) (K : oids) : iProp Σ :=
    ∃ c ℓt μ (P : iProp Σ),
      oblP_kids g {[c]} ∗ oblP_kids c K ∗ oblP_assigned c 1 ∗ oblP_fuel c ℓt (μ ⊕ 10)%M ∗
      ⌜(ℓt < ℓ)%ordi⌝ ∗ P ∗ task_at ℓt μ P f a K.

  Definition handoff_inv (b : loc) γd ℓ : iProp Σ :=
    ∃ g, (b ↦{#(1/2)} NONEV ∗ ghost_var_frac γd (1/2)%Qp g ∗ oblP_kids g ∅ ∗ witP_layer g 0) ∨
           (∃ (f a : val) K, b ↦ SOMEV (f, a) ∗ ghost_var_frac γd (1/2)%Qp (g) ∗
                             handoff_task g ℓ f a K) ∨
           (∃ (f a : val), b ↦ SOMEV (f, a) ∗ ghost_var_frac γd (1)%Qp g).

  Definition is_handoff (b : loc) (γ : handoff_γ) ℓ : iProp Σ :=
    alwaysI Na (handoff_inv b (handoff_γd γ) ℓ).

  (** What the handoff exports: the cell always holds [NONE] or a task [SOME (f, a)]; the
      task's resources and the obligations have no trace content. *)
  Definition handoff_inv_itrProp (b : loc) : itrProp heap_lang Σ :=
    ((b ↦{#1/2} NONEV ∧ itrProp_true) ∨
     (∃ f a : val, b ↦ SOMEV (f, a) ∧ itrProp_true) ∨
     (∃ f a : val, b ↦ SOMEV (f, a) ∧ itrProp_true))%ITR.

  Lemma guar_is_handoff b γ ℓ : ⊢ is_handoff b γ ℓ ⊨ₜ itrProp_always (handoff_inv_itrProp b).
  Proof. apply (into_guar _ _). Qed.

  (** The main proofs. *)
  Global Instance handoff_inv_persistent b γ ℓ : Persistent (is_handoff b γ ℓ).
  Proof. rewrite /is_handoff. apply _. Qed.

  (** The invariant is registered: a model update. The inbox [g] is an obligation at layer 0
      without children. *)
  Lemma is_handoff_initialize E b ℓ g :
    b ↦{#(1/2)} NONEV -∗ oblP_kids g ∅ -∗ witP_layer g 0 -∗
    |={E}=>m ∃ γ, is_handoff b γ ℓ ∗ ghost_var_frac (handoff_γd γ) (1/2)%Qp g.
  Proof.
    iIntros "Ptr Kg #Wg".
    iMod (ghost_var_alloc g) as "(%& [Gv Gv0])".
    iExists (HandoffName γ). iFrame "Gv0".
    rewrite /is_handoff. simpl.
    iMod (alwaysI_alloc E Na (handoff_inv b γ ℓ) with "[Ptr Kg Gv]") as "#Inv".
    { iNext. rewrite /handoff_inv. iExists g. iLeft. iFrame. iFrame "Wg". }
    eauto.
  Qed.

  Lemma Handoff_send_spec :
    ⊢ ∃ μ, ∀ lc i (b : loc) (f a : val) G p K K' γ ℓ C,
    l{{{ thread_expr i C (Handoff.send #b f a) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 0 μ) ∗
         parP_kids p K' ∗ ⌜ K ⊆ K' ⌝ ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ%ordi 1) ∗
         b ↦{#(1/2)} NONEV ∗
         is_task ℓ f a K ∗ is_handoff b γ ℓ }}}
      Handoff.send #b f a @ i
    l{{{ RET #(); thread_expr i C (#()) ∗ £ lc ∗ thP_kids i G ∗ parP_kids p (K' ∖ K) }}}.
  Proof.
    iExists 20. iIntros (lc i b f a G p K K' γ ℓ C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Cg& %SubK& OFK& Ptrb& is_task& #handoff_inv)".
    rewrite /is_handoff /Handoff.send.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_pures.
    lwp_bind (Store _ _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iInv "handoff_inv" as "inv".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "(%& [inv | [inv | inv]])".
    - iDestruct "inv" as "(Ptrb0& Gv& Kg& #Wg)".
      iApply lwp_sfmupd.
      iCombine "Ptrb Ptrb0" as "Ptrb".
      iApply (lwp_store _ ∅ 0 with "[$TE $Ptrb $TG $GF1]"). 1: done.
      iIntros "(TE& (_& TG& _)& Ptrb)".
      (* The container of the task, below the inbox at the layer of the task's fuel. *)
      iDestruct "is_task" as "(%ℓt& %P& %Hlt& HP& %μ& #Task)".
      iMod (obl_new _ (PObl g) ∅ ℓt (μ ⊕ 10)%M with "[] Kg") as "(%c& _& Kg& Kc& Ac& Fc& #Wc)".
      { iApply (parP_le_obl with "Wg"). apply ord.O_bot. }
      rewrite union_empty_r_L.
      iMod (obl_move_obl_set _ p c K' ∅ K ℓt with "Wc Cg Kc [OFK]") as "(_& Cg& Kc)".
      { done. }
      { iApply (big_sepS_impl with "OFK"). iIntros "!> %k _ F". iExists ℓ. by iFrame. }
      rewrite union_empty_r_L. iModIntro. iModIntro. iSplitR "TE HΦ Q_LC TG Cg".
      { iNext. iExists _. iRight. iLeft. iExists f, a, K. iFrame "Ptrb Gv".
        iExists c, ℓt, μ, P. iFrame. by iFrame "Task". }
      iApply "HΦ". iFrame.
    - iDestruct "inv" as "(%&%&%& Ptrb0& _)". iCombine "Ptrb Ptrb0" gives %?. destruct H. done.
    - iDestruct "inv" as "(%&%& Ptrb0& _)". iCombine "Ptrb Ptrb0" gives %?. destruct H. done.
  Qed.

  Lemma Handoff_receive_spec :
    ⊢ ∃ μ, ∀ lc i b g γ ℓ C,
    l{{{ thread_expr i C (Handoff.receive #(b : loc)) ∗ thP_kids i {[g]} ∗ ([∗ set] g ∈ {[g]}, oblP_fuel g 0 μ) ∗
         oblP_assigned g 1 ∗ ghost_var_frac (handoff_γd γ) (1/2)%Qp g ∗
         is_handoff b γ ℓ }}}
      Handoff.receive #b @ i
    l{{{ v, RET v; thread_expr i C (of_val v) ∗ £ lc ∗ thP_kids i ∅ }}}.
  Proof.
    (* For internal steps; a task brings its own fuel. *)
    iExists 10. iIntros (lc i b g γ ℓ C Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Ag& Gv& #handoff_inv)".
    rewrite /Handoff.receive.
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    (** Löb induction *)
    iRevert (g) "TE TG GF Gv Ag". iLöb as "IH". iIntros (g) "TE TG GF Gv Ag".
    lwp_pure_lc (lc ⊕ 10)%ord.
    iPoseProof (tlc_split with "LC") as "[Q_LC LC]".
    lwp_bind (Load _).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    rewrite /is_handoff.
    iInv "handoff_inv" as "inv".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]". 1: eauto.
    iApply (lwp_lc_later with "LC1"). iNext.
    iDestruct "inv" as "(%& [inv | [inv | inv]])".
    - iDestruct "inv" as "(Ptrb& Gv0& Kg& #Wg)".
      iApply lwp_sfmupd.
      iApply (lwp_load _ ∅ 0 with "[$TE $Ptrb $TG $GF1]"). 1: done.
      iIntros "(TE& (_& TG& _)& Ptrb)".
      iCombine "Gv Gv0" gives %H. destruct H as [_ <-]. subst.
      (* A fresh inbox, with fresh fuel. *)
      iMod (obl_discharge_leaf with "TG Kg Ag") as "[TG _]"; first set_solver.
      replace ({[g]} ∖ {[g]}) with (∅ : gset oid) by set_solver.
      iMod (obl_new _ (PThread i) ∅ 0 (15 ⊕ 1)%M with "[] TG") as "(%g'& _& TG& Kg'& Ag'& Gf& #Wg')".
      { iApply parP_le_thread. }
      iMod (ghost_var_update_2 g' with "Gv Gv0") as "(Gv& Gv0)". 1: by rewrite Qp.div_2.
      iClear "GF Wg". clear g.
      rewrite union_empty_r_L.
      iAssert ([∗ set] g ∈ {[g']}, oblP_fuel g 0 (15 ⊕ 1)%M)%I with "[Gf]" as "GF".
      { iApply big_sepS_singleton. iFrame. }
      iPoseProof (oblP_fuel_add_set with "GF") as "[GF _]".
      iPoseProof (oblP_fuels_init with "GF") as "GF".
      iModIntro. iModIntro. iSplitL "Ptrb Gv0 Kg'".
      { iNext. iExists _. iLeft. iFrame. iFrame "Wg'". }
      do 3 (iModIntro; lwp_pure_one).
      iPoseProof (oblP_fuels_add 2 with "GF") as "[_ GF]".
      iModIntro. iApply ("IH" with "HΦ TE TG GF Gv Ag'").
    - iDestruct "inv" as "(%&%&%& Ptrb& Gv0& HT)".
      iDestruct "HT" as "(%c& %ℓt& %μ& %P& Kg& Kc& Ac& Fc& %Hlt& HP& #Task)".
      iApply lwp_sfmupd.
      iApply (lwp_load _ ∅ 0 with "[$TE $Ptrb $TG $GF1]"). 1: done.
      iIntros "(TE& (_& TG& _)& Ptrb)".
      iCombine "Gv Gv0" as "Gv" gives %H. destruct H as [_ <-]. subst.
      (* The task's container moves up to the thread, the inbox is discharged. *)
      iMod (obl_move_up _ (PThread i) {[g]} g {[c]} c with "TG Kg") as "(%Hcg& TG& Kg)".
      { set_solver. }
      { set_solver. }
      replace ({[c]} ∖ {[c]}) with (∅ : gset oid) by set_solver.
      iMod (obl_discharge_leaf with "TG Kg Ag") as "[TG _]"; first set_solver.
      replace (({[c]} ∪ {[g]}) ∖ {[g]}) with ({[c]} : gset oid) by set_solver.
      iPoseProof (oblP_fuel_add with "Fc") as "[Fμ F10]".
      iClear "GF".
      iAssert (oblP_fuels {[c]} 10) with "[F10]" as "GF".
      { rewrite big_sepS_singleton. iExists _. iFrame. }
      iModIntro. iModIntro. iSplitL "Ptrb Gv".
      { iNext. iExists _. iRight. iRight. iFrame. }
      lwp_pures.
      lwp_bind (f a).
      iModIntro.
      iApply lwp_sfmupd.
      iApply ("Task" $! 0 with "[$TE $TG Fμ $Kc $HP]").
      { iSplitL "Fμ"; first by rewrite big_sepS_singleton. by iPureIntro. }
      iIntros (?) "(TE& _& TG& Kc)". replace (K ∖ K) with (∅ : gset oid) by set_solver.
      iMod (obl_discharge_leaf with "TG Kc Ac") as "[TG _]"; first set_solver.
      replace ({[c]} ∖ {[c]}) with (∅ : gset oid) by set_solver.
      iApply ("HΦ" with "[$TE $Q_LC $TG]").
    - iDestruct "inv" as "(%&%& _& Gv0)".
      iCombine "Gv Gv0" gives %H. destruct H as [? _]. done.
  Qed.

End proof.

(** ** The handoff cell, at the level of traces *)
Section trace.

  (** The cell [b] holds [v] in the current state of the trace (any fraction). *)
  Definition tr_cell (b : loc) (v : val) : trProp heap_lang := (∃ dq, b ↦{dq} v)%R.

  Lemma tr_cell_intro b dq v : (b ↦{dq} v)%R ⊆ tr_cell b v.
  Proof. apply (tr_exist_intro (λ dq, (b ↦{dq} v)%R) dq). Qed.

  (** At all times the cell is empty or holds a task. *)
  Definition handoff_tr (b : loc) : trProp heap_lang :=
    (□ (tr_cell b NONEV ∨ ∃ f a : val, tr_cell b (SOMEV (f, a))))%R.

  Lemma handoff_inv_itrProp_ext {Σ} b :
    itrProp_external (itrProp_always (handoff_inv_itrProp (Σ:=Σ) b)) ⊆ handoff_tr b.
  Proof.
    rewrite /handoff_inv_itrProp. etrans; first apply (itrProp_ext_of _ _). apply tr_always_mono.
    apply tr_or_elim; last apply tr_or_elim.
    - apply tr_or_intro_l. etrans; [apply tr_and_elim_l|apply tr_cell_intro].
    - apply tr_or_intro_r. apply tr_exist_elim => f. apply tr_exist_elim => a.
      etrans; first apply tr_and_elim_l. etrans; first apply tr_cell_intro.
      etrans; [apply (tr_exist_intro (λ a, tr_cell b (SOMEV (f, a))) a)|
               apply (tr_exist_intro (λ f, (∃ a : val, tr_cell b (SOMEV (f, a)))%R) f)].
    - apply tr_or_intro_r. apply tr_exist_elim => f. apply tr_exist_elim => a.
      etrans; first apply tr_and_elim_l. etrans; first apply tr_cell_intro.
      etrans; [apply (tr_exist_intro (λ a, tr_cell b (SOMEV (f, a))) a)|
               apply (tr_exist_intro (λ f, (∃ a : val, tr_cell b (SOMEV (f, a)))%R) f)].
  Qed.

End trace.
