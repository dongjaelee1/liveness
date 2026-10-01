From iris.proofmode Require Import proofmode.
From lantana.program_logic Require Export temporal_guarantee.
From lantana.heap_lang Require Export primitive_laws.
From iris.prelude Require Import options.

(** * Temporal guarantees for heap_lang

    Atoms: points-to facts and thread expressions guarantee the corresponding state
    predicates. *)

Notation "l ↦ dq v" := (tps_atomic (pred_pointsto l dq v))
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : tps_scope.
Notation "'exits' v @ i" := (tps_atomic (pred_expr i [] (of_val v)))
  (at level 20, v, i at level 1, format "exits  v @ i") : tps_scope.

Section laws.
  Context `{!heapGS Σ}.

  Global Instance into_temporal_pointsto l dq v :
    IntoTemporal (l ↦{dq} v) (tps_atomic (pred_pointsto l dq v)) | 10.
  Proof. exact (temporal_atomic (pred_pointsto l dq v)). Qed.

  Global Instance into_temporal_thread_expr i C e :
    IntoTemporal (thread_expr i C e) (tps_atomic (pred_expr i C e)) | 10.
  Proof. exact (temporal_atomic (pred_expr i C e)). Qed.

  (** Discharge at the actual final value, using credits from earlier steps. *)
  Lemma thread_expr_terminateT i E v g ℓ k N :
    ↑N ⊆ E →
    thread_expr i [] (of_val v) -∗ £ (2 : Ord.t) -∗
    thP_carriers i {[g]} -∗ crP_obls g ℓ {[k]} -∗
    finallyT N k 1 (thread_expr i [] (of_val v)) -∗ |={E}=>m
    thread_expr i [] (of_val v) ∗ thP_done i.
  Proof.
    iIntros (Hmask) "TE LC TG Cg HF".
    iMod (untilI_discharge with "HF") as "HF"; first set_solver.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iDestruct "HF" as "[_ HF]". iMod ("HF" $! _) as "HF".
    iMod ("HF" with "[TE]") as "HF".
    { iNext. iFrame. }
    iPoseProof ("HF" with "[] Cg") as "HF".
    { iPureIntro. set_solver. }
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("HF" $! _) as "HF". iMod "HF" as "(TE& Gg& #Odkl)".
    replace ({[k]} ∖ {[k]} : gset _) with (∅ : oids) by set_solver.
    iMod (carrier_delete with "TG Gg") as "TG"; first set_solver.
    replace ({[g]} ∖ {[g]} : gset _) with (∅ : gset ocid) by set_solver.
    iMod (thread_terminate with "TG") as "$". by iFrame.
  Qed.

End laws.
