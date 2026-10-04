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

  (** Discharge at the actual final value, using credits from earlier steps: the thread's
      only child is the obligation of the finally. *)
  Lemma thread_expr_terminate_finally i E v k N :
    ↑N ⊆ E →
    thread_expr i [] (of_val v) -∗ £ (2 : Ord.t) -∗
    thP_kids i {[k]} -∗ oblP_kids k ∅ -∗
    finallyI N k 1 (thread_expr i [] (of_val v)) -∗ |={E}=>m
    thread_expr i [] (of_val v) ∗ thP_done i.
  Proof.
    iIntros (Hmask) "TE LC TG Kk HF".
    iMod (finallyI_discharge with "LC TG Kk HF TE") as "(TE& TG& #Od)"; [done|set_solver|].
    replace ({[k]} ∖ {[k]} : gset _) with (∅ : oids) by set_solver.
    iMod (thread_terminate with "TG") as "$". by iFrame.
  Qed.

End laws.
