From iris.proofmode Require Import proofmode.
From lantana.trace Require Export guarantee_infer.
From lantana.heap_lang Require Export primitive_laws.
From iris.prelude Require Import options.

(** * Temporal guarantees for heap_lang: points-to facts and thread expressions guarantee
    the corresponding state predicates. *)

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
  (* TODO: [IntoTemporal] instances for the invariant heap ([l ↦_I v]). *)

  (** A freed location stays freed. *)
  Definition freed_tps (l : loc) : tps heap_lang Σ := tps_state (λ σ _, heap σ !! l = Some None).

  Lemma freed_temporal (l : loc) q : ⊢ freed l q ⊨ₜ freed_tps l.
  Proof.
    apply temporal_state. intros σ Θ κs. iIntros "[(H& _) F]".
    iApply (gen_heap_valid with "H F").
  Qed.

  (** An implication with a state antecedent, from a case split on the state: the value of
      [l] decides the disjunct. The antecedent [l ↦ v0] is read on the trace. *)
  Lemma temporal_impl_pointsto_example l v0 v1 (P0 P1 : iProp Σ) G0 :
    v0 ≠ v1 →
    P0 ⊨ₜ G0 -∗ ((l ↦ v0 ∗ P0) ∨ (l ↦ v1 ∗ P1)) ⊨ₜ ((l ↦ v0) → G0).
  Proof.
    iIntros (Hv) "#HG".
    iApply (temporal_weaken _ (tps_impl (tps_state (λ σ _, heap σ !! l = Some (Some v0))) G0)).
    { apply tps_impl_mono; [|apply tps_le_refl]. intros [n τf].
      rewrite /= /tr_atomic /ts_emb /ts_atomic /trace_now /=. by destruct (τf n) as (((?&?)&?)&?). }
    iApply (temporal_impl_state _ _ P0 with "HG").
    iIntros "!>" (σ Θ κs Hl) "[SI [[_ HP]|[Hl1 _]]]"; first by iFrame.
    iDestruct (state_interp_wf σ Θ κs (pred_pointsto l (DfracOwn 1) v1) with "[$SI $Hl1]") as %H1.
    simpl in H1. rewrite Hl in H1. by simplify_eq.
  Qed.

  (** Discharging a [finally] on the thread's final value, with credits from earlier steps. *)
  Lemma thread_expr_terminate_finally i E v k N :
    ↑N ⊆ E →
    thread_expr i [] (of_val v) -∗ £n 1 -∗
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
