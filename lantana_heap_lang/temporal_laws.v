From iris.proofmode Require Import proofmode.
From lantana.trace Require Export guarantee_infer.
From lantana.heap_lang Require Export primitive_laws.
From iris.prelude Require Import options.

(** * Temporal guarantees for heap_lang: the atoms are the state predicates of lang.v, the
    points-to facts and thread expressions determine them ([StateFact]), and so guarantee
    them ([IntoTemporal] by [into_temporal_state_fact]). *)

Notation "l ↦ dq v" := (tprop_state (pointsto_sat l dq v))
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : tprop_scope.
Notation "'exits' v @ i" := (tprop_state (thread_expr_sat i [] (of_val v)))
  (at level 20, v, i at level 1, format "exits  v @ i") : tprop_scope.

Section laws.
  Context `{!heapGS Σ}.

  Global Instance pointsto_state_fact l dq v : StateFact (l ↦{dq} v) (pointsto_sat l dq v).
  Proof. intros σ Θ κs. apply pointsto_state_interp. Qed.
  Global Instance thread_expr_state_fact i C e :
    StateFact (thread_expr i C e) (thread_expr_sat i C e).
  Proof. intros σ Θ κs. apply thread_expr_state_interp. Qed.
  (* TODO: [StateFact] instances for the invariant heap ([l ↦_I v]). *)

  (** A freed location stays freed. *)
  Definition freed_tprop (l : loc) : tprop heap_lang Σ := tprop_state (λ σ _, heap σ !! l = Some None).
  Global Instance freed_state_fact l q : StateFact (freed l q) (λ σ _, heap σ !! l = Some None).
  Proof. intros σ Θ κs. iIntros "[(H& _) F]". iApply (gen_heap_valid with "H F"). Qed.

  Lemma freed_temporal (l : loc) q : ⊢ freed l q ⊨ₜ freed_tprop l.
  Proof. apply temporal_state_fact, _. Qed.

  (** The guarantee of an atom is inferred from its state fact. *)
  Local Lemma ex_pointsto_temporal l dq v : ⊢ l ↦{dq} v ⊨ₜ (l ↦{dq} v).
  Proof. apply (into_temporal _ _). Qed.

  (** An implication with a state antecedent, from a case split on the state: the value of
      [l] decides the disjunct. The antecedent [l ↦ v0] is read on the trace. *)
  Lemma temporal_impl_pointsto_example l v0 v1 (P0 P1 : iProp Σ) G0 :
    v0 ≠ v1 →
    P0 ⊨ₜ G0 -∗ ((l ↦ v0 ∗ P0) ∨ (l ↦ v1 ∗ P1)) ⊨ₜ ((l ↦ v0) → G0).
  Proof.
    iIntros (Hv) "#HG". iApply (temporal_impl_state _ _ P0 with "HG").
    iIntros "!>" (σ Θ κs Hl) "[SI [[_ HP]|[Hl1 _]]]"; first by iFrame.
    iDestruct (pointsto_state_interp σ Θ κs l (DfracOwn 1) v1 with "[$SI $Hl1]") as %H1.
    rewrite /pointsto_sat in Hl H1. rewrite Hl in H1. by simplify_eq.
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
