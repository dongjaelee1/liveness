From iris.proofmode Require Import proofmode.
From lantana.trace Require Export guarantee_infer.
From lantana.heap_lang Require Export primitive_laws.
From iris.prelude Require Import options.

(** * Temporal guarantees for heap_lang: the atoms are the state predicates of lang.v, the
    points-to facts and thread expressions determine them ([StateFact]), and so guarantee
    them ([IntoTemporal] by [into_temporal_state_fact]). *)

Notation "l ↦ dq v" := (itrProp_state (pointsto_sat l dq v))
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : itrProp_scope.
Notation "'exits' v @ i" := (itrProp_state (thread_expr_sat i [] (of_val v)))
  (at level 20, v, i at level 1, format "exits  v @ i") : itrProp_scope.

(** The state predicate of a freed location, and its trace atom. *)
Definition freed_sat (l : loc) : state → thread_pool heap_lang → Prop := λ σ _, heap σ !! l = Some None.
Definition freed_tr (l : loc) : trProp heap_lang := tr_state (freed_sat l).

Section laws.
  Context `{!heapGS Σ}.

  Global Instance pointsto_state_fact l dq v : StateFact (l ↦{dq} v) (pointsto_sat l dq v).
  Proof. intros σ Θ κs. apply pointsto_state_interp. Qed.
  Global Instance thread_expr_state_fact i C e :
    StateFact (thread_expr i C e) (thread_expr_sat i C e).
  Proof. intros σ Θ κs. apply thread_expr_state_interp. Qed.
  (* TODO: [StateFact] instances for the invariant heap ([l ↦_I v]). *)

  (** A freed location stays freed. *)
  Definition freed_itrProp (l : loc) : itrProp heap_lang Σ := itrProp_state (freed_sat l).
  Global Instance freed_state_fact l q : StateFact (freed l q) (freed_sat l).
  Proof. intros σ Θ κs. iIntros "[(H& _) F]". iApply (gen_heap_valid with "H F"). Qed.

  Lemma freed_temporal (l : loc) q : ⊢ freed l q ⊨ₜ freed_itrProp l.
  Proof. apply temporal_state_fact, _. Qed.

  (** The guarantee of an atom is inferred from its state fact. *)
  Local Lemma ex_pointsto_temporal l dq v : ⊢ l ↦{dq} v ⊨ₜ (l ↦{dq} v).
  Proof. apply (into_temporal _ _). Qed.

  (** ** Rules for the atoms, on traces *)

  (** Two points-to atoms on the same location agree on the value; the fraction plays no
      role on traces; a location is not both allocated and freed. *)
  Lemma tr_pointsto_agree l dq1 dq2 v1 v2 : ((l ↦{dq1} v1) ∧ (l ↦{dq2} v2))%R ⊆ (⌜v1 = v2⌝)%R.
  Proof.
    etrans; first apply tr_state_and. apply tr_state_pure.
    intros σ Θ [H1 H2]. rewrite /pointsto_sat in H1 H2. by simplify_eq.
  Qed.
  Lemma tr_pointsto_frac l dq dq' v : (l ↦{dq} v)%R ⊆ (l ↦{dq'} v)%R.
  Proof. by intros τ. Qed.
  Lemma tr_pointsto_freed l dq v : ((l ↦{dq} v) ∧ freed_tr l)%R ⊆ (⌜False⌝)%R.
  Proof.
    etrans; first apply tr_state_and. apply tr_state_pure.
    intros σ Θ [H1 H2]. rewrite /pointsto_sat in H1. rewrite /freed_sat in H2. by simplify_eq.
  Qed.

  (** Implications are exported on traces ([temporal_cast]): the inferred guarantee of a
      case split on the value of [l] implies "[l ↦ v0] now → [G0]", by the rules of
      trace_prop_rules.v and the atom rule above. *)
  Lemma ex_impl_pointsto l v0 v1 (P0 P1 : iProp Σ) G0 `{!IntoTemporal P0 G0} :
    v0 ≠ v1 →
    tr_sem ((l ↦ v0 ∗ P0) ∨ (l ↦ v1 ∗ P1)) ⊆ ((l ↦ v0) → itrProp_external G0)%R.
  Proof.
    intros Hv. etrans; first apply (into_trace _ _).
    apply tr_or_elim; apply tr_impl_intro.
    - etrans; [apply tr_and_elim_l|apply tr_and_elim_r].
    - etrans; [apply tr_and_mono; [apply tr_and_elim_l|reflexivity]|].
      etrans; first apply tr_pointsto_agree. apply tr_pure_elim. intros Heq. destruct (Hv (eq_sym Heq)).
  Qed.

  (** Inference is compositional, hence incomplete: [l ↦ v ∗ l ↦ v] is inconsistent, so it
      guarantees [⊥] ([temporal_mono]), while its inferred guarantee is satisfiable. *)
  Lemma ex_sep_bot l v : ⊢ (l ↦ v ∗ l ↦ v) ⊨ₜ ⌜False⌝.
  Proof.
    iApply (temporal_mono ⌜False⌝%I); last iApply temporal_pure.
    iIntros "!> [H1 H2]". by iDestruct (pointsto_ne with "H1 H2") as %?.
  Qed.
  Local Lemma ex_sep_inferred l v :
    (ltac:(tr_of (l ↦ v ∗ l ↦ v)%I) : trProp heap_lang) = ((l ↦ v) ∧ (l ↦ v))%R.
  Proof. done. Qed.

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
