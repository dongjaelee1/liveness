(** The thread map: ghost state for a map from thread ids to values, with an authoritative
    part [thread_map_interp Θ R] and per-thread fragments [thread p b v q] (owned with fraction
    [q] if [b], persistent otherwise). *)

From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Export own.
From transfinite.base_logic.lib Require Import ghost_map.
From iris.prelude Require Import options.

Local Notation thread_map P V := (gmap P V).

Class thread_mapGpreS `{SI: sidx} (P V : Type) (Σ : gFunctors) `{Countable P} := {
  #[local] thread_map_GpreS_inG :: ghost_mapG Σ P V
}.

Class thread_mapGS `{SI: sidx} (P V : Type) (Σ : gFunctors) `{Countable P} := ThreadMapGS {
  #[local] thread_map_inG :: thread_mapGpreS P V Σ;
  thread_map_name : gname
}.
Global Arguments thread_map_name {_ _ _ _ _ _} _ : assert.

Definition thread_mapΣ `{SI: sidx} (P V : Type) `{Countable P} : gFunctors :=
  #[ghost_mapΣ P V].

Global Instance subG_thread_mapGpreS `{SI: sidx} {Σ P V} `{Countable P} :
  subG (thread_mapΣ P V) Σ → thread_mapGpreS P V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{SI: sidx} `{tG : thread_mapGS P V Σ}.
  Implicit Types R : thread_map P V.
  Implicit Types p : P.

  Definition thread_map_interp (Θ : gset P) R : iProp Σ :=
    (⌜dom R = Θ⌝ ∗ ghost_map_auth_frac (thread_map_name tG) 1 R)%I.

  Local Definition thread_def (p : P) (b : bool) (v : V) (q : Qp) : iProp Σ :=
    (if b then p ↪[thread_map_name tG]{#q} v else p ↪[thread_map_name tG]□ v)%I.
  Local Definition thread_aux : seal (@thread_def). Proof. by eexists. Qed.
  Definition thread := thread_aux.(unseal).
  Local Definition thread_unseal : @thread = @thread_def := thread_aux.(seal_eq).
End definitions.

Lemma thread_map_init `{SI: sidx} `{Countable P, !thread_mapGpreS P V Σ} τs :
  ⊢ |==> ∃ _ : thread_mapGS P V Σ, thread_map_interp (dom τs) τs ∗ ([∗ map] p↦v ∈ τs, thread p true v 1).
Proof.
  iMod (ghost_map_alloc τs) as (γ) "[Hh M]".
  iModIntro. iExists (ThreadMapGS _ P V _ _ _ _ γ).
  rewrite thread_unseal. by iFrame.
Qed.

Section thread_map.
  Context `{thread_mapGS P V Σ}.
  Implicit Types p : P.
  Implicit Types v : V.
  Implicit Types R : thread_map P V.
  Implicit Types Θ : gset P.

  (** General properties of [thread] *)
  Global Instance thread_timeless p b v q : Timeless (thread p b v q).
  Proof. rewrite thread_unseal /thread_def. apply _. Qed.
  Global Instance thread_false_persistent p v q : Persistent (thread p false v q).
  Proof. rewrite thread_unseal /thread_def. apply _. Qed.

  Global Instance thread_true_fractional p v : fractional.Fractional (λ q, thread p true v q).
  Proof. rewrite thread_unseal /thread_def. apply _. Qed.
  Global Instance thread_true_as_fractional p v q :
    fractional.AsFractional (thread p true v q) (λ q0, thread p true v q0) q.
  Proof. rewrite thread_unseal /thread_def. apply _. Qed.

  Lemma thread_true_frac_ne p1 p2 v1 v2 q1 q2 :
    ¬ ✓ ((DfracOwn q1) ⋅ (DfracOwn q2)) → thread p1 true v1 q1 -∗ thread p2 true v2 q2 -∗ ⌜p1 ≠ p2⌝.
  Proof. rewrite thread_unseal /thread_def. apply ghost_map_elem_frac_ne. Qed.
  Lemma thread_agree p b1 b2 v1 v2 q1 q2 :
    thread p b1 v1 q1 -∗ thread p b2 v2 q2 -∗ ⌜v1 = v2⌝.
  Proof. rewrite thread_unseal /thread_def. destruct b1, b2; apply ghost_map_elem_agree. Qed.

  Lemma thread_true_to_false p v q q' :
    thread p true v q ==∗ thread p false v q'.
  Proof.
    rewrite thread_unseal /thread_def. iApply ghost_map_elem_persist.
  Qed.

  Lemma thread_map_new_thread p v Θ R :
    p ∉ Θ →
    thread_map_interp Θ R ==∗
    thread_map_interp (Θ ∪ {[p]}) (<[p:=v]>R) ∗ thread p true v 1.
  Proof.
    iIntros (Hp) "[% HR]".
    rewrite thread_unseal /thread_def.
    iMod (ghost_map_insert p v with "HR") as "[H● H◯]".
    { apply not_elem_of_dom. set_solver. }
    iFrame. iPureIntro. rewrite dom_insert_L. subst. set_solver.
  Qed.

  Lemma thread_map_thread_read p b v Θ R q :
    thread_map_interp Θ R -∗ thread p b v q -∗ (⌜ R !! p = Some v ⌝).
  Proof.
    iIntros "[% HR] Ht". rewrite thread_unseal /thread_def.
    destruct b; iApply (ghost_map_lookup with "HR Ht").
  Qed.

  Lemma thread_map_thread_update p v v' Θ R :
    thread_map_interp Θ R ∗ thread p true v 1 ==∗
    thread_map_interp Θ (<[p:=v']>R) ∗ thread p true v' 1.
  Proof.
    iIntros "[[% HR] Hp]". rewrite /thread_map_interp thread_unseal /thread_def.
    iCombine "HR Hp" gives %HR.
    iMod (ghost_map_update v' with "HR Hp") as "[H● H◯]". iFrame.
    iPureIntro. apply elem_of_dom_2 in HR. rewrite dom_insert_L. subst. set_solver.
  Qed.
End thread_map.
