From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Export own.
From transfinite.base_logic.lib Require Import ghost_map.
From iris.prelude Require Import options.
Import uPred.

Local Notation threads_map P V := (gmap P V).

(** The CMRA we need. *)
Class threads_mapGpreS `{SI: indexT} (P V : Type) (Σ : gFunctors) `{Countable P} := {
  #[local] threads_map_GpreS_inG :: ghost_mapG Σ P V
}.

Class threads_mapGS `{SI: indexT} (P V : Type) (Σ : gFunctors) `{Countable P} := ProphMapGS {
  #[local] threads_map_inG :: threads_mapGpreS P V Σ;
  threads_map_name : gname
}.
Global Arguments threads_map_name {_ _ _ _ _ _} _ : assert.

Definition threads_mapΣ `{SI: indexT} (P V : Type) `{Countable P} : gFunctors :=
  #[ghost_mapΣ P V].

Global Instance subG_threads_mapGpreS `{SI: indexT} {Σ P V} `{Countable P} :
  subG (threads_mapΣ P V) Σ → threads_mapGpreS P V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{SI: indexT} `{tG : threads_mapGS P V Σ}.
  Implicit Types R : threads_map P V.
  Implicit Types p : P.

  Definition threads_map_interp R : iProp Σ :=
    ghost_map_auth (threads_map_name tG) 1 R.

  Local Definition proph_def (p : P) (vs : list V) : iProp Σ :=
    p ↪[threads_map_name pG] vs.
  Local Definition proph_aux : seal (@proph_def). Proof. by eexists. Qed.
  Definition proph := proph_aux.(unseal).
  Local Definition proph_unseal : @proph = @proph_def := proph_aux.(seal_eq).
End definitions.

Section list_resolves.
  Context {P V : Type} `{Countable P}.
  Implicit Type pvs : proph_val_list P V.
  Implicit Type p : P.
  Implicit Type R : threads_map P V.

  Lemma resolves_insert pvs p R :
    proph_resolves_in_list R pvs →
    p ∉ dom R →
    proph_resolves_in_list (<[p := proph_list_resolves pvs p]> R) pvs.
  Proof.
    intros Hinlist Hp q vs HEq.
    destruct (decide (p = q)) as [->|NEq].
    - rewrite lookup_insert_eq in HEq. by inversion HEq.
    - rewrite lookup_insert_ne in HEq; last done. by apply Hinlist.
  Qed.
End list_resolves.

Lemma threads_map_init `{SI: indexT} `{Countable P, !threads_mapGpreS P V Σ} pvs ps :
  ⊢ |==> ∃ _ : threads_mapGS P V Σ, threads_map_interp pvs ps.
Proof.
  iMod (ghost_map_alloc_empty) as (γ) "Hh".
  iModIntro. iExists (ProphMapGS _ P V _ _ _ _ γ), ∅. iSplit; last by iFrame.
  iPureIntro. done.
Qed.

Section threads_map.
  Context `{threads_mapGS P V Σ}.
  Implicit Types p : P.
  Implicit Types v : V.
  Implicit Types vs : list V.
  Implicit Types R : threads_map P V.
  Implicit Types ps : gset P.

  (** General properties of pointsto *)
  Global Instance proph_timeless p vs : Timeless (proph p vs).
  Proof. rewrite proph_unseal /proph_def. apply _. Qed.

  Lemma proph_exclusive p vs1 vs2 :
    proph p vs1 -∗ proph p vs2 -∗ False.
  Proof.
    rewrite proph_unseal /proph_def. iIntros "Hp1 Hp2".
    by iDestruct (ghost_map_elem_ne with "Hp1 Hp2") as %?.
  Qed.

  Lemma threads_map_new_proph p ps pvs :
    p ∉ ps →
    threads_map_interp pvs ps ==∗
    threads_map_interp pvs ({[p]} ∪ ps) ∗ proph p (proph_list_resolves pvs p).
  Proof.
    iIntros (Hp) "HR". iDestruct "HR" as (R) "[[% %] H●]".
    rewrite proph_unseal /proph_def.
    iMod (ghost_map_insert p (proph_list_resolves pvs p) with "H●") as "[H● H◯]".
    { apply not_elem_of_dom. set_solver. }
    iFrame. iPureIntro. split.
    - apply resolves_insert; first done. set_solver.
    - rewrite dom_insert. set_solver.
  Qed.

  Lemma threads_map_resolve_proph p v pvs ps vs :
    threads_map_interp ((p,v) :: pvs) ps ∗ proph p vs ==∗
    ∃vs', ⌜vs = v::vs'⌝ ∗ threads_map_interp pvs ps ∗ proph p vs'.
  Proof.
    iIntros "[HR Hp]". iDestruct "HR" as (R) "[HP H●]". iDestruct "HP" as %[Hres Hdom].
    rewrite /threads_map_interp proph_unseal /proph_def.
    iCombine "H● Hp" gives %HR.
    assert (vs = v :: proph_list_resolves pvs p) as ->.
    { rewrite (Hres p vs HR). simpl. by rewrite decide_True. }
    iMod (ghost_map_update (proph_list_resolves pvs p) with "H● Hp") as "[H● H◯]".
    iModIntro. iExists (proph_list_resolves pvs p). iFrame. iSplitR.
    - iPureIntro. done.
    - iPureIntro. split.
      + intros q ws HEq. destruct (decide (p = q)) as [<-|NEq].
        * rewrite lookup_insert_eq in HEq. by inversion HEq.
        * rewrite lookup_insert_ne in HEq; last done.
          rewrite (Hres q ws HEq).
          simpl. rewrite decide_False; done.
      + assert (p ∈ dom R) by exact: elem_of_dom_2.
        rewrite dom_insert. set_solver.
  Qed.
End threads_map.
