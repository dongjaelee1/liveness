(** * Parents in an obligation forest

    A parent is either a thread or an obligation. Shared by the obligation-forest interface
    ([obl_forest.v]) and its model ([oforest.v]). *)

From stdpp Require Import countable.
From iris.prelude Require Import options.
From lantana.base_logic Require Import obligation.

Inductive parent :=
| PThread (i : positive)
| PObl (k : oid).

Global Instance parent_eq_dec : EqDecision parent.
Proof. solve_decision. Qed.

Global Instance parent_countable : Countable parent.
Proof.
  refine (inj_countable' (λ p, match p with PThread i => inl i | PObl k => inr k end)
                         (λ s, match s with inl i => PThread i | inr k => PObl k end) _).
  by intros [].
Qed.
