From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

(** * Tactics for pure steps, shared by the examples

    They pay the step with the fuel of the thread's obligations and no witnesses
    ([post_lwp_lc n] also takes [n] later credits). Hypothesis names: ["TE"] expression,
    ["TG"] obligations, ["GF"] their fuel, ["LC"] credits. *)
Ltac post_lwp :=
  simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

Ltac lwp_pure_one := (lwp_pure; post_lwp).
Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

Ltac post_lwp_lc n :=
  simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).
