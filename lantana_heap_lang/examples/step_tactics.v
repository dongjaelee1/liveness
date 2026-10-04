From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

(** * Tactics for pure steps, shared by the examples

    [lwp_pure] leaves a goal that pays the step. These tactics pay it with the fuel of the
    thread's obligations and no witnesses; [post_lwp_lc n] also takes [n] later credits. They
    rely on the hypothesis names of the examples: ["TE"] for the thread's expression, ["TG"]
    for its obligations, ["GF"] for their fuel, and ["LC"] for the credits. *)
Ltac post_lwp :=
  simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

Ltac lwp_pure_one := (lwp_pure; post_lwp).
Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

Ltac post_lwp_lc n :=
  simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).
