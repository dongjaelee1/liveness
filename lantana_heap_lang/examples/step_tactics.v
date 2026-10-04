From lantana.algebra Require Import auth_mra.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

(** * Helpers shared by the examples

    Tactics for pure steps, and the [auth_mra] instance on ordinals used by the ticket locks. *)

(** ** Pure steps

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

(** ** Ordinals as an [auth_mra] *)
(** FIXME: move to the algebra library. *)
Global Program Instance ordinal_auth_mra_class : auth_mra_class ord.le ord.eq :=
  Build_auth_mra_class ord.t _ _ _ _ _ _.
Next Obligation.
  repeat intro. split; auto.
Qed.
