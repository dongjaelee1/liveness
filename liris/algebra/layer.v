From Stdlib Require Import Lia.
From stdpp Require Import base tactics.
From liris.ordinal Require Export ordinal_facts.
From liris.algebra Require Export measure.

(** We have three definitions of ordinal.
1. From transfinite.stepindex Require Import ordinals.
This one has different definitions and we use it exclusively for step-index, so there should be no problem.
2. From Ordinal Require Export Ordinal.
This is the opam library, and we use this for logic's internal definitions, namely fuels and witnesses.
3. From liris.ordinal Require Import Ordinal.
This is a copy of 2. We use this as the layer of measure_rep.
This causes universe inconsistency, so we have a copy to use as layer.

Ideally, we should make the library 2 universe polymorphic and remove 3.
 *)

Section layer.

  Definition layer : Type := prod ord.t nat.

End layer.

Global Program Instance layer_layer_class : layer_class layer :=
  Build_layer_class _
    _
    (prod_eq_lt_well_founded _ _ _ _ _ ord.eq_Equivalence _ ord.lt_well_founded PeanoNat.Nat.lt_wf_0)
    (prod_eq_lt_Transitive _ _ _ _ _)
    _
    (prod_relation_equiv ord.eq_Equivalence eq_equivalence)
    _
.
Next Obligation.
  intros. rewrite <-H. auto.
Qed.
Next Obligation.
  intros. rewrite <-H. auto.
Qed.
Next Obligation.
  intros. rewrite <-H. auto.
Qed.
Next Obligation.
  repeat intro. destruct x, y, x0, y0. destruct H, H0. simplify_eq /=. split; intro.
  - inv H1.
    + econstructor 1. rewrite <-H, <-H0. auto.
    + destruct ALE.
      * econstructor 2; auto. left. rewrite <-H, <-H0, <-H1. done.
      * econstructor 1. rewrite <-H, <-H0. auto.
  - inv H1.
    + econstructor 1. rewrite H, H0. auto.
    + destruct ALE.
      * econstructor 2; auto. left. rewrite H, H0, <-H1. done.
      * econstructor 1. rewrite H, H0. auto.
Qed.

(** Notations and Coercions. *)
Export ordinalScope.
Export arithmeticScope.
Export hessenbergScope.

Notation "'ℵ'" := (ord.large) : ordinal_scope.
