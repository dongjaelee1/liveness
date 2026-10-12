From Stdlib Require Import Lia.
From stdpp Require Import base tactics.
From lantana.prelude Require Export ordinal_copy_facts.
From lantana.algebra Require Export measure.

(** The development uses three ordinal libraries:
    1. [transfinite.stepindex.ordinals], only for step-indices;
    2. the Ordinal library (opam package [Ordinal]), for the logic's fuels and witnesses;
    3. its copy in [ordinal/], for [layer], the layers passed to [measure_rep].
    The copy avoids a universe inconsistency: library 2 is not universe polymorphic. *)

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
