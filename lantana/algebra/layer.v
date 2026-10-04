(** The layers of Lantana: pairs of an ordinal of [lantana.ordinal] and a natural number, ordered
    lexicographically. *)

From stdpp Require Import base tactics.
From lantana.ordinal Require Export ordinal_facts.
From lantana.algebra Require Export measure.

(** Lantana uses three libraries of ordinals:
    1. [transfinite.stepindex.ordinals], only for step-indexing;
    2. the opam library [Ordinal] ([Ord.t]), for the logic's internal definitions (fuels and
       witnesses, see [measure_rep]);
    3. [lantana.ordinal] ([ord.t]), a copy of 2 used for layers: using 2 for both the layers and
       [measure_rep] causes a universe inconsistency.
    Ideally, 2 would be universe polymorphic and 3 could be removed. *)

Definition layer : Type := prod ord.t nat.

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

(** Notations. *)
Export ordinalScope.
Export arithmeticScope.
Export hessenbergScope.

Notation "'ℵ'" := (ord.large) : ordinal_scope.
