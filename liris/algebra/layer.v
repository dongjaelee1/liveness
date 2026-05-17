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
This is a copy of 2. We use this as the layer of measure.
This causes universe inconsistency, so we have a copy to use as layer.

Ideally, we should make the library 2 universe polymorphic and remove 3.
 *)

Section layer.

  Definition layer : Type := prod ord.t nat.

  Lemma prod_lt_Transitive {A B} {RA : A -> A -> Prop} {RB : B -> B -> Prop} :
    Transitive RA → Transitive RB → Transitive (prod_lt RA RB).
  Proof.
    intros. repeat intro. inv H1; inv H2.
    - econstructor 1. eauto.
    - destruct ALE.
      + subst. econstructor 1. auto.
      + econstructor 1; eauto.
    - destruct ALE.
      + subst. econstructor 1; auto.
      + econstructor 1; eauto.
    - destruct ALE.
      + subst. destruct ALE0.
        * subst. econstructor 2; eauto.
        * econstructor 1; auto.
      + destruct ALE0.
        * subst. econstructor 1; eauto.
        * econstructor 1; eauto.
  Qed.

End layer.

Global Instance layer_layer_class : layer_class layer :=
  Build_layer_class _ _
    (prod_lt_well_founded _ _ _ _ ord.lt_well_founded PeanoNat.Nat.lt_wf_0)
    (prod_lt_Transitive _ _)
.

(** Notations and Coercions. *)
Export ordinalScope.
Export arithmeticScope.
Export hessenbergScope.

Notation "'ℵ'" := (ord.large) : ordinal_scope.
