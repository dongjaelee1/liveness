From Stdlib Require Import Lia.
From stdpp Require Import base tactics.
From lantana.ordinal Require Export ordinal_facts.
From lantana.algebra Require Export measure.

(** We have three definitions of ordinal.
1. From transfinite.stepindex Require Import ordinals.
This one has different definitions and we use it exclusively for step-index, so there should be no problem.
2. From Ordinal Require Export Ordinal.
This is the opam library, and we use this for logic's internal definitions, namely fuels and witnesses.
3. From lantana.ordinal Require Import Ordinal.
This is a copy of 2. We use this as the layer of measure_rep.
This causes universe inconsistency, so we have a copy to use as layer.

Ideally, we should make the library 2 universe polymorphic and remove 3.
 *)

Section layer.
  (** The layer of obligations and witnesses: an ordinal, the layer proper,
      which orders waits (and hence enforces acyclicity), and a sub-level,
      0 for carriers and 1 for obligations and witnesses, so that a witness
      at layer ℓ dominates every carrier at layer ℓ. *)
  Definition layer0 : Type := prod ord.t nat.
  (** Carrier fuel has one more coordinate below the sub-level: a depth,
      which orders calls the way the layer orders waits. Carrier fuel sits
      at [(ℓ, 0, d)], obligations and witnesses at [(ℓ, 1, ord.O)], so every
      depth stays below the witness and the acyclicity side conditions,
      which compare the ordinal only, never see it. *)
  Definition layer : Type := prod layer0 ord.t.
End layer.

Global Program Instance layer0_layer_class : layer_class layer0 :=
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

Global Program Instance layer_layer_class : layer_class layer :=
  Build_layer_class _
    _
    (@prod_eq_lt_well_founded layer0 ord.t eqL ltL ord.lt eqL_equivalence _ wf_ltL ord.lt_well_founded)
    (prod_eq_lt_Transitive _ _ _ _ _)
    _
    (prod_relation_equiv eqL_equivalence ord.eq_Equivalence)
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
  intros [a1 b1] [a2 b2] [Ha Hb] [a3 b3] [a4 b4] [Ha' Hb'].
  cbn [fst snd] in Ha, Hb, Ha', Hb'.
  split; intro HL; inversion HL; subst.
  - econstructor 1. rewrite <-Ha, <-Ha'. auto.
  - destruct ALE as [E | L].
    + econstructor 2; [left; rewrite <-Ha, <-Ha'; auto | rewrite <-Hb, <-Hb'; auto].
    + econstructor 1. rewrite <-Ha, <-Ha'. auto.
  - econstructor 1. rewrite Ha, Ha'. auto.
  - destruct ALE as [E | L].
    + econstructor 2; [left; rewrite Ha, Ha'; auto | rewrite Hb, Hb'; auto].
    + econstructor 1. rewrite Ha, Ha'. auto.
Qed.

(** Notations and Coercions. *)
Export ordinalScope.
Export arithmeticScope.
Export hessenbergScope.

Notation "'ℵ'" := (ord.large) : ordinal_scope.
