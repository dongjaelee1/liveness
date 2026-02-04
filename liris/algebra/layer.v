From Stdlib Require Import Lia.
From stdpp Require Import base tactics.
From liris.ordinal Require Import Ordinal Arithmetic Hessenberg.
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

  Definition layer : Type := Ord.t.

End layer.

Global Instance layer_layer_class : layer_class layer :=
  Build_layer_class _ _ Ord.lt_well_founded.

(** Notations and Coercions. *)
Export OrdinalScope.
Export ArithmeticScope.
Export HessenbergScope.
