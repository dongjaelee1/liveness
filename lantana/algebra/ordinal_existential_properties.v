(** The ordinals [Ord.t] of the [Ordinal] library have the existential property for the
    transfinite step-index type [ordI]. *)

From transfinite Require Export existential_properties.
From transfinite.stepindex Require Import ordinals.
From Ordinal Require Import Ordinal.

Notation OrdinalExistential := (TypeExistentialProperty Ord.t).
Global Instance OrdinalExistential_instance : OrdinalExistential ordI.
Proof. apply _. Qed.
