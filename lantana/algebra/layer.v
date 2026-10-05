(** The layers of Lantana: the ordinals of [lantana.ordinal] with their order. *)

From stdpp Require Import base tactics.
From lantana.ordinal Require Export ordinal_facts.
From lantana.algebra Require Export measure.

(** [ord.t] is a copy of [Ord.t] of the [Ordinal] library (used by [measure_rep]): using [Ord.t]
    for the layers too causes a universe inconsistency. A universe-polymorphic [Ordinal] would
    make the copy unnecessary. *)

Notation layer := ord.t.

Global Instance layer_layer_class : layer_class layer :=
  Build_layer_class layer ord.lt ord.lt_well_founded _ ord.eq _ _.

(** Notations. *)
Export ordinalScope.
Export arithmeticScope.
Export hessenbergScope.

Notation "'ℵ'" := (ord.large) : ordinal_scope.

Lemma measure_rep_layer_le `{!ord_mono_fun_class} (ℓ1 ℓ2 : layer) μ :
  (ℓ1 <= ℓ2)%ordi → (measure_rep ℓ1 μ <= measure_rep ℓ2 μ)%ord.
Proof.
  intros Hl. apply measure_rep_layer_le_proper.
  apply classicOrd.le_eq_or_lt in Hl. destruct Hl as [Hl|Hl]; [by right|by left].
Qed.
