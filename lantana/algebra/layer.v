(** The layers of Lantana: the ordinals of [lantana.ordinal] with their order. *)

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

Notation layer := ord.t.

Global Instance layer_layer_class : layer_class layer :=
  Build_layer_class layer ord.lt ord.lt_well_founded _ ord.eq _ _.

(** Notations. *)
Export ordinalScope.
Export arithmeticScope.
Export hessenbergScope.

Notation "'ℵ'" := (ord.large) : ordinal_scope.

(** A measure grows with its layer. *)
Lemma measure_rep_layer_le `{!ord_mono_fun_class} (ℓ1 ℓ2 : layer) μ :
  (ℓ1 <= ℓ2)%ordi → (measure_rep ℓ1 μ <= measure_rep ℓ2 μ)%ord.
Proof.
  intros Hl. apply measure_rep_layer_le_proper.
  apply classicOrd.le_eq_or_lt in Hl. destruct Hl as [Hl|Hl]; [by right|by left].
Qed.
