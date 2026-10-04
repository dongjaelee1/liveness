(** The classical axioms assumed by Lantana: functional and propositional extensionality,
    excluded middle, proof irrelevance and choice. *)

From Stdlib.Logic Require Import ProofIrrelevance.
From Stdlib.Logic Require Import PropExtensionality.
From Stdlib.Logic Require Import ClassicalChoice.
From Stdlib.Logic Require Import FunctionalExtensionality.

Set Implicit Arguments.

Lemma func_ext_dep {A} {B: A -> Type} (f g: forall x, B x): (forall x, f x = g x) -> f = g.
Proof.
  apply @FunctionalExtensionality.functional_extensionality_dep.
Qed.

Lemma func_ext {A B} (f g: A -> B): (forall x, f x = g x) -> f = g.
Proof.
  apply func_ext_dep.
Qed.

Definition classic := Classical_Prop.classic.

Definition proof_irrelevance := proof_irrelevance.
Definition choice := choice.

Definition propositional_extensionality := propositional_extensionality.
