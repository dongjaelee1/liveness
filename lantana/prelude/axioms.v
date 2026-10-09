From Stdlib.Logic Require ClassicalFacts.
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
Definition inj_pair2 := Classical_Prop.EqdepTheory.inj_pair2.

Lemma not_ex_all_not_help
      A (P: A -> Prop)
      (NOT: ~ (exists a: A, P a))
  :
  forall a, ~ P a.
Proof.
  intros. eapply Classical_Pred_Type.not_ex_all_not in NOT. eauto.
Qed.

Ltac nean H := eapply not_ex_all_not_help in H; red in H.

Definition proof_irrelevance := proof_irrelevance.
Definition choice := choice.

Definition propositional_extensionality := propositional_extensionality.
