From stdpp Require Import base.
From liveness Require Export orderedCM.
Require Import Lia Program.

Module WFOrderedCM.
  Class t {A : Type} (leR : A -> A -> Prop) (addO : A -> A -> A) (ltR : A -> A -> Prop) := {
      #[global] orderedCM :: OrderedCM.t leR addO;
      lt_wf : well_founded ltR;
      lt_le_add_l : forall a b c, (ltR OrderedCM.unit b) -> (leR (addO a b) c) -> (ltR a c);
    }.

  Section properties.
    Context `{t A leR addO ltR}.

    Lemma lt_le_add_r : forall a b c, (ltR OrderedCM.unit a) -> (leR (addO a b) c) -> (ltR b c).
    Proof using Type*.
      intros a b c LT LE. assert (leR (addO b a) c).
      { etransitivity. eapply OrderedCM.add_comm_le. auto. }
      eapply lt_le_add_l; eauto.
    Qed.

    Lemma induction_type : forall P : A -> Type, (forall x : A, (forall y : A, ltR y x -> P y) -> P x) -> forall a : A, P a.
    Proof using Type*.
      intros. apply (well_founded_induction_type lt_wf). auto.
    Qed.

    Lemma induction_set : forall P : A -> Set, (forall x : A, (forall y : A, ltR y x -> P y) -> P x) -> forall a : A, P a.
    Proof using Type*.
      intros. apply (well_founded_induction lt_wf). auto.
    Qed.

    Lemma ind : forall P : A -> Prop, (forall x : A, (forall y : A, ltR y x -> P y) -> P x) -> forall a : A, P a.
    Proof using Type*.
      intros. apply (well_founded_ind lt_wf). auto.
    Qed.

  End properties.
End WFOrderedCM.

Global Program Instance nat_WFOrderedCM: WFOrderedCM.t le Nat.add lt :=
  WFOrderedCM.Build_t nat le Nat.add lt _ _ _.
Next Obligation. lia. Qed.
