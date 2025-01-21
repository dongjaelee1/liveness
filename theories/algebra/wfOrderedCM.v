From stdpp Require Import base.
From liveness Require Export orderedCM.

Module WFOrderedCM.
  Class t {A : Type} (leR : A -> A -> Prop) (addO : A -> A -> A) (ltR : A -> A -> Prop) := {
      #[global] orderedCM :: OrderedCM.t leR addO;
      lt_wf : well_founded ltR;
      lt_exists_l : forall a c, (exists b, (ltR OrderedCM.unit b) /\ (leR (addO a b) c)) <-> (ltR a c);
    }.

  Section properties.
    Context `{t A leR addO ltR}.

    Lemma lt_exists_r : forall a c, (exists b, (ltR OrderedCM.unit b) /\ (leR (addO b a) c)) <-> (ltR a c).
    Proof using Type*.
      intros a c. split; intros.
      { destruct H0 as (b&LT&LE). apply lt_exists_l. exists b.
        split; [auto|]. etransitivity. eapply OrderedCM.add_comm_le. auto.
      }
      { apply lt_exists_l in H0. destruct H0 as (b&LT&LE). exists b.
        split; [auto|]. etransitivity. eapply OrderedCM.add_comm_le. auto.
      }
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
