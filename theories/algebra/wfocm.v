From stdpp Require Import base.
From liveness Require Export ocm.

Module WFOCM.
  Class t {A : Type} (leR : A -> A -> Prop) (addO : A -> A -> A) (ltR : A -> A -> Prop) := {
      #[global] ocm :: OCM.t leR addO;
      lt_wf : well_founded ltR;
      lt_exists_left : forall a c, (exists b, (ltR OCM.unit b) /\ (leR (addO a b) c)) <-> (ltR a c);
    }.

  Section properties.
    Context `{t A leR addO ltR}.

    Lemma lt_exists_right : forall a c, (exists b, (ltR OCM.unit b) /\ (leR (addO b a) c)) <-> (ltR a c).
    Proof using Type*.
      intros a c. split; intros.
      { destruct H0 as (b&LT&LE). apply lt_exists_left. exists b.
        split; [auto|]. etransitivity. eapply OCM.add_comm_le. auto.
      }
      { apply lt_exists_left in H0. destruct H0 as (b&LT&LE). exists b.
        split; [auto|]. etransitivity. eapply OCM.add_comm_le. auto.
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

  Class pack (A : Type) := {
      leR : A -> A -> Prop;
      addO : A -> A -> A;
      ltR : A -> A -> Prop;
      #[global] wfocm :: @t A leR addO ltR;
    }.

End WFOCM.
