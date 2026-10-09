From stdpp Require Import base.
From lantana Require Export ocm.

Module WFOCM.
  Class t {A : Type} (leR : A -> A -> Prop) (addO : A -> A -> A) (ltR : A -> A -> Prop) := {
      #[global] ocm :: OCM.t leR addO;
      lt_wf : well_founded ltR;
      lt_exists_left : forall a c, (exists b, (ltR OCM.unit b) /\ (leR (addO a b) c)) <-> (ltR a c);
      exists_pos : exists a, ltR OCM.unit a;
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

    Lemma lt_le : forall a b, (ltR a b) -> (leR a b).
    Proof using Type*.
      intros. apply lt_exists_left in H0. destruct H0 as (?&?&?).
      etransitivity; last eauto. apply OCM.add_base_left_le.
    Qed.
    Lemma lt_le_lt : forall a b c, (ltR a b) -> (leR b c) -> (ltR a c).
    Proof using Type*.
      intros. apply lt_exists_left in H0. destruct H0 as (?&?&?).
      apply lt_exists_left. exists x. split; first auto.
      etransitivity; eauto.
    Qed.
    Lemma le_lt_lt : forall a b c, (leR a b) -> (ltR b c) -> (ltR a c).
    Proof using Type*.
      intros. apply lt_exists_left in H1. destruct H1 as (?&?&?).
      apply lt_exists_left. exists x. split; first auto.
      etransitivity; eauto. apply OCM.add_le_proper; auto. reflexivity.
    Qed.

    Global Instance lt_Transitive : Transitive ltR.
    Proof using Type*.
      intros x y z H0 H1. eapply lt_le_lt; eauto. apply lt_le; auto.
    Qed.

    Lemma lt_Irreflexive : Irreflexive ltR.
    Proof using Type*.
      intros x. induction x using (well_founded_ind lt_wf). intros ?. eapply H0; eauto.
    Qed.

    Lemma lt_le_false : forall a b, (ltR a b) → (leR b a) → False.
    Proof using Type*.
      intros. apply lt_exists_left in H0. destruct H0 as (?&?&?).
      assert (leR (addO a x) a) by (etransitivity; eauto). assert (ltR a a).
      { apply lt_exists_left. exists x. split; auto. }
      apply lt_Irreflexive in H4. auto.
    Qed.

    Global Instance eq_Proper : Proper (OCM.eq ==> OCM.eq ==> iff) ltR.
    Proof using.
      repeat intro. destruct H0, H1. split; intros.
      - eapply (lt_le_lt _ x0); eauto. eapply (le_lt_lt _ x); eauto.
      - eapply (lt_le_lt _ y0); eauto. eapply (le_lt_lt _ y); eauto.
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

Infix "w=" := OCM.eq (at level 70).
Infix "w≤" := WFOCM.leR (at level 70).
Infix "w+" := WFOCM.addO (at level 70).
Infix "w<" := WFOCM.ltR (at level 70).
Notation "'wzero'" := OCM.unit (only parsing).
