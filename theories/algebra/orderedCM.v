From stdpp Require Import base.
From liveness Require Import axioms.
Require Import Program.

(** The less-than-or-equal-to-based Ordered Commutative Monoid class. *)
(** Reference: "Module OrderedCM" in Lilo and FOS. *)
Module OrderedCM.
  Class t {car : Type} (leR : car -> car -> Prop) (addO : car -> car -> car) := {
      unit : car;
      #[global] le_PreOrder :: PreOrder leR;
      #[global] le_total :: Total leR;
      #[global] add_assoc_le :: Assoc leR addO;
      #[global] add_comm_le :: Comm leR addO;
      #[global] add_unit_left_le :: LeftId leR unit addO;
      add_base_left_le : forall a0 a1, leR a0 (addO a0 a1);
      #[global] add_left_le_proper :: forall a, Proper (leR ==> leR) (addO a);
    }.

  Definition eq `{t car leR addO} (a0 a1 : car) : Prop := leR a0 a1 /\ leR a1 a0.

  Definition join `{t car leR addO} (a0 a1: car) : car :=
    if (excluded_middle_informative (leR a0 a1)) then a1 else a0.

  Definition meet `{t car leR addO} (a0 a1: car): car :=
    if (excluded_middle_informative (leR a0 a1)) then a0 else a1.

  Section properties.
    Context `{t car leR addO}.

    Local Notation le := leR.
    Local Notation add := addO.

    Global Program Instance eq_Equivalence : Equivalence eq.
    Next Obligation.
    Proof using Type*.
      unfold eq. intros x. split; reflexivity.
    Qed.
    Next Obligation.
    Proof using Type*.
      unfold eq. intros x y [H1 H2]. split; auto.
    Qed.
    Next Obligation.
    Proof using Type*.
      unfold eq. intros x y z [Ha1 Ha2] [Hb1 Hb2]. split; etransitivity; eauto.
    Qed.

    Global Instance add_assoc_eq : Assoc eq add.
    Proof using Type*.
      repeat intro. split.
      { eapply add_assoc_le. }
      { etransitivity; [eapply add_comm_le |].
        etransitivity; [eapply add_assoc_le |].
        etransitivity; [eapply add_comm_le |].
        etransitivity; [eapply add_assoc_le |].
        eapply add_comm_le.
      }
    Qed.

    Global Instance add_comm_eq : Comm eq add.
    Proof using Type*.
      repeat intro. split; eapply add_comm_le.
    Qed.

    Global Instance add_unit_right_le : RightId le unit add.
    Proof using Type*.
      intros a. etransitivity.
      { eapply add_comm_le. }
      { eapply add_unit_left_le. }
    Qed.

    Lemma add_base_right_le a0 a1 : le a1 (add a0 a1).
    Proof using Type*.
      etransitivity.
      { eapply add_base_left_le. }
      { eapply add_comm_le. }
    Qed.

    Global Instance add_unit_left_eq : LeftId eq unit add.
    Proof using Type*.
      intros a. split.
      { apply add_unit_left_le. }
      { apply add_base_right_le. }
    Qed.

    Global Instance add_unit_right_eq : RightId eq unit add.
    Proof using Type*.
      intros a. etransitivity.
      { eapply add_comm_eq. }
      { eapply add_unit_left_eq. }
    Qed.

    Global Instance add_right_le_proper : forall a, Proper (le ==> le) (flip add a).
    Proof using Type*.
      repeat intro. simpl. etransitivity.
      { eapply add_comm_le. }
      etransitivity.
      { eapply add_left_le_proper; eauto. }
      eapply add_comm_le.
    Qed.

    Global Instance add_le_proper : Proper (le ==> le ==> le) add.
    Proof using Type*.
      repeat intro. etransitivity.
      { eapply add_left_le_proper. eauto. }
      eapply add_right_le_proper. auto.
    Qed.

    Lemma unit_le a : le unit a.
    Proof using Type*.
      etransitivity.
      { eapply add_base_right_le. }
      { eapply add_unit_right_le. }
    Qed.

    Global Instance add_left_eq_proper : forall a, Proper (eq ==> eq) (add a).
    Proof using Type*.
      intros a b c [H1 H2]. split; eapply add_left_le_proper; eauto.
    Qed.

    Global Instance add_right_eq_proper : forall a, Proper (eq ==> eq) (flip add a).
    Proof using Type*.
      intros a b c [H1 H2]. split; eapply add_right_le_proper; eauto.
    Qed.

    Global Instance add_eq_proper : Proper (eq ==> eq ==> eq) add.
    Proof using Type*.
      intros a b [H1 H2] c d [H3 H4]. split; eapply add_le_proper; eauto.
    Qed.

    Lemma join_left_le a0 a1 : le a0 (join a0 a1).
    Proof using Type*.
      unfold join. destruct (excluded_middle_informative); auto. reflexivity.
    Qed.

    Lemma join_right_le a0 a1 : le a1 (join a0 a1).
    Proof using Type*.
      unfold join. destruct (excluded_middle_informative). reflexivity.
      destruct (le_total a0 a1); auto. contradiction.
    Qed.

    Lemma join_supremum a0 a1 a (LE0: le a0 a) (LE1: le a1 a) : le (join a0 a1) a.
    Proof using Type*.
      unfold join. destruct (excluded_middle_informative); auto.
    Qed.

    Global Instance join_assoc_le : Assoc le join.
    Proof using Type*.
      repeat intro. eapply join_supremum.
      { etransitivity; eapply join_left_le. }
      eapply join_supremum.
      { etransitivity.
        { eapply join_right_le. }
        { eapply join_left_le. }
      }
      eapply join_right_le.
    Qed.

    Global Instance join_comm_le : Comm le join.
    Proof using Type*.
      repeat intro. eapply join_supremum.
      { eapply join_right_le. }
      { eapply join_left_le. }
    Qed.

    Global Instance join_unit_left_le : LeftId le unit join.
    Proof using Type*.
      repeat intro. eapply join_supremum.
      { eapply unit_le. }
      { reflexivity. }
    Qed.

    Global Instance join_left_le_proper : forall a, Proper (le ==> le) (join a).
    Proof using Type*.
      repeat intro. eapply join_supremum.
      { eapply join_left_le. }
      { etransitivity; eauto. eapply join_right_le. }
    Qed.

    Global Instance join_assoc_eq : Assoc eq join.
    Proof using Type*.
      repeat intro. split.
      { eapply join_assoc_le. }
      { etransitivity; [eapply join_comm_le |].
        etransitivity; [eapply join_assoc_le |].
        etransitivity; [eapply join_comm_le |].
        etransitivity; [eapply join_assoc_le |].
        eapply join_comm_le.
      }
    Qed.

    Global Instance join_comm_eq : Comm eq join.
    Proof using Type*.
      repeat intro. split; eapply join_comm_le.
    Qed.

    Global Instance join_unit_right_le : RightId le unit join.
    Proof using Type*.
      repeat intro. etransitivity.
      { eapply join_comm_le. }
      { eapply join_unit_left_le. }
    Qed.

    Global Instance join_unit_left_eq : LeftId eq unit join.
    Proof using Type*.
      repeat intro. split.
      { apply join_unit_left_le. }
      { apply join_right_le. }
    Qed.

    Global Instance join_unit_right_eq : RightId eq unit join.
    Proof using Type*.
      repeat intro. etransitivity.
      { eapply join_comm_eq. }
      { eapply join_unit_left_eq. }
    Qed.

    Global Instance join_right_le_proper : forall a, Proper (le ==> le) (flip join a).
    Proof using Type*.
      repeat intro. etransitivity.
      { eapply join_comm_le. }
      etransitivity.
      { eapply join_left_le_proper; eauto. }
      { eapply join_comm_le. }
    Qed.

    Global Instance join_le_proper : Proper (le ==> le ==> le) join.
    Proof using Type*.
      repeat intro. etransitivity; [eapply join_left_le_proper; eauto |].
      eapply join_right_le_proper; eauto.
    Qed.

    Global Instance join_left_eq_proper : forall a, Proper (eq ==> eq) (join a).
    Proof using Type*.
      intros x y z [H1 H2]. split; eapply join_left_le_proper; eauto.
    Qed.

    Global Instance join_right_eq_proper : forall a, Proper (eq ==> eq) (flip join a).
    Proof using Type*.
      intros x y z [H1 H2]. split; eapply join_right_le_proper; eauto.
    Qed.

    Global Instance join_eq_proper : Proper (eq ==> eq ==> eq) join.
    Proof using Type*.
      intros x y [H1 H2] a b [H3 H4]. split; eapply join_le_proper; eauto.
    Qed.

    Global Instance join_idemp_le : IdemP le join.
    Proof. repeat intro. apply join_supremum; reflexivity. Qed.
    Global Instance join_idemp_eq : IdemP eq join.
    Proof. repeat intro. split; [apply join_idemp_le | apply join_left_le]. Qed.

    Global Instance meet_left_le : forall a, LeftAbsorb le a meet.
    Proof using Type*.
      repeat intro. unfold meet. destruct (excluded_middle_informative (le a x)).
      { reflexivity. }
      { destruct (le_total a x); auto. contradiction. }
    Qed.

    Global Instance meet_right_le : forall a, RightAbsorb le a meet.
    Proof using Type*.
      repeat intro. unfold meet. destruct (excluded_middle_informative (le x a)); auto.
      reflexivity.
    Qed.

    Lemma meet_infimum a0 a1 a (LE0: le a a0) (LE1: le a a1) : le a (meet a0 a1).
    Proof using Type*.
      unfold meet. destruct (excluded_middle_informative (le a0 a1)); auto.
    Qed.

    Global Instance meet_assoc_le : Assoc le meet.
    Proof using Type*.
      repeat intro. eapply meet_infimum.
      { eapply meet_infimum.
        { eapply meet_left_le. }
        etransitivity.
        { eapply meet_right_le. }
        { eapply meet_left_le. }
      }
      etransitivity; eapply meet_right_le.
    Qed.

    Global Instance meet_comm_le : Comm le meet.
    Proof using Type*.
      repeat intro. eapply meet_infimum.
      { eapply meet_right_le. }
      { eapply meet_left_le. }
    Qed.

    Global Instance meet_left_le_proper : forall a, Proper (le ==> le) (meet a).
    Proof using Type*.
      repeat intro. eapply meet_infimum.
      { eapply meet_left_le. }
      { etransitivity; eauto. eapply meet_right_le. }
    Qed.

    Global Instance meet_right_le_proper : forall a, Proper (le ==> le) (flip meet a).
    Proof using Type*.
      repeat intro. etransitivity.
      { eapply meet_comm_le. }
      etransitivity.
      { eapply meet_left_le_proper; eauto. }
      { eapply meet_comm_le. }
    Qed.

    Global Instance meet_le_proper : Proper (le ==> le ==> le) meet.
    Proof using Type*.
      repeat intro. etransitivity; [eapply meet_left_le_proper; eauto |].
      eapply meet_right_le_proper; eauto.
    Qed.

    Global Instance meet_assoc_eq : Assoc eq meet.
    Proof using Type*.
      repeat intro. split.
      { eapply meet_assoc_le. }
      { etransitivity; [eapply meet_comm_le |].
        etransitivity; [eapply meet_assoc_le |].
        etransitivity; [eapply meet_comm_le |].
        etransitivity; [eapply meet_assoc_le |].
        eapply meet_comm_le.
      }
    Qed.

    Global Instance meet_comm_eq : Comm eq meet.
    Proof using Type*.
      repeat intro. split; eapply meet_comm_le.
    Qed.

    Global Instance meet_unit_left_eq : LeftAbsorb eq unit meet.
    Proof using Type*.
      repeat intro. split.
      { apply meet_left_le. }
      { apply unit_le. }
    Qed.

    Global Instance meet_unit_right_eq : RightAbsorb eq unit meet.
    Proof using Type*.
      repeat intro. split.
      { apply meet_right_le. }
      { apply unit_le. }
    Qed.

    Global Instance meet_left_eq_proper : forall a, Proper (eq ==> eq) (meet a).
    Proof using Type*.
      intros a b c [H1 H2]. split; eapply meet_left_le_proper; eauto.
    Qed.

    Global Instance meet_right_eq_proper : forall a, Proper (eq ==> eq) (flip meet a).
    Proof using Type*.
      intros a b c [H1 H2]. split; eapply meet_right_le_proper; eauto.
    Qed.

    Global Instance meet_eq_proper : Proper (eq ==> eq ==> eq) meet.
    Proof using Type*.
      intros a b [H1 H2] c d [H3 H4]. split; eapply meet_le_proper; eauto.
    Qed.

    Global Instance meet_idemp_le : IdemP le meet.
    Proof. repeat intro. apply meet_left_le. Qed.
    Global Instance meet_idemp_eq : IdemP eq meet.
    Proof. repeat intro. split; [apply meet_idemp_le | apply meet_infimum; reflexivity]. Qed.

  End properties.

  (* Global Program Instance flip_add `{t car leR addO} : t leR (flip addO) := *)
  (*   Build_t _ leR (flip addO) unit le_PreOrder le_total _ _ _ _ _. *)
  (* Next Obligation. *)
  (*   destruct H. *)
  (*   intros a b c. simpl. *)
  (*   etransitivity; [rewrite add_comm_le0|]. *)
  (*   { eapply add_left_le_proper0. apply add_comm_le0. } *)
  (*   etransitivity; [eapply add_assoc_le0|]. *)
  (*   etransitivity; [rewrite add_comm_le0|]. *)
  (*   { eapply add_left_le_proper0. apply add_comm_le0. } *)
  (*   reflexivity. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   destruct H. *)
  (*   intros a b. simpl. apply add_comm_le0. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   destruct H. *)
  (*   intros a. simpl. etransitivity; [eapply add_comm_le0|]. apply add_unit_left_le0. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   destruct H. *)
  (*   etransitivity; [|eapply add_comm_le0]. apply add_base_left_le0. *)
  (* Qed. *)

End OrderedCM.

(** Quotient structure with respect to OrderedCM. *)
(** Reference: "Module Fuel" in Lilo and FOS. *)
Module quotient.

  Record t {A : Type} (leR : A -> A -> Prop) (addO : A -> A -> A) `{OrderedCM.t A leR addO} := {
      collection :> A -> Prop;
      generated : exists a0, forall a1, collection a1 <-> leR a0 a1;
    }.

  Global Program Definition from_monoid `{OrderedCM.t A leR addO} (a : A) : t leR addO :=
    Build_t _ _ _ _ (leR a) _.
  Next Obligation.
    intros. exists a. intros. auto.
  Qed.

  Definition le `{OrderedCM.t A leR addO} (s0 s1 : t leR addO) : Prop :=
    forall a, s1 a -> s0 a.

  Global Instance le_PreOrder `{OrderedCM.t A leR addO} : PreOrder le.
  Proof.
    split; repeat intro; eauto.
  Qed.

  Global Instance le_antisymm `{OrderedCM.t A leR addO} : AntiSymm (=) le.
  Proof.
    intros s0 s1 LE0 LE1. destruct s0, s1.
    assert (collection0 = collection1).
    { extensionality a. eapply propositional_extensionality.
      red in LE0, LE1. simpl in *. split; auto.
    }
    subst. f_equal. eapply proof_irrelevance.
  Qed.

  Lemma ext `{OrderedCM.t A leR addO} (s0 s1 : t leR addO) (EXT : forall a, s0 a <-> s1 a) : s0 = s1.
  Proof.
    eapply le_antisymm; repeat intro; eapply EXT; auto.
  Qed.

  Lemma from_monoid_exist `{OrderedCM.t A leR addO} (s : t leR addO) :
    exists a, s = from_monoid a.
  Proof.
    destruct (@generated _ _ _ H s) as [a0 H0].
    exists a0. eapply ext. intro. rewrite H0. simpl. auto.
  Qed.

  Lemma from_monoid_iff `{OrderedCM.t A leR addO} a0 a1 :
    from_monoid a0 a1 <-> leR a0 a1.
  Proof. simpl. auto. Qed.

  Lemma from_monoid_le `{OrderedCM.t A leR addO} a0 a1 :
    le (from_monoid a0) (from_monoid a1) <-> leR a0 a1.
  Proof.
    split.
    { repeat intro. rewrite <- from_monoid_iff. simpl.
      apply H0. simpl. reflexivity.
    }
    { repeat intro. simpl in *. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_eq `{OrderedCM.t A leR addO} a0 a1 :
    from_monoid a0 = from_monoid a1 <-> OrderedCM.eq a0 a1.
  Proof.
    split.
    { intros. split.
      { rewrite <- from_monoid_iff. rewrite H0. simpl. reflexivity. }
      { rewrite <- from_monoid_iff. rewrite <- H0. simpl. reflexivity. }
    }
    { intros [H1 H2]. eapply ext. intro. etransitivity.
      { eapply from_monoid_iff. }
      etransitivity.
      2:{ symmetry. eapply from_monoid_iff. }
      split; intro; etransitivity; eauto.
    }
  Qed.

  Global Program Definition add `{OrderedCM.t A leR addO} (s0 s1 : t leR addO) : t leR addO :=
    Build_t _ _ _ _ (fun a => exists a0 a1 (IN0: s0 a0) (IN1: s1 a1), leR (addO a0 a1) a) _.
  Next Obligation.
    destruct (from_monoid_exist s0) as [a H0].
    destruct (from_monoid_exist s1) as [a0 H1].
    subst. exists (addO a a0). intros. split.
    { intros [a2 [a3 [H1 [H2 H3]]]]. etransitivity.
      { eapply OrderedCM.add_le_proper; erewrite <- from_monoid_iff; eauto. }
      auto.
    }
    intros. repeat esplit.
    { erewrite from_monoid_iff. reflexivity. }
    { erewrite from_monoid_iff. reflexivity. }
    { eauto. }
  Qed.

  Global Program Definition join `{OrderedCM.t A leR addO} (s0 s1 : t leR addO) : t leR addO :=
    Build_t _ _ _ _ (fun a => s0 a /\ s1 a) _.
  Next Obligation.
    destruct (from_monoid_exist s0) as [a H0].
    destruct (from_monoid_exist s1) as [a0 H1].
    subst. destruct (OrderedCM.le_total a0 a).
    { exists a. intros. split.
      { intros [H1 H2]. erewrite <- from_monoid_iff. eauto. }
      { intros. split; auto. erewrite from_monoid_iff. etransitivity; eauto. }
    }
    { exists a0. intros. split.
      { intros [H1 H2]. erewrite <- from_monoid_iff. eauto. }
      { intros. split; auto. erewrite from_monoid_iff. etransitivity; eauto. }
    }
  Qed.

  Global Program Definition meet `{OrderedCM.t A leR addO} (s0 s1 : t leR addO) : t leR addO :=
    Build_t _ _ _ _ (fun a => s0 a \/ s1 a) _.
  Next Obligation.
    destruct (from_monoid_exist s0) as [a H0].
    destruct (from_monoid_exist s1) as [a0 H1].
    subst. destruct (OrderedCM.le_total a0 a).
    { exists a0. intros. split.
      { intros. erewrite ! from_monoid_iff in H1. destruct H1; auto. etransitivity; eauto. }
      { intros. right. erewrite from_monoid_iff. auto. }
    }
    { exists a. intros. split.
      { intros. erewrite ! from_monoid_iff in H1. destruct H1; auto. etransitivity; eauto. }
      { intros. left. erewrite from_monoid_iff. auto. }
    }
  Qed.

  Lemma from_monoid_add `{OrderedCM.t A leR addO} a0 a1 :
    add (from_monoid a0) (from_monoid a1) = from_monoid (addO a0 a1).
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0 as [a2 [a3 [H1 [H2 H3]]]]. etransitivity.
      { eapply OrderedCM.add_le_proper; eauto. }
      auto.
    }
    { intros. simpl in *. repeat esplit.
      { reflexivity. }
      { reflexivity. }
      { eauto. }
    }
  Qed.

  Lemma from_monoid_join_right `{OrderedCM.t A leR addO} a0 a1 (LE: leR a0 a1) :
    join (from_monoid a0) (from_monoid a1) = from_monoid a1.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0. auto. }
    { intros. simpl in *. split; auto. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_join_left `{OrderedCM.t A leR addO} a0 a1 (LE : leR a1 a0) :
    join (from_monoid a0) (from_monoid a1) = from_monoid a0.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0. auto. }
    { intros. simpl in *. split; auto. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_meet_left `{OrderedCM.t A leR addO} a0 a1 (LE : leR a0 a1) :
    meet (from_monoid a0) (from_monoid a1) = from_monoid a0.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0; auto. etransitivity; eauto. }
    { intros. simpl in *. left. auto. }
  Qed.

  Lemma from_monoid_meet_right `{OrderedCM.t A leR addO} a0 a1 (LE : leR a1 a0) :
    meet (from_monoid a0) (from_monoid a1) = from_monoid a1.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0; auto. etransitivity; eauto. }
    { intros. simpl in *. right. auto. }
  Qed.

  Lemma from_monoid_join `{OrderedCM.t A leR addO} a0 a1 :
    join (from_monoid a0) (from_monoid a1) = from_monoid (OrderedCM.join a0 a1).
  Proof.
    destruct (OrderedCM.le_total a0 a1).
    { rewrite from_monoid_join_right; eauto.
      apply from_monoid_eq.
      { split.
        { eapply OrderedCM.join_right_le. }
        { eapply OrderedCM.join_supremum; auto. reflexivity. }
      }
    }
    { rewrite from_monoid_join_left; eauto.
      apply from_monoid_eq.
      { split.
        { eapply OrderedCM.join_left_le. }
        { eapply OrderedCM.join_supremum; auto. reflexivity. }
      }
    }
  Qed.

  Lemma from_monoid_meet `{OrderedCM.t A leR addO} a0 a1 :
    meet (from_monoid a0) (from_monoid a1) = from_monoid (OrderedCM.meet a0 a1).
  Proof.
    destruct (OrderedCM.le_total a0 a1).
    { rewrite from_monoid_meet_left; eauto.
      apply from_monoid_eq.
      { split.
        { eapply OrderedCM.meet_infimum; auto. reflexivity. }
        { eapply OrderedCM.meet_left_le. }
      }
    }
    { rewrite from_monoid_meet_right; eauto.
      apply from_monoid_eq.
      { split.
        { eapply OrderedCM.meet_infimum; auto. reflexivity. }
        { eapply OrderedCM.meet_right_le. }
      }
    }
  Qed.

  Global Instance add_comm `{OrderedCM.t A leR addO} : Comm (=) add.
  Proof.
    repeat intro.
    destruct (from_monoid_exist x) as [a H0].
    destruct (from_monoid_exist y) as [a0 H1].
    subst.
    rewrite ! from_monoid_add.
    eapply from_monoid_eq. eapply OrderedCM.add_comm_eq.
  Qed.

  Global Instance join_comm `{OrderedCM.t A leR addO} : Comm (=) join.
  Proof.
    repeat intro.
    destruct (from_monoid_exist x) as [a H0].
    destruct (from_monoid_exist y) as [a0 H1].
    subst.
    rewrite ! from_monoid_join.
    eapply from_monoid_eq. eapply OrderedCM.join_comm_eq.
  Qed.

  Global Instance meet_comm `{OrderedCM.t A leR addO} : Comm (=) meet.
  Proof.
    repeat intro.
    destruct (from_monoid_exist x) as [a H0].
    destruct (from_monoid_exist y) as [a0 H1].
    subst.
    rewrite ! from_monoid_meet.
    eapply from_monoid_eq. eapply OrderedCM.meet_comm_eq.
  Qed.

  Global Instance add_assoc `{OrderedCM.t A leR addO} : Assoc (=) add.
  Proof.
    repeat intro.
    destruct (from_monoid_exist x) as [a H0].
    destruct (from_monoid_exist y) as [a0 H1].
    destruct (from_monoid_exist z) as [a1 H2].
    subst.
    rewrite ! from_monoid_add.
    eapply from_monoid_eq. eapply OrderedCM.add_assoc_eq.
  Qed.

  Global Instance join_assoc `{OrderedCM.t A leR addO} : Assoc (=) join.
  Proof.
    repeat intro.
    destruct (from_monoid_exist x) as [a H0].
    destruct (from_monoid_exist y) as [a0 H1].
    destruct (from_monoid_exist z) as [a1 H2].
    subst.
    rewrite ! from_monoid_join.
    eapply from_monoid_eq. eapply OrderedCM.join_assoc_eq.
  Qed.

  Global Instance meet_assoc `{OrderedCM.t A leR addO} : Assoc (=) meet.
  Proof.
    repeat intro.
    destruct (from_monoid_exist x) as [a H0].
    destruct (from_monoid_exist y) as [a0 H1].
    destruct (from_monoid_exist z) as [a1 H2].
    subst.
    rewrite ! from_monoid_meet.
    eapply from_monoid_eq. eapply OrderedCM.meet_assoc_eq.
  Qed.

  Definition unit `{OrderedCM.t A leR addO} := from_monoid (OrderedCM.unit).

  Lemma unit_le `{OrderedCM.t A leR addO} : forall a, le unit a.
  Proof.
    intros. destruct (from_monoid_exist a); subst. unfold unit. rewrite from_monoid_le. apply OrderedCM.unit_le.
  Qed.

  Global Instance add_unit_left_eq `{OrderedCM.t A leR addO} : LeftId (=) unit add.
  Proof.
    repeat intro. unfold unit. destruct (from_monoid_exist x); subst.
    rewrite from_monoid_add. apply from_monoid_eq. apply OrderedCM.add_unit_left_eq.
  Qed.
  Global Instance add_unit_left_le `{OrderedCM.t A leR addO} : LeftId le unit add.
  Proof. repeat intro. rewrite add_unit_left_eq. auto. Qed.
  Global Instance add_unit_right_eq `{OrderedCM.t A leR addO} : RightId (=) unit add.
  Proof.
    repeat intro. unfold unit. destruct (from_monoid_exist x); subst.
    rewrite from_monoid_add. apply from_monoid_eq. apply OrderedCM.add_unit_right_eq.
  Qed.
  Global Instance add_unit_right_le `{OrderedCM.t A leR addO} : RightId le unit add.
  Proof. repeat intro. rewrite add_unit_right_eq. auto. Qed.

  Global Instance join_unit_left_eq `{OrderedCM.t A leR addO} : LeftId (=) unit join.
  Proof.
    repeat intro. unfold unit. destruct (from_monoid_exist x); subst.
    rewrite from_monoid_join. apply from_monoid_eq. apply OrderedCM.join_unit_left_eq.
  Qed.
  Global Instance join_unit_left_le `{OrderedCM.t A leR addO} : LeftId le unit join.
  Proof. repeat intro. rewrite join_unit_left_eq. auto. Qed.
  Global Instance join_unit_right_eq `{OrderedCM.t A leR addO} : RightId (=) unit join.
  Proof.
    repeat intro. unfold unit. destruct (from_monoid_exist x); subst.
    rewrite from_monoid_join. apply from_monoid_eq. apply OrderedCM.join_unit_right_eq.
  Qed.
  Global Instance join_unit_right_le `{OrderedCM.t A leR addO} : RightId le unit join.
  Proof. repeat intro. rewrite join_unit_right_eq. auto. Qed.

  Global Instance meet_unit_left_eq `{OrderedCM.t A leR addO} : LeftAbsorb (=) unit meet.
  Proof.
    repeat intro. unfold unit. destruct (from_monoid_exist x); subst.
    rewrite from_monoid_meet. apply from_monoid_eq. apply OrderedCM.meet_unit_left_eq.
  Qed.
  Global Instance meet_left_le `{OrderedCM.t A leR addO} : forall a, LeftAbsorb le a meet.
  Proof. repeat intro. simpl. auto. Qed.
  Global Instance meet_unit_right_eq `{OrderedCM.t A leR addO} : RightAbsorb (=) unit meet.
  Proof.
    repeat intro. unfold unit. destruct (from_monoid_exist x); subst.
    rewrite from_monoid_meet. apply from_monoid_eq. apply OrderedCM.meet_unit_right_eq.
  Qed.
  Global Instance meet_right_le `{OrderedCM.t A leR addO} : forall a, RightAbsorb le a meet.
  Proof. repeat intro. simpl. auto. Qed.

  Global Instance add_le_proper `{OrderedCM.t A leR addO} : Proper (le ==> le ==> le) add.
  Proof.
    intros a b LE c d LE0.
    destruct (from_monoid_exist a); destruct (from_monoid_exist b);
      destruct (from_monoid_exist c); destruct (from_monoid_exist d); subst.
    rewrite !from_monoid_add. rewrite from_monoid_le.
    apply OrderedCM.add_le_proper; apply from_monoid_le; auto.
  Qed.
  Global Instance add_eq_proper `{OrderedCM.t A leR addO} : Proper (eq ==> eq ==> eq) add.
  Proof.
    intros a b LE c d LE0.
    destruct (from_monoid_exist a); destruct (from_monoid_exist b);
      destruct (from_monoid_exist c); destruct (from_monoid_exist d); subst.
    rewrite !from_monoid_add. rewrite from_monoid_eq.
    apply OrderedCM.add_eq_proper; apply from_monoid_eq; auto.
  Qed.
  Global Instance add_left_le_proper `{OrderedCM.t A leR addO} : forall a, Proper (le ==> le) (add a).
  Proof. intros a x y H0. apply add_le_proper; [reflexivity | auto]. Qed.
  Global Instance add_left_eq_proper `{OrderedCM.t A leR addO} : forall a, Proper (eq ==> eq) (add a).
  Proof. intros a x y H0. apply add_eq_proper; [reflexivity | auto]. Qed.
  Global Instance add_right_le_proper `{OrderedCM.t A leR addO} : forall a, Proper (le ==> le) (flip add a).
  Proof. intros a x y H0. apply add_le_proper; [auto | reflexivity]. Qed.
  Global Instance add_right_eq_proper `{OrderedCM.t A leR addO} : forall a, Proper (eq ==> eq) (flip add a).
  Proof. intros a x y H0. apply add_eq_proper; [auto | reflexivity]. Qed.

  Global Instance join_le_proper `{OrderedCM.t A leR addO} : Proper (le ==> le ==> le) join.
  Proof.
    intros a b LE c d LE0.
    destruct (from_monoid_exist a); destruct (from_monoid_exist b);
      destruct (from_monoid_exist c); destruct (from_monoid_exist d); subst.
    rewrite !from_monoid_join. rewrite from_monoid_le.
    apply OrderedCM.join_le_proper; apply from_monoid_le; auto.
  Qed.
  Global Instance join_eq_proper `{OrderedCM.t A leR addO} : Proper (eq ==> eq ==> eq) join.
  Proof.
    intros a b LE c d LE0.
    destruct (from_monoid_exist a); destruct (from_monoid_exist b);
      destruct (from_monoid_exist c); destruct (from_monoid_exist d); subst.
    rewrite !from_monoid_join. rewrite from_monoid_eq.
    apply OrderedCM.join_eq_proper; apply from_monoid_eq; auto.
  Qed.
  Global Instance join_left_le_proper `{OrderedCM.t A leR joinO} : forall a, Proper (le ==> le) (join a).
  Proof. intros a x y H0. apply join_le_proper; [reflexivity | auto]. Qed.
  Global Instance join_left_eq_proper `{OrderedCM.t A leR joinO} : forall a, Proper (eq ==> eq) (join a).
  Proof. intros a x y H0. apply join_eq_proper; [reflexivity | auto]. Qed.
  Global Instance join_right_le_proper `{OrderedCM.t A leR joinO} : forall a, Proper (le ==> le) (flip join a).
  Proof. intros a x y H0. apply join_le_proper; [auto | reflexivity]. Qed.
  Global Instance join_right_eq_proper `{OrderedCM.t A leR joinO} : forall a, Proper (eq ==> eq) (flip join a).
  Proof. intros a x y H0. apply join_eq_proper; [auto | reflexivity]. Qed.

  Global Instance meet_le_proper `{OrderedCM.t A leR addO} : Proper (le ==> le ==> le) meet.
  Proof.
    intros a b LE c d LE0.
    destruct (from_monoid_exist a); destruct (from_monoid_exist b);
      destruct (from_monoid_exist c); destruct (from_monoid_exist d); subst.
    rewrite !from_monoid_meet. rewrite from_monoid_le.
    apply OrderedCM.meet_le_proper; apply from_monoid_le; auto.
  Qed.
  Global Instance meet_eq_proper `{OrderedCM.t A leR addO} : Proper (eq ==> eq ==> eq) meet.
  Proof.
    intros a b LE c d LE0.
    destruct (from_monoid_exist a); destruct (from_monoid_exist b);
      destruct (from_monoid_exist c); destruct (from_monoid_exist d); subst.
    rewrite !from_monoid_meet. rewrite from_monoid_eq.
    apply OrderedCM.meet_eq_proper; apply from_monoid_eq; auto.
  Qed.
  Global Instance meet_left_le_proper `{OrderedCM.t A leR meetO} : forall a, Proper (le ==> le) (meet a).
  Proof. intros a x y H0. apply meet_le_proper; [reflexivity | auto]. Qed.
  Global Instance meet_left_eq_proper `{OrderedCM.t A leR meetO} : forall a, Proper (eq ==> eq) (meet a).
  Proof. intros a x y H0. apply meet_eq_proper; [reflexivity | auto]. Qed.
  Global Instance meet_right_le_proper `{OrderedCM.t A leR meetO} : forall a, Proper (le ==> le) (flip meet a).
  Proof. intros a x y H0. apply meet_le_proper; [auto | reflexivity]. Qed.
  Global Instance meet_right_eq_proper `{OrderedCM.t A leR meetO} : forall a, Proper (eq ==> eq) (flip meet a).
  Proof. intros a x y H0. apply meet_eq_proper; [auto | reflexivity]. Qed.

  Lemma join_supremum `{OrderedCM.t A leR addO} a0 a1 a (LE0: le a0 a) (LE1: le a1 a) : le (join a0 a1) a.
  Proof using Type*.
    destruct (from_monoid_exist a); destruct (from_monoid_exist a0); destruct (from_monoid_exist a1); subst.    
    rewrite from_monoid_join, !from_monoid_le in *. apply OrderedCM.join_supremum; auto.
  Qed.

  Lemma meet_infimum `{OrderedCM.t A leR addO} a0 a1 a (LE0: le a a0) (LE1: le a a1) : le a (meet a0 a1).
  Proof using Type*.
    destruct (from_monoid_exist a); destruct (from_monoid_exist a0); destruct (from_monoid_exist a1); subst.    
    rewrite from_monoid_meet, !from_monoid_le in *. apply OrderedCM.meet_infimum; auto.
  Qed.

  Lemma join_left_le `{OrderedCM.t A leR addO} a0 a1 : le a0 (join a0 a1).
  Proof using Type*.
    destruct (from_monoid_exist a0); destruct (from_monoid_exist a1); subst.
    rewrite from_monoid_join, from_monoid_le. apply OrderedCM.join_left_le.
  Qed.
  Lemma join_right_le `{OrderedCM.t A leR addO} a0 a1 : le a1 (join a0 a1).
  Proof using Type*.
    destruct (from_monoid_exist a0); destruct (from_monoid_exist a1); subst.
    rewrite from_monoid_join, from_monoid_le. apply OrderedCM.join_right_le.
  Qed.

  Global Instance join_idemp_le `{OrderedCM.t A leR addO} : IdemP le join.
  Proof. intro x.  apply join_supremum; reflexivity. Qed.
  Global Instance join_idemp_eq `{OrderedCM.t A leR addO} : IdemP (=) join.
  Proof. intro x. eapply le_antisymm; [apply join_idemp_le | apply join_left_le]. Qed.

  Global Instance meet_idemp_le `{OrderedCM.t A leR addO} : IdemP le meet.
  Proof. intro x.  apply meet_left_le; reflexivity. Qed.
  Global Instance meet_idemp_eq `{OrderedCM.t A leR addO} : IdemP (=) meet.
  Proof. intro x. eapply le_antisymm; [apply meet_idemp_le | apply meet_infimum; reflexivity]. Qed.

End quotient.
Arguments quotient.t {A} leR addO {_}.

(** Reference: "Module CounterRA" in Lilo and FOS. *)
Module partition.

  Record t {A : Type} (leR : A -> A -> Prop) (addO : A -> A -> A) `{OrderedCM.t A leR addO} := {
      collection :> A -> Prop;
      closed: forall a0 a1 (LE : leR a0 a1),
        collection a1 -> collection a0;
    }.

  Lemma ext `{OrderedCM.t A leR addO} (p0 p1 : t leR addO) (EXT: forall a, p0 a <-> p1 a) : p0 = p1.
  Proof.
    destruct p0, p1. assert (collection0 = collection1).
    { extensionality a. eapply propositional_extensionality. apply EXT. }
    { subst. f_equal. apply proof_irrelevance. }
  Qed.

  Program Definition meet `{OrderedCM.t A leR addO} (p0 p1 : t leR addO): t leR addO :=
    Build_t _ _ _ _ (fun a => p0 a /\ p1 a) _.
  Next Obligation. split; eapply closed; eauto. Qed.

  Program Definition top `{OrderedCM.t A leR addO} : t leR addO :=
    Build_t _ _ _ _ (fun _ => True) _.

  Program Definition from_monoid `{OrderedCM.t A leR addO} (a : A): t leR addO :=
    Build_t _ _ _ _ (fun a' => leR a' a) _.
  Next Obligation. etransitivity; eauto. Qed.

  Lemma from_monoid_iff `{OrderedCM.t A leR addO} a0 a1 :
    from_monoid a0 a1 <-> leR a1 a0.
  Proof.
    simpl. auto.
  Qed.

  Lemma from_monoid_eq `{OrderedCM.t A leR addO} a0 a1 :
    from_monoid a0 = from_monoid a1 <-> OrderedCM.eq a0 a1.
  Proof.
    split.
    { intros. split.
      { rewrite <- from_monoid_iff. rewrite <- H0. simpl. reflexivity. }
      { rewrite <- from_monoid_iff. rewrite H0. simpl. reflexivity. }
    }
    { intros [H1 H2]. eapply ext. intro. etransitivity.
      { eapply from_monoid_iff. }
      etransitivity.
      2:{ symmetry. eapply from_monoid_iff. }
      split; intro; etransitivity; eauto.
    }
  Qed.

  Lemma from_monoid_meet_left `{OrderedCM.t A leR addO} a0 a1 (LE : leR a0 a1) :
    meet (from_monoid a0) (from_monoid a1) = from_monoid a0.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0; auto. }
    { intros. simpl in *. split; [auto|]. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_meet_right `{OrderedCM.t A leR addO} a0 a1 (LE : leR a1 a0) :
    meet (from_monoid a0) (from_monoid a1) = from_monoid a1.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0; auto. }
    { intros. simpl in *. split; [|auto]. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_meet `{OrderedCM.t A leR addO} a0 a1 :
    meet (from_monoid a0) (from_monoid a1) = from_monoid (OrderedCM.meet a0 a1).
  Proof.
    destruct (OrderedCM.le_total a0 a1).
    { rewrite from_monoid_meet_left; eauto.
      apply from_monoid_eq.
      { split.
        { eapply OrderedCM.meet_infimum; auto. reflexivity. }
        { eapply OrderedCM.meet_left_le. }
      }
    }
    { rewrite from_monoid_meet_right; eauto.
      apply from_monoid_eq.
      { split.
        { eapply OrderedCM.meet_infimum; auto. reflexivity. }
        { eapply OrderedCM.meet_right_le. }
      }
    }
  Qed.

  Global Instance meet_comm `{OrderedCM.t A leR addO} : Comm (=) meet.
  Proof.
    repeat intro.
    apply ext. split; simpl; intros [H0 H1]; auto.
  Qed.

  Global Instance meet_assoc `{OrderedCM.t A leR addO} : Assoc (=) meet.
  Proof.
    repeat intro.
    apply ext. split; simpl; [intros (X&Y&Z) | intros ((X&Y)&Z)]; auto.
  Qed.

  Global Instance meet_top_left_eq `{OrderedCM.t A leR addO} : LeftId (=) top meet.
  Proof.
    repeat intro. apply ext. simpl. split; [intros [_ H0]; auto | auto].
  Qed.
  Global Instance meet_top_right_eq `{OrderedCM.t A leR addO} : RightId (=) top meet.
  Proof.
    repeat intro. apply ext. simpl. split; [intros [H0 _]; auto | auto].
  Qed.

  Global Instance meet_left_eq_proper `{OrderedCM.t A leR addO} : forall a, Proper (eq ==> eq) (meet a).
  Proof. intros a x y H0. subst. auto. Qed.
  Global Instance meet_right_eq_proper `{OrderedCM.t A leR addO} : forall a, Proper (eq ==> eq) (flip meet a).
  Proof. intros a x y H0. subst. auto. Qed.
  Global Instance meet_eq_proper `{OrderedCM.t A leR addO} : Proper (eq ==> eq ==> eq) meet.
  Proof. intros a b H0 c d H1. subst; auto. Qed.

  Global Instance meet_idemp_eq `{OrderedCM.t A leR addO} : IdemP (=) meet.
  Proof. intro x. apply ext. simpl. split; [intros [H0 _]; auto | auto]. Qed.

End partition.
Arguments partition.t {A} leR addO {_}.
