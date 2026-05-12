From stdpp Require Import base.
From liris Require Import axioms.
From Coq Require Import Program.

(** The less-than-or-equal-to-based Ordered Commutative Monoid class. *)
(** Reference: "Module OCM" in Lilo and FOS. *)
Module OCM.
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

  Global Instance eq_def `{t car leR addO} : Equiv car := λ a0 a1, leR a0 a1 /\ leR a1 a0.
  Definition eq `{t car leR addO} := (@equiv _ eq_def).

  Section properties.
    Context `{t car leR addO}.

    Local Notation le := leR.
    Local Notation add := addO.

    Global Instance eq_Equivalence : Equivalence eq.
    Proof using Type*.
      split.
      - intros x. split; reflexivity.
      - intros x y [H1 H2]. split; auto.
      - intros x y z [Ha1 Ha2] [Hb1 Hb2]. split; etransitivity; eauto.
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

    Global Instance eq_le_antisymm : AntiSymm eq le.
    Proof using Type*. intros x y H1 H2. split; auto. Qed.

    Global Instance eq_le_proper : Proper (eq ==> eq ==> iff) le.
    Proof using Type*.
      repeat intro. destruct H0, H1. split; intros; repeat (etransitivity; eauto).
    Qed.

  End properties.

  Class pack (car : Type) := {
      leR : car -> car -> Prop;
      addO : car -> car -> car;
      #[global] ocm :: @t car leR addO;
    }.

End OCM.

(** Quotient structure with respect to OCM. *)
(** Reference: "Module Fuel" in Lilo and FOS. *)
Module quotient.

  Record t {A : Type} (leR : A -> A -> Prop) (addO : A -> A -> A) `{OCM.t A leR addO} := {
      collection :> A -> Prop;
      generated : exists a0, forall a1, collection a1 <-> leR a0 a1;
    }.

  Global Program Definition from_monoid `{OCM.t A leR addO} (a : A) : t leR addO :=
    Build_t _ _ _ _ (leR a) _.
  Next Obligation.
    intros. exists a. intros. auto.
  Qed.

  Definition le `{OCM.t A leR addO} (s0 s1 : t leR addO) : Prop :=
    forall a, s1 a -> s0 a.

  Global Instance le_PreOrder `{OCM.t A leR addO} : PreOrder le.
  Proof.
    split; repeat intro; eauto.
  Qed.

  Global Instance le_antisymm `{OCM.t A leR addO} : AntiSymm (=) le.
  Proof.
    intros s0 s1 LE0 LE1. destruct s0, s1.
    assert (collection0 = collection1).
    { extensionality a. eapply propositional_extensionality.
      red in LE0, LE1. simpl in *. split; auto.
    }
    subst. f_equal. eapply proof_irrelevance.
  Qed.

  Lemma ext `{OCM.t A leR addO} (s0 s1 : t leR addO) (EXT : forall a, s0 a <-> s1 a) : s0 = s1.
  Proof.
    eapply le_antisymm; repeat intro; eapply EXT; auto.
  Qed.

  Lemma from_monoid_exist `{OCM.t A leR addO} (s : t leR addO) :
    exists a, s = from_monoid a.
  Proof.
    destruct (@generated _ _ _ H s) as [a0 H0].
    exists a0. eapply ext. intro. rewrite H0. simpl. auto.
  Qed.

  Lemma from_monoid_iff `{OCM.t A leR addO} a0 a1 :
    from_monoid a0 a1 <-> leR a0 a1.
  Proof. simpl. auto. Qed.

  Lemma from_monoid_le `{OCM.t A leR addO} a0 a1 :
    le (from_monoid a0) (from_monoid a1) <-> leR a0 a1.
  Proof.
    split.
    { repeat intro. rewrite <- from_monoid_iff. simpl.
      apply H0. simpl. reflexivity.
    }
    { repeat intro. simpl in *. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_eq `{OCM.t A leR addO} a0 a1 :
    from_monoid a0 = from_monoid a1 <-> OCM.eq a0 a1.
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

  Global Program Definition add `{OCM.t A leR addO} (s0 s1 : t leR addO) : t leR addO :=
    Build_t _ _ _ _ (fun a => exists a0 a1 (IN0: s0 a0) (IN1: s1 a1), leR (addO a0 a1) a) _.
  Next Obligation.
    destruct (from_monoid_exist s0) as [a H0].
    destruct (from_monoid_exist s1) as [a0 H1].
    subst. exists (addO a a0). intros. split.
    { intros [a2 [a3 [H1 [H2 H3]]]]. etransitivity.
      { eapply OCM.add_le_proper; erewrite <- from_monoid_iff; eauto. }
      auto.
    }
    intros. repeat esplit.
    { erewrite from_monoid_iff. reflexivity. }
    { erewrite from_monoid_iff. reflexivity. }
    { eauto. }
  Qed.

  Global Program Definition join `{OCM.t A leR addO} (s0 s1 : t leR addO) : t leR addO :=
    Build_t _ _ _ _ (fun a => s0 a /\ s1 a) _.
  Next Obligation.
    destruct (from_monoid_exist s0) as [a H0].
    destruct (from_monoid_exist s1) as [a0 H1].
    subst. destruct (OCM.le_total a0 a).
    { exists a. intros. split.
      { intros [H1 H2]. erewrite <- from_monoid_iff. eauto. }
      { intros. split; auto. erewrite from_monoid_iff. etransitivity; eauto. }
    }
    { exists a0. intros. split.
      { intros [H1 H2]. erewrite <- from_monoid_iff. eauto. }
      { intros. split; auto. erewrite from_monoid_iff. etransitivity; eauto. }
    }
  Qed.

  Global Program Definition meet `{OCM.t A leR addO} (s0 s1 : t leR addO) : t leR addO :=
    Build_t _ _ _ _ (fun a => s0 a \/ s1 a) _.
  Next Obligation.
    destruct (from_monoid_exist s0) as [a H0].
    destruct (from_monoid_exist s1) as [a0 H1].
    subst. destruct (OCM.le_total a0 a).
    { exists a0. intros. split.
      { intros. erewrite ! from_monoid_iff in H1. destruct H1; auto. etransitivity; eauto. }
      { intros. right. erewrite from_monoid_iff. auto. }
    }
    { exists a. intros. split.
      { intros. erewrite ! from_monoid_iff in H1. destruct H1; auto. etransitivity; eauto. }
      { intros. left. erewrite from_monoid_iff. auto. }
    }
  Qed.

  Lemma from_monoid_add `{OCM.t A leR addO} a0 a1 :
    add (from_monoid a0) (from_monoid a1) = from_monoid (addO a0 a1).
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0 as [a2 [a3 [H1 [H2 H3]]]]. etransitivity.
      { eapply OCM.add_le_proper; eauto. }
      auto.
    }
    { intros. simpl in *. repeat esplit.
      { reflexivity. }
      { reflexivity. }
      { eauto. }
    }
  Qed.

  Lemma from_monoid_join_right `{OCM.t A leR addO} a0 a1 (LE: leR a0 a1) :
    join (from_monoid a0) (from_monoid a1) = from_monoid a1.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0. auto. }
    { intros. simpl in *. split; auto. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_join_left `{OCM.t A leR addO} a0 a1 (LE : leR a1 a0) :
    join (from_monoid a0) (from_monoid a1) = from_monoid a0.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0. auto. }
    { intros. simpl in *. split; auto. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_meet_left `{OCM.t A leR addO} a0 a1 (LE : leR a0 a1) :
    meet (from_monoid a0) (from_monoid a1) = from_monoid a0.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0; auto. etransitivity; eauto. }
    { intros. simpl in *. left. auto. }
  Qed.

  Lemma from_monoid_meet_right `{OCM.t A leR addO} a0 a1 (LE : leR a1 a0) :
    meet (from_monoid a0) (from_monoid a1) = from_monoid a1.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0; auto. etransitivity; eauto. }
    { intros. simpl in *. right. auto. }
  Qed.

  Global Instance add_comm `{OCM.t A leR addO} : Comm (=) add.
  Proof.
    repeat intro.
    destruct (from_monoid_exist x) as [a H0].
    destruct (from_monoid_exist y) as [a0 H1].
    subst.
    rewrite ! from_monoid_add.
    eapply from_monoid_eq. eapply OCM.add_comm_eq.
  Qed.

  Global Instance join_comm `{OCM.t A leR addO} : Comm (=) join.
  Proof.
    repeat intro. apply ext. split; intros Hj; destruct Hj; split; auto.
  Qed.

  Global Instance meet_comm `{OCM.t A leR addO} : Comm (=) meet.
  Proof.
    repeat intro. apply ext. split; intros Hm.
    - destruct Hm; [right; auto | left; auto].
    - destruct Hm; [right; auto | left; auto].
  Qed.

  Global Instance add_assoc `{OCM.t A leR addO} : Assoc (=) add.
  Proof.
    repeat intro.
    destruct (from_monoid_exist x) as [a H0].
    destruct (from_monoid_exist y) as [a0 H1].
    destruct (from_monoid_exist z) as [a1 H2].
    subst.
    rewrite ! from_monoid_add.
    eapply from_monoid_eq. eapply OCM.add_assoc_eq.
  Qed.

  Global Instance join_assoc `{OCM.t A leR addO} : Assoc (=) join.
  Proof.
    repeat intro. apply ext. split; intros Hj; destruct Hj.
    - destruct H1. repeat split; auto.
    - destruct H0. repeat split; auto.
  Qed.

  Global Instance meet_assoc `{OCM.t A leR addO} : Assoc (=) meet.
  Proof.
    repeat intro. apply ext. split; intros Hm.
    - destruct Hm.
      + do 2 left. auto.
      + destruct H0; [left; right; auto | right; auto].
    - destruct Hm.
      + destruct H0; [left; auto | right; left; auto].
      + do 2 right; auto.
  Qed.

  Definition unit `{OCM.t A leR addO} := from_monoid (OCM.unit).

  Lemma unit_le `{OCM.t A leR addO} : forall a, le unit a.
  Proof.
    intros. destruct (from_monoid_exist a); subst. unfold unit. rewrite from_monoid_le. apply OCM.unit_le.
  Qed.

  Global Instance add_unit_left_eq `{OCM.t A leR addO} : LeftId (=) unit add.
  Proof.
    repeat intro. unfold unit. destruct (from_monoid_exist x); subst.
    rewrite from_monoid_add. apply from_monoid_eq. apply OCM.add_unit_left_eq.
  Qed.
  Global Instance add_unit_left_le `{OCM.t A leR addO} : LeftId le unit add.
  Proof. repeat intro. rewrite add_unit_left_eq. auto. Qed.
  Global Instance add_unit_right_eq `{OCM.t A leR addO} : RightId (=) unit add.
  Proof.
    repeat intro. unfold unit. destruct (from_monoid_exist x); subst.
    rewrite from_monoid_add. apply from_monoid_eq. apply OCM.add_unit_right_eq.
  Qed.
  Global Instance add_unit_right_le `{OCM.t A leR addO} : RightId le unit add.
  Proof. repeat intro. rewrite add_unit_right_eq. auto. Qed.

  Global Instance join_unit_left_eq `{OCM.t A leR addO} : LeftId (=) unit join.
  Proof.
    repeat intro. apply ext. split; intros Hj.
    - destruct Hj; auto.
    - split; auto. eapply unit_le; eauto.
  Qed.
  Global Instance join_unit_left_le `{OCM.t A leR addO} : LeftId le unit join.
  Proof. repeat intro. rewrite join_unit_left_eq. auto. Qed.
  Global Instance join_unit_right_eq `{OCM.t A leR addO} : RightId (=) unit join.
  Proof.
    repeat intro. apply ext. split; intros Hj.
    - destruct Hj; auto.
    - split; auto. eapply unit_le; eauto.
  Qed.
  Global Instance join_unit_right_le `{OCM.t A leR addO} : RightId le unit join.
  Proof. repeat intro. rewrite join_unit_right_eq. auto. Qed.

  Global Instance meet_unit_left_eq `{OCM.t A leR addO} : LeftAbsorb (=) unit meet.
  Proof.
    repeat intro. apply ext. split; intros Hm.
    - eapply unit_le; eauto.
    - left; auto.
  Qed.
  Global Instance meet_left_le `{OCM.t A leR addO} : forall a, LeftAbsorb le a meet.
  Proof. repeat intro. simpl. auto. Qed.
  Global Instance meet_unit_right_eq `{OCM.t A leR addO} : RightAbsorb (=) unit meet.
  Proof.
    repeat intro. apply ext. split; intros Hm.
    - eapply unit_le; eauto.
    - right; auto.
  Qed.
  Global Instance meet_right_le `{OCM.t A leR addO} : forall a, RightAbsorb le a meet.
  Proof. repeat intro. simpl. auto. Qed.

  Global Instance add_le_proper `{OCM.t A leR addO} : Proper (le ==> le ==> le) add.
  Proof.
    intros a b LE c d LE0.
    destruct (from_monoid_exist a); destruct (from_monoid_exist b);
      destruct (from_monoid_exist c); destruct (from_monoid_exist d); subst.
    rewrite !from_monoid_add. rewrite from_monoid_le.
    apply OCM.add_le_proper; apply from_monoid_le; auto.
  Qed.
  Global Instance add_eq_proper `{OCM.t A leR addO} : Proper (eq ==> eq ==> eq) add.
  Proof.
    intros a b LE c d LE0.
    destruct (from_monoid_exist a); destruct (from_monoid_exist b);
      destruct (from_monoid_exist c); destruct (from_monoid_exist d); subst.
    rewrite !from_monoid_add. rewrite from_monoid_eq.
    apply OCM.add_eq_proper; apply from_monoid_eq; auto.
  Qed.
  Global Instance add_left_le_proper `{OCM.t A leR addO} : forall a, Proper (le ==> le) (add a).
  Proof. intros a x y H0. apply add_le_proper; [reflexivity | auto]. Qed.
  Global Instance add_left_eq_proper `{OCM.t A leR addO} : forall a, Proper (eq ==> eq) (add a).
  Proof. intros a x y H0. apply add_eq_proper; [reflexivity | auto]. Qed.
  Global Instance add_right_le_proper `{OCM.t A leR addO} : forall a, Proper (le ==> le) (flip add a).
  Proof. intros a x y H0. apply add_le_proper; [auto | reflexivity]. Qed.
  Global Instance add_right_eq_proper `{OCM.t A leR addO} : forall a, Proper (eq ==> eq) (flip add a).
  Proof. intros a x y H0. apply add_eq_proper; [auto | reflexivity]. Qed.

  Global Instance join_le_proper `{OCM.t A leR addO} : Proper (le ==> le ==> le) join.
  Proof. intros a b LE c d LE0 x Hj. destruct Hj. split; eauto. Qed.
  Global Instance join_eq_proper `{OCM.t A leR addO} : Proper (eq ==> eq ==> eq) join.
  Proof. intros a b LE c d LE0. subst; auto. Qed.
  Global Instance join_left_le_proper `{OCM.t A leR joinO} : forall a, Proper (le ==> le) (join a).
  Proof. intros a x y H0. apply join_le_proper; [reflexivity | auto]. Qed.
  Global Instance join_left_eq_proper `{OCM.t A leR joinO} : forall a, Proper (eq ==> eq) (join a).
  Proof. intros a x y H0. apply join_eq_proper; [reflexivity | auto]. Qed.
  Global Instance join_right_le_proper `{OCM.t A leR joinO} : forall a, Proper (le ==> le) (flip join a).
  Proof. intros a x y H0. apply join_le_proper; [auto | reflexivity]. Qed.
  Global Instance join_right_eq_proper `{OCM.t A leR joinO} : forall a, Proper (eq ==> eq) (flip join a).
  Proof. intros a x y H0. apply join_eq_proper; [auto | reflexivity]. Qed.

  Global Instance meet_le_proper `{OCM.t A leR addO} : Proper (le ==> le ==> le) meet.
  Proof. intros a b LE c d LE0 x Hm. destruct Hm; [left; auto | right; auto]. Qed.
  Global Instance meet_eq_proper `{OCM.t A leR addO} : Proper (eq ==> eq ==> eq) meet.
  Proof. intros a b LE c d LE0. subst; auto. Qed.
  Global Instance meet_left_le_proper `{OCM.t A leR meetO} : forall a, Proper (le ==> le) (meet a).
  Proof. intros a x y H0. apply meet_le_proper; [reflexivity | auto]. Qed.
  Global Instance meet_left_eq_proper `{OCM.t A leR meetO} : forall a, Proper (eq ==> eq) (meet a).
  Proof. intros a x y H0. apply meet_eq_proper; [reflexivity | auto]. Qed.
  Global Instance meet_right_le_proper `{OCM.t A leR meetO} : forall a, Proper (le ==> le) (flip meet a).
  Proof. intros a x y H0. apply meet_le_proper; [auto | reflexivity]. Qed.
  Global Instance meet_right_eq_proper `{OCM.t A leR meetO} : forall a, Proper (eq ==> eq) (flip meet a).
  Proof. intros a x y H0. apply meet_eq_proper; [auto | reflexivity]. Qed.

  Lemma join_supremum `{OCM.t A leR addO} a0 a1 a (LE0: le a0 a) (LE1: le a1 a) : le (join a0 a1) a.
  Proof. intros x Ha. split; eauto. Qed.

  Lemma meet_infimum `{OCM.t A leR addO} a0 a1 a (LE0: le a a0) (LE1: le a a1) : le a (meet a0 a1).
  Proof. intros x Ha. destruct Ha; eauto. Qed.

  Lemma join_left_le `{OCM.t A leR addO} a0 a1 : le a0 (join a0 a1).
  Proof. intros x Ha. destruct Ha; auto. Qed.
  Lemma join_right_le `{OCM.t A leR addO} a0 a1 : le a1 (join a0 a1).
  Proof. intros x Ha. destruct Ha; auto. Qed.

  Global Instance join_idemp_le `{OCM.t A leR addO} : IdemP le join.
  Proof. intro x.  apply join_supremum; reflexivity. Qed.
  Global Instance join_idemp_eq `{OCM.t A leR addO} : IdemP (=) join.
  Proof. intro x. eapply le_antisymm; [apply join_idemp_le | apply join_left_le]. Qed.

  Global Instance meet_idemp_le `{OCM.t A leR addO} : IdemP le meet.
  Proof. intro x.  apply meet_left_le; reflexivity. Qed.
  Global Instance meet_idemp_eq `{OCM.t A leR addO} : IdemP (=) meet.
  Proof. intro x. eapply le_antisymm; [apply meet_idemp_le | apply meet_infimum; reflexivity]. Qed.

End quotient.
Arguments quotient.t {A} leR addO {_}.

(** Reference: "Module CounterRA" in Lilo and FOS. *)
Module partition.

  Record t {A : Type} (leR : A -> A -> Prop) (addO : A -> A -> A) `{OCM.t A leR addO} := {
      collection :> A -> Prop;
      closed: forall a0 a1 (LE : leR a0 a1),
        collection a1 -> collection a0;
    }.

  Lemma ext `{OCM.t A leR addO} (p0 p1 : t leR addO) (EXT: forall a, p0 a <-> p1 a) : p0 = p1.
  Proof.
    destruct p0, p1. assert (collection0 = collection1).
    { extensionality a. eapply propositional_extensionality. apply EXT. }
    { subst. f_equal. apply proof_irrelevance. }
  Qed.

  Program Definition meet `{OCM.t A leR addO} (p0 p1 : t leR addO): t leR addO :=
    Build_t _ _ _ _ (fun a => p0 a /\ p1 a) _.
  Next Obligation. split; eapply closed; eauto. Qed.

  Program Definition top `{OCM.t A leR addO} : t leR addO :=
    Build_t _ _ _ _ (fun _ => True) _.

  Program Definition from_monoid `{OCM.t A leR addO} (a : A): t leR addO :=
    Build_t _ _ _ _ (fun a' => leR a' a) _.
  Next Obligation. etransitivity; eauto. Qed.

  Lemma from_monoid_iff `{OCM.t A leR addO} a0 a1 :
    from_monoid a0 a1 <-> leR a1 a0.
  Proof.
    simpl. auto.
  Qed.

  Lemma from_monoid_eq `{OCM.t A leR addO} a0 a1 :
    from_monoid a0 = from_monoid a1 <-> OCM.eq a0 a1.
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

  Lemma from_monoid_meet_left `{OCM.t A leR addO} a0 a1 (LE : leR a0 a1) :
    meet (from_monoid a0) (from_monoid a1) = from_monoid a0.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0; auto. }
    { intros. simpl in *. split; [auto|]. etransitivity; eauto. }
  Qed.

  Lemma from_monoid_meet_right `{OCM.t A leR addO} a0 a1 (LE : leR a1 a0) :
    meet (from_monoid a0) (from_monoid a1) = from_monoid a1.
  Proof.
    eapply ext. intros. split.
    { intros. simpl in *. destruct H0; auto. }
    { intros. simpl in *. split; [|auto]. etransitivity; eauto. }
  Qed.

  Global Instance meet_comm `{OCM.t A leR addO} : Comm (=) meet.
  Proof.
    repeat intro.
    apply ext. split; simpl; intros [H0 H1]; auto.
  Qed.

  Global Instance meet_assoc `{OCM.t A leR addO} : Assoc (=) meet.
  Proof.
    repeat intro.
    apply ext. split; simpl; [intros (X&Y&Z) | intros ((X&Y)&Z)]; auto.
  Qed.

  Global Instance meet_top_left_eq `{OCM.t A leR addO} : LeftId (=) top meet.
  Proof.
    repeat intro. apply ext. simpl. split; [intros [_ H0]; auto | auto].
  Qed.
  Global Instance meet_top_right_eq `{OCM.t A leR addO} : RightId (=) top meet.
  Proof.
    repeat intro. apply ext. simpl. split; [intros [H0 _]; auto | auto].
  Qed.

  Global Instance meet_left_eq_proper `{OCM.t A leR addO} : forall a, Proper (eq ==> eq) (meet a).
  Proof. intros a x y H0. subst. auto. Qed.
  Global Instance meet_right_eq_proper `{OCM.t A leR addO} : forall a, Proper (eq ==> eq) (flip meet a).
  Proof. intros a x y H0. subst. auto. Qed.
  Global Instance meet_eq_proper `{OCM.t A leR addO} : Proper (eq ==> eq ==> eq) meet.
  Proof. intros a b H0 c d H1. subst; auto. Qed.

  Global Instance meet_idemp_eq `{OCM.t A leR addO} : IdemP (=) meet.
  Proof. intro x. apply ext. simpl. split; [intros [H0 _]; auto | auto]. Qed.

End partition.
Arguments partition.t {A} leR addO {_}.
