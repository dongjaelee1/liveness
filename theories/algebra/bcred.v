From stdpp Require Import base.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes updates.
From iris.prelude Require Import options.
From liveness Require Import orderedCM.

(** Bounded credit. *)
(** Reference: "Module CounterRA" in Lilo and FOS. *)
Variant bcred `{OrderedCM.t A leR addO} : Type :=
  BCred : partition.t leR addO → quotient.t leR addO → bcred.

Definition credit_bound `{OrderedCM.t A leR addO} (a : A) : @bcred A leR addO _ :=
  BCred (partition.from_monoid a) quotient.unit.

Definition credit `{OrderedCM.t A leR addO} (a : A) : @bcred A leR addO _ :=
  BCred partition.top (quotient.from_monoid a).

Definition bcred_unit `{OrderedCM.t A leR addO} : @bcred A leR addO _ :=
  BCred partition.top quotient.unit.

Section bcred.
  Context `{SI : indexT}.
  Context `{OCM : OrderedCM.t A leR addO}.
  Canonical Structure bcredO := leibnizO bcred.

  Local Infix "≤" := OrderedCM.le (at level 70).
  Local Notation "0" := OrderedCM.unit.
  Local Infix "⊕" := OrderedCM.add (at level 70).
  Local Infix "≃" := OrderedCM.eq (at level 70).
  Local Infix "⩓" := OrderedCM.meet (at level 70).
  Local Infix "⩔" := OrderedCM.join (at level 70).

  Local Infix "/≤" := quotient.le (at level 70).
  Local Infix "/⊕" := quotient.add (at level 70).
  Local Notation "'[/' a ']'" := (quotient.from_monoid a) (at level 10, a at level 1, format "[/ a ]").
  Local Infix "/⩓" := quotient.meet (at level 70).
  Local Infix "/⩔" := quotient.join (at level 70).
  Local Notation "/0" := quotient.unit.

  Local Infix "!⩓" := partition.meet (at level 70).
  Local Notation "'[!' a ']'" := (partition.from_monoid a) (at level 10, a at level 1, format "[! a ]").
  Local Notation "!0" := partition.top.

  Global Instance bcred_inhabited : Inhabited bcred := populate bcred_unit.

  Global Instance BCred_inj : Inj2 (=) (=) (=) BCred.
  Proof using. by injection 1. Qed.

  Local Instance bcred_valid_instance : Valid bcred :=
    λ b,
      match b with
        BCred p q => (∃ a, partition.collection _ _ p a ∧ quotient.collection _ _ q a)
      end.

  Local Instance bcred_unit_instance : Unit bcred := bcred_unit.

  Local Instance bcred_op_instance : Op bcred :=
    λ b0 b1,
      match b0, b1 with
        BCred p0 q0, BCred p1 q1 => BCred (p0 !⩓ p1) (q0 /⊕ q1)
      end.

  Local Instance bcred_pcore_instance : PCore bcred :=
    λ b, match b with BCred p q => Some (BCred p /0) end.

  Lemma bcred_unit_unfold : ε = BCred partition.top quotient.unit.
  Proof. done. Qed.
  Lemma bcred_op p0 p1 q0 q1 : BCred p0 q0 ⋅ BCred p1 q1 = BCred (p0 !⩓ p1) (q0 /⊕ q1).
  Proof. done. Qed.
  Lemma bcred_core p q : core (BCred p q) = BCred p /0.
  Proof. done. Qed.
  Lemma bcred_valid p q : ✓ BCred p q ↔ (∃ a, partition.collection _ _ p a ∧ quotient.collection _ _ q a).
  Proof using. done. Qed.
  Lemma bcred_included p0 p1 q0 q1 : BCred p0 q0 ≼ BCred p1 q1 ↔ ∃ p2 q2, p1 = (p0 !⩓ p2) ∧ q1 = (q0 /⊕ q2).
  Proof.
    rewrite /included /op /bcred_op_instance. split; intro.
    - destruct H. destruct x; inv H. repeat esplit.
    - destruct H as (p2&q2&Hp&Hq). subst. by exists (BCred p2 q2).
  Qed.

  Lemma bcred_ra_mixin : RAMixin bcred.
  Proof.
    apply ra_total_mixin; eauto.
    - intros [p q]. done.
    - solve_proper.
    - solve_proper.
    - solve_proper.
    - intros a b c. destruct a, b, c; rewrite !bcred_op; rewrite !assoc_L. auto.
    - intros a b. destruct a, b; rewrite !bcred_op. by rewrite (comm_L _ t) (comm_L _ t0).
    - intros [p q]. rewrite bcred_core. rewrite bcred_op. by rewrite left_id_L idemp_L.
    - intros [p q]. by rewrite !bcred_core.
    - intros [p0 q0] [p1 q1] H. rewrite !bcred_core bcred_included.
      rewrite bcred_included in H. destruct H as (p2&q2&H0&H1). subst.
      exists p2, ([/0]). by rewrite left_id_L.
    - rewrite /valid /bcred_valid_instance. intros x y V. destruct x, y; simpl; auto.
      rewrite bcred_op in V. destruct V as (a&Hp&Hq). simpl in *.
      destruct Hp. destruct Hq as (q0&q1&Ha0&Ha1&LE). exists a; split; [auto|].
      destruct t0; simpl in *. destruct generated. apply H1 in Ha0. apply H1.
      etransitivity; [eauto|]. etransitivity; [|eauto]. apply OrderedCM.add_base_left_le.
  Qed.
  Canonical Structure bcredR := discreteR bcred bcred_ra_mixin.

  Global Instance bcred_cmra_discrete : CmraDiscrete bcred.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma bcred_ucmra_mixin : UcmraMixin bcred.
  Proof.
    split.
    - rewrite /valid /bcred_valid_instance bcred_unit_unfold. exists 0. simpl. split; [auto | done].
    - intros [p q]. rewrite bcred_unit_unfold bcred_op. by rewrite !left_id_L.
    - done.
  Qed.
  Canonical Structure bcredUR := Ucmra bcred bcred_ucmra_mixin.

  Global Instance bcred_unit_core_id a : CoreId (credit_bound a).
  Proof using. by constructor. Qed.

  (** Rules about updates. *)
  Lemma bcred_opM (a : bcred) mb : a ⋅? mb = a ⋅ (default ε mb).
  Proof using SI. destruct mb; simpl; auto. by rewrite right_id_L. Qed.

  Lemma credit_bound_valid a : ✓ (credit_bound a).
  Proof. rewrite bcred_valid. simpl. exists a. split; [reflexivity | apply OrderedCM.unit_le]. Qed.
  Lemma credit_valid a : ✓ (credit a).
  Proof. rewrite bcred_valid. simpl. exists a. done. Qed.
  Lemma credit_bound_credit_valid a b : ✓ (credit_bound a ⋅ credit b) ↔ (∃ c, c ≤ a ∧ b ≤ c).
  Proof using.
    rewrite bcred_valid. simpl. split; [intros (a0&[LE0 _]&a1&a2&_&LEb&LE1) | intros (c&LE0&LE1)].
    - exists a0. split; [auto|]. etransitivity; [|eauto]. etransitivity; [eauto|].
      apply OrderedCM.add_base_right_le.
    - exists b. split.
      + split; [|auto]. etransitivity; eauto.
      + exists 0, b. esplit; [done|]. esplit; [done|]. apply OrderedCM.add_unit_left_le.
  Qed.
  Lemma credit_bound_credit_valid_eq a : ✓ (credit_bound a ⋅ credit a).
  Proof. apply credit_bound_credit_valid. by exists a. Qed.
  Lemma credit_bound_credit_valid_compare a0 a1 : ✓ (credit_bound a0 ⋅ credit a1) ↔ a1 ≤ a0.
  Proof.
    rewrite credit_bound_credit_valid. split; intros.
    - destruct H as (?&?&?). etransitivity; eauto.
    - exists a0. split; done.
  Qed.

  Lemma credit_bound_included a0 a1 (LE : a0 ≤ a1) : credit_bound a1 ≼ credit_bound a0.
  Proof.
    apply bcred_included. exists ([!a0]), ([/0]). rewrite right_id_L. rewrite partition.from_monoid_meet_right; auto.
  Qed.

  Lemma credit_update a0 a1 (LE : a0 ≤ a1) : credit a1 ~~> credit a0.
  Proof.
    intros n mb. rewrite !bcred_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros.
    - destruct c. rewrite bcred_op bcred_valid. rewrite bcred_op bcred_valid in H.
      destruct H as (a&Hp&Hq). exists a. split; [auto|].
      simpl in *. destruct Hq as (b0&b1&LE0&LE1&LE3).
      exists b0, b1. esplit; eauto. etransitivity; eauto.
    - rewrite right_id_L. apply credit_valid.
  Qed.

  Lemma credit_eq a0 a1 (EQ : OrderedCM.eq a0 a1) : credit a0 = credit a1.
  Proof. rewrite /credit. f_equal. by apply quotient.from_monoid_eq. Qed.

  Lemma credit_split a0 a1 : credit (a0 ⊕ a1) = credit a0 ⋅ credit a1.
  Proof.
    rewrite /credit bcred_op. rewrite left_id_L. rewrite quotient.from_monoid_add. auto.
  Qed.

  Lemma credit_update_split a0 a1 a2 (LE : a0 ⊕ a1 ≤ a2) : credit a2 ~~> credit a0 ⋅ credit a1.
  Proof.
    rewrite cmra_update_updateP. eapply cmra_updateP_compose_l.
    { eapply credit_update. eauto. }
    rewrite <- cmra_update_updateP. rewrite credit_split. done.
  Qed.

  Lemma credit_spend a0 a1 : credit_bound a0 ⋅ credit a1 ~~>: λ k, ∃ a2, k = credit_bound a2 ∧ (a1 ⊕ a2 ≤ a0).
  Proof.
    apply cmra_discrete_updateP. intros mb. rewrite !bcred_opM. destruct mb; simpl; intros.
    - destruct c as [p q]. rewrite bcred_op in H. rewrite right_id_L left_id_L in H.
      destruct (quotient.from_monoid_exist q); subst.
      rewrite bcred_valid in H. simpl in H. destruct H as (y&[Ha Hb]&(y0&y1&Hc&Hd&He)). 
      exists (credit_bound x). split.
      + esplit. split; [eauto|]. etransitivity; [|eauto]. etransitivity; [|eauto].
        etransitivity; [eapply OrderedCM.add_left_le_proper; eauto|].
        eapply @OrderedCM.add_right_le_proper; eauto.
      + rewrite bcred_op left_id_L. rewrite bcred_valid. simpl. exists x. split; [split; first done|done].
        eapply partition.closed; [|eauto]. etransitivity; [|eauto]. etransitivity; [eauto|].
        apply OrderedCM.add_base_right_le.
    - rewrite right_id_L in H. apply credit_bound_credit_valid in H. destruct H as (c&LE0&LE1).
      exists (credit_bound 0). split.
      + exists 0. split; [eauto|]. etransitivity; [by apply OrderedCM.add_unit_right_le|].
        etransitivity; first eauto. auto.
      + apply credit_bound_valid.
  Qed.

End bcred.
