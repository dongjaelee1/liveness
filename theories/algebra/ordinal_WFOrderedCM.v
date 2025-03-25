From stdpp Require Import base.
From liveness Require Export wfOrderedCM.
From Ordinal Require Import Ordinal Hessenberg ClassicalOrdinal.

Notation "'ω'" := Ord.omega.

Global Program Instance ord_OrderedCM : OrderedCM.t Ord.le Hessenberg.add :=
  OrderedCM.Build_t _ _ _ Ord.O _ _ _ _ _ _ _.
Next Obligation.
  repeat intro. eapply ClassicOrd.total_le.
Qed.
Next Obligation.
  repeat intro. eapply Hessenberg.add_assoc.
Qed.
Next Obligation.
  repeat intro. eapply Hessenberg.add_comm.
Qed.
Next Obligation.
  repeat intro. eapply Hessenberg.add_O_l.
Qed.
Next Obligation.
  eapply Hessenberg.add_base_l.
Qed.

Lemma ord_OrderedCM_eq (a0 a1 : Ord.t) : OrderedCM.eq a0 a1 <-> Ord.eq a0 a1.
Proof. auto. Qed.

Global Program Instance ord_WFOrderedCM : WFOrderedCM.t Ord.le Hessenberg.add Ord.lt :=
  WFOrderedCM.Build_t _ _ _ _ _ _ _.
Next Obligation.
  apply Ord.lt_well_founded.
Qed.
Next Obligation.
  intros a c. split; simpl; intros.
  { destruct H as (b&LT&LE). eapply Ord.lt_le_lt; [|eauto]. apply Hessenberg.add_lt_l. auto. }
  { exists Ord.one. split; [apply Ord.S_lt |].
    unfold Ord.one. rewrite Hessenberg.add_S_r. apply Ord.S_supremum.
    rewrite Hessenberg.add_O_r. auto.
  }
Qed.

Section ord_facts.

  Lemma ord_lt_one (o0 o1 : Ord.t) :
    (o0 < o1)%ord -> ((o0 ⊕ (Ord.S Ord.O)) <= o1)%ord.
  Proof.
    intros H. apply WFOrderedCM.lt_exists_left in H. destruct H as (b&H0&H1).
    etransitivity; [|eauto]. apply Hessenberg.le_add_r.
    apply Ord.S_supremum. auto.
  Qed.

  Lemma Jacobsthal_expn_omega (o : Ord.t) :
    (Ord.S Ord.O < o)%ord -> forall (n : nat), ((o ↑ n) < (o ↑ Ord.omega))%ord.
  Proof.
    intros. apply Jacobsthal.lt_expn_r; [auto|apply Ord.omega_upperbound].
  Qed.

End ord_facts.

Section ord_from_wf_facts.

  Context {A : Type} {R : A -> A -> Prop}.
  Variable WF : well_founded R.

  Lemma ord_from_wf_lt_one (a0 a1 : A) :
    R a0 a1 -> ((Ord.from_wf WF a0 ⊕ (Ord.S Ord.O)) <= Ord.from_wf WF a1)%ord.
  Proof using.
    intros HR. apply ord_lt_one. apply Ord.lt_from_wf. auto.
  Qed.

  Lemma ord_from_wf_set_one (a : A) :
    ((Ord.from_wf WF a ⊕ (Ord.S Ord.O)) <= Ord.from_wf_set WF)%ord.
  Proof using.
    apply ord_lt_one. apply Ord.from_wf_set_upperbound.
  Qed.

End ord_from_wf_facts.

Class enum_from_nat (A : Type) := enum_f : nat -> A.
Notation "'en[' n ']'" := (enum_f n) (format "en[ n ]").

Class Enum {A : Type} (R : A -> A -> Prop) (f : enum_from_nat A) := {
    enum_wf : well_founded R;
    enum_f_proper : Proper (lt ==> R) enum_f;
  }.

Definition ord_from_enum `{E : Enum A R} (a : A) : Ord.t := Ord.from_wf enum_wf a.
Definition ord_from_enum_set `{E : Enum A R} : Ord.t := Ord.from_wf_set enum_wf.

Notation "'oe[' a ']'" := (ord_from_enum a) (format "oe[ a ]").
Notation "'oen[' n ']'" := (ord_from_enum en[n]) (format "oen[ n ]").
Notation "'oE'" := ord_from_enum_set.

Section ord_from_enum_facts.

  Context `{@Enum A R f}.

  Lemma ord_from_enum_lt (a0 a1 : A) :
    R a0 a1 -> (oe[a0] < oe[a1])%ord.
  Proof using.
    apply Ord.lt_from_wf.
  Qed.

  Lemma ord_from_enum_lt_nat (n0 n1 : nat) :
    n0 < n1 -> (oen[n0] < oen[n1])%ord.
  Proof using.
    intros. apply Ord.lt_from_wf. apply enum_f_proper. auto.
  Qed.

  Lemma ord_from_enum_set_omega :
    (ω <= oE)%ord.
  Proof using.
    rewrite Ord.omega_from_peano_lt_set. eapply WfRel.from_wf_set_inj. apply enum_f_proper.
  Qed.

  Lemma ord_from_enum_set_nat :
    forall (n : nat), (n < oE)%ord.
  Proof using.
    intros. eapply Ord.lt_le_lt; [apply Ord.omega_upperbound | apply ord_from_enum_set_omega].
  Qed.

  Lemma ord_from_enum_set_zero :
    (Ord.O < oE)%ord.
  Proof using.
    rewrite <- Ord.from_nat_O. apply ord_from_enum_set_nat.
  Qed.

  Lemma ord_from_enum_set_one :
    (Ord.S Ord.O < oE)%ord.
  Proof using.
    rewrite <- Ord.from_nat_O, <- Ord.from_nat_S . apply ord_from_enum_set_nat.
  Qed.

End ord_from_enum_facts.
