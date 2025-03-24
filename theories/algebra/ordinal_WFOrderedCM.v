From stdpp Require Import base.
From liveness Require Export wfOrderedCM.
From Ordinal Require Import Ordinal Hessenberg ClassicalOrdinal.

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
