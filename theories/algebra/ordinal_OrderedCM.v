From stdpp Require Import base.
From liveness Require Export orderedCM.
From Ordinal Require Import Ordinal Hessenberg ClassicalOrdinal.

Global Program Instance ord_OrderedCM : OrderedCM.t Ord.le Hessenberg.add :=
  OrderedCM.Build_t _ _ _ Ord.O _ _ _ _ _ _ _ .
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
