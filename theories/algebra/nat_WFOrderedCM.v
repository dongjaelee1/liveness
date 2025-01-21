From stdpp Require Import base.
From liveness Require Export wfOrderedCM.
Require Import Lia Program.

Global Program Instance nat_OrderedCM: OrderedCM.t le Nat.add :=
  OrderedCM.Build_t nat le Nat.add 0 _ _ _ _ _ _ _.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.

Lemma nat_OrderedCM_eq (a0 a1: nat):
  OrderedCM.eq a0 a1 <-> a0 = a1.
Proof.
  split.
  { intro H. red in H. lia. }
  { intro. subst. reflexivity. }
Qed.

Global Program Instance nat_WFOrderedCM: WFOrderedCM.t le Nat.add lt :=
  WFOrderedCM.Build_t nat le Nat.add lt _ _ _.
Next Obligation. lia. Qed.
