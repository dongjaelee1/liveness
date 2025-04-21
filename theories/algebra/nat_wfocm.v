From stdpp Require Import base.
From liveness Require Export wfocm.
Require Import Lia Program.

Global Program Instance nat_OCM: OCM.t le Nat.add :=
  OCM.Build_t nat le Nat.add 0 _ _ _ _ _ _ _.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.
Next Obligation. repeat intro. lia. Qed.

Lemma nat_OCM_eq (a0 a1: nat):
  OCM.eq a0 a1 <-> a0 = a1.
Proof.
  split.
  { intro H. red in H. lia. }
  { intro. subst. reflexivity. }
Qed.

Global Program Instance nat_wfocm: WFOCM.t le Nat.add lt :=
  WFOCM.Build_t nat le Nat.add lt _ _ _.
Next Obligation. split; intros; [destruct H | exists 1]; lia. Qed.
