From stdpp Require Import base.
From lantana Require Export wfocm.
From Coq Require Import Lia Program.

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
  { intro H. destruct H. lia. }
  { intro. subst. reflexivity. }
Qed.

Global Program Instance nat_wfocm: WFOCM.t le Nat.add lt :=
  WFOCM.Build_t nat le Nat.add lt _ _ _ _.
Next Obligation. split; intros; [destruct H | exists 1]; lia. Qed.
Next Obligation. exists 1. auto. Qed.

Global Program Instance nat_wfocm_pack : WFOCM.pack nat :=
  WFOCM.Build_pack _ _ _ _ nat_wfocm.
