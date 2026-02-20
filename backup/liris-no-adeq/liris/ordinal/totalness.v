From liris.ordinal Require Import sflib.
From liris.ordinal Require Export ordinal.

Set Implicit Arguments.
Set Primitive Projections.

Lemma totalness_imply_excluded_middle_on_type
      (TOTAL: forall o0 o1, ord.le o0 o1 \/ ord.lt o1 o0)
  :
    forall (P: Type), inhabited (P + (P -> False)).
Proof.
  i. destruct (TOTAL (@ord.build P (fun _ => ord.O)) (@ord.build (P -> False) (fun _ => ord.O))).
  { assert (np: P -> False).
    { intros p. eapply (ord.le_inv p) in H. des. auto. }
    eapply (inhabits (inr np)).
  }
  { eapply ord.lt_inv in H. des. eapply (inhabits (inl a)). }
Qed.

Lemma totalness_imply_excluded_middle
      (TOTAL: forall o0 o1, ord.le o0 o1 \/ ord.lt o1 o0)
  :
    forall (P: Prop), P \/ ~ P.
Proof.
  i. destruct (totalness_imply_excluded_middle_on_type TOTAL P) as [[]]; auto.
Qed.

Lemma restricted_excluded_middle_imply_totalness
      (LEM: forall A (os: A -> ord.t) o,
          (exists a, ord.le o (os a)) \/
          ~ (exists a, ord.le o (os a))):
  forall o0 o1, ord.lt o0 o1 \/ ord.eq o0 o1 \/ ord.lt o1 o0.
Proof.
  induction o0. i.
  destruct (LEM A os o1).
  { des. right. right. econs; eauto. }
  assert (forall a, ord.lt (os a) o1).
  { i. destruct (H a o1) as [|[]]; auto.
    { exfalso. eapply H0. eexists. eapply H1. }
    { exfalso. eapply H0. eexists. eapply ord.lt_le. eapply H1. }
  }
  destruct o1.
  destruct (LEM A0 os0 (ord.build os)).
  { des. left. econs; eauto. }
  right. left. split.
  { econs. i. specialize (H1 a0).
    eapply ord.lt_inv in H1. des. eauto. }
  { econs. i.
    destruct (LEM A os (os0 a0)); auto.
    exfalso. eapply H2. exists a0.
    eapply ord.build_supremum. i. destruct (H a (os0 a0)) as [|[]]; auto.
    { exfalso. eapply H3. eexists. eapply H4. }
    { exfalso. eapply H3. eexists. eapply ord.lt_le. eapply H4. }
  }
Qed.

Lemma excluded_middle_imply_totalness
      (LEM: forall P, P \/ ~ P):
  forall o0 o1, ord.lt o0 o1 \/ ord.eq o0 o1 \/ ord.lt o1 o0.
Proof.
  eapply restricted_excluded_middle_imply_totalness. auto.
Qed.
