(** The ordinals of the [Ordinal] library with Hessenberg addition form a well-founded ordered
    commutative monoid ([WFOCM]). *)

From lantana.prelude Require Export ordinal_facts.
From lantana.algebra Require Export wfocm.

Global Program Instance ord_OCM : OCM.t Ord.le Hessenberg.add :=
  OCM.Build_t _ _ _ Ord.O _ _ _ _ _ _ _.
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

Lemma ord_OCM_eq (a0 a1 : Ord.t) : OCM.eq a0 a1 <-> Ord.eq a0 a1.
Proof. auto. Qed.

Global Program Instance ord_wfocm : WFOCM.t Ord.le Hessenberg.add Ord.lt :=
  WFOCM.Build_t _ _ _ _ _ _ _ _.
Next Obligation.
  apply Ord.lt_well_founded.
Qed.
Next Obligation.
  apply ord_lt_exists_left.
Qed.
Next Obligation.
  exists (Ord.S Ord.O). apply Ord.S_pos.
Qed.

Global Program Instance ord_wfocm_pack : WFOCM.pack Ord.t :=
  WFOCM.Build_pack _ _ _ _ ord_wfocm.
