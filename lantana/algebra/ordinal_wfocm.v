From stdpp Require Import base.
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

(** A WFOCM whose embedding into the ordinals ([Ord.from_wf]) maps [addO] to the Hessenberg sum
    and preserves [leR]. *)
Class OrdFromWFOCM `(wfocm : WFOCM.t A leR addO ltR) := {
    ord_from_wfocm_hess_add :
    forall (a1 a2 : A), (Ord.from_wf WFOCM.lt_wf (addO a1 a2) == ((Ord.from_wf WFOCM.lt_wf a1) ⊕ (Ord.from_wf WFOCM.lt_wf a2)))%ord;
    ord_from_wfocm_le :
    forall (a1 a2 : A), leR a1 a2 -> (Ord.from_wf WFOCM.lt_wf a1 <= Ord.from_wf WFOCM.lt_wf a2)%ord;
  }.

Section ord_from_wfocm.
  Context `{wfocm : WFOCM.t A leR addO ltR} {OFW : OrdFromWFOCM wfocm}.

  Lemma ord_from_wfocm_unit_lt (a : A) :
    (ltR OCM.unit a) -> (Ord.O < Ord.from_wf WFOCM.lt_wf a)%ord.
  Proof using.
    intros. apply (Ord.lt_from_wf WFOCM.lt_wf) in H. apply ord_lt_one in H.
    eapply Ord.lt_le_lt; [| eauto]. rewrite Hessenberg.add_comm, <- ord_S_add.
    apply Ord.S_pos.
  Qed.

End ord_from_wfocm.
