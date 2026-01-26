From stdpp Require Import base.
From liris Require Export wfocm ordinal_facts.

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

(** WFOCM respects some ordinal operations when embedded. *)
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

(* (** Layer structure. (Ord.S u) is the "unit" of the construction. *) *)
(* (* u is instantiated to the upperbound ordinal of the set of scheduler fairness fuel. *) *)
(* (* A inperative-like pseudocode has the following "size": *)
(* one 'line' (Ord.S u), one 'block' = line × ω, one 'loop' = block × ω <= (line × ω) ↑ 2, *)
(* and this is recursively nested: size(pseudocode) <= (line × ω) ↑ ω. *)
(* We also multiply (ω ↑ ω) to get code-size nondeterministic number of  (line × ω) ↑ ω tokens, *)
(* which allow us to write an "obligation structure code". *)
(* Finally, (⊕ u) is to initialize the layer-scheduler fairness connection. *)
(*  *) *)
(* Fixpoint layer (u : Ord.t) (i : nat) : Ord.t := *)
(*   match i with *)
(*   | O => (((((Ord.S u) × ω) ↑ ω) × (ω ↑ ω)) ⊕ u)%ord *)
(*   | S j => ((((layer u j) ↑ ω) × (ω ↑ ω)) ⊕ u)%ord *)
(*   end. *)

(* Notation "'ℓ[' u '](' i ')'" := (layer u i) (format "ℓ[ u ]( i )"). *)

(* Section layer_facts. *)

(*   Import Hessenberg Jacobsthal. *)

(*   Lemma layer_unfold_zero u : ℓ[u](0) = (((((Ord.S u) × ω) ↑ ω) × (ω ↑ ω)) ⊕ u)%ord. *)
(*   Proof using. reflexivity. Qed. *)

(*   Lemma layer_unfold_S u : *)
(*     forall i, ℓ[u](S i) = (((ℓ[u](i) ↑ ω) × (ω ↑ ω)) ⊕ u)%ord. *)
(*   Proof using. auto. Qed. *)

(*   Ltac lt_remove_add_r := eapply Ord.lt_le_lt; [|apply add_base_l]. *)
(*   Ltac lt_remove_mult_r := eapply Ord.lt_le_lt; [|apply mult_base_l; apply expn_pos]. *)
(*   Ltac lt_remove_r := lt_remove_add_r; lt_remove_mult_r. *)

(*   Lemma layer_lt_zero u : *)
(*     forall i, (Ord.O < ℓ[u](i))%ord. *)
(*   Proof using. *)
(*     destruct i. *)
(*     - unfold layer. lt_remove_r. apply Jacobsthal.expn_pos. *)
(*     - rewrite layer_unfold_S. lt_remove_r. apply Jacobsthal.expn_pos. *)
(*   Qed. *)

(*   Lemma layer_lt_one u : *)
(*     forall i, (Ord.S Ord.O < ℓ[u](i))%ord. *)
(*   Proof using. *)
(*     assert (Ord.S Ord.O < ((Ord.S u) × ω))%ord by apply unit_mult_omega_lt_one. *)
(*     assert (OM : (Ord.S Ord.O < ω)%ord) by apply omega_lt_one. *)
(*     induction i. *)
(*     - unfold layer. pose proof H. *)
(*       rewrite <- (@expn_1_r (Ord.S u × ω)%ord) in H. *)
(*       2:{ etransitivity; [|eapply H]. apply Ord.S_lt. } *)
(*       lt_remove_r. etransitivity; [eapply H|]. eapply lt_expn_r; auto. *)
(*     - etransitivity; [eauto|]. rewrite <- (@expn_1_r ℓ[u](i)); [| apply layer_lt_zero]. *)
(*       rewrite layer_unfold_S. lt_remove_r. apply lt_expn_r; auto. *)
(*   Qed. *)

(*   Lemma layer_lt_S_nats u : *)
(*     forall (n i : nat), (((ℓ[u](i) ↑ ω) × n) < ℓ[u](S i))%ord. *)
(*   Proof. *)
(*     intros. rewrite layer_unfold_S. lt_remove_add_r. apply lt_mult_r; [| apply expn_pos]. *)
(*     etransitivity; [|eapply lt_expn_r]. 2,3: apply omega_lt_one. *)
(*     rewrite expn_1_r; [apply Ord.omega_upperbound | apply omega_lt_zero]. *)
(*   Qed. *)

(*   Lemma layer_lt_S_nat u : *)
(*     forall (n i : nat), ((ℓ[u](i) ↑ n) < ℓ[u](S i))%ord. *)
(*   Proof. *)
(*     intros. rewrite layer_unfold_S. lt_remove_r. apply lt_expn_r; [apply layer_lt_one | apply Ord.omega_upperbound]. *)
(*   Qed. *)

(*   Lemma layer_lt_S u : *)
(*     forall i, (ℓ[u](i) < ℓ[u](S i))%ord. *)
(*   Proof. *)
(*     intros. eapply Ord.le_lt_lt; [|apply (layer_lt_S_nat _ 1)]. *)
(*     rewrite Ord.from_nat_1. unfold Ord.one. rewrite expn_1_r; [reflexivity|]. *)
(*     apply layer_lt_zero. *)
(*   Qed. *)

(*   Lemma layer_le_layer_zero u : *)
(*     forall i, (ℓ[u](0) <= ℓ[u](i))%ord. *)
(*   Proof using. *)
(*     induction i; [reflexivity|]. *)
(*     etransitivity; [eauto|]. apply Ord.lt_le, layer_lt_S. *)
(*   Qed. *)

(*   Lemma layer_le_proper u : *)
(*     Proper (le ==> Ord.le) (layer u). *)
(*   Proof using. *)
(*     intros i j LE. induction LE. *)
(*     - reflexivity. *)
(*     - etransitivity; [eauto|]. apply Ord.lt_le. apply layer_lt_S. *)
(*   Qed. *)

(*   Lemma layer_lt_proper u : *)
(*     Proper (lt ==> Ord.lt) (layer u). *)
(*   Proof using. *)
(*     intros i j LT. unfold lt in LT. eapply (Ord.lt_le_lt (o1 := ℓ[u](S i))). *)
(*     - apply layer_lt_S. *)
(*     - apply layer_le_proper. auto. *)
(*   Qed. *)

(*   Lemma layer_upperbound u : *)
(*     forall (n i : nat), ((((Ord.S u) × ω) ↑ n) < ℓ[u](i))%ord. *)
(*   Proof. *)
(*     intros n. induction i. *)
(*     - rewrite layer_unfold_zero. lt_remove_r. apply lt_expn_r. *)
(*       + apply unit_mult_omega_lt_one. *)
(*       + apply Ord.omega_upperbound. *)
(*     - etransitivity; [eauto|]. apply layer_lt_S. *)
(*   Qed. *)

(*   Lemma layer_upperbound_nat u : *)
(*     forall (n i : nat), (n < ℓ[u](i))%ord. *)
(*   Proof. *)
(*     intros. eapply Ord.le_lt_lt; [|eapply (layer_upperbound _ 1)]. *)
(*     rewrite expn_1_r; [|apply unit_mult_omega_lt_zero]. *)
(*     etransitivity; [eapply Ord.lt_le, Ord.omega_upperbound|]. *)
(*     apply unit_mult_omega_le_omega. *)
(*   Qed. *)

(*   Lemma layer_expn_lt_S_gen u : *)
(*     forall (n m i : nat), (((ℓ[u](i) ↑ n) × m) < (ℓ[u](i) ↑ (S n)))%ord. *)
(*   Proof. *)
(*     intros. rewrite Ord.from_nat_S, expn_S; [| apply layer_lt_zero]. *)
(*     apply lt_mult_r; [| apply expn_pos]. apply layer_upperbound_nat. *)
(*   Qed. *)

(*   Lemma layer_lt_S_gen u : *)
(*     forall (n m i : nat), (((ℓ[u](i) ↑ n) × m) < ℓ[u](S i))%ord. *)
(*   Proof. *)
(*     intros. etransitivity. instantiate (1:=(ℓ[u](i) ↑ (S n))%ord). *)
(*     - apply layer_expn_lt_S_gen. *)
(*     - rewrite layer_unfold_S. lt_remove_r. apply lt_expn_r; [apply layer_lt_one | apply Ord.omega_upperbound]. *)
(*   Qed. *)

(* End layer_facts. *)

(* (* Rank structure. *) *)
(* Definition rank (o : Ord.t) (i : nat) : Ord.t := (o ↑ i)%ord. *)

(* (* TODO: prove facts about rank. *) *)

(* (** Embedding enumeration into ordinal. Deprecated for now. *) *)
(* Class enum_from_nat (A : Type) := enum_f : nat -> A. *)
(* Notation "'en[' n ']'" := (enum_f n) (format "en[ n ]"). *)

(* Class Enum {A : Type} (R : A -> A -> Prop) (f : enum_from_nat A) := { *)
(*     enum_wf : well_founded R; *)
(*     enum_f_proper : Proper (lt ==> R) enum_f; *)
(*   }. *)

(* Definition ord_from_enum `{E : Enum A R} (a : A) : Ord.t := Ord.from_wf enum_wf a. *)
(* Definition ord_from_enum_set `{E : Enum A R} : Ord.t := Ord.from_wf_set enum_wf. *)

(* Notation "'oe[' a ']'" := (ord_from_enum a) (format "oe[ a ]"). *)
(* Notation "'oen[' n ']'" := (ord_from_enum en[n]) (format "oen[ n ]"). *)
(* Notation "'oE'" := ord_from_enum_set. *)

(* Section ord_from_enum_facts. *)

(*   Context `{@Enum A R f}. *)

(*   Lemma ord_from_enum_lt (a0 a1 : A) : *)
(*     R a0 a1 -> (oe[a0] < oe[a1])%ord. *)
(*   Proof using. apply Ord.lt_from_wf. Qed. *)

(*   Lemma ord_from_enum_lt_nat (n0 n1 : nat) : *)
(*     n0 < n1 -> (oen[n0] < oen[n1])%ord. *)
(*   Proof using. *)
(*     intros. apply Ord.lt_from_wf. apply enum_f_proper. auto. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_omega : *)
(*     (ω <= oE)%ord. *)
(*   Proof using. *)
(*     rewrite Ord.omega_from_peano_lt_set. eapply WfRel.from_wf_set_inj. apply enum_f_proper. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_nat : *)
(*     forall (n : nat), (n < oE)%ord. *)
(*   Proof using. *)
(*     intros. eapply Ord.lt_le_lt; [apply Ord.omega_upperbound | apply ord_from_enum_set_omega]. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_zero : *)
(*     (Ord.O < oE)%ord. *)
(*   Proof using. *)
(*     rewrite <- Ord.from_nat_O. apply ord_from_enum_set_nat. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_one : *)
(*     (Ord.S Ord.O < oE)%ord. *)
(*   Proof using. *)
(*     rewrite <- Ord.from_nat_O, <- Ord.from_nat_S. apply ord_from_enum_set_nat. *)
(*   Qed. *)

(*   Lemma ord_from_enum_set_square : *)
(*     forall (n : nat), ((oE × n) < (oE ↑ 2))%ord. *)
(*   Proof using. *)
(*     intros. apply Jacobsthal_expn_square. apply ord_from_enum_set_omega. *)
(*   Qed. *)

(* End ord_from_enum_facts. *)
