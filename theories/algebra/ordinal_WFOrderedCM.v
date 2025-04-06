From stdpp Require Import base.
From liveness Require Export wfOrderedCM.
From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.

Global Notation "'ω'" := Ord.omega.

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

  Lemma omega_lt_one : (Ord.S Ord.O < ω)%ord.
  Proof.
    rewrite <- Ord.from_nat_O. rewrite <- Ord.from_nat_S. apply Ord.omega_upperbound.
  Qed.

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

  Lemma Jacobsthal_expn_square (o : Ord.t) :
    (ω <= o)%ord -> forall (n : nat), ((o × n) < (o ↑ 2))%ord.
  Proof.
    intros. assert (Z : (Ord.O < o)%ord).
    { eapply Ord.lt_le_lt; [|eauto]. rewrite <- Ord.from_nat_O. apply Ord.omega_upperbound. }
    rewrite !Ord.from_nat_S, Ord.from_nat_O. rewrite Jacobsthal.expn_S; [|auto].
    rewrite Jacobsthal.expn_1_r; [|auto]. apply Jacobsthal.lt_mult_r; [|auto].
    eapply Ord.lt_le_lt; [|eauto]. apply Ord.omega_upperbound.
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

(** Limiting Jacobsthal expn to nat gives useful properties. *)
Fixpoint Jacobsthal_expn_nat (o : Ord.t) (n : nat) : Ord.t :=
  match n with
  | O => Ord.S Ord.O
  | S m => (Jacobsthal_expn_nat o m × o)%ord
  end.

Section Jacobsthal_expn_nat_facts.

  Lemma Jacobsthal_expn_nat_spec o :
    (Ord.O < o)%ord -> forall n, (Jacobsthal_expn_nat o n == (o ↑ n))%ord.
  Proof.
    intros. induction n; intros.
    - simpl. rewrite Ord.from_nat_O, Jacobsthal.expn_O. reflexivity.
    - simpl. rewrite Ord.from_nat_S, Jacobsthal.expn_S; [rewrite IHn; reflexivity | auto].
  Qed.

End Jacobsthal_expn_nat_facts.

(** Layer structure. *)
Fixpoint layer (i : nat) : Ord.t :=
  match i with
  | O => (ω ↑ ω)%ord
  | S j => ((layer j) ↑ ω)%ord
  end.

Notation "'ℓ[' i ']'" := (layer i) (format "ℓ[ i ]").

Section layer_facts.

  Import Jacobsthal.

  Lemma layer_unfold_zero : ℓ[0] = (ω ↑ ω)%ord.
  Proof using. reflexivity. Qed.

  Lemma layer_unfold_S :
    forall i, layer (S i) = ((layer i) ↑ ω)%ord.
  Proof using. auto. Qed.

  Lemma layer_lt_zero :
    forall i, (Ord.O < ℓ[i])%ord.
  Proof using.
    destruct i.
    - unfold layer. apply Jacobsthal.expn_pos.
    - rewrite layer_unfold_S. apply Jacobsthal.expn_pos.
  Qed.

  Lemma layer_lt_one :
    forall i, (Ord.S Ord.O < ℓ[i])%ord.
  Proof using.
    assert (Ord.S Ord.O < ω)%ord by apply omega_lt_one.
    induction i.
    - unfold layer. pose proof H.
      rewrite <- (@expn_1_r ω) in H; [|rewrite <- Ord.from_nat_O; apply Ord.omega_upperbound ].
      etransitivity; [eapply H|]. eapply lt_expn_r; auto.
    - etransitivity; [eauto|]. rewrite <- (@expn_1_r ℓ[i]); [| apply layer_lt_zero].
      rewrite layer_unfold_S. apply lt_expn_r; auto.
  Qed.

  Lemma layer_lt_S :
    forall i, (ℓ[i] < ℓ[S i])%ord.
  Proof.
    intros. rewrite <- (@expn_1_r ℓ[i]); [|apply layer_lt_zero].
    rewrite layer_unfold_S. apply lt_expn_r; [apply layer_lt_one | apply omega_lt_one].
  Qed.

  Lemma layer_le_layer_zero :
    forall i, (ℓ[0] <= ℓ[i])%ord.
  Proof using.
    induction i; [reflexivity|].
    etransitivity; [eauto|]. apply Ord.lt_le, layer_lt_S.
  Qed.

  Lemma layer_le_proper :
    Proper (le ==> Ord.le) layer.
  Proof using.
    intros i j LE. induction LE.
    - reflexivity.
    - etransitivity; [eauto|]. apply Ord.lt_le. apply layer_lt_S.
  Qed.

  Lemma layer_lt_proper :
    Proper (lt ==> Ord.lt) layer.
  Proof using.
    intros i j LT. unfold lt in LT. eapply (Ord.lt_le_lt (o1 := ℓ[S i])).
    - apply layer_lt_S.
    - apply layer_le_proper. auto.
  Qed.

End layer_facts.

(* Rank structure. *)
Definition rank (o : Ord.t) (i : nat) : Ord.t := (o ↑ i)%ord.

(* TODO: prove facts about rank. *)

(** Embedding enumeration into ordinal. Deprecated for now. *)
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
  Proof using. apply Ord.lt_from_wf. Qed.

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
    rewrite <- Ord.from_nat_O, <- Ord.from_nat_S. apply ord_from_enum_set_nat.
  Qed.

  Lemma ord_from_enum_set_square :
    forall (n : nat), ((oE × n) < (oE ↑ 2))%ord.
  Proof using.
    intros. apply Jacobsthal_expn_square. apply ord_from_enum_set_omega.
  Qed.

End ord_from_enum_facts.
