From stdpp Require Import base.
From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.

Class ord_mono_fun_class := {
    η : Ord.t → Ord.t;
    η_mono : ∀ o, (o <= η o)%ord;
    #[global] η_lt_proper :: Proper (Ord.lt ==> Ord.lt) η;
    #[global] η_le_proper :: Proper (Ord.le ==> Ord.le) η;
  }.

Section limit.

  Local Open Scope ord.

  Definition limit_fun {A : Type} (f : Ord.t -> A -> Ord.t) : Ord.t -> Ord.t :=
    fun o => Ord.join (f o).

  Lemma limit_fun_upperbound {A : Type} (f : Ord.t -> A -> Ord.t) : forall o a, (f o a) <= (limit_fun f o).
  Proof. intros. apply Ord.join_upperbound. Qed.

  Lemma limit_fun_supremum {A : Type} (f : Ord.t -> A -> Ord.t) : forall o u, (∀ a, f o a <= u) -> (limit_fun f o <= u).
  Proof. intros. eapply Ord.join_supremum. eauto. Qed.

End limit.

Section ord_facts.

  Import Hessenberg Jacobsthal.

  Lemma omega_lt_one : (Ord.S Ord.O < ω)%ord.
  Proof.
    rewrite <- Ord.from_nat_O. rewrite <- Ord.from_nat_S. apply Ord.omega_upperbound.
  Qed.

  Lemma ord_lt_exists_left : forall a c, (exists b, (Ord.O < b)%ord /\ ((a ⊕ b) <= c)%ord) <-> (a < c)%ord.
  Proof.
    intros a c. split; intros.
    { destruct H as (b&LT&LE). eapply Ord.lt_le_lt; [|eauto]. apply Hessenberg.add_lt_l. auto. }
    { exists Ord.one. split; [apply Ord.S_lt |].
      unfold Ord.one. rewrite Hessenberg.add_S_r. apply Ord.S_supremum.
      rewrite Hessenberg.add_O_r. auto.
    }
  Qed.

  Lemma ord_lt_one (o0 o1 : Ord.t) :
    (o0 < o1)%ord -> ((o0 ⊕ (Ord.S Ord.O)) <= o1)%ord.
  Proof.
    intros H. apply ord_lt_exists_left in H. destruct H as (b&H0&H1).
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

  Lemma unit_mult_omega_lt_one (u : Ord.t) :
    (Ord.S Ord.O < ((Ord.S u) × ω))%ord.
  Proof.
    eapply Ord.lt_le_lt; [apply omega_lt_one|].
    etransitivity; [rewrite <-mult_1_l; reflexivity|].
    apply le_mult_l, Ord.le_S, Ord.O_bot.
  Qed.

  Lemma unit_mult_omega_lt_zero (u : Ord.t) :
    (Ord.O < ((Ord.S u) × ω))%ord.
  Proof.
    etransitivity; [|eapply unit_mult_omega_lt_one]. apply Ord.S_lt.
  Qed.

  Lemma unit_mult_omega_le_omega (u : Ord.t) :
    (ω <= ((Ord.S u) × ω))%ord.
  Proof.
    etransitivity. instantiate (1:=((Ord.S Ord.O) × ω)%ord).
    - rewrite mult_1_l. reflexivity.
    - apply le_mult_l. apply Ord.le_S, Ord.O_bot.
  Qed.

  Lemma ord_S_add :
    forall o, (Ord.S o == ((Ord.S Ord.O) ⊕ o))%ord.
  Proof.
    intros. rewrite add_S_l, add_O_l. reflexivity.
  Qed.

  Lemma mult_base_l (o0 o1 : Ord.t) : (Ord.O < o1)%ord -> (o0 <= (o0 × o1))%ord.
  Proof.
    intros. etransitivity.
    2:{ eapply le_mult_r. eapply Ord.S_supremum. eauto. }
    rewrite mult_1_r. reflexivity.
  Qed.

  Lemma omega_lt_zero : (Ord.O < ω)%ord.
  Proof. etransitivity; [|eapply omega_lt_one]. apply Ord.S_lt. Qed.

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
