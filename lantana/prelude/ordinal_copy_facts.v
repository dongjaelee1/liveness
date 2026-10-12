From stdpp Require Import base.
From lantana.ordinal Require Export ordinal hessenberg classical_hessenberg.

(** The facts of [ordinal_facts.v], for the copy of the Ordinal library in [ordinal/], whose
    ordinals [ord.t] are the layers ([lantana/algebra/layer.v]). *)

Class ord_mono_fun_class := {
    η : ord.t → ord.t;
    η_mono : ∀ o, (o <= η o)%ordi;
    #[global] η_lt_proper :: Proper (ord.lt ==> ord.lt) η;
    #[global] η_le_proper :: Proper (ord.le ==> ord.le) η;
  }.

Section limit.

  Local Open Scope ordi.

  Definition limit_fun {A : Type} (f : ord.t -> A -> ord.t) : ord.t -> ord.t :=
    fun o => ord.join (f o).

  Lemma limit_fun_upperbound {A : Type} (f : ord.t -> A -> ord.t) : forall o a, (f o a) <= (limit_fun f o).
  Proof. intros. apply ord.join_upperbound. Qed.

  Lemma limit_fun_supremum {A : Type} (f : ord.t -> A -> ord.t) : forall o u, (∀ a, f o a <= u) -> (limit_fun f o <= u).
  Proof. intros. eapply ord.join_supremum. eauto. Qed.

End limit.

Section ord_facts.

  Import hessenberg jacobsthal.

  Lemma omega_lt_one : (ord.S ord.O < ω)%ordi.
  Proof.
    rewrite <- ord.from_nat_O. rewrite <- ord.from_nat_S. apply ord.omega_upperbound.
  Qed.

  Lemma ord_lt_exists_left : forall a c, (exists b, (ord.O < b)%ordi /\ ((a ⊕ b) <= c)%ordi) <-> (a < c)%ordi.
  Proof.
    intros a c. split; intros.
    { destruct H as (b&LT&LE). eapply ord.lt_le_lt; [|eauto]. apply hessenberg.add_lt_l. auto. }
    { exists ord.one. split; [apply ord.S_lt |].
      unfold ord.one. rewrite hessenberg.add_S_r. apply ord.S_supremum.
      rewrite hessenberg.add_O_r. auto.
    }
  Qed.

  Lemma ord_lt_one (o0 o1 : ord.t) :
    (o0 < o1)%ordi -> ((o0 ⊕ (ord.S ord.O)) <= o1)%ordi.
  Proof.
    intros H. apply ord_lt_exists_left in H. destruct H as (b&H0&H1).
    etransitivity; [|eauto]. apply hessenberg.le_add_r.
    apply ord.S_supremum. auto.
  Qed.

  Lemma jacobsthal_expn_omega (o : ord.t) :
    (ord.S ord.O < o)%ordi -> forall (n : nat), ((o ↑ n) < (o ↑ ord.omega))%ordi.
  Proof.
    intros. apply jacobsthal.lt_expn_r; [auto|apply ord.omega_upperbound].
  Qed.

  Lemma jacobsthal_expn_square (o : ord.t) :
    (ω <= o)%ordi -> forall (n : nat), ((o × n) < (o ↑ 2))%ordi.
  Proof.
    intros. assert (Z : (ord.O < o)%ordi).
    { eapply ord.lt_le_lt; [|eauto]. rewrite <- ord.from_nat_O. apply ord.omega_upperbound. }
    rewrite !ord.from_nat_S, ord.from_nat_O. rewrite jacobsthal.expn_S; [|auto].
    rewrite jacobsthal.expn_1_r; [|auto]. apply jacobsthal.lt_mult_r; [|auto].
    eapply ord.lt_le_lt; [|eauto]. apply ord.omega_upperbound.
  Qed.

  Lemma unit_mult_omega_lt_one (u : ord.t) :
    (ord.S ord.O < ((ord.S u) × ω))%ordi.
  Proof.
    eapply ord.lt_le_lt; [apply omega_lt_one|].
    etransitivity; [rewrite <-mult_1_l; reflexivity|].
    apply le_mult_l, ord.le_S, ord.O_bot.
  Qed.

  Lemma unit_mult_omega_lt_zero (u : ord.t) :
    (ord.O < ((ord.S u) × ω))%ordi.
  Proof.
    etransitivity; [|eapply unit_mult_omega_lt_one]. apply ord.S_lt.
  Qed.

  Lemma unit_mult_omega_le_omega (u : ord.t) :
    (ω <= ((ord.S u) × ω))%ordi.
  Proof.
    etransitivity. instantiate (1:=((ord.S ord.O) × ω)%ordi).
    - rewrite mult_1_l. reflexivity.
    - apply le_mult_l. apply ord.le_S, ord.O_bot.
  Qed.

  Lemma ord_S_add :
    forall o, (ord.S o == ((ord.S ord.O) ⊕ o))%ordi.
  Proof.
    intros. rewrite add_S_l, add_O_l. reflexivity.
  Qed.

  Lemma mult_base_l (o0 o1 : ord.t) : (ord.O < o1)%ordi -> (o0 <= (o0 × o1))%ordi.
  Proof.
    intros. etransitivity.
    2:{ eapply le_mult_r. eapply ord.S_supremum. eauto. }
    rewrite mult_1_r. reflexivity.
  Qed.

  Lemma omega_lt_zero : (ord.O < ω)%ordi.
  Proof. etransitivity; [|eapply omega_lt_one]. apply ord.S_lt. Qed.

End ord_facts.

Section ord_from_wf_facts.

  Context {A : Type} {R : A -> A -> Prop}.
  Variable WF : well_founded R.

  Lemma ord_from_wf_lt_one (a0 a1 : A) :
    R a0 a1 -> ((ord.from_wf WF a0 ⊕ (ord.S ord.O)) <= ord.from_wf WF a1)%ordi.
  Proof using.
    intros HR. apply ord_lt_one. apply ord.lt_from_wf. auto.
  Qed.

  Lemma ord_from_wf_set_one (a : A) :
    ((ord.from_wf WF a ⊕ (ord.S ord.O)) <= ord.from_wf_set WF)%ordi.
  Proof using.
    apply ord_lt_one. apply ord.from_wf_set_upperbound.
  Qed.

End ord_from_wf_facts.

(** Ordinal power with a natural-number exponent, by repeated multiplication.
    It agrees with [o ↑ n] when [o] is positive ([jacobsthal_expn_nat_spec]). *)
Fixpoint jacobsthal_expn_nat (o : ord.t) (n : nat) : ord.t :=
  match n with
  | O => ord.S ord.O
  | S m => (jacobsthal_expn_nat o m × o)%ordi
  end.

Section jacobsthal_expn_nat_facts.

  Lemma jacobsthal_expn_nat_spec o :
    (ord.O < o)%ordi -> forall n, (jacobsthal_expn_nat o n == (o ↑ n))%ordi.
  Proof.
    intros. induction n; intros.
    - simpl. rewrite ord.from_nat_O, jacobsthal.expn_O. reflexivity.
    - simpl. rewrite ord.from_nat_S, jacobsthal.expn_S; [rewrite IHn; reflexivity | auto].
  Qed.

End jacobsthal_expn_nat_facts.
