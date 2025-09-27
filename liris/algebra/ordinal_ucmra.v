(** From the artifact of
    Later Credits: Resourceful Reasoning for the Later Modality
    by Spies et al. 2022
 *)

From iris.algebra Require Export cmra.
(* From iris.algebra Require Export cmra local_updates proofmode_classes. *)
From transfinite.stepindex Require Export ordinal_arith.

Section aux.

  Local Open Scope ordinals.

  Definition n2o (n : nat) : ord := (Nat.iter n succ_def zero).

  Lemma n2o_zero : n2o 0 = zero.
  Proof. done. Qed.

  Lemma n2o_one : n2o 1 = one.
  Proof. done. Qed.

  Lemma n2o_succ n : n2o (S n) = succ_def (n2o n).
  Proof. done. Qed.

  Lemma n2o_add n m : n2o (n + m) = (n2o n) ⊕ (n2o m).
  Proof.
    revert m. induction n; intros.
    - by rewrite natural_addition_zero_left_id.
    - simpl. rewrite IHn. by rewrite natural_addition_succ.
  Qed.

  Lemma n2o_succ_add n : n2o (S n) = one ⊕ (n2o n).
  Proof. rewrite -n2o_one -n2o_add. done. Qed.

  Definition omega_def := limit n2o.
  Notation "'ω'" := (omega_def) : ordinals.

  Lemma omega_upper_bound : ∀ (n : nat), n2o n ⪯ ω.
  Proof. intros. apply limit_upper_bound. Qed.

End aux.
Notation "'ω'" := (omega_def) : ordinals.

(** Ordinals *)
Section ordinals.
  Context `{SI : indexT}.

  Local Open Scope ordinals.
  Canonical Structure ordO := leibnizO ordinals.ord.
  Instance ord_valid : Valid ord := λ x, True.
  Instance ord_validI : ValidN ord := λ α x, True.
  Instance ord_pcore : PCore ord := λ x, Some zero.
  Instance ord_op : Op ord := nadd.
  Instance ord_inhabited : Inhabited ord := populate zero.
  Definition ord_op_plus (x y: ord) : x ⋅ y = (x ⊕ y) := eq_refl.
  Definition ord_equiv_eq (x y: ord) : ((x: ordO) ≡ y) = (x = y) := eq_refl.

  Lemma ord_ra_mixin : RAMixin (ordO).
  Proof using.
    split; try by eauto.
    - by intros ??? ->.
    - intros ???. rewrite !ord_op_plus ord_equiv_eq; simpl.
      by rewrite -(natural_addition_assoc).
    - intros ??. by rewrite !ord_op_plus -natural_addition_comm.
    - intros x cx; injection 1 as <-. by rewrite ord_op_plus natural_addition_zero_left_id.
    - intros x cx; by injection 1 as <-.
    - intros x y cx Hleq; injection 1 as <-.
      exists zero; split; eauto.
      exists zero. by rewrite !ord_op_plus natural_addition_zero_left_id.
  Qed.

  Canonical Structure OrdR : cmra := discreteR ord ord_ra_mixin.

  Global Instance ord_cmra_discrete : CmraDiscrete OrdR.
  Proof using. apply discrete_cmra_discrete. Qed.

  Global Instance ord_cancelable (x : ordO) : Cancelable (x: ordO).
  Proof using.
    intros α y z Hv H. eapply natural_addition_cancel.
    rewrite natural_addition_comm [z ⊕ _]natural_addition_comm.
    by apply H.
  Qed.

  Global Instance ord_zero_left_id: LeftId eq zero nadd.
  Proof using.
    intros ?. by rewrite natural_addition_zero_left_id.
  Qed.

  Global Instance ord_unit : Unit ord := zero.
  Lemma ord_ucmra_mixin : UcmraMixin (ordO).
  Proof using.
    split; apply _ || done.
  Qed.

  Canonical Structure OrdUR : ucmra := Ucmra ord ord_ucmra_mixin.
End ordinals.
