From iris.algebra Require Export cmra.

From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.

Section facts.
  Local Open Scope ord.

  Lemma ord_linear α β : α < β ∨ α == β ∨ β < α.
  Proof.
    destruct (ClassicOrd.total α β); auto.
    apply (ClassicOrd.le_eq_or_lt) in H. destruct H; auto.
  Qed.

  Lemma Hessenberg_add_cancel α β γ : (α ⊕ γ) == (β ⊕ γ) → (α == β).
  Proof.
    intros Heq. destruct (ord_linear α β) as [H|[|H]]; auto; exfalso.
    all: eapply (Hessenberg.lt_add_l γ) in H; rewrite Heq in H; eapply Ord.lt_irreflexive; eauto.
  Qed.

  Lemma Hessenberg_add_cancel_lt α β γ : (α ⊕ γ) < (β ⊕ γ) → α < β.
  Proof.
    intros Heq. destruct (ord_linear α β) as [H|[|H]]; auto; exfalso.
    - rewrite H0 in Heq. by eapply Ord.lt_irreflexive.
    - eapply (Hessenberg.lt_add_l γ) in H. eapply Ord.lt_irreflexive. etransitivity; eauto.
  Qed.

  Lemma Hessenberg_add_cancel_leq α β γ : (α ⊕ γ) <= (β ⊕ γ) → α <= β.
  Proof.
    intros. apply ClassicOrd.le_eq_or_lt in H. destruct H.
    - apply Hessenberg_add_cancel_lt in H. apply Ord.lt_le. auto.
    - apply Hessenberg_add_cancel in H. rewrite H. reflexivity.
  Qed.

End facts.

(** Ordinals *)
Section ordinals.
  Context `{SI : sidx}.

  Local Open Scope ord.
  Global Instance ord_eq_Equiv : Equiv Ord.t := Ord.eq.
  Global Instance ord_eq_Equivalence : Equivalence Ord.eq := Ord.eq_Equivalence.
  Canonical Structure ordO := (Ofe Ord.t (@discrete_ofe_mixin _ _ ord_eq_Equiv ord_eq_Equivalence)).
  (* Canonical Structure ordO := leibnizO Ord.t. *)
  Instance ord_valid : Valid Ord.t:= λ x, True.
  Instance ord_validI : ValidN Ord.t := λ α x, True.
  Instance ord_pcore : PCore Ord.t := λ x, Some Ord.O.
  Instance ord_op : Op Ord.t := Hessenberg.add.
  Instance ord_inhabited : Inhabited Ord.t := populate Ord.O.
  Definition ord_op_plus (x y : Ord.t) : x ⋅ y = (x ⊕ y) := eq_refl.
  Definition ord_equiv_eq (x y: Ord.t) : ((x: ordO) ≡ y) = (x == y) := eq_refl.

  Lemma ord_ra_mixin : RAMixin (ordO).
  Proof using.
    split; try by eauto.
    - by intros ??? ->.
    - intros ???. rewrite !ord_op_plus ord_equiv_eq; simpl.
      by rewrite -(Hessenberg.add_assoc).
    - intros ??. by rewrite !ord_op_plus -Hessenberg.add_comm.
    - intros x cx; injection 1 as <-. by rewrite ord_op_plus Hessenberg.add_O_l.
    - intros x cx; by injection 1 as <-.
    - intros x y cx Hleq; injection 1 as <-.
      exists Ord.O; split; eauto.
      exists Ord.O. by rewrite !ord_op_plus Hessenberg.add_O_l.
  Qed.

  Canonical Structure OrdR : cmra := discreteR Ord.t ord_ra_mixin.

  Global Instance ord_cmra_discrete : CmraDiscrete OrdR.
  Proof using. apply discrete_cmra_discrete. Qed.

  Global Instance ord_cancelable (x : ordO) : Cancelable (x : ordO).
  Proof using.
    intros α y z Hv H. eapply Hessenberg_add_cancel.
    rewrite Hessenberg.add_comm [z ⊕ _]Hessenberg.add_comm.
    by apply H.
  Qed.

  Global Instance ord_zero_left_id: LeftId Ord.eq Ord.O Hessenberg.add.
  Proof using.
    intros ?. by rewrite Hessenberg.add_O_l.
  Qed.

  Global Instance ord_unit : Unit Ord.t := Ord.O.
  Lemma ord_ucmra_mixin : UcmraMixin (ordO).
  Proof using.
    split; apply _ || done.
  Qed.

  Canonical Structure OrdUR : ucmra := Ucmra Ord.t ord_ucmra_mixin.
End ordinals.

(* From transfinite.stepindex Require Export ordinal_arith. *)

(* Section aux. *)

(*   Local Open Scope ordinals. *)

(*   Definition n2o (n : nat) : ord := (Nat.iter n succ_def zero). *)

(*   Lemma n2o_zero : n2o 0 = zero. *)
(*   Proof. done. Qed. *)

(*   Lemma n2o_one : n2o 1 = one. *)
(*   Proof. done. Qed. *)

(*   Lemma n2o_succ n : n2o (S n) = succ_def (n2o n). *)
(*   Proof. done. Qed. *)

(*   Lemma n2o_add n m : n2o (n + m) = (n2o n) ⊕ (n2o m). *)
(*   Proof. *)
(*     revert m. induction n; intros. *)
(*     - by rewrite natural_addition_zero_left_id. *)
(*     - simpl. rewrite IHn. by rewrite natural_addition_succ. *)
(*   Qed. *)

(*   Lemma n2o_succ_add n : n2o (S n) = one ⊕ (n2o n). *)
(*   Proof. rewrite -n2o_one -n2o_add. done. Qed. *)

(*   Definition omega_def := limit n2o. *)
(*   Notation "'ω'" := (omega_def) : ordinals. *)

(*   Lemma omega_upper_bound : ∀ (n : nat), n2o n ⪯ ω. *)
(*   Proof. intros. apply limit_upper_bound. Qed. *)

(* End aux. *)
(* Notation "'ω'" := (omega_def) : ordinals. *)

(* (** Ordinals *) *)
(* Section ordinals. *)
(*   Context `{SI : indexT}. *)

(*   Local Open Scope ordinals. *)
(*   Canonical Structure ordO := leibnizO ordinals.ord. *)
(*   Instance ord_valid : Valid ord := λ x, True. *)
(*   Instance ord_validI : ValidN ord := λ α x, True. *)
(*   Instance ord_pcore : PCore ord := λ x, Some zero. *)
(*   Instance ord_op : Op ord := nadd. *)
(*   Instance ord_inhabited : Inhabited ord := populate zero. *)
(*   Definition ord_op_plus (x y: ord) : x ⋅ y = (x ⊕ y) := eq_refl. *)
(*   Definition ord_equiv_eq (x y: ord) : ((x: ordO) ≡ y) = (x = y) := eq_refl. *)

(*   Lemma ord_ra_mixin : RAMixin (ordO). *)
(*   Proof using. *)
(*     split; try by eauto. *)
(*     - by intros ??? ->. *)
(*     - intros ???. rewrite !ord_op_plus ord_equiv_eq; simpl. *)
(*       by rewrite -(natural_addition_assoc). *)
(*     - intros ??. by rewrite !ord_op_plus -natural_addition_comm. *)
(*     - intros x cx; injection 1 as <-. by rewrite ord_op_plus natural_addition_zero_left_id. *)
(*     - intros x cx; by injection 1 as <-. *)
(*     - intros x y cx Hleq; injection 1 as <-. *)
(*       exists zero; split; eauto. *)
(*       exists zero. by rewrite !ord_op_plus natural_addition_zero_left_id. *)
(*   Qed. *)

(*   Canonical Structure OrdR : cmra := discreteR ord ord_ra_mixin. *)

(*   Global Instance ord_cmra_discrete : CmraDiscrete OrdR. *)
(*   Proof using. apply discrete_cmra_discrete. Qed. *)

(*   Global Instance ord_cancelable (x : ordO) : Cancelable (x: ordO). *)
(*   Proof using. *)
(*     intros α y z Hv H. eapply natural_addition_cancel. *)
(*     rewrite natural_addition_comm [z ⊕ _]natural_addition_comm. *)
(*     by apply H. *)
(*   Qed. *)

(*   Global Instance ord_zero_left_id: LeftId eq zero nadd. *)
(*   Proof using. *)
(*     intros ?. by rewrite natural_addition_zero_left_id. *)
(*   Qed. *)

(*   Global Instance ord_unit : Unit ord := zero. *)
(*   Lemma ord_ucmra_mixin : UcmraMixin (ordO). *)
(*   Proof using. *)
(*     split; apply _ || done. *)
(*   Qed. *)

(*   Canonical Structure OrdUR : ucmra := Ucmra ord ord_ucmra_mixin. *)
(* End ordinals. *)
