(** The ordinals of the [Ordinal] library with Hessenberg addition as a discrete unital camera
    [OrdUR] (used for later credits), and cancellation of Hessenberg addition. *)

From iris.algebra Require Export cmra.
From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.

Section hessenberg_cancel.
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

End hessenberg_cancel.

(** * The camera of ordinals *)
Section ordinals.
  Context `{SI : sidx}.

  Local Open Scope ord.
  Global Instance ord_eq_Equiv : Equiv Ord.t := Ord.eq.
  Global Instance ord_eq_Equivalence : Equivalence Ord.eq := Ord.eq_Equivalence.
  Canonical Structure ordO := (Ofe Ord.t (@discrete_ofe_mixin _ _ ord_eq_Equiv ord_eq_Equivalence)).
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
