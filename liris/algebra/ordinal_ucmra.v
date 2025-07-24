(* From stdpp Require Import base. *)
From iris.algebra Require Export cmra local_updates proofmode_classes.
(* From iris.prelude Require Import options. *)
From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.

Global Notation "'ω'" := Ord.omega.

Lemma Hessenberg_add_cancel (a b c : Ord.t) : ((a ⊕ c) == (b ⊕ c))%ord -> (a == b)%ord.
Proof.
  intros Heq. destruct (ClassicOrd.trichotomy a b) as [H|[|H]]; eauto; exfalso.
  - apply (Hessenberg.lt_add_l c) in H. rewrite Heq in H. apply Ord.lt_irreflexive in H. auto.
  - apply (Hessenberg.lt_add_l c) in H. rewrite Heq in H. apply Ord.lt_irreflexive in H. auto.
Qed.

(** Ordinals *)
Section ordinals.
  Context `{SI : indexT}.

  Local Open Scope ord.

  Canonical Structure ordO := Ofe Ord.t (discrete_ofe_mixin Ord.eq_Equivalence).
  Local Instance ord_valid_instance : Valid Ord.t := λ x, True.
  Local Instance ord_validN_instance : ValidN Ord.t := λ α x, True.
  Local Instance ord_pcore_instance : PCore Ord.t := λ x, Some Ord.O.
  Local Instance ord_op_instance : Op Ord.t := Hessenberg.add.
  Definition ord_op (x y : Ord.t) : x ⋅ y = (x ⊕ y) := eq_refl.
  Instance ord_inhabited : Inhabited Ord.t := populate Ord.O.
  Definition ord_equiv_eq (x y: Ord.t) : (x ≡ y) = (Ord.eq x y) := eq_refl.

  (* The other direction doesn't hold in general. *)
  Lemma ord_included_1 (x y : Ord.t) : x ≼ y → (x <= y).
  Proof using. intros H. inv H. rewrite H0 ord_op. apply Hessenberg.add_base_l. Qed.

  Lemma ord_ra_mixin : RAMixin Ord.t.
  Proof.
    split; try by eauto.
    TODO
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
  Canonical Structure ordR : cmra := discreteR Ord.tord_ra_mixin.





  Global Instance ord_cmra_discrete : CmraDiscrete ordR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance ord_cancelable (x : ord) : Cancelable x.
  Proof.
    intros α y z Hv H. eapply natural_addition_cancel.
    rewrite natural_addition_comm [z ⊕ _]natural_addition_comm.
    by apply H.
  Qed.

  Global Instance ord_zero_left_id: LeftId eq zero nadd.
  Proof.
    intros ?. by rewrite natural_addition_zero_left_id.
  Qed.

  Global Instance ord_unit : Unit Ord.t:= zero.
  Lemma ord_ucmra_mixin : UcmraMixin ord.
  Proof.
    split; apply _ || done.
  Qed.

  Canonical Structure ordUR : ucmra := Ucmra Ord.tord_ucmra_mixin.


  Lemma ord_local_update (x y x' y' : ord) :
    (** Morally [x - y = x' - y']: the difference between auth and frag must
    stay the same with this update. Written using [+] due to underflow. *)
    x ⊕ y' = x' ⊕ y → (x,y) ~l~> (x',y').
  Proof.
    intros ??; apply local_update_unital_discrete=> z _.
    split.
    - by auto.
    - rewrite ord_op_plus. rewrite ord_op_plus in H0.
      rewrite H0 in H. replace ((y ⊕ z) ⊕ y') with ((y' ⊕ z) ⊕ y) in H.
      + by apply natural_addition_cancel in H.
      + rewrite natural_addition_assoc natural_addition_comm. f_equal. by apply natural_addition_comm.
  Qed.
End ordinals.
