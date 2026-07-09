From stdpp Require Import base.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes updates.
From iris.prelude Require Import options.
From lantana Require Import ocm.

(** Reference: "Module Fuel" in Lilo and FOS. *)

Variant bank `{OCM.t A leR addO} : Type :=
  | BankCash (s : quotient.t leR addO) (* sub *)
  | BankDebt (e : quotient.t leR addO) (s : quotient.t leR addO) (q : Qp) (* entire, sub, q *)
.

Definition debt `{OCM.t A leR addO} (a : A) (q : Qp) : @bank A leR addO _ :=
  BankDebt (quotient.from_monoid a) (quotient.from_monoid OCM.unit) q.
Definition cash `{OCM.t A leR addO} (a : A) : @bank A leR addO _ :=
  BankCash (quotient.from_monoid a).
Definition bank_unit `{OCM.t A leR addO} : @bank A leR addO _ :=
  cash OCM.unit.

Section bank.
  Context `{SI : indexT}.
  Context `{OCM : OCM.t A leR addO}.

  Canonical Structure bankO := leibnizO bank.

  Local Infix "≤" := leR (at level 70).
  Local Notation "0" := OCM.unit.
  Local Infix "⊕" := addO (at level 70).
  Local Infix "≃" := OCM.eq (at level 70).

  Local Infix "/≤" := quotient.le (at level 70).
  Local Infix "/⊕" := quotient.add (at level 70).
  Local Notation "'[/' a ']'" := (quotient.from_monoid a) (at level 10, a at level 1, format "[/ a ]").
  Local Infix "/⩓" := quotient.meet (at level 70).
  Local Infix "/⩔" := quotient.join (at level 70).

  Global Instance bank_inhabited : Inhabited bank := populate bank_unit.

  Global Instance BankCash_inj : Inj (=) (=) BankCash.
  Proof using. by injection 1. Qed.

  Local Instance bank_valid_instance : Valid bank :=
    λ b,
      match b with
      | BankCash s => True
      | BankDebt e s q => (s /≤ e) /\ (Qp.le q 1)%Qp
      end.

  Local Instance bank_unit_instance : Unit bank := bank_unit.

  Local Instance bank_op_instance : Op bank :=
    λ b0 b1,
      match b0, b1 with
      | BankCash s0, BankCash s1 => BankCash (s0 /⊕ s1)
      | BankCash s0, BankDebt e1 s1 q1 => BankDebt e1 (s0 /⊕ s1) q1
      | BankDebt e0 s0 q0, BankCash s1 => BankDebt e0 (s0 /⊕ s1) q0
      | BankDebt e0 s0 q0, BankDebt e1 s1 q1 => BankDebt (e0 /⩓ e1) (s0 /⊕ s1) (q0 + q1)%Qp
      end.

  Local Instance bank_pcore_instance : PCore bank := λ b, Some bank_unit.

  Lemma bank_unit_unfold : ε = BankCash quotient.unit.
  Proof. done. Qed.

  Lemma bank_op_cash a b : BankCash a ⋅ BankCash b = BankCash (a /⊕ b).
  Proof. done. Qed.
  Lemma bank_op_debt e0 e1 s0 s1 q0 q1 :
    BankDebt e0 s0 q0 ⋅ BankDebt e1 s1 q1 = BankDebt (e0 /⩓ e1) (s0 /⊕ s1) (q0 + q1)%Qp.
  Proof. done. Qed.
  Lemma bank_op_cash_debt a e s q :
    BankCash a ⋅ BankDebt e s q = BankDebt e (a /⊕ s) q%Qp.
  Proof. done. Qed.
  Lemma bank_op_debt_cash a e s q :
    BankDebt e s q ⋅ BankCash a = BankDebt e (s /⊕ a) q%Qp.
  Proof. done. Qed.

  Lemma bank_core b : core b = bank_unit.
  Proof. done. Qed.

  Lemma bank_valid_cash s : ✓ BankCash s ↔ True.
  Proof using. done. Qed.
  Lemma bank_valid_debt e s q : ✓ BankDebt e s q ↔ (s /≤ e) ∧ (q ≤ 1)%Qp.
  Proof using. done. Qed.
  Lemma bank_valid_debt_exclusive e0 e1 s0 s1 q : ✓ (BankDebt e0 s0 1 ⋅ BankDebt e1 s1 q) ↔ False.
  Proof using.
    rewrite bank_op_debt. rewrite bank_valid_debt. split; intros; [|contradiction].
    destruct H. by apply Qp.not_add_le_l in H0.
  Qed.
  Lemma bank_valid_debt_cash_raw e s q c : ✓ (BankDebt e s q ⋅ BankCash c) ↔ (s /⊕ c /≤ e) ∧ (q ≤ 1)%Qp.
  Proof. rewrite bank_op_debt_cash. apply bank_valid_debt. Qed.
  Lemma bank_valid_debt_cash a q c : ✓ (debt a q ⋅ cash c) ↔ (c ≤ a) ∧ (q ≤ 1)%Qp.
  Proof. rewrite /debt /cash bank_valid_debt_cash_raw. by rewrite left_id_L quotient.from_monoid_le. Qed.

  Lemma bank_cash_included a b : BankCash a ≼ BankCash b ↔ ∃ c, b = (a /⊕ c).
  Proof.
    rewrite /included /op /bank_op_instance. split; intro.
    - destruct H. destruct x; inv H. eauto.
    - destruct H. exists (BankCash x). by rewrite H.
  Qed.
  Lemma bank_debt_included e0 e1 s0 s1 q0 q1 :
    BankDebt e0 s0 q0 ≼ BankDebt e1 s1 q1 ↔
    (exists s, e0 = e1 ∧ s1 = (s0 /⊕ s) ∧ q0 = q1) ∨ (∃ e s q, e1 = (e0 /⩓ e) ∧ s1 = (s0 /⊕ s) ∧ q1 = (q0 + q)%Qp).
  Proof.
    rewrite /included /op /bank_op_instance. split; intro.
    - destruct H. destruct x; inv H.
      + left; eauto.
      + right. repeat esplit; eauto.
    - destruct H as [(s&He&Hs&Hq) | (e&s&q&He&Hs&Hq)].
      + exists (BankCash s). subst; eauto.
      + exists (BankDebt e s q). subst; eauto.
  Qed.
  Lemma bank_cash_debt_included a e s q :
    BankCash a ≼ BankDebt e s q ↔ ∃ b, s = (a /⊕ b).
  Proof.
    rewrite /included /op /bank_op_instance. split; intro.
    - destruct H. destruct x; inv H. eauto.
    - destruct H. subst. by exists (BankDebt e x q).
  Qed.
  Lemma bank_debt_cash_included a e s q :
    BankDebt e s q ≼ BankCash a ↔ False.
  Proof.
    rewrite /included /op /bank_op_instance. split; intro.
    - destruct H. destruct x; inv H.
    - contradiction.
  Qed.

  Lemma bank_ra_mixin : RAMixin bank.
  Proof.
    apply ra_total_mixin; eauto.
    - solve_proper.
    - solve_proper.
    - solve_proper.
    - intros a b c.
      destruct a, b, c; try rewrite !bank_op_cash; try rewrite !bank_op_debt;
                     try rewrite !bank_op_cash_debt; try rewrite !bank_op_debt_cash;
                     try rewrite !quotient.add_assoc; auto.
      + by rewrite !assoc_L.
    - intros a b.
      destruct a, b; try rewrite !bank_op_cash; try rewrite !bank_op_debt;
                  try rewrite !bank_op_cash_debt; try rewrite !bank_op_debt_cash;
                  try rewrite quotient.add_comm; auto.
      + by rewrite (comm_L quotient.meet) (comm_L Qp.add).
    - intros x. rewrite bank_core. rewrite /bank_unit. destruct x.
      + destruct (quotient.from_monoid_exist s); subst. by rewrite bank_op_cash left_id_L.
      + destruct (quotient.from_monoid_exist s); subst. by rewrite bank_op_cash_debt left_id_L.
    - intros x y H. rewrite !bank_core bank_cash_included. exists ([/0]). by rewrite left_id_L.
    - rewrite /valid /bank_valid_instance. intros x y V. destruct x, y; simpl; auto.
      + rewrite bank_op_debt_cash in V. destruct V as [H1 H2]. split; [|auto].
        etransitivity; [|eauto]. destruct (quotient.from_monoid_exist s); destruct (quotient.from_monoid_exist s0); subst.
        rewrite quotient.from_monoid_add. apply quotient.from_monoid_le. apply OCM.add_base_left_le.
      + rewrite bank_op_debt in V. destruct V as [H1 H2]. split.
        * etransitivity; [| eapply (quotient.meet_left_le e e0)].
          etransitivity; [|eauto]. etransitivity; [|eapply (quotient.add_left_le_proper s quotient.unit)].
          { by rewrite right_id_L. }
          { apply quotient.unit_le. }
        * etransitivity; [|eauto]. eapply Qp.le_add_l.
  Qed.
  Canonical Structure bankR := discreteR bank bank_ra_mixin.

  Global Instance bank_cmra_discrete : CmraDiscrete bank.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma bank_ucmra_mixin : UcmraMixin bank.
  Proof.
    split; [done | | done]. intros x. destruct x.
    - by rewrite bank_op_cash left_id_L.
    - by rewrite bank_op_cash_debt left_id_L.
  Qed.
  Canonical Structure bankUR := Ucmra bank bank_ucmra_mixin.

  Global Instance bank_unit_core_id : CoreId bank_unit.
  Proof using. by constructor. Qed.

  (** Rules about updates. *)
  Lemma bank_opM (a : bank) mb : a ⋅? mb = a ⋅ (default ε mb).
  Proof using SI. destruct mb; simpl; auto. by rewrite right_id_L. Qed.

  Lemma bank_cash_update a0 a1 (LE : a0 /≤ a1) : BankCash a1 ~~> BankCash a0.
  Proof.
    intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros.
    - destruct c.
      + rewrite bank_op_cash. auto using bank_valid_cash.
      + rewrite bank_op_cash_debt in H. rewrite bank_valid_debt in H. destruct H.
        rewrite bank_op_cash_debt. apply bank_valid_debt. split; [|auto].
        etransitivity; [|eauto]. by apply quotient.add_right_le_proper.
    - rewrite right_id_L. auto using bank_valid_cash.
  Qed.
  Lemma cash_update a0 a1 (LE : a0 ≤ a1) : cash a1 ~~> cash a0.
  Proof. apply bank_cash_update. by rewrite quotient.from_monoid_le. Qed.

  Lemma bank_debt_update a0 a1 s0 s1 q (LE1 : a0 /≤ a1) (LE2 : s0 /≤ s1) : BankDebt a0 s1 q ~~> BankDebt a1 s0 q.
  Proof.
    intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros.
    - destruct c.
      + rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. destruct H.
        rewrite bank_op_debt_cash. apply bank_valid_debt. split; [|auto].
        etransitivity; [|eauto]. etransitivity; [|eauto]. by apply quotient.add_right_le_proper.
      + rewrite bank_op_debt in H. rewrite bank_valid_debt in H. destruct H.
        rewrite bank_op_debt. apply bank_valid_debt. split; [|auto].
        etransitivity; [by eapply quotient.add_right_le_proper|].
        etransitivity; [|by eapply quotient.meet_right_le_proper]. eauto.
    - rewrite right_id_L in H. rewrite right_id_L. rewrite bank_valid_debt in H. destruct H.
      apply bank_valid_debt. split; [|auto].
      etransitivity; [eauto|]. etransitivity; [eauto|]. auto.
  Qed.
  Lemma debt_update a0 a1 q (LE : a0 ≤ a1) : debt a0 q ~~> debt a1 q.
  Proof. apply bank_debt_update; [by rewrite quotient.from_monoid_le | reflexivity]. Qed.

  Lemma bank_debt_owe a0 a1 s : BankDebt a0 s 1 ~~> BankDebt (a0 /⊕ a1) s 1 ⋅ BankCash a1.
  Proof.
    intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros.
    - destruct c.
      + rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. destruct H.
        rewrite !bank_op_debt_cash. apply bank_valid_debt. split; [|auto].
        etransitivity; [|by apply quotient.add_right_le_proper].
        simpl. rewrite -!quotient.add_assoc. rewrite (quotient.add_comm a1 s0). reflexivity.
      + rewrite bank_op_debt in H. rewrite bank_valid_debt_exclusive in H. contradiction.
    - rewrite right_id_L in H. rewrite right_id_L. rewrite bank_valid_debt in H. destruct H.
      apply bank_valid_debt. split; [|auto].
      apply quotient.add_right_le_proper; auto.
  Qed.
  Lemma debt_owe a0 a1 : debt a0 1 ~~> debt (a0 ⊕ a1) 1 ⋅ cash a1.
  Proof.
    replace (debt (a0 ⊕ a1) 1) with (BankDebt ([/a0] /⊕ [/a1]) (quotient.from_monoid 0) 1).
    - apply bank_debt_owe.
    - unfold debt. by rewrite quotient.from_monoid_add.
  Qed.

  Lemma bank_debt_pay a0 a1 s q : BankDebt a0 s q ⋅ BankCash a1 ~~>: λ k, ∃ a2, k = BankDebt a2 s q ∧ (a1 /⊕ a2 /≤ a0).
  Proof.
    apply cmra_discrete_updateP. intros mb. rewrite !bank_opM. destruct mb; simpl; intros.
    - destruct c.
      + do 2 rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. destruct H.
        exists (BankDebt (s /⊕ s0) s q). split.
        * eexists. split; [eauto|].
          rewrite !quotient.add_assoc. rewrite (quotient.add_comm a1 s). auto.
        * rewrite bank_op_debt_cash. apply bank_valid_debt. split; [reflexivity | auto].
      + rewrite bank_op_debt_cash in H. rewrite bank_op_debt in H. rewrite bank_valid_debt in H. destruct H.
        exists (BankDebt (s /⊕ s0) s q). split.
        * eexists. split; [eauto|]. etransitivity; [|by apply quotient.meet_left_le].
          etransitivity; [|eauto].
          rewrite -quotient.add_assoc. rewrite (quotient.add_comm a1 s0).
          rewrite (quotient.add_assoc s). by rewrite (quotient.add_comm a1).
        * rewrite bank_op_debt. apply bank_valid_debt. split; auto. apply quotient.meet_infimum; [reflexivity|].
          etransitivity; [|apply quotient.meet_right_le]. etransitivity; [|eauto].
          rewrite -assoc_L (comm_L _ a1 s0) assoc_L.
          etransitivity; [|apply quotient.add_left_le_proper; by apply quotient.unit_le].
          rewrite quotient.add_unit_right_eq. reflexivity.
    - rewrite right_id_L in H. rewrite bank_valid_debt in H. destruct H.
      exists (BankDebt s s q). split.
      + eexists. split; [eauto|]. rewrite comm_L. auto.
      + apply bank_valid_debt. split; [reflexivity | auto].
  Qed.
  Lemma debt_pay a0 a1 q : debt a0 q ⋅ cash a1 ~~>: λ k, ∃ a2, k = debt a2 q ∧ (a1 ⊕ a2 ≤ a0).
  Proof.
    repeat intro. destruct (bank_debt_pay _ _ _ _ n mz H) as (x&(z&Hz1&Hz2)&H2).
    exists x. split; [|auto].
    destruct (quotient.from_monoid_exist z); subst. exists x0. split; [auto|].
    rewrite quotient.from_monoid_add in Hz2. apply quotient.from_monoid_le; auto.
  Qed.

  (** More properties. *)
  Lemma cash_add a0 a1 : cash a0 ⋅ cash a1 = cash (a0 ⊕ a1).
  Proof. rewrite /cash bank_op_cash quotient.from_monoid_add. auto. Qed.

  Lemma debt_raw e q : ∃ a, (BankDebt e (quotient.from_monoid OCM.unit) q = debt a q) ∧ (e = [/a]).
  Proof. destruct (quotient.from_monoid_exist e). exists x. rewrite /debt. by subst. Qed.

  Lemma debt_add_raw a0 a1 q0 q1 :
    debt a0 q0 ⋅ debt a1 q1 = BankDebt ([/a0] /⩓ [/a1]) (quotient.from_monoid OCM.unit) (q0 + q1)%Qp.
  Proof. rewrite /debt bank_op_debt left_id_L. auto. Qed.

  Lemma debt_add a0 a1 q0 q1 :
    ∃ b, debt a0 q0 ⋅ debt a1 q1 = debt b (q0 + q1)%Qp ∧ b ≤ a0 ∧ b ≤ a1.
  Proof.
    rewrite debt_add_raw. destruct (debt_raw ([/a0] /⩓ [/a1]) (q0 + q1)) as (b&EQ1&EQ2).
    rewrite EQ1. eexists. split; first eauto. split.
    - apply quotient.from_monoid_le. rewrite -EQ2. apply quotient.meet_left_le.
    - apply quotient.from_monoid_le. rewrite -EQ2. apply quotient.meet_right_le.
  Qed.

  Lemma debt_split a q0 q1 :
    debt a (q0 + q1)%Qp = debt a q0 ⋅ debt a q1.
  Proof. rewrite /debt bank_op_debt left_id_L. by rewrite idemp. Qed.

  Lemma cash_eq a0 a1 (EQ : a0 ≃ a1) : cash a0 = cash a1.
  Proof. rewrite /cash. apply quotient.from_monoid_eq in EQ. rewrite EQ. auto. Qed.

  Lemma debt_eq a0 a1 q (EQ : a0 ≃ a1) : debt a0 q = debt a1 q.
  Proof. rewrite /debt. apply quotient.from_monoid_eq in EQ. rewrite EQ. auto. Qed.

End bank.


(* Some possible alternatives. *)

(* Alternative 1. *)

(* Variant bank `{OCM.t A leR addO} : Type := *)
(*   | BankCash (s : quotient.t leR addO) (* sub *) *)
(*   | BankDebt (e : quotient.t leR addO) (s : quotient.t leR addO) (* entire, sub *) *)
(*   | BankInvalid *)
(* . *)

(* Definition debt `{OCM.t A leR addO} (a : A) : @bank A leR addO _ := *)
(*   BankDebt (quotient.from_monoid a) (quotient.from_monoid OCM.unit). *)
(* Definition cash `{OCM.t A leR addO} (a : A) : @bank A leR addO _ := *)
(*   BankCash (quotient.from_monoid a). *)
(* Definition bank_unit `{OCM.t A leR addO} : @bank A leR addO _ := *)
(*   cash OCM.unit. *)

(* Section bank. *)
(*   Context `{SI : indexT}. *)
(*   Context `{OCM : OCM.t A leR addO}. *)

(*   Canonical Structure bankO := leibnizO bank. *)

(*   Local Infix "≤" := leR (at level 70). *)
(*   Local Notation "0" := OCM.unit. *)
(*   Local Infix "⊕" := addO (at level 70). *)
(*   Local Infix "≃" := OCM.eq (at level 70). *)

(*   Local Infix "/≤" := quotient.le (at level 70). *)
(*   Local Infix "/⊕" := quotient.add (at level 70). *)
(*   Local Notation "'[/' a ']'" := (quotient.from_monoid a) (at level 10, a at level 1, format "[/ a ]"). *)
(*   Local Infix "/⩓" := quotient.meet (at level 70). *)
(*   Local Infix "/⩔" := quotient.join (at level 70). *)

(*   Global Instance bank_inhabited : Inhabited bank := populate bank_unit. *)

(*   Global Instance BankCash_inj : Inj (=) (=) BankCash. *)
(*   Proof using. by injection 1. Qed. *)

(*   Local Instance bank_valid_instance : Valid bank := *)
(*     λ b, *)
(*       match b with *)
(*       | BankCash s => True *)
(*       | BankDebt e s => (s /≤ e) *)
(*       | BankInvalid => False *)
(*       end. *)

(*   Local Instance bank_unit_instance : Unit bank := bank_unit. *)

(*   Local Instance bank_op_instance : Op bank := *)
(*     λ b0 b1, *)
(*       match b0, b1 with *)
(*       | BankCash s0, BankCash s1 => BankCash (s0 /⊕ s1) *)
(*       | BankCash s0, BankDebt e1 s1 => BankDebt e1 (s0 /⊕ s1) *)
(*       | BankDebt e0 s0, BankCash s1 => BankDebt e0 (s0 /⊕ s1) *)
(*       | _, _ => BankInvalid *)
(*       end. *)

(*   Local Instance bank_pcore_instance : PCore bank := λ b, Some bank_unit. *)

(*   Lemma bank_unit_unfold : ε = BankCash quotient.unit. *)
(*   Proof. done. Qed. *)

(*   Lemma bank_op_cash a b : BankCash a ⋅ BankCash b = BankCash (a /⊕ b). *)
(*   Proof. done. Qed. *)
(*   Lemma bank_op_debt e0 e1 s0 s1 : *)
(*     BankDebt e0 s0 ⋅ BankDebt e1 s1 = BankInvalid. *)
(*   Proof. done. Qed. *)
(*   Lemma bank_op_cash_debt a e s : *)
(*     BankCash a ⋅ BankDebt e s = BankDebt e (a /⊕ s). *)
(*   Proof. done. Qed. *)
(*   Lemma bank_op_debt_cash a e s : *)
(*     BankDebt e s ⋅ BankCash a = BankDebt e (s /⊕ a). *)
(*   Proof. done. Qed. *)

(*   Lemma bank_core b : core b = bank_unit. *)
(*   Proof. done. Qed. *)

(*   Lemma bank_valid_cash s : ✓ BankCash s ↔ True. *)
(*   Proof using. done. Qed. *)
(*   Lemma bank_valid_debt e s : ✓ BankDebt e s ↔ (s /≤ e). *)
(*   Proof using. done. Qed. *)

(*   Lemma bank_cash_included a b : *)
(*     BankCash a ≼ BankCash b ↔ ∃ c, b = (a /⊕ c). *)
(*   Proof. *)
(*     rewrite /included /op /bank_op_instance. split; intro. *)
(*     - destruct H. destruct x; inv H. eauto. *)
(*     - destruct H. exists (BankCash x). by rewrite H. *)
(*   Qed. *)
(*   Lemma bank_debt_included e0 e1 s0 s1 : *)
(*     BankDebt e0 s0 ≼ BankDebt e1 s1 ↔ (exists s, e0 = e1 ∧ s1 = (s0 /⊕ s)). *)
(*   Proof. *)
(*     rewrite /included /op /bank_op_instance. split; intro. *)
(*     - destruct H. destruct x; inv H. repeat esplit; eauto. *)
(*     - destruct H as (s&He&Hs). exists (BankCash s). subst; eauto. *)
(*   Qed. *)
(*   Lemma bank_cash_debt_included a e s : *)
(*     BankCash a ≼ BankDebt e s ↔ ∃ b, s = (a /⊕ b). *)
(*   Proof. *)
(*     rewrite /included /op /bank_op_instance. split; intro. *)
(*     - destruct H. destruct x; inv H. eauto. *)
(*     - destruct H. subst. by exists (BankDebt e x). *)
(*   Qed. *)
(*   Lemma bank_debt_cash_included a e s : *)
(*     BankDebt e s ≼ BankCash a ↔ False. *)
(*   Proof. *)
(*     rewrite /included /op /bank_op_instance. split; intro. *)
(*     - destruct H. destruct x; inv H. *)
(*     - contradiction. *)
(*   Qed. *)

(*   Lemma bank_ra_mixin : RAMixin bank. *)
(*   Proof. *)
(*     apply ra_total_mixin; eauto. *)
(*     - solve_proper. *)
(*     - solve_proper. *)
(*     - solve_proper. *)
(*     - intros a b c. *)
(*       destruct a, b, c; try rewrite !bank_op_cash; try rewrite !bank_op_debt; *)
(*                      try rewrite !bank_op_cash_debt; try rewrite !bank_op_debt_cash; *)
(*                      try rewrite !quotient.add_assoc; auto. *)
(*     - intros a b. *)
(*       destruct a, b; try rewrite !bank_op_cash; try rewrite !bank_op_debt; *)
(*                   try rewrite !bank_op_cash_debt; try rewrite !bank_op_debt_cash; *)
(*                   try rewrite quotient.add_comm; auto. *)
(*     - intros x. rewrite bank_core. rewrite /bank_unit /cash. destruct x; auto. *)
(*       + by rewrite bank_op_cash left_id_L. *)
(*       + by rewrite bank_op_cash_debt left_id_L. *)
(*     - intros x y H. rewrite !bank_core bank_cash_included. exists ([/0]). by rewrite left_id_L. *)
(*     - rewrite /valid /bank_valid_instance. intros x y V. destruct x, y; simpl; try done. *)
(*       rewrite bank_op_debt_cash in V. rewrite -(quotient.add_unit_right_eq s). *)
(*       etransitivity; [|eauto]. apply quotient.add_left_le_proper, quotient.unit_le. *)
(*   Qed. *)
(*   Canonical Structure bankR := discreteR bank bank_ra_mixin. *)

(*   Global Instance bank_cmra_discrete : CmraDiscrete bank. *)
(*   Proof. apply discrete_cmra_discrete. Qed. *)

(*   Lemma bank_ucmra_mixin : UcmraMixin bank. *)
(*   Proof. *)
(*     split; [done | | done]. intros x. destruct x. *)
(*     - by rewrite bank_op_cash left_id_L. *)
(*     - by rewrite bank_op_cash_debt left_id_L. *)
(*     - done. *)
(*   Qed. *)
(*   Canonical Structure bankUR := Ucmra bank bank_ucmra_mixin. *)

(*   Global Instance bank_unit_core_id : CoreId bank_unit. *)
(*   Proof using. by constructor. Qed. *)

(*   (** Rules about updates. *) *)
(*   Lemma bank_opM (a : bank) mb : a ⋅? mb = a ⋅ (default ε mb). *)
(*   Proof using SI. destruct mb; simpl; auto. by rewrite right_id_L. Qed. *)

(*   Lemma bank_cash_update a0 a1 (LE : a0 /≤ a1) : BankCash a1 ~~> BankCash a0. *)
(*   Proof. *)
(*     intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros; try done. *)
(*     destruct c; try done. *)
(*     rewrite bank_op_cash_debt in H. rewrite bank_valid_debt in H. *)
(*     rewrite bank_op_cash_debt. apply bank_valid_debt. *)
(*     etransitivity; [|eauto]. by apply quotient.add_right_le_proper. *)
(*   Qed. *)
(*   Lemma cash_update a0 a1 (LE : a0 ≤ a1) : cash a1 ~~> cash a0. *)
(*   Proof. apply bank_cash_update. by rewrite quotient.from_monoid_le. Qed. *)

(*   Lemma bank_debt_update a0 a1 s0 s1 (LE1 : a0 /≤ a1) (LE2 : s0 /≤ s1) : BankDebt a0 s1 ~~> BankDebt a1 s0. *)
(*   Proof. *)
(*     intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros. *)
(*     - destruct c; try done. *)
(*       rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. *)
(*       rewrite bank_op_debt_cash. apply bank_valid_debt. *)
(*       etransitivity; [|eauto]. etransitivity; [|eauto]. by apply quotient.add_right_le_proper. *)
(*     - rewrite right_id_L in H. rewrite right_id_L. rewrite bank_valid_debt in H. *)
(*       apply bank_valid_debt. etransitivity; [eauto|]. etransitivity; [eauto|]. auto. *)
(*   Qed. *)
(*   Lemma debt_update a0 a1 (LE : a0 ≤ a1) : debt a0 ~~> debt a1. *)
(*   Proof. apply bank_debt_update; [by rewrite quotient.from_monoid_le | reflexivity]. Qed. *)

(*   Lemma bank_debt_owe a0 a1 s : BankDebt a0 s ~~> BankDebt (a0 /⊕ a1) s ⋅ BankCash a1. *)
(*   Proof. *)
(*     intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros. *)
(*     - destruct c; try done. *)
(*       rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. *)
(*       rewrite !bank_op_debt_cash. apply bank_valid_debt. *)
(*       etransitivity; [|by apply quotient.add_right_le_proper]. *)
(*       simpl. rewrite -!quotient.add_assoc. rewrite (quotient.add_comm a1 s0). reflexivity. *)
(*     - rewrite right_id_L in H. rewrite right_id_L. rewrite bank_valid_debt in H. *)
(*       apply bank_valid_debt. apply quotient.add_right_le_proper; auto. *)
(*   Qed. *)
(*   Lemma debt_owe a0 a1 : debt a0 ~~> debt (a0 ⊕ a1) ⋅ cash a1. *)
(*   Proof. *)
(*     replace (debt (a0 ⊕ a1)) with (BankDebt ([/a0] /⊕ [/a1]) (quotient.from_monoid 0)). *)
(*     - apply bank_debt_owe. *)
(*     - unfold debt. by rewrite quotient.from_monoid_add. *)
(*   Qed. *)

(*   Lemma bank_debt_pay a0 a1 s : BankDebt a0 s ⋅ BankCash a1 ~~>: λ k, ∃ a2, k = BankDebt a2 s ∧ (a1 /⊕ a2 /≤ a0). *)
(*   Proof. *)
(*     apply cmra_discrete_updateP. intros mb. rewrite !bank_opM. destruct mb; simpl; intros. *)
(*     - destruct c; try done. *)
(*       do 2 rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. *)
(*       exists (BankDebt (s /⊕ s0) s). split. *)
(*       + eexists. split; [eauto|]. *)
(*         rewrite !quotient.add_assoc. rewrite (quotient.add_comm a1 s). auto. *)
(*       + rewrite bank_op_debt_cash. apply bank_valid_debt. reflexivity. *)
(*     - rewrite right_id_L in H. rewrite bank_valid_debt in H. *)
(*       exists (BankDebt s s). split. *)
(*       + eexists. split; [eauto|]. rewrite comm_L. auto. *)
(*       + apply bank_valid_debt. reflexivity. *)
(*   Qed. *)
(*   Lemma debt_pay a0 a1 : debt a0 ⋅ cash a1 ~~>: λ k, ∃ a2, k = debt a2 ∧ (a1 ⊕ a2 ≤ a0). *)
(*   Proof. *)
(*     repeat intro. destruct (bank_debt_pay _ _ _ n mz H) as (x&(z&Hz1&Hz2)&H2). *)
(*     exists x. split; [|auto]. *)
(*     destruct (quotient.from_monoid_exist z); subst. exists x0. split; [auto|]. *)
(*     rewrite quotient.from_monoid_add in Hz2. apply quotient.from_monoid_le; auto. *)
(*   Qed. *)

(*   (** More properties. *) *)
(*   Lemma cash_add a0 a1 : cash a0 ⋅ cash a1 = cash (a0 ⊕ a1). *)
(*   Proof. rewrite /cash bank_op_cash quotient.from_monoid_add. auto. Qed. *)

(*   Lemma cash_eq a0 a1 (EQ : OCM.eq a0 a1) : cash a0 = cash a1. *)
(*   Proof. rewrite /cash. apply quotient.from_monoid_eq in EQ. rewrite EQ. auto. Qed. *)

(*   Lemma debt_eq a0 a1 (EQ : OCM.eq a0 a1) : debt a0 = debt a1. *)
(*   Proof. rewrite /debt. apply quotient.from_monoid_eq in EQ. rewrite EQ. auto. Qed. *)

(* End bank. *)

(* Alternative 2. *)

(* Variant bank : Type := *)
(*   | BankCash (s : Ord.t) (* sub *) *)
(*   | BankDebt (e : Ord.t) (s : Ord.t) (* entire, sub *) *)
(*   | BankInvalid *)
(* . *)

(* Definition bank_eq : bank → bank → Prop := *)
(*   λ b0 b1, match b0, b1 with *)
(*            | BankCash s0, BankCash s1 => (s0 == s1)%ord *)
(*            | BankDebt e0 s0, BankDebt e1 s1 => (e0 == e1)%ord ∧ (s0 == s1)%ord *)
(*            | BankInvalid, BankInvalid => True *)
(*            | _, _ => False *)
(*            end. *)

(* Global Instance bank_eq_Equivalence : Equivalence bank_eq. *)
(* Proof. *)
(*   split; repeat intro. *)
(*   - destruct x; simpl; try reflexivity; auto. split; reflexivity. *)
(*   - destruct x, y; simpl in *; try symmetry; auto. *)
(*     destruct H. split; symmetry; auto. *)
(*   - destruct x, y, z; simpl in *; auto; try contradiction. *)
(*     + etransitivity; eauto. *)
(*     + destruct H, H0. split; etransitivity; eauto. *)
(* Qed. *)

(* Global Instance bank_eq_Proper_1 : Proper (Ord.eq ==> bank_eq) BankCash. *)
(* Proof. repeat intro; simpl; auto. Qed. *)
(* Global Instance bank_eq_Proper_2 : Proper (Ord.eq ==> Ord.eq ==> bank_eq) BankDebt. *)
(* Proof. repeat intro; simpl; auto. Qed. *)

(* Definition debt (a : Ord.t) : bank := BankDebt a Ord.O. *)
(* Definition cash (a : Ord.t) : bank := BankCash a. *)
(* Definition bank_unit : bank := cash Ord.O. *)

(* Section bank. *)
(*   Context `{SI : indexT}. *)

(*   Local Open Scope ord. *)

(*   Canonical Structure ordO := Ofe Ord.t (discrete_ofe_mixin Ord.eq_Equivalence). *)
(*   Canonical Structure bankO := Ofe bank (discrete_ofe_mixin bank_eq_Equivalence). *)

(*   Global Instance bank_inhabited : Inhabited bank := populate bank_unit. *)

(*   Global Instance BankCash_inj : Inj (≡) (≡) BankCash. *)
(*   Proof using. intros x y H. inversion H; eauto. Qed. *)
(*   (* Global Instance BankCash_inj : Inj (=) (=) BankCash. *) *)
(*   (* Proof using. by injection 1. Qed. *) *)

(*   Local Instance bank_valid_instance : Valid bank := *)
(*     λ b, *)
(*       match b with *)
(*       | BankCash s => True *)
(*       | BankDebt e s => (s <= e) *)
(*       | BankInvalid => False *)
(*       end. *)

(*   Local Instance bank_unit_instance : Unit bank := bank_unit. *)

(*   Local Instance bank_op_instance : Op bank := *)
(*     λ b0 b1, *)
(*       match b0, b1 with *)
(*       | BankCash s0, BankCash s1 => BankCash (s0 ⊕ s1) *)
(*       | BankCash s0, BankDebt e1 s1 => BankDebt e1 (s0 ⊕ s1) *)
(*       | BankDebt e0 s0, BankCash s1 => BankDebt e0 (s0 ⊕ s1) *)
(*       | _, _ => BankInvalid *)
(*       end. *)

(*   Local Instance bank_pcore_instance : PCore bank := λ b, Some bank_unit. *)

(*   Lemma bank_unit_unfold : ε = BankCash Ord.O. *)
(*   Proof. done. Qed. *)

(*   Lemma bank_op_cash a b : BankCash a ⋅ BankCash b = BankCash (a ⊕ b). *)
(*   Proof. done. Qed. *)
(*   Lemma bank_op_cash_debt a e s : *)
(*     BankCash a ⋅ BankDebt e s = BankDebt e (a ⊕ s). *)
(*   Proof. done. Qed. *)
(*   Lemma bank_op_debt_cash a e s : *)
(*     BankDebt e s ⋅ BankCash a = BankDebt e (s ⊕ a). *)
(*   Proof. done. Qed. *)
(*   Lemma bank_op_debt e0 e1 s0 s1 : *)
(*     BankDebt e0 s0 ⋅ BankDebt e1 s1 = BankInvalid. *)
(*   Proof. done. Qed. *)

(*   Lemma bank_core b : core b = bank_unit. *)
(*   Proof. done. Qed. *)

(*   Lemma bank_valid_cash s : ✓ BankCash s ↔ True. *)
(*   Proof using. done. Qed. *)
(*   Lemma bank_valid_debt e s : ✓ BankDebt e s ↔ (s <= e). *)
(*   Proof using. done. Qed. *)

(*   Lemma bank_cash_included a b : *)
(*     BankCash a ≼ BankCash b ↔ ∃ c, b == (a ⊕ c). *)
(*   Proof. *)
(*     rewrite /included /op /bank_op_instance. split; intro. *)
(*     - destruct H. destruct x; inversion H. eauto. *)
(*     - destruct H. exists (BankCash x). by rewrite H. *)
(*   Qed. *)

(*   Lemma bank_debt_included e0 e1 s0 s1 : *)
(*     BankDebt e0 s0 ≼ BankDebt e1 s1 ↔ (exists s, e0 == e1 ∧ s1 == (s0 ⊕ s)). *)
(*   Proof. *)
(*     rewrite /included /op /bank_op_instance. split; intro. *)
(*     - destruct H. destruct x; inv H. eexists; split; by eauto. *)
(*     - destruct H as (s&He&Hs). exists (BankCash s). by eauto. *)
(*   Qed. *)

(*   Lemma bank_cash_debt_included a e s : *)
(*     BankCash a ≼ BankDebt e s ↔ ∃ b, s == (a ⊕ b). *)
(*   Proof. *)
(*     rewrite /included /op /bank_op_instance. split; intro. *)
(*     - destruct H. destruct x; inv H. eauto. *)
(*     - destruct H. by exists (BankDebt e x). *)
(*   Qed. *)

(*   Lemma bank_debt_cash_included a e s : *)
(*     BankDebt e s ≼ BankCash a ↔ False. *)
(*   Proof. *)
(*     rewrite /included /op /bank_op_instance. split; intro. *)
(*     - destruct H. destruct x; inv H. *)
(*     - contradiction. *)
(*   Qed. *)

(*   Lemma bank_equiv (x y : bank) : x ≡ y ↔ bank_eq x y. *)
(*   Proof. done. Qed. *)

(*   Lemma bank_ra_mixin : RAMixin bank. *)
(*   Proof. *)
(*     apply ra_total_mixin; eauto. *)
(*     - intros x a b. rewrite !bank_equiv /op. intros H. destruct a, b, x; simpl in *; try by auto. *)
(*       all: try by rewrite H. destruct H. by rewrite H H0. *)
(*     - solve_proper. *)
(*     - intros a b. rewrite bank_equiv /valid. intros H. destruct a, b; simpl in *; try done. *)
(*       destruct H. by rewrite H H0. *)
(*     - intros a b c. *)
(*       destruct a, b, c; try rewrite !bank_op_cash; try rewrite !bank_op_debt; *)
(*                      try rewrite !bank_op_cash_debt; try rewrite !bank_op_debt_cash; *)
(*                      try rewrite Hessenberg.add_assoc; auto. *)
(*     - intros a b. *)
(*       destruct a, b; try rewrite !bank_op_cash; try rewrite !bank_op_debt; *)
(*                   try rewrite !bank_op_cash_debt; try rewrite !bank_op_debt_cash; *)
(*                   try rewrite Hessenberg.add_comm; auto. *)
(*     - intros x. rewrite bank_core. rewrite /bank_unit /op. destruct x; simpl; auto. *)
(*       all: rewrite Hessenberg.add_O_l; auto. *)
(*     - intros x y H. rewrite !bank_core bank_cash_included. exists Ord.O. by rewrite Hessenberg.add_O_l. *)
(*     - rewrite /valid /bank_valid_instance. intros x y V. destruct x, y; simpl; auto. *)
(*       + rewrite bank_op_debt_cash in V. rewrite -(Hessenberg.add_O_r s). etransitivity; [|eauto]. *)
(*         apply Hessenberg.le_add_r. apply Ord.O_bot. *)
(*       + rewrite bank_op_debt in V. done. *)
(*       + rewrite /op in V. by simpl in V. *)
(*   Qed. *)
(*   Canonical Structure bankR := discreteR bank bank_ra_mixin. *)

(*   Global Instance bank_cmra_discrete : CmraDiscrete bank. *)
(*   Proof. apply discrete_cmra_discrete. Qed. *)

(*   Lemma bank_ucmra_mixin : UcmraMixin bank. *)
(*   Proof. *)
(*     split; [done | | done]. intros x. destruct x. *)
(*     - by rewrite bank_op_cash Hessenberg.add_O_l. *)
(*     - by rewrite bank_op_cash_debt Hessenberg.add_O_l. *)
(*     - done. *)
(*   Qed. *)
(*   Canonical Structure bankUR := Ucmra bank bank_ucmra_mixin. *)

(*   Global Instance bank_unit_core_id : CoreId bank_unit. *)
(*   Proof using. by constructor. Qed. *)

(*   (** Rules about updates. *) *)
(*   Lemma bank_opM (a : bank) mb : a ⋅? mb ≡ a ⋅ (default ε mb). *)
(*   Proof using SI. destruct mb; simpl; auto. by rewrite right_id. Qed. *)

(*   Lemma bank_cash_update a0 a1 (LE : a0 <= a1) : BankCash a1 ~~> BankCash a0. *)
(*   Proof. *)
(*     intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros. *)
(*     - destruct c; try done. *)
(*       + rewrite bank_op_cash_debt in H. rewrite bank_valid_debt in H. *)
(*         rewrite bank_op_cash_debt. apply bank_valid_debt. *)
(*         etransitivity; [|eauto]. by apply Hessenberg.le_add_l. *)
(*     - rewrite right_id. auto using bank_valid_cash. *)
(*   Qed. *)
(*   Lemma cash_update a0 a1 (LE : a0 <= a1) : cash a1 ~~> cash a0. *)
(*   Proof. by apply bank_cash_update. Qed. *)

(*   Lemma bank_debt_update a0 a1 s0 s1 (LE1 : a0 <= a1) (LE2 : s0 <= s1) : BankDebt a0 s1 ~~> BankDebt a1 s0. *)
(*   Proof. *)
(*     intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros. *)
(*     - destruct c; try done. *)
(*       rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. *)
(*       rewrite bank_op_debt_cash. apply bank_valid_debt. *)
(*       etransitivity; [|eauto]. etransitivity; [|eauto]. by apply Hessenberg.le_add_l. *)
(*     - rewrite right_id in H. rewrite right_id. rewrite bank_valid_debt in H. *)
(*       apply bank_valid_debt. etransitivity; first eauto. etransitivity; eauto. *)
(*   Qed. *)
(*   Lemma debt_update a0 a1 (LE : a0 <= a1) : debt a0 ~~> debt a1. *)
(*   Proof. apply bank_debt_update; done. Qed. *)

(*   Lemma bank_debt_owe a0 a1 s : BankDebt a0 s ~~> BankDebt (a0 ⊕ a1) s ⋅ BankCash a1. *)
(*   Proof. *)
(*     intros n mb. rewrite !bank_opM. rewrite -!cmra_discrete_valid_iff. destruct mb; simpl; intros. *)
(*     - destruct c; try done. *)
(*       rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. *)
(*       rewrite !bank_op_debt_cash. apply bank_valid_debt. *)
(*       etransitivity; [|by apply Hessenberg.le_add_l]. *)
(*       rewrite !Hessenberg.add_assoc. rewrite (Hessenberg.add_comm a1 s0). reflexivity. *)
(*     - rewrite right_id in H. rewrite right_id. rewrite bank_valid_debt in H. *)
(*       apply bank_valid_debt. apply Hessenberg.le_add_l; auto. *)
(*   Qed. *)
(*   Lemma debt_owe a0 a1 : debt a0 ~~> debt (a0 ⊕ a1) ⋅ cash a1. *)
(*   Proof. apply bank_debt_owe. Qed. *)

(*   Lemma bank_debt_pay a0 a1 s : BankDebt a0 s ⋅ BankCash a1 ~~>: λ k, ∃ a2, k = BankDebt a2 s ∧ ((a1 ⊕ a2) <= a0). *)
(*   Proof. *)
(*     apply cmra_discrete_updateP. intros mb. rewrite !bank_opM. destruct mb; simpl; intros. *)
(*     - destruct c; try done. *)
(*       do 2 rewrite bank_op_debt_cash in H. rewrite bank_valid_debt in H. *)
(*       exists (BankDebt (s ⊕ s0) s). split. *)
(*       + eexists. split; [eauto|]. rewrite -!Hessenberg.add_assoc. rewrite (Hessenberg.add_comm a1 s). auto. *)
(*       + rewrite bank_op_debt_cash. apply bank_valid_debt. reflexivity. *)
(*     - rewrite right_id in H. rewrite bank_valid_debt in H. *)
(*       exists (BankDebt s s). split. *)
(*       + eexists. split; [eauto|]. rewrite Hessenberg.add_comm. auto. *)
(*       + by apply bank_valid_debt. *)
(*   Qed. *)
(*   Lemma debt_pay a0 a1 : debt a0 ⋅ cash a1 ~~>: λ k, ∃ a2, k = debt a2 ∧ ((a1 ⊕ a2) <= a0). *)
(*   Proof. apply bank_debt_pay. Qed. *)

(*   (** More properties. *) *)
(*   Lemma cash_add a0 a1 : cash a0 ⋅ cash a1 = cash (a0 ⊕ a1). *)
(*   Proof. rewrite /cash bank_op_cash. auto. Qed. *)

(*   Lemma cash_eq a0 a1 : a0 == a1 → cash a0 ≡ cash a1. *)
(*   Proof. by intros ->. Qed. *)

(*   Lemma debt_eq a0 a1 : a0 == a1 → debt a0 ≡ debt a1. *)
(*   Proof. intros H. rewrite /debt. by rewrite H. Qed. *)

(* End bank. *)
