(** * Round relations of the obligation model

    A round of a model update ([mupd]) may change several obligations at once (moving a
    subtree to another thread changes the owner of all its nodes). The rounds therefore use
    pointwise relations instead of single model steps:
    - [obls_ndf]: every obligation stays the same or makes progress (strictly less fuel,
      possibly a new owner); new obligations may be added (non-discharging rounds,
      [mupd_nd_step]);
    - [obls_lef]: the same, and obligations may also be discharged (every round of [mupd]);
    - [wits_ndf] / [wits_lef]: witnesses do not increase (and may be discharged for [lef]).
    They imply the coarse relations [obls_nd] / [obls_le] seen by adequacy. *)

From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.algebra Require Import ordinal_wfocm.
From lantana.base_logic Require Export owit.

Section rels.
  Context `{OC : obl_class}.

  Definition obls_ndf (Ω1 Ω2 : obls) : Prop :=
    ∀ k g1, Ω1 !! k = Some g1 → ∃ g2, Ω2 !! k = Some g2 ∧ (g2 = g1 ∨ obl_progress g1 g2).

  Definition obls_lef (Ω1 Ω2 : obls) : Prop :=
    ∀ k g1, Ω1 !! k = Some g1 → ∃ g2, Ω2 !! k = Some g2 ∧ (g2 = g1 ∨ obl_step g1 g2).

  Definition wit_nd_le (w1 w2 : witness) : Prop :=
    match w1, w2 with
    | witness_assigned a1, witness_assigned a2 => a2 w≤ a1
    | witness_discharged, witness_discharged => True
    | _, _ => False
    end.

  Definition wit_le (w1 w2 : witness) : Prop :=
    match w1, w2 with
    | witness_assigned a1, witness_assigned a2 => a2 w≤ a1
    | witness_assigned _, witness_discharged => True
    | witness_discharged, witness_discharged => True
    | _, _ => False
    end.

  Definition wits_ndf (W1 W2 : witnesses) : Prop :=
    ∀ k w1, W1 !! k = Some w1 → ∃ w2, W2 !! k = Some w2 ∧ wit_nd_le w1 w2.

  Definition wits_lef (W1 W2 : witnesses) : Prop :=
    ∀ k w1, W1 !! k = Some w1 → ∃ w2, W2 !! k = Some w2 ∧ wit_le w1 w2.

  Lemma obls_ndf_refl Ω : obls_ndf Ω Ω.
  Proof. intros k g Hk. eauto. Qed.

  Lemma obls_lef_refl Ω : obls_lef Ω Ω.
  Proof. intros k g Hk. eauto. Qed.

  Lemma obls_ndf_obls_lef Ω1 Ω2 : obls_ndf Ω1 Ω2 → obls_lef Ω1 Ω2.
  Proof.
    intros H k g1 Hk. destruct (H k g1 Hk) as (g2& Hg2& [->|Hp]); eauto.
    exists g2. split; first done. right. by constructor.
  Qed.

  Lemma obls_ndf_obls_nd Ω1 Ω2 : obls_ndf Ω1 Ω2 → obls_nd Ω1 Ω2.
  Proof.
    intros H. split.
    - intros k Hk. apply elem_of_dom in Hk as [g1 Hk].
      destruct (H k g1 Hk) as (g2& Hg2& _). apply elem_of_dom. eauto.
    - intros k o1 o2 H1 H2. destruct (H k o1 H1) as (g2& Hg2& Hrel).
      rewrite H2 in Hg2. injection Hg2 as <-. destruct Hrel as [->|Hp].
      + destruct o1; simpl; auto. left. split; [reflexivity|done].
      + inversion Hp; subst. simpl. by right.
  Qed.

  Lemma obls_lef_obls_le Ω1 Ω2 : obls_lef Ω1 Ω2 → obls_le Ω1 Ω2.
  Proof.
    intros H. split.
    - intros k Hk. apply elem_of_dom in Hk as [g1 Hk].
      destruct (H k g1 Hk) as (g2& Hg2& _). apply elem_of_dom. eauto.
    - intros k o1 o2 H1 H2. destruct (H k o1 H1) as (g2& Hg2& Hrel).
      rewrite H2 in Hg2. injection Hg2 as <-. destruct Hrel as [->|Hs].
      + destruct o1; simpl; auto. left. split; [reflexivity|done].
      + inversion Hs as [? ? Hp| ? ? Hd]; subst.
        * inversion Hp; subst. simpl. by right.
        * inversion Hd; subst. simpl. done.
  Qed.

  Lemma wits_ndf_wits_lef W1 W2 : wits_ndf W1 W2 → wits_lef W1 W2.
  Proof.
    intros H k w1 Hk. destruct (H k w1 Hk) as (w2& Hw2& Hle). exists w2. split; first done.
    destruct w1, w2; done.
  Qed.

  Lemma wits_ndf_wits_mon W1 W2 : wits_ndf W1 W2 → dom W2 ⊆ dom W1 → wits_mon W1 W2.
  Proof.
    intros H Hdom k. destruct (W1 !! k) as [w1|] eqn:E1.
    - destruct (H k w1 E1) as (w2& Hw2& Hle). rewrite Hw2. constructor.
      destruct w1, w2; done.
    - destruct (W2 !! k) as [w2|] eqn:E2; last constructor.
      exfalso. assert (k ∈ dom W1) as Hk; last by apply not_elem_of_dom in E1.
      apply Hdom. apply elem_of_dom. eauto.
  Qed.

  Lemma obls_ndf_dom Ω1 Ω2 : obls_ndf Ω1 Ω2 → dom Ω1 ⊆ dom Ω2.
  Proof.
    intros H k Hk. apply elem_of_dom in Hk as [g1 Hk].
    destruct (H k g1 Hk) as (g2& Hg2& _). apply elem_of_dom. eauto.
  Qed.

End rels.

Section owit_rels.
  Context `{!ord_mono_fun_class}.

  (** A witness round compatible with a non-discharging obligation round does not discharge
      witnesses. *)
  Lemma wits_lef_wits_ndf Ω1 Ω2 W1 W2 :
    owit_inv Ω1 W1 → obls_ndf Ω1 Ω2 → wits_lef W1 W2 → owit_inv Ω2 W2 → wits_ndf W1 W2.
  Proof.
    intros I1 R WR I2 k w1 Hw1. destruct (WR k w1 Hw1) as (w2& Hw2& Hle).
    exists w2. split; first done.
    destruct w1 as [a1|], w2 as [a2|]; try done.
    specialize (I1 k). rewrite Hw1 in I1.
    destruct (Ω1 !! k) as [g1|] eqn:Hg1; inversion I1; subst.
    destruct g1 as [f1 o1|]; try done.
    destruct (R k _ Hg1) as (g2& Hg2& Hrel).
    specialize (I2 k). rewrite Hw2 Hg2 in I2. inversion I2 as [? ? Hm|]; subst.
    destruct Hrel as [->|Hp]; first done. inversion Hp; subst. done.
  Qed.

  Lemma wits_lef_same_wits_mon Ω W1 W2 :
    owit_inv Ω W1 → wits_lef W1 W2 → owit_inv Ω W2 → wits_mon W1 W2.
  Proof.
    intros I1 WR I2. apply wits_ndf_wits_mon.
    - eapply wits_lef_wits_ndf; eauto. apply obls_ndf_refl.
    - apply owit_inv_dom in I1, I2. by rewrite -I1 -I2.
  Qed.

  (** Adding a fresh obligation is a non-discharging round. *)
  Lemma obls_ndf_insert_fresh (Ω : obls) k g : Ω !! k = None → obls_ndf Ω (<[k:=g]> Ω).
  Proof.
    intros Hk x g1 Hx. exists g1. split; last by left.
    rewrite lookup_insert_ne; first done. intros ->. by rewrite Hk in Hx.
  Qed.

  (** The witnesses after a round that added a fresh obligation [k] with witness [w]. *)
  Lemma wits_ndf_insert_wits_mon Ω1 W1 W2 k g w :
    owit_inv Ω1 W1 → Ω1 !! k = None → wits_ndf W1 W2 → owit_inv (<[k:=g]> Ω1) W2 →
    (∀ w2, W2 !! k = Some w2 → wit_nd_le w w2) →
    wits_mon (<[k:=w]> W1) W2.
  Proof.
    intros I1 Hk WR I2 Hw x. destruct (decide (x = k)) as [->|Hx].
    - rewrite lookup_insert_eq. pose proof (I2 k) as Ik. rewrite lookup_insert_eq in Ik.
      destruct (W2 !! k) as [w2|] eqn:E; inversion Ik; subst. constructor.
      specialize (Hw w2 eq_refl). destruct w, w2; done.
    - rewrite lookup_insert_ne //. destruct (W1 !! x) as [w1|] eqn:E1.
      + destruct (WR x w1 E1) as (w2& Hw2& Hle). rewrite Hw2. constructor.
        destruct w1, w2; done.
      + destruct (W2 !! x) as [w2|] eqn:E2; last constructor. exfalso.
        pose proof (I2 x) as Ix. rewrite E2 lookup_insert_ne // in Ix.
        pose proof (I1 x) as Ix1. rewrite E1 in Ix1.
        destruct (Ω1 !! x); inversion Ix; inversion Ix1.
  Qed.


  Lemma obls_lef_insert_step (Ω : obls) k g1 g2 :
    Ω !! k = Some g1 → obl_step g1 g2 → obls_lef Ω (<[k:=g2]> Ω).
  Proof.
    intros Hk Hs x g Hx. destruct (decide (x = k)) as [->|Hne].
    - rewrite Hk in Hx. injection Hx as <-. exists g2. rewrite lookup_insert_eq. eauto.
    - exists g. rewrite lookup_insert_ne //. eauto.
  Qed.

  (** The witnesses after a round that discharged [k]. *)
  Lemma wits_lef_discharge_wits_mon Ω1 W1 W2 k a t :
    owit_inv Ω1 W1 → Ω1 !! k = Some (obl_assigned a t) → wits_lef W1 W2 →
    owit_inv (<[k:=obl_discharged]> Ω1) W2 → wits_mon (<[k:=witness_discharged]> W1) W2.
  Proof.
    intros I1 Hk WR I2 x. destruct (decide (x = k)) as [->|Hx].
    - rewrite lookup_insert_eq. pose proof (I2 k) as Ik. rewrite lookup_insert_eq in Ik.
      destruct (W2 !! k) as [w2|] eqn:E; inversion Ik as [? ? Hm|]; subst. constructor.
      by destruct w2.
    - rewrite lookup_insert_ne //. destruct (W1 !! x) as [w1|] eqn:E1.
      + destruct (WR x w1 E1) as (w2& Hw2& Hle). rewrite Hw2. constructor.
        pose proof (I1 x) as Ix1. pose proof (I2 x) as Ix2. rewrite E1 in Ix1.
        rewrite Hw2 lookup_insert_ne // in Ix2.
        destruct (Ω1 !! x) as [g|]; inversion Ix1 as [? ? Hm1|]; inversion Ix2 as [? ? Hm2|];
          subst.
        destruct g, w1, w2; simpl in *; done.
      + destruct (W2 !! x) as [w2|] eqn:E2; last constructor. exfalso.
        pose proof (I2 x) as Ix. rewrite E2 lookup_insert_ne // in Ix.
        pose proof (I1 x) as Ix1. rewrite E1 in Ix1.
        destruct (Ω1 !! x); inversion Ix; inversion Ix1.
  Qed.

End owit_rels.
