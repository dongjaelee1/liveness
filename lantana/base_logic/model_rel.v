(** * Round relations of the obligation model

    A round of [mupd] may change several obligations at once (moving a subtree changes the
    owner of all its nodes), so rounds use pointwise relations: [obls_ndf] (every obligation
    stays or makes progress; new ones may be added), [obls_lef] (also discharges), and
    [wits_ndf] / [wits_lef] (witnesses do not increase). [obls_lef] implies the order
    [obls_le] seen by adequacy. *)

From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
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

End rels.

Section owit_rels.
  Context `{!ord_mono_fun_class}.

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

(** * Choice of witnesses

    [owit_inv_lb γ Ω W]: the witness of every assigned obligation (fuel [a], owner [i]) is at
    least [γ i a]. After a round [obls_lef Ω1 Ω2], witnesses that keep the invariants exist. *)
Section witness_choice.
  Context `{OMC : !ord_mono_fun_class}.

  Definition owit_inv_lb (γ : obl_owner → obl_fuel → obl_fuel) (Ω : obls) (W : witnesses) : Prop :=
    map_Forall2
      (λ (_ : oid) (g : obl) (w : witness),
         match g with
         | obl_assigned a i => match w with
                              | witness_assigned b => (γ i a) w≤ b
                              | witness_discharged => False
                              end
         | obl_discharged => match w with
                           | witness_assigned _ => False
                           | witness_discharged => True
                           end
         end)
      Ω W.

  Definition owit_inv_lb_mon (γ : obl_owner → obl_fuel → obl_fuel) : Prop :=
    (∀ a b i j, (a w< b) → (γ i a w< γ j b)) ∧ (∀ i a, γ i a w≤ η a).

  Lemma map_Forall2_choice {A B : Type} (Ω2 : gmap oid A) (P : oid → A → B → Prop) :
    (∀ k a, Ω2 !! k = Some a → ∃ b, P k a b) → ∃ W2 : gmap oid B, map_Forall2 P Ω2 W2.
  Proof.
    induction Ω2 as [|k a Ω2 Hk IH] using map_ind; intros HP.
    { exists ∅. intros i. rewrite !lookup_empty. constructor. }
    destruct IH as [W2 HW2].
    { intros i b Hi. apply HP. rewrite lookup_insert_ne; first done. intros ->. by rewrite Hk in Hi. }
    destruct (HP k a) as [b Hb]; first by rewrite lookup_insert_eq.
    exists (<[k:=b]> W2). intros i. destruct (decide (i = k)) as [->|Hne].
    - rewrite !lookup_insert_eq. by constructor.
    - rewrite !lookup_insert_ne; auto.
  Qed.

  (** The witness chosen for an obligation that changed. *)
  Definition wit_of (γ : obl_owner → obl_fuel → obl_fuel) (g : obl (OC:=ord_obl_class)) :
    witness (OC:=ord_obl_class) :=
    match g with
    | obl_assigned a i => witness_assigned (γ i a)
    | obl_discharged => witness_discharged
    end.

  Lemma owit_inv_exists_witnesses γ Ω1 Ω2 W1 :
    owit_inv_lb_mon γ →
    obls_lef Ω1 Ω2 →
    owit_inv Ω1 W1 →
    owit_inv_lb γ Ω1 W1 →
    ∃ W2, wits_lef W1 W2 ∧ owit_inv Ω2 W2 ∧ owit_inv_lb γ Ω2 W2.
  Proof.
    intros [GMon GSched] Step Inv LB.
    destruct (map_Forall2_choice Ω2
      (λ k g2 w2,
         (match (g2 : obl (OC:=ord_obl_class)), (w2 : witness (OC:=ord_obl_class)) with
          | obl_assigned a _, witness_assigned b => b w≤ η a
          | obl_discharged, witness_discharged => True
          | _, _ => False
          end) ∧
         (match (g2 : obl (OC:=ord_obl_class)) with
          | obl_assigned a i => match (w2 : witness (OC:=ord_obl_class)) with
                               | witness_assigned b => γ i a w≤ b
                               | witness_discharged => False
                               end
          | obl_discharged => match (w2 : witness (OC:=ord_obl_class)) with
                             | witness_assigned _ => False
                             | witness_discharged => True
                             end
          end) ∧
         (∀ w1, W1 !! k = Some w1 → wit_le w1 w2))) as [W2 HW2].
    { intros k g2 Hg2. destruct (Classical_Prop.classic (Ω1 !! k = Some g2)) as [Hsame|Hdiff].
      - pose proof (Inv k) as Ik. pose proof (LB k) as Lk. rewrite Hsame in Ik, Lk.
        destruct (W1 !! k) as [w1|] eqn:Hw1; inversion Ik as [? ? Hm|]; subst.
        inversion Lk as [? ? Hl|]; subst.
        exists w1. split_and!; [done|done|]. intros w1' [=<-].
        destruct g2, w1; simpl in *; try done; reflexivity.
      - exists (wit_of γ g2). split_and!.
        + destruct g2; simpl; [apply GSched|done].
        + destruct g2; simpl; [reflexivity|done].
        + intros w1 Hw1. pose proof (Inv k) as Ik. rewrite Hw1 in Ik.
          destruct (Ω1 !! k) as [g1|] eqn:Hg1; inversion Ik as [? ? Hm|]; subst.
          destruct (Step k g1 Hg1) as (g2'& Hg2'& Hrel). rewrite Hg2 in Hg2'.
          injection Hg2' as <-. destruct Hrel as [->|Hs]; first done.
          pose proof (LB k) as Lk. rewrite Hg1 Hw1 in Lk. inversion Lk as [? ? Hl|]; subst.
          inversion Hs as [? ? Hp| ? ? Hd]; subst.
          * inversion Hp; subst. destruct w1; simpl in *; try done.
            apply WFOCM.lt_le. eapply WFOCM.lt_le_lt; last done. by apply GMon.
          * inversion Hd; subst. destruct w1; simpl in *; done. }
    exists W2. split_and!.
    - intros k w1 Hw1. pose proof (Inv k) as Ik. rewrite Hw1 in Ik.
      destruct (Ω1 !! k) as [g1|] eqn:Hg1; inversion Ik; subst.
      destruct (Step k g1 Hg1) as (g2& Hg2& _).
      pose proof (HW2 k) as Hk. rewrite Hg2 in Hk.
      destruct (W2 !! k) as [w2|] eqn:Hw2; inversion Hk as [? ? (_& _& Hle)|]; subst.
      exists w2. split; first done. by apply Hle.
    - eapply map_Forall2_impl; first done. by intros ??? (?&_&_).
    - eapply map_Forall2_impl; first done. by intros ??? (_&?&_).
  Qed.

End witness_choice.
