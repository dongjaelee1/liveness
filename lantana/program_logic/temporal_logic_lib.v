From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import iprop.
From stdpp Require Import namespaces.
From lantana.base_logic Require Import obligation.
From lantana.program_logic Require Export temporal_logic.
From lantana.algebra Require Import ordinal_ucmra.
From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat mono_list.
From transfinite.base_logic.lib Require Import ghost_map.
(** For func_ext. *)
From lantana.prelude Require Import axioms.

Definition uchain_log_wf (l : list (oid * Ord.t)) : Prop :=
  ∀ i (e1 e2 : oid * Ord.t),
  (l !! i = Some e1) → (l !! (S i) = Some e2) → (e1.2 < e2.2)%ord.

(** Properties of wf. *)
Section proof.

  Lemma uchain_log_wf_lookup_1 l i j e1 e2 :
    uchain_log_wf l → l !! i = Some e1 → l !! j = Some e2 → i < j → (e1.2 < e2.2)%ord.
  Proof.
    revert i j e1 e2. induction l; intros. 1: done. inv H2.
    - rewrite lookup_cons in H0. rewrite lookup_cons in H1. destruct i.
      + inv H0. specialize (H 0). eapply H; simpl; auto.
      + eapply IHl; eauto. repeat intro. eapply H; eauto. simpl. auto.
    - simpl in *. rewrite lookup_cons in H0. destruct i.
      + inv H0. destruct (l !! 0) eqn:LU.
        * etrans.
          { eapply (H 0); simpl; eauto. }
          { eapply (IHl 0 m); eauto. repeat intro. eapply H; eauto. simpl. auto. }
        * apply lookup_ge_None in LU. apply lookup_lt_Some in H1. lia.
      + eapply (IHl i m); eauto.
        * repeat intro. eapply H; eauto. simpl. auto.
        * lia.
  Qed.

  Lemma uchain_log_wf_cons e l :
    uchain_log_wf (e :: l) ↔ (uchain_log_wf l ∧ ∀ i a, (l !! i = Some a) → (e.2 < a.2)%ord).
  Proof.
    split; intros.
    - split.
      + repeat intro. specialize (H (S i) e1 e2). apply H; simpl; auto.
      + intros. eapply (uchain_log_wf_lookup_1 _ 0 (S i) _ _ H); auto. lia.
    - destruct H. repeat intro. destruct i; simpl in *.
      + inv H1. eauto.
      + eapply H; eauto.
  Qed.

  Lemma uchain_log_wf_app l1 l2 :
    (uchain_log_wf l1 ∧ uchain_log_wf l2 ∧ (∀ i e a, l1 !! i = Some e → head l2 = Some a → (e.2 < a.2)%ord))
    ↔ uchain_log_wf (l1 ++ l2).
  Proof.
    rewrite head_lookup. split; intros.
    - destruct H as (?&?&?). repeat intro. apply lookup_app_Some in H2, H3. destruct H2, H3; eauto.
      + destruct H3. destruct (l2 !! 0) eqn:LU2.
        * inv H3.
          { replace (S i - length l1) with 0 in * by lia. rewrite LU2 in H4. inv H4. eapply H1; eauto. }
          etrans; first (eapply H1; eauto). eapply uchain_log_wf_lookup_1. 2,3: eauto. 1: auto. 1: lia.
        * apply lookup_ge_None in LU2. apply lookup_lt_Some in H4. lia.
      + destruct H2. apply lookup_lt_Some in H3. lia.
      + destruct H2, H3. eapply uchain_log_wf_lookup_1. 2,3: eauto. 1: auto. 1: lia.
    - split_and !.
      + repeat intro. eapply (H i); rewrite lookup_app; [by rewrite H0 | by rewrite H1].
      + repeat intro.
        assert (l1 !! (length l1 + i) = None).
        { apply lookup_ge_None. lia. }
        assert (l1 !! S (length l1 + i) = None).
        { apply lookup_ge_None. lia. }
        eapply (H (length l1 + i)); rewrite lookup_app; [rewrite H2 | rewrite H3].
        * replace (length l1 + i - length l1) with i by lia. auto.
        * replace (S (length l1 + i) - length l1) with (S i) by lia. auto.
      + intros. eapply (uchain_log_wf_lookup_1 _ i (length l1) e a H).
        * rewrite lookup_app H0. auto.
        * rewrite lookup_app. rewrite lookup_ge_None_2; auto. replace (length l1 - length l1) with 0 by lia. auto.
        * apply lookup_lt_Some in H0. lia.
  Qed.

  Lemma uchain_log_wf_lookup_2 l i j e1 e2 :
    uchain_log_wf l → l !! i = Some e1 → l !! j = Some e2 → (e1.2 < e2.2)%ord →
    (i < j).
  Proof.
    revert i j e1 e2. induction l; intros. 1: done.
    destruct i, j; simpl in *; auto.
    - inv H0. apply Ord.lt_irreflexive in H2. done.
    - lia.
    - inv H1. apply uchain_log_wf_cons in H. destruct H. apply H1 in H0.
      assert (e1.2 < e1.2)%ord by (etrans; eauto). apply Ord.lt_irreflexive in H3. done.
    - apply uchain_log_wf_cons in H. destruct H.
      pose proof (IHl _ _ _ _ H H0 H1 H2). lia.
  Qed.

End proof.

Module uchainGS.

  Class uchainGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    UchainGpreS {
        uchainGpreS_log : inG Σ (mono_listUR (prod oid Ord.t));
      }.

  Class uchainGS `{SI : indexT} (Σ : gFunctors) : Set :=
    UchainG {
        uchain_inG : uchainGpreS Σ;
        log_name : gname;
      }.

  Definition uchainΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (mono_listUR (prod oid Ord.t))
      ].

  Global Instance subG_uchainΣ `{SI : indexT} {Σ} : subG (uchainΣ) Σ → (uchainGpreS Σ).
  Proof. solve_inG. Qed.

End uchainGS.
Import uchainGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances uchain_inG uchainGpreS_log.

Local Definition uchain_auth_def `{SI : indexT} `{@uchainGS SI Σ}
  (q : Qp) (l : list (oid * Ord.t)) : iProp Σ :=
  (⌜ uchain_log_wf l ⌝ ∗ own log_name (●ML{#q} l))%I.
Local Definition uchain_auth_aux : seal (@uchain_auth_def). Proof. by eexists. Qed.
Definition uchain_auth := uchain_auth_aux.(unseal).
Local Definition uchain_auth_unseal :
  @uchain_auth = @uchain_auth_def := uchain_auth_aux.(seal_eq).
Global Arguments uchain_auth {SI Σ _}.

Local Definition uchain_pin_def `{SI : indexT} `{@uchainGS SI Σ}
  (e : oid * Ord.t) : iProp Σ :=
  (∃ (l : list (oid * Ord.t)),
      (⌜ last l = Some e ∧ uchain_log_wf l ⌝) ∧ own log_name (◯ML l))%I.
Local Definition uchain_pin_aux : seal (@uchain_pin_def). Proof. by eexists. Qed.
Definition uchain_pin := uchain_pin_aux.(unseal).
Local Definition uchain_pin_unseal :
  @uchain_pin = @uchain_pin_def := uchain_pin_aux.(seal_eq).
Global Arguments uchain_pin {SI Σ _}.

Fixpoint tf_until_chain_rec `{SI : indexT} {Π} {Σ}
  (N : namespace) k (o : Ord.t) (P Q : @tf SI Π Σ) (ACC : Acc Ord.lt o) {struct ACC} : tf Σ :=
  (tf_until N k false (1/2) P (Q ∨ (∃ k' (o' : Ord.t) (LTo : Ord.lt o' o), tf_until_chain_rec N k' o' P Q (Acc_inv ACC LTo))))%F.

Definition tf_until_chain `{SI : indexT} {Π} {Σ} (N : namespace) k o (P Q : @tf SI Π Σ) : tf Σ :=
  tf_until_chain_rec N k o P Q (Ord.lt_well_founded o).

Lemma tf_until_chain_rec_proof_irrelevance `{SI : indexT} {Π} {Σ} (N : namespace) k o (P Q : @tf SI Π Σ) ACC1 ACC2 :
  tf_until_chain_rec N k o P Q ACC1 = tf_until_chain_rec N k o P Q ACC2.
Proof.
  revert k ACC1 ACC2. induction o as [o IH] using (well_founded_ind Ord.lt_well_founded).
  intros. destruct ACC1, ACC2. simpl.
  do 3 f_equal. apply func_ext. intros. f_equal. apply func_ext. intros. f_equal. apply func_ext. intros.
  eapply IH. auto.
Qed.

Lemma tf_until_chain_unfold `{SI : indexT} {Π} {Σ} (N : namespace) k o (P Q : @tf SI Π Σ) :
  tf_until_chain N k o P Q = 
  (tf_until N k false (1/2) P (Q ∨ (∃ k' (o' : Ord.t) (LTo : Ord.lt o' o), tf_until_chain N k' o' P Q)))%F.
Proof.
  unfold tf_until_chain. destruct (Ord.lt_well_founded o). simpl.
  do 3 f_equal. apply func_ext. intros. f_equal. apply func_ext. intros. f_equal. apply func_ext. intros.
  apply tf_until_chain_rec_proof_irrelevance.
Qed.

Definition tf_until_chain_log `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!uchainGS Σ}
  (N : namespace) (P Q R : tf Σ) : tf Σ :=
  locked
    (∃ (l : list (oid * Ord.t)) k o,
        ⌜ ∃ m, (o <= measure_rep (ord.O, 1) m)%ord ⌝ ∗
        ⟨uchain_auth (1/2) (l ++ [(k, o)])⟩ ∗
        ([^tf_sep list] ko ∈ l, ⟨oblP_discharged ko.1⟩ ∗ ⌜ ∃ m, (ko.2 <= measure_rep (ord.O, 1) m)%ord ⌝) ∗
        (tf_until_chain N k o P Q ∨
           (⟨uchain_auth (1/2) (l ++ [(k, o)]) ∗ oblP_discharged k⟩ ∗ R))
    )%F.

Definition until_chain_log `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!uchainGS Σ}
  (N : namespace) (P Q R : tf Σ) : iProp Σ :=
  locked
    (∃ (l : list (oid * Ord.t)) k o,
        ⌜ ∃ m, (o <= measure_rep (ord.O, 1) m)%ord ⌝ ∗
               (uchain_auth (1/2) (l ++ [(k, o)])) ∗
               ([∗ list] ko ∈ l, (oblP_discharged ko.1) ∗ ⌜ ∃ m, (ko.2 <= measure_rep (ord.O, 1) m)%ord ⌝) ∗
               (⟦tf_until_chain N k o P Q⟧ₗ ∨
                  ((uchain_auth (1/2) (l ++ [(k, o)]) ∗ oblP_discharged k) ∗ ⟦R⟧ₗ))
    )%I.

Lemma tf_until_chain_log_red `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!uchainGS Σ} N P Q R :
  ⟦tf_until_chain_log N P Q R⟧ₗ ⊣⊢ until_chain_log N P Q R.
Proof.
  rewrite /tf_until_chain_log /until_chain_log -!lock.
  tf_red. do 2 f_equiv. tf_red. do 2 f_equiv. tf_red. do 2 f_equiv.
  tf_red. f_equiv. tf_red. f_equiv. f_equiv.
  rewrite tf_big_opL_interp. done.
Qed.
