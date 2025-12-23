From iris.proofmode Require Import proofmode.
From liris.base_logic Require Import ghost_lock.
(* Only to import rc; TODO refactor *)
From transfinite.stepindex Require Import utils.

Variant witness_state `{GL : ghost_lock_class} : Type :=
  | wit_locked (wit : gl_fuel)
  | wit_unlocked
.

Definition witness `{GL : ghost_lock_class} : Type := gl_version * witness_state.

Variant witness_step `{GL : ghost_lock_class} : witness → witness → Prop :=
  | witness_progress
      ver wit1 wit2
      (LTwit : wit2 w< wit1)
    :
    witness_step (ver, wit_locked wit1) (ver, wit_locked wit2)
  | witness_unlock
      ver wit
    :
    witness_step (ver, wit_locked wit) (ver, wit_unlocked)
  | witness_inc
      ver1 ver2
      (GTver : (ver1 < ver2)%nat)
    :
    witness_step (ver1, wit_unlocked) (ver2, wit_unlocked)
  | witness_lock
      ver1 ver2 wit
      (GTver : (ver1 < ver2)%nat)
    :
    witness_step (ver1, wit_unlocked) (ver2, wit_locked wit)
.

(** To a map *)
Notation witnesses := (gmap gl_id witness).

(* Only witnesses that satisfy wit_cond makes R *)
Definition wit_cond `{GL : ghost_lock_class} := (gl_id → witness → Prop).
Definition wits_cond_rel `{GL : ghost_lock_class} (C : wit_cond) (R : witness → witness → Prop) : witnesses → witnesses → Prop :=
  λ W1 W2, map_Forall2 (λ k w1 w2, (C k w1 ∧ R w1 w2) ∨ ((¬ C k w1) ∧ w1 = w2)) W1 W2.

Definition wit_rel_preserves_cond `{GL : ghost_lock_class} (C : wit_cond) (R : witness → witness → Prop) : Prop :=
  ∀ k w1 w2, C k w1 → R w1 w2 → C k w2.

(* Some useful wit_conds *)
Definition wit_cond_one `{GL : ghost_lock_class} (k : gl_id) : wit_cond :=
  λ x _, x = k.
Global Instance wit_cond_one_dec `{GL : ghost_lock_class} : ∀ k x w, Decision (wit_cond_one k x w).
Proof using. intros. rewrite /wit_cond_one. solve_decision. Qed.

Definition wit_cond_live `{GL : ghost_lock_class} : wit_cond :=
  λ _ w, match w with | (_, wit_locked _) => True | (_, wit_unlocked) => False end.
Global Instance wit_cond_live_dec `{GL : ghost_lock_class} : ∀ k w, Decision (wit_cond_live k w).
Proof using. intros. rewrite /wit_cond_live. destruct w. destruct w; solve_decision. Qed.

(* Witnesses step relation *)
Definition wits_cond_step `{GL : ghost_lock_class} (C : wit_cond) : witnesses → witnesses → Prop :=
  wits_cond_rel C witness_step.
Notation "A ↓ₛ B | C" := (wits_cond_step C A B) (at level 20, format "A  ↓ₛ  B  |  C").

Definition wits_alloc `{GL : ghost_lock_class} : witnesses → witnesses → Prop :=
  λ W1 W2, ∃ k v w, W1 !! k = None ∧ W2 = <[k:=(v, wit_locked w)]> W1.
Infix "↓ₐ" := (wits_alloc) (at level 20).

Variant wits_step `{GL : ghost_lock_class} : witnesses → witnesses → Prop :=
  | wits_step_cond_step W1 W2 C :
    (W1 ↓ₛ W2 | C) → wits_step W1 W2
  | wits_step_alloc W1 W2 :
    W1 ↓ₐ W2 → wits_step W1 W2.

Notation "A ↓ B" := (wits_step A B) (at level 20, format "A  ↓  B").
Notation "A ↓∘ B" := (rc (wits_step) A B) (at level 20, format "A  ↓∘  B").
Notation "A ↓⁺ B" := (tc (wits_step) A B) (at level 20, format "A  ↓⁺  B").
Notation "A ↓⋆ B" := (rtc (wits_step) A B) (at level 20, format "A  ↓⋆  B").

Section witnesses.
  Context `{GL : ghost_lock_class}.

  (** Properties *)
  Lemma wits_cond_rel_dom C R W1 W2 : wits_cond_rel C R W1 W2 → dom W1 = dom W2.
  Proof using. intros. eapply map_Forall2_dom_L; eauto. Qed.
  Lemma wits_cond_rel_tc_dom C R W1 W2 : tc (wits_cond_rel C R) W1 W2 → dom W1 = dom W2.
  Proof using.
    intros H. induction H.
    - eapply wits_cond_rel_dom; eauto.
    - rewrite <- IHtc. eapply wits_cond_rel_dom; eauto.
  Qed.
  Lemma wits_cond_rel_rtc_dom C R W1 W2 : rtc (wits_cond_rel C R) W1 W2 → dom W1 = dom W2.
  Proof using.
    intros H. induction H.
    - auto.
    - rewrite <- IHrtc. eapply wits_cond_rel_dom; eauto.
  Qed.

  (* If C1 and C2 are disjoint, can decompose *)
  Lemma wits_cond_rel_split_cond C C1 C2 R W1 W2 W3 :
    (∀ k g, C k g ↔ (C1 k g ∨ C2 k g)) →
    (∀ k g, (¬ C1 k g) ∨ (¬ C2 k g)) →
    wit_rel_preserves_cond C1 R →
    wits_cond_rel C1 R W1 W2 →
    wits_cond_rel C2 R W2 W3 →
    wits_cond_rel C R W1 W3.
  Proof using.
    intros HS1 HDisj HCR1. assert (HS2: ∀ k o, (¬ C k o) ↔ ((¬ C1 k o) ∧ (¬ C2 k o))).
    { intros. firstorder. }
    intros. intros k. specialize (H k). specialize (H0 k).
    inv H.
    - rewrite <-H2 in H0. inv H0. destruct H3 as [(HC1& HR1) | (NHC1& <-)].
      + destruct H5 as [(HC2& HR2) | (NHC2& ->)].
        * specialize (HCR1 _ _ _ HC1 HR1). destruct (HDisj k y); done.
        * econstructor. left. split; eauto. eapply HS1; eauto.
      + destruct H5 as [(HC2& HR2) | (NHC2& ->)].
        * econstructor. left. split; eauto. eapply HS1; eauto.
        * econstructor. right. split; auto. eapply HS2; eauto.
    - rewrite <-H3 in H0. inv H0. econstructor.
  Qed.

  Lemma wits_cond_rel_iff_lookup C1 C2 R W1 W2 :
    wits_cond_rel C1 R W1 W2 →
    (∀ k g, W1 !! k = Some g → (C1 k g ↔ C2 k g)) →
    wits_cond_rel C2 R W1 W2.
  Proof using.
    intros. intros ?. specialize (H i). destruct (W1 !! i) eqn:Ho1, (W2 !! i) eqn:Ho2; inv H; econstructor.
    specialize (H0 _ _ Ho1). destruct H3 as [(HC1& HR) | (NHC1& <-)].
    - left. split; auto. firstorder.
    - right. split; auto. firstorder.
  Qed.
  Lemma wits_cond_rel_iff C1 C2 R W1 W2 :
    wits_cond_rel C1 R W1 W2 →
    (∀ k g, C1 k g ↔ C2 k g) →
    wits_cond_rel C2 R W1 W2.
  Proof using. intros. eapply wits_cond_rel_iff_lookup; eauto. Qed.

End witnesses.

(** Witness of each version *)
Definition gl_witness `{GL : ghost_lock_class} : Type := gl_version → gl_fuel.

Fixpoint gl_witness_sum `{GL : ghost_lock_class} (ξ : gl_witness) (v : gl_version) : gl_fuel :=
  match v with
  | O => ξ v
  | S u => (gl_witness_sum ξ u) w+ (ξ v)
  end.
Notation "'gΣ' ξ v" := (gl_witness_sum ξ v) (at level 20, format "gΣ  ξ  v").

Definition gl_witness_constant `{GL : ghost_lock_class} (c : gl_fuel) : gl_witness := λ _, c.
