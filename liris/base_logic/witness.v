From iris.proofmode Require Import proofmode.
From liris.base_logic Require Import obligation.
(* Only to import rc; TODO refactor *)
From transfinite.stepindex Require Import utils.

Class wit_live_class (wit_count : Type) (wit_count_ltR : relation wit_count) := {
    wit_count_ltR_well_founded : well_founded wit_count_ltR;
    #[global] wit_count_ltR_Transitive :: Transitive wit_count_ltR;
  }.

Record wit_live_state `{Ξl : wit_live_class} := {
    wit_progress : wit_count;
  }.

Definition wit_state `{Ξl : wit_live_class} :=
  sum wit_live_state unit.

Definition wit_live `{Ξl : wit_live_class} (d : wit_live_state) : wit_state :=
  inl d.

Definition wit_done `{Ξl : wit_live_class} : wit_state :=
  inr tt.

Definition wlive `{Ξl : wit_live_class} α :=
  wit_live (Build_wit_live_state _ _ _ α).
Definition wdone `{Ξl : wit_live_class} :=
  wit_done.

(* Transition to make logical progress. *)
Definition wit_state_progress `{Ξl : wit_live_class} : relation wit_state :=
  λ o1 o2,
    (match o1, o2 with
     | inl d1, inl d2 =>
         wit_count_ltR (wit_progress d2) (wit_progress d1)
     | _, _ => False
     end).

(* Transition to resolve a liveness witness. *)
Definition wit_state_resolve `{Ξl : wit_live_class} : relation wit_state :=
  λ o1 o2,
    (match o1, o2 with
     | inl _, inr d => True
     | _, _ => False
     end).

(** To a map *)
Notation wit_states := (gmap obl_id wit_state).

Definition wit_cond `{Ξl : wit_live_class} := (obl_id → wit_state → Prop).
Definition wit_states_cond_rel `{Ξl : wit_live_class} (C : wit_cond) (R : wit_state → wit_state → Prop) : relation wit_states :=
  λ Ω1 Ω2, map_Forall2 (λ k o1 o2, (C k o1 → R o1 o2) ∧ ((¬ C k o1) → o1 = o2)) Ω1 Ω2.

Definition wit_states_progress `{Ξl : wit_live_class} (C : wit_cond) : relation wit_states :=
  wit_states_cond_rel C wit_state_progress.

Notation "A ↓ₚ B | C" := (wit_states_progress C A B) (at level 20, format "A  ↓ₚ  B  |  C").
Notation "A ↓ₚ⁺ B | C" := (tc (wit_states_progress C) A B) (at level 20, format "A  ↓ₚ⁺  B  |  C").
Notation "A ↓ₚ⋆ B | C" := (rtc (wit_states_progress C) A B) (at level 20, format "A  ↓ₚ⋆  B  |  C").

Definition wit_states_resolve `{Ξl : wit_live_class} (C : wit_cond) : relation wit_states :=
  wit_states_cond_rel C (wit_state_resolve).

Notation "A ↓ᵣ B | C" := (wit_states_resolve C A B) (at level 20, format "A  ↓ᵣ  B  |  C").
Notation "A ↓ᵣ⁺ B | C" := (tc (wit_states_resolve C) A B) (at level 20, format "A  ↓ᵣ⁺  B  |  C").
Notation "A ↓ᵣ⋆ B | C" := (rtc (wit_states_resolve C) A B) (at level 20, format "A  ↓ᵣ⋆  B  |  C").

Definition wit_states_alloc `{Ξl : wit_live_class} : relation wit_states :=
  λ Ω1 Ω2, ∃ k d, Ω1 !! k = None ∧ Ω2 = <[k:=wit_live d]> Ω1.

Infix "↓ₐ" := (wit_states_alloc) (at level 20).
Infix "↓ₐ⁺" := (tc wit_states_alloc) (at level 20).
Infix "↓ₐ⋆" := (rtc wit_states_alloc) (at level 20).

Variant wit_states_step `{Ξl : wit_live_class} : relation wit_states :=
  | wit_states_step_progress Ω1 Ω2 C :
    (∀ k o, Decision (C k o)) → (Ω1 ↓ₚ Ω2 | C) → wit_states_step Ω1 Ω2
  | wit_states_step_resolve Ω1 Ω2 C :
    (∀ k o, Decision (C k o)) → (Ω1 ↓ᵣ Ω2 | C) → wit_states_step Ω1 Ω2
  | wit_states_step_alloc Ω1 Ω2 :
    Ω1 ↓ₐ Ω2 → wit_states_step Ω1 Ω2.

Notation "A ↓ₛ B" := (wit_states_step A B) (at level 20, format "A  ↓ₛ  B").
Notation "A ↓ₛ⁺ B" := (tc (wit_states_step) A B) (at level 20, format "A  ↓ₛ⁺  B").
Notation "A ↓ₛ⋆ B" := (rtc (wit_states_step) A B) (at level 20, format "A  ↓ₛ⋆  B").
Notation "A ↓ₛ∘ B" := (rc (wit_states_step) A B) (at level 20, format "A  ↓ₛ∘  B").

Section wit_states.
  Context `{Ξl : wit_live_class}.

  (** Additional definitions *)
  Definition wit_rel_preserves_cond (C : wit_cond) (R : relation wit_state) : Prop :=
    ∀ k o0 o1, C k o0 → R o0 o1 → C k o1.

  Definition wit_cond_one (v : obl_id) : wit_cond :=
    λ k _, k = v.

  Definition wit_cond_live : wit_cond :=
    λ _ w, match w with | inl _ => True | inr _ => False end.

  Global Instance wit_cond_one_dec : ∀ v k w, Decision (wit_cond_one v k w).
  Proof using. intros. rewrite /wit_cond_one. solve_decision. Qed.

  Global Instance wit_cond_live_dec : ∀ k w, Decision (wit_cond_live k w).
  Proof using. intros. rewrite /wit_cond_live. destruct w; solve_decision. Qed.

  (** Properties *)
  Global Instance wit_state_progress_Transitive : Transitive wit_state_progress.
  Proof using.
    intros x y z H1 H2. destruct x, y, z; simpl in *; try done.
    etrans; eauto.
  Qed.
  Global Instance wit_state_resolve_Transitive : Transitive (wit_state_resolve).
  Proof using.
    intros x y z H1 H2. destruct x, y, z; simpl in *; try done.
  Qed.

  Lemma wit_state_progress_live o1 o2 :
    wit_state_progress o1 o2 →
    ∃ d1 d2, o1 = wit_live d1 ∧ o2 = wit_live d2 ∧
             (wit_count_ltR (wit_progress d2) (wit_progress d1)).
  Proof using.
    intros. destruct o1, o2; try done. simpl in H. do 2 eexists. split_and; eauto.
  Qed.
  Lemma wit_state_progress_tc_live o1 o2 :
    tc wit_state_progress o1 o2 →
    ∃ d1 d2, o1 = wit_live d1 ∧ o2 = wit_live d2 ∧
             (wit_count_ltR (wit_progress d2) (wit_progress d1)).
  Proof using.
    intros. induction H.
    { apply (wit_state_progress_live x y); auto. }
    apply wit_state_progress_live in H.
    destruct H as (?&?&?&?&?). destruct IHtc as (?&?&?&?&?).
    subst. inv H3. exists x0, x3. split_and !; auto.
    all: etrans; eauto.
  Qed.

  Lemma wit_state_progress_preserves_live o1 o2 :
    wit_state_progress o1 o2 → (∃ d1, o1 = wit_live d1) ↔ (∃ d2, o2 = wit_live d2).
  Proof using.
    intros. split; intros [? ?]; subst.
    - destruct o2; try eauto; done.
    - destruct o1; try eauto; done.
  Qed.
  Lemma wit_state_progress_tc_preserves_live o1 o2 :
    tc wit_state_progress o1 o2 → (∃ d1, o1 = wit_live d1) ↔ (∃ d2, o2 = wit_live d2).
  Proof using.
    intros. split.
    - induction H.
      { apply (wit_state_progress_preserves_live x y); auto. }
      intros [? ?]. subst. apply wit_state_progress_preserves_live in H. destruct H.
      apply IHtc in H; eauto.
    - induction H.
      { apply (wit_state_progress_preserves_live x y); auto. }
      intros [? ?]. subst. apply wit_state_progress_preserves_live in H. destruct H.
      apply H1. eapply IHtc; eauto.
  Qed.
  Lemma wit_state_progress_rtc_preserves_live o1 o2 :
    rtc wit_state_progress o1 o2 → (∃ d1, o1 = wit_live d1) ↔ (∃ d2, o2 = wit_live d2).
  Proof using.
    intros. split.
    - induction H.
      { eauto. }
      intros [? ?]. subst. apply wit_state_progress_preserves_live in H. destruct H.
      apply IHrtc in H; eauto.
    - induction H.
      { eauto. }
      intros [? ?]. subst. apply wit_state_progress_preserves_live in H. destruct H.
      apply H1. eapply IHrtc; eauto.
  Qed.

  Global Instance wit_states_cond_rel_Transitive C R :
    wit_rel_preserves_cond C R →
    Transitive R →
    Transitive (wit_states_cond_rel C R).
  Proof using.
    intros HCR HRT x y z H1 H2. intros i. specialize (H1 i). specialize (H2 i).
    destruct (x !! i) eqn:Hxi; inv H1.
    - rewrite -H0 in H2. inv H2. destruct H3, H4. econstructor. split; intro HC.
      + specialize (H HC). etrans; first eauto. apply H3. eapply HCR; eauto.
      + specialize (H2 HC). subst. apply H4; auto.
    - rewrite -H in H2. inv H2. econstructor.
  Qed.

  Lemma wit_states_cond_rel_dom C R Ω1 Ω2 : wit_states_cond_rel C R Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using. intros. eapply map_Forall2_dom_L; eauto. Qed.
  Lemma wit_states_cond_rel_tc_dom C R Ω1 Ω2 : tc (wit_states_cond_rel C R) Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - eapply wit_states_cond_rel_dom; eauto.
    - rewrite <- IHtc. eapply wit_states_cond_rel_dom; eauto.
  Qed.
  Lemma wit_states_cond_rel_rtc_dom C R Ω1 Ω2 : rtc (wit_states_cond_rel C R) Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - auto.
    - rewrite <- IHrtc. eapply wit_states_cond_rel_dom; eauto.
  Qed.

  Lemma wit_states_cond_rel_lookup C R Ω1 Ω2 :
    wit_states_cond_rel C R Ω1 Ω2 →
    ∀ k, option_Forall2 (λ o1 o2, ((C k o1) → R o1 o2) ∧ ((¬ C k o1) → o1 = o2)) (Ω1 !! k) (Ω2 !! k).
  Proof using. done. Qed.
  Lemma wit_states_cond_rel_tc_lookup C R Ω1 Ω2 :
    wit_rel_preserves_cond C R →
    Transitive R →
    tc (wit_states_cond_rel C R) Ω1 Ω2 →
    ∀ k, option_Forall2 (λ o1 o2, ((C k o1) → tc R o1 o2) ∧ ((¬ C k o1) → o1 = o2)) (Ω1 !! k) (Ω2 !! k).
  Proof using.
    intros HCR HTR H. induction H; intros.
    - pose proof (wit_states_cond_rel_lookup _ _ _ _ H k). inv H0; econstructor.
      destruct H3. split; auto. intros. econstructor 1; auto.
    - pose proof (wit_states_cond_rel_lookup _ _ _ _ H k). specialize (IHtc k). inv IHtc.
      + destruct H4. rewrite <-H2 in H1. inv H1. destruct H8. econstructor. split; intros.
        * specialize (H1 H8). specialize (HCR _ _ _ H8 H1). specialize (H4 HCR). econstructor 2; eauto.
        * specialize (H7 H8). subst. auto.
      + rewrite <-H3 in H1. inv H1. econstructor.
  Qed.
  Lemma wit_states_cond_rel_rtc_lookup C R Ω1 Ω2 :
    wit_rel_preserves_cond C R →
    Transitive R →
    rtc (wit_states_cond_rel C R) Ω1 Ω2 →
    ∀ k, option_Forall2 (λ o1 o2, ((C k o1) → rtc R o1 o2) ∧ ((¬ C k o1) → o1 = o2)) (Ω1 !! k) (Ω2 !! k).
  Proof using.
    intros HCR HTR H. induction H; intros.
    - destruct (x !! k); econstructor. split; done.
    - pose proof (wit_states_cond_rel_lookup _ _ _ _ H k). specialize (IHrtc k). inv IHrtc.
      + destruct H4. rewrite <-H2 in H1. inv H1. destruct H8. econstructor. split; intros.
        * specialize (H1 H8). specialize (HCR _ _ _ H8 H1). specialize (H4 HCR). econstructor 2; eauto.
        * specialize (H7 H8). subst. auto.
      + rewrite <-H3 in H1. inv H1. econstructor.
  Qed.

  Lemma wit_states_cond_rel_split_cond C C1 C2 R Ω1 Ω2 Ω3 :
    (∀ k o, Decision (C1 k o)) →
    (∀ k o, Decision (C2 k o)) →
    Transitive R →
    (∀ k o, C k o ↔ (C1 k o ∨ C2 k o)) →
    wit_rel_preserves_cond C2 R →
    wit_states_cond_rel C1 R Ω1 Ω2 →
    wit_states_cond_rel C2 R Ω2 Ω3 →
    wit_states_cond_rel C R Ω1 Ω3.
  Proof using.
    intros HD1 HD2 HTR HS1 HCR2. assert (HS2: ∀ k o, (¬ C k o) → ((¬ C1 k o) ∧ (¬ C2 k o))).
    { intros. destruct (HS1 k o). destruct (decide ((C1 k o ∨ C2 k o))).
      - specialize (H1 o0). auto.
      - firstorder.
    }
    intros. intros k. specialize (H k). specialize (H0 k).
    inv H.
    - destruct H3. rewrite <-H2 in H0. inv H0. destruct H6. econstructor. split; intros.
      + destruct (HS1 k x). clear H8 HS1. rename H7 into HS1. destruct (HS1 H6).
        * specialize (H H7). destruct (decide (C2 k y)); eauto. specialize (H4 n). by subst.
        * destruct (decide (C1 k x)).
          -- specialize (H c). etrans; first eauto. specialize (HCR2 _ _ _ H7 H). auto.
          -- specialize (H3 n). subst. auto.
      + destruct (HS2 _ _ H6). specialize (H3 H7). subst. specialize (H4 H8). subst. auto.
    - rewrite -H3 in H0. inv H0. econstructor.
  Qed.

  Lemma wit_states_cond_rel_iff_lookup C1 C2 R Ω1 Ω2 :
    wit_states_cond_rel C1 R Ω1 Ω2 →
    (∀ k o, Ω1 !! k = Some o → (C1 k o ↔ C2 k o)) →
    wit_states_cond_rel C2 R Ω1 Ω2.
  Proof using.
    intros. intros ?. specialize (H i). destruct (Ω1 !! i) eqn:Ho1, (Ω2 !! i) eqn:Ho2; inv H; econstructor.
    specialize (H0 _ _ Ho1). destruct H3. split; intros.
    - apply H. by apply H0.
    - apply H1. intros ?; apply H2. by apply H0.
  Qed.
  Lemma wit_states_cond_rel_iff C1 C2 R Ω1 Ω2 :
    wit_states_cond_rel C1 R Ω1 Ω2 →
    (∀ k o, C1 k o ↔ C2 k o) →
    wit_states_cond_rel C2 R Ω1 Ω2.
  Proof using. intros. eapply wit_states_cond_rel_iff_lookup; eauto. Qed.

End wit_states.
