From iris.proofmode Require Import proofmode.

Definition prop_of (T : Type) := (T → Prop).

Global Instance prop_of_iff (T : Type) : Equiv (prop_of T) :=
  λ P1 P2, ∀ (s : T), (P1 s) ↔ (P2 s).

Global Instance prop_of_iff_equivalence T : Equivalence (@equiv _ (prop_of_iff T)).
Proof. firstorder. Qed.

Canonical Structure prop_ofO `{SI : indexT} (T : Type) := leibnizO (prop_of T).


(* FIXME : Move to somewhere else *)
Lemma sn_tc {X} (R : X → X → Prop) (x : X): sn R x ↔ sn (tc R) x.
Proof.
  split.
  - induction 1 as [x _ IH]; constructor; simpl; intros y Hy; revert IH; simpl.
    destruct Hy as [x y Honce|x y z Honce Hsteps]; intros IH; eauto.
    destruct (IH _ Honce) as [Hy]; eauto.
  - induction 1 as [z _ IH]; constructor; intros ??; apply IH; simpl in *; eauto using tc_once.
Qed.

Class obl_live_class (obl_count obl_ownerid : Type) (obl_count_ltR : relation obl_count) := {
    obl_count_ltR_well_founded : well_founded obl_count_ltR;
    #[global] obl_count_ltR_Transitive :: Transitive obl_count_ltR;
    #[global] obl_ownerid_EqDecision :: EqDecision obl_ownerid;
  }.

Record obl_live_state `{Ξl : obl_live_class} := {
    obl_owner : obl_ownerid;
    obl_progress : obl_count;
  }.

Class obl_done_class (obl_ps : Type) := {
    obl_done_class_placeholder : unit;
  }.

Record obl_done_state `{Ξd : obl_done_class} := {
    obl_atom : prop_of obl_ps;
  }.

Definition obl_state `{Ξl : obl_live_class} `{Ξd : obl_done_class} :=
  sum obl_live_state obl_done_state.

Definition obl_live `{Ξl : obl_live_class} `{Ξd : obl_done_class} (d : obl_live_state) : obl_state :=
  inl d.

Definition obl_done `{Ξl : obl_live_class} `{Ξd : obl_done_class} (d : obl_done_state) : obl_state :=
  inr d.

Definition olive `{Ξl : obl_live_class} `{Ξd : obl_done_class} θ α :=
  obl_live (Build_obl_live_state _ _ _ _ θ α).
Definition odone `{Ξl : obl_live_class} `{Ξd : obl_done_class} (P : prop_of obl_ps) :=
  obl_done (Build_obl_done_state _ _ P).

(* Transition to make logical progress that can obtain a later. *)
Definition obl_state_progress `{Ξl : obl_live_class} `{Ξd : obl_done_class} : relation obl_state :=
  λ o1 o2,
    (match o1, o2 with
     | inl d1, inl d2 =>
         (obl_owner d1 = obl_owner d2) ∧ obl_count_ltR (obl_progress d2) (obl_progress d1)
     | _, _ => False
     end).

(* Transition to resolve a liveness obligation. *)
Definition obl_state_resolve `{Ξl : obl_live_class} `{Ξd : obl_done_class} (s : obl_ps) : relation obl_state :=
  λ o1 o2,
    (match o1, o2 with
     | inl _, inr d =>
         obl_atom d s
     | _, _ => False
     end).

(** To a map *)
Definition obl_id := positive.

Notation obl_ids := (gset obl_id).
Notation obl_states := (gmap obl_id obl_state).

Definition obl_cond `{Ξl : obl_live_class} `{Ξd : obl_done_class} := (obl_id → obl_state → Prop).
Definition obl_states_cond_rel `{Ξl : obl_live_class} `{Ξd : obl_done_class} (C : obl_cond) (R : obl_state → obl_state → Prop) : relation obl_states :=
  λ Ω1 Ω2, map_Forall2 (λ k o1 o2, (C k o1 → R o1 o2) ∧ ((¬ C k o1) → o1 = o2)) Ω1 Ω2.

Definition obl_states_progress `{Ξl : obl_live_class} `{Ξd : obl_done_class} (C : obl_cond) : relation obl_states :=
  obl_states_cond_rel C obl_state_progress.

Notation "A ↪ₚ B | C" := (obl_states_progress C A B) (at level 20, format "A  ↪ₚ  B  |  C").
Notation "A ↪ₚ⁺ B | C" := (tc (obl_states_progress C) A B) (at level 20, format "A  ↪ₚ⁺  B  |  C").
Notation "A ↪ₚ⋆ B | C" := (rtc (obl_states_progress C) A B) (at level 20, format "A  ↪ₚ⋆  B  |  C").

Definition obl_states_resolve `{Ξl : obl_live_class} `{Ξd : obl_done_class} (s : obl_ps) (C : obl_cond) : relation obl_states :=
  obl_states_cond_rel C (obl_state_resolve s).

Notation "A ↪ᵣ B @ s | C" := (obl_states_resolve s C A B) (at level 20, format "A  ↪ᵣ  B  @  s  |  C").
Notation "A ↪ᵣ⁺ B @ s | C" := (tc (obl_states_resolve s C) A B) (at level 20, format "A  ↪ᵣ⁺  B  @  s  |  C").
Notation "A ↪ᵣ⋆ B @ s | C" := (rtc (obl_states_resolve s C) A B) (at level 20, format "A  ↪ᵣ⋆  B  @  s  |  C").

Definition obl_states_alloc `{Ξl : obl_live_class} `{Ξd : obl_done_class} : relation obl_states :=
  λ Ω1 Ω2, ∃ k d, Ω1 !! k = None ∧ Ω2 = <[k:=obl_live d]> Ω1.

Infix "↪ₐ" := (obl_states_alloc) (at level 20).
Infix "↪ₐ⁺" := (tc obl_states_alloc) (at level 20).
Infix "↪ₐ⋆" := (rtc obl_states_alloc) (at level 20).

Variant obl_states_step `{Ξl : obl_live_class} `{Ξd : obl_done_class} (s : obl_ps) : relation obl_states :=
  | obl_states_step_progress Ω1 Ω2 :
    (∃ C, Ω1 ↪ₚ Ω2 | C) → obl_states_step s Ω1 Ω2
  | obl_states_step_resolve Ω1 Ω2 :
    (∃ C, Ω1 ↪ᵣ Ω2 @ s | C) → obl_states_step s Ω1 Ω2
  | obl_states_step_alloc Ω1 Ω2 :
    Ω1 ↪ₐ Ω2 → obl_states_step s Ω1 Ω2.

Notation "A ↪ₛ B @ s" := (obl_states_step s A B) (at level 20, format "A  ↪ₛ  B  @  s").
Notation "A ↪ₛ⁺ B @ s" := (tc (obl_states_step s) A B) (at level 20, format "A  ↪ₛ⁺  B  @  s").
Notation "A ↪ₛ⋆ B @ s" := (rtc (obl_states_step s) A B) (at level 20, format "A  ↪ₛ⋆  B  @  s").

Section obl_states.
  Context `{Ξl : obl_live_class} `{Ξd : obl_done_class}.

  (** Additional definitions *)
  Definition obl_cond_owner (i : obl_ownerid) : obl_cond :=
    λ _ o, match o with | inl d => (obl_owner d = i) | _ => False end.

  Definition obl_rel_preserves_cond (C : obl_cond) (R : relation obl_state) : Prop :=
    ∀ k o0 o1, C k o0 → R o0 o1 → C k o1.

  (** Properties *)
  Global Instance obl_state_progress_Transitive : Transitive obl_state_progress.
  Proof using.
    intros x y z H1 H2. destruct x, y, z; simpl in *; try done.
    destruct H1 as (?&?). destruct H2 as (?&?). split_and !; try (etrans; eauto).
  Qed.
  Global Instance obl_state_resolve_Transitive s : Transitive (obl_state_resolve s).
  Proof using.
    intros x y z H1 H2. destruct x, y, z; simpl in *; try done.
  Qed.

  Lemma obl_state_progress_live o1 o2 :
    obl_state_progress o1 o2 →
    ∃ d1 d2, o1 = obl_live d1 ∧ o2 = obl_live d2 ∧
             (obl_owner d1 = obl_owner d2) ∧
             (obl_count_ltR (obl_progress d2) (obl_progress d1)).
  Proof using.
    intros. destruct o1, o2; try done. simpl in H. do 2 eexists. split_and; eauto.
  Qed.
  Lemma obl_state_progress_tc_live o1 o2 :
    tc obl_state_progress o1 o2 →
    ∃ d1 d2, o1 = obl_live d1 ∧ o2 = obl_live d2 ∧
             (obl_owner d1 = obl_owner d2) ∧
             (obl_count_ltR (obl_progress d2) (obl_progress d1)).
  Proof using.
    intros. induction H.
    { apply (obl_state_progress_live x y); auto. }
    apply obl_state_progress_live in H.
    destruct H as (?&?&?&?&?&?). destruct IHtc as (?&?&?&?&?&?).
    subst. inv H2. exists x0, x3. split_and !; auto.
    all: etrans; eauto.
  Qed.

  Lemma obl_state_progress_preserves_live o1 o2 :
    obl_state_progress o1 o2 → (∃ d1, o1 = obl_live d1) ↔ (∃ d2, o2 = obl_live d2).
  Proof using.
    intros. split; intros [? ?]; subst.
    - destruct o2; try eauto; done.
    - destruct o1; try eauto; done.
  Qed.
  Lemma obl_state_progress_tc_preserves_live o1 o2 :
    tc obl_state_progress o1 o2 → (∃ d1, o1 = obl_live d1) ↔ (∃ d2, o2 = obl_live d2).
  Proof using.
    intros. split.
    - induction H.
      { apply (obl_state_progress_preserves_live x y); auto. }
      intros [? ?]. subst. apply obl_state_progress_preserves_live in H. destruct H.
      apply IHtc in H; eauto.
    - induction H.
      { apply (obl_state_progress_preserves_live x y); auto. }
      intros [? ?]. subst. apply obl_state_progress_preserves_live in H. destruct H.
      apply H1. eapply IHtc; eauto.
  Qed.
  Lemma obl_state_progress_rtc_preserves_live o1 o2 :
    rtc obl_state_progress o1 o2 → (∃ d1, o1 = obl_live d1) ↔ (∃ d2, o2 = obl_live d2).
  Proof using.
    intros. split.
    - induction H.
      { eauto. }
      intros [? ?]. subst. apply obl_state_progress_preserves_live in H. destruct H.
      apply IHrtc in H; eauto.
    - induction H.
      { eauto. }
      intros [? ?]. subst. apply obl_state_progress_preserves_live in H. destruct H.
      apply H1. eapply IHrtc; eauto.
  Qed.

  Global Instance obl_states_cond_rel_Transitive C R :
    obl_rel_preserves_cond C R →
    Transitive R →
    Transitive (obl_states_cond_rel C R).
  Proof using.
    intros HCR HRT x y z H1 H2. intros i. specialize (H1 i). specialize (H2 i).
    destruct (x !! i) eqn:Hxi; inv H1.
    - rewrite -H0 in H2. inv H2. destruct H3, H4. econstructor. split; intro HC.
      + specialize (H HC). etrans; first eauto. apply H3. eapply HCR; eauto.
      + specialize (H2 HC). subst. apply H4; auto.
    - rewrite -H in H2. inv H2. econstructor.
  Qed.

  Lemma obl_state_progress_cond_owner i : obl_rel_preserves_cond (obl_cond_owner i) obl_state_progress.
  Proof using.
    intros k o0 o1 Hc Hr. destruct o0, o1; try done. simpl in *. destruct Hr. inv H. auto.
  Qed.

  Global Instance obl_cond_owner_Decision i : ∀ k o, Decision (obl_cond_owner i k o).
  Proof using. intros. unfold obl_cond_owner. destruct o; solve_decision. Qed.

  Lemma obl_states_cond_rel_dom C R Ω1 Ω2 : obl_states_cond_rel C R Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using. intros. eapply map_Forall2_dom_L; eauto. Qed.
  Lemma obl_states_cond_rel_tc_dom C R Ω1 Ω2 : tc (obl_states_cond_rel C R) Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - eapply obl_states_cond_rel_dom; eauto.
    - rewrite <- IHtc. eapply obl_states_cond_rel_dom; eauto.
  Qed.
  Lemma obl_states_cond_rel_rtc_dom C R Ω1 Ω2 : rtc (obl_states_cond_rel C R) Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - auto.
    - rewrite <- IHrtc. eapply obl_states_cond_rel_dom; eauto.
  Qed.

  Lemma obl_states_cond_rel_lookup C R Ω1 Ω2 :
    obl_states_cond_rel C R Ω1 Ω2 →
    ∀ k, option_Forall2 (λ o1 o2, ((C k o1) → R o1 o2) ∧ ((¬ C k o1) → o1 = o2)) (Ω1 !! k) (Ω2 !! k).
  Proof using. done. Qed.
  Lemma obl_states_cond_rel_tc_lookup C R Ω1 Ω2 :
    obl_rel_preserves_cond C R →
    Transitive R →
    tc (obl_states_cond_rel C R) Ω1 Ω2 →
    ∀ k, option_Forall2 (λ o1 o2, ((C k o1) → tc R o1 o2) ∧ ((¬ C k o1) → o1 = o2)) (Ω1 !! k) (Ω2 !! k).
  Proof using.
    intros HCR HTR H. induction H; intros.
    - pose proof (obl_states_cond_rel_lookup _ _ _ _ H k). inv H0; econstructor.
      destruct H3. split; auto. intros. econstructor 1; auto.
    - pose proof (obl_states_cond_rel_lookup _ _ _ _ H k). specialize (IHtc k). inv IHtc.
      + destruct H4. rewrite <-H2 in H1. inv H1. destruct H8. econstructor. split; intros.
        * specialize (H1 H8). specialize (HCR _ _ _ H8 H1). specialize (H4 HCR). econstructor 2; eauto.
        * specialize (H7 H8). subst. auto.
      + rewrite <-H3 in H1. inv H1. econstructor.
  Qed.
  Lemma obl_states_cond_rel_rtc_lookup C R Ω1 Ω2 :
    obl_rel_preserves_cond C R →
    Transitive R →
    rtc (obl_states_cond_rel C R) Ω1 Ω2 →
    ∀ k, option_Forall2 (λ o1 o2, ((C k o1) → rtc R o1 o2) ∧ ((¬ C k o1) → o1 = o2)) (Ω1 !! k) (Ω2 !! k).
  Proof using.
    intros HCR HTR H. induction H; intros.
    - destruct (x !! k); econstructor. split; done.
    - pose proof (obl_states_cond_rel_lookup _ _ _ _ H k). specialize (IHrtc k). inv IHrtc.
      + destruct H4. rewrite <-H2 in H1. inv H1. destruct H8. econstructor. split; intros.
        * specialize (H1 H8). specialize (HCR _ _ _ H8 H1). specialize (H4 HCR). econstructor 2; eauto.
        * specialize (H7 H8). subst. auto.
      + rewrite <-H3 in H1. inv H1. econstructor.
  Qed.

  Lemma obl_states_cond_rel_split_cond C C1 C2 R Ω1 Ω2 Ω3 :
    (∀ k o, Decision (C1 k o)) →
    (∀ k o, Decision (C2 k o)) →
    Transitive R →
    (∀ k o, C k o ↔ (C1 k o ∨ C2 k o)) →
    obl_rel_preserves_cond C2 R →
    obl_states_cond_rel C1 R Ω1 Ω2 →
    obl_states_cond_rel C2 R Ω2 Ω3 →
    obl_states_cond_rel C R Ω1 Ω3.
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

  Lemma obl_states_cond_rel_iff_lookup C1 C2 R Ω1 Ω2 :
    obl_states_cond_rel C1 R Ω1 Ω2 →
    (∀ k o, Ω1 !! k = Some o → (C1 k o ↔ C2 k o)) →
    obl_states_cond_rel C2 R Ω1 Ω2.
  Proof using.
    intros. intros ?. specialize (H i). destruct (Ω1 !! i) eqn:Ho1, (Ω2 !! i) eqn:Ho2; inv H; econstructor.
    specialize (H0 _ _ Ho1). destruct H3. split; intros.
    - apply H. by apply H0.
    - apply H1. intros ?; apply H2. by apply H0.
  Qed.
  Lemma obl_states_cond_rel_iff C1 C2 R Ω1 Ω2 :
    obl_states_cond_rel C1 R Ω1 Ω2 →
    (∀ k o, C1 k o ↔ C2 k o) →
    obl_states_cond_rel C2 R Ω1 Ω2.
  Proof using. intros. eapply obl_states_cond_rel_iff_lookup; eauto. Qed.

End obl_states.
