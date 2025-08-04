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

Class obl_class (obl_count obl_ps obl_owner : Type) := {
    obl_count_ltR : obl_count → obl_count → Prop;
    obl_count_ltR_wf : well_founded obl_count_ltR;
  }.

Record obl_live_data `{Δ : obl_class} := {
    obl_transfer : obl_count;
    obl_owner : obl_owner;
    obl_credit : obl_count;
  }.

Inductive obl_state `{Δ : obl_class} : Type :=
| obl_live (d : obl_live_data) | obl_done (P : prop_of obl_ps).

(* Logical progress that can obtain a later. *)
Definition obl_state_progress `{Δ : obl_class} : relation obl_state :=
  λ o1 o2,
    match o1, o2 with
    | obl_live d1, obl_live d2 =>
        (obl_transfer d1 = obl_transfer d2 ∧ obl_owner d1 = obl_owner d2 ∧ obl_count_ltR (obl_credit d2) (obl_credit d1))
    | obl_done P1, obl_done P2 => P1 ≡ P2
    | _, _ => False
    end.

(* General transition relation of a liveness obligation. *)
Definition obl_state_step `{Δ : obl_class} (s : obl_ps) : relation obl_state :=
  λ o1 o2,
    (match o1, o2 with
     | obl_live d1, obl_live d2 => obl_count_ltR (obl_transfer d2) (obl_transfer d1)
     | obl_live _, obl_done P => P s
     | _, _ => False
     end) ∨ obl_state_progress o1 o2.

Definition obl_id := positive.

Notation obl_ids := (gset obl_id).
Notation obl_states := (gmap obl_id obl_state).
Notation obl_states' Δ := (gmap obl_id (obl_state (Δ:=Δ))).

Definition obl_states_progress `{Δ : obl_class} : relation obl_states :=
  λ Ω1 Ω2, map_Forall2 (λ _ o1 o2, obl_state_progress o1 o2) Ω1 Ω2.

Infix "↪ₚ" := (obl_states_progress) (at level 20).
(* We use the transitive closure. It's normalization is equivalent to normalization of source_rel. *)
Infix "↪ₚ⁺" := (tc (obl_states_progress)) (at level 20).
Infix "↪ₚ⋆" := (rtc (obl_states_progress)) (at level 20).

Definition obl_states_step_one `{Δ : obl_class} (s : obl_ps) (i : obl_id) : relation obl_states :=
  λ Ω1 Ω2, map_Forall2 (λ k o1 o2, if decide (k = i) then obl_state_step s o1 o2 else o1 = o2) Ω1 Ω2.

Notation "a ↪ₒ b @ s , x" := (obl_states_step_one s x a b) (at level 20, format "a  ↪ₒ  b  @  s ,  x ").
(* We use the transitive closure. It's normalization is equivalent to normalization of source_rel. *)
Notation "a ↪ₒ⁺ b @ s , x" := (tc (obl_states_step_one s x) a b) (at level 20, format "a  ↪ₒ⁺  b  @  s ,  x ").
Notation "a ↪ₒ⋆ b @ s , x" := (rtc (obl_states_step_one s x) a b) (at level 20, format "a  ↪ₒ⋆  b  @  s ,  x ").

Definition obl_states_alloc `{Δ : obl_class} : relation obl_states :=
  λ Ω1 Ω2, ∃ i d, Ω1 !! i = None ∧ Ω2 = <[i:=obl_live d]> Ω1.

Infix "↪ₐ" := (obl_states_alloc) (at level 20).
(* We use the transitive closure. It's normalization is equivalent to normalization of source_rel. *)
Infix "↪ₐ⁺" := (tc obl_states_alloc) (at level 20).
Infix "↪ₐ⋆" := (rtc obl_states_alloc) (at level 20).

Variant obl_states_step `{Δ : obl_class} (s : obl_ps) : relation obl_states :=
  | obl_states_step_alloc Ω1 Ω2 :
    Ω1 ↪ₐ Ω2 → obl_states_step s Ω1 Ω2
  | obl_states_step_step_one i Ω1 Ω2 :
    Ω1 ↪ₒ Ω2 @ s, i → obl_states_step s Ω1 Ω2.

Notation "a ↪ₛ b @ s" := (obl_states_step s a b) (at level 20, format "a  ↪ₛ  b  @  s").
(* We use the transitive closure.
   It's normalization is equivalent to normalization of source_rel. *)
Notation "a ↪ₛ⁺ b @ s" := ((tc (obl_states_step s)) a b) (at level 20, format "a  ↪ₛ⁺  b  @  s").
Notation "a ↪ₛ⋆ b @ s" := ((rtc (obl_states_step s)) a b) (at level 20, format "a  ↪ₛ⋆  b  @  s").

Section obl_states.
  Context `{Δ : obl_class}.

  Lemma obl_states_step_one_dom Ω1 Ω2 s x : Ω1 ↪ₒ Ω2 @ s, x → dom Ω1 = dom Ω2.
  Proof using. intros H. eapply map_Forall2_dom_L; eauto. Qed.
  Lemma obl_states_step_one_tc_dom Ω1 Ω2 s x : Ω1 ↪ₒ⁺ Ω2 @ s, x → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - eapply obl_states_step_one_dom; eauto.
    - rewrite <- IHtc. eapply obl_states_step_one_dom; eauto.
  Qed.
  Lemma obl_states_step_one_rtc_dom Ω1 Ω2 s x : Ω1 ↪ₒ⋆ Ω2 @ s, x → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - auto.
    - rewrite <- IHrtc. eapply obl_states_step_one_dom; eauto.
  Qed.

  Lemma obl_states_progress_dom Ω1 Ω2 : Ω1 ↪ₚ Ω2 → dom Ω1 = dom Ω2.
  Proof using. intros H. eapply map_Forall2_dom_L; eauto. Qed.
  Lemma obl_states_progress_tc_dom Ω1 Ω2 : Ω1 ↪ₚ⁺ Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - eapply obl_states_progress_dom; eauto.
    - rewrite <- IHtc. eapply obl_states_progress_dom; eauto.
  Qed.
  Lemma obl_states_progress_rtc_dom Ω1 Ω2 : Ω1 ↪ₚ⋆ Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - auto.
    - rewrite <- IHrtc. eapply obl_states_progress_dom; eauto.
  Qed.

  Lemma obl_states_progress_lookup Ω1 Ω2 i :
    Ω1 ↪ₚ Ω2 → option_Forall2 obl_state_progress (Ω1 !! i) (Ω2 !! i).
  Proof using. done. Qed.
  Lemma obl_states_progress_tc_lookup Ω1 Ω2 i :
    Ω1 ↪ₚ⁺ Ω2 → option_Forall2 (tc obl_state_progress) (Ω1 !! i) (Ω2 !! i).
  Proof using.
    intros H. induction H.
    - eapply (obl_states_progress_lookup _ _ i) in H. inv H; econstructor. by econstructor 1.
    - apply (obl_states_progress_lookup _ _ i) in H. inv IHtc.
      + rewrite <-H1 in H. inv H. econstructor. econstructor 2; eauto.
      + rewrite <-H2 in H. inv H. econstructor.
  Qed.
  Lemma obl_states_progress_rtc_lookup Ω1 Ω2 i :
    Ω1 ↪ₚ⋆ Ω2 → option_Forall2 (rtc obl_state_progress) (Ω1 !! i) (Ω2 !! i).
  Proof using.
    intros H. induction H.
    - destruct (x !! i); done.
    - apply (obl_states_progress_lookup _ _ i) in H. inv IHrtc.
      + rewrite <-H1 in H. inv H. econstructor. econstructor 2; eauto.
      + rewrite <-H2 in H. inv H. econstructor.
  Qed.

  Lemma obl_states_progress_rtc_live Ω1 Ω2 i :
    Ω1 ↪ₚ⋆ Ω2 → (∃ d, Ω1 !! i = Some (obl_live d)) ↔ (∃ d', Ω2 !! i = Some (obl_live d')).
  Proof using.
    intros H. apply (obl_states_progress_rtc_lookup _ _ i) in H.
    split; intros (d & LU); rewrite LU in H; inv H.
    - clear LU H1 i. remember (obl_live d) as z. revert d Heqz. induction H2; intros; subst; eauto.
      destruct y; simpl in H; try done. destruct H; subst. eapply IHrtc; eauto.
    - clear LU H0 i. remember (obl_live d) as z. revert d Heqz. induction H2; intros; subst; eauto.
      specialize (IHrtc _ eq_refl). destruct IHrtc as (?&H0). inv H0. destruct x; simpl in H; try eauto; done.
  Qed.

  Lemma obl_states_progress_rtc_done_1 Ω1 Ω2 i :
    Ω1 ↪ₚ⋆ Ω2 → ∀ P, Ω1 !! i = Some (obl_done P) → (∃ P', Ω2 !! i = Some (obl_done P') ∧ P ≡ P').
  Proof using.
    intros H. apply (obl_states_progress_rtc_lookup _ _ i) in H.
    intros P LU; rewrite LU in H; inv H.
    clear LU H1. remember (obl_done P) as z. revert P Heqz. induction H2; intros; subst; eauto.
    destruct y; simpl in H; try done.
    specialize (IHrtc P0 eq_refl). destruct IHrtc as (P'&?&?). inv H0. exists P'. split; auto. etransitivity; eauto.
  Qed.

  Lemma obl_states_progress_rtc_done_2 Ω1 Ω2 i :
    Ω1 ↪ₚ⋆ Ω2 → ∀ P, Ω2 !! i = Some (obl_done P) → (∃ P', Ω1 !! i = Some (obl_done P') ∧ P ≡ P').
  Proof using.
    intros H. apply (obl_states_progress_rtc_lookup _ _ i) in H.
    intros P LU; rewrite LU in H; inv H.
    clear LU H0 i. remember (obl_done P) as z. revert P Heqz. induction H2; intros; subst; eauto.
    specialize (IHrtc _ eq_refl). destruct IHrtc as (P'&?&?). inv H0. destruct x; simpl in H; try done.
    exists P0. split; auto. etransitivity; eauto.
  Qed.

End obl_states.
