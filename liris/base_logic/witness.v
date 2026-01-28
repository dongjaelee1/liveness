From iris.proofmode Require Import proofmode.
From liris.base_logic Require Import ghost_lock.
(* Only to import rc; TODO refactor *)
From transfinite.stepindex Require Import utils.

Variant witness_state `{GL : ghost_lock_class} : Type :=
  | witness_locked (wit : ghost_lock_fuel)
  | witness_unlocked
.

Definition witness `{GL : ghost_lock_class} : Type := ghost_lock_version * witness_state.

Variant witness_step `{GL : ghost_lock_class} : witness → witness → Prop :=
  | witness_progress
      ver wit1 wit2
      (LTwit : wit2 w< wit1)
    :
    witness_step (ver, witness_locked wit1) (ver, witness_locked wit2)
  | witness_unlock
      ver wit
    :
    witness_step (ver, witness_locked wit) (ver, witness_unlocked)
  | witness_lock
      ver1 ver2 wit
      (GTver : (ver1 < ver2)%nat)
    :
    witness_step (ver1, witness_unlocked) (ver2, witness_locked wit)
.

Definition witness_keep `{GL : ghost_lock_class} : witness → witness → Prop :=
  λ '(v1, w1) '(v2, w2),
    (v1 = v2) ∧
    match w1, w2 with
    | (witness_locked _), (witness_locked _) => True
    | (witness_unlocked), (witness_unlocked) => True
    | _, _ => False
    end.

(** To a map *)
Notation witnesses := (gmap gl_id witness).

(** For witnesses, take one step at a time. *)
Definition wits_one `{GL : ghost_lock_class} : witnesses → witnesses → Prop :=
  λ W1 W2, ∃ k w1 w2, (W1 !! k = Some w1) ∧ (witness_step w1 w2) ∧ (W2 = <[k:=w2]>W1).
Infix "↓₁" := (wits_one) (at level 20).

Definition wits_alloc `{GL : ghost_lock_class} : witnesses → witnesses → Prop :=
  λ W1 W2, ∃ k v, (W1 !! k = None) ∧
                  ((∃ a, W2 = <[k:=(v, witness_locked a)]> W1) ∨
                     (W2 = <[k:=(v, witness_unlocked)]> W1)).
Infix "↓ₐ" := (wits_alloc) (at level 20).

Variant wits_step `{GL : ghost_lock_class} : witnesses → witnesses → Prop :=
  (* | wits_step_cond_step W1 W2 C : *)
  (*   (W1 ↓ₛ W2 | C) → wits_step W1 W2 *)
  | wits_step_one W1 W2 :
    W1 ↓₁ W2 → wits_step W1 W2
  | wits_step_alloc W1 W2 :
    W1 ↓ₐ W2 → wits_step W1 W2.

Notation "A ↓ B" := (wits_step A B) (at level 20, format "A  ↓  B").
Notation "A ↓∘ B" := (rc (wits_step) A B) (at level 20, format "A  ↓∘  B").
Notation "A ↓⁺ B" := (tc (wits_step) A B) (at level 20, format "A  ↓⁺  B").
Notation "A ↓⋆ B" := (rtc (wits_step) A B) (at level 20, format "A  ↓⋆  B").

(** Definitions for strict progress of witnesses. *)
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

Definition wit_cond_locked `{GL : ghost_lock_class} : wit_cond :=
  λ _ w, match w with | (_, witness_locked _) => True | (_, witness_unlocked) => False end.
Global Instance wit_cond_locked_dec `{GL : ghost_lock_class} : ∀ k w, Decision (wit_cond_locked k w).
Proof using. intros. rewrite /wit_cond_locked. destruct w. destruct w; solve_decision. Qed.

(* Witnesses step relation *)
Definition wits_cond_step `{GL : ghost_lock_class} (C : wit_cond) : witnesses → witnesses → Prop :=
  wits_cond_rel C witness_step.
Notation "A ↓ₛ B | C" := (wits_cond_step C A B) (at level 20, format "A  ↓ₛ  B  |  C").

(* Witnesses making strict progresses *)
Definition wits_keep `{GL : ghost_lock_class} : witnesses → witnesses → Prop :=
  λ W1 W2, map_Forall2 (λ k w1 w2, witness_keep w1 w2) W1 W2.

Definition wits_cond_progress `{GL : ghost_lock_class} (C : wit_cond) : witnesses → witnesses → Prop :=
  λ W1 W2, (W1 ↓ₛ W2 | C) ∧ wits_keep W1 W2.
Notation "A ↓ₚ B | C" := (wits_cond_progress C A B) (at level 20, format "A  ↓ₚ  B  |  C").

Definition wits_mon `{GL : ghost_lock_class} : witnesses → witnesses → Prop :=
  λ W1 W2, map_Forall2 (λ _ '(v1, w1) '(v2, w2),
                          (v1 = v2) ∧
                          match w1, w2 with
                          | witness_locked a1, witness_locked a2 => a2 w≤ a1
                          | witness_unlocked, witness_unlocked => True
                          | _, _ => False
                          end) W1 W2.

Section witnesses.
  Context `{GL : ghost_lock_class}.

  (** Properties *)
  (** For the one step relation. *)
  Lemma wits_one_dom W1 W2 : W1 ↪₁ W2 → dom W1 = dom W2.
  Proof using.
    intros. destruct H as (?&?&?&?&?&?). subst. rewrite dom_insert_lookup_L; eauto.
  Qed.

  Lemma wits_one_to_wits_cond W1 W2 : W1 ↓₁ W2 -> ∃ k, (W1 ↓ₛ W2 | wit_cond_one k).
  Proof using.
    intros. destruct H as (?&?&?&?&?&?). subst. exists x. intros ?. destruct (decide (i = x)).
    - subst. rewrite H lookup_insert_eq. econstructor. left. done.
    - rewrite lookup_insert_ne; last auto. destruct (W1 !! i) eqn:LU; econstructor. right. done.
  Qed.

  Lemma wits_cond_to_wits_one W1 W2 : (∃ k, is_Some (W1 !! k) ∧ (W1 ↓ₛ W2 | wit_cond_one k)) → W1 ↓₁ W2.
  Proof using.
    intros (k& (g&?)& ?). pose proof H0 as STEP. specialize (H0 k). rewrite H in H0. inv H0.
    exists k, g, y. destruct H3; cycle 1.
    { destruct H0. done. }
    destruct H0. split_and !; auto.
    apply map_eq_iff. intros. destruct (decide (i = k)).
    - subst. rewrite lookup_insert_eq. auto.
    - rewrite lookup_insert_ne; last auto. specialize (STEP i). inv STEP; auto. destruct H5.
      + destruct H5. done.
      + destruct H5. subst. auto.
  Qed.

  (** For the conditional step relation *)
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

  (** For progress *)
  Global Instance witness_keep_transitive : Transitive witness_keep.
  Proof using.
    repeat intro. destruct x, y, z. inv H. inv H0. destruct w, w0, w1; simpl in *; subst; try done.
  Qed.
  Global Instance wits_keep_transitive : Transitive wits_keep.
  Proof using.
    repeat intro. specialize (H i). specialize (H0 i).
    destruct (x !! i) eqn:Hx, (y !! i) eqn:Hy, (z !! i) eqn:Hz; inv H; inv H0; try done.
    all: econstructor; eauto. etransitivity; eauto.
  Qed.

  Global Instance witness_keep_reflexive : Reflexive witness_keep.
  Proof using.
    repeat intro. destruct x. destruct w; simpl in *; subst; try done.
  Qed.
  Global Instance wits_keep_reflexive : Reflexive wits_keep.
  Proof using.
    repeat intro. destruct (x !! i) eqn:Hx; try done.
  Qed.

  (** For mon *)
  Global Instance wits_mon_transitive : Transitive wits_mon.
  Proof using.
    repeat intro. specialize (H i). specialize (H0 i).
    destruct (x !! i) eqn:Hx.
    { rewrite Hx in H. rewrite Hx. inv H. rewrite -H2 in H0. inv H0.
      destruct w, y0, y1. destruct H3, H4. subst. destruct w, w0, w1; try done.
      - econstructor. split; eauto. etrans; eauto.
      - econstructor. split; eauto. }
    { rewrite Hx in H. rewrite Hx. inv H. rewrite -H1 in H0. inv H0. econstructor. }
  Qed.

  Global Instance wits_mon_reflexive : Reflexive wits_mon.
  Proof using.
    repeat intro. destruct (x !! i) eqn: Eqx.
    - rewrite Eqx. econstructor. destruct w. destruct w; done.
    - rewrite Eqx. econstructor.
  Qed.

  Lemma wits_cond_progress_mon C W1 W2 :
    (W1 ↓ₚ W2 | C) →
    wits_mon W1 W2.
  Proof using.
    intros [Step Keep].
    revert W2 Step Keep. induction W1 using map_ind; intros.
    { apply map_Forall2_empty_inv_l in Step. subst. apply map_Forall2_empty. }
    apply map_Forall2_insert_inv_l in Keep; last auto.
    destruct Keep as (w2& m2& EqW2& LUm2& Keepi& Keep). subst.
    apply map_Forall2_insert in Step; auto.
    destruct x as (v1&w1). destruct w2 as (v2&w2).
    destruct Keepi as [Eqvi Keepi]. subst.
    destruct Step as [HC Step].
    pose proof (IHW1 _ Step Keep) as HM. clear IHW1.
    apply map_Forall2_insert; auto. split_and !; auto.
    destruct HC as [[HC Stepi] | [HC Eqi]].
    - inv Stepi; try done. eapply WFOCM.lt_le; eauto.
    - inv Eqi. destruct w2; try done.
  Qed.

End witnesses.
