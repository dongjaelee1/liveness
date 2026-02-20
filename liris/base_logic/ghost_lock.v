From iris.proofmode Require Import proofmode.
(* Only to import rc; FIXME : refactor *)
From transfinite.stepindex Require Import utils.
From liris.algebra Require Export wfocm.

(* FIXME : Move to somewhere else *)
Lemma sn_tc {X} (R : X → X → Prop) (x : X): sn R x ↔ sn (tc R) x.
Proof.
  split.
  - induction 1 as [x _ IH]; constructor; simpl; intros y Hy; revert IH; simpl.
    destruct Hy as [x y Honce|x y z Honce Hsteps]; intros IH; eauto.
    destruct (IH _ Honce) as [Hy]; eauto.
  - induction 1 as [z _ IH]; constructor; intros ??; apply IH; simpl in *; eauto using tc_once.
Qed.

Class ghost_lock_class := {
    ghost_lock_fuel : Type;
    #[global] ghost_lock_fuel_wfocm :: WFOCM.pack ghost_lock_fuel;
  }.
(** We assume that the thread id is positive *)
Definition ghost_lock_owner := positive.

Variant ghost_lock `{GL : ghost_lock_class} : Type :=
  | ghost_lock_locked (fuel : ghost_lock_fuel) (owner : ghost_lock_owner)
  | ghost_lock_unlocked
  | ghost_lock_retired
.

(* Step relations. *)
Variant ghost_lock_progress `{GL : ghost_lock_class} : ghost_lock → ghost_lock → Prop :=
  | ghost_lock_progress_intro f1 f2 o1 o2 (LTf : f2 w< f1) :
    ghost_lock_progress (ghost_lock_locked f1 o1) (ghost_lock_locked f2 o2).

Variant ghost_lock_unlock `{GL : ghost_lock_class} : ghost_lock → ghost_lock → Prop :=
  | ghost_lock_unlock_intro f o :
    ghost_lock_unlock (ghost_lock_locked f o) (ghost_lock_unlocked).

Variant ghost_lock_retire `{GL : ghost_lock_class} : ghost_lock → ghost_lock → Prop :=
  | ghost_lock_retire_intro :
    ghost_lock_retire (ghost_lock_unlocked) (ghost_lock_retired).

Variant ghost_lock_step `{GL : ghost_lock_class} : ghost_lock → ghost_lock → Prop :=
  | ghost_lock_step_progress g1 g2 :
    ghost_lock_progress g1 g2 → ghost_lock_step g1 g2
  | ghost_lock_step_unlock g1 g2 :
    ghost_lock_unlock g1 g2 → ghost_lock_step g1 g2
  | ghost_lock_step_retire g1 g2 :
    ghost_lock_retire g1 g2 → ghost_lock_step g1 g2.

Definition ghost_lock_keep `{GL : ghost_lock_class} : ghost_lock → ghost_lock → Prop :=
  λ g1 g2,
    match g1, g2 with
    | (ghost_lock_locked _ _), (ghost_lock_locked _ _) => True
    | (ghost_lock_unlocked), (ghost_lock_unlocked) => True
    | (ghost_lock_retired), (ghost_lock_retired) => True
    | _, _ => False
    end.

(** To a map *)
Definition gl_id := positive.

Notation gl_ids := (gset gl_id).
Notation ghost_locks := (gmap gl_id ghost_lock).

(** For ghost_locks, take one step at a time. *)
Definition gls_one `{GL : ghost_lock_class} : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, ∃ k g1 g2, (Ω1 !! k = Some g1) ∧ (ghost_lock_step g1 g2) ∧ (Ω2 = <[k:=g2]>Ω1).
Infix "↪₁" := (gls_one) (at level 20).

Definition gls_alloc `{GL : ghost_lock_class} : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, ∃ k, (Ω1 !! k = None) ∧ (∃ g, Ω2 = <[k:=g]> Ω1).
Infix "↪ₐ" := (gls_alloc) (at level 20).

Variant gls_step `{GL : ghost_lock_class} : ghost_locks → ghost_locks → Prop :=
  | gls_step_one Ω1 Ω2 :
    Ω1 ↪₁ Ω2 → gls_step Ω1 Ω2
  | gls_step_alloc Ω1 Ω2 :
    Ω1 ↪ₐ Ω2 → gls_step Ω1 Ω2.

Notation "A ↪ B" := (gls_step A B) (at level 20, format "A  ↪  B").
Notation "A ↪∘ B" := (rc (gls_step) A B) (at level 20, format "A  ↪∘  B").
Notation "A ↪⁺ B" := (tc (gls_step) A B) (at level 20, format "A  ↪⁺  B").
Notation "A ↪⋆ B" := (rtc (gls_step) A B) (at level 20, format "A  ↪⋆  B").

(** Definitions for strict progress of ghost_locks. *)
(* Only ghost locks that satisfy gl_cond makes R *)
Definition gl_cond `{GL : ghost_lock_class} := (gl_id → ghost_lock → Prop).
Definition gls_cond_rel `{GL : ghost_lock_class} (C : gl_cond) (R : ghost_lock → ghost_lock → Prop) : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, map_Forall2 (λ k g1 g2, (C k g1 ∧ R g1 g2) ∨ ((¬ C k g1) ∧ g1 = g2)) Ω1 Ω2.

Definition gl_rel_preserves_cond `{GL : ghost_lock_class} (C : gl_cond) (R : ghost_lock → ghost_lock → Prop) : Prop :=
  ∀ k g1 g2, C k g1 → R g1 g2 → C k g2.

(* Some useful gl_conds *)
Definition gl_cond_owner `{GL : ghost_lock_class} (i : ghost_lock_owner) : gl_cond :=
  λ _ g, match g with | (ghost_lock_locked _ j) => (j = i) | _ => False end.
Global Instance gl_cond_owner_dec `{GL : ghost_lock_class} : ∀ i k g, Decision (gl_cond_owner i k g).
Proof using. intros. rewrite /gl_cond_owner. destruct g; solve_decision. Qed.

Definition gl_cond_one `{GL : ghost_lock_class} (v : gl_id) : gl_cond :=
  λ k _, k = v.
Global Instance gl_cond_one_dec `{GL : ghost_lock_class} : ∀ v k g, Decision (gl_cond_one v k g).
Proof using. intros. rewrite /gl_cond_one. solve_decision. Qed.

(* Ghost locks conditional step relation *)
Definition gls_cond_step `{GL : ghost_lock_class} (C : gl_cond) : ghost_locks → ghost_locks → Prop :=
  gls_cond_rel C ghost_lock_step.
Notation "A ↪ₛ B | C" := (gls_cond_step C A B) (at level 20, format "A  ↪ₛ  B  |  C").

(* Ghost locks making strict progresses *)
Definition gls_keep `{GL : ghost_lock_class} : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, map_Forall2 (λ k g1 g2, ghost_lock_keep g1 g2) Ω1 Ω2.

Definition gls_cond_progress `{GL : ghost_lock_class} (C : gl_cond) : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, (Ω1 ↪ₛ Ω2 | C) ∧ gls_keep Ω1 Ω2.
Notation "A ↪ₚ B | C" := (gls_cond_progress C A B) (at level 20, format "A  ↪ₚ  B  |  C").

Section proofs.
  Context `{GL : ghost_lock_class}.

  (** Properties *)
  (** For the one step relation. *)
  Lemma gls_one_dom Ω1 Ω2 : Ω1 ↪₁ Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros. destruct H as (?&?&?&?&?&?). subst. rewrite dom_insert_lookup_L; eauto.
  Qed.

  Lemma gls_one_to_gls_cond Ω1 Ω2 : Ω1 ↪₁ Ω2 -> ∃ k, (Ω1 ↪ₛ Ω2 | gl_cond_one k).
  Proof using.
    intros. destruct H as (?&?&?&?&?&?). subst. exists x. intros ?. destruct (decide (i = x)).
    - subst. rewrite H lookup_insert_eq. econstructor. left. done.
    - rewrite lookup_insert_ne; last auto. destruct (Ω1 !! i) eqn:LU; econstructor. right. done.
  Qed.

  Lemma gls_cond_to_gls_one Ω1 Ω2 : (∃ k, is_Some (Ω1 !! k) ∧ (Ω1 ↪ₛ Ω2 | gl_cond_one k)) → Ω1 ↪₁ Ω2.
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
  Lemma gls_cond_rel_dom C R Ω1 Ω2 : gls_cond_rel C R Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using. intros. eapply map_Forall2_dom_L; eauto. Qed.
  Lemma gls_cond_rel_tc_dom C R Ω1 Ω2 : tc (gls_cond_rel C R) Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - eapply gls_cond_rel_dom; eauto.
    - rewrite <- IHtc. eapply gls_cond_rel_dom; eauto.
  Qed.
  Lemma gls_cond_rel_rtc_dom C R Ω1 Ω2 : rtc (gls_cond_rel C R) Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - auto.
    - rewrite <- IHrtc. eapply gls_cond_rel_dom; eauto.
  Qed.

  (* If C1 and C2 are disjoint, can decompose *)
  Lemma gls_cond_rel_split_cond C C1 C2 R Ω1 Ω2 Ω3 :
    (∀ k g, C k g ↔ (C1 k g ∨ C2 k g)) →
    (∀ k g, (¬ C1 k g) ∨ (¬ C2 k g)) →
    gl_rel_preserves_cond C1 R →
    gls_cond_rel C1 R Ω1 Ω2 →
    gls_cond_rel C2 R Ω2 Ω3 →
    gls_cond_rel C R Ω1 Ω3.
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

  Lemma gls_cond_rel_iff_lookup C1 C2 R Ω1 Ω2 :
    gls_cond_rel C1 R Ω1 Ω2 →
    (∀ k g, Ω1 !! k = Some g → (C1 k g ↔ C2 k g)) →
    gls_cond_rel C2 R Ω1 Ω2.
  Proof using.
    intros. intros ?. specialize (H i). destruct (Ω1 !! i) eqn:Ho1, (Ω2 !! i) eqn:Ho2; inv H; econstructor.
    specialize (H0 _ _ Ho1). destruct H3 as [(HC1& HR) | (NHC1& <-)].
    - left. split; auto. firstorder.
    - right. split; auto. firstorder.
  Qed.
  Lemma gls_cond_rel_iff C1 C2 R Ω1 Ω2 :
    gls_cond_rel C1 R Ω1 Ω2 →
    (∀ k g, C1 k g ↔ C2 k g) →
    gls_cond_rel C2 R Ω1 Ω2.
  Proof using. intros. eapply gls_cond_rel_iff_lookup; eauto. Qed.

  (** For progress *)
  Global Instance ghost_lock_keep_transitive : Transitive ghost_lock_keep.
  Proof using.
    repeat intro. destruct x, y, z; inv H; inv H0. all: econstructor.
  Qed.
  Global Instance gls_keep_transitive : Transitive gls_keep.
  Proof using.
    repeat intro. specialize (H i). specialize (H0 i).
    destruct (x !! i) eqn:Hx, (y !! i) eqn:Hy, (z !! i) eqn:Hz; inv H; inv H0; try done.
    all: econstructor; eauto. etransitivity; eauto.
  Qed.

  Global Instance ghost_lock_keep_reflexive : Reflexive ghost_lock_keep.
  Proof using.
    repeat intro. destruct x; simpl in *; subst; try done.
  Qed.
  Global Instance gls_keep_reflexive : Reflexive gls_keep.
  Proof using.
    repeat intro. destruct (x !! i) eqn:Hx; try done.
  Qed.

End proofs.
