From iris.proofmode Require Import proofmode.
(* Only to import rc; FIXME : refactor *)
From transfinite.stepindex Require Import utils.
From liris.algebra Require Export wfocm auth_mra.

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
    gl_fuel : Type;
    gl_owner : Type;
    #[global] gl_fuel_wfocm :: WFOCM.pack gl_fuel;
    #[global] gl_owner_EqDecision :: EqDecision gl_owner;
  }.

Variant ghost_lock_state `{GL : ghost_lock_class} : Type :=
  | gl_locked (fuel : gl_fuel) (owner : gl_owner)
  | gl_unlocked
.

Definition gl_version := nat.
Definition ghost_lock `{GL : ghost_lock_class} : Type := gl_version * ghost_lock_state.

Variant ghost_lock_step `{GL : ghost_lock_class} : ghost_lock → ghost_lock → Prop :=
  | ghost_lock_progress
      ver fuel1 fuel2 owner1 owner2
      (LTfuel : fuel2 w< fuel1)
    :
    ghost_lock_step (ver, gl_locked fuel1 owner1) (ver, gl_locked fuel2 owner2)
  | ghost_lock_unlock
      ver fuel owner
    :
    ghost_lock_step (ver, gl_locked fuel owner) (ver, gl_unlocked)
  | ghost_lock_lock
      ver1 ver2 fuel owner
      (GTver : (ver1 < ver2)%nat)
    :
    ghost_lock_step (ver1, gl_unlocked) (ver2, gl_locked fuel owner)
.

(** To a map *)
Definition gl_id := positive.

Notation gl_ids := (gset gl_id).
Notation ghost_locks := (gmap gl_id ghost_lock).

(* Only ghost locks that satisfy gl_cond makes R *)
Definition gl_cond `{GL : ghost_lock_class} := (gl_id → ghost_lock → Prop).
Definition gls_cond_rel `{GL : ghost_lock_class} (C : gl_cond) (R : ghost_lock → ghost_lock → Prop) : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, map_Forall2 (λ k g1 g2, (C k g1 ∧ R g1 g2) ∨ ((¬ C k g1) ∧ g1 = g2)) Ω1 Ω2.

Definition gl_rel_preserves_cond `{GL : ghost_lock_class} (C : gl_cond) (R : ghost_lock → ghost_lock → Prop) : Prop :=
  ∀ k g1 g2, C k g1 → R g1 g2 → C k g2.

(* Some useful gl_conds *)
Definition gl_cond_owner `{GL : ghost_lock_class} (i : gl_owner) : gl_cond :=
  λ _ g, match g with | (_, gl_locked _ j) => (j = i) | _ => False end.
Global Instance gl_cond_owner_dec `{GL : ghost_lock_class} : ∀ i k g, Decision (gl_cond_owner i k g).
Proof using. intros. rewrite /gl_cond_owner. destruct g. destruct g0; solve_decision. Qed.

Definition gl_cond_one `{GL : ghost_lock_class} (v : gl_id) : gl_cond :=
  λ k _, k = v.
Global Instance gl_cond_one_dec `{GL : ghost_lock_class} : ∀ v k g, Decision (gl_cond_one v k g).
Proof using. intros. rewrite /gl_cond_one. solve_decision. Qed.

(* Ghost locks step relation *)
Definition gls_cond_step `{GL : ghost_lock_class} (C : gl_cond) : ghost_locks → ghost_locks → Prop :=
  gls_cond_rel C ghost_lock_step.
Notation "A ↪ₛ B | C" := (gls_cond_step C A B) (at level 20, format "A  ↪ₛ  B  |  C").

Definition gls_alloc `{GL : ghost_lock_class} : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, ∃ k v f o, Ω1 !! k = None ∧ Ω2 = <[k:=(v, gl_locked f o)]> Ω1.
Infix "↪ₐ" := (gls_alloc) (at level 20).

Variant gls_step `{GL : ghost_lock_class} : ghost_locks → ghost_locks → Prop :=
  | gls_step_cond_step Ω1 Ω2 C :
    (Ω1 ↪ₛ Ω2 | C) → gls_step Ω1 Ω2
  | gls_step_alloc Ω1 Ω2 :
    Ω1 ↪ₐ Ω2 → gls_step Ω1 Ω2.

Notation "A ↪ B" := (gls_step A B) (at level 20, format "A  ↪  B").
Notation "A ↪∘ B" := (rc (gls_step) A B) (at level 20, format "A  ↪∘  B").
Notation "A ↪⁺ B" := (tc (gls_step) A B) (at level 20, format "A  ↪⁺  B").
Notation "A ↪⋆ B" := (rtc (gls_step) A B) (at level 20, format "A  ↪⋆  B").

Section ghost_locks.
  Context `{GL : ghost_lock_class}.

  (** Properties *)
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

  (* Lemma gls_cond_rel_split_cond C C1 C2 R Ω1 Ω2 Ω3 : *)
  (*   Transitive R → *)
  (*   (∀ k o, C k o ↔ (C1 k o ∨ C2 k o)) → *)
  (*   gl_rel_preserves_cond C2 R → *)
  (*   gls_cond_rel C1 R Ω1 Ω2 → *)
  (*   gls_cond_rel C2 R Ω2 Ω3 → *)
  (*   gls_cond_rel C R Ω1 Ω3. *)
  (* Proof using. *)
  (*   intros HTR HS1 HCR2. assert (HS2: ∀ k o, (¬ C k o) ↔ ((¬ C1 k o) ∧ (¬ C2 k o))). *)
  (*   { intros. firstorder. } *)
  (*   intros. intros k. specialize (H k). specialize (H0 k). *)
  (*   inv H. *)
  (*   - rewrite <-H2 in H0. inv H0. destruct H3 as [(HC1& HR1) | (NHC1& <-)]. *)
  (*     + destruct H5 as [(HC2& HR2) | (NHC2& ->)]. *)
  (*       * econstructor. left. split; last by etrans. eapply HS1; eauto. *)
  (*       * econstructor. left. split; eauto. eapply HS1; eauto. *)
  (*     + destruct H5 as [(HC2& HR2) | (NHC2& ->)]. *)
  (*       * econstructor. left. split; eauto. eapply HS1; eauto. *)
  (*       * econstructor. right. split; auto. eapply HS2; eauto. *)
  (*   - rewrite <-H3 in H0. inv H0. econstructor. *)
  (* Qed. *)

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

End ghost_locks.

(** Witness of each version *)
Definition gl_witness `{GL : ghost_lock_class} : Type := gl_version → gl_fuel.

Fixpoint gl_witness_sum `{GL : ghost_lock_class} (w : gl_witness) (v : gl_version) : gl_fuel :=
  match v with
  | O => w v
  | S u => (gl_witness_sum w u) w+ (w v)
  end.
Notation "'gΣ' w v" := (gl_witness_sum w v) (at level 20, format "gΣ  w  v").

Definition gl_witness_constant `{GL : ghost_lock_class} (c : gl_fuel) : gl_witness := λ _, c.
