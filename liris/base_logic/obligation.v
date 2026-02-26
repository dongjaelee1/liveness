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

Class obligation_class := {
    obligation_fuel : Type;
    #[global] obligation_fuel_wfocm :: WFOCM.pack obligation_fuel;
  }.
(** We assume that the thread id is positive *)
Definition obligation_owner := positive.

Variant obligation `{OC : obligation_class} : Type :=
  | obligation_assigned (fuel : obligation_fuel) (owner : obligation_owner)
  | obligation_fulfilled
  | obligation_expired
.

(* Step relations. *)
Variant obligation_progress `{OC : obligation_class} : obligation → obligation → Prop :=
  | obligation_progress_intro f1 f2 o1 o2 (LTf : f2 w< f1) :
    obligation_progress (obligation_assigned f1 o1) (obligation_assigned f2 o2).

Variant obligation_fulfill `{OC : obligation_class} : obligation → obligation → Prop :=
  | obligation_fulfill_intro f o :
    obligation_fulfill (obligation_assigned f o) (obligation_fulfilled).

Variant obligation_expire `{OC : obligation_class} : obligation → obligation → Prop :=
  | obligation_expire_intro :
    obligation_expire (obligation_fulfilled) (obligation_expired).

Variant obligation_step `{OC : obligation_class} : obligation → obligation → Prop :=
  | obligation_step_progress g1 g2 :
    obligation_progress g1 g2 → obligation_step g1 g2
  | obligation_step_fulfill g1 g2 :
    obligation_fulfill g1 g2 → obligation_step g1 g2
  | obligation_step_expire g1 g2 :
    obligation_expire g1 g2 → obligation_step g1 g2.

Definition obligation_keep `{OC : obligation_class} : obligation → obligation → Prop :=
  λ g1 g2,
    match g1, g2 with
    | (obligation_assigned _ _), (obligation_assigned _ _) => True
    | (obligation_fulfilled), (obligation_fulfilled) => True
    | (obligation_expired), (obligation_expired) => True
    | _, _ => False
    end.

(** To a map *)
Definition oid := positive.

Notation oids := (gset oid).
Notation obligations := (gmap oid obligation).

(** For obligations, take one step at a time. *)
Definition obls_one `{OC : obligation_class} : obligations → obligations → Prop :=
  λ Ω1 Ω2, ∃ k g1 g2, (Ω1 !! k = Some g1) ∧ (obligation_step g1 g2) ∧ (Ω2 = <[k:=g2]>Ω1).
Infix "↪₁" := (obls_one) (at level 20).

Definition obls_alloc `{OC : obligation_class} : obligations → obligations → Prop :=
  λ Ω1 Ω2, ∃ k, (Ω1 !! k = None) ∧ (∃ g, Ω2 = <[k:=g]> Ω1).
Infix "↪ₐ" := (obls_alloc) (at level 20).

Variant obls_step `{OC : obligation_class} : obligations → obligations → Prop :=
  | obls_step_one Ω1 Ω2 :
    Ω1 ↪₁ Ω2 → obls_step Ω1 Ω2
  | obls_step_alloc Ω1 Ω2 :
    Ω1 ↪ₐ Ω2 → obls_step Ω1 Ω2.

Notation "A ↪ B" := (obls_step A B) (at level 20, format "A  ↪  B").
Notation "A ↪∘ B" := (rc (obls_step) A B) (at level 20, format "A  ↪∘  B").
Notation "A ↪⁺ B" := (tc (obls_step) A B) (at level 20, format "A  ↪⁺  B").
Notation "A ↪⋆ B" := (rtc (obls_step) A B) (at level 20, format "A  ↪⋆  B").

(** Definitions for strict progress of obligations. *)
(* Only ghost locks that satisfy obl_cond makes R *)
Definition obl_cond `{OC : obligation_class} := (oid → obligation → Prop).
Definition obls_cond_rel `{OC : obligation_class} (C : obl_cond) (R : obligation → obligation → Prop) : obligations → obligations → Prop :=
  λ Ω1 Ω2, map_Forall2 (λ k g1 g2, (C k g1 ∧ R g1 g2) ∨ ((¬ C k g1) ∧ g1 = g2)) Ω1 Ω2.

Definition gl_rel_preserves_cond `{OC : obligation_class} (C : obl_cond) (R : obligation → obligation → Prop) : Prop :=
  ∀ k g1 g2, C k g1 → R g1 g2 → C k g2.

(* Some useful obl_conds *)
Definition obl_cond_owner `{OC : obligation_class} (i : obligation_owner) : obl_cond :=
  λ _ g, match g with | (obligation_assigned _ j) => (j = i) | _ => False end.
Global Instance obl_cond_owner_dec `{OC : obligation_class} : ∀ i k g, Decision (obl_cond_owner i k g).
Proof using. intros. rewrite /obl_cond_owner. destruct g; solve_decision. Qed.

Definition obl_cond_one `{OC : obligation_class} (v : oid) : obl_cond :=
  λ k _, k = v.
Global Instance obl_cond_one_dec `{OC : obligation_class} : ∀ v k g, Decision (obl_cond_one v k g).
Proof using. intros. rewrite /obl_cond_one. solve_decision. Qed.

(* Ghost locks conditional step relation *)
Definition obls_cond_step `{OC : obligation_class} (C : obl_cond) : obligations → obligations → Prop :=
  obls_cond_rel C obligation_step.
Notation "A ↪ₛ B | C" := (obls_cond_step C A B) (at level 20, format "A  ↪ₛ  B  |  C").

(* Ghost locks making strict progresses *)
Definition obls_keep `{OC : obligation_class} : obligations → obligations → Prop :=
  λ Ω1 Ω2, map_Forall2 (λ k g1 g2, obligation_keep g1 g2) Ω1 Ω2.

Definition obls_cond_progress `{OC : obligation_class} (C : obl_cond) : obligations → obligations → Prop :=
  λ Ω1 Ω2, (Ω1 ↪ₛ Ω2 | C) ∧ obls_keep Ω1 Ω2.
Notation "A ↪ₚ B | C" := (obls_cond_progress C A B) (at level 20, format "A  ↪ₚ  B  |  C").

Section proofs.
  Context `{OC : obligation_class}.

  (** Properties *)
  (** For the one step relation. *)
  Lemma obls_one_dom Ω1 Ω2 : Ω1 ↪₁ Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros. destruct H as (?&?&?&?&?&?). subst. rewrite dom_insert_lookup_L; eauto.
  Qed.

  Lemma obls_one_to_obls_cond Ω1 Ω2 : Ω1 ↪₁ Ω2 -> ∃ k, (Ω1 ↪ₛ Ω2 | obl_cond_one k).
  Proof using.
    intros. destruct H as (?&?&?&?&?&?). subst. exists x. intros ?. destruct (decide (i = x)).
    - subst. rewrite H lookup_insert_eq. econstructor. left. done.
    - rewrite lookup_insert_ne; last auto. destruct (Ω1 !! i) eqn:LU; econstructor. right. done.
  Qed.

  Lemma obls_cond_to_obls_one Ω1 Ω2 : (∃ k, is_Some (Ω1 !! k) ∧ (Ω1 ↪ₛ Ω2 | obl_cond_one k)) → Ω1 ↪₁ Ω2.
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
  Lemma obls_cond_rel_dom C R Ω1 Ω2 : obls_cond_rel C R Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using. intros. eapply map_Forall2_dom_L; eauto. Qed.
  Lemma obls_cond_rel_tc_dom C R Ω1 Ω2 : tc (obls_cond_rel C R) Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - eapply obls_cond_rel_dom; eauto.
    - rewrite <- IHtc. eapply obls_cond_rel_dom; eauto.
  Qed.
  Lemma obls_cond_rel_rtc_dom C R Ω1 Ω2 : rtc (obls_cond_rel C R) Ω1 Ω2 → dom Ω1 = dom Ω2.
  Proof using.
    intros H. induction H.
    - auto.
    - rewrite <- IHrtc. eapply obls_cond_rel_dom; eauto.
  Qed.

  (* If C1 and C2 are disjoint, can decompose *)
  Lemma obls_cond_rel_split_cond C C1 C2 R Ω1 Ω2 Ω3 :
    (∀ k g, C k g ↔ (C1 k g ∨ C2 k g)) →
    (∀ k g, (¬ C1 k g) ∨ (¬ C2 k g)) →
    gl_rel_preserves_cond C1 R →
    obls_cond_rel C1 R Ω1 Ω2 →
    obls_cond_rel C2 R Ω2 Ω3 →
    obls_cond_rel C R Ω1 Ω3.
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

  Lemma obls_cond_rel_iff_lookup C1 C2 R Ω1 Ω2 :
    obls_cond_rel C1 R Ω1 Ω2 →
    (∀ k g, Ω1 !! k = Some g → (C1 k g ↔ C2 k g)) →
    obls_cond_rel C2 R Ω1 Ω2.
  Proof using.
    intros. intros ?. specialize (H i). destruct (Ω1 !! i) eqn:Ho1, (Ω2 !! i) eqn:Ho2; inv H; econstructor.
    specialize (H0 _ _ Ho1). destruct H3 as [(HC1& HR) | (NHC1& <-)].
    - left. split; auto. firstorder.
    - right. split; auto. firstorder.
  Qed.
  Lemma obls_cond_rel_iff C1 C2 R Ω1 Ω2 :
    obls_cond_rel C1 R Ω1 Ω2 →
    (∀ k g, C1 k g ↔ C2 k g) →
    obls_cond_rel C2 R Ω1 Ω2.
  Proof using. intros. eapply obls_cond_rel_iff_lookup; eauto. Qed.

  (** For progress *)
  Global Instance obligation_keep_transitive : Transitive obligation_keep.
  Proof using.
    repeat intro. destruct x, y, z; inv H; inv H0. all: econstructor.
  Qed.
  Global Instance obls_keep_transitive : Transitive obls_keep.
  Proof using.
    repeat intro. specialize (H i). specialize (H0 i).
    destruct (x !! i) eqn:Hx, (y !! i) eqn:Hy, (z !! i) eqn:Hz; inv H; inv H0; try done.
    all: econstructor; eauto. etransitivity; eauto.
  Qed.

  Global Instance obligation_keep_reflexive : Reflexive obligation_keep.
  Proof using.
    repeat intro. destruct x; simpl in *; subst; try done.
  Qed.
  Global Instance obls_keep_reflexive : Reflexive obls_keep.
  Proof using.
    repeat intro. destruct (x !! i) eqn:Hx; try done.
  Qed.

End proofs.
