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

Class obl_class := {
    obl_fuel : Type;
    #[global] obl_fuel_wfocm :: WFOCM.pack obl_fuel;
  }.
(** We assume that the thread id is positive *)
Definition obl_owner := positive.

Variant obl `{OC : obl_class} : Type :=
  | obl_assigned (fuel : obl_fuel) (owner : obl_owner)
  | obl_fulfilled.

(* Step relations. *)
Variant obl_progress `{OC : obl_class} : obl → obl → Prop :=
  | obl_progress_intro f1 f2 o1 o2 (LTf : f2 w< f1) :
    obl_progress (obl_assigned f1 o1) (obl_assigned f2 o2).

Variant obl_fulfill `{OC : obl_class} : obl → obl → Prop :=
  | obl_fulfill_intro f o :
    obl_fulfill (obl_assigned f o) (obl_fulfilled).

Variant obl_step `{OC : obl_class} : obl → obl → Prop :=
  | obl_step_progress g1 g2 :
    obl_progress g1 g2 → obl_step g1 g2
  | obl_step_fulfill g1 g2 :
    obl_fulfill g1 g2 → obl_step g1 g2.

Definition obl_keep `{OC : obl_class} : obl → obl → Prop :=
  λ g1 g2,
    match g1, g2 with
    | (obl_assigned _ _), (obl_assigned _ _) => True
    | (obl_fulfilled), (obl_fulfilled) => True
    | _, _ => False
    end.

Definition obl_le `{OC : obl_class} : obl → obl → Prop :=
  λ g1 g2,
    match g1, g2 with
    | (obl_assigned f1 o1), (obl_assigned f2 o2) => (f2 w≤ f1 ∧ o1 = o2) ∨ (f2 w< f1)
    | (obl_assigned _ _), obl_fulfilled => True
    | (obl_fulfilled), (obl_fulfilled) => True
    | _, _ => False
    end.

(** To a map *)
Definition oid := positive.

Notation oids := (gset oid).
Notation obls := (gmap oid obl).

(** For obls, take one step at a time. *)
Definition obls_one `{OC : obl_class} : obls → obls → Prop :=
  λ Ω1 Ω2, ∃ k g1 g2, (Ω1 !! k = Some g1) ∧ (obl_step g1 g2) ∧ (Ω2 = <[k:=g2]>Ω1).
Infix "↪₁" := (obls_one) (at level 20).

Definition obls_alloc `{OC : obl_class} : obls → obls → Prop :=
  λ Ω1 Ω2, ∃ k, (Ω1 !! k = None) ∧ (∃ g, Ω2 = <[k:=g]> Ω1).
Infix "↪ₐ" := (obls_alloc) (at level 20).

Variant obls_step `{OC : obl_class} : obls → obls → Prop :=
  | obls_step_one Ω1 Ω2 :
    Ω1 ↪₁ Ω2 → obls_step Ω1 Ω2
  | obls_step_alloc Ω1 Ω2 :
    Ω1 ↪ₐ Ω2 → obls_step Ω1 Ω2.

Notation "A ↪ B" := (obls_step A B) (at level 20, format "A  ↪  B").
Notation "A ↪∘ B" := (rc (obls_step) A B) (at level 20, format "A  ↪∘  B").
Notation "A ↪⁺ B" := (tc (obls_step) A B) (at level 20, format "A  ↪⁺  B").
Notation "A ↪⋆ B" := (rtc (obls_step) A B) (at level 20, format "A  ↪⋆  B").

(** Definitions for strict progress of obls. *)
(* Only ghost locks that satisfy obl_cond makes R *)
Definition obl_cond `{OC : obl_class} := (oid → obl → Prop).
Definition obls_cond_rel `{OC : obl_class} (C : obl_cond) (R : obl → obl → Prop) : obls → obls → Prop :=
  λ Ω1 Ω2, map_Forall2 (λ k g1 g2, (C k g1 ∧ R g1 g2) ∨ ((¬ C k g1) ∧ g1 = g2)) Ω1 Ω2.

Definition gl_rel_preserves_cond `{OC : obl_class} (C : obl_cond) (R : obl → obl → Prop) : Prop :=
  ∀ k g1 g2, C k g1 → R g1 g2 → C k g2.

(* Some useful obl_conds *)
Definition obl_cond_owner `{OC : obl_class} (i : obl_owner) : obl_cond :=
  λ _ g, match g with | (obl_assigned _ j) => (j = i) | _ => False end.
Global Instance obl_cond_owner_dec `{OC : obl_class} : ∀ i k g, Decision (obl_cond_owner i k g).
Proof using. intros. rewrite /obl_cond_owner. destruct g; solve_decision. Qed.

Definition obl_cond_one `{OC : obl_class} (v : oid) : obl_cond :=
  λ k _, k = v.
Global Instance obl_cond_one_dec `{OC : obl_class} : ∀ v k g, Decision (obl_cond_one v k g).
Proof using. intros. rewrite /obl_cond_one. solve_decision. Qed.

(* Ghost locks conditional step relation *)
Definition obls_cond_step `{OC : obl_class} (C : obl_cond) : obls → obls → Prop :=
  obls_cond_rel C obl_step.
Notation "A ↪ₛ B | C" := (obls_cond_step C A B) (at level 20, format "A  ↪ₛ  B  |  C").

(* Ghost locks making strict progresses *)
Definition obls_keep `{OC : obl_class} : obls → obls → Prop :=
  λ Ω1 Ω2, map_Forall2 (λ k g1 g2, obl_keep g1 g2) Ω1 Ω2.

Definition obls_cond_progress `{OC : obl_class} (C : obl_cond) : obls → obls → Prop :=
  λ Ω1 Ω2, (Ω1 ↪ₛ Ω2 | C) ∧ obls_keep Ω1 Ω2.
Notation "A ↪ₚ B | C" := (obls_cond_progress C A B) (at level 20, format "A  ↪ₚ  B  |  C").

Definition obls_le `{OC : obl_class} : obls → obls → Prop :=
  λ Ω1 Ω2, (dom Ω1 ⊆ dom Ω2) ∧ (∀ k o1 o2, Ω1 !! k = Some o1 → Ω2 !! k = Some o2 → obl_le o1 o2).

Section proofs.
  Context `{OC : obl_class}.

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
  Global Instance obl_keep_reflexive : Reflexive obl_keep.
  Proof using.
    repeat intro. destruct x; simpl in *; subst; try done.
  Qed.
  Global Instance obls_keep_reflexive : Reflexive obls_keep.
  Proof using.
    repeat intro. destruct (x !! i) eqn:Hx; try done.
  Qed.

  Global Instance obl_keep_transitive : Transitive obl_keep.
  Proof using.
    repeat intro. destruct x, y, z; inv H; inv H0. all: econstructor.
  Qed.
  Global Instance obls_keep_transitive : Transitive obls_keep.
  Proof using.
    repeat intro. specialize (H i). specialize (H0 i).
    destruct (x !! i) eqn:Hx, (y !! i) eqn:Hy, (z !! i) eqn:Hz; inv H; inv H0; try done.
    all: econstructor; eauto. etransitivity; eauto.
  Qed.

  Global Instance obl_keep_symmetric : Symmetric obl_keep.
  Proof using.
    repeat intro. destruct x, y; inv H. all: econstructor.
  Qed.
  Global Instance obls_keep_symmetric : Symmetric obls_keep.
  Proof using.
    repeat intro. specialize (H i). destruct (x !! i) eqn:Hx, (y !! i) eqn:Hy; inv H; try done.
    econstructor. destruct o, o0; try done.
  Qed.

  Global Instance obl_keep_equivalence : Equivalence obl_keep.
  Proof using. econstructor; apply _. Qed.
  Global Instance obls_keep_equivalence : Equivalence obls_keep.
  Proof using. econstructor; apply _. Qed.

  (** Le. *)
  Global Instance obl_le_reflexive : Reflexive obl_le.
  Proof using.
    repeat intro. destruct x; try done. left. done.
  Qed.
  Global Instance obl_le_transitive : Transitive obl_le.
  Proof using.
    repeat intro. destruct x, y, z; try done. destruct H, H0.
    - destruct H, H0. subst. left. split; auto. etrans; eauto.
    - destruct H. subst. right. eapply WFOCM.lt_le_lt; eauto.
    - destruct H0. subst. right. eapply WFOCM.le_lt_lt; eauto.
    - right. etrans; eauto.
  Qed.
  Global Instance obl_le_antisymmetric : Antisymmetric _ obl_keep obl_le.
  Proof using. repeat intro. destruct x, y, H, H0; auto; econstructor. Qed.

  Global Instance obls_le_reflexive : Reflexive obls_le.
  Proof using. repeat intro. split; first done. intros. rewrite H in H0. inv H0. done. Qed.
  Global Instance obls_le_transitive : Transitive obls_le.
  Proof using.
    repeat intro. destruct H, H0. split.
    - set_solver.
    - intros. destruct (y !! k) eqn:LUy; cycle 1.
      { apply elem_of_dom_2 in H3. apply not_elem_of_dom in LUy. set_solver. }
      specialize (H1 _ _ _ H3 LUy). specialize (H2 _ _ _ LUy H4). etrans; eauto.
  Qed.
  Global Instance obls_le_antisymmetric : Antisymmetric _ obls_keep obls_le.
  Proof using.
    repeat intro. destruct H, H0. assert (dom x = dom y) by set_solver. clear H H0.
    destruct (x !! i) eqn:LUx, (y !! i) eqn:LUy.
    - econstructor. eapply obl_le_antisymmetric; eauto.
    - apply elem_of_dom_2 in LUx. apply not_elem_of_dom in LUy. set_solver.
    - apply elem_of_dom_2 in LUy. apply not_elem_of_dom in LUx. set_solver.
    - econstructor.
  Qed.

  Lemma obl_step_le o1 o2 :
    obl_step o1 o2 → obl_le o1 o2.
  Proof using. intros. inv H; inv H0. 2: econstructor. right. auto. Qed.

  Lemma obls_step_rc_obls_le Ω1 Ω2 : Ω1 ↪∘ Ω2 → obls_le Ω1 Ω2.
  Proof using.
    intros. destruct H.
    { subst. done. }
    inv H.
    - pose proof (obls_one_dom _ _ H0). split; first set_solver.
      intros. destruct H0 as (k0&o3&o4&?&?&?). subst. destruct (decide (k0 = k)).
      + subst. rewrite lookup_insert_eq in H2. inv H2. apply obl_step_le; auto.
      + rewrite lookup_insert_ne in H2; auto. rewrite H1 in H2. inv H2. done.
    - destruct H0 as (?&?&?&?). subst. split.
      + rewrite dom_insert. set_solver.
      + intros. destruct (decide (x = k)).
        * subst. rewrite lookup_insert_eq in H1. inv H1.
        * rewrite lookup_insert_ne in H1; auto. rewrite H0 in H1. inv H1. done.
  Qed.

  Lemma obls_cond_progress_obls_le Ω1 Ω2 C : Ω1 ↪ₚ Ω2 | C → obls_le Ω1 Ω2.
  Proof using.
    intros. destruct H. pose proof (obls_cond_rel_dom _ _ _ _ H). split; first set_solver.
    intros. specialize (H0 k). rewrite H2 H3 in H0. inv H0. destruct o1, o2; try done.
    specialize (H k). rewrite H2 H3 in H. inv H. destruct H5.
    - destruct H. inv H0.
      + inv H4. right. auto.
      + inv H4.
    - destruct H. inv H0. done.
  Qed.

End proofs.
