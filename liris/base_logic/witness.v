From iris.proofmode Require Import proofmode.
From liris.base_logic Require Import obligation.
(* Only to import rc; TODO refactor *)
From transfinite.stepindex Require Import utils.

Variant witness `{OC : obl_class} : Type :=
  | witness_assigned (wit : obl_fuel)
  | witness_discharged
.

(* Step relations. *)
Variant witness_progress `{OC : obl_class} : witness → witness → Prop :=
  | witness_progress_intro f1 f2 (LTf : f2 w< f1) :
    witness_progress (witness_assigned f1) (witness_assigned f2).

Variant witness_discharge `{OC : obl_class} : witness → witness → Prop :=
  | witness_discharge_intro f :
    witness_discharge (witness_assigned f) (witness_discharged).

Variant witness_step `{OC : obl_class} : witness → witness → Prop :=
  | witness_step_progress g1 g2 :
    witness_progress g1 g2 → witness_step g1 g2
  | witness_step_discharge g1 g2 :
    witness_discharge g1 g2 → witness_step g1 g2.

Definition witness_keep `{OC : obl_class} : witness → witness → Prop :=
  λ w1 w2,
    match w1, w2 with
    | (witness_assigned _), (witness_assigned _) => True
    | (witness_discharged), (witness_discharged) => True
    | _, _ => False
    end.

(** To a map *)
Notation witnesses := (gmap oid witness).

(** For witnesses, take one step at a time. *)
Definition wits_one `{OC : obl_class} : witnesses → witnesses → Prop :=
  λ W1 W2, ∃ k w1 w2, (W1 !! k = Some w1) ∧ (witness_step w1 w2) ∧ (W2 = <[k:=w2]>W1).
Infix "↓₁" := (wits_one) (at level 20).

Definition wits_alloc `{OC : obl_class} : witnesses → witnesses → Prop :=
  λ W1 W2, ∃ k, (W1 !! k = None) ∧ (∃ w, W2 = <[k:=w]> W1).
Infix "↓ₐ" := (wits_alloc) (at level 20).

Variant wits_step `{OC : obl_class} : witnesses → witnesses → Prop :=
  | wits_step_one W1 W2 :
    W1 ↓₁ W2 → wits_step W1 W2
  | wits_step_alloc W1 W2 :
    W1 ↓ₐ W2 → wits_step W1 W2.

Notation "A ↓ B" := (wits_step A B) (at level 20, format "A  ↓  B").
Notation "A ↓∘ B" := (rc (wits_step) A B) (at level 20, format "A  ↓∘  B").
Notation "A ↓⁺ B" := (tc (wits_step) A B) (at level 20, format "A  ↓⁺  B").
Notation "A ↓⋆ B" := (rtc (wits_step) A B) (at level 20, format "A  ↓⋆  B").

(** Definitions for non-discharging stpes. *)
Definition wits_one_progress `{OC : obl_class} : witnesses → witnesses → Prop :=
  λ W1 W2, ∃ k w1 w2, (W1 !! k = Some w1) ∧ (witness_progress w1 w2) ∧ (W2 = <[k:=w2]>W1).
Infix "↓₁ₚ" := (wits_one_progress) (at level 20).

Variant wits_nd_step `{OC : obl_class} : witnesses → witnesses → Prop :=
  | wits_nd_step_one_progress W1 W2 :
    W1 ↓₁ₚ W2 → wits_nd_step W1 W2
  | wits_nd_step_alloc W1 W2 :
    W1 ↓ₐ W2 → wits_nd_step W1 W2.

Notation "A ↓ₙ B" := (wits_nd_step A B) (at level 20, format "A  ↓ₙ  B").
Notation "A ↓ₙ∘ B" := (rc (wits_nd_step) A B) (at level 20, format "A  ↓ₙ∘  B").
Notation "A ↓ₙ⁺ B" := (tc (wits_nd_step) A B) (at level 20, format "A  ↓ₙ⁺  B").
Notation "A ↓ₙ⋆ B" := (rtc (wits_nd_step) A B) (at level 20, format "A  ↓ₙ⋆  B").

(** Definitions for strict progress of witnesses. *)
(* Only witnesses that satisfy wit_cond makes R *)
Definition wit_cond `{OC : obl_class} := (oid → witness → Prop).
Definition wits_cond_rel `{OC : obl_class} (C : wit_cond) (R : witness → witness → Prop) : witnesses → witnesses → Prop :=
  λ W1 W2, map_Forall2 (λ k w1 w2, (C k w1 ∧ R w1 w2) ∨ ((¬ C k w1) ∧ w1 = w2)) W1 W2.

Definition wit_rel_preserves_cond `{OC : obl_class} (C : wit_cond) (R : witness → witness → Prop) : Prop :=
  ∀ k w1 w2, C k w1 → R w1 w2 → C k w2.

(* Some useful wit_conds *)
Definition wit_cond_one `{OC : obl_class} (k : oid) : wit_cond :=
  λ x _, x = k.
Global Instance wit_cond_one_dec `{OC : obl_class} : ∀ k x w, Decision (wit_cond_one k x w).
Proof using. intros. rewrite /wit_cond_one. solve_decision. Qed.

Definition wit_cond_assigned `{OC : obl_class} : wit_cond :=
  λ _ w, match w with | witness_assigned _ => True | _ => False end.
Global Instance wit_cond_assigned_dec `{OC : obl_class} : ∀ k w, Decision (wit_cond_assigned k w).
Proof using. intros. rewrite /wit_cond_assigned. destruct w; solve_decision. Qed.

(* Witnesses step relation *)
Definition wits_cond_step `{OC : obl_class} (C : wit_cond) : witnesses → witnesses → Prop :=
  wits_cond_rel C witness_step.
Notation "A ↓ₛ B | C" := (wits_cond_step C A B) (at level 20, format "A  ↓ₛ  B  |  C").

(* Witnesses making strict progresses *)
Definition wits_keep `{OC : obl_class} : witnesses → witnesses → Prop :=
  λ W1 W2, map_Forall2 (λ k w1 w2, witness_keep w1 w2) W1 W2.

Definition wits_cond_progress `{OC : obl_class} (C : wit_cond) : witnesses → witnesses → Prop :=
  λ W1 W2, (W1 ↓ₛ W2 | C) ∧ wits_keep W1 W2.
Notation "A ↓ₚ B | C" := (wits_cond_progress C A B) (at level 20, format "A  ↓ₚ  B  |  C").

Definition wits_mon `{OC : obl_class} : witnesses → witnesses → Prop :=
  λ W1 W2, map_Forall2 (λ _ w1 w2,
                          match w1, w2 with
                          | witness_assigned a1, witness_assigned a2 => a2 w≤ a1
                          | witness_discharged, witness_discharged => True
                          | _, _ => False
                          end) W1 W2.

Section witnesses.
  Context `{OC : obl_class}.

  (** Properties *)
  (** For the one step relation. *)
  Lemma wits_one_dom W1 W2 : W1 ↓₁ W2 → dom W1 = dom W2.
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

  (** For the one progress step relation. *)
  Lemma wits_one_progress_dom W1 W2 : W1 ↓₁ₚ W2 → dom W1 = dom W2.
  Proof using.
    intros. destruct H as (?&?&?&?&?&?). subst. rewrite dom_insert_lookup_L; eauto.
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
    repeat intro. destruct x, y, z; inv H; inv H0. all: econstructor.
  Qed.
  Global Instance wits_keep_transitive : Transitive wits_keep.
  Proof using.
    repeat intro. specialize (H i). specialize (H0 i).
    destruct (x !! i) eqn:Hx, (y !! i) eqn:Hy, (z !! i) eqn:Hz; inv H; inv H0; try done.
    all: econstructor; eauto. etransitivity; eauto.
  Qed.

  Global Instance witness_keep_reflexive : Reflexive witness_keep.
  Proof using.
    repeat intro. destruct x; simpl in *; subst; try done.
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
    { inv H. rewrite -H2 in H0. inv H0. destruct w, y0, y1; try done; try econstructor; auto. etrans; eauto. }
    { inv H. rewrite -H1 in H0. inv H0. econstructor. }
  Qed.

  Global Instance wits_mon_reflexive : Reflexive wits_mon.
  Proof using.
    repeat intro. destruct (x !! i) eqn: Eqx.
    - econstructor. destruct w; done.
    - econstructor.
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
    rename x into w1.
    destruct Step as [HC Step].
    pose proof (IHW1 _ Step Keep) as HM. clear IHW1.
    apply map_Forall2_insert; auto. split_and !; auto.
    destruct HC as [[HC Stepi] | [HC Eqi]].
    - inv Stepi.
      + inv H0. eapply WFOCM.lt_le; eauto.
      + inv H0; done.
    - subst. destruct w2; try done.
  Qed.

  Lemma wits_nd_step_wits_step W1 W2 : W1 ↓ₙ W2 → W1 ↓ W2.
  Proof using.
    intros. inv H; [econstructor 1 | econstructor 2]; eauto. inv H0.
    destruct H as (?&?&?&?&?); subst. do 3 eexists. split_and !; eauto. econstructor 1; eauto.
  Qed.

  Lemma wits_nd_step_wits_step_o W1 W2 : W1 ↓ₙ∘ W2 → W1 ↓∘ W2.
  Proof using.
    intros. inv H. 1: done. econstructor 2. apply wits_nd_step_wits_step; auto.
  Qed.

End witnesses.
