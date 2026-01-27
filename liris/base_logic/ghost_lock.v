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
    ghost_lock_fuel : Type;
    #[global] ghost_lock_fuel_wfocm :: WFOCM.pack ghost_lock_fuel;
  }.
Definition ghost_lock_version := nat.
(* We assume that thread id is positive *)
Definition ghost_lock_owner := positive.

Variant ghost_lock_state `{GL : ghost_lock_class} : Type :=
  | ghost_lock_locked (fuel : ghost_lock_fuel) (owner : ghost_lock_owner)
  | ghost_lock_unlocked
.
Definition ghost_lock `{GL : ghost_lock_class} : Type := ghost_lock_version * ghost_lock_state.

Variant ghost_lock_step `{GL : ghost_lock_class} : ghost_lock → ghost_lock → Prop :=
  | ghost_lock_progress
      ver fuel1 fuel2 owner1 owner2
      (LTfuel : fuel2 w< fuel1)
    :
    ghost_lock_step (ver, ghost_lock_locked fuel1 owner1) (ver, ghost_lock_locked fuel2 owner2)
  | ghost_lock_unlock
      ver fuel owner
    :
    ghost_lock_step (ver, ghost_lock_locked fuel owner) (ver, ghost_lock_unlocked)
  | ghost_lock_lock
      ver1 ver2 fuel owner
      (GTver : (ver1 < ver2)%nat)
    :
    ghost_lock_step (ver1, ghost_lock_unlocked) (ver2, ghost_lock_locked fuel owner)
.

Definition ghost_lock_keep `{GL : ghost_lock_class} : ghost_lock → ghost_lock → Prop :=
  λ '(v1, g1) '(v2, g2),
    (v1 = v2) ∧
    match g1, g2 with
    | (ghost_lock_locked _ _), (ghost_lock_locked _ _) => True
    | (ghost_lock_unlocked), (ghost_lock_unlocked) => True
    | _, _ => False
    end.

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
Definition gl_cond_owner `{GL : ghost_lock_class} (i : ghost_lock_owner) : gl_cond :=
  λ _ g, match g with | (_, ghost_lock_locked _ j) => (j = i) | _ => False end.
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
  λ Ω1 Ω2, ∃ k v, (Ω1 !! k = None) ∧
                  ((∃ a t, Ω2 = <[k:=(v, ghost_lock_locked a t)]> Ω1) ∨
                     (Ω2 = <[k:=(v, ghost_lock_unlocked)]> Ω1)).
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

(* Ghost locks making strict progresses *)
Definition gls_keep `{GL : ghost_lock_class} : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, map_Forall2 (λ k g1 g2, ghost_lock_keep g1 g2) Ω1 Ω2.

Definition gls_cond_progress `{GL : ghost_lock_class} (C : gl_cond) : ghost_locks → ghost_locks → Prop :=
  λ Ω1 Ω2, (Ω1 ↪ₛ Ω2 | C) ∧ gls_keep Ω1 Ω2.
Notation "A ↪ₚ B | C" := (gls_cond_progress C A B) (at level 20, format "A  ↪ₚ  B  |  C").

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

  (* For progress *)
  Global Instance ghost_lock_keep_transitive : Transitive ghost_lock_keep.
  Proof using.
    repeat intro. destruct x, y, z. inv H. inv H0. destruct g0, g2, g4; simpl in *; subst; try done.
  Qed.
  Global Instance gls_keep_transitive : Transitive gls_keep.
  Proof using.
    repeat intro. specialize (H i). specialize (H0 i).
    destruct (x !! i) eqn:Hx, (y !! i) eqn:Hy, (z !! i) eqn:Hz; inv H; inv H0; try done.
    all: econstructor; eauto. etransitivity; eauto.
  Qed.

  Global Instance ghost_lock_keep_reflexive : Reflexive ghost_lock_keep.
  Proof using.
    repeat intro. destruct x. destruct g0; simpl in *; subst; try done.
  Qed.
  Global Instance gls_keep_reflexive : Reflexive gls_keep.
  Proof using.
    repeat intro. destruct (x !! i) eqn:Hx; try done.
  Qed.

End ghost_locks.

(* (** Witness of each version *) *)
(* Definition gl_witness `{GL : ghost_lock_class} : Type := ghost_lock_version → ghost_lock_fuel. *)

(* Fixpoint gl_witness_sum_len `{GL : ghost_lock_class} (ξ : gl_witness) (v : ghost_lock_version) (n : nat) : ghost_lock_fuel := *)
(*   match n with *)
(*   | O => wzero *)
(*   | S m => (ξ v) w+ (gl_witness_sum_len ξ (S v) m) *)
(*   end. *)
(* Notation "'Σ[' ξ ']' [ v , n ]" := (gl_witness_sum_len ξ v n) (at level 20, format "Σ[ ξ ] [ v ,  n ]"). *)

(* Definition gl_witness_sum_gen `{GL : ghost_lock_class} (ξ : gl_witness) (v1 v2 : ghost_lock_version) : ghost_lock_fuel := *)
(*   Σ[ξ][v1, S (v2 - v1)]. *)
(* Notation "'Σ[' ξ ']' { v1 , v2 } " := (gl_witness_sum_gen ξ v1 v2) (at level 20, format "Σ[ ξ ] { v1 ,  v2 }"). *)

(* Fixpoint gl_witness_sum `{GL : ghost_lock_class} (ξ : gl_witness) (v : ghost_lock_version) : ghost_lock_fuel := *)
(*   match v with *)
(*   | O => ξ v *)
(*   | S u => (gl_witness_sum ξ u) w+ (ξ v) *)
(*   end. *)
(* Notation "'Σ[' ξ ']' v" := (gl_witness_sum ξ v) (at level 20, format "Σ[ ξ ]  v"). *)

(* Definition gl_witness_constant `{GL : ghost_lock_class} (c : ghost_lock_fuel) : gl_witness := λ _, c. *)

(* Section witfun. *)
(*   Context `{GL : ghost_lock_class}. *)

(*   Lemma gl_witness_sum_len_S ξ v n : Σ[ξ][v, S n] = ((ξ v) w+ Σ[ξ][S v, n]). *)
(*   Proof using. done. Qed. *)

(*   Lemma gl_witness_sum_len_start_end ξ v n : (Σ[ξ][v, n] w+ ξ (v + n)) w= (ξ v w+ Σ[ξ][S v, n]). *)
(*   Proof using. *)
(*     revert v. induction n; intros. *)
(*     { simpl. replace (v + 0) with v by lia. rewrite comm. done. } *)
(*     rewrite !gl_witness_sum_len_S. replace (v + S n) with ((S v) + n) by lia. *)
(*     rewrite -assoc. rewrite (IHn (S v)). done. *)
(*   Qed. *)

(*   Lemma gl_witness_sum_gen_S ξ v1 v2 : *)
(*     v1 ≤ v2 → *)
(*     Σ[ξ]{v1, S v2} w= ((ξ (S v2)) w+ Σ[ξ]{v1, v2}). *)
(*   Proof using. *)
(*     intros LE. *)
(*     rewrite /gl_witness_sum_gen gl_witness_sum_len_S. *)
(*     replace (S v2 - v1) with (S (v2 - v1)) by lia. *)
(*     rewrite -(gl_witness_sum_len_start_end _ v1 (S (v2 - v1))). *)
(*     replace (v1 + S (v2 - v1)) with (S v2) by lia. *)
(*     rewrite comm. done. *)
(*   Qed. *)

(*   Lemma gl_witness_sum_gen_eq ξ v : *)
(*     Σ[ξ]{v, v} w= ξ v. *)
(*   Proof using. *)
(*     rewrite /gl_witness_sum_gen. replace (S (v - v)) with (S O) by lia. *)
(*     simpl. rewrite right_id. done. *)
(*   Qed. *)

(*   Lemma gl_witness_sum_S ξ v *)
(*     : Σ[ξ] (S v) = ((Σ[ξ] v) w+ (ξ (S v))). *)
(*   Proof using. done. Qed. *)

(*   Lemma gl_witness_sum_gen_sum_equiv ξ v : Σ[ξ] v w= Σ[ξ] {0, v}. *)
(*   Proof using. *)
(*     induction v; unfold gl_witness_sum_gen. *)
(*     { simpl. rewrite right_id. done. } *)
(*     rewrite gl_witness_sum_S IHv. rewrite gl_witness_sum_len_S. *)
(*     unfold gl_witness_sum_gen. *)
(*     replace (S (v - 0)) with (S v) by lia. replace (S v - 0) with (S v) by lia. *)
(*     rewrite gl_witness_sum_len_start_end. done. *)
(*   Qed. *)

(*   Lemma gl_witness_sum_gen_sum_equiv_add ξ v1 v2 : *)
(*     (v1 < v2) → *)
(*     Σ[ξ] v2 w= (Σ[ξ] v1 w+ Σ[ξ] {S v1, v2}). *)
(*   Proof using. *)
(*     revert v1. induction v2; intros. *)
(*     { lia. } *)
(*     destruct (decide (v1 < v2)). *)
(*     { clear H. specialize (IHv2 _ l). rewrite gl_witness_sum_S IHv2. *)
(*       rewrite (gl_witness_sum_gen_S _ (S v1) v2); last lia. *)
(*       rewrite (comm _ (ξ (S v2)) (Σ[ξ]{S v1, v2})) assoc. done. *)
(*     } *)
(*     assert (v1 = v2) by lia. subst. clear n H. rewrite gl_witness_sum_gen_eq. *)
(*     rewrite gl_witness_sum_S. done. *)
(*   Qed. *)

(* End witfun. *)
