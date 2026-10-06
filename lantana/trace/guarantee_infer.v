From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export guarantee_run.
From transfinite.stepindex Require Import ordinals.

(** * Inferring guarantees ([IntoTemporal]); examples *)

(** ** Inferring guarantees

    [tps_sem P] mentions the ghost-state instances; an adequacy needs a trace property that
    does not. [IntoTemporal P G] computes one from the shape of [P], with fallback [tps_true].
    Two modes:
    - inference ([G] unknown: [tsem P], [tps_of P]): an existential is ghost if the guarantee
      of its body does not depend on the witness, else trace-visible (small types) or dropped;
    - checking against a given [G]: an existential is trace-visible exactly when [G] is a
      [tps_exist] over the same type. *)
Class IntoTemporal `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (P : iProp Σ) (G : tps Λ Σ) :=
  into_temporal : ⊢ P ⊨ₜ G.
Global Arguments into_temporal {_ _ _ _} _ _ {_}.
Global Hint Mode IntoTemporal - - - - ! - : typeclass_instances.
(* Opaque: unfolding [temporal] when an instance does not match makes the search very slow. *)
Global Typeclasses Opaque temporal.
(* Likewise for the connectives, which are records. *)
Global Typeclasses Opaque tps_pure tps_atomic tps_and tps_or tps_impl tps_forall tps_exist
  tps_always tps_until tps_state.

(** How an existential over a family of guarantees is guaranteed, when inferring. *)
Class SimplExist `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (G : X → tps Λ Σ) (G' : tps Λ Σ) :=
  simpl_exist (P : X → iProp Σ) : (∀ x, P x ⊨ₜ G x) ⊢ (∃ x, P x) ⊨ₜ G'.
Global Hint Mode SimplExist - - - - - ! - : typeclass_instances.

(** Existentials, dispatched on whether the target is known (hints after [into_temporal]).
    Records, so that a failing unification does not unfold them. *)
Class IntoTemporalExist `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (P : X → iProp Σ) (G : tps Λ Σ) :=
  { into_temporal_exist_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoTemporalExist - - - - - ! - : typeclass_instances.
(** Against a known target: trace-visible if the target is a [tps_exist] (possibly behind
    definitions), ghost otherwise. *)
Class IntoTemporalExistCheck `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (P : X → iProp Σ) (G : tps Λ Σ) :=
  { into_temporal_exist_check_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoTemporalExistCheck - - - - - ! ! : typeclass_instances.

(** The trace property inferred for [P]. *)
Definition tsem `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (P : iProp Σ) {G : tps Λ Σ} `{!IntoTemporal P G} : tps Λ Σ := G.
Global Arguments tsem {_ _ _ _} _ {_ _}.

(** The inferred trace property of [P], computed so that it no longer mentions ghost-state
    instances: [Definition G : tps Λ Σ := ltac:(tps_of P).] in a section with the instances
    yields a [G] that can be used in an adequacy statement. *)
Ltac tps_of P := let G := eval cbv [tsem] in (tsem P%I) in exact G.

(** [t] is an evar, possibly applied: the target is unknown. *)
Ltac evar_headed t := idtac; lazymatch t with ?f _ => evar_headed f | _ => is_evar t end.

Section into_temporal.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : tps Λ Σ.

  (** The fallback, used through the hint below. *)
  Lemma into_temporal_default P : IntoTemporal P tps_true.
  Proof. apply temporal_true. Qed.
  Global Instance into_temporal_pure φ : IntoTemporal (⌜φ⌝ : iProp Σ) (tps_pure φ) | 10.
  Proof. apply temporal_pure. Qed.
  Global Instance into_temporal_sep P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∗ Q) (G1 ∧ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_sep; [iApply H1|iApply H2]. Qed.
  Global Instance into_temporal_and P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∧ Q) (G1 ∧ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_and; [iApply H1|iApply H2]. Qed.
  Global Instance into_temporal_or P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∨ Q) (G1 ∨ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_or; [iApply H1|iApply H2]. Qed.

  Global Instance simpl_exist_ghost {X} G : SimplExist (λ _ : X, G) G | 0.
  Proof. intros P. iIntros "H". by iApply temporal_exist_ghost. Qed.
  Global Instance simpl_exist_visible {X} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) :
    SimplExist G (tps_exist G) | 10.
  Proof. intros P. iIntros "H". by iApply temporal_exist. Qed.
  (* Total, so that inference never backtracks into the body. *)
  Global Instance simpl_exist_true {X} (G : X → tps Λ Σ) : SimplExist G tps_true | 100.
  Proof. intros P. iIntros "_". iApply temporal_true. Qed.

  Global Instance into_temporal_exist {X} (P : X → iProp Σ) G :
    IntoTemporalExist P G → IntoTemporal (∃ x, P x) G | 10.
  Proof. by intros []. Qed.
  Lemma into_temporal_exist_infer {X} (P : X → iProp Σ) (Gx : X → tps Λ Σ) G :
    (∀ x, IntoTemporal (P x) (Gx x)) → SimplExist Gx G → IntoTemporalExist P G.
  Proof. intros H HS. constructor. unfold IntoTemporal in *. iApply HS. iIntros (x). iApply H. Qed.
  Lemma into_temporal_exist_check {X} (P : X → iProp Σ) G :
    IntoTemporalExistCheck P G → IntoTemporalExist P G.
  Proof. by intros [?]. Qed.
  Global Instance into_temporal_exist_visible_check {X} `{!TypeExistentialProperty X ordI}
    (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, IntoTemporal (P x) (G x)) → IntoTemporalExistCheck P (tps_exist G) | 0.
  Proof. intros H. constructor. unfold IntoTemporal in *. iApply temporal_exist. iIntros (x). iApply H. Qed.
  Global Instance into_temporal_exist_ghost_check {X} (P : X → iProp Σ) G :
    (∀ x, IntoTemporal (P x) G) → IntoTemporalExistCheck P G | 10.
  Proof. intros H. constructor. unfold IntoTemporal in *. iApply temporal_exist_ghost. iIntros (x). iApply H. Qed.

  Global Instance into_temporal_impl (φ : Prop) P G :
    IntoTemporal P G → IntoTemporal (⌜φ⌝ → P) (⌜φ⌝ → G) | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_impl. iApply H. Qed.
  Global Instance into_temporal_forall {X} (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, IntoTemporal (P x) (G x)) → IntoTemporal (∀ x, P x) (tps_forall G) | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_forall. iIntros (x). iApply H. Qed.
  Global Instance into_temporal_persistently P G :
    IntoTemporal P G → IntoTemporal (□ P) G | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_persistently. iApply H. Qed.
  Global Instance into_temporal_alwaysI_guar N P G :
    IntoTemporal (alwaysI_guar N P G) (tps_always G) | 10.
  Proof. apply temporal_always_guar. Qed.
  Global Instance into_temporal_alwaysI_as N P V G :
    IntoTemporal V G → IntoTemporal (alwaysI_as N P V) (tps_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_always_as_valid. Qed.
  Global Instance into_temporal_alwaysI N P G :
    IntoTemporal P G → IntoTemporal (alwaysI N P) (tps_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_always_valid. Qed.
  Global Instance into_temporal_untilI_guar N k q P Q G1 G2 :
    IntoTemporal (untilI_guar N k q P Q G1 G2) (tps_until G1 G2) | 10.
  Proof. apply temporal_until_guar. Qed.
  Global Instance into_temporal_untilI N k q P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (untilI N k q P Q) (tps_until G1 G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. by apply temporal_until_valid. Qed.
  (** A discharged until, against a target until with any left formula. *)
  Global Instance into_temporal_untilI_done_guar N k Q G1 G2 :
    IntoTemporal (untilI_done_guar N k Q G2) (tps_until G1 G2) | 10.
  Proof. apply temporal_until_done_guar. Qed.
  Global Instance into_temporal_untilI_done N k Q G1 G2 :
    IntoTemporal Q G2 → IntoTemporal (untilI_done N k Q) (tps_until G1 G2) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_until_done_valid. Qed.
  Global Instance into_temporal_state_pred π : IntoTemporal (state_pred_interp π) (tps_atomic π) | 10.
  Proof. apply temporal_atomic. Qed.

  Global Instance into_temporal_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ)
    (G : K → A → tps Λ Σ) :
    (∀ k x, IntoTemporal (Φ k x) (G k x)) →
    IntoTemporal ([∗ map] k ↦ x ∈ m, Φ k x)
      (tps_forall (λ k, tps_forall (λ x, tps_impl ⌜m !! k = Some x⌝ (G k x)))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepM. iIntros (k x). iApply HG. Qed.
  Global Instance into_temporal_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → tps Λ Σ) :
    (∀ k x, IntoTemporal (Φ k x) (G k x)) →
    IntoTemporal ([∗ list] k ↦ x ∈ l, Φ k x)
      (tps_forall (λ k, tps_forall (λ x, tps_impl ⌜l !! k = Some x⌝ (G k x)))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepL. iIntros (k x). iApply HG. Qed.
  Global Instance into_temporal_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → tps Λ Σ) :
    (∀ x, IntoTemporal (Φ x) (G x)) →
    IntoTemporal ([∗ set] x ∈ X, Φ x) (tps_forall (λ x, tps_impl ⌜x ∈ X⌝ (G x))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepS. iIntros (x). iApply HG. Qed.

  Lemma tsem_temporal (Q : iProp Σ) G `{!IntoTemporal Q G} : ⊢ Q ⊨ₜ tsem Q.
  Proof. done. Qed.

End into_temporal.

(* Existentials. With an unknown target, the strongest guarantee of the body is inferred and
   then collapsed ([SimplExist]). With a known target, the body is checked against it
   ([IntoTemporalExistCheck]). *)
Global Hint Extern 0 (IntoTemporalExist _ ?G) =>
  evar_headed G; notypeclasses refine (into_temporal_exist_infer _ _ _ _ _) : typeclass_instances.
Global Hint Extern 0 (IntoTemporalExist _ ?G) =>
  assert_fails (evar_headed G);
  notypeclasses refine (into_temporal_exist_check _ _ _) : typeclass_instances.

(* A discharged until has no left formula: with an unknown target, it is inferred as a
   finally. *)
Global Hint Extern 0 (IntoTemporal (untilI_done_guar _ _ _ _) ?G) =>
  evar_headed G; notypeclasses refine (into_temporal_untilI_done_guar _ _ _ tps_true _) : typeclass_instances.
Global Hint Extern 0 (IntoTemporal (untilI_done _ _ _) ?G) =>
  evar_headed G; notypeclasses refine (into_temporal_untilI_done _ _ _ tps_true _ _) : typeclass_instances.

(* The fallback, for an unknown target or [tps_true], and only once the formula and the
   ghost-state instances contain no evars (resolution is retried once they are solved). *)
Global Hint Extern 100 (@IntoTemporal ?Λ ?Σ ?Ht ?Hs ?P ?G) =>
  assert_fails (has_evar Λ); assert_fails (has_evar Σ); assert_fails (has_evar Ht); assert_fails (has_evar Hs);
  assert_fails (has_evar P);
  first [evar_headed G | unify G (@tps_true Λ Σ)];
  notypeclasses refine (into_temporal_default P) : typeclass_instances.

(** ** Examples and unit checks *)
Section examples.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  (** Ghost quantification over iProp, scoping over two temporal operators. *)
  Local Lemma ex_iprop N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ) ⊨ₜ
      (tps_always tps_true ∧ tps_finally tps_true).
  Proof.
    iApply temporal_exist_ghost. iIntros (Ψ).
    iApply temporal_sep; [iApply temporal_always_valid; apply temporal_true|].
    iApply temporal_until_valid; apply temporal_true.
  Qed.

  (** An invariant whose content changes over time, each content carrying its own guarantee. *)
  Local Lemma ex_dynamic_inv N G : ⊢ alwaysI N (∃ P : iProp Σ, P ∗ P ⊨ₜ G) ⊨ₜ tps_always G.
  Proof. iApply temporal_always_valid. iApply temporal_certified. Qed.

  (** The same guarantee, inferred. *)
  Local Lemma ex_iprop_inferred N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ) ⊨ₜ
      (tps_always tps_true ∧ tps_until (tps_pure True) tps_true).
  Proof. apply (into_temporal _ _). Qed.

  (** Trace-visible quantification over a small type is inferred when the guarantee of
      the body depends on the witness. *)
  Local Lemma ex_visible_inferred N (f : nat → Prop) :
    ⊢ (∃ n : nat, alwaysI N ⌜f n⌝) ⊨ₜ tps_exist (λ n : nat, tps_always (tps_pure (f n))).
  Proof. apply (into_temporal _ _). Qed.

  (** The inferred trace property as a closed term. *)
  Local Definition ex_tps_of N1 N2 k : tps Λ Σ :=
    ltac:(tps_of ((∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ)%I)).
  Local Lemma ex_tps_of_eq N1 N2 k :
    ex_tps_of N1 N2 k = (tps_always tps_true ∧ tps_until (tps_pure True) tps_true)%S.
  Proof. done. Qed.

  (** A discharged until, allocated with its right formula at hand, exports the until of any
      left formula in the form the adequacy takes: a formula, its guarantee, and the
      formula back. *)
  Local Lemma ex_until_done_export E (N : namespace) π (G1 : tps Λ Σ) :
    state_pred_interp π -∗
    |={E}=>m ∃ P : iProp Σ, (P ⊨ₜ tps_until G1 (tps_atomic π)) ∗ P ∗ (P -∗ state_pred_interp π).
  Proof.
    iIntros "Hπ". iMod (untilI_discharged_alloc E N 0 with "Hπ") as (k) "[U _]".
    iModIntro. iExists (untilI_done N k (state_pred_interp π)). iFrame "U". iSplit.
    - iApply (into_temporal _ _).
    - iIntros "U". by iDestruct (untilI_done_elim with "U") as "[$ _]".
  Qed.

  (** Its inferred trace property is the finally of its right formula. *)
  Local Definition ex_tps_of_done N k π : tps Λ Σ :=
    ltac:(tps_of (untilI_done N k (state_pred_interp π))).
  Local Lemma ex_tps_of_done_eq N k π : ex_tps_of_done N k π = tps_finally (tps_atomic π).
  Proof. done. Qed.
  Local Lemma ex_finally_done N k π : ⊢ untilI_done N k (state_pred_interp π) ⊨ₜ tps_finally (tps_atomic π).
  Proof. apply (into_temporal _ _). Qed.

  (** A higher-order specification quantifies over the content together with its guarantee
      (the guarantee of the content of an [alwaysI] must be valid, not a hypothesis). *)
  Local Lemma ex_higher_order N G :
    ⊢ (∃ P : iProp Σ, alwaysI N (P ∗ P ⊨ₜ G)) ⊨ₜ tps_always G.
  Proof.
    iApply temporal_exist_ghost. iIntros (P). iApply temporal_always_valid.
    iApply (temporal_mono (∃ P, P ∗ P ⊨ₜ G)%I with "[]"); first by iIntros "!> H"; iExists P.
    iApply temporal_certified.
  Qed.

  (** A temporal antecedent used in the logic: by completeness, the in-logic reading of
      "eventually [π]" strengthens a guarantee. *)
  Local Lemma ex_impl_temporal P π G :
    P ⊨ₜ G ⊢ P ⊨ₜ tps_impl (tps_finally (tps_atomic π)) (tps_and (tps_finally (tps_atomic π)) G).
  Proof.
    apply (temporal_impl_intro _ _ _ _ (tps_le_refl _)).
  Qed.

  (** Unsound: an iProp implication guaranteeing the implication of the guarantees (the
      antecedent's resources are not determined by the trace). *)
  Local Lemma naive_impl_rule_unsound :
    (∀ (P1 P2 : iProp Σ) G1 G2, (⊢ P1 ⊨ₜ G1) → (⊢ P2 ⊨ₜ G2) → ⊢ (P1 → P2) ⊨ₜ tps_impl G1 G2) →
    ⊢ True ⊨ₜ tps_impl tps_true (tps_pure False).
  Proof.
    intros Hrule.
    assert (HF : ∀ G, ⊢ (False : iProp Σ) ⊨ₜ G).
    { intros G. rewrite /temporal. iIntros "!>" (?????????) "(_& _& [])". }
    iApply (temporal_mono (False → False)%I with "[]"); first by iIntros "!> _ []".
    iApply Hrule; [apply temporal_true|apply HF].
  Qed.

  Local Lemma tps_impl_true_false_empty τ : ¬ tps_tr (tps_impl (Λ:=Λ) (Σ:=Σ) tps_true (tps_pure False)) τ.
  Proof. intros H. by apply H. Qed.

End examples.
