From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export guarantee_run.
From transfinite.stepindex Require Import ordinals.

(** * Inferring guarantees ([IntoTemporal]); examples *)

(** ** Inferring guarantees

    [tprop_sem P] mentions the ghost-state instances; an adequacy needs a trace property that
    does not. [IntoTemporal P G] computes one from the shape of [P], with fallback [tprop_true].
    Two modes:
    - inference ([G] unknown: [tsem P], [tprop_of P]): an existential is ghost if the guarantee
      of its body does not depend on the witness, else trace-visible (small types) or dropped;
    - checking against a given [G]: an existential is trace-visible exactly when [G] is a
      [tprop_exist] over the same type. *)
Class IntoTemporal `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (P : iProp Σ) (G : tprop Λ Σ) :=
  into_temporal : ⊢ P ⊨ₜ G.
Global Arguments into_temporal {_ _ _ _} _ _ {_}.
Global Hint Mode IntoTemporal - - - - ! - : typeclass_instances.
(* Opaque: unfolding [temporal] when an instance does not match makes the search very slow. *)
Global Typeclasses Opaque temporal.
(* Likewise for the connectives, which are records. *)
Global Typeclasses Opaque tprop_pure tprop_and tprop_or tprop_impl tprop_forall tprop_exist
  tprop_always tprop_until tprop_state.

(** How an existential over a family of guarantees is guaranteed, when inferring. *)
Class SimplExist `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (G : X → tprop Λ Σ) (G' : tprop Λ Σ) :=
  simpl_exist (P : X → iProp Σ) : (∀ x, P x ⊨ₜ G x) ⊢ (∃ x, P x) ⊨ₜ G'.
Global Hint Mode SimplExist - - - - - ! - : typeclass_instances.

(** Existentials, dispatched on whether the target is known (hints after [into_temporal]).
    Records, so that a failing unification does not unfold them. *)
Class IntoTemporalExist `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (P : X → iProp Σ) (G : tprop Λ Σ) :=
  { into_temporal_exist_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoTemporalExist - - - - - ! - : typeclass_instances.
(** Against a known target: trace-visible if the target is a [tprop_exist] (possibly behind
    definitions), ghost otherwise. *)
Class IntoTemporalExistCheck `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (P : X → iProp Σ) (G : tprop Λ Σ) :=
  { into_temporal_exist_check_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoTemporalExistCheck - - - - - ! ! : typeclass_instances.

(** The trace property inferred for [P]. *)
Definition tsem `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (P : iProp Σ) {G : tprop Λ Σ} `{!IntoTemporal P G} : tprop Λ Σ := G.
Global Arguments tsem {_ _ _ _} _ {_ _}.

(** The inferred trace property of [P], computed so that it no longer mentions ghost-state
    instances: [Definition G : tprop Λ Σ := ltac:(tprop_of P).] in a section with the instances
    yields a [G] that can be used in an adequacy statement. *)
Ltac tprop_of P := let G := eval cbv [tsem] in (tsem P%I) in exact G.

(** [t] is an evar, possibly applied: the target is unknown. *)
Ltac evar_headed t := idtac; lazymatch t with ?f _ => evar_headed f | _ => is_evar t end.

Section into_temporal.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : tprop Λ Σ.

  (** The fallback, used through the hint below. *)
  Lemma into_temporal_default P : IntoTemporal P tprop_true.
  Proof. apply temporal_true. Qed.
  Global Instance into_temporal_pure φ : IntoTemporal (⌜φ⌝ : iProp Σ) (tprop_pure φ) | 10.
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
  Global Instance simpl_exist_visible {X} `{!TypeExistentialProperty X ordI} (G : X → tprop Λ Σ) :
    SimplExist G (tprop_exist G) | 10.
  Proof. intros P. iIntros "H". by iApply temporal_exist. Qed.
  (* Total, so that inference never backtracks into the body. *)
  Global Instance simpl_exist_true {X} (G : X → tprop Λ Σ) : SimplExist G tprop_true | 100.
  Proof. intros P. iIntros "_". iApply temporal_true. Qed.

  Global Instance into_temporal_exist {X} (P : X → iProp Σ) G :
    IntoTemporalExist P G → IntoTemporal (∃ x, P x) G | 10.
  Proof. by intros []. Qed.
  Lemma into_temporal_exist_infer {X} (P : X → iProp Σ) (Gx : X → tprop Λ Σ) G :
    (∀ x, IntoTemporal (P x) (Gx x)) → SimplExist Gx G → IntoTemporalExist P G.
  Proof. intros H HS. constructor. unfold IntoTemporal in *. iApply HS. iIntros (x). iApply H. Qed.
  Lemma into_temporal_exist_check {X} (P : X → iProp Σ) G :
    IntoTemporalExistCheck P G → IntoTemporalExist P G.
  Proof. by intros [?]. Qed.
  Global Instance into_temporal_exist_visible_check {X} `{!TypeExistentialProperty X ordI}
    (P : X → iProp Σ) (G : X → tprop Λ Σ) :
    (∀ x, IntoTemporal (P x) (G x)) → IntoTemporalExistCheck P (tprop_exist G) | 0.
  Proof. intros H. constructor. unfold IntoTemporal in *. iApply temporal_exist. iIntros (x). iApply H. Qed.
  Global Instance into_temporal_exist_ghost_check {X} (P : X → iProp Σ) G :
    (∀ x, IntoTemporal (P x) G) → IntoTemporalExistCheck P G | 10.
  Proof. intros H. constructor. unfold IntoTemporal in *. iApply temporal_exist_ghost. iIntros (x). iApply H. Qed.

  Global Instance into_temporal_impl (φ : Prop) P G :
    IntoTemporal P G → IntoTemporal (⌜φ⌝ → P) (⌜φ⌝ → G) | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_impl. iApply H. Qed.
  Global Instance into_temporal_forall {X} (P : X → iProp Σ) (G : X → tprop Λ Σ) :
    (∀ x, IntoTemporal (P x) (G x)) → IntoTemporal (∀ x, P x) (tprop_forall G) | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_forall. iIntros (x). iApply H. Qed.
  Global Instance into_temporal_persistently P G :
    IntoTemporal P G → IntoTemporal (□ P) G | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_persistently. iApply H. Qed.
  Global Instance into_temporal_alwaysI_guar N P G :
    IntoTemporal (alwaysI_guar N P G) (tprop_always G) | 10.
  Proof. apply temporal_always_guar. Qed.
  Global Instance into_temporal_alwaysI_as N P V G :
    IntoTemporal V G → IntoTemporal (alwaysI_as N P V) (tprop_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_always_as_valid. Qed.
  Global Instance into_temporal_alwaysI N P G :
    IntoTemporal P G → IntoTemporal (alwaysI N P) (tprop_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_always_valid. Qed.
  Global Instance into_temporal_untilI_guar N k q P Q G1 G2 :
    IntoTemporal (untilI_guar N k q P Q G1 G2) (tprop_until G1 G2) | 10.
  Proof. apply temporal_until_guar. Qed.
  Global Instance into_temporal_untilI N k q P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (untilI N k q P Q) (tprop_until G1 G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. by apply temporal_until_valid. Qed.
  (** A done until, against a target until with any left formula. *)
  Global Instance into_temporal_untilI_done_guar k Q G1 G2 :
    IntoTemporal (untilI_done_guar k Q G2) (tprop_until G1 G2) | 10.
  Proof. apply temporal_until_done_guar. Qed.
  Global Instance into_temporal_untilI_done k Q G1 G2 :
    IntoTemporal Q G2 → IntoTemporal (untilI_done k Q) (tprop_until G1 G2) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_until_done_valid. Qed.
  (** A state fact guarantees its state atom. *)
  Global Instance into_temporal_state_fact P φ :
    StateFact P φ → IntoTemporal P (tprop_state φ) | 10.
  Proof. intros HP. exact (temporal_state_fact P φ). Qed.

  Global Instance into_temporal_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ)
    (G : K → A → tprop Λ Σ) :
    (∀ k x, IntoTemporal (Φ k x) (G k x)) →
    IntoTemporal ([∗ map] k ↦ x ∈ m, Φ k x)
      (tprop_forall (λ k, tprop_forall (λ x, tprop_impl ⌜m !! k = Some x⌝ (G k x)))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepM. iIntros (k x). iApply HG. Qed.
  Global Instance into_temporal_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → tprop Λ Σ) :
    (∀ k x, IntoTemporal (Φ k x) (G k x)) →
    IntoTemporal ([∗ list] k ↦ x ∈ l, Φ k x)
      (tprop_forall (λ k, tprop_forall (λ x, tprop_impl ⌜l !! k = Some x⌝ (G k x)))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepL. iIntros (k x). iApply HG. Qed.
  Global Instance into_temporal_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → tprop Λ Σ) :
    (∀ x, IntoTemporal (Φ x) (G x)) →
    IntoTemporal ([∗ set] x ∈ X, Φ x) (tprop_forall (λ x, tprop_impl ⌜x ∈ X⌝ (G x))) | 10.
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

(* A done until has no left formula: with an unknown target, it is inferred as a finally. *)
Global Hint Extern 0 (IntoTemporal (untilI_done_guar _ _ _) ?G) =>
  evar_headed G; notypeclasses refine (into_temporal_untilI_done_guar _ _ tprop_true _) : typeclass_instances.
Global Hint Extern 0 (IntoTemporal (untilI_done _ _) ?G) =>
  evar_headed G; notypeclasses refine (into_temporal_untilI_done _ _ tprop_true _ _) : typeclass_instances.

(* The fallback, for an unknown target or [tprop_true], and only once the formula and the
   ghost-state instances contain no evars (resolution is retried once they are solved). *)
Global Hint Extern 100 (@IntoTemporal ?Λ ?Σ ?Ht ?Hs ?P ?G) =>
  assert_fails (has_evar Λ); assert_fails (has_evar Σ); assert_fails (has_evar Ht); assert_fails (has_evar Hs);
  assert_fails (has_evar P);
  first [evar_headed G | unify G (@tprop_true Λ Σ)];
  notypeclasses refine (into_temporal_default P) : typeclass_instances.

(** ** Examples and unit checks *)
Section examples.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  (** Ghost quantification over iProp, scoping over two temporal operators. *)
  Local Lemma ex_iprop N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ) ⊨ₜ
      (tprop_always tprop_true ∧ tprop_finally tprop_true).
  Proof.
    iApply temporal_exist_ghost. iIntros (Ψ).
    iApply temporal_sep; [iApply temporal_always_valid; apply temporal_true|].
    iApply temporal_until_valid; apply temporal_true.
  Qed.

  (** An invariant whose content changes over time, each content carrying its own guarantee. *)
  Local Lemma ex_dynamic_inv N G : ⊢ alwaysI N (∃ P : iProp Σ, P ∗ P ⊨ₜ G) ⊨ₜ tprop_always G.
  Proof. iApply temporal_always_valid. iApply temporal_certified. Qed.

  (** The same guarantee, inferred. *)
  Local Lemma ex_iprop_inferred N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ) ⊨ₜ
      (tprop_always tprop_true ∧ tprop_until (tprop_pure True) tprop_true).
  Proof. apply (into_temporal _ _). Qed.

  (** Trace-visible quantification over a small type is inferred when the guarantee of
      the body depends on the witness. *)
  Local Lemma ex_visible_inferred N (f : nat → Prop) :
    ⊢ (∃ n : nat, alwaysI N ⌜f n⌝) ⊨ₜ tprop_exist (λ n : nat, tprop_always (tprop_pure (f n))).
  Proof. apply (into_temporal _ _). Qed.

  (** The inferred trace property as a closed term. *)
  Local Definition ex_tprop_of N1 N2 k : tprop Λ Σ :=
    ltac:(tprop_of ((∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ)%I)).
  Local Lemma ex_tprop_of_eq N1 N2 k :
    ex_tprop_of N1 N2 k = (tprop_always tprop_true ∧ tprop_until (tprop_pure True) tprop_true)%T.
  Proof. done. Qed.

  (** A done until, allocated with its right formula at hand, exports the until of any left
      formula in the form the adequacy takes: a formula, its guarantee, and the formula
      back. *)
  Local Lemma ex_until_done_export E p K ℓ (μ : measure) (Q : iProp Σ) φ `{!StateFact Q φ}
      (G1 : tprop Λ Σ) :
    parP_le p ℓ -∗ parP_kids p K -∗ Q -∗
    |={E}=>m parP_kids p K ∗
      ∃ P : iProp Σ, (P ⊨ₜ tprop_until G1 (tprop_state φ)) ∗ P ∗ (P -∗ Q).
  Proof.
    iIntros "B Kp Hπ". iMod (obl_new E p K ℓ μ with "B Kp") as (k) "(%Hk& Kp& Kk& Oa& _& _)".
    iMod (untilI_done_init' with "Oa Kp Kk Hπ") as "[U $]"; first done.
    iModIntro. iExists (untilI_done k Q). iFrame "U". iSplit.
    - iApply (into_temporal _ _).
    - iIntros "U". by iDestruct (untilI_done_elim with "U") as "[$ _]".
  Qed.

  (** A strong until, once discharged, is a done until with the same guarantee. *)
  Local Lemma ex_until_discharged E N k p K (Q : iProp Σ) φ `{!StateFact Q φ} (P : iProp Σ) :
    ↑N ⊆ E → k ∈ K →
    £n 1 -∗ untilI N k 1 P Q -∗ parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
    |={E}=>m ∃ U : iProp Σ, (U ⊨ₜ tprop_until (tprop_sem P) (tprop_state φ)) ∗ U ∗ parP_kids p (K ∖ {[k]}).
  Proof.
    iIntros (HN Hk) "LC U Kp Kk Hπ". iMod (untilI_discharge_done with "U") as "U"; first done.
    iApply (lc_sfmupd_add_later with "LC"). iNext. iDestruct "U" as "[_ U]".
    iPoseProof ("U" $! p K Hk with "Kp Kk Hπ") as "U".
    iMod ("U" $! (E ∖ ↑N)) as "U". iMod "U" as "[U $]". iModIntro.
    iExists (untilI_done k Q). iFrame "U". iApply (into_temporal _ _).
  Qed.

  (** Its inferred trace property is the finally of its right formula. *)
  Local Definition ex_tprop_of_done k (Q : iProp Σ) φ `{!StateFact Q φ} : tprop Λ Σ :=
    ltac:(tprop_of (untilI_done k Q)).
  Local Lemma ex_tprop_of_done_eq k (Q : iProp Σ) φ `{!StateFact Q φ} :
    ex_tprop_of_done k Q φ = tprop_finally (tprop_state φ).
  Proof. done. Qed.
  Local Lemma ex_finally_done k (Q : iProp Σ) φ `{!StateFact Q φ} :
    ⊢ untilI_done k Q ⊨ₜ tprop_finally (tprop_state φ).
  Proof. apply (into_temporal _ _). Qed.

  (** A higher-order specification quantifies over the content together with its guarantee
      (the guarantee of the content of an [alwaysI] must be valid, not a hypothesis). *)
  Local Lemma ex_higher_order N G :
    ⊢ (∃ P : iProp Σ, alwaysI N (P ∗ P ⊨ₜ G)) ⊨ₜ tprop_always G.
  Proof.
    iApply temporal_exist_ghost. iIntros (P). iApply temporal_always_valid.
    iApply (temporal_mono (∃ P, P ∗ P ⊨ₜ G)%I with "[]"); first by iIntros "!> H"; iExists P.
    iApply temporal_certified.
  Qed.

  (** A temporal antecedent used in the logic: by completeness, the in-logic reading of
      "eventually [φ]" strengthens a guarantee. *)
  Local Lemma ex_impl_temporal P φ G :
    P ⊨ₜ G ⊢ P ⊨ₜ tprop_impl (tprop_finally (tprop_state φ)) (tprop_and (tprop_finally (tprop_state φ)) G).
  Proof.
    apply (temporal_impl_intro _ _ _ _ (tprop_le_refl _)).
  Qed.

  (** Decided antecedents compose: the decider of a compound antecedent is inferred. *)
  Local Lemma ex_decided (φ : Prop) (ψ : state Λ → thread_pool Λ → Prop) :
    TpropDecided (Σ:=Σ) (tprop_or (tprop_pure φ) (tprop_impl (tprop_state ψ) (tprop_pure False)))
      (λ h, φ ∨ (hist_now ψ h → False)).
  Proof. apply _. Qed.

  (** Unsound: an iProp implication guaranteeing the implication of the guarantees (the
      antecedent's resources are not determined by the trace). *)
  Local Lemma naive_impl_rule_unsound :
    (∀ (P1 P2 : iProp Σ) G1 G2, (⊢ P1 ⊨ₜ G1) → (⊢ P2 ⊨ₜ G2) → ⊢ (P1 → P2) ⊨ₜ tprop_impl G1 G2) →
    ⊢ True ⊨ₜ tprop_impl tprop_true (tprop_pure False).
  Proof.
    intros Hrule.
    assert (HF : ∀ G, ⊢ (False : iProp Σ) ⊨ₜ G).
    { intros G. rewrite /temporal. iIntros "!>" (?????????) "(_& _& [])". }
    iApply (temporal_mono (False → False)%I with "[]"); first by iIntros "!> _ []".
    iApply Hrule; [apply temporal_true|apply HF].
  Qed.

  Local Lemma tprop_impl_true_false_empty τ : ¬ tprop_tr (tprop_impl (Λ:=Λ) (Σ:=Σ) tprop_true (tprop_pure False)) τ.
  Proof. intros H. by apply H. Qed.

End examples.
