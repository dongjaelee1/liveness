From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export temporal_formula_rules.
From transfinite.stepindex Require Import ordinals.

(** * Inferring guarantees ([IntoGuar]); examples *)

(** ** Inferring guarantees

    [itrProp_canon P] mentions the ghost-state instances; an adequacy needs a trace property that
    does not. [IntoGuar P G] computes one from the shape of [P], with fallback [itrProp_true].
    Two modes:
    - inference ([G] unknown: [itrProp_inferred P], [itrProp_of P]): an existential is ghost if the guarantee
      of its body does not depend on the witness, else trace-visible (small types) or dropped;
    - checking against a given [G]: an existential is trace-visible exactly when [G] is a
      [itrProp_exist] over the same type. *)
Class IntoGuar `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (P : iProp Σ) (G : itrProp Λ Σ) :=
  into_guar : ⊢ P ⊨ₜ G.
Global Arguments into_guar {_ _ _ _} _ _ {_}.
Global Hint Mode IntoGuar - - - - ! - : typeclass_instances.
(* Opaque: unfolding [guar] when an instance does not match makes the search very slow. *)
Global Typeclasses Opaque guar.
(* Likewise for the connectives, which are records. *)
Global Typeclasses Opaque itrProp_pure itrProp_and itrProp_or itrProp_impl itrProp_forall itrProp_exist
  itrProp_always itrProp_until itrProp_state.

(** How an existential over a family of guarantees is guaranteed, when inferring. *)
Class SimplExist `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (G : X → itrProp Λ Σ) (G' : itrProp Λ Σ) :=
  simpl_exist (P : X → iProp Σ) : (∀ x, P x ⊨ₜ G x) ⊢ (∃ x, P x) ⊨ₜ G'.
Global Hint Mode SimplExist - - - - - ! - : typeclass_instances.

(** Existentials, dispatched on whether the target is known (hints after [into_guar]).
    Records, so that a failing unification does not unfold them. *)
Class IntoGuarExist `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (P : X → iProp Σ) (G : itrProp Λ Σ) :=
  { into_guar_exist_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoGuarExist - - - - - ! - : typeclass_instances.
(** Against a known target: trace-visible if the target is a [itrProp_exist] (possibly behind
    definitions), ghost otherwise. *)
Class IntoGuarExistCheck `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (P : X → iProp Σ) (G : itrProp Λ Σ) :=
  { into_guar_exist_check_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoGuarExistCheck - - - - - ! ! : typeclass_instances.

(** The trace property inferred for [P]. *)
Definition itrProp_inferred `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (P : iProp Σ) {G : itrProp Λ Σ} `{!IntoGuar P G} : itrProp Λ Σ := G.
Global Arguments itrProp_inferred {_ _ _ _} _ {_ _}.

(** The inferred trace property of [P], computed so that it no longer mentions ghost-state
    instances: [Definition G : itrProp Λ Σ := ltac:(itrProp_of P).] in a section with the instances
    yields a [G] that can be used in an adequacy statement. *)
Ltac itrProp_of P := let G := eval cbv [itrProp_inferred] in (itrProp_inferred P%I) in exact G.

(** [t] is an evar, possibly applied: the target is unknown. *)
Ltac evar_headed t := idtac; lazymatch t with ?f _ => evar_headed f | _ => is_evar t end.

Section into_guar.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : itrProp Λ Σ.

  (** The fallback, used through the hint below. *)
  Lemma into_guar_default P : IntoGuar P itrProp_true.
  Proof. apply guar_true. Qed.
  Global Instance into_guar_pure φ : IntoGuar (⌜φ⌝ : iProp Σ) (itrProp_pure φ) | 10.
  Proof. apply guar_pure. Qed.
  Global Instance into_guar_sep P Q G1 G2 :
    IntoGuar P G1 → IntoGuar Q G2 → IntoGuar (P ∗ Q) (G1 ∧ G2) | 10.
  Proof. intros H1 H2. unfold IntoGuar in *. iApply guar_sep; [iApply H1|iApply H2]. Qed.
  Global Instance into_guar_and P Q G1 G2 :
    IntoGuar P G1 → IntoGuar Q G2 → IntoGuar (P ∧ Q) (G1 ∧ G2) | 10.
  Proof. intros H1 H2. unfold IntoGuar in *. iApply guar_and; [iApply H1|iApply H2]. Qed.
  Global Instance into_guar_or P Q G1 G2 :
    IntoGuar P G1 → IntoGuar Q G2 → IntoGuar (P ∨ Q) (G1 ∨ G2) | 10.
  Proof. intros H1 H2. unfold IntoGuar in *. iApply guar_or; [iApply H1|iApply H2]. Qed.

  Global Instance simpl_exist_ghost {X} G : SimplExist (λ _ : X, G) G | 0.
  Proof. intros P. iIntros "H". by iApply guar_exist_ghost. Qed.
  Global Instance simpl_exist_visible {X} `{!TypeExistentialProperty X ordI} (G : X → itrProp Λ Σ) :
    SimplExist G (itrProp_exist G) | 10.
  Proof. intros P. iIntros "H". by iApply guar_exist. Qed.
  (* Total, so that inference never backtracks into the body. *)
  Global Instance simpl_exist_true {X} (G : X → itrProp Λ Σ) : SimplExist G itrProp_true | 100.
  Proof. intros P. iIntros "_". iApply guar_true. Qed.

  Global Instance into_guar_exist {X} (P : X → iProp Σ) G :
    IntoGuarExist P G → IntoGuar (∃ x, P x) G | 10.
  Proof. by intros []. Qed.
  Lemma into_guar_exist_infer {X} (P : X → iProp Σ) (Gx : X → itrProp Λ Σ) G :
    (∀ x, IntoGuar (P x) (Gx x)) → SimplExist Gx G → IntoGuarExist P G.
  Proof. intros H HS. constructor. unfold IntoGuar in *. iApply HS. iIntros (x). iApply H. Qed.
  Lemma into_guar_exist_check {X} (P : X → iProp Σ) G :
    IntoGuarExistCheck P G → IntoGuarExist P G.
  Proof. by intros [?]. Qed.
  Global Instance into_guar_exist_visible_check {X} `{!TypeExistentialProperty X ordI}
    (P : X → iProp Σ) (G : X → itrProp Λ Σ) :
    (∀ x, IntoGuar (P x) (G x)) → IntoGuarExistCheck P (itrProp_exist G) | 0.
  Proof. intros H. constructor. unfold IntoGuar in *. iApply guar_exist. iIntros (x). iApply H. Qed.
  Global Instance into_guar_exist_ghost_check {X} (P : X → iProp Σ) G :
    (∀ x, IntoGuar (P x) G) → IntoGuarExistCheck P G | 10.
  Proof. intros H. constructor. unfold IntoGuar in *. iApply guar_exist_ghost. iIntros (x). iApply H. Qed.

  Global Instance into_guar_impl (φ : Prop) P G :
    IntoGuar P G → IntoGuar (⌜φ⌝ → P) (⌜φ⌝ → G) | 10.
  Proof. intros H. unfold IntoGuar in *. iApply guar_impl. iApply H. Qed.
  Global Instance into_guar_forall {X} (P : X → iProp Σ) (G : X → itrProp Λ Σ) :
    (∀ x, IntoGuar (P x) (G x)) → IntoGuar (∀ x, P x) (itrProp_forall G) | 10.
  Proof. intros H. unfold IntoGuar in *. iApply guar_forall. iIntros (x). iApply H. Qed.
  Global Instance into_guar_persistently P G :
    IntoGuar P G → IntoGuar (□ P) G | 10.
  Proof. intros H. unfold IntoGuar in *. iApply guar_persistently. iApply H. Qed.
  Global Instance into_guar_alwaysI_guar N P G :
    IntoGuar (alwaysI_guar N P G) (itrProp_always G) | 10.
  Proof. apply guar_alwaysI_guar. Qed.
  Global Instance into_guar_alwaysI_as N P V G :
    IntoGuar V G → IntoGuar (alwaysI_as N P V) (itrProp_always G) | 10.
  Proof. intros H. unfold IntoGuar in *. by apply guar_alwaysI_as_valid. Qed.
  Global Instance into_guar_alwaysI N P G :
    IntoGuar P G → IntoGuar (alwaysI N P) (itrProp_always G) | 10.
  Proof. intros H. unfold IntoGuar in *. by apply guar_alwaysI_valid. Qed.
  Global Instance into_guar_untilI_guar N k q P Q G1 G2 :
    IntoGuar (untilI_guar N k q P Q G1 G2) (itrProp_until G1 G2) | 10.
  Proof. apply guar_untilI_guar. Qed.
  Global Instance into_guar_untilI N k q P Q G1 G2 :
    IntoGuar P G1 → IntoGuar Q G2 → IntoGuar (untilI N k q P Q) (itrProp_until G1 G2) | 10.
  Proof. intros H1 H2. unfold IntoGuar in *. by apply guar_untilI_valid. Qed.
  (** A done until, against a target until with any left formula. *)
  Global Instance into_guar_untilI_done_guar k Q G1 G2 :
    IntoGuar (untilI_done_guar k Q G2) (itrProp_until G1 G2) | 10.
  Proof. apply guar_untilI_done_guar. Qed.
  Global Instance into_guar_untilI_done k Q G1 G2 :
    IntoGuar Q G2 → IntoGuar (untilI_done k Q) (itrProp_until G1 G2) | 10.
  Proof. intros H. unfold IntoGuar in *. by apply guar_untilI_done_valid. Qed.
  (** A state fact guarantees its state atom. *)
  Global Instance into_guar_state_fact P φ :
    StateFact P φ → IntoGuar P (itrProp_state φ) | 10.
  Proof. intros HP. exact (guar_state_fact P φ). Qed.

  Global Instance into_guar_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ)
    (G : K → A → itrProp Λ Σ) :
    (∀ k x, IntoGuar (Φ k x) (G k x)) →
    IntoGuar ([∗ map] k ↦ x ∈ m, Φ k x)
      (itrProp_forall (λ k, itrProp_forall (λ x, itrProp_impl ⌜m !! k = Some x⌝ (G k x)))) | 10.
  Proof. intros HG. unfold IntoGuar in *. iApply guar_big_sepM. iIntros (k x). iApply HG. Qed.
  Global Instance into_guar_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → itrProp Λ Σ) :
    (∀ k x, IntoGuar (Φ k x) (G k x)) →
    IntoGuar ([∗ list] k ↦ x ∈ l, Φ k x)
      (itrProp_forall (λ k, itrProp_forall (λ x, itrProp_impl ⌜l !! k = Some x⌝ (G k x)))) | 10.
  Proof. intros HG. unfold IntoGuar in *. iApply guar_big_sepL. iIntros (k x). iApply HG. Qed.
  Global Instance into_guar_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → itrProp Λ Σ) :
    (∀ x, IntoGuar (Φ x) (G x)) →
    IntoGuar ([∗ set] x ∈ X, Φ x) (itrProp_forall (λ x, itrProp_impl ⌜x ∈ X⌝ (G x))) | 10.
  Proof. intros HG. unfold IntoGuar in *. iApply guar_big_sepS. iIntros (x). iApply HG. Qed.

  Lemma guar_inferred (Q : iProp Σ) G `{!IntoGuar Q G} : ⊢ Q ⊨ₜ itrProp_inferred Q.
  Proof. done. Qed.

End into_guar.

(* Existentials. With an unknown target, the strongest guarantee of the body is inferred and
   then collapsed ([SimplExist]). With a known target, the body is checked against it
   ([IntoGuarExistCheck]). *)
Global Hint Extern 0 (IntoGuarExist _ ?G) =>
  evar_headed G; notypeclasses refine (into_guar_exist_infer _ _ _ _ _) : typeclass_instances.
Global Hint Extern 0 (IntoGuarExist _ ?G) =>
  assert_fails (evar_headed G);
  notypeclasses refine (into_guar_exist_check _ _ _) : typeclass_instances.

(* A done until has no left formula: with an unknown target, it is inferred as a finally. *)
Global Hint Extern 0 (IntoGuar (untilI_done_guar _ _ _) ?G) =>
  evar_headed G; notypeclasses refine (into_guar_untilI_done_guar _ _ itrProp_true _) : typeclass_instances.
Global Hint Extern 0 (IntoGuar (untilI_done _ _) ?G) =>
  evar_headed G; notypeclasses refine (into_guar_untilI_done _ _ itrProp_true _ _) : typeclass_instances.

(* The fallback, for an unknown target or [itrProp_true], and only once the formula and the
   ghost-state instances contain no evars (resolution is retried once they are solved). *)
Global Hint Extern 100 (@IntoGuar ?Λ ?Σ ?Ht ?Hs ?P ?G) =>
  assert_fails (has_evar Λ); assert_fails (has_evar Σ); assert_fails (has_evar Ht); assert_fails (has_evar Hs);
  assert_fails (has_evar P);
  first [evar_headed G | unify G (@itrProp_true Λ Σ)];
  notypeclasses refine (into_guar_default P) : typeclass_instances.

(** ** The trace reading of a guarantee

    [ItrPropExt] reads [itrProp_canon P] through [IntoGuar]. [IntoTrace P R]: [P]
    guarantees the trace property [R] ([tr_canon P ⊆ R]), the form adequacy takes. *)
Section into_trace.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Global Instance itrProp_ext_canon P G R : IntoGuar P G → ItrPropExt G R → ItrPropExt (itrProp_canon P) R | 10.
  Proof. intros HG HR τ Hτ. apply HR. exact (itrProp_canon_ext P G τ HG Hτ). Qed.

  Class IntoTrace (P : iProp Σ) (R : trProp Λ) : Prop := into_trace : tr_canon P ⊆ R.

  Global Instance into_trace_of P G R : IntoGuar P G → ItrPropExt G R → IntoTrace P R | 10.
  Proof. intros HG HR. apply tr_canon_le. by exists G. Qed.
End into_trace.
Global Arguments into_trace {_ _ _ _} _ _ {_}.
Global Hint Mode IntoTrace - - - - ! - : typeclass_instances.

(** The trace property inferred for [P]: [Definition R : trProp Λ := ltac:(tr_of P).] *)
Definition tr_inferred `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (P : iProp Σ) {R : trProp Λ} `{!IntoTrace P R} : trProp Λ := R.
Global Arguments tr_inferred {_ _ _ _} _ {_ _}.
Ltac tr_of P := let R := eval cbv [tr_inferred] in (tr_inferred P%I) in exact R.

(** ** Examples and unit checks *)
Section examples.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  (** Ghost quantification over iProp, scoping over two temporal operators. *)
  Local Lemma ex_iprop N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ) ⊨ₜ
      (itrProp_always itrProp_true ∧ itrProp_finally itrProp_true).
  Proof.
    iApply guar_exist_ghost. iIntros (Ψ).
    iApply guar_sep; [iApply guar_alwaysI_valid; apply guar_true|].
    iApply guar_untilI_valid; apply guar_true.
  Qed.

  (** An invariant whose content changes over time, each content carrying its own guarantee. *)
  Local Lemma ex_dynamic_inv N G : ⊢ alwaysI N (∃ P : iProp Σ, P ∗ P ⊨ₜ G) ⊨ₜ itrProp_always G.
  Proof. iApply guar_alwaysI_valid. iApply guar_packed. Qed.

  (** The same guarantee, inferred. *)
  Local Lemma ex_iprop_inferred N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ) ⊨ₜ
      (itrProp_always itrProp_true ∧ itrProp_until (itrProp_pure True) itrProp_true).
  Proof. apply (into_guar _ _). Qed.

  (** Trace-visible quantification over a small type is inferred when the guarantee of
      the body depends on the witness. *)
  Local Lemma ex_visible_inferred N (f : nat → Prop) :
    ⊢ (∃ n : nat, alwaysI N ⌜f n⌝) ⊨ₜ itrProp_exist (λ n : nat, itrProp_always (itrProp_pure (f n))).
  Proof. apply (into_guar _ _). Qed.

  (** The inferred trace property as a closed term. *)
  Local Definition ex_itrProp_of N1 N2 k : itrProp Λ Σ :=
    ltac:(itrProp_of ((∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ)%I)).
  Local Lemma ex_itrProp_of_eq N1 N2 k :
    ex_itrProp_of N1 N2 k = (itrProp_always itrProp_true ∧ itrProp_until (itrProp_pure True) itrProp_true)%ITR.
  Proof. done. Qed.

  (** A done until, allocated with its right formula at hand, exports the until of any left
      formula in the form the adequacy takes: a formula, its guarantee, and the formula
      back. *)
  Local Lemma ex_until_done_export E p K ℓ (μ : measure) (Q : iProp Σ) φ `{!StateFact Q φ}
      (G1 : itrProp Λ Σ) :
    parP_le p ℓ -∗ parP_kids p K -∗ Q -∗
    |={E}=>m parP_kids p K ∗
      ∃ P : iProp Σ, (P ⊨ₜ itrProp_until G1 (itrProp_state φ)) ∗ P ∗ (P -∗ Q).
  Proof.
    iIntros "B Kp Hπ". iMod (obl_new E p K ℓ μ with "B Kp") as (k) "(%Hk& Kp& Kk& Oa& _& _)".
    iMod (untilI_done_init' with "Oa Kp Kk Hπ") as "[U $]"; first done.
    iModIntro. iExists (untilI_done k Q). iFrame "U". iSplit.
    - iApply (into_guar _ _).
    - iIntros "U". by iDestruct (untilI_done_elim with "U") as "[$ _]".
  Qed.

  (** A strong until, once discharged, is a done until with the same guarantee. *)
  Local Lemma ex_until_discharged E N k p K (Q : iProp Σ) φ `{!StateFact Q φ} (P : iProp Σ) :
    ↑N ⊆ E → k ∈ K →
    £n 1 -∗ untilI N k 1 P Q -∗ parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
    |={E}=>m ∃ U : iProp Σ, (U ⊨ₜ itrProp_until (itrProp_canon P) (itrProp_state φ)) ∗ U ∗ parP_kids p (K ∖ {[k]}).
  Proof.
    iIntros (HN Hk) "LC U Kp Kk Hπ". iMod (untilI_discharge_done with "U") as "U"; first done.
    iApply (lc_sfmupd_add_later with "LC"). iNext. iDestruct "U" as "[_ U]".
    iPoseProof ("U" $! p K Hk with "Kp Kk Hπ") as "U".
    iMod ("U" $! (E ∖ ↑N)) as "U". iMod "U" as "[U $]". iModIntro.
    iExists (untilI_done k Q). iFrame "U". iApply (into_guar _ _).
  Qed.

  (** Its inferred trace property is the finally of its right formula. *)
  Local Definition ex_itrProp_of_done k (Q : iProp Σ) φ `{!StateFact Q φ} : itrProp Λ Σ :=
    ltac:(itrProp_of (untilI_done k Q)).
  Local Lemma ex_itrProp_of_done_eq k (Q : iProp Σ) φ `{!StateFact Q φ} :
    ex_itrProp_of_done k Q φ = itrProp_finally (itrProp_state φ).
  Proof. done. Qed.
  Local Lemma ex_finally_done k (Q : iProp Σ) φ `{!StateFact Q φ} :
    ⊢ untilI_done k Q ⊨ₜ itrProp_finally (itrProp_state φ).
  Proof. apply (into_guar _ _). Qed.

  (** A higher-order specification quantifies over the content together with its guarantee
      (the guarantee of the content of an [alwaysI] must be valid, not a hypothesis). *)
  Local Lemma ex_higher_order N G :
    ⊢ (∃ P : iProp Σ, alwaysI N (P ∗ P ⊨ₜ G)) ⊨ₜ itrProp_always G.
  Proof.
    iApply guar_exist_ghost. iIntros (P). iApply guar_alwaysI_valid.
    iApply (guar_mono (∃ P, P ∗ P ⊨ₜ G)%I with "[]"); first by iIntros "!> H"; iExists P.
    iApply guar_packed.
  Qed.

  (** A temporal antecedent used in the logic: by completeness, the in-logic reading of
      "eventually [φ]" strengthens a guarantee. *)
  Local Lemma ex_impl_guar P φ G :
    P ⊨ₜ G ⊢ P ⊨ₜ itrProp_impl (itrProp_finally (itrProp_state φ)) (itrProp_and (itrProp_finally (itrProp_state φ)) G).
  Proof.
    apply (guar_impl_intro _ _ _ _ (itrProp_le_refl _)).
  Qed.

  (** The inferred trace property of an iProp, as a trace predicate. *)
  Local Lemma ex_tr_of N1 N2 k :
    (ltac:(tr_of ((∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ)%I)) : trProp Λ) =
    (□ ⌜True⌝ ∧ ◇ ⌜True⌝)%R.
  Proof. done. Qed.

  (** An implication exported on traces: the inferred guarantee of a case split implies it
      (compare [guar_impl]). *)
  Local Lemma ex_impl_cast (φ : Prop) (P Q : iProp Σ) G H `{!IntoGuar P G} `{!IntoGuar Q H} :
    tr_canon ((⌜φ⌝ ∗ P) ∨ (⌜¬φ⌝ ∗ Q)) ⊆ (⌜φ⌝ → itrProp_external G)%R.
  Proof.
    etrans; first apply (into_trace _ _). tr_unfold.
    intros τ [[Hφ HG]|[Hnφ _]] H'; [done|contradiction].
  Qed.

  (** Unsound: an iProp implication guaranteeing the implication of the guarantees (the
      antecedent's resources are not determined by the trace). *)
  Local Lemma naive_impl_rule_unsound :
    (∀ (P1 P2 : iProp Σ) G1 G2, (⊢ P1 ⊨ₜ G1) → (⊢ P2 ⊨ₜ G2) → ⊢ (P1 → P2) ⊨ₜ itrProp_impl G1 G2) →
    ⊢ True ⊨ₜ itrProp_impl itrProp_true (itrProp_pure False).
  Proof.
    intros Hrule.
    assert (HF : ∀ G, ⊢ (False : iProp Σ) ⊨ₜ G).
    { intros G. rewrite /guar. iIntros "!>" (?????????) "(_& _& [])". }
    iApply (guar_mono (False → False)%I with "[]"); first by iIntros "!> _ []".
    iApply Hrule; [apply guar_true|apply HF].
  Qed.

  Local Lemma itrProp_impl_true_false_empty τ : ¬ itrProp_external (itrProp_impl (Λ:=Λ) (Σ:=Σ) itrProp_true (itrProp_pure False)) τ.
  Proof. intros H. by apply H. Qed.

End examples.
