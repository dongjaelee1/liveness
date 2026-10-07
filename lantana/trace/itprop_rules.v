From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trace_prop_rules itprop.
From transfinite.stepindex Require Import ordinals.

(** * Rules for internalized trace properties ([itProp])

    The interface of internalized trace properties, the properties that guarantees
    [P ⊨ₜ G] (guarantee.v) are about. An [itProp] is read twice (itprop.v): its internal
    reading is what a run establishes, its external reading ([itProp_external G], a
    [trProp]) is what adequacy concludes. Each reading has its entailment:

    - [G ⊑ H] compares internal readings. It transports guarantees ([temporal_weaken]) and
      the connectives are monotone in it (the rules below). It is sound for external
      readings of complete properties ([itProp_le_sound]) but, as the internal readings are
      deferred by a later, too weak for temporal reasoning: not even [□ ⊥ ⊑ ⊥] holds
      ([itProp_always_elim_not_le]). Use it for the structure of a property only.
    - [itProp_external G ⊆ R] compares external readings, on traces, with the rules of
      trace_prop_rules.v, where every law of LTL holds. [ItPropExt G R] computes the external
      reading of [G] from its shape. The cast [itProp_cast G R pf] keeps the internal reading
      of [G] and takes [R] as its external one, so [G ⊑ itProp_cast G R pf]: every
      trace-level consequence of a property is guaranteed along with it ([temporal_cast]).

    The connectives (itprop.v, scope [%IT]): [⌜φ⌝], [G ∧ H], [G ∨ H], [G → H] (the
    antecedent read on the trace), [∀ x, G], [∃ x, G] (small types), [itProp_state φ],
    [□ G], [◇ G], [G Uₜ H]. *)

Global Instance itProp_le_preorder {Λ Σ} : PreOrder (⊑@{itProp Λ Σ}).
Proof. split; [intros ?; apply itProp_le_refl|intros ???; apply itProp_le_trans]. Qed.

(** ** In-logic entailment: monotonicity of the connectives *)
Section itProp_le_rules.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A : itProp Λ Σ.

  Lemma itProp_le_true G : itProp_le G itProp_true.
  Proof. intros ??. by iIntros "_". Qed.
  Lemma itProp_and_elim_l G1 G2 : itProp_le (itProp_and G1 G2) G1.
  Proof. intros ??. rewrite /= /trI_and. by iIntros "[$ _]". Qed.
  Lemma itProp_and_elim_r G1 G2 : itProp_le (itProp_and G1 G2) G2.
  Proof. intros ??. rewrite /= /trI_and. by iIntros "[_ $]". Qed.

  Lemma itProp_or_mono G1 G2 G1' G2' :
    itProp_le G1 G1' → itProp_le G2 G2' → itProp_le (itProp_or G1 G2) (itProp_or G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /trI_or. by rewrite H1 H2. Qed.
  Lemma itProp_and_mono G1 G2 G1' G2' :
    itProp_le G1 G1' → itProp_le G2 G2' → itProp_le (itProp_and G1 G2) (itProp_and G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /trI_and. by rewrite H1 H2. Qed.
  (** Antecedents are compared as trace properties. *)
  Lemma itProp_impl_mono A A' G G' :
    (∀ τ, itProp_external A' τ → itProp_external A τ) → itProp_le G G' → itProp_le (itProp_impl A G) (itProp_impl A' G').
  Proof. intros HA HG ??. rewrite /= /trI_impl. iIntros "H %H'". iApply HG. iApply "H". eauto. Qed.
  Lemma itProp_impl_intro_le A G : itProp_le G (itProp_impl A G).
  Proof. intros ??. rewrite /= /trI_impl. by iIntros "H _". Qed.
  (** The antecedent is read on the trace, so an implication is the disjunction of its
      consequent with the negated antecedent. *)
  Lemma itProp_impl_or_not A G : itProp_le (itProp_impl A G) (itProp_or (itProp_impl A (itProp_pure False)) G).
  Proof.
    intros ? τ. rewrite /= /trI_impl /trI_or /trI_pure. iIntros "H".
    destruct (Classical_Prop.classic (itProp_external A τ)) as [HA|HA].
    - iRight. by iApply "H".
    - iLeft. by iIntros (?).
  Qed.
  Lemma itProp_or_not_impl A G : itProp_le (itProp_or (itProp_impl A (itProp_pure False)) G) (itProp_impl A G).
  Proof.
    intros ? τ. rewrite /= /trI_impl /trI_or /trI_pure. iIntros "[H|H] %HA"; last done.
    by iDestruct ("H" $! HA) as %[].
  Qed.

  (** Antecedents compose on traces, for any antecedents: a conjunction curries, a
      disjunction splits, an existential becomes a universal. *)
  Lemma itProp_impl_curry A1 A2 G :
    itProp_le (itProp_impl A1 (itProp_impl A2 G)) (itProp_impl (itProp_and A1 A2) G).
  Proof. intros ? τ. rewrite /= /trI_impl /tr_and. iIntros "H" ([H1 H2]). by iApply "H". Qed.
  Lemma itProp_impl_uncurry A1 A2 G :
    itProp_le (itProp_impl (itProp_and A1 A2) G) (itProp_impl A1 (itProp_impl A2 G)).
  Proof. intros ? τ. rewrite /= /trI_impl /tr_and. iIntros "H" (H1 H2). by iApply "H". Qed.
  Lemma itProp_impl_or_split A1 A2 G :
    itProp_le (itProp_and (itProp_impl A1 G) (itProp_impl A2 G)) (itProp_impl (itProp_or A1 A2) G).
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl /tr_or. iIntros "H" ([H1|H2]).
    - iDestruct "H" as "[H _]". by iApply "H".
    - iDestruct "H" as "[_ H]". by iApply "H".
  Qed.
  Lemma itProp_impl_or_join A1 A2 G :
    itProp_le (itProp_impl (itProp_or A1 A2) G) (itProp_and (itProp_impl A1 G) (itProp_impl A2 G)).
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl /tr_or. iIntros "H".
    iSplit; iIntros (?); iApply "H"; iPureIntro; auto.
  Qed.
  Lemma itProp_impl_exist {X} `{!TypeExistentialProperty X ordI} (A : X → itProp Λ Σ) G :
    itProp_le (itProp_forall (λ x, itProp_impl (A x) G)) (itProp_impl (itProp_exist A) G).
  Proof.
    intros ? τ. rewrite /= /trI_forall /trI_impl /tr_exist. iIntros "H" ([x Hx]). by iApply ("H" $! x).
  Qed.
  Lemma itProp_forall_mono {X} (G G' : X → itProp Λ Σ) :
    (∀ x, itProp_le (G x) (G' x)) → itProp_le (itProp_forall G) (itProp_forall G').
  Proof. intros H ??. rewrite /= /trI_forall. iIntros "H %x". iApply H. iApply "H". Qed.
  Lemma itProp_exist_mono {X} `{!TypeExistentialProperty X ordI} (G G' : X → itProp Λ Σ) :
    (∀ x, itProp_le (G x) (G' x)) → itProp_le (itProp_exist G) (itProp_exist G').
  Proof. intros H ??. rewrite /= /trI_exist. iIntros "[%x H]". iExists x. by iApply H. Qed.

  Lemma itProp_always_mono G G' : G ⊑ G' → (□ G)%IT ⊑ (□ G')%IT.
  Proof.
    intros Hle H τ. iIntros "HG". iApply (itProp_always_mono_i with "[] HG").
    iNext. iIntros "!>" (τ') "H". iApply (Hle H τ' with "H").
  Qed.

  Lemma itProp_until_mono G1 G2 G1' G2' :
    G1 ⊑ G1' → G2 ⊑ G2' → (G1 Uₜ G2)%IT ⊑ (G1' Uₜ G2')%IT.
  Proof.
    intros H1 H2 H τ. iIntros "HU". iApply (itProp_until_mono_i with "[] [] HU").
    - iNext. iIntros "!>" (τ') "H". iApply (H1 H τ' with "H").
    - iNext. iIntros "!>" (τ') "H". iApply (H2 H τ' with "H").
  Qed.

End itProp_le_rules.

(** ** Complete and instant antecedents *)
Section itProp_impl_rules.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A H : itProp Λ Σ.

  Lemma itProp_impl_intro A H G `{HA : !ItPropComplete A} :
    itProp_le (itProp_and A H) G → itProp_le H (itProp_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /trI_impl. iIntros "H %Hτ". iApply HG.
    rewrite /= /trI_and. iSplit; last done. by iApply HA.
  Qed.

  Lemma itProp_impl_elim A G `{HA : !ItPropInstant A} : itProp_le (itProp_and A (itProp_impl A G)) G.
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl. iIntros "H".
    iAssert ⌜itProp_external A τ⌝%I as %Hτ; first by iApply HA; iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ H]". by iApply "H".
  Qed.

End itProp_impl_rules.

(** ** Trace readings: the two entailments, and casts

    A property is read twice. Its in-logic reading [itProp_internal] is what a run establishes: a
    guarantee [P ⊨ₜ G] (guarantee.v) turns [P], at a position, into the in-logic reading of
    [G] there. Its trace reading [itProp_external] is what adequacy concludes.

    Accordingly, two entailments:
    - [G ⊑ H] ([itProp_le]) compares in-logic readings. It transports guarantees
      ([temporal_weaken]), and the connectives are monotone in it. It is sound for trace
      readings ([itProp_le_sound]), but it is as weak as the readings are deferred: the
      in-logic readings of [□] and [𝒰] start with a later, so not even [□ ⊥ ⊑ ⊥] holds
      ([itProp_always_elim_not_le]). It is the entailment of the structure of a property.
    - [itProp_external G ⊆ R] compares trace readings, on traces (trace_prop.v), where every law of
      LTL holds. It is the entailment of the meaning of a property. The cast
      [itProp_cast G R pf] keeps the in-logic reading of [G] and takes [R] as its trace
      reading, so [G ⊑ itProp_cast G R pf]: every trace-level consequence of a property is
      guaranteed along with it ([temporal_cast]).

    [ItPropExt G R] computes a trace reading of [G] from its shape, as a trace predicate. *)
Section readings.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G H : itProp Λ Σ.
  Implicit Types R : trProp Λ.

  Program Definition itProp_cast G R (pf : itProp_external G ⊆ R) : itProp Λ Σ :=
    {| itProp_internal _ := itProp_internal G; itProp_external := R |}.
  Next Obligation. intros G R pf ? F τ Hs. apply pf. by eapply itProp_adeq. Qed.

  Lemma itProp_cast_le G R pf : G ⊑ itProp_cast G R pf.
  Proof. intros ??. done. Qed.
  Lemma itProp_le_cast G R pf : itProp_cast G R pf ⊑ G.
  Proof. intros ??. done. Qed.
  Lemma itProp_cast_ext G R pf : itProp_external (itProp_cast G R pf) = R.
  Proof. done. Qed.
  Lemma itProp_cast_complete G R pf `{!ItPropComplete G} :
    R ⊆ itProp_external G → ItPropComplete (itProp_cast G R pf).
  Proof. intros HR ? τ Hτ. change (⊢ itProp_internal G τ). apply itProp_complete. by apply HR. Qed.

  (** [ItPropExt G R]: [R] is a trace reading of [G]. The instances follow the connectives;
      the fallback is the reading itself. *)
  Class ItPropExt G R : Prop := itProp_ext_of : itProp_external G ⊆ R.

  Global Instance itProp_ext_pure φ : ItPropExt (itProp_pure φ) (tr_pure φ) | 10.
  Proof. by intros τ. Qed.
  Global Instance itProp_ext_state φ : ItPropExt (itProp_state φ) (tr_state φ) | 10.
  Proof. by intros τ. Qed.
  Global Instance itProp_ext_and G1 G2 R1 R2 :
    ItPropExt G1 R1 → ItPropExt G2 R2 → ItPropExt (itProp_and G1 G2) (R1 ∧ R2)%R | 10.
  Proof. intros H1 H2 τ [??]. split; auto. Qed.
  Global Instance itProp_ext_or G1 G2 R1 R2 :
    ItPropExt G1 R1 → ItPropExt G2 R2 → ItPropExt (itProp_or G1 G2) (R1 ∨ R2)%R | 10.
  Proof. intros H1 H2 τ [?|?]; [left|right]; auto. Qed.
  Global Instance itProp_ext_impl A G R :
    ItPropExt G R → ItPropExt (itProp_impl A G) (itProp_external A → R)%R | 10.
  Proof. intros HG τ HAG HA. by apply HG, HAG. Qed.
  Global Instance itProp_ext_forall {X} (G : X → itProp Λ Σ) (R : X → trProp Λ) :
    (∀ x, ItPropExt (G x) (R x)) → ItPropExt (itProp_forall G) (tr_forall X R) | 10.
  Proof. intros HG τ H x. by apply HG. Qed.
  Global Instance itProp_ext_exist {X} `{!TypeExistentialProperty X ordI} (G : X → itProp Λ Σ) (R : X → trProp Λ) :
    (∀ x, ItPropExt (G x) (R x)) → ItPropExt (itProp_exist G) (tr_exist X R) | 10.
  Proof. intros HG τ [x H]. exists x. by apply HG. Qed.
  Global Instance itProp_ext_always G R : ItPropExt G R → ItPropExt (itProp_always G) (□ R)%R | 10.
  Proof. intros HG. by apply tr_always_mono. Qed.
  Global Instance itProp_ext_finally G R : ItPropExt G R → ItPropExt (itProp_finally G) (◇ R)%R | 9.
  Proof. intros HG. by apply tr_finally_mono. Qed.
  Global Instance itProp_ext_until G1 G2 R1 R2 :
    ItPropExt G1 R1 → ItPropExt G2 R2 → ItPropExt (itProp_until G1 G2) (tr_until R1 R2) | 10.
  Proof. intros H1 H2. by apply tr_until_mono. Qed.
  Global Instance itProp_ext_cast G R pf : ItPropExt (itProp_cast G R pf) R | 10.
  Proof. by intros τ. Qed.
  Global Instance itProp_ext_default G : ItPropExt G (itProp_external G) | 100.
  Proof. by intros τ. Qed.

End readings.
Global Hint Mode ItPropExt - - ! - : typeclass_instances.
Global Arguments itProp_ext_of {_ _} _ _ {_}.
