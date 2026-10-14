From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trace_prop_rules trspec.
From transfinite.stepindex Require Import ordinals.

(** * Rules for trace specifications ([trSpec])

    The interface for the properties that guarantees [P ⊨ₜ G] are about (guarantee.v). An
    [trSpec] is read twice (trspec.v): the internal reading is what a run establishes, the
    external reading ([trSpec_external G], a [trProp]) is what adequacy concludes. Each
    reading has its entailment:

    - [G ⊑ H] compares internal readings. It transports guarantees ([guar_weaken]), and
      the connectives are monotone in it. It is sound for the external readings of complete
      properties ([trSpec_le_sound]) but, the internal readings being deferred by a later,
      too weak for temporal reasoning: not even [□ ⊥ ⊑ ⊥] holds
      ([trSpec_always_elim_not_le]). Use it for the structure of a property only.
    - [trSpec_external G ⊆ R] compares external readings on traces, with the rules of
      trace_prop_rules.v, where every law of LTL holds. [TrSpecExt G R] computes the
      external reading of [G] from its shape. The cast [trSpec_cast G R pf] keeps the
      internal reading of [G] with [R] as its external reading, so
      [G ⊑ trSpec_cast G R pf]: every trace-level consequence of a property is guaranteed
      along with it ([guar_cast]).

    Connectives (trspec.v, scope [%SPEC]): [⌜φ⌝], [∧], [∨], [→] (the antecedent read on the
    trace), [∀], [∃] (small types), [trSpec_state φ], [□ G], [◇ G], [G Uₜ H]. *)

Global Instance trSpec_le_preorder {Λ Σ} : PreOrder (⊑@{trSpec Λ Σ}).
Proof. split; [intros ?; apply trSpec_le_refl|intros ???; apply trSpec_le_trans]. Qed.

(** ** In-logic entailment: monotonicity of the connectives *)
Section trSpec_le_rules.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A : trSpec Λ Σ.

  Lemma trSpec_le_true G : trSpec_le G trSpec_true.
  Proof. intros ??. by iIntros "_". Qed.
  Lemma trSpec_and_elim_l G1 G2 : trSpec_le (trSpec_and G1 G2) G1.
  Proof. intros ??. rewrite /= /trI_and. by iIntros "[$ _]". Qed.
  Lemma trSpec_and_elim_r G1 G2 : trSpec_le (trSpec_and G1 G2) G2.
  Proof. intros ??. rewrite /= /trI_and. by iIntros "[_ $]". Qed.

  Lemma trSpec_or_mono G1 G2 G1' G2' :
    trSpec_le G1 G1' → trSpec_le G2 G2' → trSpec_le (trSpec_or G1 G2) (trSpec_or G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /trI_or. by rewrite H1 H2. Qed.
  Lemma trSpec_and_mono G1 G2 G1' G2' :
    trSpec_le G1 G1' → trSpec_le G2 G2' → trSpec_le (trSpec_and G1 G2) (trSpec_and G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /trI_and. by rewrite H1 H2. Qed.
  (** Antecedents are compared as trace properties. *)
  Lemma trSpec_impl_mono A A' G G' :
    (∀ τ, trSpec_external A' τ → trSpec_external A τ) → trSpec_le G G' → trSpec_le (trSpec_impl A G) (trSpec_impl A' G').
  Proof. intros HA HG ??. rewrite /= /trI_impl. iIntros "H %H'". iApply HG. iApply "H". eauto. Qed.
  Lemma trSpec_impl_intro_le A G : trSpec_le G (trSpec_impl A G).
  Proof. intros ??. rewrite /= /trI_impl. by iIntros "H _". Qed.
  (** The antecedent is read on the trace, so an implication is the disjunction of its
      consequent with the negated antecedent. *)
  Lemma trSpec_impl_or_not A G : trSpec_le (trSpec_impl A G) (trSpec_or (trSpec_impl A (trSpec_pure False)) G).
  Proof.
    intros ? τ. rewrite /= /trI_impl /trI_or /trI_pure. iIntros "H".
    destruct (Classical_Prop.classic (trSpec_external A τ)) as [HA|HA].
    - iRight. by iApply "H".
    - iLeft. by iIntros (?).
  Qed.
  Lemma trSpec_or_not_impl A G : trSpec_le (trSpec_or (trSpec_impl A (trSpec_pure False)) G) (trSpec_impl A G).
  Proof.
    intros ? τ. rewrite /= /trI_impl /trI_or /trI_pure. iIntros "[H|H] %HA"; last done.
    by iDestruct ("H" $! HA) as %[].
  Qed.

  (** Antecedents compose on traces, for any antecedents: a conjunction curries, a
      disjunction splits, an existential becomes a universal. *)
  Lemma trSpec_impl_curry A1 A2 G :
    trSpec_le (trSpec_impl A1 (trSpec_impl A2 G)) (trSpec_impl (trSpec_and A1 A2) G).
  Proof. intros ? τ. rewrite /= /trI_impl /tr_and. iIntros "H" ([H1 H2]). by iApply "H". Qed.
  Lemma trSpec_impl_uncurry A1 A2 G :
    trSpec_le (trSpec_impl (trSpec_and A1 A2) G) (trSpec_impl A1 (trSpec_impl A2 G)).
  Proof. intros ? τ. rewrite /= /trI_impl /tr_and. iIntros "H" (H1 H2). by iApply "H". Qed.
  Lemma trSpec_impl_or_split A1 A2 G :
    trSpec_le (trSpec_and (trSpec_impl A1 G) (trSpec_impl A2 G)) (trSpec_impl (trSpec_or A1 A2) G).
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl /tr_or. iIntros "H" ([H1|H2]).
    - iDestruct "H" as "[H _]". by iApply "H".
    - iDestruct "H" as "[_ H]". by iApply "H".
  Qed.
  Lemma trSpec_impl_or_join A1 A2 G :
    trSpec_le (trSpec_impl (trSpec_or A1 A2) G) (trSpec_and (trSpec_impl A1 G) (trSpec_impl A2 G)).
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl /tr_or. iIntros "H".
    iSplit; iIntros (?); iApply "H"; iPureIntro; auto.
  Qed.
  Lemma trSpec_impl_exist {X} `{!TypeExistentialProperty X ordI} (A : X → trSpec Λ Σ) G :
    trSpec_le (trSpec_forall (λ x, trSpec_impl (A x) G)) (trSpec_impl (trSpec_exist A) G).
  Proof.
    intros ? τ. rewrite /= /trI_forall /trI_impl /tr_exist. iIntros "H" ([x Hx]). by iApply ("H" $! x).
  Qed.
  Lemma trSpec_forall_mono {X} (G G' : X → trSpec Λ Σ) :
    (∀ x, trSpec_le (G x) (G' x)) → trSpec_le (trSpec_forall G) (trSpec_forall G').
  Proof. intros H ??. rewrite /= /trI_forall. iIntros "H %x". iApply H. iApply "H". Qed.
  Lemma trSpec_exist_mono {X} `{!TypeExistentialProperty X ordI} (G G' : X → trSpec Λ Σ) :
    (∀ x, trSpec_le (G x) (G' x)) → trSpec_le (trSpec_exist G) (trSpec_exist G').
  Proof. intros H ??. rewrite /= /trI_exist. iIntros "[%x H]". iExists x. by iApply H. Qed.

  Lemma trSpec_always_mono G G' : G ⊑ G' → (□ G)%SPEC ⊑ (□ G')%SPEC.
  Proof.
    intros Hle H τ. iIntros "HG". iApply (trSpec_always_mono_i with "[] HG").
    iNext. iIntros "!>" (τ') "H". iApply (Hle H τ' with "H").
  Qed.

  Lemma trSpec_until_mono G1 G2 G1' G2' :
    G1 ⊑ G1' → G2 ⊑ G2' → (G1 Uₜ G2)%SPEC ⊑ (G1' Uₜ G2')%SPEC.
  Proof.
    intros H1 H2 H τ. iIntros "HU". iApply (trSpec_until_mono_i with "[] [] HU").
    - iNext. iIntros "!>" (τ') "H". iApply (H1 H τ' with "H").
    - iNext. iIntros "!>" (τ') "H". iApply (H2 H τ' with "H").
  Qed.

End trSpec_le_rules.

(** ** Complete and instant antecedents *)
Section trSpec_impl_rules.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A H : trSpec Λ Σ.

  Lemma trSpec_impl_intro A H G `{HA : !TrSpecComplete A} :
    trSpec_le (trSpec_and A H) G → trSpec_le H (trSpec_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /trI_impl. iIntros "H %Hτ". iApply HG.
    rewrite /= /trI_and. iSplit; last done. by iApply HA.
  Qed.

  Lemma trSpec_impl_elim A G `{HA : !TrSpecInstant A} : trSpec_le (trSpec_and A (trSpec_impl A G)) G.
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl. iIntros "H".
    iAssert ⌜trSpec_external A τ⌝%I as %Hτ; first by iApply HA; iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ H]". by iApply "H".
  Qed.

End trSpec_impl_rules.

(** ** Casts and external readings *)
Section readings.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G H : trSpec Λ Σ.
  Implicit Types R : trProp Λ.

  Program Definition trSpec_cast G R (pf : trSpec_external G ⊆ R) : trSpec Λ Σ :=
    {| trSpec_internal _ := trSpec_internal G; trSpec_external := R |}.
  Next Obligation. intros G R pf ? F τ Hs. apply pf. by eapply trSpec_adeq. Qed.

  Lemma trSpec_cast_le G R pf : G ⊑ trSpec_cast G R pf.
  Proof. intros ??. done. Qed.
  Lemma trSpec_le_cast G R pf : trSpec_cast G R pf ⊑ G.
  Proof. intros ??. done. Qed.
  Lemma trSpec_cast_ext G R pf : trSpec_external (trSpec_cast G R pf) = R.
  Proof. done. Qed.
  Lemma trSpec_cast_complete G R pf `{!TrSpecComplete G} :
    R ⊆ trSpec_external G → TrSpecComplete (trSpec_cast G R pf).
  Proof. intros HR ? τ Hτ. change (⊢ trSpec_internal G τ). apply trSpec_complete. by apply HR. Qed.

  (** [TrSpecExt G R]: [R] is a trace reading of [G]. The instances follow the connectives;
      the fallback is the reading itself. *)
  Class TrSpecExt G R : Prop := trSpec_ext_of : trSpec_external G ⊆ R.

  Global Instance trSpec_ext_pure φ : TrSpecExt (trSpec_pure φ) (tr_pure φ) | 10.
  Proof. by intros τ. Qed.
  Global Instance trSpec_ext_state φ : TrSpecExt (trSpec_state φ) (tr_state φ) | 10.
  Proof. by intros τ. Qed.
  Global Instance trSpec_ext_and G1 G2 R1 R2 :
    TrSpecExt G1 R1 → TrSpecExt G2 R2 → TrSpecExt (trSpec_and G1 G2) (R1 ∧ R2)%R | 10.
  Proof. intros H1 H2 τ [??]. split; auto. Qed.
  Global Instance trSpec_ext_or G1 G2 R1 R2 :
    TrSpecExt G1 R1 → TrSpecExt G2 R2 → TrSpecExt (trSpec_or G1 G2) (R1 ∨ R2)%R | 10.
  Proof. intros H1 H2 τ [?|?]; [left|right]; auto. Qed.
  Global Instance trSpec_ext_impl A G R :
    TrSpecExt G R → TrSpecExt (trSpec_impl A G) (trSpec_external A → R)%R | 10.
  Proof. intros HG τ HAG HA. by apply HG, HAG. Qed.
  Global Instance trSpec_ext_forall {X} (G : X → trSpec Λ Σ) (R : X → trProp Λ) :
    (∀ x, TrSpecExt (G x) (R x)) → TrSpecExt (trSpec_forall G) (tr_forall X R) | 10.
  Proof. intros HG τ H x. by apply HG. Qed.
  Global Instance trSpec_ext_exist {X} `{!TypeExistentialProperty X ordI} (G : X → trSpec Λ Σ) (R : X → trProp Λ) :
    (∀ x, TrSpecExt (G x) (R x)) → TrSpecExt (trSpec_exist G) (tr_exist X R) | 10.
  Proof. intros HG τ [x H]. exists x. by apply HG. Qed.
  Global Instance trSpec_ext_always G R : TrSpecExt G R → TrSpecExt (trSpec_always G) (□ R)%R | 10.
  Proof. intros HG. by apply tr_always_mono. Qed.
  Global Instance trSpec_ext_finally G R : TrSpecExt G R → TrSpecExt (trSpec_finally G) (◇ R)%R | 9.
  Proof. intros HG. by apply tr_finally_mono. Qed.
  Global Instance trSpec_ext_until G1 G2 R1 R2 :
    TrSpecExt G1 R1 → TrSpecExt G2 R2 → TrSpecExt (G1 Uₜ G2)%SPEC (R1 Uₜ R2)%R | 10.
  Proof. intros H1 H2. by apply tr_until_mono. Qed.
  Global Instance trSpec_ext_cast G R pf : TrSpecExt (trSpec_cast G R pf) R | 10.
  Proof. by intros τ. Qed.
  Global Instance trSpec_ext_default G : TrSpecExt G (trSpec_external G) | 100.
  Proof. by intros τ. Qed.

End readings.
Global Hint Mode TrSpecExt - - ! - : typeclass_instances.
Global Arguments trSpec_ext_of {_ _} _ _ {_}.
