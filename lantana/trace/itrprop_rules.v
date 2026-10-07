From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trace_prop_rules itrprop.
From transfinite.stepindex Require Import ordinals.

(** * Rules for internalized trace properties ([itrProp])

    The interface for the properties that guarantees [P ⊨ₜ G] are about (guarantee.v). An
    [itrProp] is read twice (itrprop.v): the internal reading is what a run establishes, the
    external reading ([itrProp_external G], a [trProp]) is what adequacy concludes. Each
    reading has its entailment:

    - [G ⊑ H] compares internal readings. It transports guarantees ([temporal_weaken]), and
      the connectives are monotone in it. It is sound for the external readings of complete
      properties ([itrProp_le_sound]) but, the internal readings being deferred by a later,
      too weak for temporal reasoning: not even [□ ⊥ ⊑ ⊥] holds
      ([itrProp_always_elim_not_le]). Use it for the structure of a property only.
    - [itrProp_external G ⊆ R] compares external readings on traces, with the rules of
      trace_prop_rules.v, where every law of LTL holds. [ItrPropExt G R] computes the
      external reading of [G] from its shape. The cast [itrProp_cast G R pf] keeps the
      internal reading of [G] with [R] as its external reading, so
      [G ⊑ itrProp_cast G R pf]: every trace-level consequence of a property is guaranteed
      along with it ([temporal_cast]).

    Connectives (itrprop.v, scope [%ITR]): [⌜φ⌝], [∧], [∨], [→] (the antecedent read on the
    trace), [∀], [∃] (small types), [itrProp_state φ], [□ G], [◇ G], [G Uₜ H]. *)

Global Instance itrProp_le_preorder {Λ Σ} : PreOrder (⊑@{itrProp Λ Σ}).
Proof. split; [intros ?; apply itrProp_le_refl|intros ???; apply itrProp_le_trans]. Qed.

(** ** In-logic entailment: monotonicity of the connectives *)
Section itrProp_le_rules.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A : itrProp Λ Σ.

  Lemma itrProp_le_true G : itrProp_le G itrProp_true.
  Proof. intros ??. by iIntros "_". Qed.
  Lemma itrProp_and_elim_l G1 G2 : itrProp_le (itrProp_and G1 G2) G1.
  Proof. intros ??. rewrite /= /trI_and. by iIntros "[$ _]". Qed.
  Lemma itrProp_and_elim_r G1 G2 : itrProp_le (itrProp_and G1 G2) G2.
  Proof. intros ??. rewrite /= /trI_and. by iIntros "[_ $]". Qed.

  Lemma itrProp_or_mono G1 G2 G1' G2' :
    itrProp_le G1 G1' → itrProp_le G2 G2' → itrProp_le (itrProp_or G1 G2) (itrProp_or G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /trI_or. by rewrite H1 H2. Qed.
  Lemma itrProp_and_mono G1 G2 G1' G2' :
    itrProp_le G1 G1' → itrProp_le G2 G2' → itrProp_le (itrProp_and G1 G2) (itrProp_and G1' G2').
  Proof. intros H1 H2 ??. rewrite /= /trI_and. by rewrite H1 H2. Qed.
  (** Antecedents are compared as trace properties. *)
  Lemma itrProp_impl_mono A A' G G' :
    (∀ τ, itrProp_external A' τ → itrProp_external A τ) → itrProp_le G G' → itrProp_le (itrProp_impl A G) (itrProp_impl A' G').
  Proof. intros HA HG ??. rewrite /= /trI_impl. iIntros "H %H'". iApply HG. iApply "H". eauto. Qed.
  Lemma itrProp_impl_intro_le A G : itrProp_le G (itrProp_impl A G).
  Proof. intros ??. rewrite /= /trI_impl. by iIntros "H _". Qed.
  (** The antecedent is read on the trace, so an implication is the disjunction of its
      consequent with the negated antecedent. *)
  Lemma itrProp_impl_or_not A G : itrProp_le (itrProp_impl A G) (itrProp_or (itrProp_impl A (itrProp_pure False)) G).
  Proof.
    intros ? τ. rewrite /= /trI_impl /trI_or /trI_pure. iIntros "H".
    destruct (Classical_Prop.classic (itrProp_external A τ)) as [HA|HA].
    - iRight. by iApply "H".
    - iLeft. by iIntros (?).
  Qed.
  Lemma itrProp_or_not_impl A G : itrProp_le (itrProp_or (itrProp_impl A (itrProp_pure False)) G) (itrProp_impl A G).
  Proof.
    intros ? τ. rewrite /= /trI_impl /trI_or /trI_pure. iIntros "[H|H] %HA"; last done.
    by iDestruct ("H" $! HA) as %[].
  Qed.

  (** Antecedents compose on traces, for any antecedents: a conjunction curries, a
      disjunction splits, an existential becomes a universal. *)
  Lemma itrProp_impl_curry A1 A2 G :
    itrProp_le (itrProp_impl A1 (itrProp_impl A2 G)) (itrProp_impl (itrProp_and A1 A2) G).
  Proof. intros ? τ. rewrite /= /trI_impl /tr_and. iIntros "H" ([H1 H2]). by iApply "H". Qed.
  Lemma itrProp_impl_uncurry A1 A2 G :
    itrProp_le (itrProp_impl (itrProp_and A1 A2) G) (itrProp_impl A1 (itrProp_impl A2 G)).
  Proof. intros ? τ. rewrite /= /trI_impl /tr_and. iIntros "H" (H1 H2). by iApply "H". Qed.
  Lemma itrProp_impl_or_split A1 A2 G :
    itrProp_le (itrProp_and (itrProp_impl A1 G) (itrProp_impl A2 G)) (itrProp_impl (itrProp_or A1 A2) G).
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl /tr_or. iIntros "H" ([H1|H2]).
    - iDestruct "H" as "[H _]". by iApply "H".
    - iDestruct "H" as "[_ H]". by iApply "H".
  Qed.
  Lemma itrProp_impl_or_join A1 A2 G :
    itrProp_le (itrProp_impl (itrProp_or A1 A2) G) (itrProp_and (itrProp_impl A1 G) (itrProp_impl A2 G)).
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl /tr_or. iIntros "H".
    iSplit; iIntros (?); iApply "H"; iPureIntro; auto.
  Qed.
  Lemma itrProp_impl_exist {X} `{!TypeExistentialProperty X ordI} (A : X → itrProp Λ Σ) G :
    itrProp_le (itrProp_forall (λ x, itrProp_impl (A x) G)) (itrProp_impl (itrProp_exist A) G).
  Proof.
    intros ? τ. rewrite /= /trI_forall /trI_impl /tr_exist. iIntros "H" ([x Hx]). by iApply ("H" $! x).
  Qed.
  Lemma itrProp_forall_mono {X} (G G' : X → itrProp Λ Σ) :
    (∀ x, itrProp_le (G x) (G' x)) → itrProp_le (itrProp_forall G) (itrProp_forall G').
  Proof. intros H ??. rewrite /= /trI_forall. iIntros "H %x". iApply H. iApply "H". Qed.
  Lemma itrProp_exist_mono {X} `{!TypeExistentialProperty X ordI} (G G' : X → itrProp Λ Σ) :
    (∀ x, itrProp_le (G x) (G' x)) → itrProp_le (itrProp_exist G) (itrProp_exist G').
  Proof. intros H ??. rewrite /= /trI_exist. iIntros "[%x H]". iExists x. by iApply H. Qed.

  Lemma itrProp_always_mono G G' : G ⊑ G' → (□ G)%ITR ⊑ (□ G')%ITR.
  Proof.
    intros Hle H τ. iIntros "HG". iApply (itrProp_always_mono_i with "[] HG").
    iNext. iIntros "!>" (τ') "H". iApply (Hle H τ' with "H").
  Qed.

  Lemma itrProp_until_mono G1 G2 G1' G2' :
    G1 ⊑ G1' → G2 ⊑ G2' → (G1 Uₜ G2)%ITR ⊑ (G1' Uₜ G2')%ITR.
  Proof.
    intros H1 H2 H τ. iIntros "HU". iApply (itrProp_until_mono_i with "[] [] HU").
    - iNext. iIntros "!>" (τ') "H". iApply (H1 H τ' with "H").
    - iNext. iIntros "!>" (τ') "H". iApply (H2 H τ' with "H").
  Qed.

End itrProp_le_rules.

(** ** Complete and instant antecedents *)
Section itrProp_impl_rules.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A H : itrProp Λ Σ.

  Lemma itrProp_impl_intro A H G `{HA : !ItrPropComplete A} :
    itrProp_le (itrProp_and A H) G → itrProp_le H (itrProp_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /trI_impl. iIntros "H %Hτ". iApply HG.
    rewrite /= /trI_and. iSplit; last done. by iApply HA.
  Qed.

  Lemma itrProp_impl_elim A G `{HA : !ItrPropInstant A} : itrProp_le (itrProp_and A (itrProp_impl A G)) G.
  Proof.
    intros ? τ. rewrite /= /trI_and /trI_impl. iIntros "H".
    iAssert ⌜itrProp_external A τ⌝%I as %Hτ; first by iApply HA; iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ H]". by iApply "H".
  Qed.

End itrProp_impl_rules.

(** ** Casts and external readings *)
Section readings.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G H : itrProp Λ Σ.
  Implicit Types R : trProp Λ.

  Program Definition itrProp_cast G R (pf : itrProp_external G ⊆ R) : itrProp Λ Σ :=
    {| itrProp_internal _ := itrProp_internal G; itrProp_external := R |}.
  Next Obligation. intros G R pf ? F τ Hs. apply pf. by eapply itrProp_adeq. Qed.

  Lemma itrProp_cast_le G R pf : G ⊑ itrProp_cast G R pf.
  Proof. intros ??. done. Qed.
  Lemma itrProp_le_cast G R pf : itrProp_cast G R pf ⊑ G.
  Proof. intros ??. done. Qed.
  Lemma itrProp_cast_ext G R pf : itrProp_external (itrProp_cast G R pf) = R.
  Proof. done. Qed.
  Lemma itrProp_cast_complete G R pf `{!ItrPropComplete G} :
    R ⊆ itrProp_external G → ItrPropComplete (itrProp_cast G R pf).
  Proof. intros HR ? τ Hτ. change (⊢ itrProp_internal G τ). apply itrProp_complete. by apply HR. Qed.

  (** [ItrPropExt G R]: [R] is a trace reading of [G]. The instances follow the connectives;
      the fallback is the reading itself. *)
  Class ItrPropExt G R : Prop := itrProp_ext_of : itrProp_external G ⊆ R.

  Global Instance itrProp_ext_pure φ : ItrPropExt (itrProp_pure φ) (tr_pure φ) | 10.
  Proof. by intros τ. Qed.
  Global Instance itrProp_ext_state φ : ItrPropExt (itrProp_state φ) (tr_state φ) | 10.
  Proof. by intros τ. Qed.
  Global Instance itrProp_ext_and G1 G2 R1 R2 :
    ItrPropExt G1 R1 → ItrPropExt G2 R2 → ItrPropExt (itrProp_and G1 G2) (R1 ∧ R2)%R | 10.
  Proof. intros H1 H2 τ [??]. split; auto. Qed.
  Global Instance itrProp_ext_or G1 G2 R1 R2 :
    ItrPropExt G1 R1 → ItrPropExt G2 R2 → ItrPropExt (itrProp_or G1 G2) (R1 ∨ R2)%R | 10.
  Proof. intros H1 H2 τ [?|?]; [left|right]; auto. Qed.
  Global Instance itrProp_ext_impl A G R :
    ItrPropExt G R → ItrPropExt (itrProp_impl A G) (itrProp_external A → R)%R | 10.
  Proof. intros HG τ HAG HA. by apply HG, HAG. Qed.
  Global Instance itrProp_ext_forall {X} (G : X → itrProp Λ Σ) (R : X → trProp Λ) :
    (∀ x, ItrPropExt (G x) (R x)) → ItrPropExt (itrProp_forall G) (tr_forall X R) | 10.
  Proof. intros HG τ H x. by apply HG. Qed.
  Global Instance itrProp_ext_exist {X} `{!TypeExistentialProperty X ordI} (G : X → itrProp Λ Σ) (R : X → trProp Λ) :
    (∀ x, ItrPropExt (G x) (R x)) → ItrPropExt (itrProp_exist G) (tr_exist X R) | 10.
  Proof. intros HG τ [x H]. exists x. by apply HG. Qed.
  Global Instance itrProp_ext_always G R : ItrPropExt G R → ItrPropExt (itrProp_always G) (□ R)%R | 10.
  Proof. intros HG. by apply tr_always_mono. Qed.
  Global Instance itrProp_ext_finally G R : ItrPropExt G R → ItrPropExt (itrProp_finally G) (◇ R)%R | 9.
  Proof. intros HG. by apply tr_finally_mono. Qed.
  Global Instance itrProp_ext_until G1 G2 R1 R2 :
    ItrPropExt G1 R1 → ItrPropExt G2 R2 → ItrPropExt (itrProp_until G1 G2) (tr_until R1 R2) | 10.
  Proof. intros H1 H2. by apply tr_until_mono. Qed.
  Global Instance itrProp_ext_cast G R pf : ItrPropExt (itrProp_cast G R pf) R | 10.
  Proof. by intros τ. Qed.
  Global Instance itrProp_ext_default G : ItrPropExt G (itrProp_external G) | 100.
  Proof. by intros τ. Qed.

End readings.
Global Hint Mode ItrPropExt - - ! - : typeclass_instances.
Global Arguments itrProp_ext_of {_ _} _ _ {_}.
