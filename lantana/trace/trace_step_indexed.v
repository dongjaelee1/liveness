From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.program_logic Require Export weakestpre.
From lantana.trace Require Export trace_pred.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.

(** * Step-indexed trace predicates and the ordinal step index

    The in-logic readings of trace properties (trace_prop.v) are built from these: [ti_always]
    and [ti_until] are guarded fixpoints, the until with a decreasing measure. They are
    generic in the step index; [ordSI] then fixes it to the ordinals, at which satisfiability
    of [ti_always] and [ti_until] gives [tr_always] and [tr_until]. *)
Notation tiProp Λ Σ := (trace Λ → iProp Σ).

Definition ti_atomic `{SI : sidx} {Λ} {Σ} (π : state_pred Λ) : tiProp Λ Σ :=
  λ τ, let '((Θ, σ), _, _) := (τ.2 τ.1) in ⌜state_sat σ Θ π⌝%I.

Definition ti_pure `{SI : sidx} {Λ} {Σ} (P : Prop) : tiProp Λ Σ :=
  λ _, ⌜P⌝%I.

Definition ti_and `{SI : sidx} {Λ} {Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, (P τ) ∧ (Q τ))%I.

Definition ti_or `{SI : sidx} {Λ} {Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, (P τ) ∨ (Q τ))%I.

(** The antecedent is a trace property proper: the step-indexed reading of an implication
    assumes the antecedent at the level of traces. *)
Definition ti_impl `{SI : sidx} {Λ} {Σ} : trProp Λ → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, ⌜P τ⌝ → (Q τ))%I.

Definition ti_forall `{SI : sidx} {Λ} {Σ} : ∀ (A : Type), (A → tiProp Λ Σ) → tiProp Λ Σ :=
  λ A P, (λ τ, ∀ (a : A), (P a τ))%I.

Definition ti_exist `{SI : sidx} {Λ} {Σ} : ∀ (A : Type), (A → tiProp Λ Σ) → tiProp Λ Σ :=
  λ A P, (λ τ, ∃ (a : A), (P a τ))%I.

(** 'Always' is a co-inductive fixpoint. *)
Definition ti_always_pre `{SI : sidx} `{!temporalGS Λ Σ} E
  (ti_always : (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  (** Deferred shape: the first fancy update with the later is the check at [τ] (the
      adequacy reads and certifies invariants there), the second with the credits is the
      step; both formulas at [τ] are established after the step, from the certificates. *)
  λ P1 P2 τ, (|={E,∅}=> ▷ |={∅,E}=> |={E,∅}=> ALC (|={∅,E}=>
               ((P1 τ) ∧ (P2 τ) ∧ ti_always P1 P2 (trace_next τ))))%I.

Local Instance ti_always_pre_contractive `{SI : sidx} `{!temporalGS Λ Σ} E : Contractive (ti_always_pre E).
Proof.
  rewrite /ti_always_pre. repeat intro. do 1 (f_equiv). f_contractive. do 4 f_equiv. f_equiv. f_equiv. apply H.
Qed.

Local Definition ti_always_def `{SI : sidx} `{!temporalGS Λ Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  fixpoint (ti_always_pre ⊤).
Local Definition ti_always_aux : seal (@ti_always_def). Proof. by eexists. Qed.
Definition ti_always := ti_always_aux.(unseal).
Global Arguments ti_always {SI Λ Σ _}.
Local Lemma ti_always_unseal `{SI : sidx} `{!temporalGS Λ Σ} : ti_always = @ti_always_def SI Λ Σ _.
Proof. rewrite -ti_always_aux.(seal_eq) //. Qed.

Lemma ti_always_unfold `{SI : sidx} `{!temporalGS Λ Σ} (P1 P2 : tiProp Λ Σ) (τ : trace Λ) :
  ti_always P1 P2 τ ⊣⊢ ti_always_pre ⊤ (ti_always) P1 P2 τ.
Proof. rewrite ti_always_unseal. apply (fixpoint_unfold (ti_always_pre ⊤)). Qed.

(** 'Until' is an inductive fixpoint, decreasing argument of Type A. *)
Definition ti_until_pre `{SI : sidx} `{!temporalGS Λ Σ} E
  {A : Type} (ltA : A → A → Prop)
  (ti_until : A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  (** Deferred shape, as for always: the decision about [τ] is made after the step, and
      the measure for the continuation is chosen then. *)
  λ a P Q τ,
    (|={E,∅}=> ▷ |={∅,E}=> |={E,∅}=> ALC (|={∅,E}=>
       ((Q τ) ∨ ((P τ) ∧ ∃ a', (⌜ltA a' a⌝) ∧ ti_until a' P Q (trace_next τ)))))%I.

Local Instance ti_until_pre_contractive `{SI : sidx} `{!temporalGS Λ Σ} E
  {A : Type} {ltA : A → A → Prop}
  : Contractive (ti_until_pre E ltA).
Proof.
  rewrite /ti_until_pre. repeat intro. do 1 (f_equiv). f_contractive. repeat f_equiv. apply H.
Qed.

Local Definition ti_until_def `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} (ltA : A → A → Prop)
  : A → tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  fixpoint (ti_until_pre ⊤ ltA).
Local Definition ti_until_aux : seal (@ti_until_def). Proof. by eexists. Qed.
Definition ti_until := ti_until_aux.(unseal).
Global Arguments ti_until {SI Λ Σ _ _}.
Local Lemma ti_until_unseal `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} {ltA : A → A → Prop} :
  @ti_until SI Λ Σ _ _ ltA = @ti_until_def SI Λ Σ _ _ ltA.
Proof. rewrite -ti_until_aux.(seal_eq) //. Qed.

Lemma ti_until_unfold `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} {ltA : A → A → Prop}
  (a : A) (P Q : tiProp Λ Σ) (τ : trace Λ) :
  ti_until ltA a P Q τ ⊣⊢ ti_until_pre ⊤ ltA (ti_until ltA) a P Q τ.
Proof. rewrite ti_until_unseal. apply (fixpoint_unfold (ti_until_pre ⊤ ltA)). Qed.

(** ** The ordinal step index *)
Global Instance ordSI : sidx := ordI.

(** This cast using 'change' avoids universe inconsistency. *)
Global Instance iProp_sat_lc_SatisfiableExists {Σ}: SatisfiableExists ordinal_ucmra.OrdUR (@iProp_sat _ Σ).
Proof.
  change (ordinal_ucmra.OrdUR: Type) with Ord.t. apply iProp_sat_exists_instance.
Qed.

(** ** Reading [ti_always] and [ti_until] off a trace *)
Section ti_always_trace.
  Context `{!temporalGS Λ Σ}.
  Context {A : Type} {ltA : A → A → Prop}.
  Implicit Type F : iProp Σ.

  Lemma ti_always_trace_next F P1 P2 τ :
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 τ) →
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 (trace_next τ)).
  Proof.
    intros. rewrite ti_always_unfold /ti_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd, sat_fupd, sat_ALC, sat_fupd in H.
    apply iProp_sat_lc_at_frame_and in H. destruct H as [_ H].
    apply iProp_sat_lc_at_frame_and in H. destruct H as [_ H]. auto.
  Qed.

  Lemma ti_always_trace_later F P1 P2 n x τf :
    n ≤ x →
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 (n, τf)) →
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 (x, τf)).
  Proof.
    intro LE. induction LE; intros; first auto.
    apply IHLE in H. apply ti_always_trace_next in H. done.
  Qed.

  Lemma ti_always_tr_always F (P1 P2 : tiProp Λ Σ) (R1 R2 : trProp Λ) :
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (P1 τ) → R1 τ) →
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (P2 τ) → R2 τ) →
    ∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 τ) → (tr_always (R1 ∧ R2))%R τ.
  Proof.
    intros IH1 IH2 τ H. unfold tr_always. destruct τ as (n&τf).
    (** Use classical logic. *)
    intro m. pattern m. revert m. apply Classical_Pred_Type.not_ex_not_all.
    intros ?. destruct H0. apply Classical_Prop.imply_to_and in H0. destruct H0.
    apply H1. clear H1.
    eapply ti_always_trace_later in H. 2: eauto.
    rewrite ti_always_unfold /ti_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd, sat_fupd, sat_ALC, sat_fupd in H.
    apply iProp_sat_lc_at_frame_and in H. destruct H as [H1 H].
    apply iProp_sat_lc_at_frame_and in H. destruct H as [H2 _].
    split; eauto.
  Qed.

End ti_always_trace.

Lemma ti_until_tr_until_gen `{!temporalGS Λ Σ} F (I1 I2 : tiProp Λ Σ) (R1 R2 : trProp Λ) :
  (∀ τ, iProp_sat_lc_at_frame F ⊤ (I1 τ) → R1 τ) →
  (∀ τ, iProp_sat_lc_at_frame F ⊤ (I2 τ) → R2 τ) →
  ∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_exist Ord.t (λ a, ti_until Ord.lt a I1 I2) τ) →
       tr_until R1 R2 τ.
Proof.
  intros IH1 IH2 τ H. unfold tr_until. destruct τ as (n&τf).
  unfold ti_exist in H. apply sat_exists in H. destruct H as [x H].
  revert n τf H. induction x as [a IHa] using (well_founded_ind Ord.lt_well_founded). intros.
  rewrite ti_until_unfold /ti_until_pre in H.
  apply sat_fupd, sat_later, sat_fupd, sat_fupd, sat_ALC, sat_fupd in H. apply sat_or in H. destruct H as [H|H].
  { apply IH2 in H. exists n. split_and !; eauto. intros. lia. }
  apply iProp_sat_lc_at_frame_and in H. destruct H as [HP H].
  apply sat_exists in H. destruct H as [b H].
  apply iProp_sat_lc_at_frame_and in H. destruct H as [Hlt H]. apply sat_elim in Hlt.
  specialize (IHa _ Hlt _ _ H). simpl in IHa. destruct IHa as (m'& Hm'& Htr& Hp).
  destruct Hm' as [|m Hm'].
  { exists (S n). split_and !; eauto. intros l [Hl1 Hl2]. inversion Hl1; subst; eauto. apply Hp. lia. }
  exists (S m). split_and !; eauto.
  { lia. }
  intros l [Hl1 Hl2]. inversion Hl1; subst; eauto. apply Hp. lia.
Qed.

(** ** In-logic monotonicity *)
Section ti_mono.
  Context {Λ : language} {Σ : gFunctors}.

  (** In-logic monotonicity of always and until: the implication between the readings is
      an iProp hypothesis, available one step later. *)
  Lemma ti_always_mono_i `{!temporalGS Λ Σ} (P1 P1' P2 : tiProp Λ Σ) :
    ▷ □ (∀ τ, P1 τ -∗ P1' τ) -∗ ∀ τ, ti_always P1 P2 τ -∗ ti_always P1' P2 τ.
  Proof.
    iIntros "#W". iLöb as "IH". iIntros (τ) "H". rewrite !ti_always_unfold /ti_always_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first (iDestruct "H" as "[H _]"; by iApply "W").
    iSplit; first by iDestruct "H" as "[_ [$ _]]".
    iDestruct "H" as "[_ [_ H]]". by iApply "IH".
  Qed.
  Lemma ti_until_mono_i `{!temporalGS Λ Σ} (P1 P2 P1' P2' : tiProp Λ Σ) :
    ▷ □ (∀ τ, P1 τ -∗ P1' τ) -∗ ▷ □ (∀ τ, P2 τ -∗ P2' τ) -∗
    ∀ (a : Ord.t) τ, ti_until Ord.lt a P1 P2 τ -∗ ti_until Ord.lt a P1' P2' τ.
  Proof.
    iIntros "#W1 #W2". iLöb as "IH". iIntros (a τ) "H". rewrite !ti_until_unfold /ti_until_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. iDestruct "H" as "[H|H]".
    - iLeft. by iApply "W2".
    - iRight. iSplit; first (iDestruct "H" as "[H _]"; by iApply "W1").
      iDestruct "H" as "[_ (%a'& %Hlt& H)]". iExists a'. iSplit; first done. by iApply "IH".
  Qed.

End ti_mono.
