From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.program_logic Require Export weakestpre.
From lantana.trace Require Export trace_prop.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.

(** * Step-indexed trace predicates and the ordinal step index

    [trI_always] and [trI_until] (with a decreasing measure) are guarded fixpoints, generic in
    the step index. At the ordinals ([ordSI]) their satisfiability gives [tr_always] and
    [tr_until]. *)
Notation trIProp Λ Σ := (trace Λ → iProp Σ).

Definition trI_pure `{SI : sidx} {Λ} {Σ} (P : Prop) : trIProp Λ Σ :=
  λ _, ⌜P⌝%I.

Definition trI_and `{SI : sidx} {Λ} {Σ} : trIProp Λ Σ → trIProp Λ Σ → trIProp Λ Σ :=
  λ P Q, (λ τ, (P τ) ∧ (Q τ))%I.

Definition trI_or `{SI : sidx} {Λ} {Σ} : trIProp Λ Σ → trIProp Λ Σ → trIProp Λ Σ :=
  λ P Q, (λ τ, (P τ) ∨ (Q τ))%I.

(** The antecedent is a trace property: it is assumed at the level of traces. *)
Definition trI_impl `{SI : sidx} {Λ} {Σ} : trProp Λ → trIProp Λ Σ → trIProp Λ Σ :=
  λ P Q, (λ τ, ⌜P τ⌝ → (Q τ))%I.

Definition trI_forall `{SI : sidx} {Λ} {Σ} : ∀ (A : Type), (A → trIProp Λ Σ) → trIProp Λ Σ :=
  λ A P, (λ τ, ∀ (a : A), (P a τ))%I.

Definition trI_exist `{SI : sidx} {Λ} {Σ} : ∀ (A : Type), (A → trIProp Λ Σ) → trIProp Λ Σ :=
  λ A P, (λ τ, ∃ (a : A), (P a τ))%I.

Definition trI_always_pre `{SI : sidx} `{!temporalGS Λ Σ} E
  (trI_always : (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  (** Deferred shape: the first update (with the later) is the check at [τ], where the
      adequacy certifies the invariants; the second (with the credits) is the step. The
      formulas at [τ] are established after the step, from the certificates. *)
  λ P1 P2 τ, (|={E,∅}=> ▷ |={∅,E}=> |={E,∅}=> ALC (|={∅,E}=>
               ((P1 τ) ∧ (P2 τ) ∧ trI_always P1 P2 (trace_next τ))))%I.

Local Instance trI_always_pre_contractive `{SI : sidx} `{!temporalGS Λ Σ} E : Contractive (trI_always_pre E).
Proof.
  rewrite /trI_always_pre. repeat intro. do 1 (f_equiv). f_contractive. do 4 f_equiv. f_equiv. f_equiv. apply H.
Qed.

Local Definition trI_always_def `{SI : sidx} `{!temporalGS Λ Σ} : trIProp Λ Σ → trIProp Λ Σ → trIProp Λ Σ :=
  fixpoint (trI_always_pre ⊤).
Local Definition trI_always_aux : seal (@trI_always_def). Proof. by eexists. Qed.
Definition trI_always := trI_always_aux.(unseal).
Global Arguments trI_always {SI Λ Σ _}.
Local Lemma trI_always_unseal `{SI : sidx} `{!temporalGS Λ Σ} : trI_always = @trI_always_def SI Λ Σ _.
Proof. rewrite -trI_always_aux.(seal_eq) //. Qed.

Lemma trI_always_unfold `{SI : sidx} `{!temporalGS Λ Σ} (P1 P2 : trIProp Λ Σ) (τ : trace Λ) :
  trI_always P1 P2 τ ⊣⊢ trI_always_pre ⊤ (trI_always) P1 P2 τ.
Proof. rewrite trI_always_unseal. apply (fixpoint_unfold (trI_always_pre ⊤)). Qed.

Definition trI_until_pre `{SI : sidx} `{!temporalGS Λ Σ} E
  {A : Type} (ltA : A → A → Prop)
  (trI_until : A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  (** Deferred shape, as for always: [τ] and the measure of the continuation are decided
      after the step. *)
  λ a P Q τ,
    (|={E,∅}=> ▷ |={∅,E}=> |={E,∅}=> ALC (|={∅,E}=>
       ((Q τ) ∨ ((P τ) ∧ ∃ a', (⌜ltA a' a⌝) ∧ trI_until a' P Q (trace_next τ)))))%I.

Local Instance trI_until_pre_contractive `{SI : sidx} `{!temporalGS Λ Σ} E
  {A : Type} {ltA : A → A → Prop}
  : Contractive (trI_until_pre E ltA).
Proof.
  rewrite /trI_until_pre. repeat intro. do 1 (f_equiv). f_contractive. repeat f_equiv. apply H.
Qed.

Local Definition trI_until_def `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} (ltA : A → A → Prop)
  : A → trIProp Λ Σ → trIProp Λ Σ → trIProp Λ Σ :=
  fixpoint (trI_until_pre ⊤ ltA).
Local Definition trI_until_aux : seal (@trI_until_def). Proof. by eexists. Qed.
Definition trI_until := trI_until_aux.(unseal).
Global Arguments trI_until {SI Λ Σ _ _}.
Local Lemma trI_until_unseal `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} {ltA : A → A → Prop} :
  @trI_until SI Λ Σ _ _ ltA = @trI_until_def SI Λ Σ _ _ ltA.
Proof. rewrite -trI_until_aux.(seal_eq) //. Qed.

Lemma trI_until_unfold `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} {ltA : A → A → Prop}
  (a : A) (P Q : trIProp Λ Σ) (τ : trace Λ) :
  trI_until ltA a P Q τ ⊣⊢ trI_until_pre ⊤ ltA (trI_until ltA) a P Q τ.
Proof. rewrite trI_until_unseal. apply (fixpoint_unfold (trI_until_pre ⊤ ltA)). Qed.

(** ** The ordinal step index *)
Global Instance ordSI : sidx := ordI.

(** This cast using 'change' avoids universe inconsistency. *)
Global Instance iProp_sat_lc_SatisfiableExists {Σ}: SatisfiableExists ordinal_ucmra.OrdUR (@iProp_sat _ Σ).
Proof.
  change (ordinal_ucmra.OrdUR: Type) with Ord.t. apply iProp_sat_exists_instance.
Qed.

(** ** Reading [trI_always] and [trI_until] off a trace *)
Section trI_always_trace.
  Context `{!temporalGS Λ Σ}.
  Context {A : Type} {ltA : A → A → Prop}.
  Implicit Type F : iProp Σ.

  Lemma trI_always_trace_next F P1 P2 τ :
    iProp_sat_lc_at_frame F ⊤ (trI_always P1 P2 τ) →
    iProp_sat_lc_at_frame F ⊤ (trI_always P1 P2 (trace_next τ)).
  Proof.
    intros. rewrite trI_always_unfold /trI_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd, sat_fupd, sat_ALC, sat_fupd in H.
    apply iProp_sat_lc_at_frame_and in H. destruct H as [_ H].
    apply iProp_sat_lc_at_frame_and in H. destruct H as [_ H]. auto.
  Qed.

  Lemma trI_always_trace_later F P1 P2 n x τf :
    n ≤ x →
    iProp_sat_lc_at_frame F ⊤ (trI_always P1 P2 (n, τf)) →
    iProp_sat_lc_at_frame F ⊤ (trI_always P1 P2 (x, τf)).
  Proof.
    intro LE. induction LE; intros; first auto.
    apply IHLE in H. apply trI_always_trace_next in H. done.
  Qed.

  Lemma trI_always_tr_always F (P1 P2 : trIProp Λ Σ) (R1 R2 : trProp Λ) :
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (P1 τ) → R1 τ) →
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (P2 τ) → R2 τ) →
    ∀ τ, iProp_sat_lc_at_frame F ⊤ (trI_always P1 P2 τ) → (tr_always (R1 ∧ R2))%R τ.
  Proof.
    intros IH1 IH2 τ H. unfold tr_always. destruct τ as (n&τf).
    (** Use classical logic. *)
    intro m. pattern m. revert m. apply Classical_Pred_Type.not_ex_not_all.
    intros ?. destruct H0. apply Classical_Prop.imply_to_and in H0. destruct H0.
    apply H1. clear H1.
    eapply trI_always_trace_later in H. 2: eauto.
    rewrite trI_always_unfold /trI_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd, sat_fupd, sat_ALC, sat_fupd in H.
    apply iProp_sat_lc_at_frame_and in H. destruct H as [H1 H].
    apply iProp_sat_lc_at_frame_and in H. destruct H as [H2 _].
    split; eauto.
  Qed.

End trI_always_trace.

Lemma trI_until_tr_until_gen `{!temporalGS Λ Σ} F (I1 I2 : trIProp Λ Σ) (R1 R2 : trProp Λ) :
  (∀ τ, iProp_sat_lc_at_frame F ⊤ (I1 τ) → R1 τ) →
  (∀ τ, iProp_sat_lc_at_frame F ⊤ (I2 τ) → R2 τ) →
  ∀ τ, iProp_sat_lc_at_frame F ⊤ (trI_exist Ord.t (λ a, trI_until Ord.lt a I1 I2) τ) →
       tr_until R1 R2 τ.
Proof.
  intros IH1 IH2 τ H. unfold tr_until. destruct τ as (n&τf).
  unfold trI_exist in H. apply sat_exists in H. destruct H as [x H].
  revert n τf H. induction x as [a IHa] using (well_founded_ind Ord.lt_well_founded). intros.
  rewrite trI_until_unfold /trI_until_pre in H.
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
Section trI_mono.
  Context {Λ : language} {Σ : gFunctors}.

  (** The implication between the readings is an iProp hypothesis, available one step later. *)
  Lemma trI_always_mono_i `{!temporalGS Λ Σ} (P1 P1' P2 : trIProp Λ Σ) :
    ▷ □ (∀ τ, P1 τ -∗ P1' τ) -∗ ∀ τ, trI_always P1 P2 τ -∗ trI_always P1' P2 τ.
  Proof.
    iIntros "#W". iLöb as "IH". iIntros (τ) "H". rewrite !trI_always_unfold /trI_always_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first (iDestruct "H" as "[H _]"; by iApply "W").
    iSplit; first by iDestruct "H" as "[_ [$ _]]".
    iDestruct "H" as "[_ [_ H]]". by iApply "IH".
  Qed.
  Lemma trI_until_mono_i `{!temporalGS Λ Σ} (P1 P2 P1' P2' : trIProp Λ Σ) :
    ▷ □ (∀ τ, P1 τ -∗ P1' τ) -∗ ▷ □ (∀ τ, P2 τ -∗ P2' τ) -∗
    ∀ (a : Ord.t) τ, trI_until Ord.lt a P1 P2 τ -∗ trI_until Ord.lt a P1' P2' τ.
  Proof.
    iIntros "#W1 #W2". iLöb as "IH". iIntros (a τ) "H". rewrite !trI_until_unfold /trI_until_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. iDestruct "H" as "[H|H]".
    - iLeft. by iApply "W2".
    - iRight. iSplit; first (iDestruct "H" as "[H _]"; by iApply "W1").
      iDestruct "H" as "[_ (%a'& %Hlt& H)]". iExists a'. iSplit; first done. by iApply "IH".
  Qed.

End trI_mono.
