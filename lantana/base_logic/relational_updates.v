(** From the artifact of
    Later Credits: Resourceful Reasoning for the Later Modality
    by Spies et al. 2022
 *)

From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From transfinite.base_logic.lib Require Import iprop.
Import uPred.

Section aux.

  Lemma rtc_acc {X} (R : X → X → Prop) x y : rtc R y x → Acc R x → Acc R y.
  Proof.
    induction 1; auto. intros Hacc. apply IHrtc; auto.
  Qed.

  Lemma tc_inv_rtc {X} (R : X → X → Prop) x y : tc R x y → ∃ z, rtc R x z ∧ R z y.
  Proof.
    induction 1.
    - exists x; split; by auto.
    - destruct IHtc as [z' [Hr Hrtc]].
      exists z'; split; auto. by econstructor 2.
  Qed.

  Lemma rtc_embed_tc {X} (R : X → X → Prop) x y : rtc R x y → rtc (tc R) x y.
  Proof.
    induction 1; first reflexivity.
    econstructor 2; eauto using tc_once.
  Qed.

  Lemma tc_wf {X} (R : X → X → Prop) : well_founded R → well_founded (tc R).
  Proof.
    intros H x. specialize (H x). induction H as [x H IH].
    constructor. intros y [z [Hrtc Hr]] % tc_inv_rtc.
    eapply rtc_acc; last apply IH; eauto. by eapply rtc_embed_tc.
  Qed.

End aux.


(** This file defines the later elimination update of the Later Credits paper,
   generalized from natural numbers to any type with a well-founded relation, so that
   it works with ordinal later credits in Transfinite Iris. We call the general
   version the relational update [|==>r]. The end of the file supports adequacy
   proofs that use relational updates. *)


(** Relational updates are parametric in:
  - a type [X],
  - a well-founded relation [rupd_rel : X → X → Prop],
  - a predicate [rupd_pred : X → iProp], the total credit supply. *)

Class rupdG `{SI : indexT} (Σ : gFunctors) (X : Type) :=
  RelG {
      rupd_pred : X → iProp Σ;
      rupd_rel : relation X;
      rupd_rel_wf : well_founded rupd_rel;
    }.

(** [rupd_pre] is the heart of the relational update, and [rupd] is its fixpoint. A
   relational update receives the total credit supply [rupd_pred x], updates the ghost
   state ([|==>]), and then either finishes, or decreases the supply
   ([tc rupd_rel x' x]) and continues with a relational update under a later.
   Continuing under a later is what lets us eliminate laters in the context. *)

Definition rupd_pre `{SI : indexT} {Σ : gFunctors} {X} `{!rupdG Σ X} (rupd : iPropO Σ -d> iPropO Σ) :
  iProp Σ -d> iPropO Σ :=
  λ P, (∀ x : X, rupd_pred x -∗
        |==> ((rupd_pred x ∗ P) ∨
                (∃ x' : X, ⌜tc rupd_rel x' x⌝ ∗ rupd_pred x' ∗ ▷ rupd P)))%I.

Local Instance rupd_pre_contractive `{SI : indexT} {Σ: gFunctors} {X} `{!rupdG Σ X} : Contractive rupd_pre.
Proof.
  rewrite /rupd_pre=> n rupd rupd' Hrupd P.
  do 9 f_equiv. f_contractive. apply Hrupd.
Qed.
Definition rupd_def `{SI : indexT} {Σ : gFunctors} {X} `{!rupdG Σ X} :
  iProp Σ -d> iPropO Σ := fixpoint rupd_pre.
Definition rupd_aux : seal (@rupd_def). Proof. by eexists. Qed.
Definition rupd := rupd_aux.(unseal).
Arguments rupd {SI Σ X rupdG} P : rename.
Local Definition rupd_eq : @rupd = @rupd_def := rupd_aux.(seal_eq).
Notation "'|==>r' P" := (rupd P) (at level 99, P at level 200, format "|==>r  P").

Lemma rupd_unfold `{SI : indexT} {Σ: gFunctors} {X} `{!rupdG Σ X} P :
  (|==>r P) ⊣⊢
  ∀ x : X, rupd_pred x -∗ |==> (rupd_pred x ∗ P) ∨ (∃ x' : X, ⌜tc rupd_rel x' x⌝ ∗ rupd_pred x' ∗ ▷ rupd P).
Proof.
  by rewrite rupd_eq /rupd_def {1}(fixpoint_unfold rupd_pre P) {1}/rupd_pre.
Qed.


(** Rules of the relational update. The rules for transfinite later credits in
   [later_credits.v] are derived from them. *)
Section rupd_lemmas.
  Context `{SI : indexT} {Σ : gFunctors} {X} `{rG : !rupdG Σ X}.
  Implicit Types (P Q : iProp Σ).

  Global Instance rupd_ne : NonExpansive rupd.
  Proof.
    intros n P Q Heq; induction (index_lt_wf n) as [n _ IH].
    rewrite (rupd_unfold P) (rupd_unfold Q).
    do 6 f_equiv.
    - done.
    - do 3 f_equiv. f_contractive. eapply IH, dist_le; eauto.
      eapply index_lt_le_subrel; auto.
  Qed.

  (** A standard update can be turned into a relational update. *)
  Lemma bupd_rupd P : (|==> P) ⊢ (|==>r P).
  Proof.
    rewrite rupd_unfold; iIntros "Hupd" (x) "Hpr".
    iMod "Hupd" as "P". iModIntro. iLeft. by iFrame.
  Qed.

  (** We can always introduce a relational update. *)
  Lemma rupd_intro P : P ⊢ |==>r P.
  Proof.
    rewrite rupd_unfold.
    iIntros "P" (x) "Hpr"; iModIntro.
    iLeft; by iFrame.
  Qed.

  (** We can combine two relational updates into one. *)
  Lemma rupd_bind P Q :
    (P -∗ |==>r Q) ⊢ (|==>r P) -∗ (|==>r Q).
  Proof.
    iLöb as "IH". iIntros "PQ".
    rewrite {2}(rupd_unfold P) {4}(rupd_unfold Q).
    iIntros  "Hupd" (x) "Hpr". iMod ("Hupd" with "Hpr") as "[Hupd|Hupd]".
    - (* base case for the update around P *)
      iDestruct "Hupd" as "[Hpr Hupd]".
      iSpecialize ("PQ" with "Hupd").
      rewrite {3}(rupd_unfold Q).
      iMod ("PQ" with "Hpr") as "[Hupd|Hupd]".
      + iModIntro. by iLeft.
      + iModIntro. iRight. iDestruct "Hupd" as  (x'' Hstep'') "[Hpr Hupd]".
        iExists _; iFrame. iPureIntro.
        by eapply tc_rtc_r.
    - iModIntro. iRight. iDestruct "Hupd" as (x') "(Hstep & Hpr & Hupd)".
      iExists _; iFrame. iNext. by iApply ("IH" with "PQ Hupd").
  Qed.

  (** Spending credits to eliminate a later. Spending means decreasing the credit
     supply along [rupd_rel]. *)
  Lemma rupd_step P :
    (∀ x, rupd_pred x -∗ |==> ∃ y, ⌜tc rupd_rel y x⌝ ∗ rupd_pred y ∗ ▷ |==>r P) ⊢ |==>r P.
  Proof.
    rewrite {2}(rupd_unfold P).
    iIntros "Hupd" (x) "Hpr". iRight. by iMod ("Hupd" with "Hpr") as "$".
  Qed.

  (* derived lemmas *)
  Lemma rupd_mono P Q : (P ⊢ Q) → (|==>r P) ⊢ (|==>r Q).
  Proof.
    intros Hent. iApply rupd_bind.
    iIntros "P"; iApply rupd_intro; by iApply Hent.
  Qed.
  Lemma rupd_trans P :  (|==>r |==>r P) ⊢ |==>r P.
  Proof.
    iIntros "HP". iApply rupd_bind; eauto.
  Qed.
  Lemma rupd_frame_r P R : (|==>r P) ∗ R ⊢ |==>r P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (rupd_bind with "[R]"); last done.
    iIntros "P". iApply rupd_intro. by iFrame.
  Qed.

  Global Instance rupd_ent_proper : Proper ((⊢) ==> (⊢)) rupd.
  Proof. intros P Q PQ. by apply rupd_mono. Qed.
  Global Instance rupd_flip_ent_proper : Proper (flip (⊢) ==> flip (⊢)) rupd.
  Proof. intros P Q PQ; by apply rupd_mono. Qed.
  Global Instance rupd_equiv_proper : Proper ((≡) ==> (≡)) rupd := ne_proper _.

  Lemma rupd_bupd_l P :
    (|==> |==>r P) ⊢ (|==>r P).
  Proof.
    by rewrite bupd_rupd rupd_trans.
  Qed.
  Lemma rupd_bupd_r P :
    (|==>r |==> P) ⊢ (|==>r P).
  Proof.
    by rewrite bupd_rupd rupd_trans.
  Qed.

  Lemma rupd_frame_l R Q : (R ∗ |==>r Q) ⊢ |==>r R ∗ Q.
  Proof. rewrite !(comm _ R); apply rupd_frame_r. Qed.
  Lemma rupd_wand_l P Q : (P -∗ Q) ∗ (|==>r P) ⊢ |==>r Q.
  Proof. by rewrite rupd_frame_l wand_elim_l. Qed.
  Lemma rupd_wand_r P Q : (|==>r P) ∗ (P -∗ Q) ⊢ |==>r Q.
  Proof. by rewrite rupd_frame_r wand_elim_r. Qed.
  Lemma rupd_sep P Q : (|==>r P) ∗ (|==>r Q) ⊢ |==>r P ∗ Q.
  Proof. by rewrite rupd_frame_r rupd_frame_l rupd_trans. Qed.
  Lemma rupd_idemp P : (|==>r |==>r P) ⊣⊢ |==>r P.
  Proof.
    apply: anti_symm.
    - apply rupd_trans.
    - apply rupd_intro.
  Qed.

  Global Instance rupd_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (rupd).
  Proof. split; [split|]; try apply _; [apply rupd_sep | apply rupd_intro]. Qed.

  Lemma big_sepL_rupd {A} (Φ : nat → A → iProp Σ) l :
    ([∗ list] k↦x ∈ l, |==>r Φ k x) ⊢ |==>r [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_rupd {A} `{Countable K} (Φ : K → A → iProp Σ) l :
    ([∗ map] k↦x ∈ l, |==>r Φ k x) ⊢ |==>r [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_rupd `{Countable A} (Φ : A → iProp Σ) l :
    ([∗ set]  x ∈ l, |==>r Φ x) ⊢ |==>r [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_rupd `{Countable A} (Φ : A → iProp Σ) l :
    ([∗ mset] x ∈ l, |==>r Φ x) ⊢ |==>r [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_rupd P : ◇ (|==>r P) ⊢ (|==>r ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using rupd_mono, or_intro_r.
    by rewrite -rupd_intro -or_intro_l.
  Qed.

  (* A sanity check: relational updates satisfy the laws of basic updates. This is not
     an instance, since it would conflict with the basic update; the proof mode
     instances below are used instead. *)
  Lemma bi_bupd_mixin_rupd : BiBUpdMixin (iPropI Σ) rupd.
  Proof.
    split.
    - solve_proper.
    - apply rupd_intro.
    - apply rupd_mono.
    - apply rupd_trans.
    - apply rupd_frame_r.
  Qed.

  (* The following instances make the Iris Proof Mode aware of the relational
     update. They are derived from the simpler rules above. *)
  Global Instance elim_bupd_rupd (p : bool) P Q :
    ElimModal True p false (|==> P) P (|==>r Q) (|==>r Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    rewrite bupd_rupd.
    iIntros "_ [HP HPQ]". iApply (rupd_bind with "HPQ HP").
  Qed.

  Global Instance add_modal_bupd P Q :
    AddModal (|==> P) P (|==>r Q).
  Proof.
    rewrite /AddModal; rewrite bupd_rupd; iIntros "[HP HPQ]".
    iApply (rupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_rupd p P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|==>r Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply rupd_intro. Qed.

  Global Instance from_pure_rupd a P φ :
    FromPure a P φ → FromPure a (|==>r P) φ.
  Proof. rewrite /FromPure=> <-. apply rupd_intro. Qed.

  Global Instance into_wand_rupd p q R P Q :
    IntoWand false false R P Q → IntoWand p q (|==>r R) (|==>r P) (|==>r Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite rupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_rupd_persistent p q R P Q :
    IntoWand false q R P Q → IntoWand p q (|==>r R) P (|==>r Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite rupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_rupd_args p q R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|==>r P) (|==>r Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim rupd_wand_r.
  Qed.

  Global Instance from_sep_rupd P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|==>r P) (|==>r Q1) (|==>r Q2).
  Proof. rewrite /FromSep=><-. apply rupd_sep. Qed.

  Global Instance from_or_rupd P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|==>r P) (|==>r Q1) (|==>r Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply rupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_rupd {A} P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|==>r P) (λ a, |==>r Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_rupd P : IsExcept0 P → IsExcept0 (|==>r P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_rupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_rupd P :
    FromModal True modality_id (|==>r P) (|==>r P) P.
  Proof. by rewrite /FromModal /= -rupd_intro. Qed.

  Global Instance elim_modal_rupd p P Q :
    ElimModal True p false (|==>r P) P (|==>r Q) (|==>r Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim rupd_frame_r wand_elim_r rupd_trans.
  Qed.

  Global Instance add_modal_rupd P Q : AddModal (|==>r P) P (|==>r Q).
  Proof. by rewrite /AddModal rupd_frame_r wand_elim_r rupd_trans. Qed.

  Global Instance frame_rupd p R P Q :
    Frame p R P Q → Frame p R (|==>r P) (|==>r Q).
  Proof. rewrite /Frame=><-. by rewrite rupd_frame_l. Qed.

End rupd_lemmas.


(** Support for adequacy proofs: from [|==>r P] we can remove the relational update
  and access [P], e.g., the postcondition of a weakest precondition. This relies on
  the existential property of Transfinite Iris, which lifts the existential
  quantifier inside [|==>r] out of Iris into the meta logic. *)

Class SatisfiableRUpd `{SI : indexT} {X : Type} {Σ : gFunctors} `{!rupdG Σ X} (sat : iProp Σ → Prop) := {
    sat_rupd P : sat (|==>r P) → sat P
  }.

Class SatisfiableRUpdUpdate `{SI : indexT} {X: Type} {Σ : gFunctors} `{!rupdG Σ X} (sat : iProp Σ → Prop) := {
    sat_pred_upd P Q :
    (∀ x, rupd_pred x -∗ |==> ∃ y, rupd_pred y ∗ Q) →
    sat P →
    sat (P ∗ Q)%I
  }.

Section rupd_satisfiable.
  Context `{SI : indexT} {X : Type} {Σ : gFunctors} `{!rupdG Σ X}.
  Context (sat : iProp Σ → Prop) `{S : !Satisfiable sat} `{SL : !SatisfiableLater sat}.
  Context `{SU : !SatisfiableBUpd sat}.
  Context `{SE1 : !SatisfiableExists X sat} `{SE2 : !SatisfiableExists bool sat}.

  Lemma rupd_satisfiable P x : sat (rupd_pred x ∗ |==>r P)%I → ∃ x', rtc rupd_rel x' x ∧ sat (rupd_pred x' ∗ P).
  Proof using sat S SL SU SE1 SE2.
    induction (tc_wf _ rupd_rel_wf x) as [x _ IH].
    rewrite rupd_unfold.
    intros Hsat. eapply sat_mono
      with (Q := (|==> ∃ x' : X, (⌜rtc rupd_rel x' x⌝ ∗ rupd_pred x' ∗ P) ∨ ▷ (⌜tc rupd_rel x' x⌝ ∗ rupd_pred x' ∗ |==>r P))%I) in Hsat; last first.
    - iIntros "[Hpr Hupd]". iMod ("Hupd" with "Hpr") as "[Hupd|Hupd]".
      + iModIntro. iExists x. iLeft. iDestruct "Hupd" as "[$ $]". by iPureIntro.
      + iModIntro. iDestruct "Hupd" as (x') "H". iExists _. iRight.
        iDestruct "H" as "($ & $ & $)".
    - apply sat_bupd in Hsat.
      eapply sat_exists in Hsat as [x' Hsat].
      eapply sat_or in Hsat as [Hsat|Hsat].
      + eapply sat_sep in Hsat as [Hrtc % sat_elim Hsat]; eauto.
      + eapply sat_later in Hsat.
        eapply sat_sep in Hsat as [Htc % sat_elim Hsat].
        edestruct (IH x') as [x'' [Hrtc Hsat']]; [done..|].
        exists x''; split; eauto.
        etrans; eauto using tc_rtc.
  Qed.

  (* Satisfiability framed with some credit supply. *)
  Definition sat_lc := sat_frame (sat:=sat) (∃ x : X, rupd_pred x)%I.

  Global Instance sat_lc_satisfiable_rupd : SatisfiableRUpd sat_lc.
  Proof using SU SL SE2 SE1 S.
    econstructor. intros P; rewrite /sat_lc /sat_frame.
    intros Hsat. eapply sat_mono with (Q:= (∃ x: X, rupd_pred x ∗ |==>r P)%I) in Hsat; last by iIntros "[? $]".
    eapply sat_exists in Hsat as [x Hsat].
    eapply rupd_satisfiable in Hsat as [x' [_ Hsat]].
    eapply sat_mono, Hsat. iIntros "[? $]"; by iExists _.
  Qed.

  Global Instance sat_lc_satisfiable_rupd_update : SatisfiableRUpdUpdate sat_lc.
  Proof using SU SL SE2 SE1 S.
    econstructor. intros P Q; rewrite /sat_lc /sat_frame.
    intros Hupd Hsat. eapply sat_bupd, sat_mono, Hsat.
    iIntros "(Hpr & P)". iDestruct "Hpr" as (x) "Hpr".
    iMod (Hupd with "Hpr") as (y) "[Hpr $]".
    iModIntro. iFrame "P". by iExists _.
  Qed.

  Global Instance sat_frame_rupd `{!SatisfiableRUpd sat} F : SatisfiableRUpd (@sat_frame _ _ sat F).
  Proof using S.
    rewrite /sat_frame.
    econstructor. intros P Hsat. eapply sat_rupd, sat_mono, Hsat; by rewrite rupd_frame_l.
  Qed.

  Global Instance sat_frame_rupd_update `{!SatisfiableRUpdUpdate sat} F : SatisfiableRUpdUpdate (@sat_frame _ _ sat F).
  Proof using S.
    rewrite /sat_frame.
    econstructor. intros P Q Hup Hsat. rewrite sep_assoc. by eapply sat_pred_upd.
  Qed.

End rupd_satisfiable.
