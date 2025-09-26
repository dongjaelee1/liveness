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


(** In this file, we define the later elimination update from the paper. The
   definition that is given here is a generalization of the definition shown in
   the paper: instead of defining the update just on natural numbers, we define
   it parametrically over a type and a well-founded relation. The added
   generality allows us to use the later elimination update both with natural
   numbers in standard Iris and to use it with ordinal later credits in
   Transfinite Iris. The more general version is called "relational update"
   in this file.

   This file exists in both the finite Iris and Transfinite Iris development of
   later credits. The only interesting difference is that the file for Transfinite
   Iris, this file, provides more support for proving adequacy when we use relational updates.
*)


(** Relational updates are defined parametrically over:
  - a type [X],
  - a well-frounded relation [rupd_rel_wf: X → X → Prop]
  - a predicate [rupd_pred: X → iProp] *)

Class rupdG `{SI : indexT} (Σ : gFunctors) (X : Type):=
  RelG {
      rupd_pred : X → iProp Σ;
      rupd_rel : relation X;
      rupd_rel_wf : well_founded rupd_rel;
    }.

(**
   The definition of [rupd_pre] is the heart of the relational update.
   It is parameterized over recursive occurences of the update modality. Whenever we
   do a relational update, we get to assume the total credit supply (here
   [rupd_pred]). Next, we get to update the ghost state [|==>], and then we can
   choose between finishing the update or the recursive case. In the recursive
   case, we have to decrease the credit supply (here with [tc rupd_rel x' x])
   and then we can prove the relational update again underneath a later. Proving
   the relational update underneath a later is what allows us to eliminate other
   laters in our context.

   We define the actual relational update [rupd] as the fixpoint of [rupd_pre].
*)

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


(** The following section contains the rules for the later elimination update
   from the paper, but phrased in terms of the more general relational update.
   The actual rules for finite and transfinite later credits are then derived
   later on from these rules. *)
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

  (** This lemma will allow us to spend one credit for a later elimination.
     Since the relational update is defined parametrically over the type X
     and the credit supply, the "spending of a credit" is generalized here. *)
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
    ([∗ list] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_rupd {A} `{Countable K} (Φ : K → A → iProp Σ) l :
    ([∗ map] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_rupd `{Countable A} (Φ : A → iProp Σ) l :
    ([∗ set]  x ∈ l, |==> Φ x) ⊢ |==> [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_rupd `{Countable A} (Φ : A → iProp Σ) l :
    ([∗ mset] x ∈ l, |==> Φ x) ⊢ |==> [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_rupd P : ◇ (|==>r P) ⊢ (|==>r ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using rupd_mono, or_intro_r.
    by rewrite -rupd_intro -or_intro_l.
  Qed.

  (* A safety check that relational updates can replace basic updates *)
  (* We do not use this to build an instance, because it would conflict
     with the basic updates. Instead, we shadow the proofmode lemmas below. *)
  Lemma bi_bupd_mixin_rupd : BiBUpdMixin (iPropI Σ) rupd.
  Proof.
    split.
    - solve_proper.
    - apply rupd_intro.
    - apply rupd_mono.
    - apply rupd_trans.
    - apply rupd_frame_r.
  Qed.

  (* The following instances make the Iris Proof Mode aware of the later
     elimination update. They are derived from the simpler rules above. *)
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


(**
  Below we define some machinery for the adequacy proof of later credits in
  Transfinite Iris. Intuitively, the goal of this machinery is that if we have
  proven |==>r P in Iris, then we can get rid of the relational update to access
  P. That way, we can, for example, access the postcondition of a weakest
  precondition in the adequacy proof.

  In Transfinite Iris, the adequacy proof for the later elimination update
  crucially relies on the existential property: As part of getting rid of |==>r,
  we have to lift the existential quantifier inside of |==>r out of Iris into
  the meta logic. That's exactly what the existential property allows us to do.
 *)

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

  (* FIXME?: need to fix transfinite.bi.satisfiable.v *)
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
