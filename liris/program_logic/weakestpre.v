From iris.proofmode Require Import base proofmode classes.
From liris Require Export language.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export fixpoint.
From liris.bi Require Export weakestpre.
From iris.prelude Require Import options.
From liris.base_logic Require Export fancy_updates.
From liris.base_logic Require Export osat othread owitness.
(* From liris.base_logic Require Export otree fancy_updates. *)
From liris.algebra Require Import ordinal_wfocm.
Import uPred.

Section curry5.
  Definition curry5 {A B C D E F : Type} (f : A * B * C * D * E → F) (a : A) (b : B) (c : C) (d : D) (e : E) : F :=
    f (a, b, c, d, e).
  Definition uncurry5 {A B C D E F : Type} (f : A → B → C → D → E → F) : (A * B * C * D * E) → F :=
    λ '(a, b, c, d, e), f a b c d e.

  Lemma curry5_uncurry5 : ∀ {A B C D E F : Type} (f : A → B → C → D → E → F), curry5 (uncurry5 f) = f.
  Proof. done. Qed.
  Lemma uncurry5_curry5 : ∀ {A B C D E F : Type} (f : A * B * C * D * E → F) (p : A * B * C * D * E), uncurry5 (curry5 f) p = f p.
  Proof. intros. destruct p as [[[[a b] c] d] e]. done. Qed.

  Global Instance uncurry5_proper' : ∀ {A : Type} {RA : relation A} {B : Type} {RB : relation B} {C : Type} {RC : relation C} {D : Type} {RD : relation D} {E : Type} {RE : relation E} {F : Type} {RF : relation F},
    Proper
      ((RA ==> RB ==> RC ==> RD ==> RE ==> RF) ==>
         prod_relation (prod_relation (prod_relation (prod_relation RA RB) RC) RD) RE ==> RF)
      (@uncurry5 A B C D E F).
  Proof.
    intros. repeat intro.
    destruct x0 as [[[[a0 b0] c0] d0] e0], y0 as [[[[a1 b1] c1] d1] e1].
    simpl. destruct H0 as [[[[? ?] ?] ?] ?]. simpl in *. by eapply H.
  Qed.
  Global Instance uncurry5_proper : ∀ {A : Type} {H : Equiv A} {B : Type} {H0 : Equiv B} {C : Type} {H1 : Equiv C} {D : Type} {H2 : Equiv D} {E : Type} {H3 : Equiv E} {F : Type} {H4 : Equiv F},
    Proper ((equiv ==> equiv ==> equiv ==> equiv ==> equiv ==> equiv) ==> equiv ==> equiv) (@uncurry5 A B C D E F).
  Proof. intros. eapply uncurry5_proper'. Qed.

  Global Instance uncurry5_ne : ∀ {SI : indexT} {A B C D E F : ofe} (n : index),
    Proper ((dist n ==> dist n ==> dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n) (@uncurry5 A B C D E F).
  Proof. intros. apply uncurry5_proper. Qed.
End curry5.

Global Instance wp_obl_live_class : obl_live_class Ord.t thread_id Ord.lt.
Proof. econstructor; try apply _. apply Ord.lt_well_founded. Qed.
Global Instance wp_obl_done_class {Λ : language} : obl_done_class (state Λ).
Proof. econstructor. done. Qed.
Global Instance wp_wit_live_class : wit_live_class Ord.t Ord.lt.
Proof. econstructor; try apply _. apply Ord.lt_well_founded. Qed.

Class lirisGS `{SI : indexT} (Λ : language) (Σ : gFunctors) := LirisG {
  (** Invariants. *)
  #[global] liris_invGS :: invGS Σ;
  (** Liveness obligations. *)
  #[global] liris_osatGS :: osatGS.osatGS (WF:=ord_wfocm_pack) (state Λ) thread_id Σ;
  (** Liveness obligations assigned to threads. *)
  #[global] liris_othreadGS :: othreadGS.othreadGS Σ;
  (** Liveness witnesses. *)
  #[global] liris_owitnessGS :: owitnessGS.owitnessGS (WF:=ord_wfocm_pack) Σ;
  (** Witness function. *)
  owfun : Ord.t → Ord.t;
  (* (** Forest of liveness obligation. *) *)
  (* #[global] liris_otreeGS :: otreeGS.otreeGS Ord.t Σ; *)

  (** The state interpretation is an invariant that should hold in
  between each step of reduction.
  Here [state] is the global state, [thread_ids] is the allocated thread ids,
  and [list (observation Λ)] are the remaining observations. *)
  state_interp : state Λ → thread_ids → list (observation Λ) → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
 fork_post : thread_id → val Λ → iProp Σ;
}.

Global Opaque liris_invGS liris_osatGS liris_othreadGS liris_owitnessGS.
Global Arguments LirisG {SI Λ Σ}.

Definition oproto `{SI : indexT} `{!lirisGS Λ Σ} (Ω : obl_states) (W : wit_states) (Θ : thread_ids) : iProp Σ :=
  (osat Ω ∗ othread Θ ∗ oassigned (dom Ω) ∗ owitness W ∗ ⌜ obl_wit owfun Ω W ⌝)%I.

(** Modality for updating obligation states. *)
(* Can allocate, progress, or fulfill obligations, no later modality. *)
Definition oupd_pre `{SI : indexT} `{!lirisGS Λ Σ} (E : coPset)
  (oupd : iPropO Σ -d> iPropO Σ) : iProp Σ -d> iPropO Σ :=
  λ P,
    (P ∨
       (∀ (Ω1 : obl_states) (W1 : wit_states) (Θ : thread_ids) σ κs,
          (oproto Ω1 W1 Θ ∗ state_interp σ Θ κs) ={E}=∗
          ∃ Ω2, (⌜(Ω1 ↪ₛ⋆ Ω2 @ σ)⌝) ∗
          ∀ W2, (⌜(W1 ↓ₛ⋆ W2) ∧ obl_wit owfun Ω2 W2 ⌝) -∗
          (oproto Ω2 W2 Θ ∗ state_interp σ Θ κs) ∗ oupd P))%I.

Lemma oupd_pre_mono `{SI : indexT} `{!lirisGS Λ Σ} E
  (oupd1 oupd2 : iPropO Σ -d> iPropO Σ) :
  ⊢ ((□ ∀ P, oupd1 P -∗ oupd2 P) →
     ∀ P, oupd_pre E oupd1 P -∗ oupd_pre E oupd2 P)%I.
Proof.
  iIntros "#Hmono"; iIntros (P) "Houpd". rewrite /oupd_pre.
  iDestruct "Houpd" as "[H | Houpd]".
  { iLeft. done. }
  iRight. iIntros (?????) "I". iMod ("Houpd" with "[$I]") as "(%& %& H)".
  iModIntro. iExists _. iSplitR; first done. iIntros (??).
  iPoseProof ("H" with "[//]") as "[$ H]". by iApply "Hmono".
Qed.

Local Instance oupd_pre_mono' `{SI : indexT} `{!lirisGS Λ Σ} E :
  BiMonoPred (oupd_pre E).
Proof.
  constructor.
  - iIntros (oupd1 oupd2 NE1 NE2) "#H". iApply oupd_pre_mono. iModIntro. iApply "H".
  - intros oupd Houpd n P1 P2 ?. rewrite /oupd_pre.
    do 22 (f_equiv || done).
Qed.

(* take the least fixpoint of the above definition, with partial sate information *)
Local Definition oupd_def `{SI : indexT} `{!lirisGS Λ Σ} E : iProp Σ → iProp Σ :=
  λ P, ((bi_least_fixpoint (oupd_pre E)) P)%I.
Local Definition oupd_aux : seal (@oupd_def). by eexists. Qed.
Definition oupd := oupd_aux.(unseal).
Arguments oupd {SI Λ Σ _}.
Local Definition oupd_unseal : @oupd = @oupd_def := oupd_aux.(seal_eq).
Notation "'|={' E '}=>o' P" := (oupd E P) (at level 99, P at level 200, format "|={ E }=>o  P").

Section oupd.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.

  Lemma oupd_unfold E P :
    (|={E}=>o P) ⊣⊢ (oupd_pre E (oupd E) P).
  Proof.
    rewrite oupd_unseal. rewrite /oupd_def.
    rewrite (least_fixpoint_unfold (oupd_pre E)). done.
  Qed.

  Global Instance oupd_ne E :
    NonExpansive (oupd E).
  Proof.
    intros n P1 P2 HP. rewrite !oupd_unseal /oupd_def. f_equiv. done.
  Qed.
  Global Instance oupd_proper E :
    Proper ((≡) ==> (≡)) (oupd E).
  Proof.
    intros P P' ?. apply equiv_dist=>n. apply oupd_ne. apply equiv_dist. done.
  Qed.

  Lemma oupd_ind_strong E (Ψ : iProp Σ → iProp Σ) :
    (∀ n, Proper (dist n ==> dist n) Ψ) →
    ⊢ (□ (∀ P, oupd_pre E (λ P, Ψ P ∧ |={E}=>o P) P -∗ Ψ P)
       → ∀ P, (|={E}=>o P) -∗ Ψ P)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (P) "H". rewrite oupd_unseal.
    iApply (least_fixpoint_ind _ Ψ with "[] H").
    iIntros "!#" (?) "H". iApply "IH".
    iApply (bi_mono_pred with "[] H").
    { repeat intro. do 3 (f_equiv || done). }
    { repeat intro. rewrite -!oupd_unseal. f_equiv; f_equiv; done. }
    iIntros "!>" (?) "H". iSplit.
    - iDestruct "H" as "[H _]". done.
    - iDestruct "H" as "[_ H]". done.
  Qed.

  Lemma oupd_ind E Ψ :
    (∀ n, Proper (dist n ==> dist n) Ψ)
    → ⊢ (□ (∀ P, oupd_pre E (λ P, Ψ P) P -∗ Ψ P)
         → ∀ P, (|={E}=>o P) -∗ Ψ P)%I.
  Proof.
    iIntros (HΨ) "#H". iApply oupd_ind_strong. iIntros "!>" (P) "Houpd".
    iApply "H". iApply (oupd_pre_mono with "[] Houpd").
    iIntros "!>" (?) "[$ _]".
  Qed.

  (** A standard update can be turned into an obligation update. *)
  Lemma bupd_oupd E P : (|==> P) ⊢ (|={E}=>o P).
  Proof.
    rewrite oupd_unfold. iIntros "Hupd". iRight. iIntros (?????) "I".
    iModIntro. iExists Ω1. iSplitR; first done.
    iIntros (?) "(%& %)".
    rewrite /oproto. iDestruct "I" as "[(S& T& A& N& %OW) I]".
    iFrame.


    TODO

    
    iMod "Hupd" as "P". iModIntro. iLeft. by iFrame.
  Qed.

  (** We can always introduce a relational update. *)
  Lemma oupd_intro P : P ⊢ |={E}=>o P.
  Proof.
    rewrite oupd_unfold.
    iIntros "P" (x) "Hpr"; iModIntro.
    iLeft; by iFrame.
  Qed.

  (** We can combine two relational updates into one. *)
  Lemma oupd_bind P Q :
    (P -∗ |={E}=>o Q) ⊢ (|={E}=>o P) -∗ (|={E}=>o Q).
  Proof.
    iLöb as "IH". iIntros "PQ".
    rewrite {2}(oupd_unfold P) {4}(oupd_unfold Q).
    iIntros  "Hupd" (x) "Hpr". iMod ("Hupd" with "Hpr") as "[Hupd|Hupd]".
    - (* base case for the update around P *)
      iDestruct "Hupd" as "[Hpr Hupd]".
      iSpecialize ("PQ" with "Hupd").
      rewrite {3}(oupd_unfold Q).
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
  Lemma oupd_step P :
    (∀ x, oupd_pred x -∗ |==> ∃ y, ⌜tc oupd_rel y x⌝ ∗ oupd_pred y ∗ ▷ |={E}=>o P) ⊢ |={E}=>o P.
  Proof.
    rewrite {2}(oupd_unfold P).
    iIntros "Hupd" (x) "Hpr". iRight. by iMod ("Hupd" with "Hpr") as "$".
  Qed.

  (* derived lemmas *)
  Lemma oupd_mono P Q : (P ⊢ Q) → (|={E}=>o P) ⊢ (|={E}=>o Q).
  Proof.
    intros Hent. iApply oupd_bind.
    iIntros "P"; iApply oupd_intro; by iApply Hent.
  Qed.
  Lemma oupd_trans P :  (|={E}=>o |={E}=>o P) ⊢ |={E}=>o P.
  Proof.
    iIntros "HP". iApply oupd_bind; eauto.
  Qed.
  Lemma oupd_frame_r P R : (|={E}=>o P) ∗ R ⊢ |={E}=>o P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (oupd_bind with "[R]"); last done.
    iIntros "P". iApply oupd_intro. by iFrame.
  Qed.

  Global Instance oupd_ent_proper : Proper ((⊢) ==> (⊢)) oupd.
  Proof. intros P Q PQ. by apply oupd_mono. Qed.
  Global Instance oupd_flip_ent_proper : Proper (flip (⊢) ==> flip (⊢)) oupd.
  Proof. intros P Q PQ; by apply oupd_mono. Qed.
  Global Instance oupd_equiv_proper : Proper ((≡) ==> (≡)) oupd := ne_proper _.

  Lemma oupd_bupd_l P :
    (|==> |={E}=>o P) ⊢ (|={E}=>o P).
  Proof.
    by rewrite bupd_oupd oupd_trans.
  Qed.
  Lemma oupd_bupd_r P :
    (|={E}=>o |==> P) ⊢ (|={E}=>o P).
  Proof.
    by rewrite bupd_oupd oupd_trans.
  Qed.

  Lemma oupd_frame_l R Q : (R ∗ |={E}=>o Q) ⊢ |={E}=>o R ∗ Q.
  Proof. rewrite !(comm _ R); apply oupd_frame_r. Qed.
  Lemma oupd_wand_l P Q : (P -∗ Q) ∗ (|={E}=>o P) ⊢ |={E}=>o Q.
  Proof. by rewrite oupd_frame_l wand_elim_l. Qed.
  Lemma oupd_wand_r P Q : (|={E}=>o P) ∗ (P -∗ Q) ⊢ |={E}=>o Q.
  Proof. by rewrite oupd_frame_r wand_elim_r. Qed.
  Lemma oupd_sep P Q : (|={E}=>o P) ∗ (|={E}=>o Q) ⊢ |={E}=>o P ∗ Q.
  Proof. by rewrite oupd_frame_r oupd_frame_l oupd_trans. Qed.
  Lemma oupd_idemp P : (|={E}=>o |={E}=>o P) ⊣⊢ |={E}=>o P.
  Proof.
    apply: anti_symm.
    - apply oupd_trans.
    - apply oupd_intro.
  Qed.

  Global Instance oupd_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (oupd).
  Proof. split; [split|]; try apply _; [apply oupd_sep | apply oupd_intro]. Qed.

  Lemma big_sepL_oupd {A} (Φ : nat → A → iProp Σ) l :
    ([∗ list] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_oupd {A} `{Countable K} (Φ : K → A → iProp Σ) l :
    ([∗ map] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_oupd `{Countable A} (Φ : A → iProp Σ) l :
    ([∗ set]  x ∈ l, |==> Φ x) ⊢ |==> [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_oupd `{Countable A} (Φ : A → iProp Σ) l :
    ([∗ mset] x ∈ l, |==> Φ x) ⊢ |==> [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_oupd P : ◇ (|={E}=>o P) ⊢ (|={E}=>o ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using oupd_mono, or_intro_r.
    by rewrite -oupd_intro -or_intro_l.
  Qed.

  (* A safety check that relational updates can replace basic updates *)
  (* We do not use this to build an instance, because it would conflict
     with the basic updates. Instead, we shadow the proofmode lemmas below. *)
  Lemma bi_bupd_mixin_oupd : BiBUpdMixin (iPropI Σ) oupd.
  Proof.
    split.
    - solve_proper.
    - apply oupd_intro.
    - apply oupd_mono.
    - apply oupd_trans.
    - apply oupd_frame_r.
  Qed.

  (* The following instances make the Iris Proof Mode aware of the later
     elimination update. They are derived from the simpler rules above. *)
  Global Instance elim_bupd_oupd (p : bool) P Q :
    ElimModal True p false (|==> P) P (|={E}=>o Q) (|={E}=>o Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    rewrite bupd_oupd.
    iIntros "_ [HP HPQ]". iApply (oupd_bind with "HPQ HP").
  Qed.

  Global Instance add_modal_bupd P Q :
    AddModal (|==> P) P (|={E}=>o Q).
  Proof.
    rewrite /AddModal; rewrite bupd_oupd; iIntros "[HP HPQ]".
    iApply (oupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_oupd p P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|={E}=>o Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply oupd_intro. Qed.

  Global Instance from_pure_oupd a P φ :
    FromPure a P φ → FromPure a (|={E}=>o P) φ.
  Proof. rewrite /FromPure=> <-. apply oupd_intro. Qed.

  Global Instance into_wand_oupd p q R P Q :
    IntoWand false false R P Q → IntoWand p q (|={E}=>o R) (|={E}=>o P) (|={E}=>o Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite oupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_oupd_persistent p q R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E}=>o R) P (|={E}=>o Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite oupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_oupd_args p q R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E}=>o P) (|={E}=>o Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim oupd_wand_r.
  Qed.

  Global Instance from_sep_oupd P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E}=>o P) (|={E}=>o Q1) (|={E}=>o Q2).
  Proof. rewrite /FromSep=><-. apply oupd_sep. Qed.

  Global Instance from_or_oupd P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E}=>o P) (|={E}=>o Q1) (|={E}=>o Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply oupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_oupd {A} P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E}=>o P) (λ a, |={E}=>o Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_oupd P : IsExcept0 P → IsExcept0 (|={E}=>o P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_oupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_oupd P :
    FromModal True modality_id (|={E}=>o P) (|={E}=>o P) P.
  Proof. by rewrite /FromModal /= -oupd_intro. Qed.

  Global Instance elim_modal_oupd p P Q :
    ElimModal True p false (|={E}=>o P) P (|={E}=>o Q) (|={E}=>o Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim oupd_frame_r wand_elim_r oupd_trans.
  Qed.

  Global Instance add_modal_oupd P Q : AddModal (|={E}=>o P) P (|={E}=>o Q).
  Proof. by rewrite /AddModal oupd_frame_r wand_elim_r oupd_trans. Qed.

  Global Instance frame_oupd p R P Q :
    Frame p R P Q → Frame p R (|={E}=>o P) (|={E}=>o Q).
  Proof. rewrite /Frame=><-. by rewrite oupd_frame_l. Qed.




  Global Instance ghost_step_ne `{SI : indexT} `{!lirisGS Λ Σ} E :
    NonExpansive (ghost_step E).
  Proof.
    intros n Φ Ψ HΦ. rewrite /ghost_step. do 15 (f_equiv || done).
  Qed.
  Global Instance ghost_step_proper `{SI : indexT} `{!lirisGS Λ Σ} E :
    Proper ((≡) ==> (≡)) (ghost_step E).
  Proof.
    intros Φ Φ' ?. apply equiv_dist=>n. apply ghost_step_ne. by apply equiv_dist.
  Qed.

  Lemma ghost_step_mono_fupd `{SI : indexT} `{!lirisGS Λ Σ} E (ν1 ν2 : iPropO Σ) :
    ⊢ ((ν1 -∗ |={E}=> ν2) -∗
       ghost_step E ν1 -∗ ghost_step E ν2)%I.
  Proof.
    iIntros "Hmono"; iIntros "Hwp". rewrite /ghost_step.
    iIntros (????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "(%&H0&H1&Hwp)". iFrame. by iApply "Hmono".
  Qed.

  Lemma ghost_step_mono `{SI : indexT} `{!lirisGS Λ Σ} (ν1 ν2 : iPropO Σ) :
    ⊢ ((ν1 -∗ ν2) -∗
       ∀ E, ghost_step E ν1 -∗ ghost_step E ν2)%I.
  Proof.
    iIntros "Hmono"; iIntros (E) "Hwp". iApply (ghost_step_mono_fupd with "[Hmono] Hwp").
    iIntros "H". iModIntro. by iApply "Hmono".
  Qed.

  Lemma fupd_ghost_step `{SI : indexT} `{!lirisGS Λ Σ} E lwp :
    (|={E}=> ghost_step E lwp) ⊢ ghost_step E lwp.
  Proof.
    iIntros "Hf". rewrite /ghost_step. iIntros.
    iMod "Hf" as "Hf". iSpecialize ("Hf" with "[$]"). done.
  Qed.

  Lemma ghost_step_intro `{SI : indexT} `{!lirisGS Λ Σ} E Ψ :
    Ψ ⊢ ghost_step E Ψ.
  Proof.
    iIntros "Hlwp". rewrite /ghost_step.
    iIntros "%%%% H". iModIntro. by iFrame.
  Qed.

  Lemma ghost_step_strong_mono `{SI : indexT} `{!lirisGS Λ Σ} E1 E2 Ψ1 Ψ2 :
    E1 ⊆ E2 →
    ghost_step E1 Ψ1 -∗ (Ψ1 ={E2}=∗ Ψ2) -∗ ghost_step E2 Ψ2.
  Proof.
    iIntros (HE) "IH Hu". rewrite /ghost_step.
    iIntros (????) "H". iSpecialize ("IH" with "[$]").
    iMod (fupd_mask_subseteq E1) as "close"; first done.
    iMod "IH" as "(%&H0&H1&IH)". iFrame. iMod "close" as "_".
    by iApply "Hu".
  Qed.

  Lemma ghost_step_atomic `{SI : indexT} `{!lirisGS Λ Σ} E1 E2 Ψ :
    (|={E1,E2}=> ghost_step E2 (|={E2,E1}=> Ψ)) ⊢ ghost_step E1 Ψ.
  Proof.
    iIntros "IH". rewrite /ghost_step.
    iIntros (????) "H". iSpecialize ("IH" with "[$]").
    iMod "IH". iMod "IH". iDestruct "IH" as "(%&%&H&Hwp)".
    iMod "Hwp". iModIntro. by iFrame.
  Qed.

  Lemma ghost_step_idemp `{SI : indexT} `{!lirisGS Λ Σ} E Ψ :
    ghost_step E (ghost_step E Ψ) ⊢ ghost_step E Ψ.
  Proof.
    iIntros "Hg". rewrite /ghost_step.
    iIntros (????) "H". iSpecialize ("Hg" with "[$]"). iMod "Hg".
    iDestruct "Hg" as "(%&%&H&Hg)". iSpecialize ("Hg" with "[-]"); first by iFrame.
    iDestruct "Hg" as ">(%&%&H&Hg)". iModIntro. iFrame.
    iPureIntro. by etransitivity.
  Qed.

End oupd.

(** Predicates we take the fixpoint of in order to define the lWP. *)
(* Ω must make strict progress for every step (to bound step index) *)
(* W witnesses progresses of obligations; it's instantiated using fair scheduler in the adequacy proof *)
Definition lwp_step `{SI : indexT} `{!lirisGS Λ Σ}
  (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ)
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ :=
  (∀ (Ω1 : obl_states) (W1 : wit_states) (Θ : thread_ids) σ1 κ κs,
     (osat Ω1 ∗ othread Θ ∗ oassigned (dom Ω1) ∗ owitness W1 ∗ state_interp σ1 Θ (κ ++ κs)) ={E,∅}=∗
     (⌜if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
     ∃ Ω2, (⌜ Ω1 ↪ₛ⋆ Ω2 @ σ1 ⌝) ∗
           ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                        |={∅}=>
     ALC (|={∅,E}=>
            ∃ Ω3 Ω4 Ω5, (⌜ (Ω2 ↪ₛ⋆ Ω3 @ σ2) ∧ (Ω3 ↪ₚ Ω4 | obl_cond_owner i) ∧ (Ω4 ↪ₛ⋆ Ω5 @ σ2) ⌝) ∗
            ∀ W2 W3 W4, (⌜ (W1 ↓ₛ⋆ W2) ∧ (W2 ↓ₚ W3 | wit_cond_live) ∧ (W3 ↓ₛ⋆ W4) ∧ obl_wit wit_fun Ω4 W4 ⌝) -∗
            (osat Ω4 ∗ othread (Θ ∪ dom efs) ∗ oassigned (dom Ω4) ∗ owitness W4 ∗ state_interp σ2 (Θ ∪ dom efs) κs) ∗
            ν e2 efs))%I.

(* Definition lwp_step `{SI : indexT} `{!lirisGS Λ Σ} *)
(*   (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ) *)
(*   (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ := *)
(*   (∀ (Ω1 : obl_states) (Θ : thread_ids) σ1 κ κs, *)
(*      (osat Ω1 ∗ othread Θ ∗ osuspend (dom Ω1) ∗ oforest (dom Ω1) ∗ state_interp σ1 Θ (κ ++ κs)) ={E,∅}=∗ *)
(*      (⌜if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗ *)
(*      ∃ Ω1', (⌜ Ω1 ↪ₒ⋆ Ω1' @ σ1 ⌝) ∗ *)
(*             ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗ *)
(*                          |={∅}=> ∃ (b : bool), ALC? b |={∅,E}=> *)
(*      ∃ Ω2 Ω2', (⌜ (if b then (Ω1' ↪ₚ Ω2 | (obl_cond_owner i)) else Ω1' = Ω2) ∧ (Ω2 ↪ₒ⋆ Ω2' @ σ2) ⌝) ∗ *)
(*                (osat Ω2' ∗ othread (Θ ∪ dom efs) ∗ osuspend (dom Ω2') ∗ oforest (dom Ω2') ∗ state_interp σ2 (Θ ∪ dom efs) κs) ∗ *)
(*                ν e2 efs)%I. *)

Section lwp_step.

  Global Instance lwp_step_ne `{SI : indexT} `{!lirisGS Λ Σ} s i E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (lwp_step s i E e).
  Proof.
    intros Φ Ψ HΦ. rewrite /lwp_step.
    do 35 (f_equiv || done).
  Qed.
  Global Instance lwp_step_proper `{SI : indexT} `{!lirisGS Λ Σ} s i E e :
    Proper (pointwise_relation _ (≡) ==> (≡)) (lwp_step s i E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_step_ne=>v; apply equiv_dist.
  Qed.

  Lemma lwp_step_mono `{SI : indexT} `{!lirisGS Λ Σ} s
    (ν1 ν2 : expr Λ -d> thread_pool Λ -d> iPropO Σ) :
    ⊢ ((□ ∀ e efs, ν1 e efs -∗ ν2 e efs) →
       ∀ i E e, lwp_step s i E e ν1 -∗ lwp_step s i E e ν2)%I.
  Proof.
    iIntros "#Hmono"; iIntros (???) "Hwp". rewrite /lwp_step.
    iIntros (?????) "H". iSpecialize ("Hwp" with "[$]").
    iMod "Hwp" as "($& %& $& Hwp)".
    iModIntro. iIntros (???) "H0". iDestruct ("Hwp" with "[$]") as ">Hwp".
    iModIntro. iMod "Hwp" as ">(%& %& %& $& Hwp)".
    iModIntro. iDestruct "Hwp" as "(H1&H2)". iFrame.
    by iApply "Hmono".
  Qed.

  Lemma fupd_lwp_step `{SI : indexT} `{!lirisGS Λ Σ} s i E e lwp :
    (|={E}=> lwp_step s i E e lwp) ⊢ lwp_step s i E e lwp.
  Proof.
    iIntros "Hf". rewrite /lwp_step. iIntros.
    iMod "Hf" as "Hf". iSpecialize ("Hf" with "[$]"). done.
  Qed.

End lwp_step.


Definition lift_term `{SI : indexT} `{!lirisGS Λ Σ} (i :thread_id) (Φ : thread_id → val Λ → iProp Σ) : val Λ → iProp Σ :=
  λ v, (othreadG_elem i ∗ othreadG_term i ∗ Φ i v)%I.

(* pre-definition of lwp of which we take a least fixpoint *)
(* For soundness of Liris, postcondition of a thread i must include othreadG_term i. *)
Definition lwp_pre `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness)
  (lwp : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ :=
  λ i E e1 Φ,
    (match to_val e1 with
     | Some v => ghost_step E (Φ v)
     | None => lwp_step s i E e1 (λ e2 efs, (lwp i E e2 Φ) ∗ [∗ map] j ↦ ef ∈ efs, lwp j ⊤ ef (lift_term j fork_post))
     end)%I.

Lemma lwp_pre_mono `{SI : indexT} `{!lirisGS Λ Σ} s
  (lwp1 lwp2 : thread_id -d> coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  ⊢ ((□ ∀ i E e Φ, lwp1 i E e Φ -∗ lwp2 i E e Φ) →
     ∀ i E e Φ, lwp_pre s lwp1 i E e Φ -∗ lwp_pre s lwp2 i E e Φ)%I.
Proof.
  iIntros "#Hmono"; iIntros (i E e1 Φ) "Hlwp". rewrite /lwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iApply (lwp_step_mono with "[] Hlwp"). iModIntro.
  iIntros (e efs) "[Hlwp Hefs]". iSplitR "Hefs"; first by iApply "Hmono".
  iApply (@big_sepM_impl with "Hefs"); iIntros "!#" (k e' _) "Hlwp". by iApply "Hmono".
Qed.

(* Uncurry [lwp_pre] and equip its type with an OFE structure *)
Definition lwp_pre' `{SI : indexT} `{!lirisGS Λ Σ} (s : stuckness) :
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ) →
  (prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ)
  := uncurry4 ∘ lwp_pre s ∘ curry4.

Local Instance lwp_pre_mono' `{SI : indexT} `{!lirisGS Λ Σ} s :
  BiMonoPred (lwp_pre' s).
Proof.
  constructor.
  - iIntros (lwp1 lwp2 NE1 NE2) "#H". iIntros ((((i&E)&e)&Φ)). iRevert (i E e Φ).
    simpl. iApply lwp_pre_mono. iIntros "!#" (i E e Φ). iApply ("H" $! (i,E,e,Φ)).
  - intros lwp Hlwp n (((i1&E1)&e1)&Φ1) (((i2&E2)&e2)&Φ2)
      (((?%leibniz_equiv & ?%leibniz_equiv) & ?%leibniz_equiv) & ?); simplify_eq/=.
    rewrite /curry4 /lwp_pre /lwp_step.
    do 37 (f_equiv || done). by apply pair_ne.
Qed.

(* take the least fixpoint of the above definition, with partial sate information *)
Local Definition lwp_def `{SI : indexT} `{!lirisGS Λ Σ} : lWp (iProp Σ) (expr Λ) (val Λ) stuckness thread_id :=
  λ s ς i E e Φ, (ς -∗ (bi_least_fixpoint (lwp_pre' s)) (i,E,e,Φ))%I.
Local Definition lwp_aux : seal (@lwp_def). by eexists. Qed.
Definition lwp' := lwp_aux.(unseal).
Global Arguments lwp' {SI Λ Σ _}.
Global Existing Instance lwp'.
Local Lemma lwp_unseal `{SI : indexT} `{!lirisGS Λ Σ} : lwp = @lwp_def SI Λ Σ _.
Proof. rewrite -lwp_aux.(seal_eq) //. Qed.

Section lwp.
Context `{SI : indexT} `{!lirisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma lwp_pre_lwp_pre' s _lwp i E e Φ :
  lwp_pre s _lwp i E e Φ = lwp_pre' s (λ '(i,E,e,Φ), _lwp i E e Φ) (i,E,e,Φ).
Proof. rewrite /lwp_pre' /curry /uncurry4. simpl. rewrite /curry4. f_equal. Qed.
Lemma lwp_unfold s ς i E e Φ :
  lWP e @ s; ς; i; E {{ Φ }} ⊣⊢ (ς -∗ lwp_pre s (lwp (PROP:=iProp Σ) s emp) i E e Φ).
Proof.
  rewrite lwp_unseal. rewrite lwp_pre_lwp_pre' /lwp_def.
  rewrite (least_fixpoint_unfold (lwp_pre' s)). iSplit; iIntros "H".
  - iIntros "Hc". iPoseProof ("H" with "Hc") as "H". iApply (bi_mono_pred with "[] H").
    { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
      f_equiv. f_equiv. done. }
    iIntros "!>" (?) "H". destruct x as [[[? ?] ? ] ?]. iIntros "_". iApply "H".
  - iIntros "Hc". iPoseProof ("H" with "Hc") as "H". iApply (bi_mono_pred with "[] H").
    { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
      f_equiv. f_equiv. done. }
    iIntros "!>" (?) "H". destruct x as [[[? ?] ? ] ?]. by iApply "H".
Qed.

Lemma lwp_cond s ς i E e Φ :
  lWP e @ s; ς; i; E {{ Φ }} ⊣⊢ (ς -∗ lWP e @ s; emp; i; E {{ Φ }}).
Proof.
  rewrite !lwp_unfold. iSplit; iIntros "H Hc".
  - iIntros "_". by iApply "H".
  - by iApply ("H" with "Hc").
Qed.
Lemma lwp_cond_intro s ς i E e Φ :
  (ς -∗ lWP e @ s; emp; i; E {{ Φ }}) -∗ lWP e @ s; ς; i; E {{ Φ }}.
Proof.
  rewrite (lwp_cond _ ς). iIntros "H Hc". by iApply "H".
Qed.
Lemma lwp_cond_elim s ς i E e Φ :
  lWP e @ s; ς; i; E {{ Φ }} -∗ ς -∗ lWP e @ s; emp; i; E {{ Φ }}.
Proof.
  rewrite (lwp_cond _ ς). iIntros "H Hc". by iApply "H".
Qed.

Lemma lwp_ind_strong s ς Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, lwp_pre s (λ i E e Φ, Ψ i E e Φ ∧ lWP e @ s; emp; i; E {{ Φ }}) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, lWP e @ s; ς; i; E {{ Φ }} -∗ ς -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (i e E Φ) "H Hc". rewrite lwp_unseal.
  iPoseProof ("H" with "Hc") as "H".
  set (Ψ' := uncurry4 Ψ :
         prodO (prodO (prodO (leibnizO thread_id) (leibnizO coPset)) (exprO Λ)) (val Λ -d> iProp Σ) → iProp Σ).
  assert (NonExpansive Ψ').
  { intros n [[[i1 E1] e1] Φ1] [[[i2 E2] e2] Φ2]
      [[[?%leibniz_equiv ?%leibniz_equiv] ?%leibniz_equiv] ?]; simplify_eq/=.
    etransitivity; first apply HΨ, H2. done. }
  iApply (least_fixpoint_ind _ Ψ' with "[] H").
  iIntros "!#" ([[[? ?] ?] ?]) "H". iApply "IH". rewrite lwp_pre_lwp_pre'.
  iApply (bi_mono_pred with "[] H").
  { repeat intro. do 3 (f_equiv || done). }
  { repeat intro. destruct x as [[[? ?] ? ] ?], y as [[[? ?] ? ] ?].
    inv H0; simpl in *. inv H1; simpl in *. inv H0; simpl in *.
    apply leibniz_equiv in H3, H1, H4. subst. f_equiv.
    { f_equiv. done. }
    { rewrite /lwp_def. f_equiv. f_equiv. done. }
  }
  iIntros "!>" (?) "H". destruct x as [[[? ?] ?] ?].
  iSplit.
  - iDestruct "H" as "[H _]". done.
  - iDestruct "H" as "[_ H]". by iIntros "_".
Qed.

Lemma lwp_ind_strong_emp s Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, lwp_pre s (λ i E e Φ, Ψ i E e Φ ∧ lWP e @ s; emp; i; E {{ Φ }}) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, lWP e @ s; emp; i; E {{ Φ }} -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (i e E Φ) "H".
  iApply (lwp_ind_strong with "IH H"). done.
Qed.

Lemma lwp_ind s ς Ψ :
  (∀ n i E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ i E e))
  → ⊢ (□ (∀ i e E Φ, lwp_pre s (λ i E e Φ, Ψ i E e Φ) i E e Φ -∗ Ψ i E e Φ)
       → ∀ i e E Φ, lWP e @ s; ς; i; E {{ Φ }} -∗ ς -∗ Ψ i E e Φ)%I.
Proof.
  iIntros (HΨ) "#H". iApply lwp_ind_strong. iIntros "!>" (i e E Φ) "Hrwp".
  iApply "H". iApply (lwp_pre_mono with "[] Hrwp"). clear.
  iIntros "!>" (i E e Φ) "[$ _]".
Qed.

Global Instance lwp_ne s ς i E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (lwp (PROP:=iProp Σ) s ς i E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !lwp_unseal /lwp_def. f_equiv.
  by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.
Global Instance lwp_proper s i ς E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (lwp (PROP:=iProp Σ) s ς i E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply lwp_ne=>v; apply equiv_dist.
Qed.

Global Instance lwp_ne_2 s i E e Φ n :
  Proper ((dist n) ==> dist n) (λ ς, lwp (PROP:=iProp Σ) s ς i E e Φ).
Proof.
  intros ?? HΦ. rewrite !lwp_unseal /lwp_def. f_equiv. done.
Qed.
Global Instance lwp_proper_2 s i E e Φ :
  Proper ((≡) ==> (≡)) (λ ς, lwp (PROP:=iProp Σ) s ς i E e Φ).
Proof.
  intros ???. apply equiv_dist=>n. apply lwp_ne_2. by apply equiv_dist.
Qed.

Lemma ghost_step_elim s ς i E e Φ :
  ghost_step E (lWP e @ s; ς; i; E {{ Φ }}) ⊢ lWP e @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros "Hg". rewrite !lwp_unfold /lwp_pre /lwp_step. iIntros "Hc".
  destruct (to_val e) as [v|] eqn:?.
  { iApply ghost_step_idemp. iApply (ghost_step_mono with "[Hc] Hg").
    iIntros "H". by iApply "H". }
  iIntros (?????) "H".
  rewrite /ghost_step. iSpecialize ("Hg" with "[$]"). iMod "Hg".
  iDestruct "Hg" as "(%&%&H&Hg)". iSpecialize ("Hg" with "Hc [-]"); first by iFrame.
  iMod "Hg". iModIntro. iDestruct "Hg" as "($& %& %& Hg)".
  iExists Ω0. iSplitR.
  { iPureIntro. etransitivity; eauto. }
  iFrame.
Qed.

Lemma lwp_value_fupd' s ς i E Φ v :
  lWP of_val v @ s; ς; i; E {{ Φ }} ⊣⊢ (ς -∗ ghost_step E (Φ v)).
Proof.
  rewrite lwp_cond. iSplit; iIntros "H Hc".
  - rewrite lwp_unfold /lwp_pre to_of_val. by iApply ("H" with "Hc").
  - rewrite lwp_unfold /lwp_pre to_of_val. iIntros "_". by iApply "H".
Qed.

Lemma lwp_stuckness_mono s1 s2 ς i E e Φ :
  s1 ⊑ s2 →
  lWP e @ s1; ς; i; E {{ Φ }} -∗ lWP e @ s2; ς; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_cond_intro. iRevert (i e E Φ) "H".
  iApply lwp_ind_strong. iModIntro. iIntros (i e E Φ) "IH".
  rewrite !lwp_unfold /lwp_pre /=. iIntros "_".
  destruct (to_val e) as [v|] eqn:?; first done.
  iIntros (?????) "H". iSpecialize ("IH" with "[$]").
  iMod "IH" as "(%& %& $& IH)". iModIntro.
  iSplit; [by destruct s1, s2|clear H0].
  iIntros (????). iDestruct ("IH" with "[//]") as ">IH".
  iModIntro. iMod "IH" as ">(%&%&%& $& I& IH& Efs)".
  iModIntro. iDestruct "IH" as "[IH _]". iFrame.
  iApply (big_sepM_impl with "Efs"). iIntros "!>" (k ef _). iIntros "[H _]". done.
Qed.

Lemma lwp_strong_mono s1 s2 ς i E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  lWP e @ s1; ς; i; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ lWP e @ s2; ς; i; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iApply lwp_cond_intro. iIntros "Hc".
  iRevert "HΦ". iRevert (E2 HE). iRevert "Hc". iRevert (i e E1 Φ) "H".
  iApply lwp_ind_strong; [solve_proper| ].
  iIntros "!>" (i e E1 Φ) "IH % %HE HΦ".
  rewrite !lwp_unfold /lwp_pre /=. iIntros "_".
  destruct (to_val e) as [v|] eqn:?.
  { iApply (ghost_step_strong_mono with "IH"); done. }
  iIntros (?????) "H". iSpecialize ("IH" with "[$]").
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod "IH" as "(%& %& %& IH)". iModIntro.
  iSplit; [by destruct s1, s2|clear H0].
  iExists _. iSplitR; first done.
  iIntros (????). iDestruct ("IH" with "[//]") as ">IH".
  iModIntro. iMod "IH" as ">(%&%&%&%& I& [IH _]& Hefs)".
  iMod "Hclose" as "_". iModIntro.
  iFrame. iExists _, _. iSplit; first done. iSplitR "Hefs".
  + by iApply "IH".
  + iApply (big_sepM_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "[_ H]". by iApply (lwp_stuckness_mono with "H").
Qed.

Lemma fupd_lwp s ς i E e Φ :
  (|={E}=> lWP e @ s; ς; i; E {{ Φ }}) ⊢ lWP e @ s; ς; i; E {{ Φ }}.
Proof.
  rewrite lwp_unfold /lwp_pre. iIntros "H Hc". destruct (to_val e) as [v|] eqn:?.
  { iMod "H". by iApply "H". }
  rewrite /lwp_step. iIntros (?????) "Hp". iMod "H".
  iSpecialize ("H" with "Hc [$]"). done.
Qed.
Lemma lwp_fupd s ς i E e Φ :
  lWP e @ s; ς; i; E {{ v, |={E}=> Φ v }} ⊢ lWP e @ s; ς; i; E {{ Φ }}.
Proof. iIntros "H". iApply (lwp_strong_mono s s ς i E with "H"); auto. Qed.

Lemma lwp_atomic s ς i E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> lWP e @ s; ς; i; E2 {{ v, |={E2,E1}=> Φ v }})
  ⊢ lWP e @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !lwp_unfold /lwp_pre. iIntros "Hc".
  destruct (to_val e) as [v|] eqn:He.
  { iApply ghost_step_atomic. by iApply "H". }
  rewrite /lwp_step.
  iIntros (?????) "Hp".
  iMod ("H" with "Hc [$]") as ">($& %& $& H)".
  iIntros "!>" (????). iDestruct ("H" with "[//]") as ">H".
  iModIntro. iMod "H" as ">(%&%&%&%& H0&H&Hefs)".
  destruct s.
  - rewrite !lwp_unfold /lwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iSpecialize ("H" with "[] [H0]"). 1,2: by iFrame.
      iMod "H" as "(%&%&H0&H)". iMod "H". iFrame.
      iModIntro. destruct H0 as [? [? ?]]. iExists Ω3, Ω4. iSplit.
      * iPureIntro. split_and !; auto. by etransitivity.
      * rewrite lwp_unfold /lwp_pre. rewrite He2. iIntros "_". by iApply ghost_step_intro.
    + iPoseProof ("H" with "[]") as "H"; first done.
      iMod ("H" $! _ _ _ [] _ with "H0") as "[H H']".
      iDestruct "H" as %(? & ? & ? & ? & ?). by edestruct (atomic _ _ _ _ _ _ _ H).
  - destruct (atomic _ _ _ _ _ _ _ H) as [v <-%of_to_val].
    rewrite lwp_value_fupd'. iPoseProof ("H" with "[]") as "H"; first done.
    iMod ("H" with "[H0]") as "H"; first by iFrame.
    iDestruct "H" as "(%&%&H0&>H)". iModIntro. iFrame.
    destruct H0 as [? [? ?]]. iExists Ω3, Ω4. iSplit.
    { iPureIntro. split_and !; auto. by etransitivity. }
    iApply lwp_value_fupd'. iIntros "_". by iApply ghost_step_intro.
Qed.

Lemma lwp_step_fupd s ς i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  ((|={E1,E2}=> |={E2,E1}=> P) ∗
   lWP e @ s; ς; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  lWP e @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros (? ?) "[HP Hwp]". iApply (lwp_strong_mono with "Hwp"); [done..|].
  iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP".
Qed.

Lemma lwp_bind_emp K `{!LanguageCtx K} s i E e Φ :
  (lWP e @ s; emp; i; E {{ v, lWP K (of_val v) @ s; emp; i; E {{ Φ }} }})
  ⊢ lWP K e @ s; emp; i; E {{ Φ }}.
Proof.
  revert Φ.
  cut (∀ Φ', lWP e @ s; emp; i; E {{ Φ' }} -∗ ∀ Φ, (∀ v, (Φ' v) -∗ (lWP K (of_val v) @ s; emp; i; E {{ Φ }})) -∗ lWP K e @ s; emp; i; E {{ Φ }}).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (i e E Φ') "H".
  iApply lwp_ind_strong_emp; first solve_proper.
  iIntros "!#" (i e E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /lwp_pre /lwp_step. destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply ghost_step_elim. iApply (ghost_step_mono with "HΦ IH"). }
  rewrite lwp_unfold /lwp_pre /lwp_step fill_not_val; last auto.
  iIntros "_".
  iIntros (?????) "H". iMod ("IH" with "H") as "(%& %& %& IH)". iModIntro. iSplit.
  { iPureIntro. destruct s; last done. unfold reducible in *. naive_solver eauto using fill_step. }
  iExists _. iSplitR; first done.
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv i e σ1 Θ κ e2 σ2 efs) as (e2'&->&?); auto.
  iDestruct ("IH" with "[//]") as ">IH".
  iModIntro. iMod "IH" as ">(%& %& %& $& I& IH& Hefs)".
  iIntros "!>". iFrame. iSplitL "IH HΦ".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite bi.and_elim_r.
Qed.

Lemma lwp_bind K `{!LanguageCtx K} s ς i E e Φ :
  (lWP e @ s; ς; i; E {{ v, ς ∗ lWP K (of_val v) @ s; ς; i; E {{ Φ }} }})
  ⊢ lWP K e @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_cond_intro. iIntros "Hc". iApply lwp_bind_emp.
  iApply (lwp_cond_elim with "[H] Hc"). iApply (lwp_strong_mono with "H"); auto.
  iIntros (?) "[Hc H]". iModIntro. iApply (lwp_cond_elim with "H Hc").
Qed.

Lemma lwp_bind_inv_emp K `{!LanguageCtx K} s i E e Φ :
  lWP K e @ s; emp; i; E {{ Φ }} ⊢ lWP e @ s; emp; i; E {{ v, lWP K (of_val v) @ s; emp; i; E {{ Φ }} }}.
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (i e' E Φ) "H". iApply lwp_ind_strong_emp; first solve_proper.
  iIntros "!#" (i e' E1 Φ) "IH". iIntros (e ->).
  rewrite !lwp_unfold {2}/lwp_pre. iIntros "_".
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply ghost_step_intro. rewrite !lwp_unfold.
    iIntros "_".
    iApply (lwp_pre_mono with "[] IH"). by iIntros "!#" (i' E e Φ') "[_ ?]". }
  rewrite /lwp_pre fill_not_val; [|done].
  iIntros (?????) "Hσ". iMod ("IH" with "[$]") as "(%& %& $& IH)".
  iModIntro. iSplitR.
  { destruct s; eauto using reducible_fill_inv. }
  iIntros (e2 σ2 efs Hstep). iDestruct ("IH" with "[]") as ">IH".
  { eauto using fill_step. }
  iModIntro. iMod "IH" as ">(%& %& %& $& I& IH& Hefs)"; iModIntro.
  iFrame . iSplitR "Hefs".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite bi.and_elim_r.
Qed.

Lemma lwp_bind_inv K `{!LanguageCtx K} s ς i E e Φ :
  lWP K e @ s; emp; i; E {{ Φ }} ⊢ lWP e @ s; ς; i; E {{ v, ς ∗ lWP K (of_val v) @ s; emp; i; E {{ Φ }} }}.
Proof.
  iIntros "H". iApply lwp_cond_intro. iIntros "Hc".
  iPoseProof (lwp_bind_inv_emp with "H") as "H".
  iApply (lwp_strong_mono with "H [Hc]"); auto. iIntros (?) "H".
  iModIntro. iFrame.
Qed.

(** * Derived rules *)
Lemma lwp_mono s ς i E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → lWP e @ s; ς; i; E {{ Φ }} ⊢ lWP e @ s; ς; i; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (lwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma lwp_stuck_mono s1 s2 ς i E e Φ :
  s1 ⊑ s2 → lWP e @ s1; ς; i; E {{ Φ }} ⊢ lWP e @ s2; ς; i; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (lwp_strong_mono with "H"); auto. Qed.
Lemma lwp_stuck_weaken s ς i E e Φ :
  lWP e @ s; ς; i; E {{ Φ }} ⊢ lWP e @ ς; i; E ?{{ Φ }}.
Proof. apply lwp_stuck_mono. by destruct s. Qed.
Lemma lwp_mask_mono s ς i E1 E2 e Φ : E1 ⊆ E2 → lWP e @ s; ς; i; E1 {{ Φ }} ⊢ lWP e @ s; ς; i; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (lwp_strong_mono with "H"); auto. Qed.
Global Instance lwp_mono' s ς i E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (lwp (PROP:=iProp Σ) s ς i E e).
Proof. by intros Φ Φ' ?; apply lwp_mono. Qed.
Global Instance lwp_flip_mono' s ς i E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (lwp (PROP:=iProp Σ) s ς i E e).
Proof. by intros Φ Φ' ?; apply lwp_mono. Qed.

Lemma lwp_value_fupd s ς i E Φ e v : IntoVal e v → lWP e @ s; ς; i; E {{ Φ }} ⊣⊢ (ς -∗ ghost_step E (Φ v)).
Proof. intros <-. by apply lwp_value_fupd'. Qed.
Lemma lwp_value' s ς i E Φ v : (ς -∗ Φ v) ⊢ lWP (of_val v) @ s; ς; i; E {{ Φ }}.
Proof.
  rewrite lwp_value_fupd'. iIntros "H Hc".
  iPoseProof ("H" with "Hc") as "Hc". iStopProof. apply ghost_step_intro.
Qed.
Lemma lwp_value s ς i E Φ e v : IntoVal e v → (ς -∗ Φ v) ⊢ lWP e @ s; ς; i; E {{ Φ }}.
Proof. intros <-. apply lwp_value'. Qed.

Lemma lwp_frame_l s ς i E e Φ R :
  R ∗ lWP e @ s; ς; i; E {{ Φ }} ⊢ lWP e @ s; ς; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma lwp_frame_r s ς i E e Φ R :
  lWP e @ s; ς; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; ς; i; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (lwp_strong_mono with "H"); auto with iFrame. Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the lWP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma lwp_step_fupd_2 s ς i E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  ((|={E1∖E2,∅}=> |={∅,E1∖E2}=> P) ∗
   lWP e @ s; ς; i; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  lWP e @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (lwp_step_fupd with "[H]"); [done|].
  iApply (sep_mono_l with "H"). iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply fupd_mask_frame; [|iMod "HP"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.

Lemma lwp_frame_step_l s ς i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1,E2}=> |={E2,E1}=> R) ∗ lWP e @ s; ς; i; E2 {{ Φ }} ⊢ lWP e @ s; ς; i; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply lwp_step_fupd; first done.
  iFrame "Hu". iApply (lwp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma lwp_frame_step_r s ς i E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  lWP e @ s; ς; i; E2 {{ Φ }} ∗ (|={E1,E2}=> |={E2,E1}=> R) ⊢ lWP e @ s; ς; i; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(lWP _ @ _; _; _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply lwp_frame_step_l.
Qed.
Lemma lwp_frame_step_l' s ς i E e Φ R :
  TCEq (to_val e) None →
  R ∗ lWP e @ s; ς; i; E {{ Φ }} ⊢ lWP e @ s; ς; i; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_l s ς i E E); try iFrame; eauto. Qed.
Lemma lwp_frame_step_r' s ς i E e Φ R :
  TCEq (to_val e) None →
  lWP e @ s; ς; i; E {{ Φ }} ∗ R ⊢ lWP e @ s; ς; i; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (lwp_frame_step_r s ς i E E); try iFrame; eauto. Qed.

Lemma lwp_wand s ς i E e Φ Ψ :
  lWP e @ s; ς; i; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ lWP e @ s; ς; i; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (lwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma lwp_wand_l s ς i E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ lWP e @ s; ς; i; E {{ Φ }} ⊢ lWP e @ s; ς; i; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (lwp_wand with "Hwp H"). Qed.
Lemma lwp_wand_r s ς i E e Φ Ψ :
  lWP e @ s; ς; i; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ lWP e @ s; ς; i; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (lwp_wand with "Hwp H"). Qed.
Lemma lwp_frame_wand s ς i E e Φ R :
  R -∗ lWP e @ s; ς; i; E {{ v, R -∗ Φ v }} -∗ lWP e @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (lwp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
End lwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types i : thread_id.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_lwp p s ς i E e R Φ Ψ :
    (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (lWP e @ s; ς; i; E {{ Φ }}) (lWP e @ s; ς; i; E {{ Ψ }}) | 2.
  Proof.
    rewrite /Frame=> HR. rewrite lwp_frame_l. apply lwp_mono, HR. constructor.
  Qed.

  Global Instance is_except_0_lwp s ς i E e Φ : IsExcept0 (lWP e @ s; ς; i; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_lwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_lwp p s ς i E e P Φ :
    ElimModal True p false (|==> P) P (lWP e @ s; ς; i; E {{ Φ }}) (lWP e @ s; ς; i; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_lwp.
  Qed.

  Global Instance elim_modal_fupd_lwp p s ς i E e P Φ :
    ElimModal True p false (|={E}=> P) P (lWP e @ s; ς; i; E {{ Φ }}) (lWP e @ s; ς; i; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_lwp.
  Qed.

  (** Error message instance for non-mask-changing view shifts.
  Also uses a slightly different error: we cannot apply [fupd_mask_subseteq]
  if [e] is not atomic, so we tell the user to first add a leading [fupd]
  and then change the mask of that. *)
  Global Instance elim_modal_fupd_lwp_wrong_mask p s ς i E1 E2 e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_lwp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2}=> P) False (lWP e @ s; ς; i; E1 {{ Φ }}) False | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_fupd_lwp_atomic p s ς i E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (lWP e @ s; ς; i; E1 {{ Φ }}) (lWP e @ s; ς; i; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r lwp_atomic.
  Qed.

  (** Error message instance for mask-changing view shifts. *)
  Global Instance elim_modal_fupd_lwp_atomic_wrong_mask p s ς i E1 E2 E2' e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2,E2'}=> P) False
      (lWP e @ s; ς; i; E1 {{ Φ }}) False | 200.
  Proof. intros []. Qed.

  Global Instance elim_modal_ghost_step_lwp p s ς i E e P Φ :
    ElimModal True p false (ghost_step E P) P (lWP e @ s; ς; i; E {{ Φ }}) (lWP e @ s; ς; i; E {{ Φ }}).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim. iIntros (?) "[H1 H2]".
    iApply ghost_step_elim. iApply (ghost_step_mono with "H2 H1").
  Qed.

  Global Instance add_modal_fupd_lwp s ς i E e P Φ :
    AddModal (|={E}=> P) P (lWP e @ s; ς; i; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_lwp. Qed.

  Global Instance add_modal_ghost_step_lwp s ς i E e P Φ :
    AddModal (ghost_step E P) P (lWP e @ s; ς; i; E {{ Φ }}).
  Proof. rewrite /AddModal. iIntros "[H1 H2]". iMod "H1". by iApply "H2". Qed.

  Global Instance elim_acc_lwp_atomic {X} ς i E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (lWP e @ s; ς; i; E1 {{ Φ }})
            (λ x, lWP e @ s; ς; i; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_lwp_nonatomic {X} ς i E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (lWP e @ s; ς; i; E {{ Φ }})
            (λ x, lWP e @ s; ς; i; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply lwp_fupd.
    iApply (lwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.
