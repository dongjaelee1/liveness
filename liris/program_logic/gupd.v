From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From liris.base_logic Require Export globl glwit.
From liris.algebra Require Import ordinal_wfocm.
Import uPred.

Global Instance ord_ghost_lock_class : ghost_lock_class :=
  Build_ghost_lock_class Ord.t ord_wfocm_pack.

(* Class gupdGS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) := *)
Class gupdGS `{SI : indexT} (Σ : gFunctors) :=
  GupdG {
      (** Invariants. *)
      #[global] gupd_invGS :: invGS Σ;
      (** Ghost locks. *)
      #[global] gupd_glsatGS :: glsatGS.glsatGS (GL:=ord_ghost_lock_class) Σ;
      (** Ghost lock obligations assigned to threads. *)
      #[global] gupd_globlGS :: globlGS.globlGS Σ;
      (** Ghost lock witnesses. *)
      #[global] gupd_glwitGS :: glwitGS.glwitGS (GL:=ord_ghost_lock_class) Σ;
      (** Fair scheduler function for witnesses. *)
      gupd_η : ghost_lock_fuel → ghost_lock_fuel;
    }.

Global Opaque gupd_invGS gupd_glsatGS gupd_globlGS gupd_glwitGS.
(* Global Arguments GupdG {SI GL Σ}. *)
Global Arguments GupdG {SI Σ}.

Definition gproto `{SI : indexT} `{!gupdGS Σ}
  (Ω : ghost_locks) (W : witnesses) Θ : iProp Σ :=
  (glsat Ω ∗ globl Θ ∗ glassigned (fst <$> Ω) ∗ glwit W ∗ ⌜ glwit_inv gupd_η Ω W ⌝)%I.

(* Simple check *)
Global Instance gproto_timeless `{SI : indexT} `{!gupdGS Σ} Ω W Θ :
  Timeless (gproto Ω W Θ).
Proof. rewrite /gproto. apply _. Qed.

(** Modality for updating ghost locks. *)
Definition gupd_pre `{SI : indexT} `{!gupdGS Σ}
  Θ (gupd : iPropO Σ -d> iPropO Σ) : iProp Σ -d> iPropO Σ :=
  λ P,
    ((|={∅}=> P) ∨
       (∀ (Ω1 : ghost_locks) (W1 : witnesses),
          (gproto Ω1 W1 Θ) ={∅}=∗
          ∃ Ω2, (⌜ (Ω1 ↪∘ Ω2) ⌝) ∗
                ∀ W2, (⌜ (W1 ↓∘ W2) ∧ glwit_inv gupd_η Ω2 W2 ⌝) ={∅}=∗
                      (gproto Ω2 W2 Θ) ∗ gupd P))%I.

Lemma gupd_pre_mono `{SI : indexT} `{!gupdGS Σ} Θ
  (gupd1 gupd2 : iPropO Σ -d> iPropO Σ) :
  ⊢ ((□ ∀ P, gupd1 P -∗ gupd2 P) →
     ∀ P, gupd_pre Θ gupd1 P -∗ gupd_pre Θ gupd2 P)%I.
Proof.
  iIntros "#Hmono"; iIntros (P) "Hgupd". rewrite /gupd_pre.
  iDestruct "Hgupd" as "[H | Hgupd]".
  { iLeft. done. }
  iRight. iIntros (??) "I". iMod ("Hgupd" with "[$I]") as "(%& %& H)".
  iModIntro. iExists _. iSplitR; first done. iIntros (??).
  iMod ("H" with "[//]") as "[$ H]". by iApply "Hmono".
Qed.

Local Instance gupd_pre_mono' `{SI : indexT} `{!gupdGS Σ} Θ :
  BiMonoPred (gupd_pre Θ).
Proof.
  constructor.
  - iIntros (gupd1 gupd2 NE1 NE2) "#H". iApply gupd_pre_mono. iModIntro. iApply "H".
  - intros gupd Hgupd n P1 P2 ?. rewrite /gupd_pre.
    do 20 (f_equiv || done).
Qed.

(* take the least fixpoint of the above definition, with partial sate information *)
Local Definition gupd_def `{SI : indexT} `{!gupdGS Σ} Θ : iProp Σ → iProp Σ :=
  λ P, ((bi_least_fixpoint (gupd_pre Θ)) P)%I.
Local Definition gupd_aux : seal (@gupd_def). by eexists. Qed.
Definition gupd := gupd_aux.(unseal).
(* Arguments gupd {SI _ Σ _}. *)
Arguments gupd {SI Σ _}.
Local Definition gupd_unseal : @gupd = @gupd_def := gupd_aux.(seal_eq).
Notation "'|={' Θ '}=>g' P" := (gupd Θ P) (at level 99, P at level 200, format "|={ Θ }=>g  P").

Section gupd.
  Context `{SI : indexT} `{!gupdGS Σ}.
  Implicit Type Θ : (gset positive).

  Lemma gupd_unfold Θ P :
    (|={Θ}=>g P) ⊣⊢ (gupd_pre Θ (gupd Θ) P).
  Proof.
    rewrite gupd_unseal. rewrite /gupd_def.
    rewrite (least_fixpoint_unfold (gupd_pre Θ)). done.
  Qed.

  Global Instance gupd_ne Θ :
    NonExpansive (gupd Θ).
  Proof.
    intros n P1 P2 HP. rewrite !gupd_unseal /gupd_def. f_equiv. done.
  Qed.
  Global Instance gupd_proper Θ :
    Proper ((≡) ==> (≡)) (gupd Θ).
  Proof.
    intros P P' ?. apply equiv_dist=>n. apply gupd_ne. apply equiv_dist. done.
  Qed.

  Lemma gupd_ind_strong (Ψ : iProp Σ → iProp Σ) Θ :
    (∀ n, Proper (dist n ==> dist n) Ψ) →
    ⊢ (□ (∀ P, gupd_pre Θ (λ P, Ψ P ∧ |={Θ}=>g P) P -∗ Ψ P)
       → ∀ P, (|={Θ}=>g P) -∗ Ψ P)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (P) "H". rewrite gupd_unseal.
    iApply (least_fixpoint_ind _ Ψ with "[] H").
    iIntros "!#" (?) "H". iApply "IH".
    iApply (bi_mono_pred with "[] H").
    { repeat intro. do 3 (f_equiv || done). }
    { repeat intro. rewrite -!gupd_unseal. f_equiv; f_equiv; done. }
    iIntros "!>" (?) "H". iSplit.
    - iDestruct "H" as "[H _]". done.
    - iDestruct "H" as "[_ H]". done.
  Qed.

  Lemma gupd_ind Θ Ψ :
    (∀ n, Proper (dist n ==> dist n) Ψ)
    → ⊢ (□ (∀ P, gupd_pre Θ (λ P, Ψ P) P -∗ Ψ P)
         → ∀ P, (|={Θ}=>g P) -∗ Ψ P)%I.
  Proof.
    iIntros (HΨ) "#H". iApply gupd_ind_strong. iIntros "!>" (P) "Hgupd".
    iApply "H". iApply (gupd_pre_mono with "[] Hgupd").
    iIntros "!>" (?) "[$ _]".
  Qed.

  (** A fancy update can be turned into an obligation update. *)
  Lemma fupd_gupd Θ P : (|={∅}=> P) ⊢ (|={Θ}=>g P).
  Proof.
    rewrite gupd_unfold. iIntros "Hupd". iLeft. done.
  Qed.

  (** We can always introduce a obligation update. *)
  Lemma gupd_intro Θ P : P ⊢ |={Θ}=>g P.
  Proof.
    rewrite gupd_unfold. iIntros "HP". iLeft. iModIntro. done.
  Qed.

  (** We can always eliminate a fancy update. *)
  Lemma fupd_gupd_elim Θ P :
    (|={∅}=> |={Θ}=>g P) ⊢ |={Θ}=>g P.
  Proof.
    iIntros "H". iApply gupd_unfold.
    iRight. iIntros (??) "I". iMod "H".
    iModIntro. iExists Ω1. iSplitR; first done.
    iIntros (? (Prog& OW2)).
    iModIntro. rewrite /gproto. iDestruct "I" as "($& $& $& N& %OW1)".
    pose proof (glwit_inv_rc_step_same_gls _ _ _ _ OW1 Prog OW2).
    iPoseProof (glwit_mon _ _ H with "N") as "$".
    iFrame. done.
  Qed.

  (** We can combine two obligation updates into one. *)
  Lemma gupd_bind Θ P Q :
    (P -∗ |={Θ}=>g Q) ⊢ (|={Θ}=>g P) -∗ (|={Θ}=>g Q).
  Proof.
    iIntros "H HP". iRevert (Q) "H". iRevert (P) "HP".
    iApply gupd_ind_strong.
    { solve_proper. }
    iIntros "!> %P IH %Q H". iDestruct "IH" as "[IH | IH]".
    - iApply fupd_gupd_elim. iMod "IH". iModIntro. iApply ("H" with "IH").
    - iApply gupd_unfold. iRight. iIntros (??) "I".
      iMod ("IH" with "I") as "(%&%& IH)".
      iModIntro. iExists _. iSplitR; first done.
      iIntros (??). iMod ("IH" with "[//]") as "[$ IH]".
      iModIntro. iDestruct "IH" as "[IH _]".
      iApply "IH". done.
  Qed.

  (* derived lemmas *)
  Lemma gupd_mono Θ P Q : (P ⊢ Q) → (|={Θ}=>g P) ⊢ (|={Θ}=>g Q).
  Proof.
    intros Hent. iApply gupd_bind.
    iIntros "P"; iApply gupd_intro; by iApply Hent.
  Qed.
  Lemma gupd_trans Θ P :  (|={Θ}=>g |={Θ}=>g P) ⊢ |={Θ}=>g P.
  Proof.
    iIntros "HP". iApply gupd_bind; eauto.
  Qed.
  Lemma gupd_frame_r Θ P R : (|={Θ}=>g P) ∗ R ⊢ |={Θ}=>g P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (gupd_bind with "[R]"); last done.
    iIntros "P". iApply gupd_intro. by iFrame.
  Qed.

  Global Instance gupd_ent_proper Θ : Proper ((⊢) ==> (⊢)) (gupd Θ).
  Proof. intros P Q PQ. by apply gupd_mono. Qed.
  Global Instance gupd_flip_ent_proper Θ : Proper (flip (⊢) ==> flip (⊢)) (gupd Θ).
  Proof. intros P Q PQ; by apply gupd_mono. Qed.
  Global Instance gupd_equiv_proper Θ : Proper ((≡) ==> (≡)) (gupd Θ) := ne_proper _.

  Lemma gupd_fupd_l Θ P :
    (|={∅}=> |={Θ}=>g P) ⊢ (|={Θ}=>g P).
  Proof.
    by erewrite fupd_gupd, gupd_trans.
  Qed.
  Lemma gupd_fupd_r Θ P :
    (|={Θ}=>g |={∅}=> P) ⊢ (|={Θ}=>g P).
  Proof.
    by erewrite fupd_gupd, gupd_trans.
  Qed.

  Lemma gupd_frame_l Θ R Q : (R ∗ |={Θ}=>g Q) ⊢ |={Θ}=>g R ∗ Q.
  Proof. rewrite !(comm _ R); apply gupd_frame_r. Qed.
  Lemma gupd_wand_l Θ P Q : (P -∗ Q) ∗ (|={Θ}=>g P) ⊢ |={Θ}=>g Q.
  Proof. by rewrite gupd_frame_l wand_elim_l. Qed.
  Lemma gupd_wand_r Θ P Q : (|={Θ}=>g P) ∗ (P -∗ Q) ⊢ |={Θ}=>g Q.
  Proof. by rewrite gupd_frame_r wand_elim_r. Qed.
  Lemma gupd_sep Θ P Q : (|={Θ}=>g P) ∗ (|={Θ}=>g Q) ⊢ |={Θ}=>g P ∗ Q.
  Proof. by rewrite gupd_frame_r gupd_frame_l gupd_trans. Qed.
  Lemma gupd_idemp Θ P : (|={Θ}=>g |={Θ}=>g P) ⊣⊢ |={Θ}=>g P.
  Proof.
    apply: anti_symm.
    - apply gupd_trans.
    - apply gupd_intro.
  Qed.

  Global Instance gupd_homomorphism Θ :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (gupd Θ).
  Proof. split; [split|]; try apply _; [apply gupd_sep | apply gupd_intro]. Qed.

  Lemma big_sepL_gupd {A} (Φ : nat → A → iProp Σ) Θ l :
    ([∗ list] k↦x ∈ l, |={Θ}=>g Φ k x) ⊢ |={Θ}=>g [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_gupd {A} `{Countable K} (Φ : K → A → iProp Σ) Θ l :
    ([∗ map] k↦x ∈ l, |={Θ}=>g Φ k x) ⊢ |={Θ}=>g [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_gupd `{Countable A} (Φ : A → iProp Σ) Θ l :
    ([∗ set]  x ∈ l, |={Θ}=>g Φ x) ⊢ |={Θ}=>g [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_gupd `{Countable A} (Φ : A → iProp Σ) Θ l :
    ([∗ mset] x ∈ l, |={Θ}=>g Φ x) ⊢ |={Θ}=>g [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_gupd Θ P : ◇ (|={Θ}=>g P) ⊢ (|={Θ}=>g ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using gupd_mono, or_intro_r.
    by rewrite -gupd_intro -or_intro_l.
  Qed.

  (* The following instances make the Iris Proof Mode aware of the
     obligation update. They are derived from the simpler rules above. *)
  (* Global Instance elim_fupd_gupd (p : bool) Θ P Q : *)
  (*   ElimModal True p false (|={∅}=> P) P (|={Θ}=>g Q) (|={Θ}=>g Q)%I. *)
  (* Proof. *)
  (*   rewrite /ElimModal bi.intuitionistically_if_elim //=. *)
  (*   rewrite fupd_gupd. *)
  (*   iIntros "_ [HP HPQ]". iApply (gupd_bind with "HPQ HP"). *)
  (* Qed. *)

  Global Instance elim_fupd_gupd (p : bool) E Θ P Q :
    ElimModal True p false (|={∅,E}=> P) P (|={Θ}=>g Q) (|={E,∅}=> |={Θ}=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_gupd_elim. iMod "HP".
    by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_gupd Θ P Q :
    AddModal (|={∅}=> P) P (|={Θ}=>g Q).
  Proof.
    rewrite /AddModal; rewrite fupd_gupd; iIntros "[HP HPQ]".
    iApply (gupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_gupd p Θ P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|={Θ}=>g Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply gupd_intro. Qed.

  Global Instance from_pure_gupd a Θ P φ :
    FromPure a P φ → FromPure a (|={Θ}=>g P) φ.
  Proof. rewrite /FromPure=> <-. apply gupd_intro. Qed.

  Global Instance into_wand_gupd p q Θ R P Q :
    IntoWand false false R P Q → IntoWand p q (|={Θ}=>g R) (|={Θ}=>g P) (|={Θ}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite gupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_gupd_persistent p q Θ R P Q :
    IntoWand false q R P Q → IntoWand p q (|={Θ}=>g R) P (|={Θ}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite gupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_gupd_args p q Θ R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={Θ}=>g P) (|={Θ}=>g Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim gupd_wand_r.
  Qed.

  Global Instance from_sep_gupd Θ P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={Θ}=>g P) (|={Θ}=>g Q1) (|={Θ}=>g Q2).
  Proof. rewrite /FromSep=><-. apply gupd_sep. Qed.

  Global Instance from_or_gupd Θ P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={Θ}=>g P) (|={Θ}=>g Q1) (|={Θ}=>g Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply gupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_gupd {A} Θ P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={Θ}=>g P) (λ a, |={Θ}=>g Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_gupd Θ P : IsExcept0 P → IsExcept0 (|={Θ}=>g P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_gupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_gupd Θ P :
    FromModal True modality_id (|={Θ}=>g P) (|={Θ}=>g P) P.
  Proof. by rewrite /FromModal /= -gupd_intro. Qed.

  Global Instance elim_modal_gupd p Θ P Q :
    ElimModal True p false (|={Θ}=>g P) P (|={Θ}=>g Q) (|={Θ}=>g Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim gupd_frame_r wand_elim_r gupd_trans.
  Qed.

  Global Instance add_modal_gupd Θ P Q : AddModal (|={Θ}=>g P) P (|={Θ}=>g Q).
  Proof. by rewrite /AddModal gupd_frame_r wand_elim_r gupd_trans. Qed.

  Global Instance frame_gupd p Θ R P Q :
    Frame p R P Q → Frame p R (|={Θ}=>g P) (|={Θ}=>g Q).
  Proof. rewrite /Frame=><-. by rewrite gupd_frame_l. Qed.

End gupd.

(* Wrapper to use fupd. *)
Definition fgupd `{SI : indexT} `{!gupdGS Σ} E Θ : iPropO Σ -d> iPropO Σ :=
  (λ P, |={E,∅}=> |={Θ}=>g |={∅,E}=> P)%I.
Notation "'|={' E : Θ '}=>g' P" := (fgupd E Θ P) (at level 99, P at level 200, format "|={ E : Θ }=>g  P").

Section fgupd.
  Context `{SI : indexT} `{!gupdGS Σ}.
  Implicit Type Θ : (gset positive).

  Global Instance fgupd_ne E Θ :
    NonExpansive (fgupd E Θ).
  Proof.
    intros n P1 P2 HP. rewrite /fgupd. do 12 (f_equiv || done).
  Qed.
  Global Instance fgupd_proper E Θ :
    Proper ((≡) ==> (≡)) (fgupd E Θ).
  Proof.
    intros P P' ?. apply equiv_dist=>n. apply fgupd_ne. apply equiv_dist. done.
  Qed.

  Lemma fupd_fgupd E Θ P : (|={E}=> P) ⊢ (|={E:Θ}=>g P).
  Proof.
    rewrite /fgupd. iIntros ">Hupd".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose !>". iMod "Hclose" as "_".
    iModIntro. iFrame.
  Qed.

  Lemma fgupd_intro E Θ P : P ⊢ |={E:Θ}=>g P.
  Proof.
    iIntros "$". iMod (fupd_mask_subseteq ∅) as "Hclose". 1: set_solver.
    iIntros "!> !>". iMod "Hclose". done.
  Qed.

  Lemma fupd_fgupd_elim E Θ P :
    (|={E}=> |={E:Θ}=>g P) ⊢ |={E:Θ}=>g P.
  Proof.
    iIntros "H". iMod "H". iApply "H".
  Qed.

  (** Change to a larger mask. *)
  Lemma fgupd_mask_mono E1 E2 Θ P :
    E1 ⊆ E2 →
    (|={E1:Θ}=>g P) ⊢ |={E2:Θ}=>g P.
  Proof.
    iIntros (Sub) "H".
    iMod (fupd_mask_subseteq E1) as "close". 1: done.
    iMod "H". iModIntro. iMod "H" as ">H".
    iMod "close" as "_".
    iMod (fupd_mask_subseteq ∅) as "close". 1: set_solver.
    iIntros "!> !>". iMod "close" as "_". by iApply "H".
  Qed.

  (** We can combine two obligation updates into one. *)
  Lemma fgupd_bind E Θ P Q :
    (P -∗ |={E:Θ}=>g Q) ⊢ (|={E:Θ}=>g P) -∗ (|={E:Θ}=>g Q).
  Proof.
    iIntros "H >HP".
    iModIntro. iMod "HP" as ">HP".
    iPoseProof ("H" with "HP") as "H". done.
  Qed.

  (* derived lemmas *)
  Lemma fgupd_mono E Θ P Q : (P ⊢ Q) → (|={E:Θ}=>g P) ⊢ (|={E:Θ}=>g Q).
  Proof.
    intros Hent. iApply fgupd_bind.
    iIntros "P"; iApply fgupd_intro; by iApply Hent.
  Qed.
  Lemma fgupd_trans E Θ P :  (|={E:Θ}=>g |={E:Θ}=>g P) ⊢ |={E:Θ}=>g P.
  Proof.
    iIntros "HP". iApply fgupd_bind; eauto.
  Qed.
  Lemma fgupd_frame_r E Θ P R : (|={E:Θ}=>g P) ∗ R ⊢ |={E:Θ}=>g P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (fgupd_bind with "[R]"); last done.
    iIntros "P". iApply fgupd_intro. by iFrame.
  Qed.

  Global Instance fgupd_ent_proper E Θ : Proper ((⊢) ==> (⊢)) (fgupd E Θ).
  Proof. intros P Q PQ. by apply fgupd_mono. Qed.
  Global Instance fgupd_flip_ent_proper E Θ : Proper (flip (⊢) ==> flip (⊢)) (fgupd E Θ).
  Proof. intros P Q PQ; by apply fgupd_mono. Qed.
  Global Instance fgupd_equiv_proper E Θ : Proper ((≡) ==> (≡)) (fgupd E Θ) := ne_proper _.

  Lemma fgupd_fupd_l E Θ P :
    (|={E}=> |={E:Θ}=>g P) ⊢ (|={E:Θ}=>g P).
  Proof.
    by erewrite fupd_fgupd, fgupd_trans.
  Qed.
  Lemma fgupd_fupd_r E Θ P :
    (|={E:Θ}=>g |={E}=> P) ⊢ (|={E:Θ}=>g P).
  Proof.
    by erewrite fupd_fgupd, fgupd_trans.
  Qed.

  Lemma fgupd_frame_l E Θ R Q : (R ∗ |={E:Θ}=>g Q) ⊢ |={E:Θ}=>g R ∗ Q.
  Proof. rewrite !(comm _ R); apply fgupd_frame_r. Qed.
  Lemma fgupd_wand_l E Θ P Q : (P -∗ Q) ∗ (|={E:Θ}=>g P) ⊢ |={E:Θ}=>g Q.
  Proof. by rewrite fgupd_frame_l wand_elim_l. Qed.
  Lemma fgupd_wand_r E Θ P Q : (|={E:Θ}=>g P) ∗ (P -∗ Q) ⊢ |={E:Θ}=>g Q.
  Proof. by rewrite fgupd_frame_r wand_elim_r. Qed.
  Lemma fgupd_sep E Θ P Q : (|={E:Θ}=>g P) ∗ (|={E:Θ}=>g Q) ⊢ |={E:Θ}=>g P ∗ Q.
  Proof. by rewrite fgupd_frame_r fgupd_frame_l fgupd_trans. Qed.
  Lemma fgupd_idemp E Θ P : (|={E:Θ}=>g |={E:Θ}=>g P) ⊣⊢ |={E:Θ}=>g P.
  Proof.
    apply: anti_symm.
    - apply fgupd_trans.
    - apply fgupd_intro.
  Qed.

  Global Instance fgupd_homomorphism E Θ :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (fgupd E Θ).
  Proof. split; [split|]; try apply _; [apply fgupd_sep | apply fgupd_intro]. Qed.

  Lemma big_sepL_fgupd {A} (Φ : nat → A → iProp Σ) E Θ l :
    ([∗ list] k↦x ∈ l, |={E:Θ}=>g Φ k x) ⊢ |={E:Θ}=>g [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_fgupd {A} `{Countable K} (Φ : K → A → iProp Σ) E Θ l :
    ([∗ map] k↦x ∈ l, |={E:Θ}=>g Φ k x) ⊢ |={E:Θ}=>g [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_fgupd `{Countable A} (Φ : A → iProp Σ) E Θ l :
    ([∗ set]  x ∈ l, |={E:Θ}=>g Φ x) ⊢ |={E:Θ}=>g [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_fgupd `{Countable A} (Φ : A → iProp Σ) E Θ l :
    ([∗ mset] x ∈ l, |={E:Θ}=>g Φ x) ⊢ |={E:Θ}=>g [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_fgupd E Θ P : ◇ (|={E:Θ}=>g P) ⊢ (|={E:Θ}=>g ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using fgupd_mono, or_intro_r.
    by rewrite -fgupd_intro -or_intro_l.
  Qed.

  Global Instance elim_fupd_fgupd (p : bool) E Θ P Q :
    ElimModal True p false (|={E}=> P) P (|={E:Θ}=>g Q) (|={E:Θ}=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_fgupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_fgupd E Θ P Q :
    AddModal (|={E}=> P) P (|={E:Θ}=>g Q).
  Proof.
    rewrite /AddModal; rewrite fupd_fgupd; iIntros "[HP HPQ]".
    iApply (fgupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_fgupd p E Θ P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|={E:Θ}=>g Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply fgupd_intro. Qed.

  Global Instance from_pure_fgupd a E Θ P φ :
    FromPure a P φ → FromPure a (|={E:Θ}=>g P) φ.
  Proof. rewrite /FromPure=> <-. apply fgupd_intro. Qed.

  Global Instance into_wand_fgupd p q E Θ R P Q :
    IntoWand false false R P Q → IntoWand p q (|={E:Θ}=>g R) (|={E:Θ}=>g P) (|={E:Θ}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite fgupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_fgupd_persistent p q E Θ R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E:Θ}=>g R) P (|={E:Θ}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite fgupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_fgupd_args p q E Θ R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E:Θ}=>g P) (|={E:Θ}=>g Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim fgupd_wand_r.
  Qed.

  Global Instance from_sep_fgupd E Θ P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E:Θ}=>g P) (|={E:Θ}=>g Q1) (|={E:Θ}=>g Q2).
  Proof. rewrite /FromSep=><-. apply fgupd_sep. Qed.

  Global Instance from_or_fgupd E Θ P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E:Θ}=>g P) (|={E:Θ}=>g Q1) (|={E:Θ}=>g Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply fgupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_fgupd {A} E Θ P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E:Θ}=>g P) (λ a, |={E:Θ}=>g Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_fgupd E Θ P : IsExcept0 P → IsExcept0 (|={E:Θ}=>g P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_fgupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_fgupd E Θ P :
    FromModal True modality_id (|={E:Θ}=>g P) (|={E:Θ}=>g P) P.
  Proof. by rewrite /FromModal /= -fgupd_intro. Qed.

  Global Instance elim_modal_fgupd p E Θ P Q :
    ElimModal True p false (|={E:Θ}=>g P) P (|={E:Θ}=>g Q) (|={E:Θ}=>g Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim fgupd_frame_r wand_elim_r fgupd_trans.
  Qed.

  Global Instance add_modal_fgupd E Θ P Q : AddModal (|={E:Θ}=>g P) P (|={E:Θ}=>g Q).
  Proof. by rewrite /AddModal fgupd_frame_r wand_elim_r fgupd_trans. Qed.

  Global Instance frame_fgupd p E Θ R P Q :
    Frame p R P Q → Frame p R (|={E:Θ}=>g P) (|={E:Θ}=>g Q).
  Proof. rewrite /Frame=><-. by rewrite fgupd_frame_l. Qed.

End fgupd.

(** Ghost lock predicates. *)
(* Ghost locks *)
Local Definition gl_def `{SI : indexT} `{@gupdGS SI Σ}
  k v : iProp Σ :=
  glG_elem k ∗ glG_version_lb k v.
Local Definition gl_aux : seal (@gl_def). Proof. by eexists. Qed.
Definition gl := gl_aux.(unseal).
Local Definition gl_unseal :
  @gl = @gl_def := gl_aux.(seal_eq).
Global Arguments gl {SI Σ _}.

Local Definition gl_witfun_def `{SI : indexT} `{@gupdGS SI Σ}
  k ξ : iProp Σ :=
  glG_witfun k ξ.
Local Definition gl_witfun_aux : seal (@gl_witfun_def). Proof. by eexists. Qed.
Definition gl_witfun := gl_witfun_aux.(unseal).
Local Definition gl_witfun_unseal :
  @gl_witfun = @gl_witfun_def := gl_witfun_aux.(seal_eq).
Global Arguments gl_witfun {SI Σ _}.

(* Local Definition gl_locked_def `{SI : indexT} `{@gupdGS SI GL Σ} *)
(*   k v : iProp Σ := *)
(*   gl k v ∗ glG_locked k v (1/2 + 1/2/2/2/2)%Qp. *)
(* Local Definition gl_locked_aux : seal (@gl_locked_def). Proof. by eexists. Qed. *)
(* Definition gl_locked := gl_locked_aux.(unseal). *)
(* Local Definition gl_locked_unseal : *)
(*   @gl_locked = @gl_locked_def := gl_locked_aux.(seal_eq). *)
(* Global Arguments gl_locked {SI GL Σ _}. *)

Local Definition gl_done_def `{SI : indexT} `{@gupdGS SI Σ}
  k v : iProp Σ :=
  gl k v ∗ glG_unlocked k v.
Local Definition gl_done_aux : seal (@gl_done_def). Proof. by eexists. Qed.
Definition gl_done := gl_done_aux.(unseal).
Local Definition gl_done_unseal :
  @gl_done = @gl_done_def := gl_done_aux.(seal_eq).
Global Arguments gl_done {SI Σ _}.

(* Local Definition gl_ver_def `{SI : indexT} `{@gupdGS SI GL Σ} *)
(*   k v : iProp Σ := *)
(*   gl k v ∗ glG_version k v (1/2 + 1/2/2)%Qp. *)
(* Local Definition gl_ver_aux : seal (@gl_ver_def). Proof. by eexists. Qed. *)
(* Definition gl_ver := gl_ver_aux.(unseal). *)
(* Local Definition gl_ver_unseal : *)
(*   @gl_ver = @gl_ver_def := gl_ver_aux.(seal_eq). *)
(* Global Arguments gl_ver {SI GL Σ _}. *)

(* Local Definition gl_pin_def `{SI : indexT} `{@gupdGS SI GL Σ} *)
(*   k v : iProp Σ := *)
(*   gl k v ∗ glG_version_pin k v. *)
(* Local Definition gl_pin_aux : seal (@gl_pin_def). Proof. by eexists. Qed. *)
(* Definition gl_pin := gl_pin_aux.(unseal). *)
(* Local Definition gl_pin_unseal : *)
(*   @gl_pin = @gl_pin_def := gl_pin_aux.(seal_eq). *)
(* Global Arguments gl_pin {SI GL Σ _}. *)

Local Definition gl_current_def `{SI : indexT} `{@gupdGS SI Σ}
  k v : iProp Σ :=
  gl k v ∗ glG_version k v (1/2 + 1/2/2)%Qp.
Local Definition gl_current_aux : seal (@gl_current_def). Proof. by eexists. Qed.
Definition gl_current := gl_current_aux.(unseal).
Local Definition gl_current_unseal :
  @gl_current = @gl_current_def := gl_current_aux.(seal_eq).
Global Arguments gl_current {SI Σ _}.

Local Definition gl_expired_def `{SI : indexT} `{@gupdGS SI Σ}
  k v : iProp Σ :=
  gl k v ∗ glG_version_expired k v.
Local Definition gl_expired_aux : seal (@gl_expired_def). Proof. by eexists. Qed.
Definition gl_expired := gl_expired_aux.(unseal).
Local Definition gl_expired_unseal :
  @gl_expired = @gl_expired_def := gl_expired_aux.(seal_eq).
Global Arguments gl_expired {SI Σ _}.

Local Definition gl_fuel_def `{SI : indexT} `{@gupdGS SI Σ}
  k a : iProp Σ :=
  glG_elem k ∗ glG_fuel k a.
Local Definition gl_fuel_aux : seal (@gl_fuel_def). Proof. by eexists. Qed.
Definition gl_fuel := gl_fuel_aux.(unseal).
Local Definition gl_fuel_unseal :
  @gl_fuel = @gl_fuel_def := gl_fuel_aux.(seal_eq).
Global Arguments gl_fuel {SI Σ _}.

Local Definition gl_variant_def `{SI : indexT} `{@gupdGS SI Σ}
  N k v (P Q R : iProp Σ) : iProp Σ :=
  gl k v ∗ glG_variant N k v (1/2/2/2/2)%Qp P Q R.
Local Definition gl_variant_aux : seal (@gl_variant_def). Proof. by eexists. Qed.
Definition gl_variant := gl_variant_aux.(unseal).
Local Definition gl_variant_unseal :
  @gl_variant = @gl_variant_def := gl_variant_aux.(seal_eq).
Global Arguments gl_variant {SI Σ _}.

(* Ghost lock obligations *)
Local Definition th_obls_def `{SI : indexT} `{@gupdGS SI Σ}
  i (G : gmap gl_id ghost_lock_version) q : iProp Σ :=
  globlG_elem i ∗ globlG_exec i (q/2 + q/2/2)%Qp ∗ globlG_obls i (dom G) q ∗
  ([∗ map] k ↦ v ∈ G,
     glG_elem k ∗ glG_locked k v (1/2 + 1/2/2/2/2)%Qp ∗
     glG_version k v (1/2 + 1/2/2)%Qp ∗
     glG_owner k i (1/2 + 1/2/2/2)%Qp ∗ globlG_owns i k v (1/2 + 1/2/2)%Qp).
Local Definition th_obls_aux : seal (@th_obls_def). Proof. by eexists. Qed.
Definition th_obls := th_obls_aux.(unseal).
Local Definition th_obls_unseal :
  @th_obls = @th_obls_def := th_obls_aux.(seal_eq).
Global Arguments th_obls {SI Σ _}.

Local Definition th_term_def `{SI : indexT} `{@gupdGS SI Σ}
  i : iProp Σ :=
  globlG_elem i ∗ globlG_term i.
Local Definition th_term_aux : seal (@th_term_def). Proof. by eexists. Qed.
Definition th_term := th_term_aux.(unseal).
Local Definition th_term_unseal :
  @th_term = @th_term_def := th_term_aux.(seal_eq).
Global Arguments th_term {SI Σ _}.

(* Ghost lock witnesses *)
Local Definition wit_def `{SI : indexT} `{@gupdGS SI Σ}
  k v α : iProp Σ :=
  gl k v ∗ witG_witness k v α.
Local Definition wit_aux : seal (@wit_def). Proof. by eexists. Qed.
Definition wit := wit_aux.(unseal).
Local Definition wit_unseal :
  @wit = @wit_def := wit_aux.(seal_eq).
Global Arguments wit {SI Σ _}.

Local Definition wit_credit_def `{SI : indexT} `{@gupdGS SI Σ}
  k v a : iProp Σ :=
  gl k v ∗ witG_credit k v a.
Local Definition wit_credit_aux : seal (@wit_credit_def). Proof. by eexists. Qed.
Definition wit_credit := wit_credit_aux.(unseal).
Local Definition wit_credit_unseal :
  @wit_credit = @wit_credit_def := wit_credit_aux.(seal_eq).
Global Arguments wit_credit {SI Σ _}.

Section preds.
  Context `{SI : indexT} `{!gupdGS Σ}.

  Local Ltac unfold_defs :=
    try rewrite !wit_credit_unseal /wit_credit_def;
    try rewrite !wit_unseal /wit_def;
    try rewrite !th_term_unseal /th_term_def;
    try rewrite !th_obls_unseal /th_obls_def;
    try rewrite !gl_variant_unseal /gl_variant_def;
    try rewrite !gl_fuel_unseal /gl_fuel_def;
    try rewrite !gl_expired_unseal /gl_expired_def;
    try rewrite !gl_current_unseal /gl_current_def;
    try rewrite !gl_done_unseal /gl_done_def;
    try rewrite !gl_witfun_unseal /gl_witfun_def;
    try rewrite !gl_unseal /gl_def.

  Section liveness_preds.

    (** Instances *)
    Global Instance gl_persistent k v : Persistent (gl k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_witfun_persistent k ξ : Persistent (gl_witfun k ξ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_done_persistent k v : Persistent (gl_done k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_expired_persistent k v : Persistent (gl_expired k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_variant_persistent N k v P Q R : Persistent (gl_variant N k v P Q R).
    Proof. unfold_defs. apply _. Qed.
    Global Instance th_term_persistent i : Persistent (th_term i).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_persistent k v α : Persistent (wit k v α).
    Proof. unfold_defs. apply _. Qed.

    Global Instance gl_timeless k v : Timeless (gl k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_witfun_timeless k ξ : Timeless (gl_witfun k ξ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_done_timeless k v : Timeless (gl_done k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_current_timeless k v : Timeless (gl_current k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_expired_timeless k v : Timeless (gl_expired k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_fuel_timeless k a : Timeless (gl_fuel k a).
    Proof. unfold_defs. apply _. Qed.
    Global Instance th_obls_timeless i G q : Timeless (th_obls i G q).
    Proof. unfold_defs. apply _. Qed.
    Global Instance th_term_timeless i : Timeless (th_term i).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_timeless k v α : Timeless (wit k v α).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_credit_timeless k v a : Timeless (wit_credit k v a).
    Proof. unfold_defs. apply _. Qed.

    Global Instance gl_variant_contractive_1 N k v Q R : Contractive (λ P, gl_variant N k v P Q R).
    Proof.
      unfold_defs. rewrite /glG_elem /glG_version_lb /glG_variant /glG_variant_internal.
      solve_contractive.
    Qed.
    Global Instance gl_variant_contractive_2 N k v P R : Contractive (λ Q, gl_variant N k v P Q R).
    Proof.
      unfold_defs. rewrite /glG_elem /glG_version_lb /glG_variant /glG_variant_internal.
      solve_contractive.
    Qed.
    Global Instance gl_variant_contractive_3 N k v P Q : Contractive (λ R, gl_variant N k v P Q R).
    Proof.
      unfold_defs. rewrite /glG_elem /glG_version_lb /glG_variant /glG_variant_internal.
      solve_contractive.
    Qed.

    Local Open Scope ord.

    (** gl_fuel rules *)
    Lemma gl_fuel_eq k a0 a1 :
      (a0 == a1) → gl_fuel k a0 = gl_fuel k a1.
    Proof.
      unfold_defs. intros. rewrite (glG_fuel_eq (GL:=ord_ghost_lock_class) k a0 a1); auto.
    Qed.
    Lemma gl_fuel_eq_list L a0 a1 :
      (a0 == a1) →
      ([∗ list] i ∈ L, gl_fuel i a0)%I ≡ ([∗ list] i ∈ L, gl_fuel i a1)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite gl_fuel_eq; eauto. Qed.
    Lemma gl_fuel_eq_set L a0 a1 :
      a0 == a1 →
      ([∗ set] i ∈ L, gl_fuel i a0)%I ≡ ([∗ set] i ∈ L, gl_fuel i a1)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite gl_fuel_eq; eauto. Qed.

    Lemma gl_fuel_mon k a0 a1 :
      (a0 <= a1)%ord → gl_fuel k a1 ==∗ gl_fuel k a0.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply glG_fuel_mon.
    Qed.
    Lemma gl_fuel_mon_list L a0 a1 :
      a0 <= a1 →
      ([∗ list] i ∈ L, gl_fuel i a1) ⊢ |==> ([∗ list] i ∈ L, gl_fuel i a0).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_mon.
    Qed.
    Lemma gl_fuel_mon_set L a0 a1 :
      a0 <= a1 →
      ([∗ set] i ∈ L, gl_fuel i a1) ⊢ |==> ([∗ set] i ∈ L, gl_fuel i a0).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_mon.
    Qed.

    Lemma gl_fuel_split k a0 a1 :
      gl_fuel k (a0 ⊕ a1)%ord ⊣⊢ gl_fuel k a0 ∗ gl_fuel k a1.
    Proof.
      unfold_defs. rewrite glG_fuel_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((B1& P1)& (B2& P2))"; iFrame.
    Qed.
    Lemma gl_fuel_split_list L a0 a1 :
      ([∗ list] i ∈ L, gl_fuel i (a0 ⊕ a1)) ⊣⊢ ([∗ list] i ∈ L, gl_fuel i a0) ∗ ([∗ list] i ∈ L, gl_fuel i a1).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply gl_fuel_split.
    Qed.
    Lemma gl_fuel_split_set L a0 a1 :
      ([∗ set] i ∈ L, gl_fuel i (a0 ⊕ a1)) ⊣⊢ ([∗ set] i ∈ L, gl_fuel i a0) ∗ ([∗ set] i ∈ L, gl_fuel i a1).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply gl_fuel_split.
    Qed.

    Lemma gl_fuel_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → gl_fuel k a2 ==∗ gl_fuel k a0 ∗ gl_fuel k a1.
    Proof.
      unfold_defs. iIntros (Hle) "(#Be& P)".
      iMod (glG_fuel_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma gl_fuel_mon_split_list L a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ list] i ∈ L, gl_fuel i a2) ⊢ |==> ([∗ list] i ∈ L, gl_fuel i a0) ∗ ([∗ list] i ∈ L, gl_fuel i a1).
    Proof.
      iIntros (LE) "H". iPoseProof (gl_fuel_mon_list with "H") as ">H"; first done.
      by iApply gl_fuel_split_list.
    Qed.
    Lemma gl_fuel_mon_split_set L a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ set] i ∈ L, gl_fuel i a2) ⊢ |==> ([∗ set] i ∈ L, gl_fuel i a0) ∗ ([∗ set] i ∈ L, gl_fuel i a1).
    Proof.
      iIntros (LE) "H". iPoseProof (gl_fuel_mon_set with "H") as ">H"; first done.
      by iApply gl_fuel_split_set.
    Qed.

    Lemma gl_fuel_lt k a0 a1 :
      a0 < a1 →
      gl_fuel k a1 ⊢ |==> gl_fuel k a0 ∗ gl_fuel k Ord.one.
    Proof.
      unfold_defs. iIntros (Hlt) "(#Be& P)".
      iMod (glG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
      iFrame "P Be". apply ord_lt_one in H. iMod (glG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
    Qed.
    Lemma gl_fuel_lt_list L a0 a1 :
      a0 < a1 →
      ([∗ list] i ∈ L, gl_fuel i a1) ⊢ |==> ([∗ list] i ∈ L, gl_fuel i a0) ∗ ([∗ list] i ∈ L, gl_fuel i Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_lt.
    Qed.
    Lemma gl_fuel_lt_set L a0 a1 :
      a0 < a1 →
      ([∗ set] i ∈ L, gl_fuel i a1) ⊢ |==> ([∗ set] i ∈ L, gl_fuel i a0) ∗ ([∗ set] i ∈ L, gl_fuel i Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_lt.
    Qed.

    (** wit_credit rules *)
    Lemma wit_credit_eq k v a0 a1 :
      (a0 == a1) → wit_credit k v a1 = wit_credit k v a0.
    Proof.
      unfold_defs. intros. rewrite (witG_credit_eq (GL:=ord_ghost_lock_class) k v a0 a1); auto.
    Qed.
    Lemma wit_credit_mon k v a0 a1 :
      (a0 <= a1) → wit_credit k v a1 ==∗ wit_credit k v a0.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_credit_mon.
    Qed.
    Lemma wit_credit_split k v a0 a1 :
      wit_credit k v (a0 ⊕ a1)%ord ⊣⊢ wit_credit k v a0 ∗ wit_credit k v a1.
    Proof.
      unfold_defs. rewrite witG_credit_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((P1& B1)& (P2& B2))"; iFrame.
    Qed.
    Lemma wit_credit_mon_split k v a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord →
      wit_credit k v a2 ==∗ wit_credit k v a0 ∗ wit_credit k v a1.
    Proof.
      unfold_defs. iIntros (Hle) "(#Be& P)".
      iMod (witG_credit_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma wit_credit_lt k v a0 a1 :
      (a0 < a1) → wit_credit k v a1 ==∗ wit_credit k v a0 ∗ wit_credit k v Ord.one.
    Proof.
      unfold_defs. iIntros (Hlt) "(#Be& P)". iFrame "Be".
      iMod (witG_credit_lt with "P") as "[$ (%& %& C)]"; first done. 
      apply ord_lt_one in H. iMod (witG_credit_mon_split with "C") as "[_ $]"; done.
    Qed.

    (** wit rules *)
    Lemma wit_mon k v a0 a1 :
      (a0 <= a1)%ord → wit k v a0 ==∗ wit k v a1.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_witness_mon.
    Qed.
    Lemma wit_credit_compare k v a0 a1 :
      wit k v a0 -∗ wit_credit k v a1 -∗ ⌜ (a1 <= a0)%ord ⌝.
    Proof.
      unfold_defs. iIntros "(P& Be) (_& Cred)". iApply (witG_compare with "[$]").
    Qed.
    Lemma wit_credit_spend_gen k v a0 a1 :
      wit k v a0 -∗ wit_credit k v a1 ==∗ ∃ a2, ⌜ ((a1 ⊕ a2) <= a0)%ord ⌝ ∗ wit k v a2.
    Proof.
      unfold_defs. iIntros "($& Ow) (_& Oc)". iApply (witG_credit_spend_gen with "[$]").
    Qed.
    Lemma wit_credit_spend k v a0 a1 :
      (Ord.O < a1)%ord →
      wit k v a0 -∗ wit_credit k v a1 ==∗ ∃ a2, ⌜ (a2 < a0)%ord ⌝ ∗ wit k v a2.
    Proof.
      unfold_defs. iIntros (LT) "($& Ow) (_& Oc)". iApply (witG_credit_spend with "[$]"). done.
    Qed.
    Lemma wit_credit_spend_one k v a :
      wit k v a -∗ wit_credit k v Ord.one ==∗ ∃ a0, ⌜ (a0 < a)%ord ⌝ ∗ wit k v a0.
    Proof.
      iIntros "Ow Oc". iApply (wit_credit_spend with "Ow Oc"). apply Ord.S_pos.
    Qed.

    (** th_obls rules *)
    Lemma th_obls_disj i G1 G2 q1 q2 :
      th_obls i G1 q1 -∗ th_obls i G2 q2 -∗ (⌜ G1 ##ₘ G2 ⌝).
    Proof.
      unfold_defs. iIntros "(#Ge1& Gx1& T1& Es1) (#Ge2& Gx2& T2& Es2)".
      iPoseProof (globlG_obls_valid_2 with "[$T1 $T2]") as "%". destruct H.
      apply map_disjoint_dom in H0. done.
    Qed.

    Lemma th_obls_op_1 i G1 G2 q1 q2 :
      th_obls i G1 q1 -∗ th_obls i G2 q2 -∗ th_obls i (G1 ∪ G2) (q1 + q2).
    Proof.
      unfold_defs. iIntros "(#Ge1& Gx1& T1& Es1) (#Ge2& Gx2& T2& Es2)".
      iPoseProof (globlG_obls_valid_2 with "[$T1 $T2]") as "%". destruct H.
      iPoseProof (globlG_obls_op_1 with "[$T1 $T2]") as "T".
      iDestruct "Gx1" as "[Gx1 Gx1']". iDestruct "Gx2" as "[Gx2 Gx2']".
      iCombine "Gx1 Gx2" as "Gx". iCombine "Gx1' Gx2'" as "Gx'".
      iPoseProof (big_sepM_union with "[$Es1 $Es2]") as "$". 1: by apply map_disjoint_dom.
      iFrame "Ge1".
      rewrite -!Qp.div_add_distr. iCombine "Gx Gx'" as "Gx". rewrite -Qp.div_add_distr. iFrame "Gx".
      rewrite !dom_union_L. iFrame.
    Qed.
    Lemma th_obls_op_2 i G1 G2 q1 q2 :
      dom G1 ## dom G2 →
      th_obls i (G1 ∪ G2) (q1 + q2) -∗ (th_obls i G1 q1 ∗ th_obls i G2 q2).
    Proof.
      unfold_defs. iIntros (Hd) "(#Ge& Gx& T& Es)".
      rewrite dom_union_L. iPoseProof (globlG_obls_op_2 with "T") as "[$ $]"; first auto.
      iDestruct "Gx" as "[Gx Gx']". rewrite !Qp.div_add_distr.
      iDestruct "Gx" as "[Gx1 Gx2]". iDestruct "Gx'" as "[Gx1' Gx2']".
      iCombine "Gx1 Gx1'" as "$". iCombine "Gx2 Gx2'" as "$".
      rewrite big_sepM_union. 2: by apply map_disjoint_dom.
      iFrame "Ge". iFrame.
    Qed.

  End liveness_preds.

  Section fgupd.

    Lemma gl_alloc_obl E Θ i G q N ξ v P Q R :
      th_obls i G q -∗
      (▷ P) -∗
      |={E:Θ}=>g ∃ k, (⌜ G !! k = None ⌝) ∗
                     th_obls i (<[k:=v]>G) q ∗
                     gl_witfun k ξ ∗ gl k v ∗ gl_fuel k (Σ[ξ] v) ∗
                     gl_variant N k v P Q R ∗
                     wit k v (gupd_η (Σ[ξ] v)) ∗
                     ([∗ set] u ∈ set_seq 0 v, gl_done k u).
    Proof.
      unfold_defs. iIntros "(#Oe& Ox& Ob& OS) HP".
      iApply fupd_mask_intro. 1: set_solver. iIntros "Fupd".
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (glsat_alloc_ghost_lock_locked _ k ξ v i with "S") as "(S& #Gwf& #Ge& Gl& Gv& Gf& Go& #Gseq& %OStep)".
      1: auto.
      iDestruct "Gl" as "[Gl0 [Gl1 Gl']]".
      iMod (globl_alloc_obl with "[$S $O $Ob $Ge $Gl' $Go]") as "(S& O& %NinGk& Ob& Oo& Go)".
      iPoseProof (glG_version_get_lb _ v v with "Gv") as "#Gvl". 1: done.
      set (ηξ := (λ v, gupd_η (Σ[ξ] v)) : gl_witness).
      iMod (glwit_alloc_witness_locked _ k v ηξ with "[$W $Gseq $Gvl]") as "(W& #Wseq)".
      { apply glwit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iAssert (witG_witness k v (ηξ v))%I with "[Wseq]" as "#Ww".
      { rewrite set_seq_S_end_union_L. rewrite big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        iDestruct "Wseq" as "[Ww _]". rewrite big_sepS_singleton. eauto. }
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo0 [Oo1 Oo']]".
      iPoseProof (glassigned_add_obl with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. }
      iDestruct "Gl1" as "[Gl1 Gl']". iMod "Fupd" as "_".
      iMod (glG_variant_alloc_locked _ N _ _ _ P Q R with "[$Gl' $HP]") as "#GVar".
      iApply fupd_mask_intro. 1: set_solver. iIntros "Fupd".
      iExists (<[k:=(v, ghost_lock_locked (Σ[ξ] v) i)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 2. auto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (glwit_inv_alloc_locked _ Ω1 k W1 NinOk1 GWI _ _ _ W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W". iSplitL "A".
      { rewrite fmap_insert. simpl. iFrame. eauto. }
      iModIntro. iMod "Fupd" as "_". iModIntro.
      iExists k. iFrame "Oe Gwf Ge Gvl Ww GVar Gf Ox". iSplitR.
      { iPureIntro. apply not_elem_of_dom. auto. }
      iSplitL.
      { rewrite dom_insert_L. iFrame "Ob". iApply big_sepM_insert. 1: apply not_elem_of_dom; auto.
        iFrame "OS Ge Gv Go". iCombine "Gl0 Gl1" as "$". iCombine "Oo0 Oo1" as "$". }
      { iApply (big_sepS_impl with "Gseq"). iIntros "!> %% ($& $)". auto. }
    Qed.

    Lemma gl_alloc_done E Θ N ξ v P Q R :
      (▷ Q) -∗
      |={E:Θ}=>g ∃ k, gl_witfun k ξ ∗ gl k v ∗ gl_current k v ∗ gl_done k v ∗ gl_fuel k (Σ[ξ] v) ∗
                     gl_variant N k v P Q R ∗
                     wit k v (gupd_η (Σ[ξ] v)) ∗
                     ([∗ set] u ∈ set_seq 0 (S v), gl_done k u).
    Proof.
      unfold_defs. iIntros "HQ".
      iApply fupd_mask_intro. 1: set_solver. iIntros "Fupd".
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (glsat_alloc_ghost_lock_unlocked _ k ξ v with "S") as "(S& #Gwf& #Ge& #Gu& Gv& Gf& #Gseq& %OStep)".
      { auto. }
      iPoseProof (glG_version_get_lb _ v v with "Gv") as "#Gvl". 1: done.
      set (ηξ := (λ v, gupd_η (Σ[ξ] v)) : gl_witness).
      iAssert ([∗ set] u ∈ set_seq 0 (S v), glG_version_lb k u ∗ glG_unlocked k u)%I as "Gseq2".
      { rewrite set_seq_S_end_union_L big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        rewrite big_sepS_singleton. eauto. }
      iMod (glwit_alloc_witness_unlocked _ k v ηξ with "[$W $Gseq2]") as "(W& #Wseq)".
      { apply glwit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iAssert (witG_witness k v (ηξ v))%I with "[Wseq]" as "#Ww".
      { iClear "Gseq2". rewrite !set_seq_S_end_union_L !big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        iDestruct "Wseq" as "[Ww _]". rewrite big_sepS_singleton. eauto. }
      iPoseProof (glassigned_add_obl with "[$A $Ge Gu]") as "A".
      { iRight. iFrame "Gu". }
      iMod (glG_variant_alloc_unlocked _ N _ _ _ P Q R with "[$Gu $HQ]") as "#GVar".
      iModIntro. iExists (<[k:=(v, ghost_lock_unlocked)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 2. auto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (glwit_inv_alloc_unlocked _ Ω1 k W1 NinOk1 GWI _ W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W". iSplitL "A".
      { rewrite fmap_insert. simpl. iFrame. eauto. }
      iModIntro. iMod "Fupd" as "_". iModIntro.
      iExists k. iFrame "Gwf Ge Gvl Ww GVar Gf Gv Gu".
      iApply (big_sepS_impl with "Gseq2"). iIntros "!> %% ($& $)". auto.
    Qed.

    Lemma gl_lock E Θ N i G q k ξ v1 v2 I P1 Q1 R1 P2 Q2 R2 :
      v1 < v2 →
      ↑N ⊆ E →
      th_obls i G q -∗
      gl_current k v1 -∗
      gl_done k v1 -∗
      gl_variant N k v1 P1 Q1 R1 -∗
      gl_witfun k ξ -∗
      (I -∗ gl_current k v1 -∗ Q1 -∗ |={E ∖ ↑N:Θ}=>g (I ∗ gl_current k v1 ∗ (▷ R1) ∗ (▷ P2))) -∗
      |={E:Θ}=>g th_obls i (<[k:=v2]>G) q ∗
              gl k v2 ∗ gl_fuel k (Σ[ξ]{S v1, v2}) ∗
              gl_variant N k v2 P2 Q2 R2 ∗
              wit k v2 (gupd_η (Σ[ξ] v2)) ∗
              ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), wit k u (gupd_η (Σ[ξ] u))) ∗
              ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), gl_done k u).
    Proof.
      unfold_defs. iIntros (LTv MASK) "(#Oe& Ox& Ob& OS) ((#Ge& #Gvl1)& Gv1) (_& #Gu1) (_& #Gvar1) #Gwf UPD".
      iMod (glG_variant_acc_version_unlocked with "Gvar1 Gv1 Gu1") as "[H ACC]". 1: auto.

      TODO
      
glG_variant_acc_version_unlocked:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {glsatGS0 : glsatGS.glsatGS Σ} 
    {invGS0 : invGS Σ} (E : coPset) (N : namespace) (k : gl_id) (v : ghost_lock_version) 
    (q1 q2 : Qp) (P Q R : iProp Σ),
    ↑N ⊆ E
    → glG_variant N k v q1 P Q R -∗
      glG_version k v q2 -∗
      glG_unlocked k v ={E,E ∖ ↑N}=∗
      ▷ (glG_version k v q2 ∗ glG_unlocked k v ∗ glG_unlocked k v ∗ Q) ∗
      (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True)

      
      iApply fupd_mask_intro. 1: set_solver. iIntros "Fupd".
      iApply gupd_unfold.
      
      iMod (glsat_variant_lock _ k ξ v1 v2 i _ _ _ _ _ _ _ P2 Q2 R2 with "[$Gvar1 ]")
      

TODO

glsat_variant_lock:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {glsatGS0 : glsatGS.glsatGS Σ} 
    {invGS0 : invGS Σ} (Ω : ghost_locks) (k : gl_id) (ξ : gl_witness) (v1 v2 : nat) 
    (t : ghost_lock_owner) (q0 q1 : Qp) (E : coPset) (N : namespace) (P Q R : iProp Σ),
    (q0 + q1)%Qp = (1 / 2 + 1 / 2 / 2)%Qp
    → v1 < v2
      → ↑N ⊆ E
        → glG_variant N k v1 q0 P Q R ∗ glsat Ω ∗ glG_witfun k ξ ∗ glG_unlocked k v1 ∗
          glG_version k v1 (1 / 2 + 1 / 2 / 2)
          ⊢ |={E,E ∖ ↑N}=>
              ▷ ((glsat Ω ∗ glG_version k v1 (1 / 2 + 1 / 2 / 2) ∗ Q) ∗
                 (glsat Ω ∗ glG_version k v1 (1 / 2 + 1 / 2 / 2) ∗ ▷ R ∗ ▷ P ={
                  E ∖ ↑N,E}=∗
                  glsat (<[k:=(v2, ghost_lock_locked (Σ[ξ] v2) t)]> Ω) ∗ 
                  glG_locked k v2 q1 ∗ glG_version k v2 (1 / 2 + 1 / 2 / 2) ∗
                  glG_fuel k (Σ[ξ]{S v1, v2}) ∗ glG_owner k t (1 / 2 + 1 / 2 / 2) ∗
                  ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u) ∗
                  ⌜ghost_lock_step (v1, ghost_lock_unlocked) (v2, ghost_lock_locked (Σ[ξ] v2) t)⌝ ∗
                  glG_variant N k v2 q0 P Q R))
globl_alloc_obl:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {GLSAT : glsatGS.glsatGS Σ} 
    {globlGS0 : globlGS.globlGS Σ} (Ω : ghost_locks) (TP : gset positive) 
    (i : positive) (G : gl_ids) (q : Qp) (k : gl_id) (v : ghost_lock_version),
    glsat Ω ∗ globl TP ∗ globlG_obls i G q ∗ glG_elem k ∗ glG_locked k v (1 / 2 / 2 / 2) ∗
    glG_owner k i (1 / 2 + 1 / 2 / 2)
    ⊢ |==> glsat Ω ∗ globl TP ∗ ⌜k ∉ G⌝ ∗ globlG_obls i ({[k]} ∪ G) q ∗ globlG_owns i k v 1 ∗
        glG_owner k i (1 / 2 + 1 / 2 / 2 / 2 + 1 / 2 / 2 / 2 / 2)
glwit_lock:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {GLSAT : glsatGS.glsatGS Σ} 
    {glwitGS0 : glwitGS.glwitGS Σ} (W : witnesses) (k : gl_id) (v1 v2 : nat) 
    (ηξ : gl_witness),
    v1 < v2
    → W !! k = Some (v1, witness_unlocked)
      → glwit W ∗ ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u) ∗
        glG_version_lb k v2
        ⊢ |==> glwit (<[k:=(v2, witness_locked (ηξ v2))]> W) ∗ witG_witness k v2 (ηξ v2) ∗
            ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), witG_witness k u (ηξ u))
glassigned_add_obl:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {GLSAT : glsatGS.glsatGS Σ} 
    {globlGS0 : globlGS.globlGS Σ} (Gls : gmap gl_id ghost_lock_version) 
    (k : gl_id) (v : ghost_lock_version),
    glassigned Gls ∗ glG_elem k ∗
    ((∃ i : ghost_lock_owner, glG_owner k i (1 / 2 / 2 / 2 / 2) ∗ globlG_owns i k v (1 / 2 / 2))
     ∨ glG_unlocked k v)
    ⊢ glassigned (<[k:=v]> Gls)
glwit_inv_lock:
  ∀ {GL : ghost_lock_class} (η : ghost_lock_fuel → ghost_lock_fuel) (Ω : ghost_locks) 
    (k : gl_id) (v1 v2 : ghost_lock_version) (a : ghost_lock_fuel) (t : ghost_lock_owner) 
    (W1 : witnesses),
    Ω !! k = Some (v1, ghost_lock_unlocked)
    → glwit_inv η Ω W1
      → ghost_lock_step (v1, ghost_lock_unlocked) (v2, ghost_lock_locked a t)
        → ∀ W2 : witnesses,
            W1 ↓∘ W2
            → glwit_inv η (<[k:=(v2, ghost_lock_locked a t)]> Ω) W2
              → W1 !! k = Some (v1, witness_unlocked)
                ∧ wits_mon (<[k:=(v2, witness_locked (η a))]> W1) W2



glsat_variant_unlock:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {glsatGS0 : glsatGS.glsatGS Σ} 
    {invGS0 : invGS Σ} (Ω : ghost_locks) (k : gl_id) (v : ghost_lock_version) 
    (t : ghost_lock_owner) (q0 q1 : Qp) (E : coPset) (N : namespace) (P Q R : iProp Σ),
    (q0 + q1)%Qp = (1 / 2 + 1 / 2 / 2)%Qp
    → ↑N ⊆ E
      → glG_variant N k v q0 P Q R ∗ glsat Ω ∗ glG_elem k ∗ glG_locked k v q1 ∗
        glG_owner k t (1 / 2 + 1 / 2 / 2)
        ⊢ |={E,E ∖ ↑N}=>
            ▷ ((glsat Ω ∗ glG_locked k v (1 / 2 + 1 / 2 / 2) ∗ glG_owner k t (1 / 2 + 1 / 2 / 2) ∗ P) ∗
               (glsat Ω ∗ glG_locked k v (1 / 2 + 1 / 2 / 2) ∗ glG_owner k t (1 / 2 + 1 / 2 / 2) ∗
                ▷ Q ={E ∖ ↑N,E}=∗
                glsat (<[k:=(v, ghost_lock_unlocked)]> Ω) ∗ glG_unlocked k v ∗
                ⌜∀ a : ghost_lock_fuel,
                   ghost_lock_step (v, ghost_lock_locked a t) (v, ghost_lock_unlocked)⌝))
globl_delete_obl_frac:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {GLSAT : glsatGS.glsatGS Σ} 
    {globlGS0 : globlGS.globlGS Σ} (TP : gset positive) (i : positive) (G : gl_ids) 
    (q : Qp) (k : gl_id) (v : ghost_lock_version),
    k ∈ G
    → globl TP ∗ globlG_obls i G q ∗ globlG_owns i k v 1
      ⊢ |==> globl TP ∗ globlG_obls i (G ∖ {[k]}) q ∗ glG_locked k v (1 / 2 / 2 / 2) ∗
          glG_owner k i (1 / 2 / 2 / 2 / 2)
glwit_unlock:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {GLSAT : glsatGS.glsatGS Σ} 
    {glwitGS0 : glwitGS.glwitGS Σ} (W : witnesses) (k : gl_id) (v : ghost_lock_version) 
    (a : ghost_lock_fuel),
    W !! k = Some (v, witness_locked a)
    → glwit W ∗ glG_unlocked k v ⊢ glwit (<[k:=(v, witness_unlocked)]> W)
glassigned_delete_obl:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {GLSAT : glsatGS.glsatGS Σ} 
    {globlGS0 : globlGS.globlGS Σ} (Gls : gmap gl_id ghost_lock_version) 
    (k : gl_id) (v : ghost_lock_version),
    Gls !! k = Some v
    → glassigned Gls ⊢ glassigned (delete k Gls) ∗ glG_elem k ∗
      ((∃ i : ghost_lock_owner, glG_owner k i (1 / 2 / 2 / 2 / 2) ∗ globlG_owns i k v (1 / 2 / 2))
       ∨ glG_unlocked k v)
glwit_inv_unlock:
  ∀ {GL : ghost_lock_class} (η : ghost_lock_fuel → ghost_lock_fuel) (Ω : ghost_locks) 
    (k : gl_id) (v : ghost_lock_version) (a : ghost_lock_fuel) (t : ghost_lock_owner) 
    (W1 : witnesses),
    Ω !! k = Some (v, ghost_lock_locked a t)
    → glwit_inv η Ω W1
      → ghost_lock_step (v, ghost_lock_locked a t) (v, ghost_lock_unlocked)
        → ∀ W2 : witnesses,
            W1 ↓∘ W2
            → glwit_inv η (<[k:=(v, ghost_lock_unlocked)]> Ω) W2
              → ∃ b : ghost_lock_fuel,
                  W1 !! k = Some (v, witness_locked b)
                  ∧ wits_mon (<[k:=(v, witness_unlocked)]> W1) W2

     TODO

  Local Ltac unfold_defs :=
    try rewrite !wit_credit_unseal /wit_credit_def;
    try rewrite !wit_unseal /wit_def;
    try rewrite !th_term_unseal /th_term_def;
    try rewrite !th_obls_unseal /th_obls_def;
    try rewrite !gl_variant_unseal /gl_variant_def;
    try rewrite !gl_fuel_unseal /gl_fuel_def;
    try rewrite !gl_expired_unseal /gl_expired_def;
    try rewrite !gl_done_unseal /gl_done_def;
    try rewrite !gl_witfun_unseal /gl_witfun_def;
    try rewrite !gl_unseal /gl_def.


    Lemma obl_resolve E i G q k T P :
      k ∈ G →
      th_obls i G q -∗ oGoal k T P -∗
      (∀ σ Θ κs, state_interp σ Θ κs ={E,∅}=∗ (⌜ T σ ⌝ ∗ ▷ P) ∗ (oDone k ={∅,E}=∗ state_interp σ Θ κs)) -∗
      |={E}=>o th_obls i (G ∖ {[k]}) q ∗ oDone k.
    Proof.
      unfold_defs. iIntros (InGk) "(Tbs& Texi& #Tei& Tds) (#Bgk& #Bek) ACC".
      iIntros (???) "SI". iMod ("ACC" with "SI") as "[(%HT& HP) ACC]".
      iPoseProof (big_sepS_delete _ _ _ InGk with "Tds") as "[(_& Blk& Tok) Tds]". iFrame "Texi Tei Tds Bek".
      iModIntro. iApply oupd_unfold. iRight.
      rewrite /oproto. iIntros (??) "(S& T& A& N& %OW)".
      assert (Dom1 : dom Ω1 = dom W1).
      { eapply obl_wit_dom; eauto. }
      iPoseProof (osat_elem with "[$S $Bek]") as "%InOk".
      iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%& Bok& Tok2) | #Bdk])"; first eauto; cycle 1.
      { iPoseProof (oblG_live_done_false with "[$Blk $Bdk]") as "%F". done. }
      iPoseProof (othread_obls_open _ _ k G with "[$T $Tei $Tbs]") as "(Tbs& [Blk2 Bok2]& ACC2)"; first auto.
      iPoseProof (oblG_owner_agree with "[$Bok $Bok2]") as "(%Eq& %)". subst i0. clear H.
      iPoseProof ("ACC2" with "[$Blk2 $Bok2]") as "T".
      iCombine "Tok Tok2" as "Tok". iPoseProof (globlG_owns_frac_op _ _ _ _ 1 with "Tok") as "Tok".
      { rewrite -assoc Qp.div_2 Qp.div_2. done. }
      iMod (othread_delete_obl_frac with "[$T $Tbs $Tok]") as "(T& Tbs& Blk2& Bok2)"; first auto.
      iCombine "Blk Blk2" as "Blk". iPoseProof (oblG_live_div_2 with "Blk") as "Blk".
      iCombine "Bok Bok2" as "Bok". iPoseProof (oblG_owner_div_2 with "Bok") as "Bok".
      iPoseProof (osat_obl_is_live with "[$S $Bek $Blk]") as "(%& %LUOk)".
      iMod (osat_obl_resolve_one with "[$S $Bek $Bgk $HP $Blk $Bok]") as "[S #Bdk]".
      iPoseProof (oassigned_add_obl with "[$A $Bek Bdk]") as "A".
      { iRight. auto. }
      replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (dom Ω1); cycle 1.
      { apply union_difference_L. set_solver. }
      iModIntro.
      iExists (<[k:=odone T]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. eapply (obl_states_step_resolve _ _ _ (obl_cond_one k)).
        1: apply _.
        intro x. destruct (decide (x = k)).
        - subst. rewrite LUOk lookup_insert_eq. econstructor. split; intros; done.
        - rewrite lookup_insert_ne; auto. destruct (Ω1 !! x) eqn:LUx; econstructor. split; intros; done.
      }
      iIntros (W2 [ProgW OW2]).
      assert (ResolveW : W1 ↓ᵣ W2 | wit_cond_one k) by (eapply obl_wit_resolve; eauto).
      iMod (owitness_wit_resolve_one _ _ _ ResolveW with "[$N $Bdk]") as "N".
      iModIntro. rewrite dom_insert_L. replace ({[k]} ∪ dom Ω1) with (dom Ω1) by set_solver.
      iFrame. iSplitR; first done. iModIntro. iMod ("ACC" with "[$Bdk $Bek]") as "$".
      iModIntro. auto.
    Qed.

    Lemma obl_ea_done E k P :
      Persistent P →
      oEA k P -∗ oDone k -∗ |={E}=>o ▷ P.
    Proof.
      unfold_defs. iIntros (PersP) "(%& #Bgk) [#Bdk #Bek]".
      iIntros (???) "SI".
      iApply fupd_mask_intro. 1: set_solver. iIntros "close".
      iApply oupd_unfold. iRight.
      rewrite /oproto. iIntros (??) "(S& T& A& N& %OW)".
      iPoseProof (osat_done_open_pers with "[$S $Bgk $Bdk]") as "[S HP]".
      iModIntro. iExists Ω1. iSplitR; first done.
      iIntros (W2 (ProgW& OW2)).
      iPoseProof (owitness_obl_wit_rc_step_same_obl _ _ _ _ OW ProgW OW2 with "N") as "N".
      iModIntro. iFrame. iSplit; first done. iModIntro. by iMod "close".
    Qed.

  End fgupd.

End preds.
