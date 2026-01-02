From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.prelude Require Import options.
From liris.base_logic Require Export globl glwit.
From liris.algebra Require Import ordinal_wfocm.
Import uPred.

Class gupdGS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) :=
  GupdG {
      (** Invariants. *)
      #[global] gupd_invGS :: invGS Σ;
      (** Ghost locks. *)
      #[global] gupd_glsatGS :: glsatGS.glsatGS (GL:=GL) Σ;
      (** Ghost lock obligations assigned to threads. *)
      #[global] gupd_globlGS :: globlGS.globlGS Σ;
      (** Ghost lock witnesses. *)
      #[global] gupd_glwitGS :: glwitGS.glwitGS (GL:=GL) Σ;
      (** Fair scheduler function for witnesses. *)
      gupd_η : gl_fuel → gl_fuel;
    }.

Global Opaque gupd_invGS gupd_glsatGS gupd_globlGS gupd_glwitGS.
Global Arguments GupdG {SI GL Σ}.

Definition gproto `{SI : indexT} `{GL : ghost_lock_class} `{!gupdGS Σ}
  (Ω : ghost_locks) (W : witnesses) Θ : iProp Σ :=
  (glsat Ω ∗ globl Θ ∗ glassigned (fst <$> Ω) ∗ glwit W ∗ ⌜ glwit_inv gupd_η Ω W ⌝)%I.

(** Modality for updating ghost locks. *)
Definition gupd_pre `{SI : indexT} `{GL : ghost_lock_class} `{!gupdGS Σ}
  Θ (gupd : iPropO Σ -d> iPropO Σ) : iProp Σ -d> iPropO Σ :=
  λ P,
    ((|={∅}=> P) ∨
       (∀ (Ω1 : ghost_locks) (W1 : witnesses),
          (gproto Ω1 W1 Θ) ={∅}=∗
          ∃ Ω2, (⌜ (Ω1 ↪∘ Ω2) ⌝) ∗
                ∀ W2, (⌜ (W1 ↓∘ W2) ∧ glwit_inv gupd_η Ω2 W2 ⌝) ={∅}=∗
                      (gproto Ω2 W2 Θ) ∗ gupd P))%I.

Lemma gupd_pre_mono `{SI : indexT} `{GL : ghost_lock_class} `{!gupdGS Σ} Θ
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

Local Instance gupd_pre_mono' `{SI : indexT} `{GL : ghost_lock_class} `{!gupdGS Σ} Θ :
  BiMonoPred (gupd_pre Θ).
Proof.
  constructor.
  - iIntros (gupd1 gupd2 NE1 NE2) "#H". iApply gupd_pre_mono. iModIntro. iApply "H".
  - intros gupd Hgupd n P1 P2 ?. rewrite /gupd_pre.
    do 20 (f_equiv || done).
Qed.

(* take the least fixpoint of the above definition, with partial sate information *)
Local Definition gupd_def `{SI : indexT} `{GL : ghost_lock_class} `{!gupdGS Σ} Θ : iProp Σ → iProp Σ :=
  λ P, ((bi_least_fixpoint (gupd_pre Θ)) P)%I.
Local Definition gupd_aux : seal (@gupd_def). by eexists. Qed.
Definition gupd := gupd_aux.(unseal).
Arguments gupd {SI _ Σ _}.
Local Definition gupd_unseal : @gupd = @gupd_def := gupd_aux.(seal_eq).
Notation "'|={' Θ '}=>g' P" := (gupd Θ P) (at level 99, P at level 200, format "|={ Θ }=>g  P").

Section gupd.
  Context `{SI : indexT} `{GL : ghost_lock_class} `{!gupdGS Σ}.
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
Definition fgupd `{SI : indexT} `{GL : ghost_lock_class} `{!gupdGS Σ} E Θ : iPropO Σ -d> iPropO Σ :=
  (λ P, |={E,∅}=> |={Θ}=>g |={∅,E}=> P)%I.
Notation "'|={' E : Θ '}=>g' P" := (fgupd E Θ P) (at level 99, P at level 200, format "|={ E : Θ }=>g  P").

Section fgupd.
  Context `{SI : indexT} `{GL : ghost_lock_class} `{!gupdGS Σ}.
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

  Lemma fupd_fgupd_elim_lwp E Θ P :
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
    iIntros "_ [HP HPQ]". iApply fupd_fgupd_elim_lwp.
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
