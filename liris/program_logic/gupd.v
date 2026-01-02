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

(** Ghost lock predicates. *)
(* Ghost locks *)
Local Definition gl_def `{SI : indexT} `{@gupdGS SI GL Σ}
  k v : iProp Σ :=
  glG_elem k ∗ glG_version_lb k v.
Local Definition gl_aux : seal (@gl_def). Proof. by eexists. Qed.
Definition gl := gl_aux.(unseal).
Local Definition gl_unseal :
  @gl = @gl_def := gl_aux.(seal_eq).
Global Arguments gl {SI GL Σ _}.

Local Definition gl_witfun_def `{SI : indexT} `{@gupdGS SI GL Σ}
  k ξ : iProp Σ :=
  glG_witfun k ξ.
Local Definition gl_witfun_aux : seal (@gl_witfun_def). Proof. by eexists. Qed.
Definition gl_witfun := gl_witfun_aux.(unseal).
Local Definition gl_witfun_unseal :
  @gl_witfun = @gl_witfun_def := gl_witfun_aux.(seal_eq).
Global Arguments gl_witfun {SI GL Σ _}.

(* Local Definition gl_locked_def `{SI : indexT} `{@gupdGS SI GL Σ} *)
(*   k v : iProp Σ := *)
(*   gl k v ∗ glG_locked k v (1/2 + 1/2/2/2/2)%Qp. *)
(* Local Definition gl_locked_aux : seal (@gl_locked_def). Proof. by eexists. Qed. *)
(* Definition gl_locked := gl_locked_aux.(unseal). *)
(* Local Definition gl_locked_unseal : *)
(*   @gl_locked = @gl_locked_def := gl_locked_aux.(seal_eq). *)
(* Global Arguments gl_locked {SI GL Σ _}. *)

Local Definition gl_unlocked_def `{SI : indexT} `{@gupdGS SI GL Σ}
  k v : iProp Σ :=
  gl k v ∗ glG_unlocked k v.
Local Definition gl_unlocked_aux : seal (@gl_unlocked_def). Proof. by eexists. Qed.
Definition gl_unlocked := gl_unlocked_aux.(unseal).
Local Definition gl_unlocked_unseal :
  @gl_unlocked = @gl_unlocked_def := gl_unlocked_aux.(seal_eq).
Global Arguments gl_unlocked {SI GL Σ _}.

(* Local Definition gl_ver_def `{SI : indexT} `{@gupdGS SI GL Σ} *)
(*   k v : iProp Σ := *)
(*   gl k v ∗ glG_version k v (1/2 + 1/2/2)%Qp. *)
(* Local Definition gl_ver_aux : seal (@gl_ver_def). Proof. by eexists. Qed. *)
(* Definition gl_ver := gl_ver_aux.(unseal). *)
(* Local Definition gl_ver_unseal : *)
(*   @gl_ver = @gl_ver_def := gl_ver_aux.(seal_eq). *)
(* Global Arguments gl_ver {SI GL Σ _}. *)

Local Definition gl_pin_def `{SI : indexT} `{@gupdGS SI GL Σ}
  k v : iProp Σ :=
  gl k v ∗ glG_version_pin k v.
Local Definition gl_pin_aux : seal (@gl_pin_def). Proof. by eexists. Qed.
Definition gl_pin := gl_pin_aux.(unseal).
Local Definition gl_pin_unseal :
  @gl_pin = @gl_pin_def := gl_pin_aux.(seal_eq).
Global Arguments gl_pin {SI GL Σ _}.

Local Definition gl_done_def `{SI : indexT} `{@gupdGS SI GL Σ}
  k v : iProp Σ :=
  gl k v ∗ glG_version_done k v.
Local Definition gl_done_aux : seal (@gl_done_def). Proof. by eexists. Qed.
Definition gl_done := gl_done_aux.(unseal).
Local Definition gl_done_unseal :
  @gl_done = @gl_done_def := gl_done_aux.(seal_eq).
Global Arguments gl_done {SI GL Σ _}.

Local Definition gl_fuel_def `{SI : indexT} `{@gupdGS SI GL Σ}
  k a : iProp Σ :=
  glG_elem k ∗ glG_fuel k a.
Local Definition gl_fuel_aux : seal (@gl_fuel_def). Proof. by eexists. Qed.
Definition gl_fuel := gl_fuel_aux.(unseal).
Local Definition gl_fuel_unseal :
  @gl_fuel = @gl_fuel_def := gl_fuel_aux.(seal_eq).
Global Arguments gl_fuel {SI GL Σ _}.

Local Definition gl_variant_def `{SI : indexT} `{@gupdGS SI GL Σ}
  N k v (P Q R : iProp Σ) : iProp Σ :=
  gl k v ∗ glG_variant N k v (1/2/2/2/2)%Qp P Q R.
Local Definition gl_variant_aux : seal (@gl_variant_def). Proof. by eexists. Qed.
Definition gl_variant := gl_variant_aux.(unseal).
Local Definition gl_variant_unseal :
  @gl_variant = @gl_variant_def := gl_variant_aux.(seal_eq).
Global Arguments gl_variant {SI GL Σ _}.

(* Ghost lock obligations *)
Local Definition th_obls_def `{SI : indexT} `{@gupdGS SI GL Σ}
  i (G : gmap gl_id (gl_version * bool)) q : iProp Σ :=
  globlG_elem i ∗ globlG_exec i (q/2 + q/2/2)%Qp ∗ globlG_obls i (dom G) q ∗
  ([∗ map] k ↦ '(v, p) ∈ G,
     glG_elem k ∗ glG_locked k v (1/2 + 1/2/2/2/2)%Qp ∗
     (if (p : bool) then glG_version_pin k v else glG_version k v (1/2 + 1/2/2)%Qp) ∗
     glG_owner k i (1/2 + 1/2/2/2)%Qp ∗ globlG_owns i k v (1/2 + 1/2/2)%Qp).
Local Definition th_obls_aux : seal (@th_obls_def). Proof. by eexists. Qed.
Definition th_obls := th_obls_aux.(unseal).
Local Definition th_obls_unseal :
  @th_obls = @th_obls_def := th_obls_aux.(seal_eq).
Global Arguments th_obls {SI GL Σ _}.

Local Definition th_term_def `{SI : indexT} `{@gupdGS SI GL Σ}
  i : iProp Σ :=
  globlG_elem i ∗ globlG_term i.
Local Definition th_term_aux : seal (@th_term_def). Proof. by eexists. Qed.
Definition th_term := th_term_aux.(unseal).
Local Definition th_term_unseal :
  @th_term = @th_term_def := th_term_aux.(seal_eq).
Global Arguments th_term {SI GL Σ _}.

(* Ghost lock witnesses *)
Local Definition wit_def `{SI : indexT} `{@gupdGS SI GL Σ}
  k v α : iProp Σ :=
  gl k v ∗ witG_witness k v α.
Local Definition wit_aux : seal (@wit_def). Proof. by eexists. Qed.
Definition wit := wit_aux.(unseal).
Local Definition wit_unseal :
  @wit = @wit_def := wit_aux.(seal_eq).
Global Arguments wit {SI GL Σ _}.

Local Definition wit_credit_def `{SI : indexT} `{@gupdGS SI GL Σ}
  k v a : iProp Σ :=
  gl k v ∗ witG_credit k v a.
Local Definition wit_credit_aux : seal (@wit_credit_def). Proof. by eexists. Qed.
Definition wit_credit := wit_credit_aux.(unseal).
Local Definition wit_credit_unseal :
  @wit_credit = @wit_credit_def := wit_credit_aux.(seal_eq).
Global Arguments wit_credit {SI GL Σ _}.

TODO


Local Definition oGoal_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k T P : iProp Σ :=
  oblG_goal k T P ∗ obl k.
Local Definition oGoal_aux : seal (@oGoal_def). Proof. by eexists. Qed.
Definition oGoal := oGoal_aux.(unseal).
Local Definition oGoal_unseal :
  @oGoal = @oGoal_def := oGoal_aux.(seal_eq).
Global Arguments oGoal {SI Λ Σ _}.

(* Eventually, P always holds. *)
Local Definition oEA_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k P : iProp Σ :=
  (∃ T, oblG_goal k T P).
Local Definition oEA_aux : seal (@oEA_def). Proof. by eexists. Qed.
Definition oEA := oEA_aux.(unseal).
Local Definition oEA_unseal :
  @oEA = @oEA_def := oEA_aux.(seal_eq).
Global Arguments oEA {SI Λ Σ _}.

Local Definition oDone_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k : iProp Σ :=
  oblG_done k ∗ obl k.
Local Definition oDone_aux : seal (@oDone_def). Proof. by eexists. Qed.
Definition oDone := oDone_aux.(unseal).
Local Definition oDone_unseal :
  @oDone = @oDone_def := oDone_aux.(seal_eq).
Global Arguments oDone {SI Λ Σ _}.

Local Definition oFuel_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k a : iProp Σ :=
  oblG_fuel k a ∗ obl k.
Local Definition oFuel_aux : seal (@oFuel_def). Proof. by eexists. Qed.
Definition oFuel := oFuel_aux.(unseal).
Local Definition oFuel_unseal :
  @oFuel = @oFuel_def := oFuel_aux.(seal_eq).
Global Arguments oFuel {SI Λ Σ _}.

Local Definition oWit_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k ℵ : iProp Σ :=
  owitnessG_witness k ℵ ∗ obl k.
Local Definition oWit_aux : seal (@oWit_def). Proof. by eexists. Qed.
Definition oWit := oWit_aux.(unseal).
Local Definition oWit_unseal :
  @oWit = @oWit_def := oWit_aux.(seal_eq).
Global Arguments oWit {SI Λ Σ _}.

Local Definition oCred_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  k a : iProp Σ :=
  owitnessG_credit k a ∗ obl k.
Local Definition oCred_aux : seal (@oCred_def). Proof. by eexists. Qed.
Definition oCred := oCred_aux.(unseal).
Local Definition oCred_unseal :
  @oCred = @oCred_def := oCred_aux.(seal_eq).
Global Arguments oCred {SI Λ Σ _}.

Local Definition tHas_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  i G q : iProp Σ :=
  othreadG_obls i G q ∗ othreadG_exec i (q/2) ∗ othreadG_elem i ∗
  ([∗ set] k ∈ G, obl k ∗ oblG_live k (1/2/2)%Qp ∗ othreadG_owns i k (1/2 + 1/2/2)%Qp).
Local Definition tHas_aux : seal (@tHas_def). Proof. by eexists. Qed.
Definition tHas := tHas_aux.(unseal).
Local Definition tHas_unseal :
  @tHas = @tHas_def := tHas_aux.(seal_eq).
Global Arguments tHas {SI Λ Σ _}.

Local Definition tTerm_def `{SI : indexT} `{@lirisGS SI Λ Σ}
  i : iProp Σ :=
  othreadG_term i ∗ othreadG_elem i.
Local Definition tTerm_aux : seal (@tTerm_def). Proof. by eexists. Qed.
Definition tTerm := tTerm_aux.(unseal).
Local Definition tTerm_unseal :
  @tTerm = @tTerm_def := tTerm_aux.(seal_eq).
Global Arguments tTerm {SI Λ Σ _}.

Section lifting.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Local Ltac unfold_defs :=
    try rewrite !tTerm_unseal /tTerm_def;
    try rewrite !tHas_unseal /tHas_def;
    try rewrite !oCred_unseal /oCred_def;
    try rewrite !oWit_unseal /oWit_def;
    try rewrite !oFuel_unseal /oFuel_def;
    try rewrite !oDone_unseal /oDone_def;
    try rewrite !oEA_unseal /oEA_def;
    try rewrite !oGoal_unseal /oGoal_def;
    try rewrite !obl_unseal /obl_def.

  Section liveness_preds.

    Global Instance obl_persistent k : Persistent (obl k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance oGoal_persistent k T P : Persistent (oGoal k T P).
    Proof. unfold_defs. apply _. Qed.
    Global Instance oEA_persistent k P : Persistent (oEA k P).
    Proof. unfold_defs. apply _. Qed.
    Global Instance oDone_persistent k : Persistent (oDone k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance oWit_persistent k ℵ : Persistent (oWit k ℵ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance tTerm_persistent i : Persistent (tTerm i).
    Proof. unfold_defs. apply _. Qed.

    Global Instance obl_timeless k : Timeless (obl k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance oDone_timeless k : Timeless (oDone k).
    Proof. unfold_defs. apply _. Qed.
    Global Instance oFuel_timeless k a : Timeless (oFuel k a).
    Proof. unfold_defs. apply _. Qed.
    Global Instance oWit_timeless k ℵ : Timeless (oWit k ℵ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance oCred_timeless k a : Timeless (oCred k a).
    Proof. unfold_defs. apply _. Qed.
    Global Instance tHas_timeless i G q : Timeless (tHas i G q).
    Proof. unfold_defs. apply _. Qed.
    Global Instance tTerm_timeless i : Timeless (tTerm i).
    Proof. unfold_defs. apply _. Qed.

    Local Open Scope ord.

    (** oFuel rules *)
    Lemma oFuel_eq k a0 a1 :
      (a0 == a1) → oFuel k a0 = oFuel k a1.
    Proof.
      unfold_defs. intros. rewrite (oblG_fuel_eq k a0 a1); auto.
    Qed.
    Lemma oFuel_eq_list L a0 a1 :
      (a0 == a1) →
      ([∗ list] i ∈ L, oFuel i a0)%I ≡ ([∗ list] i ∈ L, oFuel i a1)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite oFuel_eq; eauto. Qed.
    Lemma oFuel_eq_set L a0 a1 :
      a0 == a1 →
      ([∗ set] i ∈ L, oFuel i a0)%I ≡ ([∗ set] i ∈ L, oFuel i a1)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite oFuel_eq; eauto. Qed.

    Lemma oFuel_mon k a0 a1 :
      (a0 <= a1)%ord → oFuel k a1 ==∗ oFuel k a0.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply oblG_fuel_mon.
    Qed.
    Lemma oFuel_mon_list L a0 a1 :
      a0 <= a1 →
      ([∗ list] i ∈ L, oFuel i a1) ⊢ |==> ([∗ list] i ∈ L, oFuel i a0).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oFuel_mon.
    Qed.
    Lemma oFuel_mon_set L a0 a1 :
      a0 <= a1 →
      ([∗ set] i ∈ L, oFuel i a1) ⊢ |==> ([∗ set] i ∈ L, oFuel i a0).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oFuel_mon.
    Qed.

    Lemma oFuel_split k a0 a1 :
      oFuel k (a0 ⊕ a1)%ord ⊣⊢ oFuel k a0 ∗ oFuel k a1.
    Proof.
      unfold_defs. rewrite oblG_fuel_split. iSplit.
      - iIntros "((P1& P2)& #Be)"; iFrame; eauto.
      - iIntros "((P1& B1)& (P2& B2))"; iFrame.
    Qed.
    Lemma oFuel_split_list L a0 a1 :
      ([∗ list] i ∈ L, oFuel i (a0 ⊕ a1)) ⊣⊢ ([∗ list] i ∈ L, oFuel i a0) ∗ ([∗ list] i ∈ L, oFuel i a1).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oFuel_split.
    Qed.
    Lemma oFuel_split_set L a0 a1 :
      ([∗ set] i ∈ L, oFuel i (a0 ⊕ a1)) ⊣⊢ ([∗ set] i ∈ L, oFuel i a0) ∗ ([∗ set] i ∈ L, oFuel i a1).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oFuel_split.
    Qed.

    Lemma oFuel_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → oFuel k a2 ==∗ oFuel k a0 ∗ oFuel k a1.
    Proof.
      unfold_defs. iIntros (Hle) "(P& #Be)".
      iMod (oblG_fuel_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma oFuel_mon_split_list L a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ list] i ∈ L, oFuel i a2) ⊢ |==> ([∗ list] i ∈ L, oFuel i a0) ∗ ([∗ list] i ∈ L, oFuel i a1).
    Proof.
      iIntros (LE) "H". iPoseProof (oFuel_mon_list with "H") as ">H"; first done.
      by iApply oFuel_split_list.
    Qed.
    Lemma oFuel_mon_split_set L a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ set] i ∈ L, oFuel i a2) ⊢ |==> ([∗ set] i ∈ L, oFuel i a0) ∗ ([∗ set] i ∈ L, oFuel i a1).
    Proof.
      iIntros (LE) "H". iPoseProof (oFuel_mon_set with "H") as ">H"; first done.
      by iApply oFuel_split_set.
    Qed.

    Lemma oFuel_lt k a0 a1 :
      a0 < a1 →
      oFuel k a1 ⊢ |==> oFuel k a0 ∗ oFuel k Ord.one.
    Proof.
      unfold_defs. iIntros (Hlt) "(P& #Be)".
      iMod (oblG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
      iFrame "P Be". apply ord_lt_one in H. iMod (oblG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
    Qed.
    Lemma oFuel_lt_list L a0 a1 :
      a0 < a1 →
      ([∗ list] i ∈ L, oFuel i a1) ⊢ |==> ([∗ list] i ∈ L, oFuel i a0) ∗ ([∗ list] i ∈ L, oFuel i Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply oFuel_lt.
    Qed.
    Lemma oFuel_lt_set L a0 a1 :
      a0 < a1 →
      ([∗ set] i ∈ L, oFuel i a1) ⊢ |==> ([∗ set] i ∈ L, oFuel i a0) ∗ ([∗ set] i ∈ L, oFuel i Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply oFuel_lt.
    Qed.

    (** oCred rules *)
    Lemma oCred_eq k a0 a1 :
      (a0 == a1)%ord → oCred k a1 = oCred k a0.
    Proof.
      unfold_defs. intros. rewrite (owitnessG_credit_eq k a0 a1); auto.
    Qed.
    Lemma oCred_mon k a0 a1 :
      (a0 <= a1)%ord → oCred k a1 ==∗ oCred k a0.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply owitnessG_credit_mon.
    Qed.
    Lemma oCred_split k a0 a1 :
      oCred k (a0 ⊕ a1)%ord ⊣⊢ oCred k a0 ∗ oCred k a1.
    Proof.
      unfold_defs. rewrite owitnessG_credit_split. iSplit.
      - iIntros "((P1& P2)& #Be)"; iFrame; eauto.
      - iIntros "((P1& B1)& (P2& B2))"; iFrame.
    Qed.
    Lemma oCred_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → oCred k a2 ==∗ oCred k a0 ∗ oCred k a1.
    Proof.
      unfold_defs. iIntros (Hle) "(P& #Be)".
      iMod (owitnessG_credit_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.

    (** oWit rules *)
    Lemma oWit_mon k a0 a1 :
      (a0 <= a1)%ord → oWit k a0 ==∗ oWit k a1.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply owitnessG_witness_mon.
    Qed.
    Lemma oWit_cred_compare k a0 a1 :
      oWit k a0 -∗ oCred k a1 -∗ ⌜ (a1 <= a0)%ord ⌝.
    Proof.
      unfold_defs. iIntros "(P& Be) (Cred& _)". iApply (owitnessG_compare with "[$]").
    Qed.
    Lemma oWit_cred_spend_gen k a0 a1 :
      oWit k a0 -∗ oCred k a1 ==∗ ∃ a2, ⌜ ((a1 ⊕ a2) <= a0)%ord ⌝ ∗ oWit k a2.
    Proof.
      unfold_defs. iIntros "(Ow& $) (Oc& _)". iApply (owitnessG_credit_spend_gen with "[$]").
    Qed.
    Lemma oWit_cred_spend k a0 a1 :
      (Ord.O < a1)%ord →
      oWit k a0 -∗ oCred k a1 ==∗ ∃ a2, ⌜ (a2 < a0)%ord ⌝ ∗ oWit k a2.
    Proof.
      unfold_defs. iIntros (LT) "(Ow& $) (Oc& _)". iApply (owitnessG_credit_spend with "[$]"). done.
    Qed.
    Lemma oWit_cred_spend_one k a :
      oWit k a -∗ oCred k Ord.one ==∗ ∃ a0, ⌜ (a0 < a)%ord ⌝ ∗ oWit k a0.
    Proof.
      iIntros "Ow Oc". iApply (oWit_cred_spend with "Ow Oc"). apply Ord.S_pos.
    Qed.

    (** tHas rules *)
    Lemma tHas_disj i G1 G2 q1 q2 :
      tHas i G1 q1 -∗ tHas i G2 q2 -∗ (⌜ G1 ## G2 ⌝).
    Proof.
      unfold_defs. iIntros "(T1& E1& #Te1& Es1) (T2& E2& #Te2& Es2)".
      rewrite elem_of_disjoint. iIntros (x IN1 IN2).
      iPoseProof (big_sepS_delete _ _ _ IN1 with "Es1") as "[(_&_&Tok1) _]".
      iPoseProof (big_sepS_delete _ _ _ IN2 with "Es2") as "[(_&_&Tok2) _]".
      iPoseProof (othreadG_owns_valid_2 with "[$Tok1 $Tok2]") as "%F".
      done.
    Qed.

    Lemma tHas_op_1 i G1 G2 q1 q2 :
      tHas i G1 q1 -∗ tHas i G2 q2 -∗ tHas i (G1 ∪ G2) (q1 + q2).
    Proof.
      unfold_defs. iIntros "(T1& E1& #Te1& Es1) (T2& E2& #Te2& Es2)".
      iPoseProof (othreadG_obls_valid_2 with "[$T1 $T2]") as "%". destruct H.
      iPoseProof (othreadG_obls_op_1 with "[$T1 $T2]") as "T". iFrame.
      iCombine "E1 E2" as "E". iPoseProof (othreadG_exec_frac_op with "E") as "E"; first reflexivity.
      rewrite Qp.div_add_distr. iFrame. iSplitR; auto.
      rewrite big_sepS_union; auto. iFrame.
    Qed.
    Lemma tHas_op_2 i G1 G2 q1 q2 :
      G1 ## G2 →
      tHas i (G1 ∪ G2) (q1 + q2) -∗ (tHas i G1 q1 ∗ tHas i G2 q2).
    Proof.
      unfold_defs. iIntros (Hd) "(T& E& #Te& Es)".
      iPoseProof (othreadG_obls_op_2 with "T") as "[T1 T2]"; first auto.
      rewrite Qp.div_add_distr. iPoseProof (othreadG_exec_frac_op _ (q1/2) (q2/2) with "E") as "[E1 E2]"; first auto.
      iFrame. iFrame "Te". rewrite -big_sepS_union; auto.
    Qed.

  End liveness_preds.

  Section foupd.

    Lemma obl_alloc E i G q T P a :
      tHas i G q -∗
      |={E}=>o ∃ k, ⌜ k ∉ G ⌝ ∗ tHas i ({[k]} ∪ G) q ∗ obl k ∗ oGoal k T P ∗ oEA k P ∗ oFuel k a ∗ oWit k (owfun a).
    Proof.
      unfold_defs. iIntros "(Tbs& Texi& #Tei& Tds)". iIntros (???) "SI".
      iApply fupd_mask_intro. 1: set_solver. iIntros "close".
      iApply oupd_unfold. iRight.
      rewrite /oproto. iIntros (??) "(S& T& A& N& %OW)".
      assert (∃ k, k ∉ dom Ω1).
      { exists (fresh (dom Ω1)). apply is_fresh. }
      assert (Dom1 : dom Ω1 = dom W1).
      { eapply obl_wit_dom; eauto. }
      destruct H as (k& Nink).
      iMod (osat_alloc_obl _ k i a T P with "S") as "(S& #Bgk& #Bek& Blk& Bok& Bfk)". 1: done.
      iPoseProof (oblG_owner_div_2 with "Bok") as "[Bok Bok2]".
      iMod (othread_alloc_obl with "[$S $T $Tbs $Bek $Blk $Bok2]") as "(S& T& %Nink2& Tbs& Tok& Blk)".
      iPoseProof (othreadG_owns_div_2 with "Tok") as "[Tok Tok2]".
      iPoseProof (othreadG_owns_div_2 with "Tok2") as "[Tok' Tok2]".
      iCombine "Tok Tok'" as "Tok". iPoseProof (othreadG_owns_frac_op with "Tok") as "Tok". 1: reflexivity.
      iPoseProof (oassigned_add_obl with "[$A $Bek Bok Tok2]") as "A".
      { iLeft. iFrame. }
      iMod (owitness_alloc_wit _ k (owfun a) with "N") as "[N #Nwk]".
      { rewrite -Dom1. done. }
      iModIntro. iFrame "S T". iSplitR.
      { iPureIntro. econstructor 2. eapply obl_states_step_alloc.
        exists k. eexists. split; last done. by apply not_elem_of_dom. }
      iIntros (W2 [ProgW OW2]).
      iMod (owitness_obl_wit_alloc with "N") as "N". 1: eapply Nink. all: eauto.
      iModIntro. iSplitL "A N".
      { rewrite dom_insert_L. iFrame. auto. }
      iApply oupd_unfold. iLeft. iModIntro. iMod "close" as "_". iModIntro.
      iFrame "SI Tbs Texi Tei Bek Bgk Bfk Nwk".
      iSplitR; first auto.
      iApply big_sepS_union. 1: set_solver.
      iFrame "Tds". iApply big_sepS_singleton. iFrame. auto.
    Qed.

    Lemma obl_resolve E i G q k T P :
      k ∈ G →
      tHas i G q -∗ oGoal k T P -∗
      (∀ σ Θ κs, state_interp σ Θ κs ={E,∅}=∗ (⌜ T σ ⌝ ∗ ▷ P) ∗ (oDone k ={∅,E}=∗ state_interp σ Θ κs)) -∗
      |={E}=>o tHas i (G ∖ {[k]}) q ∗ oDone k.
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
      iCombine "Tok Tok2" as "Tok". iPoseProof (othreadG_owns_frac_op _ _ _ _ 1 with "Tok") as "Tok".
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

  End foupd.
