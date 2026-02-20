From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From liris.base_logic Require Export globl glwit.
From liris.algebra Require Import ordinal_wfocm.
Import uPred.

Class gupdGS `{SI : indexT} (Σ : gFunctors) :=
  GupdG {
      (** Invariants. *)
      #[global] gupd_invGS :: invGS Σ;
      (** Ghost locks. *)
      #[global] gupd_glsatGS :: glsatGS.glsatGS Σ;
      (** Ghost lock obligations assigned to threads. *)
      #[global] gupd_globlGS :: globlGS.globlGS Σ;
      (** Ghost lock witnesses. *)
      #[global] gupd_glwitGS :: glwitGS.glwitGS Σ;
      (** Fair scheduler function for witnesses. *)
      #[global] fair_scheduler_fun :: ord_mono_fun_class;
    }.

Global Opaque gupd_invGS gupd_glsatGS gupd_globlGS gupd_glwitGS.
Global Arguments GupdG {SI Σ}.

Definition gproto `{SI : indexT} `{!gupdGS Σ}
  (Ω : ghost_locks) (W : witnesses) Θ : iProp Σ :=
  (glsat Ω ∗ globl Θ ∗ glassigned (fst <$> Ω) ∗ glwit W ∗ ⌜ glwit_inv Ω W ⌝)%I.

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
                ∀ W2, (⌜ (W1 ↓∘ W2) ∧ glwit_inv Ω2 W2 ⌝) ={∅}=∗
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
Arguments gupd {SI Σ _}.
Local Definition gupd_unseal : @gupd = @gupd_def := gupd_aux.(seal_eq).
Notation "'|=[' Θ ']=>g' P" := (gupd Θ P) (at level 99, P at level 200, format "|=[ Θ ]=>g  P").

Section gupd.
  Context `{SI : indexT} `{!gupdGS Σ}.
  Implicit Type Θ : (gset positive).

  Lemma gupd_unfold Θ P :
    (|=[Θ]=>g P) ⊣⊢ (gupd_pre Θ (gupd Θ) P).
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
    ⊢ (□ (∀ P, gupd_pre Θ (λ P, Ψ P ∧ |=[Θ]=>g P) P -∗ Ψ P)
       → ∀ P, (|=[Θ]=>g P) -∗ Ψ P)%I.
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
         → ∀ P, (|=[Θ]=>g P) -∗ Ψ P)%I.
  Proof.
    iIntros (HΨ) "#H". iApply gupd_ind_strong. iIntros "!>" (P) "Hgupd".
    iApply "H". iApply (gupd_pre_mono with "[] Hgupd").
    iIntros "!>" (?) "[$ _]".
  Qed.

  (** A fancy update can be turned into an obligation update. *)
  Lemma fupd_gupd Θ P : (|={∅}=> P) ⊢ (|=[Θ]=>g P).
  Proof.
    rewrite gupd_unfold. iIntros "Hupd". iLeft. done.
  Qed.

  (** We can always introduce a obligation update. *)
  Lemma gupd_intro Θ P : P ⊢ |=[Θ]=>g P.
  Proof.
    rewrite gupd_unfold. iIntros "HP". iLeft. iModIntro. done.
  Qed.

  (** We can always eliminate a fancy update. *)
  Lemma fupd_gupd_elim Θ P :
    (|={∅}=> |=[Θ]=>g P) ⊢ |=[Θ]=>g P.
  Proof.
    iIntros "H". iApply gupd_unfold.
    iRight. iIntros (??) "I". iMod "H".
    iModIntro. iExists Ω1. iSplitR; first done.
    iIntros (? (Prog& OW2)).
    iModIntro. rewrite /gproto. iDestruct "I" as "($& $& $& N& %OW1)".
    pose proof (glwit_inv_rc_step_same_gls _ _ _ OW1 Prog OW2).
    iPoseProof (glwit_mon _ _ H with "N") as "$".
    iFrame. done.
  Qed.

  (** We can combine two obligation updates into one. *)
  Lemma gupd_bind Θ P Q :
    (P -∗ |=[Θ]=>g Q) ⊢ (|=[Θ]=>g P) -∗ (|=[Θ]=>g Q).
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
  Lemma gupd_mono Θ P Q : (P ⊢ Q) → (|=[Θ]=>g P) ⊢ (|=[Θ]=>g Q).
  Proof.
    intros Hent. iApply gupd_bind.
    iIntros "P"; iApply gupd_intro; by iApply Hent.
  Qed.
  Lemma gupd_trans Θ P :  (|=[Θ]=>g |=[Θ]=>g P) ⊢ |=[Θ]=>g P.
  Proof.
    iIntros "HP". iApply gupd_bind; eauto.
  Qed.
  Lemma gupd_frame_r Θ P R : (|=[Θ]=>g P) ∗ R ⊢ |=[Θ]=>g P ∗ R.
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
    (|={∅}=> |=[Θ]=>g P) ⊢ (|=[Θ]=>g P).
  Proof.
    by erewrite fupd_gupd, gupd_trans.
  Qed.
  Lemma gupd_fupd_r Θ P :
    (|=[Θ]=>g |={∅}=> P) ⊢ (|=[Θ]=>g P).
  Proof.
    by erewrite fupd_gupd, gupd_trans.
  Qed.

  Lemma gupd_frame_l Θ R Q : (R ∗ |=[Θ]=>g Q) ⊢ |=[Θ]=>g R ∗ Q.
  Proof. rewrite !(comm _ R); apply gupd_frame_r. Qed.
  Lemma gupd_wand_l Θ P Q : (P -∗ Q) ∗ (|=[Θ]=>g P) ⊢ |=[Θ]=>g Q.
  Proof. by rewrite gupd_frame_l wand_elim_l. Qed.
  Lemma gupd_wand_r Θ P Q : (|=[Θ]=>g P) ∗ (P -∗ Q) ⊢ |=[Θ]=>g Q.
  Proof. by rewrite gupd_frame_r wand_elim_r. Qed.
  Lemma gupd_sep Θ P Q : (|=[Θ]=>g P) ∗ (|=[Θ]=>g Q) ⊢ |=[Θ]=>g P ∗ Q.
  Proof. by rewrite gupd_frame_r gupd_frame_l gupd_trans. Qed.
  Lemma gupd_idemp Θ P : (|=[Θ]=>g |=[Θ]=>g P) ⊣⊢ |=[Θ]=>g P.
  Proof.
    apply: anti_symm.
    - apply gupd_trans.
    - apply gupd_intro.
  Qed.

  Global Instance gupd_homomorphism Θ :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (gupd Θ).
  Proof. split; [split|]; try apply _; [apply gupd_sep | apply gupd_intro]. Qed.

  Lemma big_sepL_gupd {A} (Φ : nat → A → iProp Σ) Θ l :
    ([∗ list] k↦x ∈ l, |=[Θ]=>g Φ k x) ⊢ |=[Θ]=>g [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_gupd {A} `{Countable K} (Φ : K → A → iProp Σ) Θ l :
    ([∗ map] k↦x ∈ l, |=[Θ]=>g Φ k x) ⊢ |=[Θ]=>g [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_gupd `{Countable A} (Φ : A → iProp Σ) Θ l :
    ([∗ set]  x ∈ l, |=[Θ]=>g Φ x) ⊢ |=[Θ]=>g [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_gupd `{Countable A} (Φ : A → iProp Σ) Θ l :
    ([∗ mset] x ∈ l, |=[Θ]=>g Φ x) ⊢ |=[Θ]=>g [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_gupd Θ P : ◇ (|=[Θ]=>g P) ⊢ (|=[Θ]=>g ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using gupd_mono, or_intro_r.
    by rewrite -gupd_intro -or_intro_l.
  Qed.

  Lemma gproto_glwit_inv Ω W Θ :
    gproto Ω W Θ ⊢ ⌜ glwit_inv Ω W ⌝.
  Proof. iIntros "(_&_&_&_&$)". Qed.

  Lemma glwit_inv_exists_witnesses Ω1 Ω2 W1 :
    Ω1 ↪∘ Ω2 →
    glwit_inv Ω1 W1 →
    ∃ W2, W1 ↓∘ W2 ∧ glwit_inv Ω2 W2.
  Proof.
    intros Step Inv. destruct Step.
    { subst. exists W1. eauto. }
    inv H.
    - destruct H0 as (?&?&?&?&?&?). subst. inv H0.
      + pose proof Inv as Inv2. specialize (Inv2 x). rewrite H in Inv2. inv Inv2.
        destruct y. destruct H2, w; last done. subst. symmetry in H1.
        assert (Ord.O <= wit)%ord by (apply Ord.O_bot).
        apply ClassicOrd.le_eq_or_lt in H0. destruct H0; cycle 1.
        * exists W1. split; first auto. intros ?. destruct (decide (i = x)).
          { subst. rewrite lookup_insert_eq H1. econstructor. split; auto. rewrite -H0. apply Ord.O_bot. }
          { rewrite lookup_insert_ne; last auto. apply Inv. }
          (* FIXME : fail typeclass inference *)
        * exists (<[x:=(g, witness_locked (GL:=ord_ghost_lock_class) (Ord.O))]>W1). split.
          { econstructor 2. econstructor. exists x. do 2 eexists. split_and !; eauto. econstructor. auto. }
          { intros ?. destruct (decide (i = x)).
            - subst. rewrite !lookup_insert_eq. econstructor. split; auto. apply Ord.O_bot.
            - rewrite !lookup_insert_ne; eauto. }
      + pose proof Inv as Inv2. specialize (Inv2 x). rewrite H in Inv2. inv Inv2.
        destruct y. destruct H2, w; last done. subst. symmetry in H1.
        exists (<[x:=(g, witness_unlocked)]>W1). split.
        * econstructor 2. econstructor. exists x. do 2 eexists. split_and !; eauto. econstructor.
        * intros ?. destruct (decide (i = x)).
          { subst. rewrite !lookup_insert_eq. econstructor. auto. }
          { rewrite !lookup_insert_ne; eauto. }
      + pose proof Inv as Inv2. specialize (Inv2 x). rewrite H in Inv2. inv Inv2.
        destruct y. destruct H2, w; first done. subst. symmetry in H1. clear H2.
        exists (<[x:=(ver2, witness_locked (GL:=ord_ghost_lock_class) (η fuel))]>W1). split.
        * econstructor 2. econstructor. exists x. do 2 eexists. split_and !; eauto. econstructor. auto.
        * intros ?. destruct (decide (i = x)).
          { subst. rewrite !lookup_insert_eq. econstructor. split; done. }
          { rewrite !lookup_insert_ne; eauto. }
      + pose proof Inv as Inv2. specialize (Inv2 x). rewrite H in Inv2. inv Inv2.
        destruct y. destruct H2, w; first done. subst. symmetry in H1. clear H2.
        exists (<[x:=(ver2, witness_unlocked)]>W1). split.
        * econstructor 2. econstructor. exists x. do 2 eexists. split_and !; eauto. econstructor. auto.
        * intros ?. destruct (decide (i = x)).
          { subst. rewrite !lookup_insert_eq. econstructor. split; done. }
          { rewrite !lookup_insert_ne; eauto. }
    - pose proof Inv as Dom. apply glwit_inv_dom in Dom. destruct H0 as (k& v& LUO& [? | ?]).
      + destruct H as (a& t& ?). exists (<[k:=(v, witness_locked (GL:=ord_ghost_lock_class) (η a))]>W1). split.
        * econstructor 2. econstructor 2. exists k, v. split.
          { apply not_elem_of_dom. apply not_elem_of_dom in LUO. rewrite -Dom. auto. }
          left. eauto.
        * subst. intros ?. destruct (decide (i = k)).
          { subst. rewrite !lookup_insert_eq. econstructor. split; done. }
          { rewrite !lookup_insert_ne; eauto. }
      + exists (<[k:=(v, witness_unlocked)]>W1). split.
        * econstructor 2. econstructor 2. exists k, v. split.
          { apply not_elem_of_dom. apply not_elem_of_dom in LUO. rewrite -Dom. auto. }
          right. eauto.
        * subst. intros ?. destruct (decide (i = k)).
          { subst. rewrite !lookup_insert_eq. econstructor. split; done. }
          { rewrite !lookup_insert_ne; eauto. }
  Qed.

  Lemma gproto_gupd_steps Ω W Θ P :
    (|=[Θ]=>g P) -∗ gproto Ω W Θ ={∅}=∗ (P ∗ ∃ Ω' W', gproto Ω' W' Θ).
  Proof.
    iIntros "H". iRevert (Ω W). iRevert (P) "H".
    iApply gupd_ind_strong.
    { solve_proper. }
    iIntros "!> %P IH % % H". iDestruct "IH" as "[IH | IH]".
    { iMod "IH". by iFrame. }
    iPoseProof (gproto_glwit_inv with "H") as "%".
    iMod ("IH" with "H") as "(%&%& IH)".
    pose proof (glwit_inv_exists_witnesses _ _ _ H0 H). destruct H1 as (W2& ?).
    iMod ("IH" $! _ H1) as "[G [IH _]]". iApply ("IH" with "G").
  Qed.

  (* The following instances make the Iris Proof Mode aware of the
     obligation update. They are derived from the simpler rules above. *)
  (* Global Instance elim_fupd_gupd (p : bool) Θ P Q : *)
  (*   ElimModal True p false (|={∅}=> P) P (|=[Θ]=>g Q) (|=[Θ]=>g Q)%I. *)
  (* Proof. *)
  (*   rewrite /ElimModal bi.intuitionistically_if_elim //=. *)
  (*   rewrite fupd_gupd. *)
  (*   iIntros "_ [HP HPQ]". iApply (gupd_bind with "HPQ HP"). *)
  (* Qed. *)

  Global Instance elim_fupd_gupd (p : bool) E Θ P Q :
    ElimModal True p false (|={∅,E}=> P) P (|=[Θ]=>g Q) (|={E,∅}=> |=[Θ]=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_gupd_elim. iMod "HP".
    by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_gupd Θ P Q :
    AddModal (|={∅}=> P) P (|=[Θ]=>g Q).
  Proof.
    rewrite /AddModal; rewrite fupd_gupd; iIntros "[HP HPQ]".
    iApply (gupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_gupd p Θ P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|=[Θ]=>g Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply gupd_intro. Qed.

  Global Instance from_pure_gupd a Θ P φ :
    FromPure a P φ → FromPure a (|=[Θ]=>g P) φ.
  Proof. rewrite /FromPure=> <-. apply gupd_intro. Qed.

  Global Instance into_wand_gupd p q Θ R P Q :
    IntoWand false false R P Q → IntoWand p q (|=[Θ]=>g R) (|=[Θ]=>g P) (|=[Θ]=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite gupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_gupd_persistent p q Θ R P Q :
    IntoWand false q R P Q → IntoWand p q (|=[Θ]=>g R) P (|=[Θ]=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite gupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_gupd_args p q Θ R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|=[Θ]=>g P) (|=[Θ]=>g Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim gupd_wand_r.
  Qed.

  Global Instance from_sep_gupd Θ P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|=[Θ]=>g P) (|=[Θ]=>g Q1) (|=[Θ]=>g Q2).
  Proof. rewrite /FromSep=><-. apply gupd_sep. Qed.

  Global Instance from_or_gupd Θ P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|=[Θ]=>g P) (|=[Θ]=>g Q1) (|=[Θ]=>g Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply gupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_gupd {A} Θ P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|=[Θ]=>g P) (λ a, |=[Θ]=>g Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_gupd Θ P : IsExcept0 P → IsExcept0 (|=[Θ]=>g P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_gupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_gupd Θ P :
    FromModal True modality_id (|=[Θ]=>g P) (|=[Θ]=>g P) P.
  Proof. by rewrite /FromModal /= -gupd_intro. Qed.

  Global Instance elim_modal_gupd p Θ P Q :
    ElimModal True p false (|=[Θ]=>g P) P (|=[Θ]=>g Q) (|=[Θ]=>g Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim gupd_frame_r wand_elim_r gupd_trans.
  Qed.

  Global Instance add_modal_gupd Θ P Q : AddModal (|=[Θ]=>g P) P (|=[Θ]=>g Q).
  Proof. by rewrite /AddModal gupd_frame_r wand_elim_r gupd_trans. Qed.

  Global Instance frame_gupd p Θ R P Q :
    Frame p R P Q → Frame p R (|=[Θ]=>g P) (|=[Θ]=>g Q).
  Proof. rewrite /Frame=><-. by rewrite gupd_frame_l. Qed.

End gupd.

(* Wrapper to use fupd. *)
Definition fgupd `{SI : indexT} `{!gupdGS Σ} E Θ : iPropO Σ -d> iPropO Σ :=
  (λ P, |={E,∅}=> |=[Θ]=>g |={∅,E}=> P)%I.
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

  Lemma gupd_fgupd E Θ P : (|=[Θ]=>g P) ⊢ (|={E:Θ}=>g P).
  Proof.
    rewrite /fgupd. iIntros "Hupd".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose". iMod "Hupd".
    iModIntro. iMod "Hclose". by iFrame.
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

  Lemma gupd_fgupd_elim E Θ P :
    (|=[Θ]=>g |={E:Θ}=>g P) ⊢ |={E:Θ}=>g P.
  Proof.
    iIntros "H". iApply fupd_mask_intro. 1: set_solver.
    iIntros "Fupd". iMod "H". iMod "Fupd" as "_". done.
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

  Global Instance elim_gupd_fgupd (p : bool) E Θ P Q :
    ElimModal True p false (|=[Θ]=>g P) P (|={E:Θ}=>g Q) (|={E:Θ}=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply gupd_fgupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_fgupd E Θ P Q :
    AddModal (|={E}=> P) P (|={E:Θ}=>g Q).
  Proof.
    rewrite /AddModal; rewrite fupd_fgupd; iIntros "[HP HPQ]".
    iApply (fgupd_bind with "HPQ HP").
  Qed.

  Global Instance add_modal_gupd_fgupd E Θ P Q :
    AddModal (|=[Θ]=>g P) P (|={E:Θ}=>g Q).
  Proof.
    rewrite /AddModal; rewrite gupd_fgupd; iIntros "[HP HPQ]".
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
(** All Local Definitions are only for internal uses and users should not need them. *)
(* Ghost locks *)
Local Definition gl_layers_def `{SI : indexT} `{@gupdGS SI Σ}
  k ℓs : iProp Σ :=
  glG_layers k ℓs.
Local Definition gl_layers_aux : seal (@gl_layers_def). Proof. by eexists. Qed.
Definition gl_layers := gl_layers_aux.(unseal).
Local Definition gl_layers_unseal :
  @gl_layers = @gl_layers_def := gl_layers_aux.(seal_eq).
Global Arguments gl_layers {SI Σ _}.

Local Definition gl_def `{SI : indexT} `{@gupdGS SI Σ}
  k v : iProp Σ :=
  glG_elem k ∗ glG_version_lb k v ∗
  ([∗ set] u ∈ set_seq 0 v, glG_version_lb k u ∗ glG_unlocked k u).
Local Definition gl_aux : seal (@gl_def). Proof. by eexists. Qed.
Definition gl := gl_aux.(unseal).
Local Definition gl_unseal :
  @gl = @gl_def := gl_aux.(seal_eq).
Global Arguments gl {SI Σ _}.

Local Definition gl_locked_def `{SI : indexT} `{@gupdGS SI Σ}
  k v : iProp Σ :=
  gl k v ∗ glG_locked k v (1 / 2 / 2 / 2 / 2).
Local Definition gl_locked_aux : seal (@gl_locked_def). Proof. by eexists. Qed.
Definition gl_locked := gl_locked_aux.(unseal).
Local Definition gl_locked_unseal :
  @gl_locked = @gl_locked_def := gl_locked_aux.(seal_eq).
Global Arguments gl_locked {SI Σ _}.

Local Definition gl_done_def `{SI : indexT} `{@gupdGS SI Σ}
  k v : iProp Σ :=
  gl k v ∗ glG_unlocked k v.
Local Definition gl_done_aux : seal (@gl_done_def). Proof. by eexists. Qed.
Definition gl_done := gl_done_aux.(unseal).
Local Definition gl_done_unseal :
  @gl_done = @gl_done_def := gl_done_aux.(seal_eq).
Global Arguments gl_done {SI Σ _}.

Local Definition gl_current_def `{SI : indexT} `{@gupdGS SI Σ}
  k v q : iProp Σ :=
  gl k v ∗ glG_version k v (q/2 + q/2/2)%Qp.
Local Definition gl_current_aux : seal (@gl_current_def). Proof. by eexists. Qed.
Definition gl_current := gl_current_aux.(unseal).
Local Definition gl_current_unseal :
  @gl_current = @gl_current_def := gl_current_aux.(seal_eq).
Global Arguments gl_current {SI Σ _}.

Local Definition gl_expired_def `{SI : indexT} `{@gupdGS SI Σ}
  k v : iProp Σ :=
  gl_done k v ∗ glG_version_expired k v.
Local Definition gl_expired_aux : seal (@gl_expired_def). Proof. by eexists. Qed.
Definition gl_expired := gl_expired_aux.(unseal).
Local Definition gl_expired_unseal :
  @gl_expired = @gl_expired_def := gl_expired_aux.(seal_eq).
Global Arguments gl_expired {SI Σ _}.

Local Definition gl_fuel_val_def `{SI : indexT} `{@gupdGS SI Σ}
  k α : iProp Σ :=
  glG_elem k ∗ glG_fuel k α.
Local Definition gl_fuel_val_aux : seal (@gl_fuel_val_def). Proof. by eexists. Qed.
Local Definition gl_fuel_val := gl_fuel_val_aux.(unseal).
Local Definition gl_fuel_val_unseal :
  @gl_fuel_val = @gl_fuel_val_def := gl_fuel_val_aux.(seal_eq).
Global Arguments gl_fuel_val {SI Σ _}.

Local Definition gl_fuel_def `{SI : indexT} `{@gupdGS SI Σ}
  k ℓ μ : iProp Σ :=
  gl_fuel_val k (measure ℓ μ).
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

Local Definition gl_variant_cases_def `{SI : indexT} `{@gupdGS SI Σ}
  k v (P Q R : iProp Σ) : iProp Σ :=
  ((gl_locked k v ∗ P) ∨ (gl_done k v ∗ Q)) ∨ (gl_expired k v ∗ R).
Local Definition gl_variant_cases_aux : seal (@gl_variant_cases_def). Proof. by eexists. Qed.
Definition gl_variant_cases := gl_variant_cases_aux.(unseal).
Local Definition gl_variant_cases_unseal :
  @gl_variant_cases = @gl_variant_cases_def := gl_variant_cases_aux.(seal_eq).
Global Arguments gl_variant_cases {SI Σ _}.

(* Ghost lock obligations *)
Local Definition th_obls_def `{SI : indexT} `{@gupdGS SI Σ}
  i (G : gmap gl_id ghost_lock_version) q : iProp Σ :=
  globlG_elem i ∗ globlG_exec i (q/2 + q/2/2)%Qp ∗ globlG_obls i (dom G) q ∗
  ([∗ map] k ↦ v ∈ G,
     gl k v ∗ glG_locked k v (1/2 + 1/2/2/2/2)%Qp ∗
     gl_current k v (1/2)%Qp ∗
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
Local Definition wit_bound_def `{SI : indexT} `{@gupdGS SI Σ}
  k v α : iProp Σ :=
  gl k v ∗ witG_bound k v α.
Local Definition wit_bound_aux : seal (@wit_bound_def). Proof. by eexists. Qed.
Local Definition wit_bound := wit_bound_aux.(unseal).
Local Definition wit_bound_unseal :
  @wit_bound = @wit_bound_def := wit_bound_aux.(seal_eq).
Global Arguments wit_bound {SI Σ _}.

Local Definition wit_layer_def `{SI : indexT} `{@gupdGS SI Σ}
  k v ℓ : iProp Σ :=
  ∃ μ, wit_bound k v (η (measure ℓ μ)).
Local Definition wit_layer_aux : seal (@wit_layer_def). Proof. by eexists. Qed.
Definition wit_layer := wit_layer_aux.(unseal).
Local Definition wit_layer_unseal :
  @wit_layer = @wit_layer_def := wit_layer_aux.(seal_eq).
Global Arguments wit_layer {SI Σ _}.

Local Definition wit_def `{SI : indexT} `{@gupdGS SI Σ}
  k v a : iProp Σ :=
  gl k v ∗ witG_witness k v a.
Local Definition wit_aux : seal (@wit_def). Proof. by eexists. Qed.
Definition wit := wit_aux.(unseal).
Local Definition wit_unseal :
  @wit = @wit_def := wit_aux.(seal_eq).
Global Arguments wit {SI Σ _}.

(* Collection of fuels to support induction rules *)
Local Definition gl_fuels_def `{SI : indexT} `{@gupdGS SI Σ}
  α (F : gmap gl_id (layer * measurable_syntax)) : iProp Σ :=
  ([∗ map] f ↦ '(l, m) ∈ F, gl_fuel_val f ((measure l m) × α)%ord).
Local Definition gl_fuels_aux : seal (@gl_fuels_def). Proof. by eexists. Qed.
Local Definition gl_fuels := gl_fuels_aux.(unseal).
Local Definition gl_fuels_unseal :
  @gl_fuels = @gl_fuels_def := gl_fuels_aux.(seal_eq).
Global Arguments gl_fuels {SI Σ _}.

Local Definition embed_fuels_def `{SI : indexT} `{@gupdGS SI Σ}
  {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  (a : A) ℓ (F : gmap gl_id (layer * measurable_syntax)) : iProp Σ :=
  gl_fuels (measure ℓ (⟪wf_ltA, a⟫)%M) F.
Local Definition embed_fuels_aux : seal (@embed_fuels_def). Proof. by eexists. Qed.
Definition embed_fuels := embed_fuels_aux.(unseal).
Local Definition embed_fuels_unseal :
  @embed_fuels = @embed_fuels_def := embed_fuels_aux.(seal_eq).
Global Arguments embed_fuels {SI Σ _ A ltA}.

Local Definition wit_fuels_def `{SI : indexT} `{@gupdGS SI Σ}
  k v ℓ α (F : gmap gl_id (layer * measurable_syntax)) : iProp Σ :=
  ∃ μ, ⌜ (α <= η (measure ℓ μ))%ord ⌝ ∗ wit_bound k v α ∗
       gl_fuels α F.
Local Definition wit_fuels_aux : seal (@wit_fuels_def). Proof. by eexists. Qed.
Definition wit_fuels := wit_fuels_aux.(unseal).
Local Definition wit_fuels_unseal :
  @wit_fuels = @wit_fuels_def := wit_fuels_aux.(seal_eq).
Global Arguments wit_fuels {SI Σ _}.

Section preds.
  Context `{SI : indexT} `{!gupdGS Σ}.

  Local Ltac unfold_defs :=
    try rewrite !wit_fuels_unseal /wit_fuels_def;
    try rewrite !embed_fuels_unseal /embed_fuels_def;
    try rewrite !gl_fuels_unseal /gl_fuels_def;
    try rewrite !wit_unseal /wit_def;
    try rewrite !wit_layer_unseal /wit_layer_def;
    try rewrite !wit_bound_unseal /wit_bound_def;
    try rewrite !th_term_unseal /th_term_def;
    try rewrite !th_obls_unseal /th_obls_def;
    try rewrite !gl_variant_cases_unseal /gl_variant_cases_def;
    try rewrite !gl_variant_unseal /gl_variant_def;
    try rewrite !gl_fuel_unseal /gl_fuel_def;
    try rewrite !gl_fuel_val_unseal /gl_fuel_val_def;
    try rewrite !gl_expired_unseal /gl_expired_def;
    try rewrite !gl_current_unseal /gl_current_def;
    try rewrite !gl_done_unseal /gl_done_def;
    try rewrite !gl_locked_unseal /gl_locked_def;
    try rewrite !gl_layers_unseal /gl_layers_def;
    try rewrite !gl_unseal /gl_def.

  Local Ltac unfold_gl_fuel :=
    try rewrite !gl_fuel_unseal /gl_fuel_def.

  Section liveness_preds.

    (** Instances *)
    Global Instance gl_persistent k v : Persistent (gl k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_layers_persistent k ℓ : Persistent (gl_layers k ℓ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_done_persistent k v : Persistent (gl_done k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_expired_persistent k v : Persistent (gl_expired k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_variant_persistent N k v P Q R : Persistent (gl_variant N k v P Q R).
    Proof. unfold_defs. apply _. Qed.
    Global Instance th_term_persistent i : Persistent (th_term i).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_bound_persistent k v α : Persistent (wit_bound k v α).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_layer_persistent k v ℓ : Persistent (wit_layer k v ℓ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_fuels_empty_persistent α : Persistent (gl_fuels α ∅).
    Proof. unfold_defs. apply _. Qed.
    Global Instance embed_fuels_empty_persistent {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ :
      Persistent (embed_fuels wf_ltA a ℓ ∅).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_fuels_empty_persistent k v ℓ α : Persistent (wit_fuels k v ℓ α ∅).
    Proof. unfold_defs. apply _. Qed.

    Global Instance gl_timeless k v : Timeless (gl k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_layers_timeless k ℓ : Timeless (gl_layers k ℓ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_locked_timeless k v : Timeless (gl_locked k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_done_timeless k v : Timeless (gl_done k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_current_timeless k v q : Timeless (gl_current k v q).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_expired_timeless k v : Timeless (gl_expired k v).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_fuel_val_timeless k α : Timeless (gl_fuel_val k α).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_fuel_timeless k ℓ μ : Timeless (gl_fuel k ℓ μ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_variant_cases_timeless k v P Q R :
      Timeless P → Timeless Q → Timeless R →
      Timeless (gl_variant_cases k v P Q R).
    Proof. intros. unfold_defs. apply _. Qed.
    Global Instance th_obls_timeless i G q : Timeless (th_obls i G q).
    Proof. unfold_defs. apply _. Qed.
    Global Instance th_term_timeless i : Timeless (th_term i).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_bound_timeless k v α : Timeless (wit_bound k v α).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_layer_timeless k v ℓ : Timeless (wit_layer k v ℓ).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_timeless k v a : Timeless (wit k v a).
    Proof. unfold_defs. apply _. Qed.
    Global Instance gl_fuels_timeless α F : Timeless (gl_fuels α F).
    Proof. unfold_defs. apply _. Qed.
    Global Instance embed_fuels_empty_timeless {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ :
      Timeless (embed_fuels wf_ltA a ℓ ∅).
    Proof. unfold_defs. apply _. Qed.
    Global Instance wit_fuels_timeless k v ℓ α F : Timeless (wit_fuels k v ℓ α F).
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

    Global Instance gl_variant_ne_1 N k v Q R : NonExpansive (λ P, gl_variant N k v P Q R).
    Proof. apply _. Qed.
    Global Instance gl_variant_ne_2 N k v P R : NonExpansive (λ Q, gl_variant N k v P Q R).
    Proof. apply _. Qed.
    Global Instance gl_variant_ne_3 N k v P Q : NonExpansive (λ R, gl_variant N k v P Q R).
    Proof. apply _. Qed.

    Global Instance gl_variant_proper_1 N k v Q R : Proper (equiv ==> equiv) (λ P, gl_variant N k v P Q R).
    Proof.
      unfold_defs. repeat intro. rewrite /glG_variant /glG_variant_internal H. done.
    Qed.
    Global Instance gl_variant_proper_2 N k v P R : Proper (equiv ==> equiv) (λ Q, gl_variant N k v P Q R).
    Proof.
      unfold_defs. repeat intro. rewrite /glG_variant /glG_variant_internal H. done.
    Qed.
    Global Instance gl_variant_proper_3 N k v P Q : Proper (equiv ==> equiv) (λ R, gl_variant N k v P Q R).
    Proof.
      unfold_defs. repeat intro. rewrite /glG_variant /glG_variant_internal H. done.
    Qed.

    Global Instance gl_current_fractional k v :
      Fractional (gl_current k v).
    Proof.
      rewrite !gl_current_unseal /gl_current_def. intros p q. iSplit.
      - iIntros "(#$& [Gv1 Gv2])". rewrite !Qp.div_add_distr.
        iDestruct "Gv1" as "[Gv1 Gv1']". iDestruct "Gv2" as "[Gv2 Gv2']".
        iCombine "Gv1 Gv2" as "$". iCombine "Gv1' Gv2'" as "$".
      - iIntros "((#$& [Gv1 Gv2])& _& [Gv3 Gv4])". rewrite !Qp.div_add_distr.
        iCombine "Gv1 Gv3" as "Gv1". iSplitL "Gv1"; iFrame. iSplitR "Gv4"; iFrame.
    Qed.
    Global Instance gl_current_as_fractional k v q :
      AsFractional (gl_current k v q) (gl_current k v) q.
    Proof. split; [auto|apply _]. Qed.

    (** gl rules *)
    Local Lemma gl_history_mon k v1 v2 :
      v1 ≤ v2 →
      ([∗ set] u ∈ set_seq 0 v2, glG_version_lb k u ∗ glG_unlocked k u) -∗
      ([∗ set] u ∈ set_seq 0 v1, glG_version_lb k u ∗ glG_unlocked k u).
    Proof.
      intros Hv. induction Hv; iIntros "#Gseq".
      { auto. }
      rewrite set_seq_S_end_union_L. iPoseProof (big_sepS_union with "Gseq") as "[H1 H2]".
      { apply set_seq_S_end_disjoint. }
      iApply IHHv. auto.
    Qed.

    Local Lemma gl_history_add k v1 v2 :
      v1 < v2 →
      ([∗ set] u ∈ set_seq 0 (S v1), glG_version_lb k u ∗ glG_unlocked k u) -∗
      ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u) -∗
      ([∗ set] u ∈ set_seq 0 v2, glG_version_lb k u ∗ glG_unlocked k u).
    Proof.
      iIntros (Hv) "#Seq1 #Seq2".
      replace (set_seq 0 v2) with (set_seq 0 ((S v1) + (v2 - v1 - 1)) : gset _); cycle 1.
      { replace ((S v1) + (v2 - v1 - 1)) with v2 by lia. done. }
      rewrite (set_seq_add_L _ (S v1)). iApply big_sepS_union.
      { apply set_seq_add_disjoint. }
      auto.
    Qed.

    (** gl_locked and gl_done rules *)
    Lemma gl_locked_done_false k v :
      gl_locked k v -∗ gl_done k v -∗ False.
    Proof.
      unfold_defs. iIntros "((#Ge& #Gvl& GHis)& Gl) (_& #Gu)".
      iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    Qed.

    (* TODO : more lemmas? *)

    (** gl_current and gl_expired rules *)
    Lemma gl_current_expired_false k v q :
      gl_current k v q -∗ gl_expired k v -∗ False.
    Proof.
      unfold_defs. iIntros "((#Ge& #Gvl)& Gv) (_& #Gve)".
      iPoseProof (glG_version_expired_valid with "[$Gv $Gve]") as "%". lia.
    Qed.

    Lemma gl_expired_get k v1 v2 :
      (v1 < v2) →
      gl k v2 ⊢ gl_expired k v1.
    Proof.
      unfold_defs. iIntros (LT) "(#Ge& #Gvl& #Seq)". iFrame "Ge".
      iPoseProof (glG_version_get_expired _ v2 v1 with "Gvl") as "$". 1: auto.
      iPoseProof (gl_history_mon _ v1 v2 with "Seq") as "#Seq2". 1: lia.
      iFrame "Seq2".
      iPoseProof (big_sepS_delete _ _ v1 with "Seq") as "[$ _]".
      apply elem_of_set_seq. lia.
    Qed.

    (* TODO : more lemmas? *)

    Local Open Scope ord.

    (** gl_fuel_val rules *)
    Lemma gl_fuel_val_eq k a0 a1 :
      (a0 == a1) → gl_fuel_val k a0 = gl_fuel_val k a1.
    Proof.
      unfold_defs. intros. rewrite (glG_fuel_eq k a0 a1); auto.
    Qed.
    Lemma gl_fuel_val_eq_list K a0 a1 :
      (a0 == a1) →
      ([∗ list] k ∈ K, gl_fuel_val k a0)%I ≡ ([∗ list] k ∈ K, gl_fuel_val k a1)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite gl_fuel_val_eq; eauto. Qed.
    Lemma gl_fuel_val_eq_set K a0 a1 :
      a0 == a1 →
      ([∗ set] k ∈ K, gl_fuel_val k a0)%I ≡ ([∗ set] k ∈ K, gl_fuel_val k a1)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite gl_fuel_val_eq; eauto. Qed.

    Lemma gl_fuel_val_mon k a0 a1 :
      (a0 <= a1)%ord → gl_fuel_val k a1 ==∗ gl_fuel_val k a0.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply glG_fuel_mon.
    Qed.
    Lemma gl_fuel_val_mon_list K a0 a1 :
      a0 <= a1 →
      ([∗ list] k ∈ K, gl_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, gl_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_val_mon.
    Qed.
    Lemma gl_fuel_val_mon_set K a0 a1 :
      a0 <= a1 →
      ([∗ set] k ∈ K, gl_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, gl_fuel_val k a0).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_val_mon.
    Qed.

    Lemma gl_fuel_val_add k a0 a1 :
      gl_fuel_val k (a0 ⊕ a1)%ord ⊣⊢ gl_fuel_val k a0 ∗ gl_fuel_val k a1.
    Proof.
      unfold_defs. rewrite glG_fuel_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((B1& P1)& (B2& P2))"; iFrame.
    Qed.
    Lemma gl_fuel_val_add_list K a0 a1 :
      ([∗ list] k ∈ K, gl_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ list] k ∈ K, gl_fuel_val k a0) ∗ ([∗ list] k ∈ K, gl_fuel_val k a1).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply gl_fuel_val_add.
    Qed.
    Lemma gl_fuel_val_add_set K a0 a1 :
      ([∗ set] k ∈ K, gl_fuel_val k (a0 ⊕ a1)) ⊣⊢ ([∗ set] k ∈ K, gl_fuel_val k a0) ∗ ([∗ set] k ∈ K, gl_fuel_val k a1).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply gl_fuel_val_add.
    Qed.

    Lemma gl_fuel_val_mon_split k a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord → gl_fuel_val k a2 ==∗ gl_fuel_val k a0 ∗ gl_fuel_val k a1.
    Proof.
      unfold_defs. iIntros (Hle) "(#Be& P)".
      iMod (glG_fuel_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma gl_fuel_val_mon_split_list K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ list] k ∈ K, gl_fuel_val k a2) ⊢ |==> ([∗ list] k ∈ K, gl_fuel_val k a0) ∗ ([∗ list] k ∈ K, gl_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (gl_fuel_val_mon_list with "H") as ">H"; first done.
      by iApply gl_fuel_val_add_list.
    Qed.
    Lemma gl_fuel_val_mon_split_set K a0 a1 a2 :
      (a0 ⊕ a1) <= a2 →
      ([∗ set] k ∈ K, gl_fuel_val k a2) ⊢ |==> ([∗ set] k ∈ K, gl_fuel_val k a0) ∗ ([∗ set] k ∈ K, gl_fuel_val k a1).
    Proof.
      iIntros (LE) "H". iPoseProof (gl_fuel_val_mon_set with "H") as ">H"; first done.
      by iApply gl_fuel_val_add_set.
    Qed.

    Lemma gl_fuel_val_lt k a0 a1 :
      a0 < a1 →
      gl_fuel_val k a1 ⊢ |==> gl_fuel_val k a0 ∗ gl_fuel_val k Ord.one.
    Proof.
      unfold_defs. iIntros (Hlt) "(#Be& P)".
      iMod (glG_fuel_lt with "P") as "(P& %& %& H)". 1: done.
      iFrame "P Be". apply ord_lt_one in H. iMod (glG_fuel_mon_split _ _ _ _ with "H") as "[_ $]"; done.
    Qed.
    Lemma gl_fuel_val_lt_list K a0 a1 :
      a0 < a1 →
      ([∗ list] k ∈ K, gl_fuel_val k a1) ⊢ |==> ([∗ list] k ∈ K, gl_fuel_val k a0) ∗ ([∗ list] k ∈ K, gl_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_val_lt.
    Qed.
    Lemma gl_fuel_val_lt_set K a0 a1 :
      a0 < a1 →
      ([∗ set] k ∈ K, gl_fuel_val k a1) ⊢ |==> ([∗ set] k ∈ K, gl_fuel_val k a0) ∗ ([∗ set] k ∈ K, gl_fuel_val k Ord.one).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_val_lt.
    Qed.

    Lemma gl_fuel_val_mult k a0 a1 b :
      (a0 < a1)%ord →
      gl_fuel_val k (b × a1)%ord ⊢ |==> gl_fuel_val k (b × a0) ∗ gl_fuel_val k b.
    Proof.
      unfold_defs. intros LT. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (glG_fuel_mon _ ((b × a0) ⊕ b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_mult_r; eauto. rewrite Jacobsthal.mult_S Hessenberg.add_comm. done. }
      by iDestruct (glG_fuel_split with "Gf") as "[$ $]".
    Qed.
    Lemma gl_fuel_val_mult_list K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ list] k ∈ K, gl_fuel_val k (b × a1))
      ⊢ |==> ([∗ list] k ∈ K, gl_fuel_val k (b × a0)) ∗ ([∗ list] k ∈ K, gl_fuel_val k b).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply gl_fuel_val_mult. auto.
    Qed.
    Lemma gl_fuel_val_mult_set K a0 a1 b :
      (a0 < a1)%ord →
      ([∗ set] k ∈ K, gl_fuel_val k (b × a1))
      ⊢ |==> ([∗ set] k ∈ K, gl_fuel_val k (b × a0)) ∗ ([∗ set] k ∈ K, gl_fuel_val k b).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply gl_fuel_val_mult. auto.
    Qed.

    Lemma gl_fuel_val_expn k a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      gl_fuel_val k (b ↑ a1)%ord ⊢ |==> gl_fuel_val k ((b ↑ a0) × b).
    Proof.
      unfold_defs. intros LT Pos. iIntros "[#Ge Gf]". iFrame "Ge".
      apply Ord.S_supremum in LT. iMod (glG_fuel_mon _ ((b ↑ a0) × b)%ord with "Gf") as "Gf".
      { etransitivity; last eapply Jacobsthal.le_expn_r; eauto. rewrite Jacobsthal.expn_S; done. }
      done.
    Qed.
    Lemma gl_fuel_val_expn_list K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ list] k ∈ K, gl_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ list] k ∈ K, gl_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply gl_fuel_val_expn; auto.
    Qed.
    Lemma gl_fuel_val_expn_set K a0 a1 b :
      (a0 < a1)%ord →
      (Ord.O < b)%ord →
      ([∗ set] k ∈ K, gl_fuel_val k (b ↑ a1)) ⊢ |==> ([∗ set] k ∈ K, gl_fuel_val k ((b ↑ a0) × b)).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply gl_fuel_val_expn; auto.
    Qed.

    (** gl_fuel rules *)
    Lemma gl_fuel_unfold k ℓ μ :
      gl_fuel k ℓ μ = gl_fuel_val k (measure ℓ μ).
    Proof. rewrite gl_fuel_unseal /gl_fuel_def. auto. Qed.

    Lemma gl_fuel_eq k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) → gl_fuel k ℓ1 μ1 = gl_fuel k ℓ2 μ2.
    Proof.
      unfold_gl_fuel. intros. rewrite (gl_fuel_val_eq k _ _ H); auto.
    Qed.
    Lemma gl_fuel_eq_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) →
      ([∗ list] k ∈ K, gl_fuel k ℓ1 μ1)%I ≡ ([∗ list] k ∈ K, gl_fuel k ℓ2 μ2)%I.
    Proof. intros. apply big_opL_proper. intros. erewrite gl_fuel_eq; eauto. Qed.
    Lemma gl_fuel_eq_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 == measure ℓ2 μ2) →
      ([∗ set] k ∈ K, gl_fuel k ℓ1 μ1)%I ≡ ([∗ set] k ∈ K, gl_fuel k ℓ2 μ2)%I.
    Proof. intros. apply big_opS_proper. intros. erewrite gl_fuel_eq; eauto. Qed.

    Lemma gl_fuel_mon k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord → gl_fuel k ℓ2 μ2 ==∗ gl_fuel k ℓ1 μ1.
    Proof.
      unfold_gl_fuel. apply gl_fuel_val_mon.
    Qed.
    Lemma gl_fuel_mon_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord →
      ([∗ list] k ∈ K, gl_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, gl_fuel k ℓ1 μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_mon.
    Qed.
    Lemma gl_fuel_mon_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 <= measure ℓ2 μ2)%ord →
      ([∗ set] k ∈ K, gl_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, gl_fuel k ℓ1 μ1).
    Proof.
      iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_mon.
    Qed.

    Lemma gl_fuel_mon_split k ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord → gl_fuel k ℓ3 μ3 ==∗ gl_fuel k ℓ1 μ1 ∗ gl_fuel k ℓ2 μ2.
    Proof.
      unfold_gl_fuel. apply gl_fuel_val_mon_split.
    Qed.
    Lemma gl_fuel_mon_split_list K ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord →
      ([∗ list] k ∈ K, gl_fuel k ℓ3 μ3) ⊢ |==> ([∗ list] k ∈ K, gl_fuel k ℓ1 μ1) ∗ ([∗ list] k ∈ K, gl_fuel k ℓ2 μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
      iIntros "!> % % %". iApply gl_fuel_mon_split; auto.
    Qed.
    Lemma gl_fuel_mon_split_set K ℓ1 ℓ2 ℓ3 μ1 μ2 μ3 :
      ((measure ℓ1 μ1 ⊕ measure ℓ2 μ2) <= measure ℓ3 μ3)%ord →
      ([∗ set] k ∈ K, gl_fuel k ℓ3 μ3) ⊢ |==> ([∗ set] k ∈ K, gl_fuel k ℓ1 μ1) ∗ ([∗ set] k ∈ K, gl_fuel k ℓ2 μ2).
    Proof.
      iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
      iIntros "!> % %". iApply gl_fuel_mon_split; auto.
    Qed.

    Lemma gl_fuel_lt k ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      gl_fuel k ℓ2 μ2 ⊢ |==> gl_fuel k ℓ1 μ1 ∗ gl_fuel k 0 1.
    Proof.
      unfold_gl_fuel. rewrite (gl_fuel_val_eq _ (measure (0 : layer) 1) Ord.one).
      1: apply gl_fuel_val_lt.
      rewrite measure_nat Ord.from_nat_1. done.
    Qed.
    Lemma gl_fuel_lt_list K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      ([∗ list] k ∈ K, gl_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, gl_fuel k ℓ1 μ1) ∗ ([∗ list] k ∈ K, gl_fuel k 0 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_lt.
    Qed.
    Lemma gl_fuel_lt_set K ℓ1 ℓ2 μ1 μ2 :
      (measure ℓ1 μ1 < measure ℓ2 μ2)%ord →
      ([∗ set] k ∈ K, gl_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, gl_fuel k ℓ1 μ1) ∗ ([∗ set] k ∈ K, gl_fuel k 0 1).
    Proof.
      iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
      iModIntro. iIntros. by iApply gl_fuel_lt.
    Qed.

    (* measurable syntax rules. *)
    Lemma gl_fuel_embed k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      gl_fuel k ℓ (⟪wf_ltA, a2⟫)%M ⊢ |==> gl_fuel k ℓ (⟪wf_ltA, a1⟫)%M ∗ gl_fuel k 0 1.
    Proof.
      intros. apply gl_fuel_lt. apply measure_embed_lt. auto.
    Qed.
    Lemma gl_fuel_embed_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ list] k ∈ K, gl_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ list] k ∈ K, gl_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ list] k ∈ K, gl_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply gl_fuel_embed. auto.
    Qed.
    Lemma gl_fuel_embed_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
      ltA a1 a2 →
      ([∗ set] k ∈ K, gl_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
      ⊢ |==> ([∗ set] k ∈ K, gl_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ set] k ∈ K, gl_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply gl_fuel_embed. auto.
    Qed.

    Lemma gl_fuel_large k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      gl_fuel k ℓ (⫚)%M ⊢ |==> gl_fuel k ℓ (⟪wf_ltA, a⟫)%M ∗ gl_fuel k 0 1.
    Proof.
      intros. apply gl_fuel_lt. apply measure_large_lt.
    Qed.
    Lemma gl_fuel_large_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ list] k ∈ K, gl_fuel k ℓ (⫚)%M)
      ⊢ |==> ([∗ list] k ∈ K, gl_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ list] k ∈ K, gl_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply gl_fuel_large.
    Qed.
    Lemma gl_fuel_large_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
      ([∗ set] k ∈ K, gl_fuel k ℓ (⫚)%M)
      ⊢ |==> ([∗ set] k ∈ K, gl_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ set] k ∈ K, gl_fuel k 0 1).
    Proof.
      intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply gl_fuel_large.
    Qed.

    Lemma gl_fuel_add k ℓ μ1 μ2 :
      gl_fuel k ℓ (μ1 ⊕ μ2)%M ⊣⊢ gl_fuel k ℓ μ1 ∗ gl_fuel k ℓ μ2.
    Proof.
      unfold_gl_fuel. rewrite measure_add. apply gl_fuel_val_add.
    Qed.
    Lemma gl_fuel_add_list K ℓ μ1 μ2 :
      ([∗ list] k ∈ K, gl_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ list] k ∈ K, gl_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, gl_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply gl_fuel_add.
    Qed.
    Lemma gl_fuel_add_set K ℓ μ1 μ2 :
      ([∗ set] k ∈ K, gl_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ set] k ∈ K, gl_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, gl_fuel k ℓ μ2).
    Proof.
      rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply gl_fuel_add.
    Qed.

    Lemma gl_fuel_mult k ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      gl_fuel k ℓ (s × μ2)%M ⊢ |==> gl_fuel k ℓ (s × μ1)%M ∗ gl_fuel k ℓ s.
    Proof.
      unfold_gl_fuel. intros LT. rewrite !measure_mult. apply gl_fuel_val_mult. auto.
    Qed.
    Lemma gl_fuel_mult_list K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ list] k ∈ K, gl_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ list] k ∈ K, gl_fuel k ℓ (s × μ1)%M) ∗ ([∗ list] k ∈ K, gl_fuel k ℓ s).
    Proof.
      rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply gl_fuel_mult. auto.
    Qed.
    Lemma gl_fuel_mult_set K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      ([∗ set] k ∈ K, gl_fuel k ℓ (s × μ2)%M)
      ⊢ |==> ([∗ set] k ∈ K, gl_fuel k ℓ (s × μ1)%M) ∗ ([∗ set] k ∈ K, gl_fuel k ℓ s).
    Proof.
      rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply gl_fuel_mult. auto.
    Qed.

    Lemma gl_fuel_expn k ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      gl_fuel k ℓ (s ↑ μ2)%M ⊢ |==> gl_fuel k ℓ ((s ↑ μ1) × s)%M.
    Proof.
      unfold_gl_fuel. intros LT Pos. rewrite !measure_mult !measure_expn. apply gl_fuel_val_expn; auto.
    Qed.
    Lemma gl_fuel_expn_list K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      ([∗ list] k ∈ K, gl_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ list] k ∈ K, gl_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply gl_fuel_expn; auto.
    Qed.
    Lemma gl_fuel_expn_set K ℓ μ1 μ2 s :
      (measure ℓ μ1 < measure ℓ μ2)%ord →
      (Ord.O < measure ℓ s)%ord →
      ([∗ set] k ∈ K, gl_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ set] k ∈ K, gl_fuel k ℓ ((s ↑ μ1) × s)%M).
    Proof.
      rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply gl_fuel_expn; auto.
    Qed.

    Lemma gl_fuel_extend_val k ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      gl_fuel k ℓ2 (▽)%M ⊢ |==> gl_fuel_val k o.
    Proof.
      iIntros (LT Hl1) "H". unfold_gl_fuel. iApply (gl_fuel_val_mon with "H").      
      eapply measure_extend_alt; eauto.
    Qed.
    Lemma gl_fuel_extend_val_list K ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      ([∗ list] k ∈ K, gl_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ list] k ∈ K, gl_fuel_val k o).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply gl_fuel_extend_val; eauto.
    Qed.
    Lemma gl_fuel_extend_val_set K ℓ1 ℓ2 o :
      (ℓ1 < ℓ2)%ordi →
      (∃ s, (o <= η (measure ℓ1 s))%ord) →
      ([∗ set] k ∈ K, gl_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ set] k ∈ K, gl_fuel_val k o).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply gl_fuel_extend_val; eauto.
    Qed.

    Lemma gl_fuel_extend k ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      gl_fuel k ℓ2 (▽)%M ⊢ |==> gl_fuel k ℓ1 μ.
    Proof.
      iIntros (LT) "H". iMod (gl_fuel_extend_val _ ℓ1 with "H") as "H"; last (unfold_gl_fuel; by iFrame).
      1: auto.
      exists μ. apply η_mono.
    Qed.
    Lemma gl_fuel_extend_list K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ list] k ∈ K, gl_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ list] k ∈ K, gl_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. eapply gl_fuel_extend; eauto.
    Qed.
    Lemma gl_fuel_extend_set K ℓ1 ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      ([∗ set] k ∈ K, gl_fuel k ℓ2 (▽)%M) ⊢ |==> ([∗ set] k ∈ K, gl_fuel k ℓ1 μ).
    Proof.
      intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. eapply gl_fuel_extend; eauto.
    Qed.

    (** wit_bound rules *)
    Lemma wit_bound_mon k v a0 a1 :
      (a0 <= a1)%ord → wit_bound k v a0 ==∗ wit_bound k v a1.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_bound_mon.
    Qed.
    Lemma wit_bound_compare k v a0 a1 :
      wit_bound k v a0 -∗ wit k v a1 -∗ ⌜ (a1 <= a0)%ord ⌝.
    Proof.
      unfold_defs. iIntros "(P& Be) (_& Cred)". iApply (witG_compare with "[$]").
    Qed.
    Lemma wit_bound_spend_gen k v a0 a1 :
      wit_bound k v a0 -∗ wit k v a1 ==∗ ∃ a2, ⌜ ((a1 ⊕ a2) <= a0)%ord ⌝ ∗ wit_bound k v a2.
    Proof.
      unfold_defs. iIntros "($& Ow) (_& Oc)". iApply (witG_witness_spend_gen with "[$]").
    Qed.
    Lemma wit_bound_spend k v a0 a1 :
      (Ord.O < a1)%ord →
      wit_bound k v a0 -∗ wit k v a1 ==∗ ∃ a2, ⌜ (a2 < a0)%ord ⌝ ∗ wit_bound k v a2.
    Proof.
      unfold_defs. iIntros (LT) "($& Ow) (_& Oc)". iApply (witG_witness_spend with "[$]"). done.
    Qed.
    Lemma wit_bound_spend_one k v a :
      wit_bound k v a -∗ wit k v Ord.one ==∗ ∃ a0, ⌜ (a0 < a)%ord ⌝ ∗ wit_bound k v a0.
    Proof.
      iIntros "Ow Oc". iApply (wit_bound_spend with "Ow Oc"). apply Ord.S_pos.
    Qed.

    (** wit_layer rules *)
    Lemma wit_layer_wit_bound k v ℓ :
      wit_layer k v ℓ -∗ ∃ μ, wit_bound k v (η (measure ℓ μ)).
    Proof. unfold_defs. eauto. Qed.

    (** wit rules *)
    Lemma wit_eq k v a0 a1 :
      (a0 == a1) → wit k v a1 = wit k v a0.
    Proof.
      unfold_defs. intros. rewrite (witG_witness_eq k v a0 a1); auto.
    Qed.
    Lemma wit_mon k v a0 a1 :
      (a0 <= a1) → wit k v a1 ==∗ wit k v a0.
    Proof.
      unfold_defs. iIntros (Hle) "(P& Be)". iFrame. by iApply witG_witness_mon.
    Qed.
    Lemma wit_split k v a0 a1 :
      wit k v (a0 ⊕ a1)%ord ⊣⊢ wit k v a0 ∗ wit k v a1.
    Proof.
      unfold_defs. rewrite witG_witness_split. iSplit.
      - iIntros "(#Ge& P1& P2)"; iFrame; eauto.
      - iIntros "((P1& B1)& (P2& B2))"; iFrame.
    Qed.
    Lemma wit_mon_split k v a0 a1 a2 :
      ((a0 ⊕ a1) <= a2)%ord →
      wit k v a2 ==∗ wit k v a0 ∗ wit k v a1.
    Proof.
      unfold_defs. iIntros (Hle) "(#Be& P)".
      iMod (witG_witness_mon_split with "P") as "[P1 P2]"; first done.
      iFrame; eauto.
    Qed.
    Lemma wit_lt k v a0 a1 :
      (a0 < a1) → wit k v a1 ==∗ wit k v a0 ∗ wit k v Ord.one.
    Proof.
      unfold_defs. iIntros (Hlt) "(#Be& P)". iFrame "Be".
      iMod (witG_witness_lt with "P") as "[$ (%& %& C)]"; first done. 
      apply ord_lt_one in H. iMod (witG_witness_mon_split with "C") as "[_ $]"; done.
    Qed.

    (** gl_fuels rules *)
    Lemma gl_fuels_init α :
      ⊢ gl_fuels α ∅.
    Proof.
      unfold_defs. rewrite big_sepM_empty. done.
    Qed.

    Lemma gl_fuels_add α F f ℓ ν μ :
      (α <= measure ℓ ν)%ord →
      gl_fuels α F -∗ gl_fuel f ℓ (μ × ν)%M ==∗ gl_fuels α (<[f:=(ℓ, μ)]>F).
    Proof.
      iIntros (LT) "Wfs Gf". rewrite !gl_fuels_unseal /gl_fuels_def.
      unfold_gl_fuel. iMod (gl_fuel_val_mon _ ((measure ℓ μ) × α)%ord with "Gf") as "Gf".
      { rewrite measure_mult. apply Jacobsthal.le_mult_r. auto. }
      iModIntro. iApply (big_sepM_insert_delete _ _ f).
      iFrame "Gf". destruct (F !! f) eqn:LUF.
      - iPoseProof (big_sepM_delete _ _ f with "Wfs") as "[_ $]". eauto.
      - rewrite delete_id; auto.
    Qed.

    Lemma gl_fuels_add_map α F (G : gmap gl_id (layer * measurable_syntax)) ν :
      gl_fuels α F -∗
      ([∗ map] g ↦ '(l, m) ∈ G, ⌜ (α <= measure l ν)%ord ⌝ ∗ gl_fuel g l (m × ν)%M) ==∗
      gl_fuels α (G ∪ F).
    Proof.
      revert α F. induction G using map_ind; intros; iIntros "Wfs Fs".
      { rewrite left_id_L. by iFrame. }
      rewrite big_sepM_insert; last auto.
      rename m into G. destruct x as (l& m). iDestruct "Fs" as "((%Lt& Gf)& Fs)".
      iMod (IHG with "Wfs Fs") as "Wfs".
      replace (<[i:=(l, m)]> G ∪ F) with (<[i:=(l, m)]> (G ∪ F)).
      { iApply (gl_fuels_add with "Wfs Gf"). auto. }
      by rewrite insert_union_l.
    Qed.

    Lemma gl_fuels_decr α α0 F :
      (α0 < α)%ord →
      gl_fuels α F ==∗
      (gl_fuels α0 F ∗ ([∗ map] f ↦ '(l, m) ∈ F, gl_fuel f l m)).
    Proof.
      rewrite gl_fuels_unseal /gl_fuels_def. iIntros (LT) "Fs".
      rewrite -big_sepM_sep -big_sepM_bupd. iApply (big_sepM_impl with "Fs").
      iIntros "!> % % % H". destruct x as (l& m).
      rewrite gl_fuel_unseal /gl_fuel_def. rewrite -gl_fuel_val_add. iApply (gl_fuel_val_mon with "H").
      rewrite Hessenberg.add_comm -Jacobsthal.mult_S.
      apply Jacobsthal.le_mult_r. apply Ord.S_supremum; auto.
    Qed.

    (** embed_fuels rules *)
    Lemma embed_fuels_init {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ :
      ⊢ embed_fuels wf_ltA a ℓ ∅.
    Proof.
      rewrite !embed_fuels_unseal /embed_fuels_def. apply gl_fuels_init.
    Qed.

    Lemma embed_fuels_add {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a ℓ1 F f ℓ2 μ :
      layer_leibniz_le ℓ1 ℓ2 →
      embed_fuels wf_ltA a ℓ1 F -∗ gl_fuel f ℓ2 (μ × ⟪wf_ltA, a⟫)%M ==∗ embed_fuels wf_ltA a ℓ1 (<[f:=(ℓ2, μ)]>F).
    Proof.
      iIntros (LE) "Wfs Gf". rewrite !embed_fuels_unseal /embed_fuels_def.
      iApply (gl_fuels_add with "Wfs Gf"). apply measure_layer_leibniz_le_proper. auto.
    Qed.

    Lemma embed_fuels_add_map {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
      a ℓ F (G : gmap gl_id (layer * measurable_syntax)) :
      embed_fuels wf_ltA a ℓ F -∗
      ([∗ map] g ↦ '(l, m) ∈ G, ⌜ layer_leibniz_le ℓ l ⌝ ∗ gl_fuel g l (m × ⟪wf_ltA, a⟫)%M) ==∗
      embed_fuels wf_ltA a ℓ (G ∪ F).
    Proof.
      rewrite !embed_fuels_unseal /embed_fuels_def.
      iIntros "Gfs Fs". iApply (gl_fuels_add_map with "Gfs [Fs]").
      iApply (big_sepM_impl with "Fs"). iIntros "!> %%%". destruct x. iIntros "(%& $)".
      iPureIntro. apply measure_layer_leibniz_le_proper. auto.
    Qed.

    Lemma embed_fuels_decr {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a a' ℓ F :
      ltA a' a →
      embed_fuels wf_ltA a ℓ F ==∗
      embed_fuels wf_ltA a' ℓ F ∗ ([∗ map] f ↦ '(l, m) ∈ F, gl_fuel f l m).
    Proof.
      rewrite embed_fuels_unseal /embed_fuels_def.
      intros LT. apply (gl_fuels_decr). apply measure_embed_lt. auto.
    Qed.

    (** wit_fuels rules *)
    Lemma wit_fuels_init k v ℓ :
      wit_layer k v ℓ -∗ ∃ α, wit_fuels k v ℓ α ∅.
    Proof.
      unfold_defs. iIntros "(%& $& $)". iExists μ. iSplitR; done.
    Qed.

    Lemma wit_fuels_wit_layer k v ℓ α F :
      wit_fuels k v ℓ α F ==∗ wit_layer k v ℓ.
    Proof.
      iIntros "Wl". rewrite !wit_fuels_unseal /wit_fuels_def.
      iDestruct "Wl" as "(%& %& #Wb& _)".
      rewrite !wit_layer_unseal /wit_layer_def.
      iExists μ. iApply wit_bound_mon; eauto.
    Qed.

    Lemma wit_fuels_add k v ℓ1 α F f ℓ2 μ :
      (ℓ1 < ℓ2)%ordi →
      wit_fuels k v ℓ1 α F -∗ gl_fuel f ℓ2 (μ × ▽)%M ==∗ wit_fuels k v ℓ1 α (<[f:=(ℓ2, μ)]>F).
    Proof.
      iIntros (LT) "Wfs Gf". rewrite !wit_fuels_unseal /wit_fuels_def.
      iDestruct "Wfs" as "(%& %& $& M)".
      iExists _. iSplitR; first eauto.
      iApply (gl_fuels_add with "M Gf").
      etrans; first eauto. apply measure_extend; auto.
    Qed.

    Lemma wit_fuels_add_map k v ℓ α F (G : gmap gl_id (layer * measurable_syntax)) :
      wit_fuels k v ℓ α F -∗
      ([∗ map] g ↦ '(l, m) ∈ G, ⌜ (ℓ < l)%ordi ⌝ ∗ gl_fuel g l (m × ▽)%M) ==∗
      wit_fuels k v ℓ α (G ∪ F).
    Proof.
      rewrite !wit_fuels_unseal /wit_fuels_def.
      iIntros "(%& %& $& Fs) Gfs". iExists _. iSplitR; first eauto.
      iApply (gl_fuels_add_map _ _ _ (▽)%M with "Fs [Gfs]").
      iApply (big_sepM_impl with "Gfs"). iIntros "!> %%%". destruct x. iIntros "(%& $)".
      iPureIntro. etrans; first eauto. apply measure_extend. done.
    Qed.

    Lemma wit_fuels_decr k v ℓ α F :
      wit_fuels k v ℓ α F -∗ wit k v Ord.one ==∗
      ∃ α0, ⌜ (α0 < α)%ord ⌝ ∗ wit_fuels k v ℓ α0 F ∗
            ([∗ map] f ↦ '(l, m) ∈ F, gl_fuel f l m).
    Proof.
      rewrite wit_fuels_unseal /wit_fuels_def. iIntros "(%& %& #Wbk& Fs) Wk".
      iMod (wit_bound_spend_one with "Wbk Wk") as "(%& %& #Wbk2)".
      iExists a0. iSplitR; first done. iFrame "Wbk2". assert (a0 <= η (measure ℓ μ)).
      { etransitivity; last eauto. apply WFOCM.lt_le. auto. }
      iFrame (H1).
      iApply (gl_fuels_decr with "Fs"). auto.
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

    Lemma gl_alloc_obl_0 Θ i G q ℓs μ v :
      Proper (le ==> layer_leibniz_le) ℓs →
      th_obls i G q -∗
      |=[Θ]=>g ∃ k, (⌜ G !! k = None ⌝) ∗
                   th_obls i (<[k:=v]>G) q ∗
                   gl_current k v (1/2)%Qp ∗
                   gl_layers k ℓs ∗ gl k v ∗
                   gl_fuel k (ℓs v) μ ∗
                   wit_layer k v (ℓs v) ∗
                   ([∗ set] u ∈ set_seq 0 v, gl_done k u) ∗
                   (∀ E N (P Q R : iProp Σ), (▷ P) ={E}=∗ gl_variant N k v P Q R).
    Proof.
      unfold_defs. iIntros (MONO) "(#Oe& Ox& Ob& OS)".
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (glsat_alloc_ghost_lock_locked _ k v ℓs μ i with "S") as "(S& #Gwf& #Ge& Gl& Gv& Gf& Go& #Gseq& %OStep)".
      1: auto.
      iDestruct "Gl" as "[Gl0 [Gl1 Gl']]".
      iMod (globl_alloc_obl with "[$S $O $Ob $Ge $Gl' $Go]") as "(S& O& %NinGk& Ob& Oo& Go)".
      iPoseProof (glG_version_get_lb _ v v with "Gv") as "#Gvl". 1: done.
      set (ηℓ := (λ x, η (measure (ℓs v) μ)) : ghost_lock_version → _).
      iMod (glwit_alloc_witness_locked _ k v ηℓ with "[$W $Gseq $Gvl]") as "(W& #Wseq)".
      { apply glwit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iAssert (witG_bound k v (η (measure (ℓs v) μ)))%I with "[Wseq]" as "#Ww".
      { rewrite set_seq_S_end_union_L. rewrite big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        iDestruct "Wseq" as "[Ww _]". rewrite big_sepS_singleton.
        subst ηℓ. simpl. eauto. }
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo0 [Oo1 Oo']]".
      iPoseProof (glassigned_add_obl with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. }
      iDestruct "Gl1" as "[Gl1 Gl']".
      iModIntro. iExists (<[k:=(v, ghost_lock_locked (GL:=ord_ghost_lock_class) (measure (ℓs v) μ) i)]> Ω1).
      iSplitR.
      { iPureIntro. econstructor 2. econstructor 2. auto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (glwit_inv_alloc_locked Ω1 k W1 NinOk1 GWI _ _ _ W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W". iSplitL "A".
      { rewrite fmap_insert. simpl. iFrame. eauto. }
      iDestruct "Gv" as "[[Gv1 Gv1'] [Gv2 Gv2']]". iCombine "Gv1 Gv2" as "Gv". iCombine "Gv1' Gv2'" as "Gv'".
      iModIntro. iExists k. iFrame "Oe Gwf Ge Gvl Ww Gf Ox Gseq Gv'". iSplitR.
      { iPureIntro. apply not_elem_of_dom. auto. }
      iSplitL "Ob OS Gv Go Gl0 Gl1 Oo0 Oo1".
      { rewrite dom_insert_L. iFrame "Ob". iApply big_sepM_insert. 1: apply not_elem_of_dom; auto.
        iFrame "OS Ge Gv Go". iCombine "Gl0 Gl1" as "$". iCombine "Oo0 Oo1" as "$". eauto. }
      iSplitR.
      { iApply (big_sepS_impl with "Gseq"). iIntros "!> %% ($& $)". iFrame "Ge".
        iApply (gl_history_mon with "Gseq"). apply elem_of_set_seq in H. lia. }
      iIntros (E N P Q R) "HP".
      iMod (glG_variant_alloc_locked _ N _ _ _ P Q R with "[$Gl' $HP]") as "#GVar".
      iModIntro. eauto.
    Qed.
    Lemma gl_alloc_obl_1 E Θ i G q ℓs μ N v (P Q R : iProp Σ) :
      Proper (le ==> layer_leibniz_le) ℓs →
      th_obls i G q -∗
      (▷ P) -∗
      |={E:Θ}=>g ∃ k, (⌜ G !! k = None ⌝) ∗
                     th_obls i (<[k:=v]>G) q ∗
                     gl_current k v (1/2)%Qp ∗
                     gl_layers k ℓs ∗ gl k v ∗
                     gl_fuel k (ℓs v) μ ∗
                     gl_variant N k v P Q R ∗
                     wit_layer k v (ℓs v) ∗
                     ([∗ set] u ∈ set_seq 0 v, gl_done k u).
    Proof.
      iIntros (MONO) "TG HP".
      iMod (gl_alloc_obl_0 with "TG") as "(%& $& $& $& $& $& $& $& $& H)".
      iMod ("H" $! E N P Q R with "HP") as "H". by iModIntro.
    Qed.

    Lemma gl_alloc_done_0 Θ ℓs μ v :
      Proper (le ==> layer_leibniz_le) ℓs →
      ⊢ |=[Θ]=>g ∃ k, gl_layers k ℓs ∗ gl k v ∗ gl_current k v 1 ∗ gl_done k v ∗ gl_fuel k (ℓs v) μ ∗
                     wit_layer k v (ℓs v) ∗
                     ([∗ set] u ∈ set_seq 0 (S v), gl_done k u) ∗
                     (∀ E N (P Q R : iProp Σ), (▷ Q) ={E}=∗ gl_variant N k v P Q R).
    Proof.
      unfold_defs. iIntros (MONO).
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      assert (NEW : ∃ k, Ω1 !! k = None).
      { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
      destruct NEW as (k& NEWk).
      assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
      iMod (glsat_alloc_ghost_lock_unlocked _ k v ℓs μ with "S") as "(S& #Gwf& #Ge& #Gu& Gv& Gf& #Gseq& %OStep)".
      { auto. }
      iPoseProof (glG_version_get_lb _ v v with "Gv") as "#Gvl". 1: done.
      set (ηℓ := (λ x, η (measure (ℓs v) μ)) : ghost_lock_version → _).
      iAssert ([∗ set] u ∈ set_seq 0 (S v), glG_version_lb k u ∗ glG_unlocked k u)%I as "Gseq2".
      { rewrite set_seq_S_end_union_L big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        rewrite big_sepS_singleton. eauto. }
      iMod (glwit_alloc_witness_unlocked _ k v ηℓ with "[$W $Gseq2]") as "(W& #Wseq)".
      { apply glwit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
      iAssert (witG_bound k v (η (measure (ℓs v) μ)))%I with "[Wseq]" as "#Ww".
      { iClear "Gseq2". rewrite !set_seq_S_end_union_L !big_sepS_union; cycle 1.
        { apply set_seq_S_end_disjoint. }
        iDestruct "Wseq" as "[Ww _]". rewrite big_sepS_singleton.
        subst ηℓ. simpl. eauto. }
      iPoseProof (glassigned_add_obl with "[$A $Ge Gu]") as "A".
      { iRight. iFrame "Gu". }
      iModIntro. iExists (<[k:=(v, ghost_lock_unlocked)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 2. auto. }
      iIntros (? [WStep GWI2]) "!>".
      pose proof (glwit_inv_alloc_unlocked Ω1 k W1 NinOk1 GWI _ W2 WStep GWI2) as (NinWk1& WMon).
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W". iSplitL "A".
      { rewrite fmap_insert. simpl. iFrame. eauto. }
      iModIntro. iExists k. iFrame "Gwf Ge Gvl Ww Gf Gv Gu Gseq".
      iSplitR.
      { iApply (big_sepS_impl with "Gseq2"). iIntros "!> %% ($& $)". iFrame "Ge".
        iApply (gl_history_mon with "Gseq"). apply elem_of_set_seq in H. lia. }
      iIntros (E N P Q R) "HQ".
      iMod (glG_variant_alloc_unlocked _ N _ _ _ P Q R with "[$Gu $HQ]") as "#GVar".
      iModIntro. eauto.
    Qed.
    Lemma gl_alloc_done_1 E Θ ℓs μ N v P Q R :
      Proper (le ==> layer_leibniz_le) ℓs →
      (▷ Q) -∗
      |={E:Θ}=>g ∃ k, gl_layers k ℓs ∗ gl k v ∗ gl_current k v 1 ∗ gl_done k v ∗ gl_fuel k (ℓs v) μ ∗
                     gl_variant N k v P Q R ∗
                     wit_layer k v (ℓs v) ∗
                     ([∗ set] u ∈ set_seq 0 (S v), gl_done k u).
    Proof.
      iIntros (MONO) "HQ".
      iMod (gl_alloc_done_0) as "(%& $& $& $& $& $& $& $& H)".
      iMod ("H" $! E N P Q R with "HQ") as "H". by iModIntro.
    Qed.

    Lemma gl_lock_0 E qc k N v1 (P1 Q1 R1 : iProp Σ) :
      ↑N ⊆ E →
      gl_current k v1 qc -∗
      gl_done k v1 -∗
      gl_variant N k v1 P1 Q1 R1 -∗
      |={E,E ∖ ↑N}=> (▷ (gl_current k v1 qc ∗ Q1)) ∗
                    (∀ i G q ℓs,
                       th_obls i G q -∗
                       gl_current k v1 1 -∗
                       gl_layers k ℓs -∗
                       ∀ v2 μ, (⌜v1 < v2⌝) →
                               ∀ Θ, |=[Θ]=>g (th_obls i (<[k:=v2]>G) q ∗ ⌜ G !! k = None ⌝ ∗
                                             gl_current k v2 (1/2)%Qp ∗
                                             gl k v2 ∗ gl_fuel k (ℓs v2) μ ∗
                                             wit_layer k v2 (ℓs v2) ∗
                                             ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), wit_layer k u (ℓs u)) ∗
                                             ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), gl_done k u)) ∗
                                          (∀ E0 (P2 Q2 R2 : iProp Σ), (▷ P2) ={E0}=∗ gl_variant N k v2 P2 Q2 R2) ∗
                                          ((▷ R1) ={E ∖ ↑N,E}=∗ True)).
    Proof.
      unfold_defs. iIntros (MASK) "((#Ge& #Gvl1)& Gv1) (_& #Gu1) (_& #Gvar1)".
      iMod (glG_variant_acc_version_unlocked with "Gvar1 Gv1 Gu1") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "H".
      { iNext. iDestruct "H" as "($& _& _& $)". eauto. }
      iIntros (i G q ℓs) "(#Oe& Ox& Ob& OS) (_& Gv1) #Gwf % % %Ltv %".
      iPoseProof (glG_layers_mono with "Gwf") as "%MONO".
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iPoseProof (glsat_lookup_unlocked with "[$S $Ge $Gu1]") as "%LUO1u".
      iPoseProof (glsat_lookup_version with "[$S $Ge $Gv1]") as "%LUO1v".
      destruct LUO1v as (?&LUO1v). destruct LUO1u as [LUO1u | (?&?&?&LUO1u)]; cycle 1.
      { exfalso. rewrite LUO1u in LUO1v. inv LUO1v. lia. }
      rewrite LUO1u in LUO1v. inv LUO1v.
      iMod (glsat_lock _ _ v1 v2 ℓs μ i with "[$S $Gwf $Gu1 $Gv1]") as "(%& S& Gl& Gv& Gf& Go& #Gseq& %Gstep)".
      1: auto.
      iDestruct "Gl" as "[Gl1 [Gl2 Gl']]".
      iMod (globl_alloc_obl with "[$S $O $Ob $Ge $Gl' $Go]") as "(S& O& %NinGk& Ob& Oo& Go)".
      iPoseProof (glG_version_get_lb _ v2 v2 with "Gv") as "#Gvl2". 1: done.
      set (ηℓ := (λ v, η (measure (ℓs v) (μ')%M)) : ghost_lock_version → _).
      iMod (glwit_lock _ _ v1 v2 ηℓ with "[$W $Gseq $Gvl2]") as "(W& #Ww& #Wseq)".
      1: auto.
      { specialize (GWI k). rewrite LUO1u in GWI. inv GWI.
        destruct y. destruct H1. subst. by destruct w. }
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo1 [Oo2 Oo']]".
      iPoseProof (glassigned_add_obl _ k v2 with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. }
      iDestruct "Gv" as "[[Gv1 Gv1'] [Gv2 Gv2']]". iCombine "Gv1 Gv2" as "Gv". iCombine "Gv1' Gv2'" as "Gv'".
      iModIntro. iExists (<[k:=(v2, ghost_lock_locked (GL:=ord_ghost_lock_class) (measure (ℓs v2) (μ')%M) i)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (glwit_inv_lock _ _ v1 v2 _ _ _ LUO1u GWI Gstep W2 WStep GWI2) as [LUW1 WMon].
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W". iSplitL "A".
      { iModIntro. rewrite fmap_insert. iFrame. eauto. }
      (* FIXME: iModIntro introduces too many modalities. *)
      iApply fupd_intro. iModIntro.
      iDestruct "Gl2" as "[Gl2 Gl']".
      rewrite dom_insert_L. iFrame "Oe Ge Gvl2 Ox Ob Gf Ww Gv'".
      iDestruct "Gvl1" as "[Gvl1' His1]".
      iPoseProof (gl_history_add _ v1 v2 with "[His1] Gseq") as "#His2".
      1: auto.
      { rewrite set_seq_S_end_union_L. iApply big_sepS_union.
        { apply set_seq_S_end_disjoint. }
        rewrite big_sepS_singleton. auto. }
      iFrame "His2". iSplitR "ACC Gl'".
      { iSplitL.
        { iApply big_sepM_insert.
          { apply not_elem_of_dom; auto. }
          iFrame. iCombine "Gl1 Gl2" as "$". iCombine "Oo1 Oo2" as "$". auto. }
        iSplitR.
        { iPureIntro. apply not_elem_of_dom. auto. }
        iSplitL.
        { iApply (big_sepS_impl with "Wseq"). iIntros "!> %% $".
          iPoseProof (big_sepS_delete _ _ _ H with "Gseq") as "[[$ _] _]".
          iFrame "Ge". iApply (gl_history_mon with "His2"). apply elem_of_set_seq in H. lia. }
        { iApply (big_sepS_impl with "Gseq"). iIntros "!> %% [$ $]".
          iFrame "Ge". iApply (gl_history_mon with "His2"). apply elem_of_set_seq in H. lia. }
      }
      iSplitR "ACC".
      { iIntros (? P2 Q2 R2) "HP2". iMod (glG_variant_alloc_locked _ N k v2 _ P2 Q2 R2 with "[$Gl' $HP2]") as "#Gvar2". done. }
      iIntros "HR1". iMod ("ACC" with "[HR1]") as "_".
      { iNext. iRight. iFrame. iFrame "Gu1". iApply (glG_version_get_expired _ v2 v1); auto. }
      done.
    Qed.

    Lemma gl_unlock_0 E i G q N k v P Q R :
      ↑N ⊆ E →
      G !! k = Some v →
      th_obls i G q -∗
      gl_variant N k v P Q R -∗
      |={E,E ∖ ↑N}=> (▷ (th_obls i G q ∗ gl_locked k v ∗ P)) ∗
                    (th_obls i G q -∗
                     gl_locked k v -∗
                     ∀ Θ, |=[Θ]=>g (th_obls i (delete k G) q ∗ gl_current k v (1/2)%Qp ∗ gl_done k v) ∗
                                ((▷ Q) ={E ∖ ↑N,E}=∗ True)).
    Proof.
      unfold_defs. iIntros (MASK LUGk) "(#Oe& Ox& Ob& OS) ((#Ge& #Gvl)& #Gvar)".
      iPoseProof (big_sepM_delete _ _ _ _ LUGk with "OS") as "[(_& Gl& [_ Gv]& Go& Oo) OS]".
      iMod (glG_variant_acc_version_locked with "Gvar Gv Gl") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "Ox Ob Go Oo OS H".
      { iNext. iFrame "Oe Ox Ob". iDestruct "H" as "(Gv& Gl& $& $)".
        rewrite (big_sepM_delete _ _ _ _ LUGk). iFrame. iFrame "Ge Gvl". }
      iIntros "(_& Ox& Ob& OS) (_& Gl1) %".
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iPoseProof (big_sepM_delete _ _ _ _ LUGk with "OS") as "[(_& Gl& Gv& Go& Oo) OS]".
      iPoseProof (glsat_lookup_locked with "[$S $Ge $Gl]") as "%LUO1l".
      iPoseProof (glsat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
      destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&?&LUO1o).
      rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into v, x2 into a.
      iPoseProof (glassigned_delete_obl _ k v with "A") as "(A& _& [(%& Go1& Oo1) | #Gu])".
      { rewrite lookup_fmap LUO1l. done. }
      2:{ iExFalso. iPoseProof (glG_locked_unlocked_false with "[$Gl $Gu]") as "%". done. }
      iPoseProof (glG_owner_agree _ i i0 with "[$Go $Go1]") as "%". destruct H as [<- _].
      iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
      iMod (globl_delete_obl_frac with "[$O $Ob $Oo]") as "(O& Ob& Gl2& Go2)".
      { apply elem_of_dom. eauto. }
      iDestruct "Gl" as "[Gl Gl']". iCombine "Gl' Gl1" as "Gl'". iCombine "Gl' Gl2" as "Gl'".
      iCombine "Gl Gl'" as "Gl".
      iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
      iCombine "Go Go'" as "Go".
      iMod (glsat_unlock with "[$S $Ge $Gl $Go]") as "(S& #Gu& %Gstep)".
      assert (LUW : ∃ b, W1 !! k = Some (v, witness_locked b) ∧ (b <= η a)%ord).
      { specialize (GWI k). rewrite LUO1l in GWI. inv GWI. destruct y. destruct H1. subst.
        destruct w; eauto. done. }
      destruct LUW as (b&LUW1& LEab).
      iPoseProof (glwit_unlock with "[$W $Gu]") as "W". 1: eauto.
      iPoseProof (glassigned_add_obl _ k v with "[$A $Ge]") as "A".
      { iRight. eauto. }
      iModIntro. iExists (<[k:=(v, ghost_lock_unlocked)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]). specialize (Gstep a).
      pose proof (glwit_inv_unlock _ _ v _ _ _ LUO1l GWI Gstep W2 WStep GWI2) as (?& LUW& WMon).
      rewrite LUW1 in LUW. inv LUW.
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W". iSplitL "A".
      { iModIntro. rewrite insert_delete_eq. rewrite fmap_insert. iFrame. eauto. }
      iApply fupd_intro. iIntros "!>". iDestruct "Gv" as "[_ Gv]". iFrame "Oe Ge Gvl Gu Ox Gv".
      iSplitR "ACC".
      { iSplitL "Ob".
        - rewrite dom_delete_L. iFrame.
        - iFrame. }
      iIntros "HQ". iMod ("ACC" with "[HQ]") as "_".
      { iNext. iLeft. iRight. iFrame. eauto. }
      done.
    Qed.

    Lemma gl_new_version_0 E k qc v1 N (P1 Q1 R1 : iProp Σ) :
      ↑N ⊆ E →
      gl_current k v1 qc -∗
      gl_done k v1 -∗
      gl_variant N k v1 P1 Q1 R1 -∗
      |={E,E ∖ ↑N}=> (▷ (gl_current k v1 qc ∗ Q1)) ∗
                    (gl_current k v1 1 -∗
                     ∀ v2, (⌜ v1 < v2 ⌝) →
                           ∀ Θ, |=[Θ]=>g (gl k v2 ∗ gl_done k v2 ∗ gl_current k v2 1 ∗
                                         ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), gl_done k u)) ∗
                                      (∀ E0 (P2 Q2 R2 : iProp Σ), (▷ Q2) ={E0}=∗ gl_variant N k v2 P2 Q2 R2) ∗
                                      ((▷ R1) ={E ∖ ↑N,E}=∗ True)).
    Proof.
      unfold_defs. iIntros (MASK) "((#Ge& #Gvl1)& Gv1) (_& #Gu1) (_& #Gvar1)".
      iMod (glG_variant_acc_version_unlocked with "Gvar1 Gv1 Gu1") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "H".
      { iNext. iDestruct "H" as "($& _& _& $)". eauto. }
      iIntros "(_& Gv1) % %LTv %".
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iPoseProof (glsat_lookup_unlocked with "[$S $Ge $Gu1]") as "%LUO1u".
      iPoseProof (glsat_lookup_version with "[$S $Ge $Gv1]") as "%LUO1v".
      destruct LUO1v as (?&LUO1v). destruct LUO1u as [LUO1u | (?&?&?&LUO1u)]; cycle 1.
      { exfalso. rewrite LUO1u in LUO1v. inv LUO1v. lia. }
      rewrite LUO1u in LUO1v. inv LUO1v.
      iMod (glsat_new_version _ _ v1 v2 with "[$S $Ge $Gu1 $Gv1]") as "(S& #Gu2& Gv2& #Gseq& %Gstep)".
      1: auto.
      iPoseProof (glG_version_get_lb _ v2 v2 with "Gv2") as "#Gvl2". 1: done.
      set (ηℓ := (λ v, η (Ord.O)) : ghost_lock_version → _).
      iMod (glwit_new_version _ _ v1 v2 ηℓ with "[$W $Gseq $Gvl2]") as "(W& #Ww& #Wseq)".
      1: auto.
      { specialize (GWI k). rewrite LUO1u in GWI. inv GWI.
        destruct y, H1. subst. destruct w; done. }
      iPoseProof (glassigned_add_obl _ k v2 with "[$A $Ge]") as "A".
      { iRight. eauto. }
      iModIntro. iExists (<[k:=(v2, ghost_lock_unlocked)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (glwit_inv_new_version _ _ v1 v2 _ LUO1u GWI Gstep W2 WStep GWI2) as [LUW1 WMon].
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W". iSplitL "A".
      { iModIntro. rewrite fmap_insert. iFrame. eauto. }
      (* FIXME: iModIntro introduces too many modalities. *)
      iApply fupd_intro. iModIntro.
      iFrame "Ge Gvl2 Gu2 Gv2".
      iAssert ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u)%I with "[]" as "#Gseq'".
      { replace (v2 - v1) with (S (v2 - v1 - 1)) by lia. rewrite (set_seq_S_end_union_L _ (v2 - v1 - 1)).
        iPoseProof (big_sepS_union with "Gseq") as "[_ Gseq']".
        { apply set_seq_S_end_disjoint. }
        replace (S (v2 - v1 - 1) - 1) with (v2 - v1 - 1) by lia. eauto. }
      iDestruct "Gvl1" as "[Gvl1' His1]".
      iPoseProof (gl_history_add _ v1 v2 with "[His1] Gseq'") as "#His2".
      1: auto.
      { rewrite set_seq_S_end_union_L. iApply big_sepS_union.
        { apply set_seq_S_end_disjoint. }
        rewrite big_sepS_singleton. auto. }
      iFrame "His2". iSplitR "ACC".
      { iApply (big_sepS_impl with "Gseq'"). iIntros "!> %% [$ $]".
        iFrame "Ge". iApply (gl_history_mon with "His2"). apply elem_of_set_seq in H. lia.
      }
      iSplitR "ACC".
      { iIntros (? P2 Q2 R2) "HQ2". iMod (glG_variant_alloc_unlocked _ N k v2 _ P2 Q2 R2 with "[$Gu2 $HQ2]") as "#Gvar2". done. }
      iIntros "HR1". iMod ("ACC" with "[HR1]") as "_".
      { iNext. iRight. iFrame. iFrame "Gu1". iApply (glG_version_get_expired _ v2 v1); auto. }
      done.
    Qed.

    Lemma gl_change_owner_0 Θ i1 i2 G1 G2 q1 q2 k v ℓ0 :
      G1 !! k = Some v →
      th_obls i1 G1 q1 -∗
      th_obls i2 G2 q2 -∗
      gl_fuel k ℓ0 1 -∗
      |=[Θ]=>g th_obls i1 (delete k G1) q1 ∗ th_obls i2 (<[k:=v]>G2) q2 ∗ ⌜ G2 !! k = None ⌝.
    Proof.
      unfold_defs. iIntros (LUGk) "(#Oe1& Ox1& Ob1& OS1) (#Oe2& Ox2& Ob2& OS2) (#Ge& Gf)".
      rewrite (glG_fuel_eq _ _ Ord.one); cycle 1.
      { rewrite measure_nat Ord.from_nat_1. done. }
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iPoseProof (big_sepM_delete _ _ _ _ LUGk with "OS1") as "[(_& Gl& [#Gseq Gv]& Go& Oo) OS1]".
      iPoseProof (glsat_lookup_locked with "[$S $Ge $Gl]") as "%LUO1l".
      iPoseProof (glsat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
      destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&?&LUO1o).
      rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into v, x2 into a.
      iPoseProof (glassigned_delete_obl _ k v with "A") as "(A& _& [(%& Go1& Oo1) | #Gu])".
      { rewrite lookup_fmap LUO1l. done. }
      2:{ iExFalso. iPoseProof (glG_locked_unlocked_false with "[$Gl $Gu]") as "%". done. }
      iPoseProof (glG_owner_agree _ i i1 with "[$Go $Go1]") as "%". destruct H as [-> _].
      iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
      iMod (globl_delete_obl_frac with "[$O $Ob1 $Oo]") as "(O& Ob1& Gl2& Go2)".
      { apply elem_of_dom. eauto. }
      iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
      iCombine "Go Go'" as "Go".
      iMod (glsat_progress_one_owner _ _ _ _ _ i2 with "[$S $Go $Gf]") as "(%& S& Go& %Gstep)".
      1: eauto.
      1: apply Ord.S_lt.
      iMod (globl_alloc_obl with "[$S $O $Ob2 $Ge $Gl2 $Go]") as "(S& O& %NinkG2& Ob2& Oo& Go)".
      iDestruct "Go" as "[Go Go']". iDestruct "Oo" as "[Oo [Oo1 Oo']]".
      iPoseProof (glassigned_add_obl with "[$A $Ge Go' Oo']") as "A".
      { iLeft. iFrame. }
      iModIntro. iExists (<[k:=(v, ghost_lock_locked a' i2)]> Ω1). iSplitR.
      { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
      iIntros (? [WStep GWI2]).
      pose proof (glwit_inv_progress_owner _ k v _ _ _ LUO1l GWI _ _ Gstep W2 WStep GWI2) as WMon.
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W". iSplitL "A".
      { iModIntro. rewrite insert_delete_eq. rewrite fmap_insert. iFrame. eauto. }
      iIntros "!> !>". iFrame "Oe1 Oe2 Ox1 Ox2 OS1". rewrite dom_delete_L dom_insert_L.
      iFrame "Ob1 Ob2". assert (LUkG2 : G2 !! k = None) by (apply not_elem_of_dom; auto).
      iSplitL; last auto.
      iApply big_sepM_insert. 1: auto. iFrame. iCombine "Oo Oo1" as "Oo". eauto.
    Qed.

    Lemma gl_terminate_0 Θ i :
      th_obls i ∅ 1 -∗ |=[Θ]=>g th_term i.
    Proof.
      unfold_defs. iIntros "(#Oe& Ox& Ob& OS)".
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI)".
      iMod (globl_exec_to_term with "[$O $Ox $Ob]") as "[O #Ot]".
      iModIntro. iExists Ω1. iSplitR; first done.
      iIntros (? [WStep GWI2]).
      pose proof (glwit_inv_rc_step_same_gls _ _ _ GWI WStep GWI2) as WMon.
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W A". iSplitR.
      { eauto. }
      iIntros "!> !>". auto.
    Qed.

    Lemma gl_check_witnesses_0 Θ R :
      ([∗ map] r ↦ v ∈ R, gl r v) -∗
      |=[Θ]=>g ([∗ map] r ↦ v ∈ R, wit r v Ord.O ∨ gl_done r v).
    Proof.
      unfold_defs. iIntros "#REs".
      iApply gupd_unfold. iRight. iIntros (??) "(S& O& A& W& %GWI1)".
      iPoseProof (glwit_get_credit_zero with "W") as "[W Ws]".
      assert (DomOW : dom Ω1 = dom W1) by (eapply glwit_inv_dom; eauto).
      iAssert (⌜ dom R ⊆ dom W1 ⌝)%I as "%RWSub".
      { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
        pose proof INRx. apply elem_of_dom in H. destruct H.
        iPoseProof (big_sepM_delete _ _ _ _ H with "REs") as "[[#Beg _] _]".
        iPoseProof (glsat_elem with "[$S $Beg]") as "%". done.
      }
      iModIntro. iExists Ω1. iSplitR; first done. iIntros (? [WStep GWI2]).
      assert (HW1 : ∃ WR WR', WR ##ₘ WR' ∧ W1 = WR ∪ WR' ∧ dom R = dom WR).
      { clear GWI1 DomOW WStep.
        revert R RWSub. induction W1 using map_ind; intros.
        { assert (dom R = ∅) by (set_solver). apply dom_empty_inv_L in H. subst. exists ∅, ∅. done. }
        rename i into r. rewrite dom_insert_L in RWSub. destruct (decide (r ∈ dom R)).
        - set (R2 := delete r R). assert (dom R2 ⊆ dom m).
          { subst R2. rewrite dom_delete_L. set_solver + RWSub. }
          apply elem_of_dom in e. destruct e. rename H1 into LUR.
          destruct (IHW1 _ H0) as (WR&WR'&?&?&?).
          exists (<[r:=x]>WR), WR'. subst R2.
          assert (WR !! r = None ∧ WR' !! r = None).
          { apply lookup_union_None. rewrite -H2; auto. }
          destruct H4. split_and !.
          + apply map_disjoint_insert_l. split; auto.
          + subst. rewrite insert_union_l. done.
          + replace R with (<[r:=x0]> (delete r R)).
            * rewrite !dom_insert_L H3. auto.
            * rewrite insert_delete_id; auto.
        - assert (dom R ⊆ dom m).
          { set_solver + RWSub n. }
          pose proof H0. apply IHW1 in H1. destruct H1 as (WR& WR'& ?&?&?).
          assert (WR !! r = None ∧ WR' !! r = None).
          { apply lookup_union_None. rewrite -H2; auto. }
          destruct H4. exists WR, (<[r:=x]>WR'). split_and !; auto.
          + apply map_disjoint_insert_r. split; auto.
          + subst. rewrite insert_union_r; done.
      }
      destruct HW1 as (WR& WR'& DisjWR& EQWR& DomWR).
      assert (EQfst : fst <$> Ω1 = fst <$> W1).
      { apply map_eq. intros j. specialize (GWI1 j). rewrite !lookup_fmap. destruct (W1 !! j) eqn:LUW1.
        - rewrite LUW1. rewrite LUW1 in GWI1. inv GWI1. destruct x. destruct w. destruct H1. by subst.
        - rewrite LUW1. rewrite LUW1 in GWI1. inv GWI1. done.
      }
      iAssert (⌜ ∀ k v, R !! k = Some v → ∃ w, WR !! k = Some w ∧ v ≤ w.1 ⌝)%I as "%Rver".
      { iIntros (k v LUR). iPoseProof (big_sepM_delete _ _ _ _ LUR with "REs") as "[(#Ge& #Gvl& #His) _]".
        iPoseProof (glsat_lookup_version_lb with "[$S $Ge $Gvl]")as "(%&%&%&%)".
        rewrite map_eq_iff in EQfst. specialize (EQfst k). rewrite !lookup_fmap H in EQfst.
        assert (is_Some (WR !! k)).
        { apply elem_of_dom. rewrite -DomWR. apply elem_of_dom; eauto. }
        destruct H1 as (?& LUWRk).
        assert (WR' !! k = None).
        { eapply map_disjoint_Some_l; eauto.  }
        destruct (W1 !! k) eqn:LUW1.
        - rewrite LUW1 in EQfst. inv EQfst. apply lookup_union_Some_inv_l in LUW1; eauto.
        - rewrite LUW1 in EQfst. inv EQfst.
      }
      iAssert (|==> [∗ map] r↦v ∈ R, (witG_witness r v Ord.O) ∨ (glG_unlocked r v))%I
        with "[Ws]" as ">Rs".
      { subst W1. iPoseProof (big_sepM_union with "Ws") as "[Ws1 _]"; first auto.
        iApply big_sepM_bupd. iClear "REs". clear dependent WR'.
        iStopProof. revert R DomWR Rver. induction WR using map_ind; iIntros (R DomWR Rver) "M".
        { apply dom_empty_inv_L in DomWR. subst. done. }
        rename i into r. rewrite dom_insert_L in DomWR. destruct (R !! r) eqn:LUR; cycle 1.
        { exfalso. apply not_elem_of_dom in LUR. set_solver + DomWR LUR. }
        remember (delete r R) as R0.
        assert (dom R0 = dom m).
        { subst. rewrite dom_delete_L. apply not_elem_of_dom in H. rewrite DomWR. set_solver + H. }
        assert (R0 !! r = None).
        { subst. apply lookup_delete_eq. }
        assert (R = <[r:=g]>R0).
        { subst. rewrite insert_delete_id; auto. }
        rewrite H2.
        assert (∀ k v, R0 !! k = Some v → ∃ w, m !! k = Some w ∧ v ≤ w.1).
        { intros. specialize (Rver k v). subst. destruct (decide (k = r)).
          { subst. rewrite lookup_delete_eq in H3. inv H3. }
          rewrite lookup_delete_ne in H3; auto. apply Rver in H3. destruct H3 as (?&?&?).
          rewrite lookup_insert_ne in H3; eauto.
        }
        destruct (Rver _ _ LUR) as (w& LUmk& LEv). rewrite lookup_insert_eq in LUmk.
        clear dependent R. inv LUmk. rewrite !big_sepM_insert; auto.
        destruct w. iDestruct "M" as "[H M]". iPoseProof (IHWR _ H0 H3 with "M") as "$".
        iDestruct "H" as "(#H1& #H2& H)". simpl in LEv. destruct w.
        - assert (g = n ∨ g < n) by lia. destruct H2.
          + subst. by iFrame.
          + assert (g ∈ (set_seq 0 n : gset _)).
            { apply elem_of_set_seq. lia. }
            iPoseProof (big_sepS_delete _ _ _ H4 with "H1") as "[(_& Gu) _]".
            iRight. auto.
        - assert (g = n ∨ g < n) by lia. destruct H2.
          + subst. iRight. auto.
          + assert (g ∈ (set_seq 0 n : gset _)).
            { apply elem_of_set_seq. lia. }
            iPoseProof (big_sepS_delete _ _ _ H4 with "H1") as "[(_& Gu) _]".
            iRight. auto.
      }
      iAssert ([∗ map] r↦v ∈ R,
                 ((glG_elem r ∗ glG_version_lb r v ∗
                   ([∗ set] u ∈ set_seq 0 v, glG_version_lb r u ∗ glG_unlocked r u)) ∗ witG_witness r v Ord.O) ∨
                   ((glG_elem r ∗ glG_version_lb r v ∗
                     ([∗ set] u ∈ set_seq 0 v, glG_version_lb r u ∗ glG_unlocked r u)) ∗ glG_unlocked r v))%I
        with "[Rs]" as "Rs".
      { iPoseProof (big_sepM_sep with "[$Rs $REs]") as "H". iApply (big_sepM_impl with "H").
        iIntros "!> %%% ([Wc | #Gu]& #Ge& #Gvl& #His)".
        - iLeft. iFrame. auto.
        - iRight. auto.
      }
      pose proof (glwit_inv_rc_step_same_gls _ _ _ GWI1 WStep GWI2) as WMon.
      iPoseProof (glwit_mon _ _ WMon with "W") as "W".
      rewrite /gproto. iFrame "S O W A". iSplitR.
      { eauto. }
      iIntros "!> !>". auto.
    Qed.

    (** Variant access rules *)
    Lemma gl_variant_cases_unfold k v P Q R :
      gl_variant_cases k v P Q R
      ⊣⊢ ((gl_locked k v ∗ P) ∨ (gl_done k v ∗ Q)) ∨ (gl_expired k v ∗ R).
    Proof.
      rewrite !gl_variant_cases_unseal /gl_variant_cases_def. auto.
    Qed.

    Local Lemma gl_variant_cases_internal k v P Q R :
      gl_variant_cases k v P Q R -∗
      glG_variant_internal k v (1 / 2 / 2 / 2 / 2) P Q R.
    Proof.
      unfold_defs. iIntros "[[H | H] | H]".
      - iLeft. iLeft. iDestruct "H" as "((_& $)& $)".
      - iLeft. iRight. iDestruct "H" as "((_& $)& $)".
      - iRight. iDestruct "H" as "((((_& _)& $)& $)& $)".
    Qed.

    Lemma gl_variant_acc_cases E N k v P Q R :
      ↑N ⊆ E →
      gl_variant N k v P Q R ={E,E ∖ ↑N}=∗
      (▷ gl_variant_cases k v P Q R) ∗ (▷ gl_variant_cases k v P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      unfold_defs. iIntros (MASK) "((#Ge& #Gvl)& #Gvar)".
      iMod (glG_variant_acc with "Gvar") as "[[[H | H] | H] ACC]". 1: auto.
      - iModIntro. iSplitL "H".
        + iNext. iLeft. iLeft. iDestruct "H" as "($& $)". eauto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply gl_variant_cases_internal. unfold_defs. done.
      - iModIntro. iSplitL "H".
        + iNext. iLeft. iRight. iDestruct "H" as "($& $)". eauto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply gl_variant_cases_internal. unfold_defs. done.
      - iModIntro. iSplitL "H".
        + iNext. iRight. iDestruct "H" as "($& $& $)". eauto.
        + iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
          iNext. iApply gl_variant_cases_internal. unfold_defs. done.
    Qed.

    Lemma gl_variant_acc E N k v P Q R :
      ↑N ⊆ E →
      gl_variant N k v P Q R ={E,E ∖ ↑N}=∗
      (▷ (((gl_locked k v ∗ P) ∨ (gl_done k v ∗ Q)) ∨ (gl_expired k v ∗ R))) ∗
      (▷ gl_variant_cases k v P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      iIntros (H) "Gv". iMod (gl_variant_acc_cases with "Gv") as "[H $]". 1: auto.
      iModIntro. iNext. by iApply gl_variant_cases_unfold.
    Qed.

    Lemma gl_variant_acc_own E i G q N k v P Q R :
      ↑N ⊆ E →
      G !! k = Some v →
      th_obls i G q -∗
      gl_variant N k v P Q R ={E,E ∖ ↑N}=∗
      (▷ (th_obls i G q ∗ gl_locked k v ∗ P)) ∗
      (▷ gl_variant_cases k v P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      unfold_defs. iIntros (MASK LUGk) "(#Oe& Ox& Ob& OS) ((#Ge& #Gvl)& #Gvar)".
      iPoseProof (big_sepM_delete _ _ _ _ LUGk with "OS") as "[(_& Gl& [#Gseq Gv]& Go& Oo) OS]".
      iMod (glG_variant_acc_version_locked with "Gvar Gv Gl") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "Ox Ob Go Oo OS H".
      { iNext. iFrame "Oe Ox Ob". iDestruct "H" as "(Gv& Gl& $& $)".
        rewrite (big_sepM_delete _ _ _ _ LUGk). iFrame. eauto. }
      iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
      iNext. iApply gl_variant_cases_internal. unfold_defs. done.
    Qed.

    Lemma gl_variant_acc_done E N k v P Q R :
      ↑N ⊆ E →
      gl_done k v -∗
      gl_variant N k v P Q R ={E,E ∖ ↑N}=∗
      (▷ (Q ∨ (gl_expired k v ∗ R))) ∗
      (▷ gl_variant_cases k v P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      unfold_defs. iIntros (MASK) "((#Ge& #Gvl)& #Gu) (_& #Gvar)".
      iMod (glG_variant_acc_unlocked with "Gvar Gu") as "[H ACC]". 1: auto.
      iModIntro. iSplitL "H".
      { iNext. iDestruct "H" as "[$ | (_& #Gxp& HR)]". iRight. iFrame. auto. }
      iIntros "H". iMod ("ACC" with "[H]") as "_"; last done.
      iNext. iApply gl_variant_cases_internal. unfold_defs. done.
    Qed.

    Lemma gl_variant_acc_current_timeless E N k v q P Q R :
      Timeless R →
      ↑N ⊆ E →
      gl_current k v q -∗
      gl_variant N k v P Q R ={E,E ∖ ↑N}=∗
      (▷ (gl_current k v q ∗ (gl_locked k v ∗ P ∨ gl_done k v ∗ Q))) ∗
      (▷ gl_variant_cases k v P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      iIntros (TR MASK) "Gc #GV".
      iMod (gl_variant_acc with "GV") as "[H ACC]". 1: auto.
      iDestruct "H" as "[$ | H]".
      - iFrame "Gc". eauto.
      - iDestruct "H" as ">[#Gx _]". iPoseProof (gl_current_expired_false with "Gc Gx") as "%". done.
    Qed.

    Lemma gl_variant_acc_current_done_timeless E N k v q P Q R :
      Timeless R →
      ↑N ⊆ E →
      gl_current k v q -∗
      gl_done k v -∗
      gl_variant N k v P Q R ={E,E ∖ ↑N}=∗
      (▷ (gl_current k v q ∗ Q)) ∗
      (▷ gl_variant_cases k v P Q R ={E ∖ ↑N,E}=∗ True).
    Proof.
      iIntros (TR MASK) "Gc #Gd #GV".
      iMod (gl_variant_acc_done with "Gd GV") as "[[$ | >[Gx _]] ACC]". 1: auto.
      - iFrame "Gc". eauto.
      - iPoseProof (gl_current_expired_false with "Gc Gx") as "%". done.
    Qed.

  End fgupd.

End preds.
