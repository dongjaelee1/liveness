From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From liris.algebra Require Import ordinal_wfocm.
From liris.base_logic Require Export mupd.
Import uPred.

(** ** Modality for non-discharging (ghost) updates to obls. *)
Definition gupd_pre `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class}
  n Θ (gupd : iPropO Σ -d> iPropO Σ) : iProp Σ -d> iPropO Σ :=
  λ P,
    ((|={∅}=> P) ∨
       (∀ h i Ω1 W1,
          (model_interp h i Ω1 W1 n Θ) ={∅}=∗
          ∃ Ω2, (⌜ (Ω1 ↪ₙ∘ Ω2) ⌝) ∗
                (* ∀ W2, (⌜ (wits_mon W1 W2) ∧ owit_inv Ω2 W2 ⌝) ={∅}=∗ *)
                ∀ W2, (⌜ (W1 ↓ₙ∘ W2) ∧ owit_inv Ω2 W2 ⌝) ={∅}=∗
                      (model_interp (h ++ [(n, Ω2)]) (S i) Ω2 W2 n Θ) ∗ gupd P))%I.

Lemma gupd_pre_mono `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class}
  n Θ (gupd1 gupd2 : iPropO Σ -d> iPropO Σ) :
  ⊢ ((□ ∀ P, gupd1 P -∗ gupd2 P) →
     ∀ P, gupd_pre n Θ gupd1 P -∗ gupd_pre n Θ gupd2 P)%I.
Proof.
  iIntros "#Hmono"; iIntros (P) "Hgupd". rewrite /gupd_pre.
  iDestruct "Hgupd" as "[H | Hgupd]".
  { iLeft. done. }
  iRight. iIntros (????) "I". iMod ("Hgupd" with "[$I]") as "(%& %& H)".
  iModIntro. iExists _. iSplitR; first done. iIntros (??).
  iMod ("H" with "[//]") as "[$ H]". by iApply "Hmono".
Qed.

Local Instance gupd_pre_mono' `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class} n Θ :
  BiMonoPred (gupd_pre n Θ).
Proof.
  constructor.
  - iIntros (gupd1 gupd2 NE1 NE2) "#H". iApply gupd_pre_mono. iModIntro. iApply "H".
  - intros gupd Hgupd ? P1 P2 ?. rewrite /gupd_pre.
    do 21 (f_equiv || done).
Qed.

(* take the least fixpoint of the above definition *)
Local Definition gupd_def `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class} n Θ : iProp Σ → iProp Σ :=
  λ P, ((bi_least_fixpoint (gupd_pre n Θ)) P)%I.
Local Definition gupd_aux : seal (@gupd_def). by eexists. Qed.
Definition gupd := gupd_aux.(unseal).
Arguments gupd {SI Σ _ _}.
Local Definition gupd_unseal : @gupd = @gupd_def := gupd_aux.(seal_eq).
Notation "'|=[' n , Θ ']=>g' P" := (gupd n Θ P) (at level 99, P at level 200, format "|=[ n , Θ ]=>g  P").

Section gupd.
  Context `{SI : indexT} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.
  Implicit Type Θ : (gset positive).

  Lemma gupd_unfold n Θ P :
    (|=[n,Θ]=>g P) ⊣⊢ (gupd_pre n Θ (gupd n Θ) P).
  Proof.
    rewrite gupd_unseal. rewrite /gupd_def.
    rewrite (least_fixpoint_unfold (gupd_pre n Θ)). done.
  Qed.

  Global Instance gupd_ne n Θ :
    NonExpansive (gupd n Θ).
  Proof. intros ? P1 P2 HP. rewrite !gupd_unseal /gupd_def. f_equiv. done. Qed.
  Global Instance gupd_proper n Θ :
    Proper ((≡) ==> (≡)) (gupd n Θ).
  Proof. intros P P' ?. apply equiv_dist=>?. apply gupd_ne. apply equiv_dist. done. Qed.

  Lemma gupd_ind_strong (Ψ : iProp Σ → iProp Σ) n Θ :
    (∀ i, Proper (dist i ==> dist i) Ψ) →
    ⊢ (□ (∀ P, gupd_pre n Θ (λ P, Ψ P ∧ |=[n,Θ]=>g P) P -∗ Ψ P)
       → ∀ P, (|=[n,Θ]=>g P) -∗ Ψ P)%I.
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

  Lemma gupd_ind n Θ Ψ :
    (∀ i, Proper (dist i ==> dist i) Ψ)
    → ⊢ (□ (∀ P, gupd_pre n Θ (λ P, Ψ P) P -∗ Ψ P)
         → ∀ P, (|=[n,Θ]=>g P) -∗ Ψ P)%I.
  Proof.
    iIntros (HΨ) "#H". iApply gupd_ind_strong. iIntros "!>" (P) "Hgupd".
    iApply "H". iApply (gupd_pre_mono with "[] Hgupd").
    iIntros "!>" (?) "[$ _]".
  Qed.

  (** An empty fancy update can be turned into an obl update. *)
  Lemma fupd_gupd n Θ P : (|={∅}=> P) ⊢ (|=[n,Θ]=>g P).
  Proof. rewrite gupd_unfold. iIntros "Hupd". iLeft. done. Qed.

  (** We can always introduce a obl update. *)
  Lemma gupd_intro n Θ P : P ⊢ |=[n,Θ]=>g P.
  Proof. rewrite gupd_unfold. iIntros "HP". iLeft. iModIntro. done. Qed.

  (** We can always eliminate an empty fancy update. *)
  Lemma fupd_gupd_elim n Θ P :
    (|={∅}=> |=[n,Θ]=>g P) ⊢ |=[n,Θ]=>g P.
  Proof.
    iIntros "H". iApply gupd_unfold.
    iRight. iIntros (????) "I". iMod "H".
    iModIntro. iExists Ω1. iSplitR; first done.
    iIntros (? (Prog& OW2)).
    rewrite /model_interp. iDestruct "I" as "(HI& $& $& $& $& N& %OW1)".
    iMod (model_history_interp_step with "HI") as "$". 1,2: done.
    iModIntro.
    unshelve epose proof (owit_inv_rc_step_same_gls _ _ _ OW1 _ OW2).
    { inv Prog; eauto. econstructor 2. by apply wits_nd_step_wits_step. }
    iPoseProof (owit_mon _ _ H with "N") as "$". iFrame. done.
  Qed.

  (** We can combine two obl updates into one. *)
  Lemma gupd_bind n Θ P Q :
    (P -∗ |=[n,Θ]=>g Q) ⊢ (|=[n,Θ]=>g P) -∗ (|=[n,Θ]=>g Q).
  Proof.
    iIntros "H HP". iRevert (Q) "H". iRevert (P) "HP".
    iApply gupd_ind_strong.
    { solve_proper. }
    iIntros "!> %P IH %Q H". iDestruct "IH" as "[IH | IH]".
    - iApply fupd_gupd_elim. iMod "IH". iModIntro. iApply ("H" with "IH").
    - iApply gupd_unfold. iRight. iIntros (????) "I".
      iMod ("IH" with "I") as "(%&%& IH)".
      iModIntro. iExists _. iSplitR; first done.
      iIntros (??). iMod ("IH" with "[//]") as "[$ IH]".
      iModIntro. iDestruct "IH" as "[IH _]".
      iApply "IH". done.
  Qed.

  Lemma obls_nd_step_owit_inv_wits_nd_step Ω1 Ω2 W1 W2 :
    owit_inv Ω1 W1 →
    Ω1 ↪ₙ∘ Ω2 →
    W1 ↓∘ W2 →
    owit_inv Ω2 W2 →
    W1 ↓ₙ∘ W2.
  Proof.
    intros OI1 OS WS OI2. inv WS. 1: done. inv H.
    - destruct H0 as (?&?&?&?&?&?). inv H0.
      + econstructor 2. econstructor. do 3 eexists. split_and !; eauto.
      + inv H2. specialize (OI2 x). rewrite lookup_insert_eq in OI2. inv OI2. destruct x0; try done.
        specialize (OI1 x). rewrite H in OI1. inv OI1. destruct x0; try done. inv OS.
        { by rewrite -H0 in H1. }
        inv H3.
        { destruct H5 as (?&?&?&?&?&?). inv H5. destruct (decide (x = x0)).
          - subst. rewrite lookup_insert_eq in H0. inv H0.
          - rewrite lookup_insert_ne in H0; auto. rewrite -H0 in H1. done. }
        { destruct H5 as (?&?&?&?). destruct (decide (x = x0)).
          - subst. rewrite H3 in H1. done.
          - subst. rewrite lookup_insert_ne in H0; auto. rewrite -H0 in H1. done. }
    - econstructor 2. econstructor 2. auto.
  Qed.

  Lemma gupd_mupd n Θ P :
    (|=[n,Θ]=>g P) ⊢ |=[n,Θ]=>m P.
  Proof.
    iIntros "H". iRevert (P) "H".
    iApply gupd_ind_strong.
    iIntros "!> %P IH". iDestruct "IH" as "[IH | IH]".
    - iMod "IH". iModIntro. iModIntro. done.
    - iApply mupd_unfold. iRight. iIntros (????) "I".
      iPoseProof (model_interp_owit_inv with "I") as "%Hinv".
      iMod ("IH" with "I") as "(%&%& IH)".
      iModIntro. iExists _. iSplit.
      { iPureIntro. inv H. 1: done. econstructor 2. by apply obls_nd_step_obls_step. }
      iIntros (??). destruct H0. pose proof (obls_nd_step_owit_inv_wits_nd_step _ _ _ _ Hinv H H0 H1).
      iMod ("IH" with "[//]") as "[$ IH]".
      iModIntro. iDestruct "IH" as "[IH _]". done.
  Qed.

  (* derived lemmas *)
  Lemma gupd_mono n Θ P Q : (P ⊢ Q) → (|=[n,Θ]=>g P) ⊢ (|=[n,Θ]=>g Q).
  Proof.
    intros Hent. iApply gupd_bind.
    iIntros "P"; iApply gupd_intro; by iApply Hent.
  Qed.
  Lemma gupd_trans n Θ P :  (|=[n,Θ]=>g |=[n,Θ]=>g P) ⊢ |=[n,Θ]=>g P.
  Proof.
    iIntros "HP". iApply gupd_bind; eauto.
  Qed.
  Lemma gupd_frame_r n Θ P R : (|=[n,Θ]=>g P) ∗ R ⊢ |=[n,Θ]=>g P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (gupd_bind with "[R]"); last done.
    iIntros "P". iApply gupd_intro. by iFrame.
  Qed.

  Global Instance gupd_ent_proper n Θ : Proper ((⊢) ==> (⊢)) (gupd n Θ).
  Proof. intros P Q PQ. by apply gupd_mono. Qed.
  Global Instance gupd_flip_ent_proper n Θ : Proper (flip (⊢) ==> flip (⊢)) (gupd n Θ).
  Proof. intros P Q PQ; by apply gupd_mono. Qed.
  Global Instance gupd_equiv_proper n Θ : Proper ((≡) ==> (≡)) (gupd n Θ) := ne_proper _.

  Lemma gupd_fupd_l n Θ P :
    (|={∅}=> |=[n,Θ]=>g P) ⊢ (|=[n,Θ]=>g P).
  Proof.
    by erewrite fupd_gupd, gupd_trans.
  Qed.
  Lemma gupd_fupd_r n Θ P :
    (|=[n,Θ]=>g |={∅}=> P) ⊢ (|=[n,Θ]=>g P).
  Proof.
    by erewrite fupd_gupd, gupd_trans.
  Qed.

  Lemma gupd_frame_l n Θ R Q : (R ∗ |=[n,Θ]=>g Q) ⊢ |=[n,Θ]=>g R ∗ Q.
  Proof. rewrite !(comm _ R); apply gupd_frame_r. Qed.
  Lemma gupd_wand_l n Θ P Q : (P -∗ Q) ∗ (|=[n,Θ]=>g P) ⊢ |=[n,Θ]=>g Q.
  Proof. by rewrite gupd_frame_l wand_elim_l. Qed.
  Lemma gupd_wand_r n Θ P Q : (|=[n,Θ]=>g P) ∗ (P -∗ Q) ⊢ |=[n,Θ]=>g Q.
  Proof. by rewrite gupd_frame_r wand_elim_r. Qed.
  Lemma gupd_sep n Θ P Q : (|=[n,Θ]=>g P) ∗ (|=[n,Θ]=>g Q) ⊢ |=[n,Θ]=>g P ∗ Q.
  Proof. by rewrite gupd_frame_r gupd_frame_l gupd_trans. Qed.
  Lemma gupd_idemp n Θ P : (|=[n,Θ]=>g |=[n,Θ]=>g P) ⊣⊢ |=[n,Θ]=>g P.
  Proof.
    apply: anti_symm.
    - apply gupd_trans.
    - apply gupd_intro.
  Qed.

  Global Instance gupd_homomorphism n Θ :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (gupd n Θ).
  Proof. split; [split|]; try apply _; [apply gupd_sep | apply gupd_intro]. Qed.

  Lemma big_sepL_gupd {A} (Φ : nat → A → iProp Σ) n Θ l :
    ([∗ list] k↦x ∈ l, |=[n,Θ]=>g Φ k x) ⊢ |=[n,Θ]=>g [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_gupd {A} `{Countable K} (Φ : K → A → iProp Σ) n Θ l :
    ([∗ map] k↦x ∈ l, |=[n,Θ]=>g Φ k x) ⊢ |=[n,Θ]=>g [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_gupd `{Countable A} (Φ : A → iProp Σ) n Θ l :
    ([∗ set]  x ∈ l, |=[n,Θ]=>g Φ x) ⊢ |=[n,Θ]=>g [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_gupd `{Countable A} (Φ : A → iProp Σ) n Θ l :
    ([∗ mset] x ∈ l, |=[n,Θ]=>g Φ x) ⊢ |=[n,Θ]=>g [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_gupd n Θ P : ◇ (|=[n,Θ]=>g P) ⊢ (|=[n,Θ]=>g ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using gupd_mono, or_intro_r.
    by rewrite -gupd_intro -or_intro_l.
  Qed.

  Lemma owit_inv_exists_witnesses_nd γ Ω1 Ω2 W1 :
    owit_inv_lb_mon γ →
    Ω1 ↪ₙ∘ Ω2 →
    owit_inv Ω1 W1 →
    owit_inv_lb γ Ω1 W1 →
    ∃ W2, W1 ↓ₙ∘ W2 ∧ owit_inv Ω2 W2 ∧ owit_inv_lb γ Ω2 W2.
  Proof.
    intros [GMon GSched] Step Inv LB. destruct Step.
    { subst. exists W1. eauto. }
    inv H.
    - destruct H0 as (?&?&?&?&?&?). subst.
      pose proof Inv as Inv2. specialize (Inv2 x). rewrite H in Inv2. inv Inv2.
      inv H0. destruct y; try done. symmetry in H2.
      pose proof LB as LB2. specialize (LB2 x). rewrite H H2 in LB2. inv LB2.
      exists (<[x:=(witness_assigned (OC:=ord_obl_class) (γ o2 f2))]>W1). split_and !.
      { econstructor 2. econstructor. exists x. do 2 eexists. split_and !; eauto. econstructor.
        eapply WFOCM.lt_le_lt. 2: eauto. apply GMon. auto. }
      { intros ?. destruct (decide (i = x)).
        - subst. rewrite !lookup_insert_eq. econstructor. apply GSched.
        - rewrite !lookup_insert_ne; eauto. }
      { intros ?. destruct (decide (i = x)).
        - subst. rewrite !lookup_insert_eq. econstructor. done.
        - rewrite !lookup_insert_ne; eauto. }
    - pose proof Inv as Dom. apply owit_inv_dom in Dom. destruct H0 as (k& LUO& ?& ?). destruct x.
      + exists (<[k:=(witness_assigned (OC:=ord_obl_class) (η fuel))]>W1). split_and !.
        * econstructor 2. econstructor 2. exists k. split; eauto.
          apply not_elem_of_dom. apply not_elem_of_dom in LUO. rewrite -Dom. auto.
        * subst. intros ?. destruct (decide (i = k)).
          { subst. rewrite !lookup_insert_eq. econstructor. done. }
          { rewrite !lookup_insert_ne; eauto. }
        * subst. intros ?. destruct (decide (i = k)).
          { subst. rewrite !lookup_insert_eq. econstructor. eapply GSched. }
          { rewrite !lookup_insert_ne; eauto. }
      + exists (<[k:=(witness_discharged)]>W1). split_and !.
        * econstructor 2. econstructor 2. exists k. split; eauto.
          apply not_elem_of_dom. apply not_elem_of_dom in LUO. rewrite -Dom. auto.
        * subst. intros ?. destruct (decide (i = k)).
          { subst. rewrite !lookup_insert_eq. econstructor. split; done. }
          { rewrite !lookup_insert_ne; eauto. }
        * subst. intros ?. destruct (decide (i = k)).
          { subst. rewrite !lookup_insert_eq. econstructor. split; done. }
          { rewrite !lookup_insert_ne; eauto. }
  Qed.

  Lemma model_interp_gupd_steps (γ : obl_owner → obl_fuel → obl_fuel) h i Ω W n Θ P :
    owit_inv_lb_mon γ →
    (owit_inv_lb γ Ω W) →
    (|=[n,Θ]=>g P) -∗ model_interp h i Ω W n Θ ={∅}=∗
    (P ∗ ∃ h' i' Ω' W', ⌜ obls_nd Ω Ω' ∧ owit_inv_lb γ Ω' W' ⌝ ∗ model_interp (h ++ h') (i + i') Ω' W' n Θ).
  Proof.
    iIntros ([GMon GSched] LB) "H". iRevert (h i Ω W LB). iRevert (P) "H".
    iApply gupd_ind_strong.
    { solve_proper. }
    iIntros "!> %P IH %%%% %LB H". iDestruct "IH" as "[IH | IH]".
    { iMod "IH". iModIntro. iFrame. iExists [], 0, _, _. rewrite app_nil_r Nat.add_0_r. iFrame. done. }
    iPoseProof (model_interp_owit_inv with "H") as "%".
    iMod ("IH" with "H") as "(%&%& IH)".
    unshelve epose proof (owit_inv_exists_witnesses_nd γ _ _ _ _ H0 H LB).
    1: split; auto.
    destruct H1 as (W2& WProg& Inv2& LB2).
    iMod ("IH" $! W2 with "[//]") as "[G [IH _]]". iMod ("IH" with "[] G") as "[$ (%&%&%&%& %LEO& MI)]".
    1: eauto.
    iModIntro. iExists ([(n, Ω2)] ++ h'), (S i'), _, _.
    replace (h ++ [(n, Ω2)] ++ h') with ((h ++ [(n, Ω2)]) ++ h'); cycle 1.
    { by rewrite app_assoc. }
    replace (i + S i') with (S i + i') by lia. iFrame.
    iPureIntro. destruct LEO as [LEO ?]. split; auto.
    etrans; last eapply LEO. apply obls_nd_step_rc_obls_nd; auto.
  Qed.

  (* The following instances make the Iris Proof Mode aware of the
     obl update. They are derived from the simpler rules above. *)
  (* Global Instance elim_fupd_gupd (p : bool) n Θ P Q : *)
  (*   ElimModal True p false (|={∅}=> P) P (|=[n,Θ]=>g Q) (|=[n,Θ]=>g Q)%I. *)
  (* Proof. *)
  (*   rewrite /ElimModal bi.intuitionistically_if_elim //=. *)
  (*   rewrite fupd_gupd. *)
  (*   iIntros "_ [HP HPQ]". iApply (gupd_bind with "HPQ HP"). *)
  (* Qed. *)

  Global Instance elim_fupd_gupd (p : bool) E n Θ P Q :
    ElimModal True p false (|={∅,E}=> P) P (|=[n,Θ]=>g Q) (|={E,∅}=> |=[n,Θ]=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_gupd_elim. iMod "HP".
    by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_gupd n Θ P Q :
    AddModal (|={∅}=> P) P (|=[n,Θ]=>g Q).
  Proof.
    rewrite /AddModal; rewrite fupd_gupd; iIntros "[HP HPQ]".
    iApply (gupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_gupd p n Θ P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|=[n,Θ]=>g Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply gupd_intro. Qed.

  Global Instance from_pure_gupd a n Θ P φ :
    FromPure a P φ → FromPure a (|=[n,Θ]=>g P) φ.
  Proof. rewrite /FromPure=> <-. apply gupd_intro. Qed.

  Global Instance into_wand_gupd p q n Θ R P Q :
    IntoWand false false R P Q → IntoWand p q (|=[n,Θ]=>g R) (|=[n,Θ]=>g P) (|=[n,Θ]=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite gupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_gupd_persistent p q n Θ R P Q :
    IntoWand false q R P Q → IntoWand p q (|=[n,Θ]=>g R) P (|=[n,Θ]=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite gupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_gupd_args p q n Θ R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|=[n,Θ]=>g P) (|=[n,Θ]=>g Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim gupd_wand_r.
  Qed.

  Global Instance from_sep_gupd n Θ P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|=[n,Θ]=>g P) (|=[n,Θ]=>g Q1) (|=[n,Θ]=>g Q2).
  Proof. rewrite /FromSep=><-. apply gupd_sep. Qed.

  Global Instance from_or_gupd n Θ P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|=[n,Θ]=>g P) (|=[n,Θ]=>g Q1) (|=[n,Θ]=>g Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply gupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_gupd {A} n Θ P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|=[n,Θ]=>g P) (λ a, |=[n,Θ]=>g Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_gupd n Θ P : IsExcept0 P → IsExcept0 (|=[n,Θ]=>g P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_gupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_gupd n Θ P :
    FromModal True modality_id (|=[n,Θ]=>g P) (|=[n,Θ]=>g P) P.
  Proof. by rewrite /FromModal /= -gupd_intro. Qed.

  Global Instance elim_modal_gupd p n Θ P Q :
    ElimModal True p false (|=[n,Θ]=>g P) P (|=[n,Θ]=>g Q) (|=[n,Θ]=>g Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim gupd_frame_r wand_elim_r gupd_trans.
  Qed.

  Global Instance add_modal_gupd n Θ P Q : AddModal (|=[n,Θ]=>g P) P (|=[n,Θ]=>g Q).
  Proof. by rewrite /AddModal gupd_frame_r wand_elim_r gupd_trans. Qed.

  Global Instance frame_gupd p n Θ R P Q :
    Frame p R P Q → Frame p R (|=[n,Θ]=>g P) (|=[n,Θ]=>g Q).
  Proof. rewrite /Frame=><-. by rewrite gupd_frame_l. Qed.

  Global Instance elim_modal_gupd_mupd p n Θ P Q :
    ElimModal True p false (|=[n,Θ]=>g P) P (|=[n,Θ]=>m Q) (|=[n,Θ]=>m Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim gupd_frame_r wand_elim_r.
    iIntros (_) "H". iApply mupd_trans. iApply gupd_mupd. done.
  Qed.

End gupd.

(* Wrapper to use fupd. *)
Definition fgupd `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class} E1 E2 n Θ : iPropO Σ -d> iPropO Σ :=
  (λ P, |={E1,∅}=> |=[n,Θ]=>g |={∅,E2}=> P)%I.
Notation "'|={' E1 , E2 : n , Θ '}=>g' P" := (fgupd E1 E2 n Θ P) (at level 99, P at level 200, format "|={ E1 , E2 : n , Θ }=>g  P").
Notation "'|={' E : n , Θ '}=>g' P" := (fgupd E E n Θ P) (at level 99, P at level 200, format "|={ E : n , Θ }=>g  P").

Section fgupd.
  Context `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class}.
  Implicit Type Θ : (gset positive).

  Global Instance fgupd_ne E1 E2 n Θ : NonExpansive (fgupd E1 E2 n Θ).
  Proof. intros ? P1 P2 HP. rewrite /fgupd. do 12 (f_equiv || done). Qed.
  Global Instance fgupd_proper E1 E2 n Θ : Proper ((≡) ==> (≡)) (fgupd E1 E2 n Θ).
  Proof. intros P P' ?. apply equiv_dist=>?. apply fgupd_ne. apply equiv_dist. done. Qed.

  Lemma fupd_fgupd E1 E2 n Θ P : (|={E1,E2}=> P) ⊢ (|={E1,E2:n,Θ}=>g P).
  Proof.
    rewrite /fgupd. iIntros ">Hupd".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose !>". iMod "Hclose" as "_".
    iModIntro. iFrame.
  Qed.

  Lemma gupd_fgupd E n Θ P : (|=[n,Θ]=>g P) ⊢ (|={E:n,Θ}=>g P).
  Proof.
    rewrite /fgupd. iIntros "Hupd".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose". iMod "Hupd".
    iModIntro. iMod "Hclose". by iFrame.
  Qed.

  Lemma fgupd_intro E n Θ P : P ⊢ |={E:n,Θ}=>g P.
  Proof.
    iIntros "$". iMod (fupd_mask_subseteq ∅) as "Hclose". 1: set_solver.
    iIntros "!> !>". iMod "Hclose". done.
  Qed.

  Lemma fupd_fgupd_elim E1 E2 n Θ P :
    (|={E1}=> |={E1,E2:n,Θ}=>g P) ⊢ |={E1,E2:n,Θ}=>g P.
  Proof.
    iIntros "H". iMod "H". iApply "H".
  Qed.

  Lemma fupd_fgupd_elim_2 E1 E2 n Θ P :
    (|={E1,E2:n,Θ}=>g |={E2}=> P) ⊢ |={E1,E2:n,Θ}=>g P.
  Proof.
    iIntros "H". iMod "H". iModIntro. iMod "H" as ">H".
    iMod "H" as "$". iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    iModIntro. by iMod "close".
  Qed.

  Lemma gupd_fgupd_elim E1 E2 n Θ P :
    (|=[n,Θ]=>g |={E1,E2:n,Θ}=>g P) ⊢ |={E1,E2:n,Θ}=>g P.
  Proof.
    iIntros "H". iApply fupd_mask_intro. 1: set_solver.
    iIntros "Fupd". iMod "H". iMod "Fupd" as "_". done.
  Qed.

  (** Change to a larger mask. *)
  Lemma fgupd_mask_mono E1 E2 n Θ P :
    E1 ⊆ E2 →
    (|={E1:n,Θ}=>g P) ⊢ |={E2:n,Θ}=>g P.
  Proof.
    iIntros (Sub) "H".
    iMod (fupd_mask_subseteq E1) as "close". 1: done.
    iMod "H". iModIntro. iMod "H" as "H".
    iModIntro. iMod "H" as "$". eauto.
  Qed.

  (** We can combine two obl updates into one. *)
  Lemma fgupd_bind E1 E2 E3 n Θ P Q :
    (P -∗ |={E2,E3:n,Θ}=>g Q) ⊢ (|={E1,E2:n,Θ}=>g P) -∗ (|={E1,E3:n,Θ}=>g Q).
  Proof.
    iIntros "H >HP".
    iModIntro. iMod "HP" as ">HP".
    iPoseProof ("H" with "HP") as "H". done.
  Qed.

  (* derived lemmas *)
  Lemma fgupd_mono E1 E2 n Θ P Q : (P ⊢ Q) → (|={E1,E2:n,Θ}=>g P) ⊢ (|={E1,E2:n,Θ}=>g Q).
  Proof.
    intros Hent. iApply fgupd_bind.
    iIntros "P"; iApply fgupd_intro; by iApply Hent.
  Qed.
  Lemma fgupd_trans E1 E2 E3 n Θ P :  (|={E1,E3:n,Θ}=>g |={E3,E2:n,Θ}=>g P) ⊢ |={E1,E2:n,Θ}=>g P.
  Proof.
    iIntros "HP". iApply fgupd_bind; eauto.
  Qed.
  Lemma fgupd_frame_r E1 E2 n Θ P R : (|={E1,E2:n,Θ}=>g P) ∗ R ⊢ |={E1,E2:n,Θ}=>g P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (fgupd_bind with "[R]"); last done.
    iIntros "P". iApply fgupd_intro. by iFrame.
  Qed.

  Global Instance fgupd_ent_proper E1 E2 n Θ : Proper ((⊢) ==> (⊢)) (fgupd E1 E2 n Θ).
  Proof. intros P Q PQ. by apply fgupd_mono. Qed.
  Global Instance fgupd_flip_ent_proper E1 E2 n Θ : Proper (flip (⊢) ==> flip (⊢)) (fgupd E1 E2 n Θ).
  Proof. intros P Q PQ; by apply fgupd_mono. Qed.
  Global Instance fgupd_equiv_proper E1 E2 n Θ : Proper ((≡) ==> (≡)) (fgupd E1 E2 n Θ) := ne_proper _.

  Lemma fgupd_fupd_l E1 E2 n Θ P :
    (|={E1,E2}=> |={E2:n,Θ}=>g P) ⊢ (|={E1,E2:n,Θ}=>g P).
  Proof.
    by erewrite fupd_fgupd, fgupd_trans.
  Qed.
  Lemma fgupd_fupd_r E1 E2 n Θ P :
    (|={E1:n,Θ}=>g |={E1,E2}=> P) ⊢ (|={E1,E2:n,Θ}=>g P).
  Proof.
    by erewrite fupd_fgupd, fgupd_trans.
  Qed.

  Lemma fgupd_frame_l E1 E2 n Θ R Q : (R ∗ |={E1,E2:n,Θ}=>g Q) ⊢ |={E1,E2:n,Θ}=>g R ∗ Q.
  Proof. rewrite !(comm _ R); apply fgupd_frame_r. Qed.
  Lemma fgupd_wand_l E1 E2 n Θ P Q : (P -∗ Q) ∗ (|={E1,E2:n,Θ}=>g P) ⊢ |={E1,E2:n,Θ}=>g Q.
  Proof. by rewrite fgupd_frame_l wand_elim_l. Qed.
  Lemma fgupd_wand_r E1 E2 n Θ P Q : (|={E1,E2:n,Θ}=>g P) ∗ (P -∗ Q) ⊢ |={E1,E2:n,Θ}=>g Q.
  Proof. by rewrite fgupd_frame_r wand_elim_r. Qed.
  Lemma fgupd_sep E n Θ P Q : (|={E:n,Θ}=>g P) ∗ (|={E:n,Θ}=>g Q) ⊢ |={E:n,Θ}=>g P ∗ Q.
  Proof. by rewrite fgupd_frame_r fgupd_frame_l fgupd_trans. Qed.
  Lemma fgupd_sep_l E1 E2 E3 n Θ P Q : (|={E1,E3:n,Θ}=>g P) ∗ (|={E3,E2:n,Θ}=>g Q) ⊢ |={E1,E2:n,Θ}=>g P ∗ Q.
  Proof. rewrite fgupd_frame_r fgupd_frame_l. apply fgupd_trans. Qed.
  Lemma fgupd_sep_r E1 E2 E3 n Θ P Q : (|={E3,E2:n,Θ}=>g P) ∗ (|={E1,E3:n,Θ}=>g Q) ⊢ |={E1,E2:n,Θ}=>g P ∗ Q.
  Proof. rewrite bi.sep_comm. rewrite fgupd_frame_r fgupd_frame_l bi.sep_comm. apply fgupd_trans. Qed.
  Lemma fgupd_idemp E n Θ P : (|={E:n,Θ}=>g |={E:n,Θ}=>g P) ⊣⊢ |={E:n,Θ}=>g P.
  Proof.
    apply: anti_symm.
    - apply fgupd_trans.
    - apply fgupd_intro.
  Qed.

  Global Instance fgupd_homomorphism E n Θ :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (fgupd E E n Θ).
  Proof. split; [split|]; try apply _; [apply fgupd_sep | apply fgupd_intro]. Qed.

  Lemma big_sepL_fgupd {A} (Φ : nat → A → iProp Σ) E n Θ l :
    ([∗ list] k↦x ∈ l, |={E:n,Θ}=>g Φ k x) ⊢ |={E:n,Θ}=>g [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_fgupd {A} `{Countable K} (Φ : K → A → iProp Σ) E n Θ l :
    ([∗ map] k↦x ∈ l, |={E:n,Θ}=>g Φ k x) ⊢ |={E:n,Θ}=>g [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_fgupd `{Countable A} (Φ : A → iProp Σ) E n Θ l :
    ([∗ set]  x ∈ l, |={E:n,Θ}=>g Φ x) ⊢ |={E:n,Θ}=>g [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_fgupd `{Countable A} (Φ : A → iProp Σ) E n Θ l :
    ([∗ mset] x ∈ l, |={E:n,Θ}=>g Φ x) ⊢ |={E:n,Θ}=>g [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_fgupd E1 E2 n Θ P : ◇ (|={E1,E2:n,Θ}=>g P) ⊢ (|={E1,E2:n,Θ}=>g ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using fgupd_mono, or_intro_r.
    rewrite -fupd_fgupd. iIntros "H". iApply except_0_fupd. iMod "H". done.
  Qed.

  Global Instance elim_fupd_fgupd (p : bool) E1 E2 E3 n Θ P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3:n,Θ}=>g Q) (|={E2,E3:n,Θ}=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fgupd_trans.
    iApply fupd_fgupd. iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_gupd_fgupd (p : bool) E1 E2 n Θ P Q :
    ElimModal True p false (|=[n,Θ]=>g P) P (|={E1,E2:n,Θ}=>g Q) (|={E1,E2:n,Θ}=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply gupd_fgupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_fgupd E1 E2 n Θ P Q :
    AddModal (|={E1}=> P) P (|={E1,E2:n,Θ}=>g Q).
  Proof.
    rewrite /AddModal; rewrite fupd_fgupd; iIntros "[HP HPQ]".
    iApply (fgupd_bind with "HPQ HP").
  Qed.

  Global Instance add_modal_gupd_fgupd E1 E2 n Θ P Q :
    AddModal (|=[n,Θ]=>g P) P (|={E1,E2:n,Θ}=>g Q).
  Proof.
    rewrite /AddModal; rewrite gupd_fgupd; iIntros "[HP HPQ]".
    iApply (fgupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_fgupd p E n Θ P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|={E:n,Θ}=>g Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply fgupd_intro. Qed.

  Global Instance from_pure_fgupd a E n Θ P φ :
    FromPure a P φ → FromPure a (|={E:n,Θ}=>g P) φ.
  Proof. rewrite /FromPure=> <-. apply fgupd_intro. Qed.

  Global Instance into_wand_fgupd p q E n Θ R P Q :
    IntoWand false false R P Q → IntoWand p q (|={E:n,Θ}=>g R) (|={E:n,Θ}=>g P) (|={E:n,Θ}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite fgupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_fgupd_persistent p q E1 E2 n Θ R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E1,E2:n,Θ}=>g R) P (|={E1,E2:n,Θ}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite fgupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_fgupd_args p q E1 E2 n Θ R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E1,E2:n,Θ}=>g P) (|={E1,E2:n,Θ}=>g Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim fgupd_wand_r.
  Qed.

  Global Instance from_sep_fgupd E n Θ P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E:n,Θ}=>g P) (|={E:n,Θ}=>g Q1) (|={E:n,Θ}=>g Q2).
  Proof. rewrite /FromSep=><-. apply fgupd_sep. Qed.

  Global Instance from_or_fgupd E1 E2 n Θ P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E1,E2:n,Θ}=>g P) (|={E1,E2:n,Θ}=>g Q1) (|={E1,E2:n,Θ}=>g Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply fgupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_fgupd {A} E1 E2 n Θ P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E1,E2:n,Θ}=>g P) (λ a, |={E1,E2:n,Θ}=>g Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_fgupd E1 E2 n Θ P : IsExcept0 P → IsExcept0 (|={E1,E2:n,Θ}=>g P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_fgupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_fgupd E n Θ P :
    FromModal True modality_id (|={E:n,Θ}=>g P) (|={E:n,Θ}=>g P) P.
  Proof. by rewrite /FromModal /= -fgupd_intro. Qed.

  Global Instance elim_modal_fgupd p E1 E2 E3 n Θ P Q :
    ElimModal True p false (|={E1,E2:n,Θ}=>g P) P (|={E1,E3:n,Θ}=>g Q) (|={E2,E3:n,Θ}=>g Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim fgupd_frame_r wand_elim_r fgupd_trans.
  Qed.

  Global Instance add_modal_fgupd E1 E2 n Θ P Q : AddModal (|={E1:n,Θ}=>g P) P (|={E1,E2:n,Θ}=>g Q).
  Proof. by rewrite /AddModal fgupd_frame_r wand_elim_r fgupd_trans. Qed.

  Global Instance frame_fgupd p E1 E2 n Θ R P Q :
    Frame p R P Q → Frame p R (|={E1,E2:n,Θ}=>g P) (|={E1,E2:n,Θ}=>g Q).
  Proof. rewrite /Frame=><-. by rewrite fgupd_frame_l. Qed.

  Global Instance elim_modal_fgupd_fmupd p E1 E2 E3 n Θ P Q :
    ElimModal True p false (|={E1,E2:n,Θ}=>g P) P (|={E1,E3:n,Θ}=>m Q) (|={E2,E3:n,Θ}=>m Q).
  Proof.
    rewrite /ElimModal intuitionistically_if_elim fgupd_frame_r wand_elim_r.
    iIntros (_) "H". iMod "H". iModIntro. iMod "H". iMod "H". done.
  Qed.

End fgupd.
