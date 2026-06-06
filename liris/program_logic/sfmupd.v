From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From liris.base_logic Require Export opreds.
From liris.program_logic Require Export history_interp.
Import uPred.

Local Definition sfmupd_def `{SI : indexT} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}
  `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))}
  E : iPropO Σ -d> iPropO Σ :=
  (λ P, ∀ h n σ Θ κs, (history_interp h n σ Θ κs) -∗ |={E:n,dom Θ}=>m (history_interp h n σ Θ κs) ∗ P)%I.
Local Definition sfmupd_aux : seal (@sfmupd_def). Proof. by eexists. Qed.
Definition sfmupd := sfmupd_aux.(unseal).
Global Arguments sfmupd {SI Λ Σ _ _ _ _}.
Local Lemma sfmupd_unseal `{SI : indexT} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}
  `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))} :
  sfmupd = @sfmupd_def SI Λ Σ _ _ _ _.
Proof. rewrite -sfmupd_aux.(seal_eq) //. Qed.

Ltac unfold_sfmupd := rewrite sfmupd_unseal /sfmupd_def.

Notation "'|={' E '}=>m' P" := (sfmupd E P) (at level 99, P at level 200, format "|={ E }=>m  P").

Section sfmupd.
  Context `{SI : indexT} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))}.

  Global Instance sfmupd_ne E : NonExpansive (sfmupd E).
  Proof. intros n P1 P2 HP. rewrite sfmupd_unseal /sfmupd_def. do 14 (f_equiv || done). Qed.
  Global Instance sfmupd_proper E : Proper ((≡) ==> (≡)) (sfmupd E).
  Proof. intros P P' ?. apply equiv_dist=>n. apply sfmupd_ne. apply equiv_dist. done. Qed.

  Lemma fupd_sfmupd E P : (|={E}=> P) ⊢ (|={E}=>m P).
  Proof.
    unfold_sfmupd. iIntros ">Hupd %%%%% SI".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose !>". iMod "Hclose" as "_". iModIntro. iFrame.
  Qed.

  Lemma sfmupd_intro E P : P ⊢ |={E}=>m P.
  Proof.
    unfold_sfmupd. iIntros "$ %%%%% $". iMod (fupd_mask_subseteq ∅) as "Hclose". 1: set_solver.
    iIntros "!> !>". iMod "Hclose". done.
  Qed.

  Lemma fupd_sfmupd_elim E P : (|={E}=> |={E}=>m P) ⊢ |={E}=>m P.
  Proof.
    iIntros "H". unfold_sfmupd. iIntros (?????) "SI". iMod "H". iApply "H". done.
  Qed.

  (** Change to a larger mask. *)
  Lemma sfmupd_mask_mono E1 E2 P :
    E1 ⊆ E2 →
    (|={E1}=>m P) ⊢ |={E2}=>m P.
  Proof.
    unfold_sfmupd. iIntros (Sub) "H %%%%% SI".
    iMod (fupd_mask_subseteq E1) as "close". 1: done.
    iMod ("H" with "SI") as "H". iModIntro. iMod "H" as ">H".
    iMod "close" as "_".
    iMod (fupd_mask_subseteq ∅) as "close". 1: set_solver.
    iIntros "!> !>". iMod "close" as "_". by iApply "H".
  Qed.

  (** We can combine two obligation updates into one. *)
  Lemma sfmupd_bind E P Q :
    (P -∗ |={E}=>m Q) ⊢ (|={E}=>m P) -∗ (|={E}=>m Q).
  Proof.
    iIntros "H HP". unfold_sfmupd. iIntros "%%%%% SI".
    iMod ("HP" with "SI") as "[SI HP]".
    iPoseProof ("H" with "HP SI") as "H". done.
  Qed.

  (* derived lemmas *)
  Lemma sfmupd_mono E P Q : (P ⊢ Q) → (|={E}=>m P) ⊢ (|={E}=>m Q).
  Proof.
    intros Hent. iApply sfmupd_bind.
    iIntros "P"; iApply sfmupd_intro; by iApply Hent.
  Qed.
  Lemma sfmupd_trans E P :  (|={E}=>m |={E}=>m P) ⊢ |={E}=>m P.
  Proof.
    iIntros "HP". iApply sfmupd_bind; eauto.
  Qed.
  Lemma sfmupd_frame_r E P R : (|={E}=>m P) ∗ R ⊢ |={E}=>m P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (sfmupd_bind with "[R]"); last done.
    iIntros "P". iApply sfmupd_intro. by iFrame.
  Qed.

  Global Instance sfmupd_ent_proper E : Proper ((⊢) ==> (⊢)) (sfmupd E).
  Proof. intros P Q PQ. by apply sfmupd_mono. Qed.
  Global Instance sfmupd_flip_ent_proper E : Proper (flip (⊢) ==> flip (⊢)) (sfmupd E).
  Proof. intros P Q PQ; by apply sfmupd_mono. Qed.
  Global Instance sfmupd_equiv_proper E : Proper ((≡) ==> (≡)) (sfmupd E) := ne_proper _.

  Lemma sfmupd_fupd_l E P :
    (|={E}=> |={E}=>m P) ⊢ (|={E}=>m P).
  Proof.
    by erewrite fupd_sfmupd, sfmupd_trans.
  Qed.
  Lemma sfmupd_fupd_r E P :
    (|={E}=>m |={E}=> P) ⊢ (|={E}=>m P).
  Proof.
    by erewrite fupd_sfmupd, sfmupd_trans.
  Qed.

  Lemma sfmupd_frame_l E R Q : (R ∗ |={E}=>m Q) ⊢ |={E}=>m R ∗ Q.
  Proof. rewrite !(comm _ R); apply sfmupd_frame_r. Qed.
  Lemma sfmupd_wand_l E P Q : (P -∗ Q) ∗ (|={E}=>m P) ⊢ |={E}=>m Q.
  Proof. by rewrite sfmupd_frame_l wand_elim_l. Qed.
  Lemma sfmupd_wand_r E P Q : (|={E}=>m P) ∗ (P -∗ Q) ⊢ |={E}=>m Q.
  Proof. by rewrite sfmupd_frame_r wand_elim_r. Qed.
  Lemma sfmupd_sep E P Q : (|={E}=>m P) ∗ (|={E}=>m Q) ⊢ |={E}=>m P ∗ Q.
  Proof. by rewrite sfmupd_frame_r sfmupd_frame_l sfmupd_trans. Qed.
  Lemma sfmupd_idemp E P : (|={E}=>m |={E}=>m P) ⊣⊢ |={E}=>m P.
  Proof.
    apply: anti_symm.
    - apply sfmupd_trans.
    - apply sfmupd_intro.
  Qed.

  Global Instance sfmupd_homomorphism E :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (sfmupd E).
  Proof. split; [split|]; try apply _; [apply sfmupd_sep | apply sfmupd_intro]. Qed.

  Lemma big_sepL_sfmupd {A} (Φ : nat → A → iProp Σ) E l :
    ([∗ list] k↦x ∈ l, |={E}=>m Φ k x) ⊢ |={E}=>m [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_sfmupd {A} `{Countable K} (Φ : K → A → iProp Σ) E l :
    ([∗ map] k↦x ∈ l, |={E}=>m Φ k x) ⊢ |={E}=>m [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_sfmupd `{Countable A} (Φ : A → iProp Σ) E l :
    ([∗ set]  x ∈ l, |={E}=>m Φ x) ⊢ |={E}=>m [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_sfmupd `{Countable A} (Φ : A → iProp Σ) E l :
    ([∗ mset] x ∈ l, |={E}=>m Φ x) ⊢ |={E}=>m [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_sfmupd E P : ◇ (|={E}=>m P) ⊢ (|={E}=>m ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using sfmupd_mono, or_intro_r.
    by rewrite -sfmupd_intro -or_intro_l.
  Qed.

  Lemma sfmupd_fupd_acc E1 E2 P :
    (|={E1,E2}=> |={E2}=>m |={E2,E1}=> P) ⊢ (|={E1}=>m P).
  Proof.
    unfold_sfmupd. iIntros "H %%%%% I". iMod "H". iPoseProof ("H" with "I") as "H".
    iMod "H". iModIntro. iMod "H". iModIntro. iMod "H" as "[$ H]". auto.
  Qed.

  (** Modality instances *)
  Global Instance elim_bupd_sfmupd (p : bool) E P Q :
    ElimModal True p false (|==> P) P (|={E}=>m Q) (|={E}=>m Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_sfmupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_fupd_sfmupd (p : bool) E P Q :
    ElimModal True p false (|={E}=> P) P (|={E}=>m Q) (|={E}=>m Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_sfmupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_sfmupd E P Q :
    AddModal (|={E}=> P) P (|={E}=>m Q).
  Proof.
    rewrite /AddModal; rewrite fupd_sfmupd; iIntros "[HP HPQ]".
    iApply (sfmupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_sfmupd p E P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|={E}=>m Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply sfmupd_intro. Qed.

  Global Instance from_pure_sfmupd a E P φ :
    FromPure a P φ → FromPure a (|={E}=>m P) φ.
  Proof. rewrite /FromPure=> <-. apply sfmupd_intro. Qed.

  Global Instance into_wand_sfmupd p q E R P Q :
    IntoWand false false R P Q → IntoWand p q (|={E}=>m R) (|={E}=>m P) (|={E}=>m Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite sfmupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_sfmupd_persistent p q E R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E}=>m R) P (|={E}=>m Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite sfmupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_sfmupd_args p q E R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E}=>m P) (|={E}=>m Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim sfmupd_wand_r.
  Qed.

  Global Instance from_sep_sfmupd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E}=>m P) (|={E}=>m Q1) (|={E}=>m Q2).
  Proof. rewrite /FromSep=><-. apply sfmupd_sep. Qed.

  Global Instance from_or_sfmupd E P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E}=>m P) (|={E}=>m Q1) (|={E}=>m Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply sfmupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_sfmupd {A} E P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E}=>m P) (λ a, |={E}=>m Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_sfmupd E P : IsExcept0 P → IsExcept0 (|={E}=>m P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_sfmupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_sfmupd E P :
    FromModal True modality_id (|={E}=>m P) (|={E}=>m P) P.
  Proof. by rewrite /FromModal /= -sfmupd_intro. Qed.

  Global Instance elim_modal_sfmupd p E P Q :
    ElimModal True p false (|={E}=>m P) P (|={E}=>m Q) (|={E}=>m Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim sfmupd_frame_r wand_elim_r sfmupd_trans.
  Qed.

  Global Instance add_modal_sfmupd E P Q : AddModal (|={E}=>m P) P (|={E}=>m Q).
  Proof. by rewrite /AddModal sfmupd_frame_r wand_elim_r sfmupd_trans. Qed.

  Global Instance frame_sfmupd p E R P Q :
    Frame p R P Q → Frame p R (|={E}=>m P) (|={E}=>m Q).
  Proof. rewrite /Frame=><-. by rewrite sfmupd_frame_l. Qed.

  Lemma all_interp_sfmupd_steps γ E h n σ Θ κs g v Ω W (P : iProp Σ) :
    owit_inv_lb_mon γ →
    owit_inv_lb γ Ω W →
    (|={E}=>m P) -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={E}=∗
    (P ∗ history_interp h n σ Θ κs ∗
     ∃ g' v' Ω' W', ⌜ obls_le Ω Ω' ∧ owit_inv_lb γ Ω' W' ⌝ ∗ model_interp (g ++ g') (v + v') Ω' W' n (dom Θ)).
  Proof.
    iIntros (MON LB) "HP HI MI". unfold_sfmupd. iPoseProof ("HP" with "HI") as ">HP".
    iMod (model_interp_mupd_steps γ with "HP MI") as "(>($& $)& $)"; done.
  Qed.

  (** lc rules *)
  Lemma lc_sfmupd_add_later E P :
    £n 1 -∗ ▷ (|={E}=>m P) -∗ |={E}=>m P.
  Proof.
    iIntros "LC H". iApply fupd_sfmupd_elim. by iApply (lc_fupd_elim_later with "LC").
  Qed.

  Lemma lc_sfmupd_add_laterN E P n :
    £n n -∗ ▷^n (|={E}=>m P) -∗ |={E}=>m P.
  Proof.
    iIntros "LC H". iApply fupd_sfmupd_elim. iApply (lc_fupd_add_laterN with "LC"). iNext. auto.
  Qed.

  (** ** Update rules *)
  Lemma thread_terminate E i :
    thP_groups i ∅ -∗ |={E}=>m thP_done i.
  Proof.
    unfold_sfmupd. iIntros "Tb %%%%% $". iMod (thread_terminate_mupd with "Tb") as "#Tt". auto.
  Qed.

  Lemma group_alloc E i G ℓ μ :
    thP_groups i G -∗
    |={E}=>m ∃ g, (⌜ g ∉ G ⌝) ∗
                 thP_groups i ({[g]} ∪ G) ∗ grP_obls i g ℓ ∅ ∗ grP_fuel g ℓ μ.
  Proof.
    unfold_sfmupd. iIntros "Tb %%%%% $".
    iMod (group_alloc_mupd with "Tb") as "(%& %& $& $& $)". auto.
  Qed.

  Lemma group_delete E i G g ℓ :
    thP_groups i G -∗
    grP_obls i g ℓ ∅ -∗
    |={E}=>m thP_groups i (G ∖ {[g]}).
  Proof.
    unfold_sfmupd. iIntros "Tb Gg %%%%% $".
    iMod (group_delete_mupd with "Tb Gg") as "$". auto.
  Qed.

  Lemma obl_alloc_assigned E i g K b ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    grP_obls i g ℓ1 K -∗
    |={E}=>m ∃ k, (⌜ k ∉ K ⌝) ∗
                 grP_obls i g ℓ1 ({[k]} ∪ K) ∗
                 oblP_assigned k b (1/2)%Qp ∗
                 oblP_fuel k ℓ2 μ ∗
                 witP_layer k ℓ2 ∗
                 (∀ E N (P Q R : iProp Σ), (▷ (if b then Q else P)) ={E}=∗ oblP_inv N k P Q R).
  Proof.
    unfold_sfmupd. iIntros (Ltl) "Tb %%%%% $".
    iMod (obl_alloc_assigned_mupd with "Tb") as "(%& %& $& $& $& $& $)"; auto.
  Qed.

  Lemma obl_alloc_discharged E ℓ μ :
    ⊢ |={E}=>m ∃ k, oblP_discharged k ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                   (∀ E N (P Q R : iProp Σ), (▷ R) ={E}=∗ oblP_inv N k P Q R).
  Proof.
    unfold_sfmupd. iIntros "%%%%% $".
    iMod (obl_alloc_discharged_mupd) as "(%& $& $& $& $)"; auto.
  Qed.

  Lemma obl_assigned_to_true E N k P Q R :
    ↑N ⊆ E →
    oblP_inv N k P Q R -∗
    |={E,E ∖ ↑N}=> oblP_assigned k false (1/2)%Qp -∗
                  ((▷ (oblP_assigned k false 1 ∗ P)) ∗
                   (∀ b, oblP_assigned k b 1 -∗
                         ∀ E', |={E'}=>m (oblP_assigned k true (1/2)%Qp) ∗
                                      ((▷ Q) ={E ∖ ↑N,E}=∗ True))).
  Proof.
    iIntros (MASK) "#Gv". iMod (obl_assigned_to_true_mupd with "Gv") as "H". 1: auto.
    iIntros "!> Ga". iPoseProof ("H" with "Ga") as "[$ ACC]". iIntros "% Ga". iPoseProof ("ACC" with "Ga") as "H".
    unfold_sfmupd. iIntros "% %%%%% $". iMod ("H" $! n (dom Θ)) as "H". iModIntro. done.
  Qed.

  Lemma obl_true_to_discharge E N k P Q R :
    ↑N ⊆ E →
    oblP_inv N k P Q R -∗
    |={E,E ∖ ↑N}=> ∀ i g ℓ K q,
    (⌜k ∈ K⌝) → grP_obls i g ℓ K -∗ oblP_assigned k true q -∗
    ((▷ (grP_obls i g ℓ K ∗ oblP_assigned k true q ∗ oblP_assigned k true (1/2) ∗ Q)) ∗
     (grP_obls i g ℓ K -∗
      oblP_assigned k true 1 -∗
      ∀ E', |={E'}=>m (grP_obls i g ℓ (K ∖ {[k]}) ∗ oblP_discharged k) ∗
                     ((▷ (R)) ={E ∖ ↑N,E}=∗ True))).
  Proof.
    iIntros (MASK) "#Gv". iMod (obl_discharge_mupd with "Gv") as "H". 1: auto.
    iIntros "!> %%%%% % TG Ga". iPoseProof ("H" with "[//] TG Ga") as "[$ ACC]". iIntros "TG Ga".
    iPoseProof ("ACC" with "TG Ga") as "H".
    unfold_sfmupd. iIntros "% %%%%% $". iMod ("H" $! n (dom Θ)) as "H". iModIntro. done.
  Qed.

  Lemma obl_offload E i1 i2 g1 g2 K1 K2 ℓ1 ℓ2 ℓ k :
    k ∈ K1 →
    (ℓ2 <= ℓ)%ordi →
    grP_obls i1 g1 ℓ1 K1 -∗
    grP_obls i2 g2 ℓ2 K2 -∗
    oblP_fuel k ℓ 1 -∗
    |={E}=>m grP_obls i1 g1 ℓ1 (K1 ∖ {[k]}) ∗ grP_obls i2 g2 ℓ2 (K2 ∪ {[k]}) ∗ ⌜ k ∉ K2 ⌝.
  Proof.
    iIntros (Ink Ltl) "Gg1 Gg2 Of".
    unfold_sfmupd. iIntros "%%%%% $".
    iMod (obl_offload_mupd with "Gg1 Gg2 Of") as "($& $& $)"; auto.
  Qed.

  Lemma obl_offload_set E i1 i2 g1 g2 K1 K2 K ℓ1 ℓ2 ℓ :
    K ⊆ K1 →
    (ℓ2 <= ℓ)%ordi →
    grP_obls i1 g1 ℓ1 K1 -∗
    grP_obls i2 g2 ℓ2 K2 -∗
    ([∗ set] k ∈ K, oblP_fuel k ℓ 1) -∗
    |={E}=>m grP_obls i1 g1 ℓ1 (K1 ∖ K) ∗ grP_obls i2 g2 ℓ2 (K2 ∪ K) ∗ ⌜ K2 ## K ⌝.
  Proof.
    iIntros (Ink Ltl) "Gg1 Gg2 Of".
    unfold_sfmupd. iIntros "%%%%% $".
    iMod (obl_offload_set_mupd with "Gg1 Gg2 Of") as "($& $& $)"; auto.
  Qed.

  Lemma obl_check_witnesses E (R : oids) :
    ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) -∗
    |={E}=>m ([∗ set] r ∈ R, (witP_cred r Ord.O) ∨ oblP_discharged r).
  Proof.
    unfold_sfmupd. iIntros "Rs %%%%% $". iMod (obl_check_witnesses_mupd with "Rs") as "H". auto.
  Qed.

End sfmupd.
