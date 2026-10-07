From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From lantana.base_logic Require Export opreds.
From lantana.program_logic Require Export history_interp.
Import uPred.

Local Definition sfgupd_def `{SI : sidx} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}
  `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))}
  E1 E2 : iPropO Σ -d> iPropO Σ :=
  (λ P, ∀ h n σ Θ κs, (history_interp h n σ Θ κs) -∗ |={E1,E2:n,dom Θ}=>g (history_interp h n σ Θ κs) ∗ P)%I.
Local Definition sfgupd_aux : seal (@sfgupd_def). Proof. by eexists. Qed.
Definition sfgupd := sfgupd_aux.(unseal).
Global Arguments sfgupd {SI Λ Σ _ _ _ _}.
Local Lemma sfgupd_unseal `{SI : sidx} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}
  `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))} :
  sfgupd = @sfgupd_def SI Λ Σ _ _ _ _.
Proof. rewrite -sfgupd_aux.(seal_eq) //. Qed.

Ltac unfold_sfgupd := rewrite sfgupd_unseal /sfgupd_def.

Notation "'|={' E1 , E2 '}=>g' P" := (sfgupd E1 E2 P) (at level 20, P at level 200, format "|={ E1 , E2 }=>g  P").
Notation "'|={' E '}=>g' P" := (sfgupd E E P) (at level 20, P at level 200, format "|={ E }=>g  P").

Section sfgupd.
  Context `{SI : sidx} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))}.

  Global Instance sfgupd_ne E1 E2 : NonExpansive (sfgupd E1 E2).
  Proof. intros n P1 P2 HP. rewrite sfgupd_unseal /sfgupd_def. do 14 (f_equiv || done). Qed.
  Global Instance sfgupd_proper E1 E2 : Proper ((≡) ==> (≡)) (sfgupd E1 E2).
  Proof. intros P P' ?. apply equiv_dist=>n. apply sfgupd_ne. apply equiv_dist. done. Qed.

  Lemma fupd_sfgupd E1 E2 P : (|={E1,E2}=> P) ⊢ (|={E1,E2}=>g P).
  Proof.
    unfold_sfgupd. iIntros ">Hupd %%%%% SI".
    iModIntro. iFrame.
  Qed.

  Lemma sfgupd_intro E P : P ⊢ |={E}=>g P.
  Proof.
    unfold_sfgupd. iIntros "$ %%%%% $". iMod (fupd_mask_subseteq ∅) as "Hclose". 1: set_solver.
    iIntros "!> !>". iMod "Hclose". done.
  Qed.

  Lemma fupd_sfgupd_elim E1 E2 P : (|={E1}=> |={E1,E2}=>g P) ⊢ |={E1,E2}=>g P.
  Proof.
    iIntros "H". unfold_sfgupd. iIntros (?????) "SI". iMod "H". iApply "H". done.
  Qed.
  Lemma fupd_sfgupd_elim_2 E1 E2 P : (|={E1,E2}=>g |={E2}=> P) ⊢ |={E1,E2}=>g P.
  Proof.
    iIntros "H". unfold_sfgupd. iIntros (?????) "SI". by iMod ("H" with "SI") as "[$ >$]".
  Qed.

  (** Change to a larger mask. *)
  Lemma sfgupd_mask_mono E1 E2 P :
    E1 ⊆ E2 →
    (|={E1}=>g P) ⊢ |={E2}=>g P.
  Proof.
    unfold_sfgupd. iIntros (Sub) "H %%%%% SI".
    iMod (fupd_mask_subseteq E1) as "close". 1: done.
    iMod ("H" with "SI") as "H". by iMod "close".
  Qed.

  (** We can combine two obligation updates into one. *)
  Lemma sfgupd_bind E1 E2 E3 P Q :
    (P -∗ |={E2,E3}=>g Q) ⊢ (|={E1,E2}=>g P) -∗ (|={E1,E3}=>g Q).
  Proof.
    iIntros "H HP". unfold_sfgupd. iIntros "%%%%% SI".
    iMod ("HP" with "SI") as "[SI HP]".
    iPoseProof ("H" with "HP SI") as "H". done.
  Qed.

  (* derived lemmas *)
  Lemma sfgupd_mono E1 E2 P Q : (P ⊢ Q) → (|={E1,E2}=>g P) ⊢ (|={E1,E2}=>g Q).
  Proof.
    intros Hent. iApply sfgupd_bind.
    iIntros "P"; iApply sfgupd_intro; by iApply Hent.
  Qed.
  Lemma sfgupd_trans E1 E2 E3 P :  (|={E1,E3}=>g |={E3,E2}=>g P) ⊢ |={E1,E2}=>g P.
  Proof.
    iIntros "HP". iApply sfgupd_bind; eauto.
  Qed.
  Lemma sfgupd_frame_r E1 E2 P R : (|={E1,E2}=>g P) ∗ R ⊢ |={E1,E2}=>g P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (sfgupd_bind with "[R]"); last done.
    iIntros "P". iApply sfgupd_intro. by iFrame.
  Qed.

  Global Instance sfgupd_ent_proper E1 E2 : Proper ((⊢) ==> (⊢)) (sfgupd E1 E2).
  Proof. intros P Q PQ. by apply sfgupd_mono. Qed.
  Global Instance sfgupd_flip_ent_proper E1 E2 : Proper (flip (⊢) ==> flip (⊢)) (sfgupd E1 E2).
  Proof. intros P Q PQ; by apply sfgupd_mono. Qed.
  Global Instance sfgupd_equiv_proper E1 E2 : Proper ((≡) ==> (≡)) (sfgupd E1 E2) := ne_proper _.

  Lemma sfgupd_fupd_l E1 E2 P :
    (|={E1,E2}=> |={E2}=>g P) ⊢ (|={E1,E2}=>g P).
  Proof.
    by erewrite fupd_sfgupd, sfgupd_trans.
  Qed.
  Lemma sfgupd_fupd_r E1 E2 P :
    (|={E1}=>g |={E1,E2}=> P) ⊢ (|={E1,E2}=>g P).
  Proof.
    by erewrite fupd_sfgupd, sfgupd_trans.
  Qed.

  Lemma sfgupd_frame_l E1 E2 R Q : (R ∗ |={E1,E2}=>g Q) ⊢ |={E1,E2}=>g R ∗ Q.
  Proof. rewrite !(comm _ R); apply sfgupd_frame_r. Qed.
  Lemma sfgupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|={E1,E2}=>g P) ⊢ |={E1,E2}=>g Q.
  Proof. by rewrite sfgupd_frame_l wand_elim_l. Qed.
  Lemma sfgupd_wand_r E1 E2 P Q : (|={E1,E2}=>g P) ∗ (P -∗ Q) ⊢ |={E1,E2}=>g Q.
  Proof. by rewrite sfgupd_frame_r wand_elim_r. Qed.
  Lemma sfgupd_sep E P Q : (|={E}=>g P) ∗ (|={E}=>g Q) ⊢ |={E}=>g P ∗ Q.
  Proof. by rewrite sfgupd_frame_r sfgupd_frame_l sfgupd_trans. Qed.
  Lemma sfgupd_idemp E P : (|={E}=>g |={E}=>g P) ⊣⊢ |={E}=>g P.
  Proof.
    apply: anti_symm.
    - apply sfgupd_trans.
    - apply sfgupd_intro.
  Qed.

  Global Instance sfgupd_homomorphism E :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (sfgupd E E).
  Proof. split; [split|]; try apply _; [apply sfgupd_sep | apply sfgupd_intro]. Qed.

  Lemma big_sepL_sfgupd {A} (Φ : nat → A → iProp Σ) E l :
    ([∗ list] k↦x ∈ l, |={E}=>g Φ k x) ⊢ |={E}=>g [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_sfgupd {A} `{Countable K} (Φ : K → A → iProp Σ) E l :
    ([∗ map] k↦x ∈ l, |={E}=>g Φ k x) ⊢ |={E}=>g [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_sfgupd `{Countable A} (Φ : A → iProp Σ) E l :
    ([∗ set]  x ∈ l, |={E}=>g Φ x) ⊢ |={E}=>g [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_sfgupd `{Countable A} (Φ : A → iProp Σ) E l :
    ([∗ mset] x ∈ l, |={E}=>g Φ x) ⊢ |={E}=>g [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_sfgupd E1 E2 P : ◇ (|={E1,E2}=>g P) ⊢ (|={E1,E2}=>g ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using sfgupd_mono, or_intro_r.
    rewrite -fupd_sfgupd. iIntros "H". iApply except_0_fupd. iMod "H". done.
  Qed.

  Lemma sfgupd_fupd_acc_gen E1 E2 E3 E4 P :
    (|={E1,E2}=> |={E2,E3}=>g |={E3,E4}=> P) ⊢ (|={E1,E4}=>g P).
  Proof.
    unfold_sfgupd. iIntros "H %%%%% I". iMod "H". iPoseProof ("H" with "I") as "H".
    iMod "H". iDestruct "H" as "[$ H]". iApply fupd_fgupd. auto.
  Qed.

  Lemma sfgupd_fupd_acc E1 E2 P :
    (|={E1,E2}=> |={E2}=>g |={E2,E1}=> P) ⊢ (|={E1}=>g P).
  Proof. apply sfgupd_fupd_acc_gen. Qed.

  (** Modality instances *)
  Global Instance elim_bupd_sfgupd (p : bool) E1 E2 P Q :
    ElimModal True p false (|==> P) P (|={E1,E2}=>g Q) (|={E1,E2}=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_sfgupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_fupd_sfgupd (p : bool) E1 E2 E3 P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3}=>g Q) (|={E2,E3}=>g Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply sfgupd_trans.
    iApply fupd_sfgupd. iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_sfgupd E1 E2 P Q :
    AddModal (|={E1}=> P) P (|={E1,E2}=>g Q).
  Proof.
    rewrite /AddModal; rewrite fupd_sfgupd; iIntros "[HP HPQ]".
    iApply (sfgupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_sfgupd p E P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|={E}=>g Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply sfgupd_intro. Qed.

  Global Instance from_pure_sfgupd a E P φ :
    FromPure a P φ → FromPure a (|={E}=>g P) φ.
  Proof. rewrite /FromPure=> <-. apply sfgupd_intro. Qed.

  Global Instance into_wand_sfgupd p q E R P Q :
    IntoWand false false R P Q → IntoWand p q (|={E}=>g R) (|={E}=>g P) (|={E}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite sfgupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_sfgupd_persistent p q E1 E2 R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E1,E2}=>g R) P (|={E1,E2}=>g Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite sfgupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_sfgupd_args p q E1 E2 R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E1,E2}=>g P) (|={E1,E2}=>g Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim sfgupd_wand_r.
  Qed.

  Global Instance from_sep_sfgupd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E}=>g P) (|={E}=>g Q1) (|={E}=>g Q2).
  Proof. rewrite /FromSep=><-. apply sfgupd_sep. Qed.

  Global Instance from_or_sfgupd E1 E2 P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E1,E2}=>g P) (|={E1,E2}=>g Q1) (|={E1,E2}=>g Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply sfgupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_sfgupd {A} E1 E2 P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E1,E2}=>g P) (λ a, |={E1,E2}=>g Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_sfgupd E1 E2 P : IsExcept0 P → IsExcept0 (|={E1,E2}=>g P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_sfgupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_sfgupd E P :
    FromModal True modality_id (|={E}=>g P) (|={E}=>g P) P.
  Proof. by rewrite /FromModal /= -sfgupd_intro. Qed.

  Global Instance elim_modal_sfgupd p E1 E2 E3 P Q :
    ElimModal True p false (|={E1,E2}=>g P) P (|={E1,E3}=>g Q) (|={E2,E3}=>g Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim sfgupd_frame_r wand_elim_r sfgupd_trans.
  Qed.

  Global Instance add_modal_sfgupd E1 E2 P Q : AddModal (|={E1}=>g P) P (|={E1,E2}=>g Q).
  Proof. by rewrite /AddModal sfgupd_frame_r wand_elim_r sfgupd_trans. Qed.

  Global Instance frame_sfgupd p E1 E2 R P Q :
    Frame p R P Q → Frame p R (|={E1,E2}=>g P) (|={E1,E2}=>g Q).
  Proof. rewrite /Frame=><-. by rewrite sfgupd_frame_l. Qed.

  Lemma all_interp_sfgupd_steps γ E1 E2 h n σ Θ κs g v Ω W (P : iProp Σ) :
    owit_inv_lb_mon γ →
    owit_inv_lb γ Ω W →
    (|={E1,E2}=>g P) -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={E1,E2}=∗
    (P ∗ history_interp h n σ Θ κs ∗
     ∃ g' v' Ω' W', ⌜ obls_nd Ω Ω' ∧ owit_inv_lb γ Ω' W' ⌝ ∗ model_interp (g ++ g') (v + v') Ω' W' n (dom Θ)).
  Proof.
    iIntros (MON LB) "HP HI MI". unfold_sfgupd. iPoseProof ("HP" with "HI") as ">HP".
    iMod (model_interp_gupd_steps γ with "HP MI") as "(>($& $)& $)"; done.
  Qed.

  (** lc rules *)
  Lemma lc_sfgupd_add_later E1 E2 P :
    £n 1 -∗ ▷ (|={E1,E2}=>g P) -∗ |={E1,E2}=>g P.
  Proof.
    iIntros "LC H". iApply fupd_sfgupd_elim. by iApply (lantana.base_logic.fancy_updates.lc_fupd_elim_later with "LC").
  Qed.

  Lemma lc_sfgupd_add_laterN E1 E2 P n :
    £n n -∗ ▷^n (|={E1,E2}=>g P) -∗ |={E1,E2}=>g P.
  Proof.
    iIntros "LC H". iApply fupd_sfgupd_elim. iApply (lantana.base_logic.fancy_updates.lc_fupd_add_laterN with "LC"). iNext. auto.
  Qed.

  (** ** Update rules *)
  Lemma thread_terminate E i :
    thP_carriers i ∅ -∗ |={E}=>g thP_done i.
  Proof.
    unfold_sfgupd. iIntros "Tb %%%%% $". iMod (thread_terminate_gupd with "Tb") as "#Tt". auto.
  Qed.

  Lemma carrier_alloc E i G ℓ μ :
    thP_carriers i G -∗
    |={E}=>g ∃ g, (⌜ g ∉ G ⌝) ∗
                 thP_carriers i ({[g]} ∪ G) ∗ crP_obls g ℓ ∅ ∗ crP_fuel g ℓ μ.
  Proof.
    unfold_sfgupd. iIntros "Tb %%%%% $".
    iMod (carrier_alloc_gupd with "Tb") as "(%& %& $& $& $)". auto.
  Qed.

  Lemma carrier_delete E i G g ℓ :
    g ∈ G →
    thP_carriers i G -∗
    crP_obls g ℓ ∅ -∗
    |={E}=>g thP_carriers i (G ∖ {[g]}).
  Proof.
    unfold_sfgupd. iIntros (Ing) "Tb Gg %%%%% $".
    iMod (carrier_delete_gupd with "Tb Gg") as "$"; auto.
  Qed.

  Lemma obl_alloc_assigned E g K b ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    crP_obls g ℓ1 K -∗
    |={E}=>g ∃ k, (⌜ k ∉ K ⌝) ∗
                 crP_obls g ℓ1 ({[k]} ∪ K) ∗
                 oblP_assigned k b (1/2)%Qp ∗
                 oblP_fuel k ℓ2 μ ∗
                 witP_layer k ℓ2 ∗
                 (∀ E N (P Q R : iProp Σ), (▷ (if b then Q else P)) ={E}=∗ oblP_inv N k P Q R).
  Proof.
    unfold_sfgupd. iIntros (Ltl) "Tb %%%%% $".
    iMod (obl_alloc_assigned_gupd with "Tb") as "(%& %& $& $& $& $& $)"; auto.
  Qed.

  Lemma obl_alloc_discharged E ℓ μ :
    ⊢ |={E}=>g ∃ k, oblP_discharged k ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                   (∀ E N (P Q R : iProp Σ), (▷ R) ={E}=∗ oblP_inv N k P Q R).
  Proof.
    unfold_sfgupd. iIntros "%%%%% $".
    iMod (obl_alloc_discharged_gupd) as "(%& $& $& $& $)"; auto.
  Qed.

  Lemma obl_assigned_to_true E N k P Q R :
    ↑N ⊆ E →
    oblP_inv N k P Q R -∗
    |={E,E ∖ ↑N}=> oblP_assigned k false (1/2)%Qp -∗
                  ((▷ (oblP_assigned k false 1 ∗ P)) ∗
                   (∀ b, oblP_assigned k b 1 -∗
                         ∀ E', |={E'}=>g (oblP_assigned k true (1/2)%Qp) ∗
                                      ((▷ Q) ={E ∖ ↑N,E}=∗ True))).
  Proof.
    iIntros (MASK) "#Gv". iMod (obl_assigned_to_true_gupd with "Gv") as "H". 1: auto.
    iIntros "!> Ga". iPoseProof ("H" with "Ga") as "[$ ACC]". iIntros "% Ga". iPoseProof ("ACC" with "Ga") as "H".
    unfold_sfgupd. iIntros "% %%%%% $". iMod ("H" $! n (dom Θ)) as "H". iModIntro. done.
  Qed.

  Lemma obl_offload E g1 g2 K1 K2 ℓ1 ℓ2 ℓ k :
    k ∈ K1 →
    (ℓ2 <= ℓ)%ordi →
    crP_obls g1 ℓ1 K1 -∗
    crP_obls g2 ℓ2 K2 -∗
    oblP_fuel k ℓ 1 -∗
    |={E}=>g crP_obls g1 ℓ1 (K1 ∖ {[k]}) ∗ crP_obls g2 ℓ2 (K2 ∪ {[k]}) ∗ ⌜ k ∉ K2 ⌝.
  Proof.
    iIntros (Ink Ltl) "Gg1 Gg2 Of".
    unfold_sfgupd. iIntros "%%%%% $".
    iMod (obl_offload_gupd with "Gg1 Gg2 Of") as "($& $& $)"; auto.
  Qed.

  Lemma obl_offload_set E g1 g2 K1 K2 K ℓ1 ℓ2 ℓ :
    K ⊆ K1 →
    (ℓ2 <= ℓ)%ordi →
    crP_obls g1 ℓ1 K1 -∗
    crP_obls g2 ℓ2 K2 -∗
    ([∗ set] k ∈ K, oblP_fuel k ℓ 1) -∗
    |={E}=>g crP_obls g1 ℓ1 (K1 ∖ K) ∗ crP_obls g2 ℓ2 (K2 ∪ K) ∗ ⌜ K2 ## K ⌝.
  Proof.
    iIntros (Ink Ltl) "Gg1 Gg2 Of".
    unfold_sfgupd. iIntros "%%%%% $".
    iMod (obl_offload_set_gupd with "Gg1 Gg2 Of") as "($& $& $)"; auto.
  Qed.

  (** ** Derived carrier-management rules.

      The three rules above are what the logic offers; the proofs of the case
      studies compose them in a few recurring shapes, each followed by set
      arithmetic on carrier sets. We package the shapes once, with the set
      equalities as premises, so a use site discharges them by [set_solver]
      instead of [replace]. *)

  (** Delete a carrier whose obligation set is empty (up to [set_solver]). *)
  Lemma carrier_delete_eq E i G G' g ℓ K :
    g ∈ G → K = ∅ → G' = G ∖ {[g]} →
    thP_carriers i G -∗ crP_obls g ℓ K -∗ |={E}=>g thP_carriers i G'.
  Proof. intros ? -> ->. by apply carrier_delete. Qed.

  (** Same, also dropping the carrier from a [crP_fuels] collection. *)
  Lemma carrier_delete_fuels E i G G' g ℓ K n :
    g ∈ G → K = ∅ → G' = G ∖ {[g]} →
    thP_carriers i G -∗ crP_obls g ℓ K -∗ crP_fuels G n -∗
    |={E}=>g thP_carriers i G' ∗ crP_fuels G' n.
  Proof.
    iIntros (? -> ->) "TG Gg GF".
    iMod (carrier_delete_eq with "TG Gg") as "$"; [done..|].
    iApply sfgupd_intro. by iApply crP_fuels_remove_carrier.
  Qed.

  Lemma crP_fuels_remove_carrier_eq g G G' n :
    G' = G ∖ {[g]} → crP_fuels G n -∗ crP_fuels G' n.
  Proof. intros ->. apply crP_fuels_remove_carrier. Qed.

  (** Refresh: retire an empty carrier and start a fresh one with a budget of
      the proof's choice. The cutpoint where a perpetual worker's fuel resets. *)
  Lemma carrier_renew E i G G' g ℓ K ℓ' μ :
    g ∈ G → K = ∅ → G' = G ∖ {[g]} →
    thP_carriers i G -∗ crP_obls g ℓ K -∗
    |={E}=>g ∃ g', ⌜g' ∉ G'⌝ ∗ thP_carriers i ({[g']} ∪ G') ∗ crP_obls g' ℓ' ∅ ∗ crP_fuel g' ℓ' μ.
  Proof.
    iIntros (? -> ->) "TG Gg".
    iApply (sfgupd_bind with "[] [TG Gg]"); last by iApply (carrier_delete_eq with "TG Gg").
    iIntros "TG". by iApply carrier_alloc.
  Qed.

  (** Allocate a fresh carrier and move the obligations [K] off [g1] onto it,
      spending one unit of transfer credit per obligation. *)
  Lemma carrier_alloc_offload E i G g1 ℓ1 K1 K ℓ ℓo μ :
    K ⊆ K1 → (ℓ <= ℓo)%ordi →
    thP_carriers i G -∗ crP_obls g1 ℓ1 K1 -∗ ([∗ set] k ∈ K, oblP_fuel k ℓo 1) -∗
    |={E}=>g ∃ g, ⌜g ∉ G⌝ ∗ thP_carriers i ({[g]} ∪ G) ∗
                 crP_obls g1 ℓ1 (K1 ∖ K) ∗ crP_obls g ℓ K ∗ crP_fuel g ℓ μ.
  Proof.
    iIntros (??) "TG Gg1 Of".
    iApply (sfgupd_bind with "[Gg1 Of] [TG]"); last by iApply (carrier_alloc with "TG").
    iIntros "(%g& %& TG& Gg& Fg)".
    iApply (sfgupd_bind with "[TG Fg] [Gg1 Gg Of]"); last by iApply (obl_offload_set with "Gg1 Gg Of").
    iIntros "(Gg1& Gg& _)". iApply sfgupd_intro. rewrite left_id_L. by iFrame.
  Qed.

  Lemma obl_check_witnesses E (R : oids) :
    ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) -∗
    |={E}=>g ([∗ set] r ∈ R, (witP_cred r Ord.O) ∨ oblP_discharged r).
  Proof.
    unfold_sfgupd. iIntros "Rs %%%%% $". iMod (obl_check_witnesses_gupd with "Rs") as "H". auto.
  Qed.

End sfgupd.
