(** * Derived rules of the obligation-forest interface

    The usual rules of the model update [|={E1,E2}=>m P] and its proof-mode instances, from
    the three core rules of the class; the rules of obligation invariants, witnesses, parents,
    fuel and credits; model updates and physical steps in their usual shapes. *)

From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.program_logic Require Export obl_forest.
Import uPred.

(** * The model update *)
Section modality.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!obl_forest_interface}.
  Context `{!TemporalInterp Λ Σ}.
  Implicit Types P Q R : iProp Σ.

  Lemma sfmupd_intro E P : P ⊢ |={E}=>m P.
  Proof. rewrite -fupd_sfmupd. apply fupd_intro. Qed.

  Lemma sfmupd_mono E1 E2 P Q : (P ⊢ Q) → (|={E1,E2}=>m P) ⊢ (|={E1,E2}=>m Q).
  Proof.
    iIntros (Hent) "H". iApply (sfmupd_bind with "[] H"). iIntros "HP".
    iApply sfmupd_intro. by iApply Hent.
  Qed.
  Lemma sfmupd_trans E1 E2 E3 P : (|={E1,E3}=>m |={E3,E2}=>m P) ⊢ |={E1,E2}=>m P.
  Proof. iIntros "H". iApply (sfmupd_bind with "[] H"). by iIntros "H". Qed.
  Lemma sfmupd_frame_r E1 E2 P R : (|={E1,E2}=>m P) ∗ R ⊢ |={E1,E2}=>m P ∗ R.
  Proof.
    iIntros "[H R]". iApply (sfmupd_bind with "[R] H"). iIntros "HP".
    iApply sfmupd_intro. iFrame.
  Qed.

  Lemma fupd_sfmupd_elim E1 E2 P : (|={E1}=> |={E1,E2}=>m P) ⊢ |={E1,E2}=>m P.
  Proof. by rewrite fupd_sfmupd sfmupd_trans. Qed.
  Lemma fupd_sfmupd_elim_2 E1 E2 P : (|={E1,E2}=>m |={E2}=> P) ⊢ |={E1,E2}=>m P.
  Proof.
    iIntros "H". iApply (sfmupd_bind with "[] H"). iIntros "H". by iApply fupd_sfmupd.
  Qed.

  Lemma sfmupd_mask_mono E1 E2 P :
    E1 ⊆ E2 →
    (|={E1}=>m P) ⊢ |={E2}=>m P.
  Proof.
    iIntros (HE) "H".
    iPoseProof (fupd_sfmupd E2 E1 (|={E1,E2}=> emp)%I with "[]") as "C".
    { by iApply fupd_mask_subseteq. }
    iApply (sfmupd_bind with "[H] C"). iIntros "C2".
    iApply (sfmupd_bind with "[C2] H"). iIntros "HP".
    iApply fupd_sfmupd. iMod "C2". by iModIntro.
  Qed.

  Global Instance sfmupd_ent_proper E1 E2 : Proper ((⊢) ==> (⊢)) (sfmupd E1 E2).
  Proof. intros P Q PQ. by apply sfmupd_mono. Qed.
  Global Instance sfmupd_flip_ent_proper E1 E2 : Proper (flip (⊢) ==> flip (⊢)) (sfmupd E1 E2).
  Proof. intros P Q PQ; by apply sfmupd_mono. Qed.
  Global Instance sfmupd_proper E1 E2 : Proper ((≡) ==> (≡)) (sfmupd E1 E2) := ne_proper _.

  Lemma sfmupd_fupd_l E1 E2 P :
    (|={E1,E2}=> |={E2}=>m P) ⊢ (|={E1,E2}=>m P).
  Proof.
    by erewrite fupd_sfmupd, sfmupd_trans.
  Qed.
  Lemma sfmupd_fupd_r E1 E2 P :
    (|={E1}=>m |={E1,E2}=> P) ⊢ (|={E1,E2}=>m P).
  Proof.
    by erewrite fupd_sfmupd, sfmupd_trans.
  Qed.

  Lemma sfmupd_frame_l E1 E2 R Q : (R ∗ |={E1,E2}=>m Q) ⊢ |={E1,E2}=>m R ∗ Q.
  Proof. rewrite !(comm _ R); apply sfmupd_frame_r. Qed.
  Lemma sfmupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|={E1,E2}=>m P) ⊢ |={E1,E2}=>m Q.
  Proof. by rewrite sfmupd_frame_l wand_elim_l. Qed.
  Lemma sfmupd_wand_r E1 E2 P Q : (|={E1,E2}=>m P) ∗ (P -∗ Q) ⊢ |={E1,E2}=>m Q.
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
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (sfmupd E E).
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

  Lemma except_0_sfmupd E1 E2 P : ◇ (|={E1,E2}=>m P) ⊢ (|={E1,E2}=>m ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using sfmupd_mono, or_intro_r.
    rewrite -fupd_sfmupd. iIntros "H". iApply except_0_fupd. iMod "H". done.
  Qed.

  Lemma sfmupd_fupd_acc_gen E1 E2 E3 E4 P :
    (|={E1,E2}=> |={E2,E3}=>m |={E3,E4}=> P) ⊢ (|={E1,E4}=>m P).
  Proof.
    iIntros "H". iApply (sfmupd_trans E1 E4 E2). iApply fupd_sfmupd. iMod "H". iModIntro.
    iApply (sfmupd_bind with "[] H"). iIntros "H". by iApply fupd_sfmupd.
  Qed.

  Lemma sfmupd_fupd_acc E1 E2 P :
    (|={E1,E2}=> |={E2}=>m |={E2,E1}=> P) ⊢ (|={E1}=>m P).
  Proof. apply sfmupd_fupd_acc_gen. Qed.

  (** Modality instances *)
  Global Instance elim_bupd_sfmupd (p : bool) E1 E2 P Q :
    ElimModal True p false (|==> P) P (|={E1,E2}=>m Q) (|={E1,E2}=>m Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_sfmupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_fupd_sfmupd (p : bool) E1 E2 E3 P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3}=>m Q) (|={E2,E3}=>m Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply sfmupd_trans.
    iApply fupd_sfmupd. iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_sfmupd E1 E2 P Q :
    AddModal (|={E1}=> P) P (|={E1,E2}=>m Q).
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

  Global Instance into_wand_sfmupd_persistent p q E1 E2 R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E1,E2}=>m R) P (|={E1,E2}=>m Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite sfmupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_sfmupd_args p q E1 E2 R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E1,E2}=>m P) (|={E1,E2}=>m Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim sfmupd_wand_r.
  Qed.

  Global Instance from_sep_sfmupd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E}=>m P) (|={E}=>m Q1) (|={E}=>m Q2).
  Proof. rewrite /FromSep=><-. apply sfmupd_sep. Qed.

  Global Instance from_or_sfmupd E1 E2 P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E1,E2}=>m P) (|={E1,E2}=>m Q1) (|={E1,E2}=>m Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply sfmupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_sfmupd {A} E1 E2 P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E1,E2}=>m P) (λ a, |={E1,E2}=>m Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_sfmupd E1 E2 P : IsExcept0 P → IsExcept0 (|={E1,E2}=>m P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_sfmupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_sfmupd E P :
    FromModal True modality_id (|={E}=>m P) (|={E}=>m P) P.
  Proof. by rewrite /FromModal /= -sfmupd_intro. Qed.

  Global Instance elim_modal_sfmupd p E1 E2 E3 P Q :
    ElimModal True p false (|={E1,E2}=>m P) P (|={E1,E3}=>m Q) (|={E2,E3}=>m Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim sfmupd_frame_r wand_elim_r sfmupd_trans.
  Qed.

  Global Instance add_modal_sfmupd E1 E2 P Q : AddModal (|={E1}=>m P) P (|={E1,E2}=>m Q).
  Proof. by rewrite /AddModal sfmupd_frame_r wand_elim_r sfmupd_trans. Qed.

  Global Instance frame_sfmupd p E1 E2 R P Q :
    Frame p R P Q → Frame p R (|={E1,E2}=>m P) (|={E1,E2}=>m Q).
  Proof. rewrite /Frame=><-. by rewrite sfmupd_frame_l. Qed.

  (** Later credits *)
  Lemma lc_sfmupd_add_later E1 E2 P :
    £n 1 -∗ ▷ (|={E1,E2}=>m P) -∗ |={E1,E2}=>m P.
  Proof.
    iIntros "LC H". iApply fupd_sfmupd_elim. by iApply (lantana.base_logic.fancy_updates.lc_fupd_elim_later with "LC").
  Qed.

  Lemma lc_sfmupd_add_laterN E1 E2 P n :
    £n n -∗ ▷^n (|={E1,E2}=>m P) -∗ |={E1,E2}=>m P.
  Proof.
    iIntros "LC H". iApply fupd_sfmupd_elim.
    iApply (lantana.base_logic.fancy_updates.lc_fupd_add_laterN with "LC"). iNext. auto.
  Qed.

End modality.

(** * Obligation predicates and invariants *)
(** The two states of an obligation invariant. *)
Definition oblP_variant `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  `{!ord_mono_fun_class} `{!obl_forest_interface} k (P R : iProp Σ) : iProp Σ :=
  ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R))%I.

Section preds.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!obl_forest_interface}.

  Global Instance oblP_assigned_as_fractional k q :
    AsFractional (oblP_assigned k q) (oblP_assigned k) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance oblP_inv_ne_1 N k R : NonExpansive (λ P, oblP_inv N k P R).
  Proof. apply _. Qed.
  Global Instance oblP_inv_ne_2 N k P : NonExpansive (λ R, oblP_inv N k P R).
  Proof. apply _. Qed.
  Global Instance oblP_inv_proper_1 N k R : Proper (equiv ==> equiv) (λ P, oblP_inv N k P R).
  Proof. apply ne_proper, _. Qed.
  Global Instance oblP_inv_proper_2 N k P : Proper (equiv ==> equiv) (λ R, oblP_inv N k P R).
  Proof. apply ne_proper, _. Qed.

  Global Instance oblP_variant_timeless k P R :
    Timeless P → Timeless R → Timeless (oblP_variant k P R).
  Proof. rewrite /oblP_variant. apply _. Qed.

  Lemma oblP_variant_unfold k P R :
    oblP_variant k P R ⊣⊢ ((oblP_assigned k (1/2)%Qp ∗ P) ∨ (oblP_discharged k ∗ R))%I.
  Proof. done. Qed.

  Lemma oblP_inv_acc_cases E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    (▷ oblP_variant k P R) ∗ (▷ oblP_variant k P R ={E ∖ ↑N,E}=∗ True).
  Proof. apply oblP_inv_acc. Qed.

  Lemma oblP_inv_acc_assigned E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗ ∀ q,
    oblP_assigned k q -∗
    (▷ (oblP_assigned k q ∗ oblP_assigned k (1/2) ∗ P)) ∗
    (▷ oblP_variant k P R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HN) "I". iMod (oblP_inv_acc with "I") as "[V ACC]"; first done.
    iIntros "!> %q A". iFrame "ACC". iNext. iDestruct "V" as "[[A' HP] | [D _]]".
    - iFrame.
    - iDestruct (oblP_assigned_discharged_false with "A D") as %[].
  Qed.

  Lemma oblP_inv_acc_discharged E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R ={E,E ∖ ↑N}=∗
    oblP_discharged k -∗ (▷ R) ∗ (▷ oblP_variant k P R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HN) "I". iMod (oblP_inv_acc with "I") as "[V ACC]"; first done.
    iIntros "!> #D". iFrame "ACC". iNext. iDestruct "V" as "[[A _] | [_ $]]".
    iDestruct (oblP_assigned_discharged_false with "A D") as %[].
  Qed.

  Lemma oblP_inv_acc_discharged_persistent E N k P R :
    Persistent R →
    ↑N ⊆ E →
    oblP_inv N k P R -∗ oblP_discharged k ={E}[E ∖ ↑N]▷=∗ R.
  Proof.
    iIntros (PR HE) "#I #D". iMod (oblP_inv_acc_discharged with "I D") as "[H ACC]"; first done.
    iModIntro. iNext. iPoseProof "H" as "#H". iFrame "H". iApply "ACC".
    rewrite oblP_variant_unfold. iRight. eauto.
  Qed.

  (** ** Witness induction *)
  Lemma wit_fuels_add_map_gen k ℓ α F (G : gmap oid (layer * measure)) :
    wit_fuels k ℓ α F -∗
    ([∗ map] g ↦ lm ∈ G, let '(l, m) := lm in ⌜ (ℓ < l)%ordi ⌝ ∗ oblP_fuel g l (m × ▽)%M) ==∗
    wit_fuels k ℓ α (G ∪ F).
  Proof.
    revert F. induction G as [|f x G Hf IH] using map_ind; iIntros (F) "W Fs".
    { rewrite left_id_L. by iFrame. }
    destruct x as [l m]. rewrite big_sepM_insert; last done.
    iDestruct "Fs" as "((%Hl& Ff)& Fs)".
    iMod (IH with "W Fs") as "W". rewrite -insert_union_l.
    iApply (wit_fuels_add with "W Ff"). done.
  Qed.

  Lemma wit_fuels_add_map k ℓ α F G l m :
    (ℓ < l)%ordi →
    wit_fuels k ℓ α F -∗
    ([∗ set] g ∈ G, oblP_fuel g l (m × ▽)%M) ==∗
    wit_fuels k ℓ α ((gset_to_gmap (l, m) G) ∪ F).
  Proof.
    iIntros (Hl) "W Fs". iApply (wit_fuels_add_map_gen with "W").
    rewrite big_sepM_gset_to_gmap. iApply (big_sepS_impl with "Fs"). iIntros "!> %% $". done.
  Qed.

  Lemma wit_fuels_ind k ℓ α F (P : iProp Σ) :
    □ ((witP_cred1 k ==∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m) ∗ P) ==∗ P) ∗
    wit_fuels k ℓ α F
    ⊢ |==> P.
  Proof.
    iIntros "[#H WF]". iInduction α as [α IH] using (well_founded_ind WFOCM.lt_wf).
    iApply "H". iIntros "Wc". iMod (wit_fuels_decr with "WF Wc") as "(%&%& WF& Fs)".
    iFrame "Fs". iApply ("IH" with "[//] WF").
  Qed.

  Lemma wit_layer_ind k ℓ G l m (P : iProp Σ) :
    (ℓ < l)%ordi →
    □ ((witP_cred1 k ==∗ ([∗ set] g ∈ G, oblP_fuel g l m) ∗ P) ==∗ P) ∗
    witP_layer k ℓ ∗
    ([∗ set] g ∈ G, oblP_fuel g l (m × ▽)%M)
    ⊢ |==> P.
  Proof.
    iIntros (LT) "(#IND& #Wl& FG)". iPoseProof (wit_fuels_init with "Wl") as "[% Wf0]".
    iMod (wit_fuels_add_map with "Wf0 FG") as "WF". 1: auto.
    iApply (wit_fuels_ind with "[IND $WF]").
    iIntros "!> H". rewrite map_union_empty big_sepM_gset_to_gmap.
    iApply ("IND" with "H").
  Qed.

  (** ** Parents *)
  Global Instance parent_below_persistent p ℓ : Persistent (parP_below p ℓ).
  Proof. destruct p; rewrite /parent_below; apply _. Qed.

  Lemma parP_below_thread i ℓ : ⊢ parP_below (PThread i) ℓ.
  Proof. done. Qed.

  Lemma parP_below_obl q ℓq ℓ :
    (ℓq < ℓ)%ordi → witP_layer q ℓq -∗ parP_below (PObl q) ℓ.
  Proof. iIntros (Hl) "W". iExists ℓq. by iFrame. Qed.

  Global Instance parent_le_persistent p ℓ : Persistent (parP_le p ℓ).
  Proof. destruct p; rewrite /parent_le; apply _. Qed.

  Lemma parP_le_thread i ℓ : ⊢ parP_le (PThread i) ℓ.
  Proof. done. Qed.

  Lemma parP_le_obl q ℓq ℓ :
    (ℓq <= ℓ)%ordi → witP_layer q ℓq -∗ parP_le (PObl q) ℓ.
  Proof. iIntros (Hl) "W". iExists ℓq. by iFrame. Qed.

  Lemma parP_below_le p ℓ : parP_below p ℓ -∗ parP_le p ℓ.
  Proof.
    destruct p as [i|q]; first by iIntros. iIntros "(%ℓq& %Hl& W)". iExists ℓq. iFrame.
    iPureIntro. by apply ord.lt_le.
  Qed.
End preds.

(** * Fuel and credit algebra *)
Section fuel.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!obl_forest_interface}.

  Local Open Scope ord.

  (** ** oblP_fuel rules *)
  Lemma oblP_fuel_layer_eq k ℓ1 ℓ2 μ :
    (ℓ1 == ℓ2)%ordi →
    oblP_fuel k ℓ1 μ ⊣⊢ oblP_fuel k ℓ2 μ.
  Proof.
    intros. apply oblP_fuel_proper; first done.
    by apply measure_rep_layer_eq.
  Qed.
  Lemma oblP_fuel_layer_eq_list K ℓ1 ℓ2 μ :
    (ℓ1 == ℓ2)%ordi →
    ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ)%I ≡ ([∗ list] k ∈ K, oblP_fuel k ℓ2 μ)%I.
  Proof. intros. apply big_opL_proper. intros. by apply oblP_fuel_layer_eq. Qed.
  Lemma oblP_fuel_layer_eq_set K ℓ1 ℓ2 μ :
    (ℓ1 == ℓ2)%ordi →
    ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ)%I ≡ ([∗ set] k ∈ K, oblP_fuel k ℓ2 μ)%I.
  Proof. intros. apply big_opS_proper. intros. by apply oblP_fuel_layer_eq. Qed.

  Lemma oblP_fuel_eq k ℓ μ1 μ2 :
    (measure_rep ℓ (μ1)%M == measure_rep ℓ (μ2)%M) →
    oblP_fuel k ℓ μ1 ⊣⊢ oblP_fuel k ℓ μ2.
  Proof. intros. apply oblP_fuel_proper; [reflexivity|done]. Qed.
  Lemma oblP_fuel_eq_list K ℓ μ1 μ2 :
    (measure_rep ℓ (μ1)%M == measure_rep ℓ (μ2)%M) →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2)%I.
  Proof. intros. apply big_opL_proper. intros. by apply oblP_fuel_eq. Qed.
  Lemma oblP_fuel_eq_set K ℓ μ1 μ2 :
    (measure_rep ℓ (μ1)%M == measure_rep ℓ (μ2)%M) →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ1)%I ≡ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2)%I.
  Proof. intros. apply big_opS_proper. intros. by apply oblP_fuel_eq. Qed.

  Lemma oblP_fuel_mon_gen_list K ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 <= ℓ2)%ordi →
    (measure_rep ℓ1 (μ1)%M <= measure_rep ℓ2 (μ2)%M)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ2 μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ1).
  Proof.
    iIntros (LL LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_mon_gen.
  Qed.
  Lemma oblP_fuel_mon_gen_set K ℓ1 ℓ2 μ1 μ2 :
    (ℓ1 <= ℓ2)%ordi →
    (measure_rep ℓ1 (μ1)%M <= measure_rep ℓ2 (μ2)%M)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ2 μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ1).
  Proof.
    iIntros (LL LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_mon_gen.
  Qed.

  Lemma oblP_fuel_mon k ℓ μ1 μ2 :
    (measure_rep ℓ (μ1)%M <= measure_rep ℓ (μ2)%M)%ord →
    oblP_fuel k ℓ μ2 ==∗ oblP_fuel k ℓ μ1.
  Proof. intros. apply oblP_fuel_mon_gen; auto. done. Qed.
  Lemma oblP_fuel_mon_list K ℓ μ1 μ2 :
    (measure_rep ℓ (μ1)%M <= measure_rep ℓ (μ2)%M)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_mon.
  Qed.
  Lemma oblP_fuel_mon_set K ℓ μ1 μ2 :
    (measure_rep ℓ (μ1)%M <= measure_rep ℓ (μ2)%M)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_mon.
  Qed.

  Lemma oblP_fuel_layer_mon k ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    oblP_fuel k ℓ2 μ ==∗ oblP_fuel k ℓ1 μ.
  Proof.
    iIntros (LE) "H". iApply (oblP_fuel_mon_gen with "H"). 1: auto.
    by apply measure_rep_layer_le.
  Qed.
  Lemma oblP_fuel_layer_mon_list K ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    ([∗ list] k ∈ K, oblP_fuel k ℓ2 μ) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_layer_mon.
  Qed.
  Lemma oblP_fuel_layer_mon_set K ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    ([∗ set] k ∈ K, oblP_fuel k ℓ2 μ) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_layer_mon.
  Qed.

  Lemma oblP_fuel_mon_split k ℓ μ1 μ2 μ3 :
    ((measure_rep ℓ (μ1)%M ⊕ measure_rep ℓ (μ2)%M) <= measure_rep ℓ (μ3)%M)%ord →
    oblP_fuel k ℓ μ3 ==∗ oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ μ2.
  Proof.
    intros. rewrite -oblP_fuel_add. iIntros "H". iApply (oblP_fuel_mon with "H").
    rewrite measure_rep_add. done.
  Qed.
  Lemma oblP_fuel_mon_split_list K ℓ μ1 μ2 μ3 :
    ((measure_rep ℓ (μ1)%M ⊕ measure_rep ℓ (μ2)%M) <= measure_rep ℓ (μ3)%M)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ3) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    iIntros (LE) "H". rewrite -big_sepL_sep -big_sepL_bupd. iApply (big_sepL_impl with "H").
    iIntros "!> % % %". iApply oblP_fuel_mon_split; auto.
  Qed.
  Lemma oblP_fuel_mon_split_set K ℓ μ1 μ2 μ3 :
    ((measure_rep ℓ (μ1)%M ⊕ measure_rep ℓ (μ2)%M) <= measure_rep ℓ (μ3)%M)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ3) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    iIntros (LE) "H". rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "H").
    iIntros "!> % %". iApply oblP_fuel_mon_split; auto.
  Qed.

  Lemma oblP_fuel_lt k ℓ μ1 μ2 :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    oblP_fuel k ℓ μ2 ⊢ |==> oblP_fuel k ℓ μ1 ∗ oblP_fuel k ℓ (1)%M.
  Proof.
    intros. rewrite -oblP_fuel_add. iIntros "H". iApply (oblP_fuel_mon with "H").
    rewrite measure_rep_add measure_rep_nat. rewrite Hessenberg.add_comm -ord_S_add.
    apply Ord.S_supremum; auto.
  Qed.
  Lemma oblP_fuel_lt_list K ℓ μ1 μ2 :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_lt.
  Qed.
  Lemma oblP_fuel_lt_set K ℓ μ1 μ2 :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ μ2) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    iIntros (LT) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblP_fuel_lt.
  Qed.

  (** measurable syntax rules. *)
  Lemma oblP_fuel_embed k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
    ltA a1 a2 →
    oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M ⊢ |==> oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M ∗ oblP_fuel k ℓ 1.
  Proof.
    intros. apply oblP_fuel_lt. apply measure_rep_embed_lt. auto.
  Qed.
  Lemma oblP_fuel_embed_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
    ltA a1 a2 →
    ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
    ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply oblP_fuel_embed. auto.
  Qed.
  Lemma oblP_fuel_embed_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a1 a2 : A) :
    ltA a1 a2 →
    ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a2⟫)%M)
    ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a1⟫)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply oblP_fuel_embed. auto.
  Qed.

  Lemma oblP_fuel_large k ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
    oblP_fuel k ℓ (ℵ)%M ⊢ |==> oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M ∗ oblP_fuel k ℓ 1.
  Proof.
    intros. apply oblP_fuel_lt. apply measure_rep_large_lt.
  Qed.
  Lemma oblP_fuel_large_list K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
    ([∗ list] k ∈ K, oblP_fuel k ℓ (ℵ)%M)
    ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    intros. rewrite -big_sepL_sep -big_sepL_bupd. iApply big_sepL_mono. intros. apply oblP_fuel_large.
  Qed.
  Lemma oblP_fuel_large_set K ℓ {A} {ltA} (wf_ltA : well_founded ltA) (a : A) :
    ([∗ set] k ∈ K, oblP_fuel k ℓ (ℵ)%M)
    ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (⟪wf_ltA, a⟫)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ 1).
  Proof.
    intros. rewrite -big_sepS_sep -big_sepS_bupd. iApply big_sepS_mono. intros. apply oblP_fuel_large.
  Qed.

  Lemma oblP_fuel_add_list K ℓ μ1 μ2 :
    ([∗ list] k ∈ K, oblP_fuel k ℓ (μ1 ⊕ μ2)%M)
    ⊣⊢ ([∗ list] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oblP_fuel_add.
  Qed.
  Lemma oblP_fuel_add_set K ℓ μ1 μ2 :
    ([∗ set] k ∈ K, oblP_fuel k ℓ (μ1 ⊕ μ2)%M) ⊣⊢ ([∗ set] k ∈ K, oblP_fuel k ℓ μ1) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ μ2).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oblP_fuel_add.
  Qed.

  Lemma oblP_fuel_mult k ℓ μ1 μ2 s :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    oblP_fuel k ℓ (s × μ2)%M ⊢ |==> oblP_fuel k ℓ (s × μ1)%M ∗ oblP_fuel k ℓ s.
  Proof.
    intros LT. rewrite -oblP_fuel_add. iIntros "H". iApply (oblP_fuel_mon with "H").
    rewrite measure_rep_add !measure_rep_mult.
    transitivity (measure_rep ℓ s × Ord.S (measure_rep ℓ μ1)).
    - rewrite Jacobsthal.mult_S Hessenberg.add_comm. done.
    - apply Jacobsthal.le_mult_r. by apply Ord.S_supremum.
  Qed.
  Lemma oblP_fuel_mult_list K ℓ μ1 μ2 s :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ (s × μ2)%M)
    ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ (s × μ1)%M) ∗ ([∗ list] k ∈ K, oblP_fuel k ℓ s).
  Proof.
    rewrite -big_sepL_sep -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_mult. auto.
  Qed.
  Lemma oblP_fuel_mult_set K ℓ μ1 μ2 s :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ (s × μ2)%M)
    ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ (s × μ1)%M) ∗ ([∗ set] k ∈ K, oblP_fuel k ℓ s).
  Proof.
    rewrite -big_sepS_sep -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_mult. auto.
  Qed.

  Lemma oblP_fuel_expn k ℓ μ1 μ2 s :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    (Ord.O < measure_rep ℓ s)%ord →
    oblP_fuel k ℓ (s ↑ μ2)%M ⊢ |==> oblP_fuel k ℓ ((s ↑ μ1) × s)%M.
  Proof.
    intros LT Pos. iIntros "H". iApply (oblP_fuel_mon with "H").
    rewrite measure_rep_mult !measure_rep_expn -(Jacobsthal.expn_S Pos).
    apply Jacobsthal.le_expn_r. by apply Ord.S_supremum.
  Qed.
  Lemma oblP_fuel_expn_list K ℓ μ1 μ2 s :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    (Ord.O < measure_rep ℓ s)%ord →
    ([∗ list] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
  Proof.
    rewrite -big_sepL_bupd. intros. apply big_sepL_mono; intros. apply oblP_fuel_expn; auto.
  Qed.
  Lemma oblP_fuel_expn_set K ℓ μ1 μ2 s :
    (measure_rep ℓ μ1 < measure_rep ℓ μ2)%ord →
    (Ord.O < measure_rep ℓ s)%ord →
    ([∗ set] k ∈ K, oblP_fuel k ℓ (s ↑ μ2)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ ((s ↑ μ1) × s)%M).
  Proof.
    rewrite -big_sepS_bupd. intros. apply big_sepS_mono; intros. apply oblP_fuel_expn; auto.
  Qed.

  Lemma oblP_fuel_extend_list K ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    ([∗ list] k ∈ K, oblP_fuel k ℓ2 1) ⊢ |==> ([∗ list] k ∈ K, oblP_fuel k ℓ1 μ).
  Proof.
    intros. rewrite -big_sepL_bupd. iApply big_sepL_mono. intros. iIntros "H". by iApply (oblP_fuel_extend with "H").
  Qed.
  Lemma oblP_fuel_extend_set K ℓ1 ℓ2 μ :
    (ℓ1 < ℓ2)%ordi →
    ([∗ set] k ∈ K, oblP_fuel k ℓ2 (1)%M) ⊢ |==> ([∗ set] k ∈ K, oblP_fuel k ℓ1 μ).
  Proof.
    intros. rewrite -big_sepS_bupd. iApply big_sepS_mono. intros. iIntros "H". by iApply (oblP_fuel_extend with "H").
  Qed.

  (** ** witP_cred rules *)
  Lemma witP_cred_eq k a0 a1 :
    (a0 == a1) → witP_cred k a1 ⊣⊢ witP_cred k a0.
  Proof. intros. symmetry. by apply witP_cred_proper. Qed.
  Lemma witP_cred_mon_split k a0 a1 a2 :
    ((a0 ⊕ a1) <= a2)%ord →
    witP_cred k a2 ==∗ witP_cred k a0 ∗ witP_cred k a1.
  Proof. intros. rewrite -witP_cred_split. iIntros "H". by iApply (witP_cred_mon with "H"). Qed.
  Lemma witP_cred_lt k a0 a1 :
    (a0 < a1) → witP_cred k a1 ==∗ witP_cred k a0 ∗ witP_cred1 k.
  Proof.
    intros. iIntros "H". iApply (witP_cred_mon_split with "H").
    transitivity (Ord.S a0); last by apply Ord.S_supremum.
    rewrite Hessenberg.add_comm (ord_S_add a0). reflexivity.
  Qed.

  Lemma oblP_fuel_add_nat m1 m2 n k ℓ :
    (n = m1 + m2)%nat →
    oblP_fuel k ℓ n ⊣⊢ (oblP_fuel k ℓ m1 ∗ oblP_fuel k ℓ m2)%I.
  Proof.
    intros ->. rewrite -oblP_fuel_add. apply oblP_fuel_eq.
    rewrite measure_rep_add !measure_rep_nat. rewrite -Hessenberg.add_from_nat. done.
  Qed.

  Lemma oblP_fuels_add_gen m1 m2 K :
    oblP_fuels K (m1 ⊕ m2)%M ⊢ oblP_fuels K m1 ∗ oblP_fuels K m2.
  Proof.
    rewrite -big_sepS_sep. iIntros "H"; iApply (big_sepS_impl with "H"); iIntros "!> %% H".
    iDestruct "H" as "(%& H)". iPoseProof (oblP_fuel_add with "H") as "[$ $]".
  Qed.

  Lemma oblP_fuels_add (n m : nat) K :
    oblP_fuels K (n + m)%nat ⊢ oblP_fuels K n ∗ oblP_fuels K m.
  Proof.
    rewrite -big_sepS_sep. iIntros "H"; iApply (big_sepS_impl with "H"); iIntros "!> %% H".
    iDestruct "H" as "(%& H)". iPoseProof (oblP_fuel_add_nat with "H") as "[H F]". 1: eauto.
    iFrame.
  Qed.

  Lemma oblP_fuels_add_nat (m1 m2 n : nat) K :
    (n = m1 + m2)%nat →
    oblP_fuels K n ⊢ oblP_fuels K m1 ∗ oblP_fuels K m2.
  Proof. intros ->. apply oblP_fuels_add. Qed.

  Lemma oblP_fuels_init K m ℓ :
    ([∗ set] k ∈ K, oblP_fuel k ℓ m)%I ⊢ oblP_fuels K m.
  Proof. iIntros "H". iApply (big_sepS_impl with "H"). iIntros "!> %% $". Qed.

  Lemma oblP_fuels_add_obl K k ℓ n :
    oblP_fuel k ℓ n -∗ oblP_fuels K n -∗ oblP_fuels ({[k]} ∪ K) n.
  Proof.
    iIntros "H2 H1". iApply (big_sepS_union_2 with "[H2] H1"). iApply big_sepS_singleton. iFrame.
  Qed.

  Lemma oblP_fuels_add_obls K1 K2 n :
    oblP_fuels K1 n -∗ oblP_fuels K2 n -∗ oblP_fuels (K1 ∪ K2) n.
  Proof. iIntros "H1 H2". iApply (big_sepS_union_2 with "H1 H2"). Qed.

  Lemma oblP_fuels_remove_obl k K n :
    oblP_fuels K n -∗ oblP_fuels (K ∖ {[k]}) n.
  Proof.
    iIntros "H". destruct (decide (k ∈ K)); cycle 1.
    { replace (K ∖ {[k]}) with K by set_solver. auto. }
    iPoseProof (big_sepS_delete _ _ k with "H") as "[_ $]". auto.
  Qed.

  Lemma oblP_fuels_remove_obls K2 K1 n :
    oblP_fuels K1 n -∗ oblP_fuels (K1 ∖ K2) n.
  Proof.
    rewrite -(difference_union_intersection_L K1 K2).
    iIntros "H". iPoseProof (big_sepS_union with "H") as "[H1 H2]". 1: set_solver.
    rewrite (difference_union_intersection_L K1 K2). iFrame.
  Qed.

End fuel.

(** * Fuels for an induction on a well-founded order [ltA], embedded in the measures *)
Section embed_fuels.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!obl_forest_interface}.

  (** [embed_fuels wf_ltA a F]: each fuel [(l, m)] of [F], times [a]. *)
  Definition embed_fuels {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
      (a : A) (F : gmap oid (layer * measure)) : iProp Σ :=
    [∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l (m × ⟪wf_ltA, a⟫)%M.

  Lemma embed_fuels_init {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a :
    ⊢ embed_fuels wf_ltA a ∅.
  Proof. by rewrite /embed_fuels big_sepM_empty. Qed.

  Lemma embed_fuels_add_map {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
    a F G l m :
    embed_fuels wf_ltA a F -∗
    ([∗ set] g ∈ G, oblP_fuel g l (m × ℵ)%M) ==∗
    embed_fuels wf_ltA a ((gset_to_gmap (l, m) G) ∪ F).
  Proof.
    rewrite /embed_fuels.
    revert F. induction G as [|g G Hg IH] using set_ind_L; intros F; iIntros "Efs Fs".
    { rewrite gset_to_gmap_empty left_id_L. by iFrame. }
    rewrite big_sepS_insert; last done. iDestruct "Fs" as "[Fg Fs]".
    iMod (IH with "Efs Fs") as "Efs".
    rewrite gset_to_gmap_union_singleton -insert_union_l.
    iMod (oblP_fuel_mon _ _ (m × ⟪wf_ltA, a⟫)%M with "Fg") as "Fg".
    { rewrite !measure_rep_mult. apply Jacobsthal.le_mult_r.
      apply Ord.lt_le, measure_rep_large_lt. }
    iModIntro. iApply (big_sepM_insert_delete _ _ g). iFrame "Fg".
    destruct ((gset_to_gmap (l, m) G ∪ F) !! g) eqn:LU.
    - iPoseProof (big_sepM_delete _ _ g with "Efs") as "[_ $]"; eauto.
    - by rewrite delete_id.
  Qed.

  Lemma embed_fuels_decr {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA) a a' F :
    ltA a' a →
    embed_fuels wf_ltA a F ==∗
    embed_fuels wf_ltA a' F ∗ ([∗ map] f ↦ '(l, m) ∈ F, oblP_fuel f l m).
  Proof.
    rewrite /embed_fuels. iIntros (LT) "Fs".
    rewrite -big_sepM_sep -big_sepM_bupd. iApply (big_sepM_impl with "Fs").
    iIntros "!>" (f [l m] _) "F". iApply (oblP_fuel_mult with "F").
    by apply measure_rep_embed_lt.
  Qed.
End embed_fuels.

(** * Model updates in their usual shapes *)
Section model_updates.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!obl_forest_interface}.
  Context `{!TemporalInterp Λ Σ}.

  (** ** Allocation and moves *)
  Lemma obl_alloc_assigned E p K ℓ μ :
    parP_le p ℓ -∗ parP_kids p K -∗
    |={E}=>m ∃ k, ⌜ k ∉ K ⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_assigned k (1/2)%Qp ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 (∀ E N (P R : iProp Σ), ▷ P ={E}=∗ oblP_inv N k P R).
  Proof.
    iIntros "B C". iMod (obl_new with "B C") as (k) "(%Hk& C& Ck& [A1 A2]& F& W)".
    iModIntro. iExists k. iFrame "C Ck A1 F W". iSplit; first done.
    iIntros (E' N P R) "H". iApply (oblP_inv_alloc_assigned with "A2 H").
  Qed.

  (** Moving a set [X] of children of [p1] to [p2], one unit each, each at its own layer. *)
  Lemma obl_move_set_gen E p1 p2 K1 K2 X :
    X ⊆ K1 →
    parP_kids p1 K1 -∗ parP_kids p2 K2 -∗
    ([∗ set] k ∈ X, ∃ ℓ, parP_below p2 ℓ ∗ oblP_fuel k ℓ 1) -∗
    |={E}=>m ⌜ X ## K2 ⌝ ∗ parP_kids p1 (K1 ∖ X) ∗ parP_kids p2 (X ∪ K2).
  Proof.
    induction X as [|x X Hx IH] using set_ind_L; iIntros (HX) "P1 P2 Fs".
    { rewrite difference_empty_L left_id_L. iModIntro. iFrame. iPureIntro. set_solver. }
    iPoseProof (big_sepS_insert with "Fs") as "[(%ℓ& B& Fx) Fs]"; first done.
    iMod (IH with "P1 P2 Fs") as "(%Hdis& P1& P2)"; first set_solver.
    iMod (obl_move _ _ _ _ _ x with "B P1 P2 Fx") as "(%Hx2& P1& P2)"; first set_solver.
    replace (K1 ∖ X ∖ {[x]}) with (K1 ∖ ({[x]} ∪ X)) by set_solver.
    replace ({[x]} ∪ (X ∪ K2)) with ({[x]} ∪ X ∪ K2) by set_solver.
    iModIntro. iFrame. iPureIntro. set_solver.
  Qed.

  (** Moving a set [X] of children of [p1] below the thread [j]: one unit each, at any
      layer. *)
  Lemma obl_move_thread_set E p1 j K1 K2 X :
    X ⊆ K1 →
    parP_kids p1 K1 -∗ thP_kids j K2 -∗ ([∗ set] k ∈ X, ∃ ℓ, oblP_fuel k ℓ 1) -∗
    |={E}=>m ⌜ X ## K2 ⌝ ∗ parP_kids p1 (K1 ∖ X) ∗ thP_kids j (X ∪ K2).
  Proof.
    iIntros (HX) "P1 P2 Fs". iApply (obl_move_set_gen with "P1 P2"); first done.
    iApply (big_sepS_impl with "Fs"). iIntros "!> %k _ [%ℓ F]". iExists ℓ. iFrame "F".
    iApply parP_below_thread.
  Qed.

  (** Moving a set [X] of children of [p1] below the obligation [q]: one unit each, each at
      a layer above the witness layer [ℓq] of [q]. *)
  Lemma obl_move_obl_set E p1 q K1 K2 X ℓq :
    X ⊆ K1 →
    witP_layer q ℓq -∗ parP_kids p1 K1 -∗ oblP_kids q K2 -∗
    ([∗ set] k ∈ X, ∃ ℓ, ⌜ (ℓq < ℓ)%ordi ⌝ ∗ oblP_fuel k ℓ 1) -∗
    |={E}=>m ⌜ X ## K2 ⌝ ∗ parP_kids p1 (K1 ∖ X) ∗ oblP_kids q (X ∪ K2).
  Proof.
    iIntros (HX) "#W P1 P2 Fs". iApply (obl_move_set_gen with "P1 P2"); first done.
    iApply (big_sepS_impl with "Fs"). iIntros "!> %k _ (%ℓ& %Hl& F)". iExists ℓ. iFrame "F".
    by iApply (parP_below_obl q ℓq ℓ Hl).
  Qed.

  (** Moving a set [X] of children of [k] up to the parent [p] of [k], for free. *)
  Lemma obl_move_up_set E p K k Kk X :
    k ∈ K → X ⊆ Kk →
    parP_kids p K -∗ oblP_kids k Kk -∗
    |={E}=>m ⌜ X ## K ⌝ ∗ parP_kids p (X ∪ K) ∗ oblP_kids k (Kk ∖ X).
  Proof.
    induction X as [|x X Hx IH] using set_ind_L; iIntros (Hk HX) "P Ck".
    { rewrite difference_empty_L left_id_L. iModIntro. iFrame. iPureIntro. set_solver. }
    iMod (IH with "P Ck") as "(%Hdis& P& Ck)"; [done|set_solver|].
    iMod (obl_move_up _ _ _ k _ x with "P Ck") as "(%Hx2& P& Ck)"; [set_solver|set_solver|].
    replace (Kk ∖ X ∖ {[x]}) with (Kk ∖ ({[x]} ∪ X)) by set_solver.
    replace ({[x]} ∪ (X ∪ K)) with ({[x]} ∪ X ∪ K) by set_solver.
    iModIntro. iFrame. iPureIntro. set_solver.
  Qed.

  Lemma obl_alloc_discharged E ℓ :
    ⊢ |={E}=>m ∃ k, oblP_discharged k ∗ witP_layer k ℓ ∗
                   (∀ E N (P R : iProp Σ), (▷ R) ={E}=∗ oblP_inv N k P R).
  Proof.
    iMod (obl_new_discharged E ℓ) as (k) "(#D& W)". iModIntro. iExists k. iFrame "D W".
    iIntros (E' N P R) "H". iApply (oblP_inv_alloc_discharged with "D H").
  Qed.

  Lemma obl_check_witnesses E (R : oids) :
    ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) -∗
    |={E}=>m ([∗ set] r ∈ R, (witP_cred0 r) ∨ oblP_discharged r).
  Proof.
    iIntros "Rs". iApply big_sepS_sfmupd. iApply (big_sepS_impl with "Rs").
    iIntros "!> %r _ [%ℓ W]". iApply (obl_check_witness with "W").
  Qed.

  (** ** Discharge *)
  (** Discharging [k] after moving its children up to its parent [p] (for free). *)
  Lemma obl_discharge_lift_kids E p K k Kk :
    k ∈ K →
    parP_kids p K -∗ oblP_kids k Kk -∗ oblP_assigned k 1 -∗
    |={E}=>m parP_kids p (Kk ∪ (K ∖ {[k]})) ∗ oblP_discharged k.
  Proof.
    iIntros (Hk) "P Ck A".
    iMod (obl_move_up_set _ p K k Kk Kk with "P Ck") as "(%Hdis& P& Ck)"; [done|done|].
    rewrite difference_diag_L.
    iMod (obl_discharge_leaf with "P Ck A") as "[P D]"; first set_solver.
    replace ((Kk ∪ K) ∖ {[k]}) with (Kk ∪ (K ∖ {[k]})) by set_solver.
    by iFrame.
  Qed.

  (** Discharging [k] with the invariant [oblP_inv N k P R]: [P] is taken out, and once [R] is
      established [k], a childless child of [p], is discharged. *)
  Lemma obl_discharge_inv E N k P R :
    ↑N ⊆ E →
    oblP_inv N k P R -∗
    |={E,E ∖ ↑N}=> ∀ q, oblP_assigned k q -∗
    ▷ (oblP_assigned k q ∗ oblP_assigned k (1/2) ∗ P) ∗
    (∀ p K, ⌜ k ∈ K ⌝ → parP_kids p K -∗ oblP_kids k ∅ -∗ oblP_assigned k 1 -∗ ▷ R -∗
     ∀ E', |={E'}=>m |={E ∖ ↑N,E}=> parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k).
  Proof.
    iIntros (HN) "#I". iMod (oblP_inv_acc_assigned with "I") as "H"; first done.
    iIntros "!> %q A". iDestruct ("H" with "A") as "[$ ACC]".
    iIntros (p K Hk) "Kp Kk A HR %E'". iMod (obl_discharge_leaf with "Kp Kk A") as "[$ #D]"; first done.
    iModIntro. iMod ("ACC" with "[HR]") as "_".
    { iNext. rewrite oblP_variant_unfold. iRight. iFrame "D HR". }
    iModIntro. iFrame "D".
  Qed.
End model_updates.

(** * Physical steps in their usual shapes (cf. [model_physical_updates.v]) *)
Section steps.
  Context `{SI : sidx} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!ord_mono_fun_class}.
  Context `{!obl_forest_interface}.

  Lemma mprog_step n Θ i P :
    (|={∅}=> ∃ K, thP_kids i K ∗ oblP_fuels K 1 ∗
                   ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                        ((thP_kids i K ∗ ([∗ set] r ∈ R, witP_cred1 r ∨ oblP_discharged r))
                         ={∅}=∗ P))
    ⊢ mprog n Θ i P.
  Proof.
    iIntros "H". iApply fupd_mprog. iMod "H" as (K) "(T& F& %R& W& H)". iModIntro.
    iApply (step_progress with "T F W"). iIntros "T C". iApply ("H" with "[$T $C]").
  Qed.

  Lemma mphys_step n1 n2 Θ1 Θ2 π P :
    n1 ≤ n2 →
    Θ2 = Θ1 ∪ π →
    Θ1 ## π →
    (|={∅}=> ([∗ set] j ∈ π, thP_kids j ∅) ={∅}=∗ P)
    ⊢ mphys n1 n2 Θ1 Θ2 P.
  Proof.
    iIntros (???) "H". iApply fupd_mphys. iMod "H". iModIntro. by iApply (step_fork with "H").
  Qed.
End steps.
