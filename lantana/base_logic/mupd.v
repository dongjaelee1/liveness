From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Export fixpoint_mono.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.algebra Require Import ordinal_wfocm.
From lantana.base_logic Require Export owit othread oforest model_rel model_interp invariants.
(* From lantana.base_logic Require Export history_interp invariants. *)
Import uPred.

Class mupdGpreS `{SI : sidx} (Σ : gFunctors) :=
  MupdGpreS {
      #[local] mupdGpreS_inv :: invGpreS Σ;
      #[local] mupdGpreS_osat :: osatGS.osatGpreS Σ;
      #[local] mupdGpreS_othread :: othreadGS.othreadGpreS Σ;
      #[local] mupdGpreS_oforest :: oforestGS.oforestGpreS Σ;
      #[local] mupdGpreS_owit :: owitGS.owitGpreS Σ;
      #[local] mupdGpreS_mhist :: mhistGS.mhistGpreS Σ;
    }.

Class mupdGS `{SI : sidx} (Σ : gFunctors) :=
  MupdG {
      (** Invariants. *)
      #[global] mupd_invGS :: invGS Σ;
      (** Obls. *)
      #[global] mupd_osatGS :: osatGS.osatGS Σ;
      (** Obls assigned to threads. *)
      #[global] mupd_othreadGS :: othreadGS.othreadGS Σ;
      (** Obligation forest. *)
      #[global] mupd_oforestGS :: oforestGS.oforestGS Σ;
      (** Witnesses. *)
      #[global] mupd_owitGS :: owitGS.owitGS Σ;
      (** Model history. *)
      #[global] mupd_mhistGS :: mhistGS.mhistGS Σ;
    }.
Global Opaque mupd_invGS mupd_osatGS mupd_othreadGS mupd_oforestGS mupd_owitGS mupd_mhistGS.
Global Arguments MupdG {SI Σ}.

Definition mupdΣ `{SI : sidx} : gFunctors :=
  #[invΣ; osatGS.osatΣ; othreadGS.othreadΣ; oforestGS.oforestΣ; owitGS.owitΣ; mhistGS.mhistΣ].
Global Instance subG_mupdΣ `{SI : sidx} {Σ} : subG mupdΣ Σ → mupdGpreS Σ.
Proof. solve_inG. Qed.

Definition model_interp `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class}
  h i Ω W n Θ : iProp Σ :=
  (model_history_interp h i n Ω ∗ osat Ω ∗ othread Θ ∗ oassigned (dom Ω) ∗ oforest Ω Θ ∗ owit W ∗ ⌜ owit_inv Ω W ⌝)%I.

(** ** Modality for updating obls. *)
Definition mupd_pre `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class}
  n Θ (mupd : iPropO Σ -d> iPropO Σ) : iProp Σ -d> iPropO Σ :=
  λ P,
    ((|={∅}=> P) ∨
       (∀ h i Ω1 W1,
          (model_interp h i Ω1 W1 n Θ) ={∅}=∗
          ∃ Ω2, (⌜ obls_lef Ω1 Ω2 ⌝) ∗
                ∀ W2, (⌜ wits_lef W1 W2 ∧ owit_inv Ω2 W2 ⌝) ={∅}=∗
                      (model_interp (h ++ [(n, Ω2)]) (S i) Ω2 W2 n Θ) ∗ mupd P))%I.

Lemma mupd_pre_mono `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class}
  n Θ (mupd1 mupd2 : iPropO Σ -d> iPropO Σ) :
  ⊢ ((□ ∀ P, mupd1 P -∗ mupd2 P) →
     ∀ P, mupd_pre n Θ mupd1 P -∗ mupd_pre n Θ mupd2 P)%I.
Proof.
  iIntros "#Hmono"; iIntros (P) "Hmupd". rewrite /mupd_pre.
  iDestruct "Hmupd" as "[H | Hmupd]".
  { iLeft. done. }
  iRight. iIntros (????) "I". iMod ("Hmupd" with "[$I]") as "(%& %& H)".
  iModIntro. iExists _. iSplitR; first done. iIntros (??).
  iMod ("H" with "[//]") as "[$ H]". by iApply "Hmono".
Qed.

Local Instance mupd_pre_mono' `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class} n Θ :
  BiMonoPred (mupd_pre n Θ).
Proof.
  constructor.
  - iIntros (mupd1 mupd2 NE1 NE2) "#H". iApply mupd_pre_mono. iModIntro. iApply "H".
  - intros mupd Hmupd ? P1 P2 ?. rewrite /mupd_pre.
    do 21 (f_equiv || done).
Qed.

(* take the least fixpoint of the above definition *)
Local Definition mupd_def `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class} n Θ : iProp Σ → iProp Σ :=
  λ P, ((bi_least_fixpoint (mupd_pre n Θ)) P)%I.
Local Definition mupd_aux : seal (@mupd_def). by eexists. Qed.
Definition mupd := mupd_aux.(unseal).
Arguments mupd {SI Σ _ _}.
Local Definition mupd_unseal : @mupd = @mupd_def := mupd_aux.(seal_eq).
Notation "'|=[' n , Θ ']=>m' P" := (mupd n Θ P) (at level 99, P at level 200, format "|=[ n , Θ ]=>m  P").

Section mupd.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.
  Implicit Type Θ : (gset positive).

  Lemma mupd_unfold n Θ P :
    (|=[n,Θ]=>m P) ⊣⊢ (mupd_pre n Θ (mupd n Θ) P).
  Proof.
    rewrite mupd_unseal. rewrite /mupd_def.
    rewrite (least_fixpoint_unfold (mupd_pre n Θ)). done.
  Qed.

  Global Instance mupd_ne n Θ :
    NonExpansive (mupd n Θ).
  Proof. intros ? P1 P2 HP. rewrite !mupd_unseal /mupd_def. f_equiv. done. Qed.
  Global Instance mupd_proper n Θ :
    Proper ((≡) ==> (≡)) (mupd n Θ).
  Proof. intros P P' ?. apply equiv_dist=>?. apply mupd_ne. apply equiv_dist. done. Qed.

  Lemma mupd_ind_strong (Ψ : iProp Σ → iProp Σ) n Θ :
    (∀ i, Proper (dist i ==> dist i) Ψ) →
    ⊢ (□ (∀ P, mupd_pre n Θ (λ P, Ψ P ∧ |=[n,Θ]=>m P) P -∗ Ψ P)
       → ∀ P, (|=[n,Θ]=>m P) -∗ Ψ P)%I.
  Proof.
    iIntros (HΨ). iIntros "#IH" (P) "H". rewrite mupd_unseal.
    iApply (least_fixpoint_ind _ Ψ with "[] H").
    iIntros "!#" (?) "H". iApply "IH".
    iApply (bi_mono_pred with "[] H").
    { repeat intro. do 3 (f_equiv || done). }
    { repeat intro. rewrite -!mupd_unseal. f_equiv; f_equiv; done. }
    iIntros "!>" (?) "H". iSplit.
    - iDestruct "H" as "[H _]". done.
    - iDestruct "H" as "[_ H]". done.
  Qed.

  Lemma mupd_ind n Θ Ψ :
    (∀ i, Proper (dist i ==> dist i) Ψ)
    → ⊢ (□ (∀ P, mupd_pre n Θ (λ P, Ψ P) P -∗ Ψ P)
         → ∀ P, (|=[n,Θ]=>m P) -∗ Ψ P)%I.
  Proof.
    iIntros (HΨ) "#H". iApply mupd_ind_strong. iIntros "!>" (P) "Hmupd".
    iApply "H". iApply (mupd_pre_mono with "[] Hmupd").
    iIntros "!>" (?) "[$ _]".
  Qed.

  (** An empty fancy update can be turned into an obl update. *)
  Lemma fupd_mupd n Θ P : (|={∅}=> P) ⊢ (|=[n,Θ]=>m P).
  Proof. rewrite mupd_unfold. iIntros "Hupd". iLeft. done. Qed.

  (** We can always introduce a obl update. *)
  Lemma mupd_intro n Θ P : P ⊢ |=[n,Θ]=>m P.
  Proof. rewrite mupd_unfold. iIntros "HP". iLeft. iModIntro. done. Qed.

  (** We can always eliminate an empty fancy update. *)
  Lemma fupd_mupd_elim n Θ P :
    (|={∅}=> |=[n,Θ]=>m P) ⊢ |=[n,Θ]=>m P.
  Proof.
    iIntros "H". iApply mupd_unfold.
    iRight. iIntros (????) "I". iMod "H".
    iModIntro. iExists Ω1. iSplitR; first (iPureIntro; apply obls_lef_refl).
    iIntros (? (Prog& OW2)).
    rewrite /model_interp. iDestruct "I" as "(HI& $& $& $& $& N& %OW1)".
    iMod (model_history_interp_step with "HI") as "$". 1,2: done.
    iModIntro. pose proof (wits_lef_same_wits_mon _ _ _ OW1 Prog OW2).
    iPoseProof (owit_mon _ _ H with "N") as "$". iFrame. done.
  Qed.

  (** We can combine two obl updates into one. *)
  Lemma mupd_bind n Θ P Q :
    (P -∗ |=[n,Θ]=>m Q) ⊢ (|=[n,Θ]=>m P) -∗ (|=[n,Θ]=>m Q).
  Proof.
    iIntros "H HP". iRevert (Q) "H". iRevert (P) "HP".
    iApply mupd_ind_strong.
    { solve_proper. }
    iIntros "!> %P IH %Q H". iDestruct "IH" as "[IH | IH]".
    - iApply fupd_mupd_elim. iMod "IH". iModIntro. iApply ("H" with "IH").
    - iApply mupd_unfold. iRight. iIntros (????) "I".
      iMod ("IH" with "I") as "(%&%& IH)".
      iModIntro. iExists _. iSplitR; first done.
      iIntros (??). iMod ("IH" with "[//]") as "[$ IH]".
      iModIntro. iDestruct "IH" as "[IH _]".
      iApply "IH". done.
  Qed.

  (* derived lemmas *)
  Lemma mupd_mono n Θ P Q : (P ⊢ Q) → (|=[n,Θ]=>m P) ⊢ (|=[n,Θ]=>m Q).
  Proof.
    intros Hent. iApply mupd_bind.
    iIntros "P"; iApply mupd_intro; by iApply Hent.
  Qed.
  Lemma mupd_trans n Θ P :  (|=[n,Θ]=>m |=[n,Θ]=>m P) ⊢ |=[n,Θ]=>m P.
  Proof.
    iIntros "HP". iApply mupd_bind; eauto.
  Qed.
  Lemma mupd_frame_r n Θ P R : (|=[n,Θ]=>m P) ∗ R ⊢ |=[n,Θ]=>m P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (mupd_bind with "[R]"); last done.
    iIntros "P". iApply mupd_intro. by iFrame.
  Qed.

  Global Instance mupd_ent_proper n Θ : Proper ((⊢) ==> (⊢)) (mupd n Θ).
  Proof. intros P Q PQ. by apply mupd_mono. Qed.
  Global Instance mupd_flip_ent_proper n Θ : Proper (flip (⊢) ==> flip (⊢)) (mupd n Θ).
  Proof. intros P Q PQ; by apply mupd_mono. Qed.
  Global Instance mupd_equiv_proper n Θ : Proper ((≡) ==> (≡)) (mupd n Θ) := ne_proper _.

  Lemma mupd_fupd_l n Θ P :
    (|={∅}=> |=[n,Θ]=>m P) ⊢ (|=[n,Θ]=>m P).
  Proof.
    by erewrite fupd_mupd, mupd_trans.
  Qed.
  Lemma mupd_fupd_r n Θ P :
    (|=[n,Θ]=>m |={∅}=> P) ⊢ (|=[n,Θ]=>m P).
  Proof.
    by erewrite fupd_mupd, mupd_trans.
  Qed.

  Lemma mupd_frame_l n Θ R Q : (R ∗ |=[n,Θ]=>m Q) ⊢ |=[n,Θ]=>m R ∗ Q.
  Proof. rewrite !(comm _ R); apply mupd_frame_r. Qed.
  Lemma mupd_wand_l n Θ P Q : (P -∗ Q) ∗ (|=[n,Θ]=>m P) ⊢ |=[n,Θ]=>m Q.
  Proof. by rewrite mupd_frame_l wand_elim_l. Qed.
  Lemma mupd_wand_r n Θ P Q : (|=[n,Θ]=>m P) ∗ (P -∗ Q) ⊢ |=[n,Θ]=>m Q.
  Proof. by rewrite mupd_frame_r wand_elim_r. Qed.
  Lemma mupd_sep n Θ P Q : (|=[n,Θ]=>m P) ∗ (|=[n,Θ]=>m Q) ⊢ |=[n,Θ]=>m P ∗ Q.
  Proof. by rewrite mupd_frame_r mupd_frame_l mupd_trans. Qed.
  Lemma mupd_idemp n Θ P : (|=[n,Θ]=>m |=[n,Θ]=>m P) ⊣⊢ |=[n,Θ]=>m P.
  Proof.
    apply: anti_symm.
    - apply mupd_trans.
    - apply mupd_intro.
  Qed.

  Global Instance mupd_homomorphism n Θ :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (mupd n Θ).
  Proof. split; [split|]; try apply _; [apply mupd_sep | apply mupd_intro]. Qed.

  Lemma big_sepL_mupd {A} (Φ : nat → A → iProp Σ) n Θ l :
    ([∗ list] k↦x ∈ l, |=[n,Θ]=>m Φ k x) ⊢ |=[n,Θ]=>m [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_mupd {A} `{Countable K} (Φ : K → A → iProp Σ) n Θ l :
    ([∗ map] k↦x ∈ l, |=[n,Θ]=>m Φ k x) ⊢ |=[n,Θ]=>m [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_mupd `{Countable A} (Φ : A → iProp Σ) n Θ l :
    ([∗ set]  x ∈ l, |=[n,Θ]=>m Φ x) ⊢ |=[n,Θ]=>m [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_mupd `{Countable A} (Φ : A → iProp Σ) n Θ l :
    ([∗ mset] x ∈ l, |=[n,Θ]=>m Φ x) ⊢ |=[n,Θ]=>m [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_mupd n Θ P : ◇ (|=[n,Θ]=>m P) ⊢ (|=[n,Θ]=>m ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using mupd_mono, or_intro_r.
    by rewrite -mupd_intro -or_intro_l.
  Qed.

  Lemma model_interp_owit_inv h i Ω W n Θ :
    model_interp h i Ω W n Θ ⊢ ⌜ owit_inv Ω W ⌝.
  Proof. iIntros "(_&_&_&_&_&_&$)". Qed.

  Definition owit_inv_lb (γ : obl_owner → obl_fuel → obl_fuel) (Ω : obls) (W : witnesses) : Prop :=
    map_Forall2
      (λ (_ : oid) (g : obl) (w : witness),
         match g with
         | obl_assigned a i => match w with
                              | witness_assigned b => (γ i a) w≤ b
                              | witness_discharged => False
                              end
         | obl_discharged => match w with
                           | witness_assigned _ => False
                           | witness_discharged => True
                           end
         end)
      Ω W.

  Definition owit_inv_lb_mon (γ : obl_owner → obl_fuel → obl_fuel) : Prop :=
    (∀ a b i j, (a w< b) → (γ i a w< γ j b)) ∧ (∀ i a, γ i a w≤ η a).

  (** Choosing a map pointwise. *)
  Lemma map_Forall2_choice {A B : Type} (Ω2 : gmap oid A) (P : oid → A → B → Prop) :
    (∀ k a, Ω2 !! k = Some a → ∃ b, P k a b) → ∃ W2 : gmap oid B, map_Forall2 P Ω2 W2.
  Proof.
    induction Ω2 as [|k a Ω2 Hk IH] using map_ind; intros HP.
    { exists ∅. intros i. rewrite !lookup_empty. constructor. }
    destruct IH as [W2 HW2].
    { intros i b Hi. apply HP. rewrite lookup_insert_ne; first done. intros ->. by rewrite Hk in Hi. }
    destruct (HP k a) as [b Hb]; first by rewrite lookup_insert_eq.
    exists (<[k:=b]> W2). intros i. destruct (decide (i = k)) as [->|Hne].
    - rewrite !lookup_insert_eq. by constructor.
    - rewrite !lookup_insert_ne; auto.
  Qed.

  (** The witness chosen for an obligation that changed. *)
  Definition wit_of (γ : obl_owner → obl_fuel → obl_fuel) (g : obl (OC:=ord_obl_class)) :
    witness (OC:=ord_obl_class) :=
    match g with
    | obl_assigned a i => witness_assigned (γ i a)
    | obl_discharged => witness_discharged
    end.

  Lemma owit_inv_exists_witnesses γ Ω1 Ω2 W1 :
    owit_inv_lb_mon γ →
    obls_lef Ω1 Ω2 →
    owit_inv Ω1 W1 →
    owit_inv_lb γ Ω1 W1 →
    ∃ W2, wits_lef W1 W2 ∧ owit_inv Ω2 W2 ∧ owit_inv_lb γ Ω2 W2.
  Proof.
    intros [GMon GSched] Step Inv LB.
    destruct (map_Forall2_choice Ω2
      (λ k g2 w2,
         (match (g2 : obl (OC:=ord_obl_class)), (w2 : witness (OC:=ord_obl_class)) with
          | obl_assigned a _, witness_assigned b => b w≤ η a
          | obl_discharged, witness_discharged => True
          | _, _ => False
          end) ∧
         (match (g2 : obl (OC:=ord_obl_class)) with
          | obl_assigned a i => match (w2 : witness (OC:=ord_obl_class)) with
                               | witness_assigned b => γ i a w≤ b
                               | witness_discharged => False
                               end
          | obl_discharged => match (w2 : witness (OC:=ord_obl_class)) with
                             | witness_assigned _ => False
                             | witness_discharged => True
                             end
          end) ∧
         (∀ w1, W1 !! k = Some w1 → wit_le w1 w2))) as [W2 HW2].
    { intros k g2 Hg2. destruct (Classical_Prop.classic (Ω1 !! k = Some g2)) as [Hsame|Hdiff].
      - pose proof (Inv k) as Ik. pose proof (LB k) as Lk. rewrite Hsame in Ik, Lk.
        destruct (W1 !! k) as [w1|] eqn:Hw1; inversion Ik as [? ? Hm|]; subst.
        inversion Lk as [? ? Hl|]; subst.
        exists w1. split_and!; [done|done|]. intros w1' [=<-].
        destruct g2, w1; simpl in *; try done; reflexivity.
      - exists (wit_of γ g2). split_and!.
        + destruct g2; simpl; [apply GSched|done].
        + destruct g2; simpl; [reflexivity|done].
        + intros w1 Hw1. pose proof (Inv k) as Ik. rewrite Hw1 in Ik.
          destruct (Ω1 !! k) as [g1|] eqn:Hg1; inversion Ik as [? ? Hm|]; subst.
          destruct (Step k g1 Hg1) as (g2'& Hg2'& Hrel). rewrite Hg2 in Hg2'.
          injection Hg2' as <-. destruct Hrel as [->|Hs]; first done.
          pose proof (LB k) as Lk. rewrite Hg1 Hw1 in Lk. inversion Lk as [? ? Hl|]; subst.
          inversion Hs as [? ? Hp| ? ? Hd]; subst.
          * inversion Hp; subst. destruct w1; simpl in *; try done.
            apply WFOCM.lt_le. eapply WFOCM.lt_le_lt; last done. by apply GMon.
          * inversion Hd; subst. destruct w1; simpl in *; done. }
    exists W2. split_and!.
    - intros k w1 Hw1. pose proof (Inv k) as Ik. rewrite Hw1 in Ik.
      destruct (Ω1 !! k) as [g1|] eqn:Hg1; inversion Ik; subst.
      destruct (Step k g1 Hg1) as (g2& Hg2& _).
      pose proof (HW2 k) as Hk. rewrite Hg2 in Hk.
      destruct (W2 !! k) as [w2|] eqn:Hw2; inversion Hk as [? ? (_& _& Hle)|]; subst.
      exists w2. split; first done. by apply Hle.
    - eapply map_Forall2_impl; first done. by intros ??? (?&_&_).
    - eapply map_Forall2_impl; first done. by intros ??? (_&?&_).
  Qed.

  Lemma model_interp_mupd_steps (γ : obl_owner → obl_fuel → obl_fuel) h i Ω W n Θ P :
    owit_inv_lb_mon γ →
    (owit_inv_lb γ Ω W) →
    (|=[n,Θ]=>m P) -∗ model_interp h i Ω W n Θ ={∅}=∗
    (P ∗ ∃ h' i' Ω' W', ⌜ obls_le Ω Ω' ∧ owit_inv_lb γ Ω' W' ⌝ ∗ model_interp (h ++ h') (i + i') Ω' W' n Θ).
  Proof.
    iIntros ([GMon GSched] LB) "H". iRevert (h i Ω W LB). iRevert (P) "H".
    iApply mupd_ind_strong.
    { solve_proper. }
    iIntros "!> %P IH %%%% %LB H". iDestruct "IH" as "[IH | IH]".
    { iMod "IH". iModIntro. iFrame. iExists [], 0, _, _. rewrite app_nil_r Nat.add_0_r. iFrame. done. }
    iPoseProof (model_interp_owit_inv with "H") as "%".
    iMod ("IH" with "H") as "(%&%& IH)".
    unshelve epose proof (owit_inv_exists_witnesses γ _ _ _ _ H0 H LB).
    1: split; auto.
    destruct H1 as (W2& WProg& Inv2& LB2).
    iMod ("IH" $! W2 with "[//]") as "[G [IH _]]". iMod ("IH" with "[] G") as "[$ (%&%&%&%& %LEO& MI)]".
    1: eauto.
    iModIntro. iExists ([(n, Ω2)] ++ h'), (S i'), _, _.
    replace (h ++ [(n, Ω2)] ++ h') with ((h ++ [(n, Ω2)]) ++ h'); cycle 1.
    { by rewrite app_assoc. }
    replace (i + S i') with (S i + i') by lia. iFrame.
    iPureIntro. destruct LEO as [LEO ?]. split; auto.
    etrans; last eapply LEO. apply obls_lef_obls_le; auto.
  Qed.

  (* The following instances make the Iris Proof Mode aware of the
     obl update. They are derived from the simpler rules above. *)
  (* Global Instance elim_fupd_mupd (p : bool) n Θ P Q : *)
  (*   ElimModal True p false (|={∅}=> P) P (|=[n,Θ]=>m Q) (|=[n,Θ]=>m Q)%I. *)
  (* Proof. *)
  (*   rewrite /ElimModal bi.intuitionistically_if_elim //=. *)
  (*   rewrite fupd_mupd. *)
  (*   iIntros "_ [HP HPQ]". iApply (mupd_bind with "HPQ HP"). *)
  (* Qed. *)

  Global Instance elim_fupd_mupd (p : bool) E n Θ P Q :
    ElimModal True p false (|={∅,E}=> P) P (|=[n,Θ]=>m Q) (|={E,∅}=> |=[n,Θ]=>m Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_mupd_elim. iMod "HP".
    by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_mupd n Θ P Q :
    AddModal (|={∅}=> P) P (|=[n,Θ]=>m Q).
  Proof.
    rewrite /AddModal; rewrite fupd_mupd; iIntros "[HP HPQ]".
    iApply (mupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_mupd p n Θ P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|=[n,Θ]=>m Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply mupd_intro. Qed.

  Global Instance from_pure_mupd a n Θ P φ :
    FromPure a P φ → FromPure a (|=[n,Θ]=>m P) φ.
  Proof. rewrite /FromPure=> <-. apply mupd_intro. Qed.

  Global Instance into_wand_mupd p q n Θ R P Q :
    IntoWand false false R P Q → IntoWand p q (|=[n,Θ]=>m R) (|=[n,Θ]=>m P) (|=[n,Θ]=>m Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite mupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_mupd_persistent p q n Θ R P Q :
    IntoWand false q R P Q → IntoWand p q (|=[n,Θ]=>m R) P (|=[n,Θ]=>m Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite mupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_mupd_args p q n Θ R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|=[n,Θ]=>m P) (|=[n,Θ]=>m Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim mupd_wand_r.
  Qed.

  Global Instance from_sep_mupd n Θ P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|=[n,Θ]=>m P) (|=[n,Θ]=>m Q1) (|=[n,Θ]=>m Q2).
  Proof. rewrite /FromSep=><-. apply mupd_sep. Qed.

  Global Instance from_or_mupd n Θ P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|=[n,Θ]=>m P) (|=[n,Θ]=>m Q1) (|=[n,Θ]=>m Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply mupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_mupd {A} n Θ P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|=[n,Θ]=>m P) (λ a, |=[n,Θ]=>m Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_mupd n Θ P : IsExcept0 P → IsExcept0 (|=[n,Θ]=>m P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_mupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_mupd n Θ P :
    FromModal True modality_id (|=[n,Θ]=>m P) (|=[n,Θ]=>m P) P.
  Proof. by rewrite /FromModal /= -mupd_intro. Qed.

  Global Instance elim_modal_mupd p n Θ P Q :
    ElimModal True p false (|=[n,Θ]=>m P) P (|=[n,Θ]=>m Q) (|=[n,Θ]=>m Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim mupd_frame_r wand_elim_r mupd_trans.
  Qed.

  Global Instance add_modal_mupd n Θ P Q : AddModal (|=[n,Θ]=>m P) P (|=[n,Θ]=>m Q).
  Proof. by rewrite /AddModal mupd_frame_r wand_elim_r mupd_trans. Qed.

  Global Instance frame_mupd p n Θ R P Q :
    Frame p R P Q → Frame p R (|=[n,Θ]=>m P) (|=[n,Θ]=>m Q).
  Proof. rewrite /Frame=><-. by rewrite mupd_frame_l. Qed.

  (** ** Non-discharging rounds

      A model update may take a non-discharging round of the obligations ([obls_ndf Ω1 Ω2]:
      every obligation stays or makes progress, possibly changing owner, and new ones may
      appear), along which the witnesses do not increase ([wits_ndf]). The obligation rules
      (opreds.v) are proved through [mupd_nd_step]. *)
  Lemma mupd_nd_step n Θ P :
    (∀ h i Ω1 W1,
       model_interp h i Ω1 W1 n Θ ={∅}=∗
       ∃ Ω2, ⌜ obls_ndf Ω1 Ω2 ⌝ ∗
             ∀ W2, ⌜ wits_ndf W1 W2 ∧ owit_inv Ω2 W2 ⌝ ={∅}=∗
                   model_interp (h ++ [(n, Ω2)]) (S i) Ω2 W2 n Θ ∗ |=[n,Θ]=>m P)
    ⊢ |=[n,Θ]=>m P.
  Proof.
    iIntros "IH". iApply mupd_unfold. iRight. iIntros (????) "I".
    iPoseProof (model_interp_owit_inv with "I") as "%Hinv".
    iMod ("IH" with "I") as "(%Ω2& %Hndf& IH)".
    iModIntro. iExists _. iSplit.
    { iPureIntro. by apply obls_ndf_obls_lef. }
    iIntros (W2 [WS OI2]).
    by iMod ("IH" with "[%]") as "[$ $]"; first (split; [by eapply wits_lef_wits_ndf|done]).
  Qed.

End mupd.

(* Wrapper to use fupd. *)
Definition fmupd `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class} E1 E2 n Θ : iPropO Σ -d> iPropO Σ :=
  (λ P, |={E1,∅}=> |=[n,Θ]=>m |={∅,E2}=> P)%I.
Notation "'|={' E1 , E2 : n , Θ '}=>m' P" := (fmupd E1 E2 n Θ P) (at level 20, P at level 200, format "|={ E1 , E2 : n , Θ }=>m  P").
Notation "'|={' E : n , Θ '}=>m' P" := (fmupd E E n Θ P) (at level 20, P at level 200, format "|={ E : n , Θ }=>m  P").

Section fmupd.
  Context `{SI : sidx} `{!mupdGS Σ} `{!ord_mono_fun_class}.
  Implicit Type Θ : (gset positive).

  Global Instance fmupd_ne E1 E2 n Θ : NonExpansive (fmupd E1 E2 n Θ).
  Proof. intros ? P1 P2 HP. rewrite /fmupd. do 12 (f_equiv || done). Qed.
  Global Instance fmupd_proper E1 E2 n Θ : Proper ((≡) ==> (≡)) (fmupd E1 E2 n Θ).
  Proof. intros P P' ?. apply equiv_dist=>?. apply fmupd_ne. apply equiv_dist. done. Qed.

  Lemma fupd_fmupd E1 E2 n Θ P : (|={E1,E2}=> P) ⊢ (|={E1,E2:n,Θ}=>m P).
  Proof.
    rewrite /fmupd. iIntros ">Hupd".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose !>". iMod "Hclose" as "_".
    iModIntro. iFrame.
  Qed.

  Lemma mupd_fmupd E n Θ P : (|=[n,Θ]=>m P) ⊢ (|={E:n,Θ}=>m P).
  Proof.
    rewrite /fmupd. iIntros "Hupd".
    iApply fupd_mask_intro. 1: set_solver.
    iIntros "Hclose". iMod "Hupd".
    iModIntro. iMod "Hclose". by iFrame.
  Qed.

  Lemma fmupd_intro E n Θ P : P ⊢ |={E:n,Θ}=>m P.
  Proof.
    iIntros "$". iMod (fupd_mask_subseteq ∅) as "Hclose". 1: set_solver.
    iIntros "!> !>". iMod "Hclose". done.
  Qed.

  Lemma fupd_fmupd_elim E1 E2 n Θ P :
    (|={E1}=> |={E1,E2:n,Θ}=>m P) ⊢ |={E1,E2:n,Θ}=>m P.
  Proof.
    iIntros "H". iMod "H". iApply "H".
  Qed.

  Lemma fupd_fmupd_elim_2 E1 E2 n Θ P :
    (|={E1,E2:n,Θ}=>m |={E2}=> P) ⊢ |={E1,E2:n,Θ}=>m P.
  Proof.
    iIntros "H". iMod "H". iModIntro. iMod "H" as ">H".
    iMod "H" as "$". iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    iModIntro. by iMod "close".
  Qed.

  Lemma mupd_fmupd_elim E1 E2 n Θ P :
    (|=[n,Θ]=>m |={E1,E2:n,Θ}=>m P) ⊢ |={E1,E2:n,Θ}=>m P.
  Proof.
    iIntros "H". iApply fupd_mask_intro. 1: set_solver.
    iIntros "Fupd". iMod "H". iMod "Fupd" as "_". done.
  Qed.

  (** Change to a larger mask. *)
  Lemma fmupd_mask_mono E1 E2 n Θ P :
    E1 ⊆ E2 →
    (|={E1:n,Θ}=>m P) ⊢ |={E2:n,Θ}=>m P.
  Proof.
    iIntros (Sub) "H".
    iMod (fupd_mask_subseteq E1) as "close". 1: done.
    iMod "H". iModIntro. iMod "H" as "H".
    iModIntro. iMod "H" as "$". eauto.
  Qed.

  (** We can combine two obl updates into one. *)
  Lemma fmupd_bind E1 E2 E3 n Θ P Q :
    (P -∗ |={E2,E3:n,Θ}=>m Q) ⊢ (|={E1,E2:n,Θ}=>m P) -∗ (|={E1,E3:n,Θ}=>m Q).
  Proof.
    iIntros "H >HP".
    iModIntro. iMod "HP" as ">HP".
    iPoseProof ("H" with "HP") as "H". done.
  Qed.

  (* derived lemmas *)
  Lemma fmupd_mono E1 E2 n Θ P Q : (P ⊢ Q) → (|={E1,E2:n,Θ}=>m P) ⊢ (|={E1,E2:n,Θ}=>m Q).
  Proof.
    intros Hent. iApply fmupd_bind.
    iIntros "P"; iApply fmupd_intro; by iApply Hent.
  Qed.
  Lemma fmupd_trans E1 E2 E3 n Θ P :  (|={E1,E3:n,Θ}=>m |={E3,E2:n,Θ}=>m P) ⊢ |={E1,E2:n,Θ}=>m P.
  Proof.
    iIntros "HP". iApply fmupd_bind; eauto.
  Qed.
  Lemma fmupd_frame_r E1 E2 n Θ P R : (|={E1,E2:n,Θ}=>m P) ∗ R ⊢ |={E1,E2:n,Θ}=>m P ∗ R.
  Proof.
    iIntros "[Hupd R]". iApply (fmupd_bind with "[R]"); last done.
    iIntros "P". iApply fmupd_intro. by iFrame.
  Qed.

  Global Instance fmupd_ent_proper E1 E2 n Θ : Proper ((⊢) ==> (⊢)) (fmupd E1 E2 n Θ).
  Proof. intros P Q PQ. by apply fmupd_mono. Qed.
  Global Instance fmupd_flip_ent_proper E1 E2 n Θ : Proper (flip (⊢) ==> flip (⊢)) (fmupd E1 E2 n Θ).
  Proof. intros P Q PQ; by apply fmupd_mono. Qed.
  Global Instance fmupd_equiv_proper E1 E2 n Θ : Proper ((≡) ==> (≡)) (fmupd E1 E2 n Θ) := ne_proper _.

  Lemma fmupd_fupd_l E1 E2 n Θ P :
    (|={E1,E2}=> |={E2:n,Θ}=>m P) ⊢ (|={E1,E2:n,Θ}=>m P).
  Proof.
    by erewrite fupd_fmupd, fmupd_trans.
  Qed.
  Lemma fmupd_fupd_r E1 E2 n Θ P :
    (|={E1:n,Θ}=>m |={E1,E2}=> P) ⊢ (|={E1,E2:n,Θ}=>m P).
  Proof.
    by erewrite fupd_fmupd, fmupd_trans.
  Qed.

  Lemma fmupd_frame_l E1 E2 n Θ R Q : (R ∗ |={E1,E2:n,Θ}=>m Q) ⊢ |={E1,E2:n,Θ}=>m R ∗ Q.
  Proof. rewrite !(comm _ R); apply fmupd_frame_r. Qed.
  Lemma fmupd_wand_l E1 E2 n Θ P Q : (P -∗ Q) ∗ (|={E1,E2:n,Θ}=>m P) ⊢ |={E1,E2:n,Θ}=>m Q.
  Proof. by rewrite fmupd_frame_l wand_elim_l. Qed.
  Lemma fmupd_wand_r E1 E2 n Θ P Q : (|={E1,E2:n,Θ}=>m P) ∗ (P -∗ Q) ⊢ |={E1,E2:n,Θ}=>m Q.
  Proof. by rewrite fmupd_frame_r wand_elim_r. Qed.
  Lemma fmupd_sep E n Θ P Q : (|={E:n,Θ}=>m P) ∗ (|={E:n,Θ}=>m Q) ⊢ |={E:n,Θ}=>m P ∗ Q.
  Proof. by rewrite fmupd_frame_r fmupd_frame_l fmupd_trans. Qed.
  Lemma fmupd_sep_l E1 E2 E3 n Θ P Q : (|={E1,E3:n,Θ}=>m P) ∗ (|={E3,E2:n,Θ}=>m Q) ⊢ |={E1,E2:n,Θ}=>m P ∗ Q.
  Proof. rewrite fmupd_frame_r fmupd_frame_l. apply fmupd_trans. Qed.
  Lemma fmupd_sep_r E1 E2 E3 n Θ P Q : (|={E3,E2:n,Θ}=>m P) ∗ (|={E1,E3:n,Θ}=>m Q) ⊢ |={E1,E2:n,Θ}=>m P ∗ Q.
  Proof. rewrite bi.sep_comm. rewrite fmupd_frame_r fmupd_frame_l bi.sep_comm. apply fmupd_trans. Qed.
  Lemma fmupd_idemp E n Θ P : (|={E:n,Θ}=>m |={E:n,Θ}=>m P) ⊣⊢ |={E:n,Θ}=>m P.
  Proof.
    apply: anti_symm.
    - apply fmupd_trans.
    - apply fmupd_intro.
  Qed.

  Global Instance fmupd_homomorphism E n Θ :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (fmupd E E n Θ).
  Proof. split; [split|]; try apply _; [apply fmupd_sep | apply fmupd_intro]. Qed.

  Lemma big_sepL_fmupd {A} (Φ : nat → A → iProp Σ) E n Θ l :
    ([∗ list] k↦x ∈ l, |={E:n,Θ}=>m Φ k x) ⊢ |={E:n,Θ}=>m [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_fmupd {A} `{Countable K} (Φ : K → A → iProp Σ) E n Θ l :
    ([∗ map] k↦x ∈ l, |={E:n,Θ}=>m Φ k x) ⊢ |={E:n,Θ}=>m [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_fmupd `{Countable A} (Φ : A → iProp Σ) E n Θ l :
    ([∗ set]  x ∈ l, |={E:n,Θ}=>m Φ x) ⊢ |={E:n,Θ}=>m [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_fmupd `{Countable A} (Φ : A → iProp Σ) E n Θ l :
    ([∗ mset] x ∈ l, |={E:n,Θ}=>m Φ x) ⊢ |={E:n,Θ}=>m [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_fmupd E1 E2 n Θ P : ◇ (|={E1,E2:n,Θ}=>m P) ⊢ (|={E1,E2:n,Θ}=>m ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using fmupd_mono, or_intro_r.
    rewrite -fupd_fmupd. iIntros "H". iApply except_0_fupd. iMod "H". done.
  Qed.

  Global Instance elim_fupd_fmupd (p : bool) E1 E2 E3 n Θ P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3:n,Θ}=>m Q) (|={E2,E3:n,Θ}=>m Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fmupd_trans.
    iApply fupd_fmupd. iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance elim_mupd_fmupd (p : bool) E1 E2 n Θ P Q :
    ElimModal True p false (|=[n,Θ]=>m P) P (|={E1,E2:n,Θ}=>m Q) (|={E1,E2:n,Θ}=>m Q)%I.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply mupd_fmupd_elim.
    iMod "HP". by iApply "HPQ".
  Qed.

  Global Instance add_modal_fupd_fmupd E1 E2 n Θ P Q :
    AddModal (|={E1}=> P) P (|={E1,E2:n,Θ}=>m Q).
  Proof.
    rewrite /AddModal; rewrite fupd_fmupd; iIntros "[HP HPQ]".
    iApply (fmupd_bind with "HPQ HP").
  Qed.

  Global Instance add_modal_mupd_fmupd E1 E2 n Θ P Q :
    AddModal (|=[n,Θ]=>m P) P (|={E1,E2:n,Θ}=>m Q).
  Proof.
    rewrite /AddModal; rewrite mupd_fmupd; iIntros "[HP HPQ]".
    iApply (fmupd_bind with "HPQ HP").
  Qed.

  Global Instance from_assumption_fmupd p E n Θ P Q :
    FromAssumption p P Q → KnownRFromAssumption p P (|={E:n,Θ}=>m Q).
  Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply fmupd_intro. Qed.

  Global Instance from_pure_fmupd a E n Θ P φ :
    FromPure a P φ → FromPure a (|={E:n,Θ}=>m P) φ.
  Proof. rewrite /FromPure=> <-. apply fmupd_intro. Qed.

  Global Instance into_wand_fmupd p q E n Θ R P Q :
    IntoWand false false R P Q → IntoWand p q (|={E:n,Θ}=>m R) (|={E:n,Θ}=>m P) (|={E:n,Θ}=>m Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite fmupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_fmupd_persistent p q E1 E2 n Θ R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E1,E2:n,Θ}=>m R) P (|={E1,E2:n,Θ}=>m Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
    apply wand_intro_l. by rewrite fmupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_fmupd_args p q E1 E2 n Θ R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E1,E2:n,Θ}=>m P) (|={E1,E2:n,Θ}=>m Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite intuitionistically_if_elim fmupd_wand_r.
  Qed.

  Global Instance from_sep_fmupd E n Θ P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E:n,Θ}=>m P) (|={E:n,Θ}=>m Q1) (|={E:n,Θ}=>m Q2).
  Proof. rewrite /FromSep=><-. apply fmupd_sep. Qed.

  Global Instance from_or_fmupd E1 E2 n Θ P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E1,E2:n,Θ}=>m P) (|={E1,E2:n,Θ}=>m Q1) (|={E1,E2:n,Θ}=>m Q2).
  Proof.
    rewrite /FromOr=><-.
    apply or_elim; apply fmupd_mono; auto using or_intro_l, or_intro_r.
  Qed.

  Global Instance from_exist_fmupd {A} E1 E2 n Θ P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E1,E2:n,Θ}=>m P) (λ a, |={E1,E2:n,Θ}=>m Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance is_except_0_fmupd E1 E2 n Θ P : IsExcept0 P → IsExcept0 (|={E1,E2:n,Θ}=>m P).
  Proof.
    rewrite /IsExcept0=> HP.
    by rewrite -{2}HP -(except_0_idemp P) -except_0_fmupd -(except_0_intro P).
  Qed.

  Global Instance from_modal_fmupd E n Θ P :
    FromModal True modality_id (|={E:n,Θ}=>m P) (|={E:n,Θ}=>m P) P.
  Proof. by rewrite /FromModal /= -fmupd_intro. Qed.

  Global Instance elim_modal_fmupd p E1 E2 E3 n Θ P Q :
    ElimModal True p false (|={E1,E2:n,Θ}=>m P) P (|={E1,E3:n,Θ}=>m Q) (|={E2,E3:n,Θ}=>m Q).
  Proof.
    by rewrite /ElimModal
      intuitionistically_if_elim fmupd_frame_r wand_elim_r fmupd_trans.
  Qed.

  Global Instance add_modal_fmupd E1 E2 n Θ P Q : AddModal (|={E1:n,Θ}=>m P) P (|={E1,E2:n,Θ}=>m Q).
  Proof. by rewrite /AddModal fmupd_frame_r wand_elim_r fmupd_trans. Qed.

  Global Instance frame_fmupd p E1 E2 n Θ R P Q :
    Frame p R P Q → Frame p R (|={E1,E2:n,Θ}=>m P) (|={E1,E2:n,Θ}=>m Q).
  Proof. rewrite /Frame=><-. by rewrite fmupd_frame_l. Qed.

End fmupd.

(* Allocation of model_interp. *)
Lemma model_interp_alloc `{SI : sidx} `{!ord_mono_fun_class} `{!mupdGpreS Σ}
  (n : nat) :
  ⊢ |==> ∃ _ : mupdGS Σ, (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗
                      wsat.wsat ∗ wsat.ownE ⊤ ∗
                      model_interp [(n, ∅)] 0 ∅ ∅ n ∅.
Proof.
  iIntros. rewrite /model_interp. rewrite dom_empty_L.
  iMod invGS_alloc as "(%HInv& R& W& O)".
  iMod (model_history_interp_init n ∅) as "(%HHist& MHI)".
  iMod (osat_alloc) as "(%HS& S)".
  iMod (othread_alloc) as "(%HT& T& A)".
  iMod (oforest_alloc) as "(%HG& G)".
  iMod (owit_alloc) as "(%HW& Wit)".
  iExists (MupdG HInv HS HT HG HW HHist). iFrame.
  iPureIntro. apply map_Forall2_empty.
Qed.
