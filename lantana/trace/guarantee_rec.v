From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export guarantee_infer trspec_fixpoint.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.
From lantana.prelude Require Import axioms.

(** * Guarantees of fixpoints, recursive structures ([nest], [renew]) *)

(** ** Guarantees of fixpoints *)
Section fixpoint_guarantees.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma guar_nu_coind (F : trSpec Λ Σ → trSpec Λ Σ) `{!TrSpecMono F} P H :
    trSpec_le H (F H) → P ⊨ₜ H ⊢ P ⊨ₜ trSpec_nu F.
  Proof. intros HH. by apply guar_weaken, trSpec_nu_coind. Qed.

  (** How guarded-recursive formulas get fixpoint guarantees. *)
  Lemma guar_nu_canon (F : trSpec Λ Σ → trSpec Λ Σ) `{!TrSpecMono F} P :
    (⊢ P ⊨ₜ F (trSpec_canon P)) → ⊢ P ⊨ₜ trSpec_nu F.
  Proof.
    intros HP. iApply guar_weaken; [|iApply guar_canon].
    apply trSpec_nu_coind. by apply trSpec_canon_le.
  Qed.

  Lemma guar_mu_rank (F : trSpec Λ Σ → trSpec Λ Σ) `{!TrSpecMono F} P (H : Ord.t → trSpec Λ Σ) α :
    (∀ α, trSpec_le (H α) (F (trSpec_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    P ⊨ₜ H α ⊢ P ⊨ₜ trSpec_mu F.
  Proof. intros HH. by apply guar_weaken, trSpec_mu_intro. Qed.

  (** Introduction without a ranking, for a continuous body. *)
  Lemma guar_mu_fold (F : trSpec Λ Σ → trSpec Λ Σ) `{!TrSpecMono F, !TrSpecCont F} P :
    P ⊨ₜ F (trSpec_mu F) ⊢ P ⊨ₜ trSpec_mu F.
  Proof. by apply guar_weaken, trSpec_mu_unfold_r. Qed.

End fixpoint_guarantees.

(** ** A recursive structure: invariants nested forever

    [nest] is defined by guarded recursion through [alwaysI_guar], with the reading
    [G ∧ ν X. □(G ∧ X)]. The guarantee of its content is a closed proof: the recursion is in
    the structure, not in the proof. Allocation opens the new invariant, registers it, and
    gets the record of its content by Löb induction. *)
Section nest.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Definition F_nest (G : trSpec Λ Σ) : trSpec Λ Σ → trSpec Λ Σ := λ X, trSpec_always (trSpec_and G X).
  Global Instance F_nest_mono G : TrSpecMono (F_nest G).
  Proof.
    apply (trSpec_mono_always (λ X, trSpec_and G X)), (trSpec_mono_and (λ _, G) (λ X, X)).
    - apply trSpec_mono_const.
    - apply trSpec_mono_id.
  Qed.

  (** The reading of a nested invariant. *)
  Definition nest_trSpec G : trSpec Λ Σ := trSpec_and G (trSpec_nu (F_nest G)).

  Definition nest_pre N (Q : iProp Σ) G (X : iPropO Σ) : iPropO Σ := alwaysI_guar N (Q ∗ X) (nest_trSpec G).
  Local Instance nest_pre_contractive N Q G : Contractive (nest_pre N Q G).
  Proof.
    intros n X X' HX. rewrite /nest_pre. apply alwaysI_guar_contractive.
    eapply (ne_dist_later (λ Y : iPropO Σ, (Q ∗ Y)%I)); [solve_proper|exact HX].
  Qed.
  Definition nest N Q G : iProp Σ := fixpoint (nest_pre N Q G).
  Lemma nest_unfold N Q G : nest N Q G ≡ alwaysI_guar N (Q ∗ nest N Q G) (nest_trSpec G).
  Proof. apply (fixpoint_unfold (nest_pre N Q G)). Qed.
  Global Instance nest_persistent N Q G : Persistent (nest N Q G).
  Proof. rewrite /Persistent nest_unfold. apply persistent, _. Qed.

  Lemma guar_nest N Q G : ⊢ nest N Q G ⊨ₜ trSpec_nu (F_nest G).
  Proof.
    iApply (guar_weaken _ (trSpec_always (nest_trSpec G))).
    { apply (trSpec_nu_unfold_r (F_nest G)). }
    iApply (guar_mono (alwaysI_guar N (Q ∗ nest N Q G) (nest_trSpec G)) with "[]").
    { iIntros "!> H". by iEval (rewrite nest_unfold) in "H". }
    iApply guar_alwaysI_guar.
  Qed.

  Lemma guar_nest_content N Q G : (⊢ Q ⊨ₜ G) → ⊢ (Q ∗ nest N Q G) ⊨ₜ nest_trSpec G.
  Proof. intros HQ. iApply guar_sep; [iApply HQ|iApply guar_nest]. Qed.

  Lemma nest_alloc E N Q G :
    ↑N ⊆ E → (⊢ Q ⊨ₜ G) →
    ▷ Q -∗ |={E}=>m nest N Q G.
  Proof.
    iIntros (HN HQ) "HQ". iApply sfmupd_read_fupd. iIntros (h n σ Θ κs) "HI TI".
    iMod (saved_trI_alloc (trSpec_internal (nest_trSpec G))) as (γ) "#Hγ".
    iMod (inv_alloc_open N E (Q ∗ nest N Q G)) as "[#Hinv Hclose]"; first done.
    iPoseProof (history_interp_hist_event_now with "HI") as "#HE".
    iMod (reg_register reg_entry_interp (RAlways N γ) with "TI [] HI") as "(HI& TI& (%j& #Hj))".
    { iIntros (st) "_". simpl. iExists (Q ∗ nest N Q G)%I, (nest_trSpec G). iFrame "Hγ Hinv".
      iNext. iApply (guar_nest_content _ _ _ HQ). }
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    iIntros (g i Ω W) "MI".
    (* the record of the content at [n], by Löb: the content holds the structure, whose own
       record is later-guarded *)
    iAssert (□ (▷ Q -∗ history_interp h n σ Θ κs -∗ model_interp g i Ω W n (dom Θ) -∗
                ▷ record (nest_trSpec G) n))%I with "[]" as "#R".
    { iLöb as "IH". iIntros "!> HQ HI MI".
      iAssert (▷ nest N Q G)%I as "#Hnest".
      { iNext. iEval (rewrite nest_unfold alwaysI_guar_unfold). iExists j, n, γ, _.
        iFrame "Hj HE Hγ Hinv". iSplitR; first (iNext; iApply (guar_nest_content _ _ _ HQ)).
        iApply ("IH" with "[HQ] HI MI"). by iNext. }
      iApply (guar_elim_later_guar (Q ∗ nest N Q G) (nest_trSpec G) with "[] [$HI $MI HQ]").
      { iNext. iApply (guar_nest_content _ _ _ HQ). }
      iNext. iFrame "HQ Hnest". }
    iPoseProof ("R" with "HQ HI MI") as "#T".
    iFrame "MI". iMod "close" as "_".
    iMod ("Hclose" with "[HQ]") as "_".
    { iNext. iFrame "HQ". iEval (rewrite nest_unfold alwaysI_guar_unfold). iExists j, n, γ, _.
      iFrame "Hj HE Hγ Hinv". iSplitR; [iNext; iApply (guar_nest_content _ _ _ HQ)|].
      iNext. iExact "T". }
    iModIntro. iFrame "HI TI". iEval (rewrite nest_unfold alwaysI_guar_unfold). iExists j, n, γ, _.
    iFrame "Hj HE Hγ Hinv T". iNext. iApply (guar_nest_content _ _ _ HQ).
  Qed.

End nest.

(** ** A recursive until: a commitment that renews itself

    [renew N Q G], by guarded recursion through the right side of an until: a finally of [Q]
    and the next link, read as [G ∧ ν X. ◇(G ∧ X)]. The left formula is [True], so allocation
    needs no Löb induction. A thread renews by allocating the next link and discharging the
    current one with it. On traces the reading is just [◇G] (the eventuality is not strict);
    [□◇G] is the guarantee of an always over a finally ([guar_always_finally]). *)
Section renew.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : trSpec Λ Σ.

  Definition F_renew (G : trSpec Λ Σ) : trSpec Λ Σ → trSpec Λ Σ := λ X, trSpec_finally (trSpec_and G X).
  Global Instance F_renew_mono G : TrSpecMono (F_renew G).
  Proof.
    apply (trSpec_mono_until (λ _, trSpec_true) (λ X, trSpec_and G X)); first apply trSpec_mono_const.
    apply (trSpec_mono_and (λ _, G) (λ X, X)); [apply trSpec_mono_const|apply trSpec_mono_id].
  Qed.

  (** The reading of the right formula of a link. *)
  Definition renew_trSpec G : trSpec Λ Σ := trSpec_and G (trSpec_nu (F_renew G)).

  Definition renew_pre N (Q : iProp Σ) G (X : iPropO Σ) : iPropO Σ :=
    (∃ k, untilI_guar N k 1 True (Q ∗ X) trSpec_true (renew_trSpec G))%I.
  Local Instance renew_pre_contractive N Q G : Contractive (renew_pre N Q G).
  Proof.
    intros n X X' HX. rewrite /renew_pre. f_equiv=> k. apply untilI_guar_contractive_r.
    eapply (ne_dist_later (λ Y : iPropO Σ, (Q ∗ Y)%I)); [solve_proper|exact HX].
  Qed.
  Definition renew N Q G : iProp Σ := fixpoint (renew_pre N Q G).
  Lemma renew_unfold N Q G :
    renew N Q G ≡ (∃ k, untilI_guar N k 1 True (Q ∗ renew N Q G) trSpec_true (renew_trSpec G))%I.
  Proof. apply (fixpoint_unfold (renew_pre N Q G)). Qed.

  Lemma renew_intro N Q G k :
    untilI_guar N k 1 True (Q ∗ renew N Q G) trSpec_true (renew_trSpec G) ⊢ renew N Q G.
  Proof. iIntros "H". iEval (rewrite renew_unfold). by iExists k. Qed.

  Lemma guar_renew N Q G : ⊢ renew N Q G ⊨ₜ trSpec_nu (F_renew G).
  Proof.
    iApply (guar_weaken _ (F_renew G (trSpec_nu (F_renew G)))).
    { apply (trSpec_nu_unfold_r (F_renew G)). }
    iApply (guar_mono (∃ k, untilI_guar N k 1 True (Q ∗ renew N Q G) trSpec_true (renew_trSpec G)) with "[]").
    { iIntros "!> H". by iEval (rewrite renew_unfold) in "H". }
    iApply guar_exist_ghost. iIntros (k). iApply guar_untilI_guar.
  Qed.

  Lemma guar_renew_content N Q G : (⊢ Q ⊨ₜ G) → ⊢ (Q ∗ renew N Q G) ⊨ₜ renew_trSpec G.
  Proof. intros HQ. iApply guar_sep; [iApply HQ|iApply guar_renew]. Qed.

  (** Allocation of a link, with a fresh obligation [k] below [p]. *)
  Lemma renew_alloc E N Q G p K ℓ μ :
    (⊢ Q ⊨ₜ G) →
    parP_le p ℓ -∗ parP_kids p K -∗
    |={E}=>m ∃ k, ⌜k ∉ K⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 untilI_guar N k 1 True (Q ∗ renew N Q G) trSpec_true (renew_trSpec G).
  Proof.
    iIntros (HQ) "B Kp". iMod (untilI_guar_alloc with "B Kp") as "(%k& %Hk& Kp& Kk& F& W& ACC)".
    iMod ("ACC" $! E N True%I (Q ∗ renew N Q G)%I trSpec_true (renew_trSpec G) with "[] [] [//]") as "U".
    { iNext. iApply guar_true. }
    { iNext. iApply (guar_renew_content _ _ _ HQ). }
    iModIntro. iExists k. iSplitR; first done. iFrame.
  Qed.

  (** Renewal: the link [k] is discharged with [Q] and the next link at hand. *)
  Lemma renew_discharge E N Q G k p K :
    ↑N ⊆ E → k ∈ K →
    £n 1 -∗ parP_kids p K -∗ oblP_kids k ∅ -∗
    untilI_guar N k 1 True (Q ∗ renew N Q G) trSpec_true (renew_trSpec G) -∗ Q -∗ renew N Q G -∗
    |={E}=>m Q ∗ renew N Q G ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof.
    iIntros (HN Hk) "LC Kp Kk U HQ R".
    iMod (untilI_guar_discharge_lc with "LC Kp Kk U [$HQ $R]") as "([$ $]& $& $)"; done.
  Qed.

  (** On traces, [ν X. ◇(G ∧ X)] is [◇ G]: the eventuality is not strict. *)
  Lemma trSpec_nu_renew_ext G : trSpec_external (trSpec_nu (F_renew G)) ⊆ (◇ trSpec_external G)%R.
  Proof.
    intros [n τf]. rewrite trSpec_nu_ext /=. intros (R & HR & Hτ).
    destruct (HR _ Hτ) as (m & Hm & [HG _] & _). exists m. split_and!; [done|done|by intros].
  Qed.
  Lemma trSpec_nu_renew_ext' G : (◇ trSpec_external G)%R ⊆ trSpec_external (trSpec_nu (F_renew G)).
  Proof.
    intros [n τf]. rewrite trSpec_nu_ext /=. intros (m & Hm & HG & _).
    exists (λ τ', ∃ m', τ'.1 ≤ m' ∧ trSpec_external G (m', τ'.2)). split; last by exists m.
    intros [n' τf'] (m' & Hm' & HG'). exists m'. split_and!; [done| |by intros].
    split; first done. by exists m'.
  Qed.

  (** [□ ◇ G] reads as [□ ◇] of the reading of [G]: [G] infinitely often. *)
  Lemma trSpec_always_finally_ext G : trSpec_external (□ ◇ G)%SPEC = (□ ◇ trSpec_external G)%R.
  Proof. done. Qed.
  Lemma guar_always_finally N N' q (Q : iProp Σ) :
    ⊢ alwaysI N (∃ k, finallyI N' k q Q) ⊨ₜ trSpec_always (trSpec_finally (trSpec_canon Q)).
  Proof.
    iApply guar_alwaysI_valid. iApply guar_exist_ghost. iIntros (k).
    iApply guar_untilI_valid; [apply guar_true|apply guar_canon].
  Qed.

End renew.
