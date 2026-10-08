From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export guarantee_infer itrprop_fixpoint.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties axioms.

(** * Guarantees of fixpoints, recursive structures ([nest], [renew]) *)

(** ** Guarantees of fixpoints *)
Section fixpoint_guarantees.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma temporal_nu_coind (F : itrProp Λ Σ → itrProp Λ Σ) `{!ItrPropMono F} P H :
    itrProp_le H (F H) → P ⊨ₜ H ⊢ P ⊨ₜ itrProp_nu F.
  Proof. intros HH. by apply temporal_weaken, itrProp_nu_coind. Qed.

  (** How guarded-recursive formulas get fixpoint guarantees. *)
  Lemma temporal_nu_sem (F : itrProp Λ Σ → itrProp Λ Σ) `{!ItrPropMono F} P :
    (⊢ P ⊨ₜ F (itrProp_sem P)) → ⊢ P ⊨ₜ itrProp_nu F.
  Proof.
    intros HP. iApply temporal_weaken; [|iApply temporal_sem].
    apply itrProp_nu_coind. by apply itrProp_sem_le.
  Qed.

  Lemma temporal_mu_rank (F : itrProp Λ Σ → itrProp Λ Σ) `{!ItrPropMono F} P (H : Ord.t → itrProp Λ Σ) α :
    (∀ α, itrProp_le (H α) (F (itrProp_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    P ⊨ₜ H α ⊢ P ⊨ₜ itrProp_mu F.
  Proof. intros HH. by apply temporal_weaken, itrProp_mu_intro. Qed.

  (** Introduction without a ranking, for a continuous body. *)
  Lemma temporal_mu_fold (F : itrProp Λ Σ → itrProp Λ Σ) `{!ItrPropMono F, !ItrPropCont F} P :
    P ⊨ₜ F (itrProp_mu F) ⊢ P ⊨ₜ itrProp_mu F.
  Proof. by apply temporal_weaken, itrProp_mu_unfold_r. Qed.

End fixpoint_guarantees.

(** ** A recursive structure: invariants nested forever

    [nest] is defined by guarded recursion through [alwaysI_guar], with the reading
    [G ∧ ν X. □(G ∧ X)]. The guarantee of its content is a closed proof: the recursion is in
    the structure, not in the proof. Allocation opens the new invariant, registers it, and
    gets the record of its content by Löb induction. *)
Section nest.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Definition F_nest (G : itrProp Λ Σ) : itrProp Λ Σ → itrProp Λ Σ := λ X, itrProp_always (itrProp_and G X).
  Global Instance F_nest_mono G : ItrPropMono (F_nest G).
  Proof.
    apply (itrProp_mono_always (λ X, itrProp_and G X)), (itrProp_mono_and (λ _, G) (λ X, X)).
    - apply itrProp_mono_const.
    - apply itrProp_mono_id.
  Qed.

  (** The reading of a nested invariant. *)
  Definition nest_itrProp G : itrProp Λ Σ := itrProp_and G (itrProp_nu (F_nest G)).

  Definition nest_pre N (Q : iProp Σ) G (X : iPropO Σ) : iPropO Σ := alwaysI_guar N (Q ∗ X) (nest_itrProp G).
  Local Instance nest_pre_contractive N Q G : Contractive (nest_pre N Q G).
  Proof.
    intros n X X' HX. rewrite /nest_pre. apply alwaysI_guar_contractive.
    eapply (ne_dist_later (λ Y : iPropO Σ, (Q ∗ Y)%I)); [solve_proper|exact HX].
  Qed.
  Definition nest N Q G : iProp Σ := fixpoint (nest_pre N Q G).
  Lemma nest_unfold N Q G : nest N Q G ≡ alwaysI_guar N (Q ∗ nest N Q G) (nest_itrProp G).
  Proof. apply (fixpoint_unfold (nest_pre N Q G)). Qed.
  Global Instance nest_persistent N Q G : Persistent (nest N Q G).
  Proof. rewrite /Persistent nest_unfold. apply persistent, _. Qed.

  Lemma nest_temporal N Q G : ⊢ nest N Q G ⊨ₜ itrProp_nu (F_nest G).
  Proof.
    iApply (temporal_weaken _ (itrProp_always (nest_itrProp G))).
    { apply (itrProp_nu_unfold_r (F_nest G)). }
    iApply (temporal_mono (alwaysI_guar N (Q ∗ nest N Q G) (nest_itrProp G)) with "[]").
    { iIntros "!> H". by iEval (rewrite nest_unfold) in "H". }
    iApply temporal_always_guar.
  Qed.

  Lemma nest_content_temporal N Q G : (⊢ Q ⊨ₜ G) → ⊢ (Q ∗ nest N Q G) ⊨ₜ nest_itrProp G.
  Proof. intros HQ. iApply temporal_sep; [iApply HQ|iApply nest_temporal]. Qed.

  Lemma nest_alloc E N Q G :
    ↑N ⊆ E → (⊢ Q ⊨ₜ G) →
    ▷ Q -∗ |={E}=>m nest N Q G.
  Proof.
    iIntros (HN HQ) "HQ". iApply sfmupd_read_fupd. iIntros (h n σ Θ κs) "HI TI".
    iMod (saved_ti_alloc (itrProp_internal (nest_itrProp G))) as (γ) "#Hγ".
    iMod (inv_alloc_open N E (Q ∗ nest N Q G)) as "[#Hinv Hclose]"; first done.
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iMod (treg_st_register treg_handle (RAlways N γ) with "TI [] HI") as "(HI& TI& (%j& #Hj))".
    { iIntros (st) "_". simpl. iExists (Q ∗ nest N Q G)%I, (nest_itrProp G). iFrame "Hγ Hinv".
      iNext. iApply (nest_content_temporal _ _ _ HQ). }
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    iIntros (g i Ω W) "MI".
    (* the record of the content at [n], by Löb: the content holds the structure, whose own
       record is later-guarded *)
    iAssert (□ (▷ Q -∗ history_interp h n σ Θ κs -∗ model_interp g i Ω W n (dom Θ) -∗
                ▷ tguar (nest_itrProp G) n))%I with "[]" as "#R".
    { iLöb as "IH". iIntros "!> HQ HI MI".
      iAssert (▷ nest N Q G)%I as "#Hnest".
      { iNext. iEval (rewrite nest_unfold alwaysI_guar_unfold). iExists j, n, γ, _.
        iFrame "Hj HE Hγ Hinv". iSplitR; first (iNext; iApply (nest_content_temporal _ _ _ HQ)).
        iApply ("IH" with "[HQ] HI MI"). by iNext. }
      iApply (temporal_elim_later_guar (Q ∗ nest N Q G) (nest_itrProp G) with "[] [$HI $MI HQ]").
      { iNext. iApply (nest_content_temporal _ _ _ HQ). }
      iNext. iFrame "HQ Hnest". }
    iPoseProof ("R" with "HQ HI MI") as "#T".
    iFrame "MI". iMod "close" as "_".
    iMod ("Hclose" with "[HQ]") as "_".
    { iNext. iFrame "HQ". iEval (rewrite nest_unfold alwaysI_guar_unfold). iExists j, n, γ, _.
      iFrame "Hj HE Hγ Hinv". iSplitR; [iNext; iApply (nest_content_temporal _ _ _ HQ)|].
      iNext. iExact "T". }
    iModIntro. iFrame "HI TI". iEval (rewrite nest_unfold alwaysI_guar_unfold). iExists j, n, γ, _.
    iFrame "Hj HE Hγ Hinv T". iNext. iApply (nest_content_temporal _ _ _ HQ).
  Qed.

End nest.

(** ** A recursive until: a commitment that renews itself

    [renew N Q G], by guarded recursion through the right side of an until: a finally of [Q]
    and the next link, read as [G ∧ ν X. ◇(G ∧ X)]. The left formula is [True], so allocation
    needs no Löb induction. A thread renews by allocating the next link and discharging the
    current one with it. On traces the reading is just [◇G] (the eventuality is not strict);
    [□◇G] is the guarantee of an always over a finally ([always_finally_temporal]). *)
Section renew.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : itrProp Λ Σ.

  Definition F_renew (G : itrProp Λ Σ) : itrProp Λ Σ → itrProp Λ Σ := λ X, itrProp_finally (itrProp_and G X).
  Global Instance F_renew_mono G : ItrPropMono (F_renew G).
  Proof.
    apply (itrProp_mono_until (λ _, itrProp_true) (λ X, itrProp_and G X)); first apply itrProp_mono_const.
    apply (itrProp_mono_and (λ _, G) (λ X, X)); [apply itrProp_mono_const|apply itrProp_mono_id].
  Qed.

  (** The reading of the right formula of a link. *)
  Definition renew_itrProp G : itrProp Λ Σ := itrProp_and G (itrProp_nu (F_renew G)).

  Definition renew_pre N (Q : iProp Σ) G (X : iPropO Σ) : iPropO Σ :=
    (∃ k, untilI_guar N k 1 True (Q ∗ X) itrProp_true (renew_itrProp G))%I.
  Local Instance renew_pre_contractive N Q G : Contractive (renew_pre N Q G).
  Proof.
    intros n X X' HX. rewrite /renew_pre. f_equiv=> k. apply untilI_guar_contractive_r.
    eapply (ne_dist_later (λ Y : iPropO Σ, (Q ∗ Y)%I)); [solve_proper|exact HX].
  Qed.
  Definition renew N Q G : iProp Σ := fixpoint (renew_pre N Q G).
  Lemma renew_unfold N Q G :
    renew N Q G ≡ (∃ k, untilI_guar N k 1 True (Q ∗ renew N Q G) itrProp_true (renew_itrProp G))%I.
  Proof. apply (fixpoint_unfold (renew_pre N Q G)). Qed.

  Lemma renew_intro N Q G k :
    untilI_guar N k 1 True (Q ∗ renew N Q G) itrProp_true (renew_itrProp G) ⊢ renew N Q G.
  Proof. iIntros "H". iEval (rewrite renew_unfold). by iExists k. Qed.

  Lemma renew_temporal N Q G : ⊢ renew N Q G ⊨ₜ itrProp_nu (F_renew G).
  Proof.
    iApply (temporal_weaken _ (F_renew G (itrProp_nu (F_renew G)))).
    { apply (itrProp_nu_unfold_r (F_renew G)). }
    iApply (temporal_mono (∃ k, untilI_guar N k 1 True (Q ∗ renew N Q G) itrProp_true (renew_itrProp G)) with "[]").
    { iIntros "!> H". by iEval (rewrite renew_unfold) in "H". }
    iApply temporal_exist_ghost. iIntros (k). iApply temporal_until_guar.
  Qed.

  Lemma renew_content_temporal N Q G : (⊢ Q ⊨ₜ G) → ⊢ (Q ∗ renew N Q G) ⊨ₜ renew_itrProp G.
  Proof. intros HQ. iApply temporal_sep; [iApply HQ|iApply renew_temporal]. Qed.

  (** Allocation of a link, with a fresh obligation [k] below [p]. *)
  Lemma renew_alloc E N Q G p K ℓ μ :
    (⊢ Q ⊨ₜ G) →
    parP_le p ℓ -∗ parP_kids p K -∗
    |={E}=>m ∃ k, ⌜k ∉ K⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 untilI_guar N k 1 True (Q ∗ renew N Q G) itrProp_true (renew_itrProp G).
  Proof.
    iIntros (HQ) "B Kp". iMod (untilI_guar_alloc with "B Kp") as "(%k& %Hk& Kp& Kk& F& W& ACC)".
    iMod ("ACC" $! E N True%I (Q ∗ renew N Q G)%I itrProp_true (renew_itrProp G) with "[] [] [//]") as "U".
    { iNext. iApply temporal_true. }
    { iNext. iApply (renew_content_temporal _ _ _ HQ). }
    iModIntro. iExists k. iSplitR; first done. iFrame.
  Qed.

  (** Renewal: the link [k] is discharged with [Q] and the next link at hand. *)
  Lemma renew_discharge E N Q G k p K :
    ↑N ⊆ E → k ∈ K →
    £n 1 -∗ parP_kids p K -∗ oblP_kids k ∅ -∗
    untilI_guar N k 1 True (Q ∗ renew N Q G) itrProp_true (renew_itrProp G) -∗ Q -∗ renew N Q G -∗
    |={E}=>m Q ∗ renew N Q G ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof.
    iIntros (HN Hk) "LC Kp Kk U HQ R".
    iMod (untilI_guar_discharge_lc with "LC Kp Kk U [$HQ $R]") as "([$ $]& $& $)"; done.
  Qed.

  (** On traces, [ν X. ◇(G ∧ X)] is [◇G]. *)
  Lemma itrProp_nu_renew_ext G τ : itrProp_external (itrProp_nu (F_renew G)) τ ↔ itrProp_external (itrProp_finally G) τ.
  Proof.
    rewrite itrProp_nu_ext. destruct τ as [n τf]. rewrite /=. split.
    - intros (R & HR & Hτ). destruct (HR _ Hτ) as (m & Hm & [HG _] & _).
      exists m. split_and!; [done|done|by intros].
    - intros (m & Hm & HG & _).
      exists (λ τ', ∃ m', τ'.1 ≤ m' ∧ itrProp_external G (m', τ'.2)). split; last by exists m.
      intros [n' τf'] (m' & Hm' & HG'). exists m'. split_and!; [done| |by intros].
      split; first done. by exists m'.
  Qed.

  (** [G] infinitely often: always a live finally, renewed in an invariant. *)
  Lemma itrProp_always_finally_ext G n τf :
    itrProp_external (itrProp_always (itrProp_finally G)) (n, τf) ↔ ∀ m, n ≤ m → ∃ l, m ≤ l ∧ itrProp_external G (l, τf).
  Proof.
    rewrite /=. split.
    - intros H m Hm. destruct (H m Hm) as (l & ? & ? & _). eauto.
    - intros H m Hm. destruct (H m Hm) as (l & ? & ?). exists l. split_and!; [done|done|by intros].
  Qed.
  Lemma always_finally_temporal N N' q (Q : iProp Σ) :
    ⊢ alwaysI N (∃ k, finallyI N' k q Q) ⊨ₜ itrProp_always (itrProp_finally (itrProp_sem Q)).
  Proof.
    iApply temporal_always_valid. iApply temporal_exist_ghost. iIntros (k).
    iApply temporal_until_valid; [apply temporal_true|apply temporal_sem].
  Qed.

End renew.
