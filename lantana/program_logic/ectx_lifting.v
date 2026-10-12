(** Lifting lemmas of [lWP] for ectx-based languages, stated with base steps. Adapted from
    Iris's [iris.program_logic.ectx_lifting]. *)
From iris.proofmode Require Import proofmode.
From lantana.program_logic Require Export ectx_language lifting.
From iris.prelude Require Import options.

Section ectx_lifting.
  Context {Λ : ectxLanguage} `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ} {Hinh : Inhabited (state Λ)}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types e : expr Λ.
  Local Hint Resolve base_prim_reducible base_reducible_prim_step : core.
  Local Definition reducible_not_val_inhabitant i e τ := reducible_not_val i e inhabitant τ.
  Local Hint Resolve reducible_not_val_inhabitant : core.
  Local Hint Resolve base_stuck_stuck : core.

  Lemma lwp_lift_base_step {s i E Φ} e1 :
    to_val e1 = None →
    (∀ K σ1 Θ κ κs,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
       (state_interp σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E,∅}=∗
       (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 (dom Θ) ⌝) ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
            ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 (∀ e2 σ2 efs, (⌜base_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                               thP_kids i G -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                               ([∗ set] j ∈ dom efs, thP_kids j ∅) -∗
                               ALC (|={∅,E}=>
                                      (state_interp σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                       state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
                                      (|={E}=>m ((lWP e2 @ s; i; E {{ Φ }}) ∗
                                                     ([∗ map] j ↦ ef ∈ efs,
                                                        lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))))))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (He) "H". iApply (lwp_lift_step_si s i E e1 Φ). 1: auto. iIntros (K σ1 Θ κ κs HK HΘ) "Hσ".
    iMod ("H" $! K with "[//] [//] Hσ") as "(%& %& $& $& %& $& H)". iModIntro.
    destruct H. iSplit; first by destruct s; eauto.
    iIntros (e2 σ2 efs ?). iApply "H"; eauto.
  Qed.

  Lemma lwp_lift_base_stuck i E Φ e :
    to_val e = None →
    sub_redexes_are_values e →
    (∀ K σ κ Θ, ⌜LanguageCtx K⌝ → ⌜Θ !! i = Some (K e)⌝ →
                (state_interp σ Θ κ ∗ state_interp_aux σ Θ κ) ={E,∅}=∗
                ⌜ base_stuck i e σ (dom Θ) ⌝)
    ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    iIntros (??) "H". iApply lwp_lift_stuck; first done.
    iIntros (???? ??) "Hσ". iMod ("H" $! K with "[//] [//] Hσ") as "H".
    iDestruct "H" as "%". iModIntro. by auto.
  Qed.

  Lemma lwp_lift_pure_base_stuck i E Φ e :
    to_val e = None →
    sub_redexes_are_values e →
    (∀ σ τ, base_stuck i e σ τ) →
    ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof using Hinh.
    iIntros (?? Hstuck). iApply lwp_lift_base_stuck; [done|done|].
    iIntros (???? ??) "_". iApply fupd_mask_intro; by auto with set_solver.
  Qed.

  Lemma lwp_lift_atomic_base_step {s i E1 E2 Φ} e1 :
    to_val e1 = None →
    (∀ K σ1 Θ κ κs,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
       (state_interp σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E1,E2}=∗
       (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 (dom Θ) ⌝) ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
            ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 ∀ e2 σ2 efs, (⌜base_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                              thP_kids i G -∗
                              ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                              ([∗ set] j ∈ dom efs, thP_kids j ∅) -∗
                              ALC (|={E2,E1}=>
                                     (state_interp σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                      state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
                                     |={E1}=>m
                                              (from_option (λ v, (|={E1}=>m (Φ v))) False (to_val e2)) ∗
                                            [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
    ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros (He) "H". iApply lwp_lift_atomic_step. 1: auto.
    iIntros (????? ??) "Hσ1". iMod ("H" $! K with "[//] [//] Hσ1") as "(%& %&$&$& %&$& H)".
    iModIntro. destruct H1. iSplit; first by destruct s; auto.
    iIntros (e2 σ2 efs Hstep). iApply "H"; eauto.
  Qed.

  Lemma lwp_lift_atomic_base_step_no_fork {s i E1 E2 Φ} e1 :
    to_val e1 = None →
    (∀ K σ1 Θ κ κs,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
       (state_interp σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E1,E2}=∗
       (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 (dom Θ) ⌝) ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
            ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 ∀ e2 σ2 efs, (⌜base_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                              thP_kids i G -∗
                              ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                              ALC (|={E2,E1}=>
                                     ⌜efs = ∅⌝ ∗
                                     (state_interp σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                      state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
                                     (from_option (λ v, (|={E1}=>m (Φ v))) False (to_val e2))))
    ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros (He) "H". iApply lwp_lift_atomic_base_step. 1: auto.
    iIntros (????? ??) "Hσ1". iMod ("H" $! K with "[//] [//] Hσ1") as "($& %&$&$& %&$& H)".
    iModIntro.
    iIntros (??? Hstep). iMod ("H" with "[# //]") as "H".
    iIntros "!> Tb Wcs _". iMod ("H" with "Tb Wcs") as ">(%& I& $)".
    subst. rewrite !map_union_empty. iFrame. iModIntro. iModIntro. done.
  Qed.

  Lemma lwp_lift_pure_det_base_step_no_fork {s i E E' Φ ς} e1 e2 :
    to_val e1 = None →
    (∀ σ1 τ, base_reducible i e1 σ1 τ) →
    (∀ σ1 κ τ e2' σ2 efs',
       base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    PureExecSI ς i →
    (|={E,E'}=>
       ς i e1 ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
            ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 (ς i e2 -∗
                  thP_kids i G -∗
                  ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                  ALC (|={E',E}=> (|={E}=>m (lWP e2 @ s; i; E {{ Φ }})))))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof using Hinh.
    intros. rewrite -(lwp_lift_pure_det_step_no_fork e1 e2); eauto.
    destruct s; by auto.
  Qed.

End ectx_lifting.
