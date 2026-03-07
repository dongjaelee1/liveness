(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From liris.program_logic Require Export ectx_language lifting.
From iris.prelude Require Import options.
From liris Require Import ordinal_wfocm.

Section wp.
  Context {Λ : ectxLanguage} `{SI : indexT} `{!lirisGS Λ Σ} {Hinh : Inhabited (state Λ)}.
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
    (∀ h n σ1 κ κs Θ,
       history_interp h n (σ1, κ ++ κs) Θ ={E,∅}=∗
       (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
            ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                 (∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
                               thP_obls i G 1 -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                               ([∗ set] j ∈ dom efs, thP_obls j ∅ 1) -∗
                               ALC (|={∅,E}=> history_interp (h ++ [(σ2, κs, Θ ∪ dom efs)]) (S n) (σ2, κs) (Θ ∪ dom efs) ∗
                                             (|={E}=>m lWP e2 @ s; i; E {{ Φ }}) ∗
                                             [∗ map] j ↦ ef ∈ efs, |={⊤}=>m lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". iApply (lwp_lift_step s i E e1 Φ). iIntros (h n σ1 κ κs Θ) "Hσ".
    iMod ("H" with "Hσ") as "(%& %& $& $& %& $& H)"; iModIntro.
    destruct H. iSplit; first by destruct s; eauto.
    iIntros (e2 σ2 efs ?). iApply "H"; eauto.
  Qed.

  Lemma lwp_lift_base_stuck i E Φ e :
    to_val e = None →
    sub_redexes_are_values e →
    (∀ h n σ κs Θ, history_interp h n (σ, κs) Θ ={E,∅}=∗ ⌜ base_stuck i e σ Θ ⌝)
    ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    iIntros (??) "H". iApply lwp_lift_stuck; first done.
    iIntros (?????) "Hσ". iMod ("H" with "Hσ") as "H".
    iDestruct "H" as "%". iModIntro. by auto.
  Qed.

  Lemma lwp_lift_pure_base_stuck i E Φ e :
    to_val e = None →
    sub_redexes_are_values e →
    (∀ σ τ, base_stuck i e σ τ) →
    ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof using Hinh.
    iIntros (?? Hstuck). iApply lwp_lift_base_stuck; [done|done|].
    iIntros (?????) "_". iApply fupd_mask_intro; by auto with set_solver.
  Qed.

  Lemma lwp_lift_atomic_base_step {s i E1 E2 Φ} e1 :
    (∀ h n σ1 κ κs Θ,
       history_interp h n (σ1, κ ++ κs) Θ ={E1,E2}=∗
       (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
            ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                 ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
                              thP_obls i G 1 -∗
                              ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                              ([∗ set] j ∈ dom efs, thP_obls j ∅ 1) -∗
                              ALC (|={E2,E1}=> history_interp (h ++ [(σ2, κs, Θ ∪ dom efs)]) (S n) (σ2, κs) (Θ ∪ dom efs) ∗
                                              (from_option (λ v, |={E1}=>m (Φ v)) False (to_val e2)) ∗
                                              [∗ map] j ↦ ef ∈ efs, |={⊤}=>m lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
    ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H". iApply lwp_lift_atomic_step.
    iIntros (??????) "Hσ1". iMod ("H" with "Hσ1") as "(%& %&$&$& %&$& H)"; iModIntro.
    destruct H. iSplit; first by destruct s; auto.
    iIntros (e2 σ2 efs Hstep). iApply "H"; eauto.
  Qed.

  Lemma lwp_lift_atomic_base_step_no_fork {s i E1 E2 Φ} e1 :
    (∀ h n σ1 κ κs Θ,
       history_interp h n (σ1, κ ++ κs) Θ ={E1,E2}=∗
       (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
            ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                 ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
                              thP_obls i G 1 -∗
                              ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                              ALC (|={E2,E1}=> ⌜efs = ∅⌝ ∗
                                              history_interp (h ++ [(σ2, κs, Θ ∪ dom efs)]) (S n) (σ2, κs) (Θ ∪ dom efs) ∗
                                              (from_option (λ v, |={E1}=>m (Φ v)) False (to_val e2))))
    ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H". iApply lwp_lift_atomic_base_step.
    iIntros (??????) "Hσ1". iMod ("H" with "Hσ1") as "($& %&$&$& %&$& H)"; iModIntro.
    iIntros (??? Hstep). iMod ("H" with "[# //]") as "H".
    iIntros "!> Tb Wcs _". iMod ("H" with "Tb Wcs") as ">(%& I& $)".
    subst. replace (Θ ∪ dom ∅) with Θ by set_solver. iFrame.
    iModIntro. done.
  Qed.

  Lemma lwp_lift_pure_det_base_step_no_fork {s i E E' Φ C ς} e1 e2 :
    to_val e1 = None →
    (∀ σ1 τ, C i σ1 → base_reducible i e1 σ1 τ) →
    (∀ σ1 κ τ e2' σ2 efs',
       C i σ1 →
       base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    PureExecCond C ς i →
    (|={E,E'}=>
       ς ∗
       ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
            ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                 (ς -∗
                  thP_obls i G 1 -∗
                  ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r) -∗
                  ALC (|={E',E}=> |={E}=>m lWP e2 @ s; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof using Hinh.
    intros. rewrite -(lwp_lift_pure_det_step_no_fork e1 e2); eauto.
    destruct s; by auto.
  Qed.

End wp.
