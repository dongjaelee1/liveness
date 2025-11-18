(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From liris Require Import ordinal_wfocm.
From liris.program_logic Require Export ectx_language weakestpre lifting.
From iris.prelude Require Import options.

Section wp.
Context {Λ : ectxLanguage} `{SI : indexT} `{!lirisGS Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve base_prim_reducible base_reducible_prim_step : core.
Local Definition reducible_not_val_inhabitant i e τ := reducible_not_val i e inhabitant τ.
Local Hint Resolve reducible_not_val_inhabitant : core.
Local Hint Resolve base_stuck_stuck : core.

Lemma lwp_lift_base_step_fupd {s ς i E Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                  ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                  |={∅,E}=>
     state_interp σ2 (Θ ∪ dom efs) κs ∗
     lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply (lwp_lift_step_fupd s _ i E e1 Φ). iIntros (Θ σ1 κ κs) "Hσ".
  iMod ("H" with "Hσ") as "(%& H)"; iModIntro. destruct H.
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 efs ?).
  iApply "H"; eauto.
Qed.

Lemma lwp_lift_base_step_fupd_lc {s ς i E Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ Ψ q,
       (othread_obls i Ψ 1 ∗
        [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
       ∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                    othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                    ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                    ALC (|={∅,E}=>
                           state_interp σ2 (Θ ∪ dom efs) κs ∗
                           lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply (lwp_lift_step_fupd_lc s _ i E e1 Φ). iIntros (Θ σ1 κ κs) "Hσ".
  iMod ("H" with "Hσ") as "(%& H)"; iModIntro. destruct H. iSplit; first by destruct s; eauto.
  iDestruct "H" as "(%&%& $& H)".
  iIntros (e2 σ2 efs ?). iApply "H"; eauto.
Qed.

Lemma lwp_lift_base_step_fupd_suspended {s ς i E Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ π Ψ K,
       (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
        ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       ∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                    othread_obls i Ψ 1 -∗
                    ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                       (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                    ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                    ALC (|={∅,E}=>
                           state_interp σ2 (Θ ∪ dom efs) κs ∗
                           lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  iIntros "H". iApply (lwp_lift_step_fupd_suspended s _ i E e1 Φ). iIntros (Θ σ1 κ κs) "Hσ".
  iMod ("H" with "Hσ") as "(%& H)"; iModIntro. destruct H. iSplit; first by destruct s; eauto.
  iDestruct "H" as "(%&%&%& $& H)".
  iIntros (e2 σ2 efs ?). iApply "H"; eauto.
Qed.

Lemma lwp_lift_base_step_fupd_gen (glc : get_lc) {s ς i E Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     match glc with
     | NoLc =>
         (∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                       ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                       |={∅,E}=>
            state_interp σ2 (Θ ∪ dom efs) κs ∗
            lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
     | GetLc =>
         (∃ Ψ q,
             (othread_obls i Ψ 1 ∗
              [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
             ∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                          othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                          ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                          ALC (|={∅,E}=>
                                 state_interp σ2 (Θ ∪ dom efs) κs ∗
                                 lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
     | GetLcSus =>
         (∃ π Ψ K,
             (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
              ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
             ∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                          othread_obls i Ψ 1 -∗
                          ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                            ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                             (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                          ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                          ALC (|={∅,E}=>
                                 state_interp σ2 (Θ ∪ dom efs) κs ∗
                                 lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
     end)
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof.
  destruct glc.
  - apply lwp_lift_base_step_fupd.
  - apply lwp_lift_base_step_fupd_lc.
  - apply lwp_lift_base_step_fupd_suspended.
Qed.

Lemma lwp_lift_base_stuck ς i E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ Ω Θ σ κs,
     (ς ∗ osat Ω ∗ othread Θ ∗ osuspend (dom Ω) ∗ oforest (dom Ω) ∗ state_interp σ Θ κs)
     ={E,∅}=∗
     ⌜ base_stuck i e σ Θ ⌝)
  ⊢ lWP e @ ς; i; E ?{{ Φ }}.
Proof.
  iIntros (??) "H". iApply lwp_lift_stuck; first done.
  iIntros (????) "Hσ". iMod ("H" with "Hσ") as "%". by auto.
Qed.

Lemma lwp_lift_pure_base_stuck ς i E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ τ, base_stuck i e σ τ) →
  ⊢ lWP e @ ς; i; E ?{{ Φ }}.
Proof using Hinh.
  iIntros (?? Hstuck). iApply lwp_lift_base_stuck; [done|done|].
  iIntros (????) "_". iApply fupd_mask_intro; by auto with set_solver.
Qed.

Lemma lwp_lift_atomic_base_step_fupd {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                  ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                  |={E2,E1}=>
     state_interp σ2 (Θ ∪ dom efs) κs ∗
     (ς -∗ from_option Φ False (to_val e2)) ∗
     [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_step_fupd.
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)"; iModIntro. destruct H.
  iSplit; first by destruct s; auto. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma lwp_lift_atomic_base_step_fupd_lc {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ Ψ q,
       (othread_obls i Ψ 1 ∗
        [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
       ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                    othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                    ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                    ALC (|={E2,E1}=>
                           state_interp σ2 (Θ ∪ dom efs) κs ∗
                           (ς -∗ from_option Φ False (to_val e2)) ∗
                           [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_step_fupd_lc.
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)"; iModIntro. destruct H.
  iSplit; first by destruct s; auto. iDestruct "H" as "(%&%&$&H)".
  iIntros (????) "H1 H2 H3".
  iApply ("H" with "[] H1 H2 H3"). eauto.
Qed.

Lemma lwp_lift_atomic_base_step_fupd_suspended {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ π Ψ K,
       (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
        ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                    othread_obls i Ψ 1 -∗
                    ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                       (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                    ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                    ALC (|={E2,E1}=>
                           state_interp σ2 (Θ ∪ dom efs) κs ∗
                           (ς -∗ from_option Φ False (to_val e2)) ∗
                           [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_step_fupd_suspended.
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)"; iModIntro. destruct H.
  iSplit; first by destruct s; auto. iDestruct "H" as "(%&%&%&D&H)". iFrame "D".
  iIntros (????) "H1 H2 H3".
  iApply ("H" with "[] H1 H2 H3"). eauto.
Qed.

Lemma lwp_lift_atomic_base_step_fupd_gen (glc : get_lc) {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     match glc with
     | NoLc =>
         (∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                       ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                       |={E2,E1}=>
            state_interp σ2 (Θ ∪ dom efs) κs ∗
            (ς -∗ from_option Φ False (to_val e2)) ∗
            [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
     | GetLc =>
         (∃ Ψ q,
             (othread_obls i Ψ 1 ∗
              [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
             ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                          othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                          ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                          ALC (|={E2,E1}=>
                                 state_interp σ2 (Θ ∪ dom efs) κs ∗
                                 (ς -∗ from_option Φ False (to_val e2)) ∗
                                 [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
     | GetLcSus =>
         (∃ π Ψ K,
             (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
              ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
             ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                          othread_obls i Ψ 1 -∗
                          ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                            ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                             (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                          ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                          ALC (|={E2,E1}=>
                                 state_interp σ2 (Θ ∪ dom efs) κs ∗
                                 (ς -∗ from_option Φ False (to_val e2)) ∗
                                 [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
     end)
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  destruct glc.
  - apply lwp_lift_atomic_base_step_fupd.
  - apply lwp_lift_atomic_base_step_fupd_lc.
  - apply lwp_lift_atomic_base_step_fupd_suspended.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork_fupd {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                  |={E2,E1}=>
     ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
     (ς -∗ from_option Φ False (to_val e2)))
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step_fupd.
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "($& H)"; iModIntro.
  iIntros (??? Hstep) "H1".
  iMod ("H" with "[# //]") as "(%& I& H)". iModIntro.
  subst. replace (Θ ∪ dom ∅) with Θ by set_solver. by iFrame.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork_fupd_lc {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ Ψ q,
       (othread_obls i Ψ 1 ∗
        [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
       ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                    othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                    ALC (|={E2,E1}=>
                           ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
                           (ς -∗ from_option Φ False (to_val e2))))
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step_fupd_lc.
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "($& H)"; iModIntro.
  iDestruct "H" as "(%&%&D&H)". iFrame "D".
  iIntros (??? Hstep) "H1 H2 H3". iMod ("H" with "[# //] H1 H2") as ">(%& I& H)".
  iModIntro. subst. replace (Θ ∪ dom ∅) with Θ by set_solver. by iFrame.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork_fupd_suspended {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ π Ψ K,
       (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
        ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                    othread_obls i Ψ 1 -∗
                    ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                       (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                    ALC (|={E2,E1}=>
                           ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
                           (ς -∗ from_option Φ False (to_val e2))))
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  iIntros "H". iApply lwp_lift_atomic_base_step_fupd_suspended.
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "($& H)"; iModIntro.
  iDestruct "H" as "(%&%&%&D&H)". iFrame "D".
  iIntros (??? Hstep) "H1 H2 H3". iMod ("H" with "[# //] H1 H2") as ">(%& I& H)".
  iModIntro. subst. replace (Θ ∪ dom ∅) with Θ by set_solver. by iFrame.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork_fupd_gen (glc : get_lc) {s ς i E1 E2 Φ} e1 :
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ to_val e1 = None ∧ base_reducible i e1 σ1 Θ ⌝) ∗
     match glc with
     | NoLc =>
         (∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                       |={E2,E1}=>
            ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
            (ς -∗ from_option Φ False (to_val e2)))
     | GetLc =>
         (∃ Ψ q,
             (othread_obls i Ψ 1 ∗
              [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
             ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                          othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                          ALC (|={E2,E1}=>
                                 ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
                                 (ς -∗ from_option Φ False (to_val e2))))
     | GetLcSus =>
         (∃ π Ψ K,
             (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
              ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
             ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                          othread_obls i Ψ 1 -∗
                          ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                            ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                             (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                          ALC (|={E2,E1}=>
                                 ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
                                 (ς -∗ from_option Φ False (to_val e2))))
     end)
  ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
Proof.
  destruct glc.
  - apply lwp_lift_atomic_base_step_no_fork_fupd.
  - apply lwp_lift_atomic_base_step_no_fork_fupd_lc.
  - apply lwp_lift_atomic_base_step_no_fork_fupd_suspended.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork {s ς i E Φ C} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, C i σ1 → base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     C i σ1 →
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  PureExecCond C ς i →
  (lWP e2 @ s; ς; i; E {{ Φ }})
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(lwp_lift_pure_det_step_no_fork e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork_lc {s ς i E E' Φ C} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, C i σ1 → base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     C i σ1 →
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  PureExecCond C ς i →
  (|={E,E'}=>
     ∃ Ψ q,
     (othread_obls i Ψ 1 ∗
      [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
     (othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
      ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(lwp_lift_pure_det_step_no_fork_lc e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork_suspended {s ς i E E' Φ C} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, C i σ1 → base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     C i σ1 →
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  PureExecCond C ς i →
  (|={E,E'}=>
     ∃ π Ψ K,
     (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
      ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
     (othread_obls i Ψ 1 -∗
      ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
         (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
      ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(lwp_lift_pure_det_step_no_fork_suspended e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork_gen (glc : get_lc) {s ς i E E' Φ C} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, C i σ1 → base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     C i σ1 →
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  PureExecCond C ς i →
  (match glc with
   | NoLc =>
       (lWP e2 @ s; ς; i; E {{ Φ }})
   | GetLc =>
       |={E,E'}=>
         (∃ Ψ q,
             (othread_obls i Ψ 1 ∗
              [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
             (othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
              ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
   | GetLcSus =>
       |={E,E'}=>
         (∃ π Ψ K,
             (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
              ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
             (othread_obls i Ψ 1 -∗
              ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                 (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
              ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
   end)
  ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
Proof using Hinh.
  destruct glc.
  - apply lwp_lift_pure_det_base_step_no_fork.
  - apply lwp_lift_pure_det_base_step_no_fork_lc.
  - apply lwp_lift_pure_det_base_step_no_fork_suspended.
Qed.

End wp.
