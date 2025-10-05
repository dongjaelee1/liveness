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

Lemma lwp_lift_base_step_fupd {s i E Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     |={∅}=> ∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                         ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                         |={∅,E}=>
     state_interp σ2 (Θ ∪ dom efs) κs ∗
     lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (lwp_lift_step_fupd s i E e1 Φ H)=>//. iIntros (Θ σ1 κ κs) "Hσ".
  iMod ("H" with "Hσ") as "(%& H)"; iModIntro.
  iSplit; first by destruct s; eauto. iMod "H". iIntros "!>" (e2 σ2 efs ?).
  iApply "H"; eauto.
Qed.

Lemma lwp_lift_base_step_fupd_lc {s i E Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ Ψ q,
       (othread_obls i Ψ 1 ∗
        [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
       ALC (|={∅}=>
              ∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                           othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                           ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                           |={∅,E}=>
              state_interp σ2 (Θ ∪ dom efs) κs ∗
              lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (lwp_lift_step_fupd_lc s i E e1 Φ H). iIntros (Θ σ1 κ κs) "Hσ".
  iMod ("H" with "Hσ") as "(%& H)"; iModIntro. iSplit; first by destruct s; eauto.
  iDestruct "H" as "(%&%&D& H)". iFrame "D". iMod "H" as ">H".
  iIntros "!>" (e2 σ2 efs ?). iApply "H"; eauto.
Qed.

Lemma lwp_lift_base_step_fupd_suspended {s i E Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ π Ψ K,
       (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
        ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       ALC (|={∅}=>
              ∀ e2 σ2 efs, (⌜ base_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                           othread_obls i Ψ 1 -∗
                           ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                             ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                              (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                           ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                           |={∅,E}=>
              state_interp σ2 (Θ ∪ dom efs) κs ∗
              lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (lwp_lift_step_fupd_suspended s i E e1 Φ H). iIntros (Θ σ1 κ κs) "Hσ".
  iMod ("H" with "Hσ") as "(%& H)"; iModIntro. iSplit; first by destruct s; eauto.
  iDestruct "H" as "(%&%&%&D& H)". iFrame "D". iMod "H" as ">H".
  iIntros "!>" (e2 σ2 efs ?). iApply "H"; eauto.
Qed.

Lemma lwp_lift_base_stuck i E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ Ω Θ σ κs,
     (osat Ω ∗ othread Θ ∗ osuspend (dom Ω) ∗ oforest (dom Ω) ∗ state_interp σ Θ κs)
     ={E,∅}=∗
     ⌜ base_stuck i e σ Θ ⌝)
  ⊢ lWP e @ i; E ?{{ Φ }}.
Proof.
  iIntros (??) "H". iApply lwp_lift_stuck; first done.
  iIntros (????) "Hσ". iMod ("H" with "Hσ") as "%". by auto.
Qed.

Lemma lwp_lift_pure_base_stuck i E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ τ, base_stuck i e σ τ) →
  ⊢ lWP e @ i; E ?{{ Φ }}.
Proof using Hinh.
  iIntros (?? Hstuck). iApply lwp_lift_base_stuck; [done|done|].
  iIntros (????) "_". iApply fupd_mask_intro; by auto with set_solver.
Qed.

Lemma lwp_lift_atomic_base_step_fupd {s i E Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                  ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                  |={E}=>
     state_interp σ2 (Θ ∪ dom efs) κs ∗
     from_option Φ False (to_val e2) ∗
     [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_step_fupd; [done|].
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)"; iModIntro.
  iSplit; first by destruct s; auto. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma lwp_lift_atomic_base_step_fupd_lc {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ Ψ q,
       (othread_obls i Ψ 1 ∗
        [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
       ALC (|={∅}=>
              ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                           othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                           ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                           |={E2,E1}=>
              state_interp σ2 (Θ ∪ dom efs) κs ∗
              from_option Φ False (to_val e2) ∗
              [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_step_fupd_lc; [done|].
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)"; iModIntro.
  iSplit; first by destruct s; auto. iDestruct "H" as "(%&%&D&H)". iFrame "D".
  iMod "H" as ">H". iIntros "!>" (????) "H1 H2 H3".
  iApply ("H" with "[] H1 H2 H3"). eauto.
Qed.

Lemma lwp_lift_atomic_base_step_fupd_suspended {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ π Ψ K,
       (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
        ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       ALC (|={∅}=>
              ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                           othread_obls i Ψ 1 -∗
                           ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                             ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                              (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                           ([∗ set] j ∈ dom efs, othread_obls j ∅ 1) -∗
                           |={E2,E1}=>
              state_interp σ2 (Θ ∪ dom efs) κs ∗
              from_option Φ False (to_val e2) ∗
              [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
  ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_step_fupd_suspended; [done|].
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)"; iModIntro.
  iSplit; first by destruct s; auto. iDestruct "H" as "(%&%&%&D&H)". iFrame "D".
  iMod "H" as ">H". iIntros "!>" (????) "H1 H2 H3".
  iApply ("H" with "[] H1 H2 H3"). eauto.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork_fupd {s i E Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                  |={E}=>
     ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
     from_option Φ False (to_val e2))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_base_step_fupd; [done|].
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "($& H)"; iModIntro.
  iIntros (??? Hstep) "H1".
  iMod ("H" with "[# //]") as "(%& I& H)". iModIntro.
  subst. replace (Θ ∪ dom ∅) with Θ by set_solver. by iFrame.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork_fupd_lc {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ Ψ q,
       (othread_obls i Ψ 1 ∗
        [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
       ALC (|={∅}=>
              ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                           othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
                           |={E2,E1}=>
              ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
              from_option Φ False (to_val e2)))
  ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_base_step_fupd_lc; [done|].
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "($& H)"; iModIntro.
  iDestruct "H" as "(%&%&D&H)". iFrame "D". iMod "H" as ">H".
  iIntros "!>" (??? Hstep) "H1 H2 H3". iMod ("H" with "[# //] H1 H2") as "(%& I& H)".
  iModIntro. subst. replace (Θ ∪ dom ∅) with Θ by set_solver. by iFrame.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork_fupd_suspended {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ Θ σ1 κ κs,
     state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
     (⌜ base_reducible i e1 σ1 Θ ⌝) ∗
     ∃ π Ψ K,
       (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
        ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       ALC (|={∅}=>
              ∀ e2 σ2 efs, (⌜base_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                           othread_obls i Ψ 1 -∗
                           ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
                             ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                              (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
                           |={E2,E1}=>
              ⌜efs = ∅⌝ ∗ state_interp σ2 Θ κs ∗
              from_option Φ False (to_val e2)))
  ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_base_step_fupd_suspended; [done|].
  iIntros (????) "Hσ1". iMod ("H" with "Hσ1") as "($& H)"; iModIntro.
  iDestruct "H" as "(%&%&%&D&H)". iFrame "D". iMod "H" as ">H".
  iIntros "!>" (??? Hstep) "H1 H2 H3". iMod ("H" with "[# //] H1 H2") as "(%& I& H)".
  iModIntro. subst. replace (Θ ∪ dom ∅) with Θ by set_solver. by iFrame.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork {s i E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
    base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (|={E,E'}=> |={E',E}=> lWP e2 @ s; i; E {{ Φ }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(lwp_lift_pure_det_step_no_fork e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork_lc {s i E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (|={E,E'}=>
     ∃ Ψ q,
     (othread_obls i Ψ 1 ∗
      [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
     ALC (|={∅}=>
            othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
            |={E',E}=> lWP e2 @ s; i; E {{ Φ }}))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(lwp_lift_pure_det_step_no_fork_lc e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork_suspended {s i E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (|={E,E'}=>
     ∃ π Ψ K,
     (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
      ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
     ALC (|={∅}=>
            othread_obls i Ψ 1 -∗
            ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
               (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
            |={E',E}=> lWP e2 @ s; i; E {{ Φ }}))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(lwp_lift_pure_det_step_no_fork_suspended e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork' {s i E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (lWP e2 @ s; i; E {{ Φ }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof using Hinh.
  intros. iIntros "H". iApply lwp_lift_pure_det_base_step_no_fork; eauto.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork_lc' {s i E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (|={E,∅}=>
     ∃ Ψ q,
     (othread_obls i Ψ 1 ∗
      [∗ set] ρ ∈ Ψ, othread_owns i ρ q ∗ obl_pc ρ Ord.one) ∗
     ALC (|={∅}=>
            othread_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othread_owns i ρ q) -∗
            |={∅,E}=> lWP e2 @ s; i; E {{ Φ }}))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(lWP e1 @ s; i; _ {{ _ }})%I]lwp_lift_pure_det_base_step_no_fork_lc //.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork_suspended' {s i E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, base_reducible i e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
     base_step i e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (|={E,∅}=>
     ∃ π Ψ K,
     (⌜Ψ = dom K⌝ ∗ othread_obls i Ψ 1 ∗ obl π ∗
      ([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
     ALC (|={∅}=>
            othread_obls i Ψ 1 -∗
            ((([∗ set] ρ ∈ Ψ, obl_pc ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
               (obl_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ obl_pc k ψ))) -∗
            |={∅,E}=> lWP e2 @ s; i; E {{ Φ }}))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(lWP e1 @ s; i; _ {{ _ }})%I]lwp_lift_pure_det_base_step_no_fork_suspended //.
Qed.

End wp.
