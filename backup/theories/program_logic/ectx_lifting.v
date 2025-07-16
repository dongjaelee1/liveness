(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import proofmode.
From liris Require Import ordinal_wfocm.
From liris.program_logic Require Export ectx_language weakestpre lifting.
From iris.prelude Require Import options.

Section wp.
Context {Λ : ectxLanguage} `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve base_prim_reducible base_reducible_prim_step : core.
Local Definition reducible_not_val_inhabitant e τ := reducible_not_val e inhabitant τ.
Local Hint Resolve reducible_not_val_inhabitant : core.
Local Hint Resolve base_stuck_stuck : core.

Lemma lwp_lift_base_step_fupd {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ,
     state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
     ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈Λ⌉)) ∗
            (⌜ base_reducible e1 σ1 τ ⌝) ∗
            ∀ e2 σ2 efs, (⌜ base_step e1 σ1 τ κ e2 σ2 efs ⌝) -∗
                         toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗
                         £ 1 ={∅}=∗ ▷ |={∅,E}=>
     state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
     lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (lwp_lift_step_fupd s i E Φ e1 H)=>//. iIntros (σ1 ns κ κs τ) "Hσ".
  iMod ("H" with "Hσ") as "(% & % & HL & Hc & % & H)"; iModIntro.
  iFrame "HL Hc". iSplit; first by destruct s; eauto. iIntros (e2 σ2 efs ?).
  iApply "H"; eauto.
Qed.

Lemma lwp_lift_base_step {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ,
     state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
     ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈Λ⌉)) ∗
            (⌜ base_reducible e1 σ1 τ ⌝) ∗
            ▷ ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                           toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗
                           £ 1 ={∅,E}=∗
                           state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
                           lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_base_step_fupd; [done|]. iIntros (?????) "?".
  iMod ("H" with "[$]") as "(%&%&HL&Hc&$&H)". iFrame "HL Hc".
  iIntros "!>" (e2 σ2 efs ?) "HL Hfc HLs Hcred !> !>". iApply ("H" with "[] HL Hfc HLs Hcred").
  iPureIntro. by apply base_prim_step.
Qed.

Lemma lwp_lift_base_stuck i E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ δ (Ω : obl_statesL Λ) γ σ ns κs τ,
     (⌜ τ = dom δ ⌝ ∗ schedfairIL Λ δ ∗ osat Ω ∗ toIL Λ γ ∗ oftIL Λ Ω δ γ ∗ state_interp σ ns κs τ) ={E,∅}=∗
     ⌜ base_stuck e σ τ ⌝)
  ⊢ lWP e @ i; E ?{{ Φ }}.
Proof.
  iIntros (??) "H". iApply lwp_lift_stuck; first done.
  iIntros (δ Ω γ σ ns κs τ) "Hσ". iMod ("H" with "Hσ") as "%". by auto.
Qed.

Lemma lwp_lift_pure_base_stuck i E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ τ, base_stuck e σ τ) →
  ⊢ lWP e @ i; E ?{{ Φ }}.
Proof using Hinh.
  iIntros (?? Hstuck). iApply lwp_lift_base_stuck; [done|done|].
  iIntros (δ Ω γ σ ns κs τ) "_". iApply fupd_mask_intro; by auto with set_solver.
Qed.

Lemma lwp_lift_atomic_base_step_fupd {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ, state_interp σ1 ns (κ ++ κs) τ ={E1,∅}=∗
    ∃ (q : Qp) (L : list obl_id), toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
    ⌜ base_reducible e1 σ1 τ ⌝ ∗
    ∀ e2 σ2 efs, ⌜ base_step e1 σ1 τ κ e2 σ2 efs ⌝ -∗
    toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗ £ 1 ={∅,E1}=∗ |={E1}[E2]▷=>
      state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_step_fupd; [done|].
  iIntros (σ1 ns κ κs τ) "Hσ1". iMod ("H" with "Hσ1") as "(%&%&HL&Hc&%&H)"; iModIntro.
  iFrame "HL Hc". iSplit; first by destruct s; auto. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma lwp_lift_atomic_base_step {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ, state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
    ∃ (q : Qp) (L : list obl_id), toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
    ⌜ base_reducible e1 σ1 τ ⌝ ∗
      ∀ e2 σ2 efs, ⌜base_step e1 σ1 τ κ e2 σ2 efs⌝ -∗
      toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗ £ 1 ={∅,E}=∗ |={E}▷=>
      state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_step; first done.
  iIntros (σ1 ns κ κs τ) "Hσ1". iMod ("H" with "Hσ1") as "(%&%&HL&Hc&%&H)"; iModIntro.
  iFrame "HL Hc". iSplit; first by destruct s; auto. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork_fupd {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ, state_interp σ1 ns (κ ++ κs) τ ={E1,∅}=∗
    ∃ (q : Qp) (L : list obl_id), toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
    ⌜ base_reducible e1 σ1 τ ⌝ ∗
    ∀ e2 σ2 (efs : thread_pool Λ), ⌜ base_step e1 σ1 τ κ e2 σ2 efs ⌝ -∗
    toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ £ 1 ={∅,E1}=∗ |={E1}[E2]▷=>
      ⌜efs = ∅⌝ ∗ state_interp σ2 (S ns) κs τ ∗ from_option Φ False (to_val e2))
  ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_base_step_fupd; [done|].
  iIntros (σ1 ns κ κs τ) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "(%&%&HL&Hc& $ &H)"; iModIntro.
  iFrame "HL Hc". iIntros (v2 σ2 efs Hstep) "HL Hfc HLs Hcred".
  iMod ("H" $! v2 σ2 efs with "[# //] HL Hfc Hcred") as "H". iModIntro.
  iMod "H". iModIntro. iNext. iMod "H" as "(-> & ? & ?) /=". iModIntro.
  replace (τ ∪ dom ∅) with τ by set_solver. by iFrame.
Qed.

Lemma lwp_lift_atomic_base_step_no_fork {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ, state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
    ∃ (q : Qp) (L : list obl_id), toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
    ⌜ base_reducible e1 σ1 τ ⌝ ∗
    ∀ e2 σ2 (efs : thread_pool Λ), ⌜ base_step e1 σ1 τ κ e2 σ2 efs ⌝ -∗
    toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ £ 1 ={∅,E}=∗ |={E}▷=>
      ⌜efs = ∅⌝ ∗ state_interp σ2 (S ns) κs τ ∗ from_option Φ False (to_val e2))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_base_step; first done.
  iIntros (σ1 ns κ κs τ) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "(%&%&HL&Hc& $ &H)"; iModIntro.
  iFrame "HL Hc". iIntros (v2 σ2 efs Hstep) "HL Hfc HLs Hcred".
  iMod ("H" $! v2 σ2 efs with "[# //] HL Hfc Hcred") as "H". iModIntro.
  iMod "H". iModIntro. iNext. iMod "H" as "(-> & ? & ?) /=". iModIntro.
  replace (τ ∪ dom ∅) with τ by set_solver. by iFrame.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork {s i E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, base_reducible e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
    base_step e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (|={E,E'}=> ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
                    ▷ (toL_thread i q L ={E',E}=∗ sfS_fuel_credit_forallL Λ -∗ £ 1 -∗
                    lWP e2 @ s; i; E {{ Φ }})) ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(lwp_lift_pure_det_step_no_fork e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma lwp_lift_pure_det_base_step_no_fork' {s i E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1 τ, base_reducible e1 σ1 τ) →
  (∀ σ1 κ τ e2' σ2 efs',
    base_step e1 σ1 τ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (|={E,∅}=> ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
                    ▷ (toL_thread i q L ={∅,E}=∗ sfS_fuel_credit_forallL Λ -∗ £ 1 -∗
                    lWP e2 @ s; i; E {{ Φ }})) ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(lWP e1 @ s; i; _ {{ _ }})%I]lwp_lift_pure_det_base_step_no_fork //.
Qed.
End wp.
