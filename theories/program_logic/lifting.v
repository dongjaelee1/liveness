(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From liveness.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{SI : indexT} `{!lirisGS_gen hlc Λ Σ}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma lwp_lift_step_fupdN s i E Φ e1 :
  to_val e1 = None →
  (∀ δ1 (Ω1 : obl_statesL Λ) γ1 σ1 ns κ κs τ,
     (schedfairIL Λ δ1 ∗ osat Ω1 ∗ toIL Λ γ1 ∗ oftIL Λ Ω1 δ1 γ1 ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
     ⌜if s is NotStuck then reducible e1 σ1 τ else True⌝ ∗ ∃ Ω2,
       (⌜(Ω1 ↪ₛ⋆ Ω2 @ σ1)⌝) ∗ ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗ ∀ δ2 δ3,
     (⌜fuels_fair_update {[i]} δ1 δ2 ∧ fuels_fair_fork efs δ2 δ3⌝) -∗
     £ (S $ num_laters_per_step ns) ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
     ∃ Ω3 Ω4, (⌜(Ω2 ↪ₚ⁺ Ω3 @ σ2) ∧ (Ω3 ↪ₛ⋆ Ω4 @ σ2)⌝) ∗
              ∃ γ2, (schedfairIL Λ δ3 ∗ osat Ω4 ∗ toIL Λ γ2 ∗ oftIL Λ Ω4 δ3 γ2 ∗ state_interp σ2 (S ns) κs (τ ∪ dom efs)) ∗
                    lWP e2 @ s; i; E {{ Φ }} ∗
                                   [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof. by rewrite lwp_unfold /lwp_pre /lwp_step =>->. Qed.

Lemma lwp_lift_step_fupd s i E Φ e1 :
  to_val e1 = None →
  (∀ δ1 (Ω1 : obl_statesL Λ) γ1 σ1 ns κ κs τ,
     (schedfairIL Λ δ1 ∗ osat Ω1 ∗ toIL Λ γ1 ∗ oftIL Λ Ω1 δ1 γ1 ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
     ⌜if s is NotStuck then reducible e1 σ1 τ else True⌝ ∗ ∃ Ω2,
       (⌜(Ω1 ↪ₛ⋆ Ω2 @ σ1)⌝) ∗ ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗ ∀ δ2 δ3,
     (⌜fuels_fair_update {[i]} δ1 δ2 ∧ fuels_fair_fork efs δ2 δ3⌝) -∗
     £ 1 ={∅}=∗ ▷ |={∅,E}=>
     ∃ Ω3 Ω4, (⌜(Ω2 ↪ₚ⁺ Ω3 @ σ2) ∧ (Ω3 ↪ₛ⋆ Ω4 @ σ2)⌝) ∗
              ∃ γ2, (schedfairIL Λ δ3 ∗ osat Ω4 ∗ toIL Λ γ2 ∗ oftIL Λ Ω4 δ3 γ2 ∗ state_interp σ2 (S ns) κs (τ ∪ dom efs)) ∗
                    lWP e2 @ s; i; E {{ Φ }} ∗
                                   [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "Hlwp". rewrite -lwp_lift_step_fupdN; [|done].
  iIntros (????????) "Hσ". iMod ("Hlwp" with "Hσ") as "($ & (% & % & Hlwp))".
  iModIntro. iExists _. iSplit; first done. iIntros (??? ? ?? ?) "Hcred".
  iPoseProof (lc_weaken 1 with "Hcred") as "Hcred"; first lia.
  simpl. rewrite -step_fupdN_intro; [|done]. rewrite -bi.laterN_intro.
  iMod ("Hlwp" with "[//] [//] Hcred") as "Hlwp".
  iApply step_fupd_intro; done.
Qed.

Lemma lwp_lift_stuck i E Φ e :
  to_val e = None →
  (∀ δ1 (Ω1 : obl_statesL Λ) γ1 σ1 ns κ κs τ,
     (schedfairIL Λ δ1 ∗ osat Ω1 ∗ toIL Λ γ1 ∗ oftIL Λ Ω1 δ1 γ1 ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
     ⌜ stuck e σ1 τ ⌝)
  ⊢ lWP e @ i; E ?{{ Φ }}.
Proof.
  rewrite lwp_unfold /lwp_pre /lwp_step =>->. iIntros "H" (??? σ1 ns κ κs nt) "Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iExists Ω1. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.

(** Derived lifting lemmas. *)
Lemma lwp_lift_step s i E Φ e1 :
  to_val e1 = None →
  (∀ δ1 (Ω1 : obl_statesL Λ) γ1 σ1 ns κ κs τ,
     (schedfairIL Λ δ1 ∗ osat Ω1 ∗ toIL Λ γ1 ∗ oftIL Λ Ω1 δ1 γ1 ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
     ⌜if s is NotStuck then reducible e1 σ1 τ else True⌝ ∗ ∃ Ω2,
       (⌜(Ω1 ↪ₛ⋆ Ω2 @ σ1)⌝) ∗ ▷ ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗ ∀ δ2 δ3,
     (⌜fuels_fair_update {[i]} δ1 δ2 ∧ fuels_fair_fork efs δ2 δ3⌝) -∗
     £ 1 ={∅,E}=∗
     ∃ Ω3 Ω4, (⌜(Ω2 ↪ₚ⁺ Ω3 @ σ2) ∧ (Ω3 ↪ₛ⋆ Ω4 @ σ2)⌝) ∗
              ∃ γ2, (schedfairIL Λ δ3 ∗ osat Ω4 ∗ toIL Λ γ2 ∗ oftIL Λ Ω4 δ3 γ2 ∗ state_interp σ2 (S ns) κs (τ ∪ dom efs)) ∗
                    lWP e2 @ s; i; E {{ Φ }} ∗
                                   [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_step_fupd; [done|]. iIntros (????????) "Hσ".
  iMod ("H" with "Hσ") as "[$ (%&%&H)]". iModIntro. iExists _. iSplit; first done.
  iIntros (??? ? ?? ?) "Hcred !> !>". by iApply "H".
Qed.

Lemma lwp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s i E E' Φ e1 :
  (∀ σ1 τ, if s is NotStuck then reducible e1 σ1 τ else to_val e1 = None) →
  (∀ κ σ1 τ e2 σ2 efs, prim_step e1 σ1 τ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
  (|={E}[E']▷=> ∀ κ τ e2 efs σ, ⌜prim_step e1 σ τ κ e2 σ efs⌝ -∗ £ 1 -∗ lWP e2 @ s; i; E {{ Φ }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply lwp_lift_step.
  { specialize (Hsafe inhabitant ∅). destruct s; eauto using reducible_not_val. }
  iIntros (??? σ1 ns κ κs τ) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. destruct s; done. }
  iExists Ω1. iSplit; first done.
  iNext. iIntros (e2 σ2 efs ? ?? ?) "Hcred".
  destruct (Hstep κ σ1 τ e2 σ2 efs) as (-> & <- & ->); auto.
  iDestruct "Hσ" as "(H0 & H1 & H2 & H3 & Hσ)". replace (τ ∪ dom ∅) with τ by set_solver.
  iMod (state_interp_mono with "Hσ") as "$". iMod "Hclose" as "_". iMod "H". iModIntro.
  TODO
    (* We need to consume progress credits and use sched fairness and pcreds to prove progress of Ω. *)
  by iDestruct ("H" with "[//] Hcred") as "$".
Qed.

Lemma lwp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  True ⊢ LWP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply lwp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma lwp_lift_atomic_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ 1 ={E1}[E2]▷=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, LWP ef @ s; ⊤ {{ fork_post }})
  ⊢ LWP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (lwp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 efs ?) "Hcred". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#] Hcred") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply lwp_value; last done. by apply of_to_val.
Qed.

Lemma lwp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ 1 ={E}=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, LWP ef @ s; ⊤ {{ fork_post }})
  ⊢ LWP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_step_fupd; [done|].
  iIntros (?????) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "Hcred !> !>".
  by iApply "H".
Qed.

Lemma lwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E E' Φ} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> £ 1 -∗ LWP e2 @ s; E {{ Φ }}) ⊢ LWP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (lwp_lift_pure_step_no_fork s E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

Lemma lwp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n £ n -∗ LWP e2 @ s; E {{ Φ }}) ⊢ LWP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hlwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
  { iMod lc_zero as "Hz". by iApply "Hlwp". }
  iApply lwp_lift_pure_det_step_no_fork.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - done.
  - iApply (step_fupd_wand with "Hlwp").
    iIntros "Hlwp Hone". iApply "IH".
    iApply (step_fupdN_wand with "Hlwp").
    iIntros "Hlwp Hc". iApply ("Hlwp" with "[Hone Hc]").
    rewrite (lc_succ n). iFrame.
Qed.

Lemma lwp_pure_step_later `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n (£ n -∗ LWP e2 @ s; E {{ Φ }}) ⊢ LWP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -lwp_pure_step_fupd //. clear Hexec.
  enough (∀ P, ▷^n P ⊢ |={E}▷=>^n P) as Hlwp by apply Hlwp. intros ?.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
