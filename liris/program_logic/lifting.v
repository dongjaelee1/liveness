(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From liris.program_logic Require Export weakestpre.
(* From iris.prelude Require Import options. *)
From liris.algebra Require Import ordinal_wfocm.

Section lifting.
  Context `{SI : indexT} `{!lirisGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Local Ltac unfold_defs :=
    try rewrite !gupd.wit_fuels_unseal /gupd.wit_fuels_def;
    try rewrite !gupd.wit_unseal /gupd.wit_def;
    try rewrite !gupd.wit_layer_unseal /gupd.wit_layer_def;
    try rewrite !gupd.wit_bound_unseal /gupd.wit_bound_def;
    try rewrite !gupd.th_term_unseal /gupd.th_term_def;
    try rewrite !gupd.th_obls_unseal /gupd.th_obls_def;
    try rewrite !gupd.gl_variant_cases_unseal /gupd.gl_variant_cases_def;
    try rewrite !gupd.gl_variant_unseal /gupd.gl_variant_def;
    try rewrite !gupd.gl_fuel_unseal /gupd.gl_fuel_def;
    try rewrite !gupd.gl_fuel_val_unseal /gupd.gl_fuel_val_def;
    try rewrite !gupd.gl_expired_unseal /gupd.gl_expired_def;
    try rewrite !gupd.gl_current_unseal /gupd.gl_current_def;
    try rewrite !gupd.gl_done_unseal /gupd.gl_done_def;
    try rewrite !gupd.gl_locked_unseal /gupd.gl_locked_def;
    try rewrite !gupd.gl_layer_unseal /gupd.gl_layer_def;
    try rewrite !gupd.gl_unseal /gupd.gl_def.

  Section lwp_step.

    (* For lwp_step, enable progress and fork. *)
    Lemma lwp_step_step s i E e1 ν :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
         (⌜ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0 1) ∗
         ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
           (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
              th_obls i G 1 -∗
              ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗
              ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
              ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs)))
      ⊢ lwp_step s i E e1 ν.
    Proof.
      iIntros "H". iIntros (????) "SI".
      iMod ("H" with "SI") as "($& %& GOs& GFs& %& #REs& H)".
      iIntros "!> !> % % % %Step".
      iApply (gprog_step Θ _ (dom efs)).
      1: auto.
      { eapply fork_thread_ids; eauto. }
      iModIntro. iFrame "GOs GFs REs". iIntros "(GOs& Ws& Efs)".
      iMod ("H" with "[//] GOs Ws Efs") as "H". iModIntro.
      iMod "H". iModIntro. eauto.
    Qed.

  End lwp_step.

  Section lwp.

    Lemma lwp_lift_step s i E e1 Φ :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
         (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0 1) ∗
         ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
           (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
              th_obls i G 1 -∗
              ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗
              ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
              ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗
                            lWP e2 @ s; i; E {{ Φ }} ∗
                            [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})))
      ⊢ lWP e1 @ s; i; E {{ Φ }}.
    Proof.
      iIntros "H". rewrite lwp_unfold /lwp_pre. destruct (to_val e1) eqn:He.
      { iIntros "%%% I". iMod ("H" $! _ _ [] with "I") as "((%&%)& _)". done. }
      iApply lwp_step_step.
      iIntros (????) "I". iMod ("H" with "I") as "(%& H)". destruct H as [_ H].
      iModIntro. iSplitR; first done. auto.
    Qed.

  End lwp.

  Local Hint Resolve reducible_no_obs_reducible : core.

  Lemma lwp_lc_later_ord s i E e Φ :
    £ Ord.one -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". by iMod (lc_fupd_elim_later_ord with "LC H") as "H".
  Qed.
  Lemma lwp_lc_later s i E e Φ :
    £n 1 -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof. iApply lwp_lc_later_ord. Qed.
  Lemma lwp_lc_laterN n s i E e Φ :
    £n n -∗ (▷^n lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". iApply fupd_lwp. iApply (lc_fupd_add_laterN E E with "LC"). iNext. by iModIntro.
  Qed.

  Lemma lwp_lift_stuck i E Φ e :
    to_val e = None →
    (∀ Θ σ κs, state_interp σ Θ κs ={E,∅}=∗ |=[Θ]=>g ⌜ stuck i e σ Θ ⌝)
    ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    rewrite lwp_unfold /lwp_pre /lwp_step =>->. iIntros "H" (Θ σ κ κs) "Hσ".
    iMod ("H" with "Hσ") as "H". iModIntro. iMod "H" as %[? Hirr].
    iModIntro. iSplit; first done.
    iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
  Qed.

  (** Derived lifting lemmas. *)
  Class PureExecCond (C : thread_id → state Λ → Prop) ς (i : thread_id) :=
    pure_exec_cond : ∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝.

  Lemma lwp_lift_pure_step_no_fork s i E E' e1 Φ C ς :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
    PureExecCond C ς i →
    (|={E,E'}=>
       ς ∗
       ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0 1) ∗
       ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
         (ς -∗
          th_obls i G 1 -∗
          ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗
          ALC (|={E',E}=>
                 ∀ σ Θ κ e2 efs, (⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝) -∗
                                 lWP e2 @ s; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep HCC) "H".
    iApply lwp_lift_step. iIntros (Θ σ1 κ κs) "Hσ".
    iMod "H" as "[Hc (%& Tb& Gfs& %& #Rs& H)]". iPoseProof (HCC with "Hc Hσ") as "%HC".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. split.
      - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
      - destruct s; auto. }
    iExists _. iFrame "Tb Gfs". iExists _. iFrame "Rs".
    iIntros (e2 σ2 efs ?) "!> Tb Wcs Efs".
    destruct (Hstep κ σ1 Θ e2 σ2 efs HC) as (-> & <- & ->); auto.
    replace (Θ ∪ dom ∅) with Θ by set_solver.
    iMod ("H" with "Hc Tb Wcs [//]") as "H".
    iMod "Hclose" as "_". iMod "H". iModIntro. rewrite big_sepM_empty. iFrame.
  Qed.

  Lemma lwp_lift_pure_stuck `{!Inhabited (state Λ)} i E Φ e :
    (∀ σ τ, stuck i e σ τ) →
    True ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    iIntros (Hstuck) "_". iApply lwp_lift_stuck.
    - destruct(to_val e) as [v|] eqn:He; last done.
      rewrite -He. by case (Hstuck inhabitant ∅).
    - iIntros (???) "_". iApply fupd_mask_intro; auto with set_solver.
  Qed.

  Lemma lwp_lift_atomic_step {s i E1 E2 Φ} e1 :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
         (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0 1) ∗
         ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
           (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
              th_obls i G 1 -∗
              ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗
              ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
              ALC (|={E2,E1}=> state_interp σ2 (Θ ∪ dom efs) κs ∗
                            (from_option (λ v, |={E1}=>g (Φ v)) False (to_val e2)) ∗
                            [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})))
      ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (lwp_lift_step s i E1 e1).
    iIntros (Θ σ1 κ κs) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first auto.
    iDestruct "H" as "(%& Tb& Gfs& %& #Rs& H)".
    iExists _. iFrame "Tb Gfs". iExists _. iFrame "Rs".
    iIntros (????). iMod ("H" with "[//]") as "H".
    iIntros "!> Tb Wcs Efs". iMod ("H" with "Tb Wcs Efs") as "H".
    iMod "Hclose" as "_". iMod "H" as "($&Hq&$)".
    iModIntro. destruct (to_val e2) eqn:?; last by iExFalso.
    iApply lwp_value_sfgupd; last eauto. by apply of_to_val.
  Qed.

  Lemma lwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s i E E' Φ C ς} e1 e2 :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    PureExecCond C ς i →
    (|={E,E'}=>
       ς ∗
       ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0 1) ∗
       ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
         (ς -∗
          th_obls i G 1 -∗
          ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗
          ALC (|={E',E}=> lWP e2 @ s; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet HCC) "H". iApply (lwp_lift_pure_step_no_fork s i E E'); eauto.
    { naive_solver. }
    iMod "H" as "($& %& $& $& %& $& H)". iModIntro.
    iIntros "Hc Tb Wcs". iMod ("H" with "Hc Tb Wcs") as ">H".
    iIntros "!> % % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
  Qed.

  Lemma lwp_pure_step `{!Inhabited (state Λ)} (n : nat) (o : Ord.t) s i E E' e1 e2 φ Φ C ς :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς i →
    (Nat.iter n (λ P, |={E,E'}=>
                   ς ∗
                   ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0 1) ∗
                   ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
                   (ς -∗
                    th_obls i G 1 -∗
                    ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗
                    ALC (£ o ={E',E}=∗ P)))
       (lWP e2 @ s; i; E {{ Φ }}))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ HCC) "Hlwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
    { auto. }
    iApply (lwp_lift_pure_det_step_no_fork (E':=E')).
    - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
    - eauto.
    - iDestruct "Hlwp" as ">($& %& $& $& %& $& H)".
      iModIntro. iIntros "Hc Gb Wcs". iDestruct ("H" with "Hc Gb Wcs") as "H".
      iDestruct "H" as "(%& H)". iExists (o ⊕ x)%ord. iIntros "LC".
      iPoseProof (tlc_split with "LC") as "[LC LC2]".
      iMod ("H" with "LC2") as "H". iModIntro. iMod ("H" with "LC") as "H".
      iApply "IH". iModIntro. auto.
  Qed.

  Lemma lwp_pure_step_alt `{!Inhabited (state Λ)} (n : nat) G R (o : Ord.t) s i E E' e1 e2 φ Φ C ς :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς i →
    ([∗ map] r ↦ v ∈ R, gl r v) ∗
    (Nat.iter n (λ P, |={E,E'}=> ς ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0 1) ∗
                                (ς -∗ th_obls i G 1 -∗ ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ gl_done r v) -∗ ALC (£ o ={E',E}=∗ P))) (lWP e2 @ s; i; E {{ Φ }}))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec HΦ HCC) "(#Rs& LWP)".
    iApply (lwp_pure_step n o _ _ E E'). 1: auto.
    iStopProof. clear Hexec. pattern n. induction n.
    { simpl. iIntros "(#Rs& LWP)". auto. }
    simpl. iIntros "(#Rs& LWP)".
    iMod "LWP" as "($& $& $& LWP)". iFrame "Rs".
    iIntros "!> Hc TG Wcs". iMod ("LWP" with "Hc TG Wcs") as "LWP". iIntros "LC".
    iApply IHn. iFrame "Rs". iMod ("LWP" with "LC") as "LWP". iModIntro. iFrame "LWP".
  Qed.

  Lemma lwp_pure_step_simple `{!Inhabited (state Λ)} n G R (o : Ord.t) s i E e1 e2 φ Φ C ς :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς i →
    (ς ∗ th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g 0 n) ∗ ([∗ map] r ↦ v ∈ R, gl r v) ∗
     (ς -∗ th_obls i G 1 -∗ ([∗ map] r ↦ v ∈ R, wit r v n ∨ gl_done r v) -∗
      £ (o × n)%ord -∗ lWP e2 @ s; i ; E {{ Φ }}))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec HΦ HCC) "(Hc& TG& Gfs& #Rs& Hlwp)".
    iApply (lwp_pure_step n o _ _ E E). 1: auto.
    iStopProof. clear Hexec. pattern n. induction n.
    { iIntros "(#Rs& Hc& TG& Gfs& IH)". simpl.
      iMod tlc_zero as "Hz". iPoseProof (tlc_equiv Ord.O (o × 0)%ord with "Hz") as "Hz".
      { by rewrite Jacobsthal.mult_O_r. }
      iMod (gl_check_witnesses with "Rs") as "Ws".
      iApply ("IH" with "Hc TG [Ws] Hz").
      rewrite Ord.from_nat_O. done. }
    iIntros "(#Rs& Hc& TG& Gfs& IH)". simpl.
    iAssert (([∗ map] g↦_ ∈ G, gl_fuel g 0 n) ∗ ([∗ map] g↦_ ∈ G, gl_fuel g 0 1))%I with "[Gfs]" as "[Gfs Gf]".
    { rewrite !big_sepM_dom. iApply (gl_fuel_add_set).
      rewrite (gl_fuel_eq_set _ _ _ (n ⊕ 1)%M (S n)%M). 1: auto.
      rewrite measure_nat_S measure_add. by rewrite Hessenberg.add_comm. }
    iModIntro. iFrame "Hc TG Gf Rs". iIntros "Hc TG RWs".
    iIntros "!> LC !>". iApply IHn. iFrame "Rs Hc TG Gfs".
    iIntros "Hc TG Ws LC2". iApply ("IH" with "Hc TG [Ws RWs] [LC LC2]").
    { iCombine "Ws RWs" as "Ws". rewrite -big_sepM_sep. iApply (big_sepM_impl with "Ws").
      iIntros "!> %%% [[Wc1 | #Gd1] [Wc2 | #Gd2]]"; auto.
      iLeft. rewrite (wit_eq _ _ (n ⊕ Ord.one)%ord (S n)).
      - iApply wit_split. iFrame.
      - rewrite -Ord.from_nat_1 -Hessenberg.add_from_nat comm. done. }
    { rewrite (tlc_equiv (o × S n)%ord ((o × n) ⊕ o)%ord).
      - rewrite tlc_split. iFrame.
      - rewrite Ord.from_nat_S Jacobsthal.mult_S comm. done. }
  Qed.

End lifting.
