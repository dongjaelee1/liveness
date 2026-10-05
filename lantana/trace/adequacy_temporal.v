From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export adequacy_step guarantee_infer.
From lantana.base_logic Require Import satisfiable.

(** * Adequacy of [lWP] for temporal guarantees

    [lWP] is a running system with the one-step property ([sys_step_lwp]). Hence, if the
    initial resources guarantee [G], every fair run satisfies [tps_tr G]
    ([lwp_adequacy_temporal]). *)
Section adequacy.
  Context `{!lantanaGS Λ Σ}.

  (** The running system: every thread runs its [lwp_fix]. *)
  Definition threads_run (s : stuckness)
    (TQ : gmap thread_id ((expr Λ) * (thread_id → val Λ → iProp Σ))) : iProp Σ :=
    [∗ map] i ↦ '(e, Q) ∈ TQ, match to_val e with
                              | Some v => (lift_term i Q) v
                              | None => lwp_fix s i ⊤ e (lift_term i Q)
                              end.

  (** ** The fairness measure drops across a step *)
  Local Lemma obl_le_measure γ fu o fu' o' :
    obl_le (obl_assigned fu o) (obl_assigned fu' o') →
    (fair_sched_fun γ o' fu' <= fair_sched_fun γ o fu)%ord.
  Proof.
    intros [[Hle <-]|Hlt].
    - apply Hessenberg.le_add_l, Jacobsthal.le_mult_r. done.
    - apply Ord.lt_le, fair_sched_fun_mon_gen. done.
  Qed.

  (** Under [obls_le], an assigned obligation comes from an assigned one. *)
  Local Lemma obls_le_assigned_inv Ω Ω' k x fu' o' :
    obls_le Ω Ω' → Ω !! k = Some x → Ω' !! k = Some (obl_assigned fu' o') →
    ∃ fu o, x = obl_assigned fu o ∧ obl_le (obl_assigned fu o) (obl_assigned fu' o').
  Proof.
    intros [_ H] Hk Hk'. specialize (H _ _ _ Hk Hk'). destruct x as [fu o|]; [eauto|done].
  Qed.

  (** A step of the scheduled thread [i1]: its obligations lose fuel, the counters of the
      other active threads drop. *)
  Lemma obls_drop_step γ γ2 i1 (τ : trace Λ) Ω Ω0 Ω2 Ω' :
    obls_le Ω Ω0 → (Ω0 ↪ₚ Ω2 | obl_cond_owner i1) → obls_le Ω2 Ω' →
    obls_thread_active Ω2 τ → trace_thread τ = i1 → fscnt_next_rel τ γ γ2 →
    obls_drop (fair_sched_fun γ) (fair_sched_fun γ2) Ω Ω'.
  Proof.
    intros LEO0 [StepO _] LEO' OTA Hi FSrel k fu o fu' o' Hk Hk'.
    assert (Hk0 : ∃ x0, Ω0 !! k = Some x0).
    { destruct LEO0 as [Hdom _]. apply elem_of_dom, Hdom, elem_of_dom. eauto. }
    destruct Hk0 as [x0 Hk0].
    destruct LEO0 as [_ Hle0]. specialize (Hle0 _ _ _ Hk Hk0).
    specialize (StepO k). rewrite Hk0 in StepO.
    destruct (Ω2 !! k) as [x2|] eqn:Hk2; last by inv StepO.
    pose proof (obls_le_assigned_inv _ _ _ _ _ _ LEO' Hk2 Hk') as (fu2& o2& ->& Hle2).
    apply (obl_le_measure γ2) in Hle2.
    destruct x0 as [fu0 o0|]; last first.
    { inv StepO. match goal with H : _ ∨ _ |- _ => destruct H as [[HC _]|[_ Heq]]; [simpl in HC; done|done] end. }
    apply (obl_le_measure γ) in Hle0.
    inv StepO. match goal with H : _ ∨ _ |- _ => destruct H as [[HC Hstep]|[HC Heq]] end.
    - simpl in HC. subst o0.
      inv Hstep; match goal with H : obl_progress _ _ |- _ => inv H | H : obl_discharge _ _ |- _ => inv H end.
      eapply Ord.le_lt_lt; first exact Hle2. eapply Ord.lt_le_lt; last exact Hle0.
      apply fair_sched_fun_mon_gen. done.
    - inv Heq. simpl in HC.
      pose proof (OTA k _ Hk2) as TA. simpl in TA.
      specialize (FSrel o2). unfold fscnt_next_rel_th in FSrel.
      rewrite decide_False in FSrel; last by intros ->.
      rewrite decide_False in FSrel; last by intros F; eapply thread_active_and_not_false.
      eapply Ord.le_lt_lt; first exact Hle2. eapply Ord.lt_le_lt; last exact Hle0.
      apply Hessenberg.lt_add_r, OrdArith.lt_from_nat. done.
  Qed.

  (** A step of a finished thread: it owns nothing, every counter drops. *)
  Lemma obls_drop_na γ γ2 (τ : trace Λ) Ω :
    ts_emb (thread_na (trace_thread τ)) τ → obls_thread_active Ω τ → fscnt_next_rel τ γ γ2 →
    obls_drop (fair_sched_fun γ) (fair_sched_fun γ2) Ω Ω.
  Proof.
    intros TNA OTA FSrel k fu o fu' o' Hk Hk'. rewrite Hk in Hk'. inv Hk'.
    pose proof (OTA k _ Hk) as TA. simpl in TA.
    specialize (FSrel o'). unfold fscnt_next_rel_th in FSrel.
    rewrite decide_False in FSrel; last by intros ->; eapply thread_active_and_not_false.
    rewrite decide_False in FSrel; last by intros F; eapply thread_active_and_not_false.
    apply Hessenberg.lt_add_r, OrdArith.lt_from_nat. done.
  Qed.

  (** ** One step of the run

      From a consistent system at [n]: the system at [S n], the facts about the step, and
      later credits for the continuation (which may use fancy updates). *)
  Lemma run_step (c : nat) s h n σ Θ TQ κs g v Ω W τf γ (Φ : iProp Σ) :
    ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
     hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
    (history_tinterp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W n (dom Θ) ∗ threads_run s TQ -∗
    (∀ σ' Θ' κs' TQ' g' v' Ω' W' γ',
       ⌜behavior (S n, τf) ∧ beh_fscnt (S n, τf) γ' ∧ owit_inv_lb (fair_sched_fun γ') Ω' W' ∧
        hist_trace (h ++ [(σ', Θ', κs')]) τf ∧ Θ' = fst <$> TQ' ∧
        obls_drop (fair_sched_fun γ) (fair_sched_fun γ') Ω Ω'⌝ -∗
       £n c -∗
       (history_tinterp (h ++ [(σ', Θ', κs')]) (S n) σ' Θ' κs' ∗ state_interp_aux σ' Θ' κs') ∗
       model_interp g' v' Ω' W' (S n) (dom Θ') ∗ threads_run s TQ' -∗
       |={⊤}=> Φ) -∗
    |={⊤,∅}=> ALC (|={∅,⊤}=> Φ).
  Proof.
    iIntros "%H ([[HI TI] SIa]& MI& WPs) K". destruct H as (BEH& FS& LB& HIST& EQTQ). rewrite /threads_run.
    inversion BEH. clear BEH. subst n0 τf0.
    iPoseProof (history_interp_lookup with "HI") as "%LUhn". apply HIST in LUhn. destruct LUhn as (i'&LUhn).
    rewrite H1 in LUhn. inversion LUhn. clear LUhn. subst ρ1 i' κs.
    rename κs0 into κs, H1 into TRn, H3 into TRn1, H4 into BEH'.
    iAssert ([∗ map] i ↦ e ∈ Θ, match to_val e with | Some _ => (thP_done i) | None => True end)%I as "#THs".
    { subst. iApply big_sepM_fmap. iApply (big_sepM_impl with "WPs").
      iIntros "!> %%% H". destruct x. simpl. destruct (to_val e); auto. iDestruct "H" as "[$ _]". }
    iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    destruct H2 as [TStep | TDone].
    - iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TStep. clear TStep. inversion H. clear H. subst Θ0 σ ρ2. rename H1 into PStep, H0 into LUTi1.
      assert (LUTQi1 : ∃ Q, TQ !! i1 = Some (e1, Q)).
      { subst Θ. rewrite lookup_fmap_Some in LUTi1. destruct LUTi1 as (?&?&?). destruct x. subst. eauto. }
      destruct LUTQi1 as (Q& LUTQi1). iPoseProof (big_sepM_delete _ _ _ _ LUTQi1 with "WPs") as "[WP WPs]".
      pose proof (val_stuck _ _ _ _ _ _ _ _ PStep) as He1. rewrite He1.
      iPoseProof (lwp_fix_unfold_fix with "WP") as "WP". rewrite /lwp_pre He1 /lwp_step.
      iSpecialize ("WP" $! ctx_id). iEval (rewrite !ctx_id_apply) in "WP".
      iMod ("WP" with "[] [//] [$HI $TI $SIa]") as "WP".
      { iPureIntro. apply _. }
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
      iMod (model_interp_mupd_steps with "WP MI") as "(WP& %g0& %v0& %Ω0 & %W0& %& MI)".
      2: eapply LB.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [LEO0 LB0].
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv0".
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA0". 1,2: eauto.
      iDestruct "WP" as "[%NStuck WP]".
      iPoseProof ("WP" with "[//]") as "WP".
      iEval (rewrite !ctx_id_apply) in "WP". rewrite /mprog.
      iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
      assert (TNow : trace_thread (n, τf) = i1).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      pose proof (mprog_exists_step i1 Ω0 Ω2 W0 (n, τf) γ (eq_sym TNow) OTA0 OWinv0 LB0 FS ProgO) as H.
      destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
      iMod ("WP" $! W2 with "[]") as "[MI WP]".
      { iPureIntro. split; auto. }
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA2". 1,2: eauto.
      rewrite /mphys. iMod ("WP" with "MI") as "[MI WP]". iModIntro.
      rewrite (ALC_credits _ _ (Ord.from_nat c) (|={∅,⊤}=> Φ)%I). iMod "WP". iIntros "LC". simpl.
      iMod (model_interp_mupd_steps with "WP MI") as "(WP& %g'& %v'& %Ω3& %W3& %& MI)".
      2: eapply LB2.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [LEO LB3]. iMod "WP" as "(HI& WP& Efs)".
      unfold trace_next in *. simpl in *. assert (TDisj : Θ ##ₘ efs).
      { eapply map_disjoint_dom_2, fork_thread_ids; eauto. }
      remember ((<[i1:=e2]> Θ) ∪ efs) as Θ2.
      replace (dom (<[i1:=e2]> Θ) ∪ dom efs) with (dom Θ2); cycle 1.
      { subst Θ2. rewrite dom_union_L. auto. }
      remember ((λ e, (e, fork_post)) <$> efs : gmap thread_id (expr Λ * (thread_id → val Λ → iProp Σ))) as TQefs.
      iAssert ([∗ map] j ↦ '(e, Q) ∈ TQefs, (|={⊤}=>m (match to_val e with
                                                          | Some v => lift_term j Q v
                                                          | None => lwp_fix s j ⊤ e (lift_term j Q)
                                                          end)))%I with "[Efs]" as "Efs".
      { subst TQefs. iApply big_sepM_fmap. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% WP".
        destruct (to_val x) eqn:EQx.
        - rewrite lwp_fix_unfold_fix /lwp_pre EQx. iApply sfmupd_trans. iApply "WP".
        - iApply "WP". }
      iDestruct "HI" as "[HIT SIa]".
      iMod (all_interp_sfmupd_steps_gmap γ2 with "Efs HIT MI") as "(Efs& HIT& %g2& %v2& %Ω4& %W4& %& MI)".
      1: auto. destruct H as [LEO2 LB4].
      assert (EQTQ2 : Θ2 = fst <$> (<[i1:=(e2, Q)]> TQ ∪ TQefs)).
      { subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
      assert (TQDisj : <[i1:=(e2, Q)]> TQ ##ₘ TQefs).
      { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
        apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
      iDestruct "HIT" as "[HI TI]".
      iPoseProof (history_interp_wf with "HI") as "%HistWF".
      assert (HIST' : hist_trace (h ++ [(σ2, Θ2, κs)]) τf).
      { intros n' σ' Θ' κs' H. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
        - inv H. eapply HIST in LUh. eauto.
        - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
          inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
          destruct HistWF as [Hlen _]. rewrite length_app in Hlen. simpl in Hlen.
          assert (Hh : length h = S n) by lia. rewrite Hh TRn1. eauto. }
      destruct (to_val e2) eqn:He2.
      + rewrite lwp_fix_unfold_fix /lwp_pre He2.
        iMod (all_interp_sfmupd_steps (fair_sched_fun γ2) with "WP [$HI $TI] MI") as "(WP& [HI TI]& %g3& %v3& %Ω5& %W5& %& MI)".
        { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
        1: eapply LB4. destruct H as [LEO3 LB5].
        iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix s j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union; first done.
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iApply ("K" with "[%] LC [$HI $TI $SIa $MI $WPs]"). split_and!; eauto.
        eapply (obls_drop_step _ _ i1 (n, τf) _ Ω0 Ω2); eauto.
        etrans; first exact LEO. etrans; [exact LEO2|exact LEO3].
      + iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix s j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union; first done.
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iApply ("K" with "[%] LC [$HI $TI $SIa $MI $WPs]"). split_and!; eauto.
        eapply (obls_drop_step _ _ i1 (n, τf) _ Ω0 Ω2); eauto.
        etrans; [exact LEO|exact LEO2].
    - iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TDone. clear TDone. inversion H. clear H. subst Θ0 σ1 ρ2.
      destruct H1 as (He1&<-&<-&->&->). destruct He1 as [v1 He1]. simpl in *.
      rewrite map_union_empty insert_id in TRn1. 2: auto.
      iPoseProof (history_interp_step with "HI") as "[SI ACC]". iMod ("ACC" with "SI") as "HI".
      pose proof (exists_fscnt_next _ _ FS). destruct H as (γ2& FS2& FSrel).
      unfold trace_next in *. simpl in *.
      assert (TNow : trace_thread (n, τf) = i1).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      assert (TNA : ts_emb (thread_na i1) (n, τf)).
      { unfold ts_emb, thread_na. simpl. rewrite TRn. right. eauto. }
      rewrite -TNow in TNA. pose proof (owit_inv_lb_step_na_turn _ _ _ _ _ TNA OTA LB FSrel) as LB2.
      iDestruct "MI" as "[MHI MI]". iMod (model_history_interp_step _ _ _ (S n) with "MHI") as "MHI".
      1: lia. 1: reflexivity.
      iPoseProof (history_interp_wf with "HI") as "%HistWF".
      assert (HIST' : hist_trace (h ++ [(σ, Θ, κs)]) τf).
      { intros n' σ' Θ' κs' H. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
        - inv H. eapply HIST in LUh. eauto.
        - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
          inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
          destruct HistWF as [Hlen _]. rewrite length_app in Hlen. simpl in Hlen.
          assert (Hh : length h = S n) by lia. rewrite Hh TRn1. eauto. }
      iApply fupd_mask_intro. 1: set_solver. iIntros "close".
      rewrite (ALC_credits _ _ (Ord.from_nat c) (|={∅,⊤}=> Φ)%I). iApply ALC_intro. iIntros "LC". iMod "close" as "_".
      iApply ("K" with "[%] LC [$HI $TI $SIa $MHI $MI $WPs]"). split_and!; eauto.
      eapply obls_drop_na; eauto.
  Qed.

  (** ** The one-step property for [lWP]

      The system: the auxiliary state interpretation, the registry state and the running
      threads. A step: the check, then [run_step]. *)
  Definition sys_lwp (s : stuckness) : nat → state Λ → thread_pool Λ → list (observation Λ) → iProp Σ :=
    λ _ σ Θ κs, (state_interp_aux σ Θ κs ∗ treg_state ∗ ∃ TQ, ⌜Θ = fst <$> TQ⌝ ∗ threads_run s TQ)%I.

  Lemma sys_step_lwp s : ⊢ sys_step (sys_lwp s).
  Proof.
    rewrite /sys_step /sys_step_pre.
    iIntros "!>" (c h n σ Θ κs g v Ω W τf γ) "%H (HI& MI& SIa& TI& %TQ& %EQTQ& WPs)".
    destruct H as (BEH& FS& LB& HIST).
    iMod (treg_check n with "TI HI MI") as "(TI& HI& MI& %l& #B)".
    iApply fupd_mask_intro; first set_solver. iIntros "close". iExists l. iFrame "B".
    iNext. iMod "close" as "_". iModIntro.
    iApply (run_step c s with "[%] [$HI $TI $SIa $MI $WPs]"); first by split_and!.
    iIntros (σ' Θ' κs' TQ' g' v' Ω' W' γ') "%Hstep LC ([[HI TI] SIa]& MI& WPs)".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& EQTQ'& DROP).
    iModIntro. iExists σ', Θ', κs', g', v', Ω', W', γ'. rewrite /sys_lwp.
    iFrame "LC HI MI SIa TI". iSplit; first (iPureIntro; split_and!; done). iExists TQ'. by iFrame.
  Qed.

  (** The program logic from position [n]: check, step, and eliminate the record of the
      initial formula. *)
  Lemma lwp_ti_logic_temporal s h n σ Θ (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)) κs g v Ω W τf γ
    (G : tps Λ Σ) :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    owit_inv_lb (fair_sched_fun γ) Ω W →
    hist_trace h τf →
    ((history_tinterp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗
      model_interp g v Ω W n (dom Θ) ∗
      (|={⊤}=>m ∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                  (P -∗ |={⊤}=>m [∗ map] i↦e;Ψ ∈ Θ;Ψs, lWP e @ s; i; ⊤ {{ v, lift_term i Ψ v }})))
      ⊢ |={⊤,∅}=> ALC (|={∅,⊤}=> tps_ti G (n, τf)).
  Proof.
    iIntros (BEH FS LB HIST) "([HI SIa]& MI& WPs)".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "((%P& #HG& HP& WPs)& [HI TI]& %&%&%&%& %H& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO1 LB1].
    iPoseProof (temporal_elim with "HG [$HI $MI $HP]") as "#TF".
    iPoseProof ("WPs" with "HP") as "WPs".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs [$HI $TI] MI") as "(WPs& [HI TI]& %&%&%&%& %H& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO2 LB2].
    iPoseProof (big_sepM2_alt with "WPs") as "[%Dom WPs]".
    remember (map_zip Θ Ψs) as TQ. assert (EQTQ : Θ = fst <$> TQ).
    { subst. rewrite fst_map_zip; auto. intro k. rewrite -!elem_of_dom Dom. auto. }
    iAssert ([∗ map] i↦'(e, Q) ∈ TQ,
               (|={⊤}=>m (match to_val e with
                             | Some v => (lift_term i Q) v
                             | None => lwp_fix s i ⊤ e (lift_term i Q)
                             end)))%I with "[WPs]" as "WPs".
    { iApply (big_sepM_impl with "WPs"). iIntros "!> %%% H". destruct x as [e Q]. simpl.
      rewrite lwp_unfold_fix. destruct (to_val e) eqn:He.
      - by iEval (rewrite lwp_fix_unfold_fix /lwp_pre He) in "H".
      - by iApply sfmupd_intro. }
    iMod (all_interp_sfmupd_steps_gmap γ with "WPs [$HI $TI] MI") as "(WPs& [HI TI]& %&%&%&%& %H& MI)".
    { auto. }
    destruct H as [LEO3 LB3].
    (* the check at [n] *)
    iMod (treg_check n with "TI HI MI") as "(TI& HI& MI& %l& #B)".
    iApply (run_step 0 s with "[%] [$HI $TI $SIa $MI $WPs]"); first by split_and!.
    iIntros (σ2 Θ2 κs2 TQ2 g2 v2 Ω2 W2 γ2) "%Hstep LC' ([[HI TI] SIa]& MI& WPs)".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& EQTQ'& DROP).
    iModIntro. iApply (tguar_elim _ (sys_lwp s) with "TF [] [%] B [$HI $MI SIa TI WPs]").
    { iApply sys_step_lwp. }
    { split_and!; done. }
    rewrite /sys_lwp. iFrame "SIa TI". iExists TQ2. by iFrame.
  Qed.

End adequacy.

(** The program logic establishes [G]; anything implied by its trace property holds. *)
Theorem lwp_adequacy_temporal (Σ : gFunctors) (Λ : language)
  `{!mupdGpreS Σ} `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
  s σ Θ i κs (G : tps Λ Σ) (R : trProp Λ) :
  (∀ τ, tps_tr G τ → R τ) →
  ∀ (τ : trace Λ),
  behavior τ →
  fair_scheduling τ →
  (τ.1 = 0) →
  (τ.2 0 = (Θ, σ, i, κs)) →
  (∀ `{Htemporal : !temporalGS Λ Σ},
     ∃ (c : Ord.t),
     ⊢ |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                (fork_post : thread_id → val Λ → iProp Σ)
                (Ψs : gmap thread_id (H:=pos_countable) (thread_id → val Λ → iProp Σ)),
     let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
     state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
     (£ c -∗ ([∗ set] i ∈ dom Θ, thP_kids i ∅) -∗
      |={⊤}=>m (∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                  (P -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lWP e @ s; i; ⊤ {{ lift_term i Ψ }})))) →
  R τ.
Proof.
  intros HR τ BEH FS INIT1 INIT2 Hwp. apply HR.
  assert (iProp_sat
            (|==> ∃ (Hmupd : mupdGS Σ) (Hhist : histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ)))
                    (Htreg : tregGS.tregGS Λ Σ),
                let _ : temporalGS Λ Σ := TemporalG Hmupd Hhist Htreg in
                (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗
                wsat.wsat ∗ wsat.ownE ⊤ ∗
                |={⊤,∅}=> ALC (|={∅,⊤}=> tps_ti G τ))) as Hsat; cycle 1.
  { apply sat_bupd, sat_exists in Hsat. destruct Hsat as (Hmupd& Hsat).
    apply sat_exists in Hsat. destruct Hsat as (Hhist& Hsat).
    apply sat_exists in Hsat. destruct Hsat as (Htreg& Hsat).
    set (Htemp := TemporalG Hmupd Hhist Htreg : temporalGS Λ Σ).
    apply (tps_good G (temporalGS0:=Htemp) emp).
    apply (sat_fupd ∅), sat_ALC, (sat_fupd ⊤).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono. 2: eapply Hsat. simpl. iIntros "($& $& $& $)". }
  assert (Hwp' : ⊢ ∀ Htemporal : temporalGS Λ Σ,
            ∃ (c : Ord.t),
            |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                     (fork_post : thread_id → val Λ → iProp Σ)
                     (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)),
            let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
            state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
            (£ c -∗ ([∗ set] i ∈ dom Θ, thP_kids i ∅) -∗
             |={⊤}=>m (∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                         (P -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lWP e @ s; i; ⊤ {{ lift_term i Ψ }})))).
  { iIntros (Htemp). destruct (Hwp Htemp) as [x Hx]. iExists x. iApply Hx. }
  eapply sat_wand; cycle 1.
  { eapply Hwp'. }
  apply (sat_mono True); cycle 1.
  { apply iProp_sat_intro. }
  iIntros "_ H".
  iMod (model_interp_alloc 0) as "(%Hmupd& R& W& WOE& MI)".
  iMod (history_interp_init σ Θ κs) as "(%Hhist& HI)".
  iMod (treg_alloc (Λ:=Λ)) as "(%Htreg& TR)".
  iExists Hmupd, Hhist, Htreg.
  set (Htemp := TemporalG Hmupd Hhist Htreg : temporalGS Λ Σ).
  iDestruct ("H" $! Htemp) as "(%c& H)".
  iDestruct "R" as "(%x& R)".
  iMod (own_update _ (● x) with "R") as "[R LC]".
  { apply (auth_update_alloc x (c ⋅ x)).
    apply (op_local_update_discrete x ε c).
    intros ?. apply auth_valid_trivial. }
  iModIntro. iFrame "R W WOE". rewrite (right_id ε).
  iMod "H" as "(%Hsic& %fork_post& %Ψs& SI& SIa& WPs)".
  iMod ("HI" $! Hsic with "SI") as "HI". iDestruct "MI" as "(MHI& S& T& A& G& MI)".
  iMod (thP_kids_alloc_threads _ (dom Θ) with "[$T $G]") as "(T& G& Ths)". 1: set_solver.
  set (Hlantana := LantanaG Htemp Hsic fork_post : lantanaGS Λ Σ).
  iPoseProof (treg_st_init (treg_handle (temporalGS0:=Htemp)) with "TR") as "TI".
  iPoseProof ("WPs" with "LC Ths") as "WPs". rewrite union_empty_l_L.
  destruct τ as [n τf]. simpl in INIT1, INIT2. subst n.
  apply fair_scheduling_fscnt in FS. destruct FS as (γ& FS).
  iApply (lwp_ti_logic_temporal (lantanaGS0:=Hlantana) with "[$HI $TI $SIa $MHI $S $T $A $G $MI $WPs]").
  1,2: eauto. 1: apply map_Forall2_empty.
  { intros n' σ' Θ' κs' Hlu. rewrite lookup_cons in Hlu. destruct n'; last done. inv Hlu. rewrite INIT2. eauto. }
Qed.
