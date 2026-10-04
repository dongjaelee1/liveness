From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From lantana.program_logic Require Export language weakestpre.
From lantana.program_logic Require Export temporal_property.
From lantana.program_logic Require Export adequacy.
From lantana.program_logic Require Import temporal_guarantee.

From transfinite.stepindex Require Import ordinals.
(* From transfinite.base_logic Require Import satisfiable. *)
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.

From lantana.prelude Require Import axioms.

Local Definition safety_iris_tiProp `{!temporalGS Λ Σ} i Φ : tiProp Λ Σ :=
  ti_always (ti_pure True) (λ τ, (⌜ (ts_emb (not_stuck) ∧ ts_emb (if_term_val i Φ))%R τ ⌝)%I).

Section proof1.
  Context `{!temporalGS Λ Σ}.
  Implicit Type F : iProp Σ.

  Lemma safety_iris_tiProp_trProp F i Φ :
    ∀ (τ : trace Λ), iProp_sat_lc_at_frame F ⊤ (safety_iris_tiProp i Φ τ) → safety_iris i Φ τ.
  Proof.
    intros. cut (tr_always (tr_pure True ∧ (ts_emb not_stuck ∧ ts_emb (if_term_val i Φ)))%R τ).
    { unfold safety_iris, tr_always. destruct τ. intros. apply H0 in H1. by destruct H1. }
    eapply ti_always_tr_always; eauto. 1: done. simpl. intros. apply sat_elim in H0. auto.
  Qed.

End proof1.

Section proof2.
  Context `{!lantanaGS Λ Σ}.

  Lemma lwp_fix_safety_iris_tiProp
    h n σ Θ (TQ : gmap thread_id ((expr Λ) * (thread_id → val Λ → iProp Σ))) κs
    g v Ω1 Ω2 W τf γ (i : thread_id) (Φ : thread_id → val Λ → Prop) :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    obls_le Ω1 Ω2 →
    owit_inv_lb (fair_sched_fun γ) Ω2 W →
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    Θ = fst <$> TQ →
    (∃ e Q, TQ !! i = Some (e, Q) ∧ ∀ v, (Q i v ⊢ ⌜Φ i v⌝)) →
    ((history_tinterp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω2 W n (dom Θ) ∗
     ([∗ map] i ↦ '(e, Q) ∈ TQ, match to_val e with
                                | Some v => (lift_term i Q) v
                                | None => lwp_fix NotStuck i ⊤ e (lift_term i Q)
                                end))
    ⊢ safety_iris_tiProp i Φ (n, τf).
  Proof.
    iIntros (BEH FS LEO LB HIST EQTQ POST) "([[HI TI] SIa]& MI& WPs)".
    clear dependent Ω1. rename Ω2 into Ω.
    iRevert (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ POST) "HI TI SIa MI WPs".
    iLöb as "IH". iIntros (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ POST) "HI TI SIa MI WPs".
    rewrite /safety_iris_tiProp ti_always_unfold /ti_always_pre.
    iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext.
    iMod "close" as "_". iModIntro.
    (** Fetch the scheduled thread and take a step; the position is decided after it. *)
    inversion BEH. clear BEH. subst n0 τf0.
    iPoseProof (history_interp_lookup with "HI") as "%LUhn". apply HIST in LUhn. destruct LUhn as (i'&LUhn).
    rewrite H1 in LUhn. inversion LUhn. clear LUhn. subst ρ1 i' κs.
    rename κs0 into κs, H1 into TRn, H3 into TRn1, H4 into BEH.
    iAssert ([∗ map] i ↦ e ∈ Θ, match to_val e with | Some _ => (thP_done i) | None => True end)%I as "#THs".
    { subst. iApply big_sepM_fmap. iApply (big_sepM_impl with "WPs").
      iIntros "!> %%% H". destruct x. simpl. destruct (to_val e); auto. iDestruct "H" as "[$ _]". }
    iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    destruct H2 as [TStep | TDone].
    + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
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
      destruct H as [OND LB0].
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv0".
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA0". 1,2: eauto.
      iDestruct "WP" as "[%NStuck WP]".
      iPoseProof ("WP" with "[//]") as "WP".
      iEval (rewrite !ctx_id_apply) in "WP". rewrite /mprog.
      iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
      unshelve epose proof (mprog_exists_step i1 Ω0 Ω2 W0 (n, τf) γ _ OTA0 OWinv0 LB0 FS ProgO).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
      iMod ("WP" $! W2 with "[]") as "[MI WP]".
      { iPureIntro. split; auto. }
      rewrite /mphys. iMod ("WP" with "MI") as "[MI WP]". iModIntro.
      assert (SAFE : (ts_emb not_stuck ∧ ts_emb (if_term_val i Φ))%R (n, τf)).
      { rewrite /tr_and /ts_emb /not_stuck /if_term_val. simpl. rewrite !TRn. split; eauto.
        - eexists. split; eauto. rewrite He1. auto.
        - destruct (decide (i = i1)); auto. subst i1. eexists. split; eauto. rewrite He1. auto. }
      iMod "WP". simpl.
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
                                                          | None => lwp_fix NotStuck j ⊤ e (lift_term j Q)
                                                          end)))%I with "[Efs]" as "Efs".
      { subst TQefs. iApply big_sepM_fmap. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% WP".
        destruct (to_val x) eqn:EQx.
        - rewrite lwp_fix_unfold_fix /lwp_pre EQx. by iApply sfmupd_trans.
        - iApply "WP". }
      iDestruct "HI" as "[HI SIa]".
      iMod (all_interp_sfmupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)".
      1: auto. destruct H as [LEO2 LB4]. destruct (to_val e2) eqn:He2.
      * rewrite lwp_fix_unfold_fix /lwp_pre He2.
        iMod (all_interp_sfmupd_steps (fair_sched_fun γ2) with "WP HI MI") as "(WP& [HI TI]& %g3& %v3& %Ω5& %W5& %& MI)".
        { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
        1: eapply LB4.
        destruct H as [LEO3 LB5].
        iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix NotStuck j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union.
          { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
            apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        iPoseProof ("IH" with "[] [] [] [] [] [] HI TI SIa MI WPs") as "H".
        1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H1 TRn1. eauto. }
        { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
        { iPureIntro. destruct POST as (?&?& POSTLU& POST). destruct (decide (i = i1)).
          - subst i1. do 2 eexists. rewrite -insert_union_l lookup_insert_eq. split; eauto.
            rewrite LUTQi1 in POSTLU. simplify_eq. eauto.
          - rewrite -insert_union_l lookup_insert_ne; auto. exists x, x0. split; eauto.
            simplify_eq. apply lookup_union_Some_l. auto. }
        iModIntro. iSplit; first done. iSplit; first done. iFrame.
      * iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix NotStuck j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union.
          { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
            apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iDestruct "HI" as "[HI TI]".
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        iPoseProof ("IH" with "[] [] [] [] [] [] HI TI SIa MI WPs") as "H".
        1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H1 TRn1. eauto. }
        { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
        { iPureIntro. intros. destruct POST as (?&?& POSTLU& POST). destruct (decide (i = i1)).
          - subst i1. do 2 eexists. rewrite -insert_union_l lookup_insert_eq. split; eauto.
            rewrite LUTQi1 in POSTLU. simplify_eq. eauto.
          - rewrite -insert_union_l lookup_insert_ne; auto. exists x, x0. split; eauto.
            simplify_eq. apply lookup_union_Some_l. auto. }
        iModIntro. iSplit; first done. iSplit; first done. iFrame.
    + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
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
      destruct (decide (i = i1)).
      * subst i. assert (LUTQi1 : ∃ Q, TQ !! i1 = Some (e1, Q)).
        { subst Θ. rewrite lookup_fmap_Some in H0. destruct H0 as (?&?&?). destruct x. subst. eauto. }
        destruct LUTQi1 as (Q& LUTQi1). destruct POST as (?&?& POSTLU& POST). rewrite LUTQi1 in POSTLU.
        inversion POSTLU; clear POSTLU. subst x x0.
        iPoseProof (POST v1 with "[WPs]") as "%POSTval".
        { iPoseProof (big_sepM_delete _ _ _ _ LUTQi1 with "WPs") as "[WP WPs]".
          rewrite He1. iDestruct "WP" as "[_ $]". }
        iPoseProof ("IH" with "[] [] [] [] [] [] HI TI SIa [$MHI $MI] WPs") as "H".
        1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H2 TRn1. eauto. }
        1: eauto. 1: eauto.
        iApply fupd_mask_intro. 1: set_solver. iIntros "close". iApply ALC_intro. iMod "close" as "_".
        iModIntro. iSplit; first done. iSplit.
        { iPureIntro. rewrite /tr_and /ts_emb /not_stuck /if_term_val. simpl. rewrite !TRn. split; eauto.
          - eexists. split; eauto. rewrite He1. auto.
          - rewrite decide_True; auto. eexists. split; eauto. rewrite He1. auto. }
        iFrame.
      * iPoseProof ("IH" with "[] [] [] [] [] [] HI TI SIa [$MHI $MI] WPs") as "H".
        1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H2 TRn1. eauto. }
        1: eauto. 1: eauto.
        iApply fupd_mask_intro. 1: set_solver. iIntros "close". iApply ALC_intro. iMod "close" as "_".
        iModIntro. iSplit; first done. iSplit.
        { iPureIntro. rewrite /tr_and /ts_emb /not_stuck /if_term_val. simpl. rewrite !TRn. split; eauto.
          - eexists. split; eauto. rewrite He1. auto.
          - rewrite decide_False; auto. }
        iFrame.
  Qed.

  Lemma lwp_safety_iris_tiProp h n σ Θ (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)) κs g v Ω W τf γ
    (i : thread_id) (Φ : thread_id → val Λ → Prop) :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    owit_inv_lb (fair_sched_fun γ) Ω W →
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    (∃ Q, Ψs !! i = Some Q ∧ ∀ v, (Q i v ⊢ ⌜Φ i v⌝)) →
    ((history_tinterp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗
     model_interp g v Ω W n (dom Θ) ∗
     (|={⊤}=>m [∗ map] i↦e;Ψ ∈ Θ;Ψs, (|={⊤}=>m (lWP e @ NotStuck; i; ⊤ {{ v, lift_term i Ψ v }}))))
    ⊢ |={⊤}=> safety_iris_tiProp i Φ (n, τf).
  Proof.
    iIntros (BEH FS LB HIST POST) "([HI SIa]& MI& WPs)".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "(WPs& HI& %&%&%&%& %& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO1 LB1].
    iPoseProof (big_sepM2_alt with "WPs") as "[%Dom WPs]".
    remember (map_zip Θ Ψs) as TQ. assert (EQTQ : Θ = fst <$> TQ).
    { subst. rewrite fst_map_zip; auto. intro k. rewrite -!elem_of_dom Dom. auto. }
    iAssert ([∗ map] i↦'(e, Q) ∈ TQ,
               (|={⊤}=>m (match to_val e with
                             | Some v => (lift_term i Q) v
                             | None => lwp_fix NotStuck i ⊤ e (lift_term i Q)
                             end)))%I with "[WPs]" as "WPs".
    { iApply (big_sepM_impl with "WPs"). iIntros "!> %%% H". destruct x.
      rewrite lwp_unfold_fix. iEval (rewrite lwp_fix_unfold_fix /lwp_pre) in "H".
      simpl. destruct (to_val e) eqn:He.
      - by iApply sfmupd_trans.
      - rewrite lwp_fix_unfold_fix /lwp_pre He. iFrame. }
    iMod (all_interp_sfmupd_steps_gmap γ with "WPs HI MI") as "(WPs& HI& %&%&%&%& %& MI)".
    { auto. }
    destruct H as [LEO3 LB3].
    iPoseProof (lwp_fix_safety_iris_tiProp with "[$HI $SIa $MI $WPs]") as "$".
    1,2: eauto. all: eauto.
    destruct POST as (?& LUi& POST). assert (is_Some (Θ !! i)).
    { apply elem_of_dom. apply elem_of_dom_2 in LUi. rewrite Dom. auto. }
    destruct H. exists x0, x. split; eauto. subst. eapply map_lookup_zip_Some; auto.
  Qed.

End proof2.

Theorem lwp_adequacy_safety_iris (Σ : gFunctors) (Λ : language)
  `{!mupdGpreS Σ} `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
  σ Θ i κs j (Φ : thread_id → val Λ → Prop) :
  ∀ (τ : trace Λ),
  behavior τ →
  fair_scheduling τ →
  (τ.1 = 0) →
  (τ.2 0 = (Θ, σ, i, κs)) →
  (∀ `{Htemporal : !temporalGS Λ Σ},
     ∃ (c : Ord.t),
       ⊢ |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                  (fork_post : thread_id → val Λ → iProp Σ)
                  (* FIXME: cannot unify pos_countable for some reason *)
                  (Ψs : gmap thread_id (H:=pos_countable) (thread_id → val Λ → iProp Σ)),
     let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
     ⌜(∃ Q, Ψs !! j = Some Q ∧ ∀ v, (Q j v ⊢ ⌜Φ j v⌝))⌝ ∧
     state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
     (£ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
      (|={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, (|={⊤}=>m (lWP e @ NotStuck; i; ⊤ {{ lift_term i Ψ }}))))) →
  safety_iris j Φ τ.
Proof.
  intros τ BEH FS INIT1 INIT2 Hwp.
  assert (iProp_sat
            (|==> ∃ (Hmupd : mupdGS Σ) (Hhist : histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))) (Htreg : tregGS.tregGS Λ Σ),
                let _ : temporalGS Λ Σ := TemporalG Hmupd Hhist Htreg in
                (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗
                wsat.wsat ∗ wsat.ownE ⊤ ∗
                |={⊤}=> safety_iris_tiProp j Φ τ)) as Hsat; cycle 1.
  { apply sat_bupd, sat_exists in Hsat. destruct Hsat as (Hmupd& Hsat). apply sat_exists in Hsat. destruct Hsat as (Hhist& Hsat).
    apply sat_exists in Hsat. destruct Hsat as (Htreg& Hsat).
    set (Htemp := TemporalG Hmupd Hhist Htreg : temporalGS Λ Σ).
    apply (safety_iris_tiProp_trProp emp). apply (sat_fupd ⊤).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono. 2: eapply Hsat. simpl. iIntros "($& $& $& $)". }
  assert (Hwp' : ⊢ ∀ Htemporal : temporalGS Λ Σ,
            ∃ (c : Ord.t),
            |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                     (fork_post : thread_id → val Λ → iProp Σ)
                     (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)),
            let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
            ⌜(∃ (Q : thread_id → val Λ → iProp Σ), Ψs !! j = Some Q ∧ ∀ v, (Q j v ⊢ ⌜Φ j v⌝))⌝ ∧
            state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
            (£ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
             (|={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, (|={⊤}=>m (lWP e @ NotStuck; i; ⊤ {{ lift_term i Ψ }}))))).
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
  iDestruct ("H" $! Htemp) as "(%& H)".
  iDestruct "R" as "(%x& R)".
  iMod (own_update _ (● x) with "R") as "[R LC]".
  { apply (auth_update_alloc x ((c : ordinal_ucmra.OrdUR) ⋅ x)).
    apply (op_local_update_discrete x ε c).
    intros ?. apply auth_valid_trivial. }
  iModIntro. iFrame "R W WOE". rewrite (right_id ε).
  iMod "H" as "(%Hsic& %fork_post& %Ψs& %POST& SI& SIa& WPs)".
  iMod ("HI" $! Hsic with "SI") as "HI". iDestruct "MI" as "(MHI& S& T& A& G& MI)".
  iMod (thP_carriers_alloc_threads (dom Θ) with "[$T $G]") as "(T& G& Ths)". 1: set_solver.
  iPoseProof ("WPs" with "LC Ths") as "WPs". rewrite union_empty_l_L.
  destruct τ as [n τf]. simpl in INIT1, INIT2. subst n.
  apply fair_scheduling_fscnt in FS. destruct FS as (γ& FS).
  set (Hlantana := LantanaG Htemp Hsic fork_post : lantanaGS Λ Σ).
  iPoseProof (treg_st_init (treg_handle (temporalGS0:=Htemp)) with "TR") as "TI".
  iApply (lwp_safety_iris_tiProp (lantanaGS0:=Hlantana) with "[$HI $TI $SIa $MHI $S $T $A $G $MI $WPs]").
  1,2: eauto. 1: apply map_Forall2_empty.
  { intros n' σ' Θ' κs' Hlu. rewrite lookup_cons in Hlu. destruct n'; last done. inv Hlu. rewrite INIT2. eauto. }
  eauto.
Qed.

(* Print Assumptions lwp_adequacy_safety_iris. *)
