From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Export flag task_queue.
From lantana.heap_lang.examples Require Import step_tactics.

(** * A client of the task queue: a reentrant task that puts itself back [n] times before
    setting a flag, which the main thread waits on *)

Definition decr_reentrant : val :=
  (rec: "f" "a" :=
     let: "q" := Fst (Fst "a") in
     let: "x" := Snd (Fst "a") in
     let: "n" := Snd "a" in
     if: "n" ≤ #0%Z
     then Flag.set "x"
     else TaskQueue.put_task "q" "f" ("q", "x", "n" - #1%Z)).

Definition main : val :=
  λ: <>,
    let: "q" := TaskQueue.init #() in
    let: "x" := Flag.init #() in
    let: "n" := ChooseNat in
    decr_reentrant ("q", "x", "n");;
    let: "v" := Flag.wait "x" in
    "v".

Section proof.
  Context `{!heapGS Σ, !queueG Σ, !ticket_lockG Σ}.

  Let Nl := nroot.@ "return".
  Let Nc := nroot.@ "flag".

  (** The layer of the task queue: [is_task] in [TaskQueue_put_task_spec] needs [1 < ℓq]. *)
  Let ℓq : ord.t := (1 ⊕ 1)%ordi.
  Remark ℓq_cond : (1 < ℓq)%ordi.
  Proof. apply hessenberg.add_lt_l. apply ord.S_lt. Qed.

  Definition is_decr_reentrant (arg : val) γ (k : oid) : iProp Σ :=
    ∃ (ql : val) (x : loc) (n : Z),
      ⌜arg = (ql, #x, #n)%V⌝ ∧
      is_flag x k (ℓq ⊕ 2)%ordi ∗
      is_task_queue ql γ ℓq.

  (** The main proof. *)
  Global Instance is_decr_reentrant_persistent arg γ k : Persistent (is_decr_reentrant arg γ k).
  Proof. rewrite /is_decr_reentrant. apply _. Qed.

  Lemma decr_reentrant_spec :
    ⊢ ∃ μ, ∀ lc i G p k K γ (arg : val) C,
    l{{{ thread_expr i C (decr_reentrant arg) ∗ thP_kids i G ∗ ([∗ set] g ∈ G, oblP_fuel g 1%ordi μ) ∗
         parP_kids p K ∗ ⌜k ∈ K⌝ ∗ oblP_kids k ∅ ∗
         ∃ (ql : val) (x : loc) (n : Z),
           ⌜arg = (ql, #x, #n)%V⌝ ∗
           oblP_fuel k (ℓq ⊕ 2)%ordi (Z.to_nat n)%M ∗
           flag_tk x k ∗
           is_decr_reentrant arg γ k }}}
      decr_reentrant arg @ i
    l{{{ RET #(); thread_expr i C #() ∗ £ lc ∗ thP_kids i G ∗ parP_kids p (K ∖ {[k]}) }}}.
  Proof.
    unfold decr_reentrant.
    (** Lob to bootstrap the spec *)
    iLöb as "TASK".
    iPoseProof (Flag_set_spec) as (μ_fs) "Flag_set_spec".
    iPoseProof (TaskQueue_put_task_spec) as (μ_tp) "TaskQueue_put_task_spec".
    iExists (100 ⊕ (μ_fs ⊕ μ_tp))%M.
    iIntros (lc i G p k K γ arg C) "!> % (TE& TG& GF& Gg& %SubK& Kk& %&%&%& %Harg& Of& Ftk& #DRI) HΦ".
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF Fm]".
    iPoseProof (oblP_fuel_add_set with "Fm") as "[F_fs F_tp]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc lc. iRename "LC" into "Q_LC".
    subst arg.
    lwp_pures.
    iDestruct "DRI" as "(%&%&%& %& is_flag& is_task_queue)".
    symmetry in H. simplify_eq /=.
    destruct (decide (n ≤ 0)%Z).
    - iClear "TASK TaskQueue_put_task_spec". rewrite bool_decide_eq_true_2; last done.
      iModIntro. lwp_pure_lc 100.
      lwp_bind (Flag.set _).
      iMod (oblP_fuel_layer_mon_set _ 0 with "F_fs") as "F_fs".
      { apply ordArith.le_from_nat. lia. }
      iModIntro. iApply ("Flag_set_spec" $! 0 with "[$TE $TG $F_fs $Gg $Kk $Ftk $is_flag]").
      { auto. }
      iIntros "(TE& _& TG& Cg& #Od)". iApply ("HΦ" with "[$TE $Q_LC $TG $Cg]").
    - rewrite bool_decide_eq_false_2; last done.
      iModIntro. lwp_pure_lc 100.
      lwp_pures.
      iPoseProof (tlc_split_nat 1 99 with "LC") as "[LC1 LC]".
      iApply (lc_sfmupd_add_later with "LC1"). iNext.
      lwp_bind (TaskQueue.put_task _ _ _).
      assert (Hn : Z.to_nat n = 1 + Z.to_nat (n - 1)) by lia.
      rewrite (oblP_fuel_eq k _ _ (1 ⊕ (Z.to_nat (n - 1)))%M); cycle 1.
      { rewrite measure_rep_add !measure_rep_nat -Hessenberg.add_from_nat Hn. done. }
      iPoseProof (oblP_fuel_add with "Of") as "[Of1 Of]".
      iModIntro. iApply ("TaskQueue_put_task_spec" $! 0 _ _ _ _ {[k]} γ ℓq with "[$TE $TG $F_tp $Gg Of1 Of Ftk Kk]").
      { iClear "TaskQueue_put_task_spec". iSplit.
        { iPureIntro. set_solver. }
        iSplitL "Of1".
        { iApply big_sepS_singleton. iFrame. }
        rewrite /is_task_queue. iFrame "is_task_queue".
        rewrite /is_task. iDestruct "TASK" as (mt) "TASK".
        iExists 1%ordi, _. iSplit.
        { iPureIntro. apply ℓq_cond. }
        iSplitL.
        { iCombine "Of Ftk Kk" as "H". iApply "H". }
        iExists mt. iIntros (??????) "!> % (TE& TG& GF& Gg& %Hsub& OF& Ftk& Kk) HΦ".
        iApply ("TASK" $! lc0 with "[$TE $TG $GF $Gg $Kk $OF $Ftk]").
        { iSplit.
          { iPureIntro. set_solver. }
          iExists _. iSplit; first done. rewrite /is_decr_reentrant /is_task_queue.
          iFrame "is_flag is_task_queue". eauto. }
        iIntros "(TE& LC& TG& Gg)". iApply ("HΦ" with "[$TE $LC $TG $Gg]"). }
      iIntros "(TE& _& TG& Gg)". iApply ("HΦ" with "[$TE $Q_LC $TG $Gg]").
  Qed.

  (** Besides returning, the main thread commits to creating a flag and a task queue ([kc]). *)
  Lemma main_spec :
    ⊢ ∃ μ, ∀ i kl kc,
    l{{{ thread_expr i [] (main #()) ∗ thP_kids i {[kl; kc]} ∗ ([∗ set] g ∈ {[kl; kc]}, oblP_fuel g (ℓq ⊕ 3)%ordi μ) ∗
         ⌜kl ≠ kc⌝ ∗ oblP_kids kl ∅ ∗ oblP_kids kc ∅ ∗
         finallyI Nl kl 1 (exits #1@i) ∗
         finallyI Nc kc 1 ((∃ x k ℓ, is_flag x k ℓ) ∗ (∃ ql γ ℓ, is_task_queue ql γ ℓ)) }}}
      main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ lift_term i (λ _ v, ⌜v = #1⌝) v }}}.
  Proof using queueG0 ticket_lockG0.
    unfold main.
    iPoseProof (TaskQueue_init_spec) as (μ_ti) "TaskQueue_init_spec".
    iPoseProof (Flag_init_spec) as (μ_fi) "Flag_init_spec".
    iPoseProof (decr_reentrant_spec) as (μ_d) "decr_reentrant_spec".
    iPoseProof (Flag_wait_spec) as (μ_fw) "Flag_wait_spec".
    (* Internal steps, func calls, wait *)
    iExists (100 ⊕ μ_ti ⊕ μ_fi ⊕ μ_d ⊕ μ_fw)%M. iIntros (i kl kc) "!> % (TE& TG& GF& %Hklc& Kkl& Kkc& HF& HC) HΦ".
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF GF_m]".
    iPoseProof (oblP_fuel_add_set with "GF_m") as "[GF_ti GF_m]".
    iPoseProof (oblP_fuel_add_set with "GF_m") as "[GF_fi GF_m]".
    iPoseProof (oblP_fuel_add_set with "GF_m") as "[GF_d GF_fw]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    lwp_pure_lc 100.
    lwp_pures.
    lwp_bind (TaskQueue.init _).
    iMod (oblP_fuel_layer_mon_set _ (0)%ordi with "GF_ti") as "GF_ti".
    { apply ord.O_bot. }
    iModIntro. iApply ("TaskQueue_init_spec" $! 0 _ _ ℓq with "[$TE $TG $GF_ti]").
    { iPureIntro. apply ord.lt_le, ℓq_cond. }
    iClear "TaskQueue_init_spec".
    iIntros (ql qγ) "(TE& _& TG& #ITQ)".
    lwp_pures.
    lwp_bind (Flag.init _).
    (* A container for the flag's obligation, at the flag's layer. *)
    iMod (obl_new _ (PThread i) _ (ℓq ⊕ 2)%ordi (μ_fi ⊕ μ_d ⊕ 97)%M with "[] TG")
      as "(%g0& %NinG& TG& Cg0& Ag0& GF0& #Wg0)".
    { iApply parP_le_thread. }
    iPoseProof (oblP_fuel_add with "GF0") as "[F_init0 GF0]".
    iPoseProof (oblP_fuel_add with "GF0") as "[F_d0 GF0]".
    iMod (oblP_fuel_layer_mon_set _ 0 with "GF_fi") as "F_init".
    { apply ord.O_bot. }
    iMod (oblP_fuel_layer_mon _ 0 with "F_init0") as "F_init0".
    { apply ord.O_bot. }
    iModIntro.
    iApply ("Flag_init_spec" $! 0 _ _ (PObl g0) ∅ (ℓq ⊕ 2)%ordi (ℵ)%M with "[$TE $TG F_init F_init0 $Cg0]").
    { iSplitL "F_init F_init0".
      - iApply big_sepS_union. 1: set_solver. rewrite big_sepS_singleton. iFrame.
      - iApply (parP_le_obl with "Wg0"). done. }
    iIntros "%ptrx %k (TE& _& TG& _& Cg0& Kk& Of0& Ftk& #is_flag)".
    rewrite union_empty_r_L.
    (* Keep the commitment: the flag exists. *)
    iPoseProof (tlc_split_nat 2 98 with "LC") as "[LCc LC]".
    iMod (finallyI_discharge with "LCc TG Kkc HC []") as "(_& TG& _)".
    { set_solver. }
    { set_solver. }
    { iSplit; [iExists ptrx, k, _; iFrame "is_flag"|iExists ql, qγ, ℓq; iFrame "ITQ"]. }
    iPoseProof (oblP_fuels_remove_obl kc with "GF") as "GF".
    iPoseProof (big_sepS_delete _ _ kc with "GF_d") as "[_ GF_d]"; first set_solver.
    iPoseProof (big_sepS_delete _ _ kc with "GF_fw") as "[_ GF_fw]"; first set_solver.
    replace (({[g0]} ∪ {[kl; kc]}) ∖ {[kc]}) with ({[g0]} ∪ {[kl]} : gset oid) by set_solver.
    replace ({[kl; kc]} ∖ {[kc]}) with ({[kl]} : gset oid) by set_solver.
    iClear "Flag_init_spec".
    iPoseProof (oblP_fuels_add_obl with "GF0 GF") as "GF".
    lwp_pures.
    lwp_bind (ChooseNat).
    iPoseProof (oblP_fuels_add 1 with "GF") as "[GF1 GF]".
    iModIntro.
    iApply (lwp_choosenat _ ∅ 0 with "[$TE $TG $GF1]"). 1: done.
    iIntros (n) "(TE& _& TG& _)".
    lwp_pures.
    lwp_bind (decr_reentrant _).
    iMod (oblP_fuel_mon _ _ (n)%M with "Of0") as "Of0".
    { rewrite !measure_rep_nat measure_rep_large.
      etrans; first (eapply Ord.lt_le, Ord.omega_upperbound).
      rewrite Ord.omega_from_peano_lt_set.
      eapply Ord.lt_le, Ord.large_lt_from_wf_set. }
    iMod (oblP_fuel_layer_mon_set _ 1 with "GF_d") as "F_d".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.le_from_nat. lia. }
    iMod (oblP_fuel_layer_mon _ 1 with "F_d0") as "F_d0".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.le_from_nat. lia. }
    iModIntro.
    iApply ("decr_reentrant_spec" $! 0 with "[$TE $TG F_d F_d0 $Cg0 $Kk Of0 $Ftk]").
    { iSplitR "Of0".
      { iApply big_sepS_union. 1: set_solver. rewrite !big_sepS_singleton. iFrame. }
      iSplitR.
      { iPureIntro. set_solver. }
      iExists ql, n. iSplitR; first done. replace (Z.to_nat n) with n by lia.
      iFrame. iFrame "ITQ is_flag". eauto. }
    iClear "decr_reentrant_spec".
    iIntros "(TE& _& TG& Cg0)".
    replace ({[k]} ∖ {[k]}) with (∅ : oids) by set_solver.
    iMod (obl_discharge_leaf with "TG Cg0 Ag0") as "[TG _]". 1: set_solver.
    iPoseProof (oblP_fuels_remove_obl g0 with "GF") as "GF".
    replace (({[g0]} ∪ {[kl]}) ∖ {[g0]}) with ({[kl]} : gset oid) by set_solver.
    lwp_pures.
    lwp_bind (Flag.wait _).
    iModIntro.
    iMod (oblP_fuel_layer_mon_set _ ((ℓq ⊕ 2) ⊕ 1)%ordi with "GF_fw") as "GF_fw".
    { unfold ℓq. rewrite -!hessenberg.add_from_nat. apply ordArith.le_from_nat. lia. }
    iApply ("Flag_wait_spec" $! 0 with "[$TE $TG $GF_fw $is_flag]").
    iIntros "(TE& _& TG& #Od0)".
    do 2 (iModIntro; lwp_pure_one).
    iApply sfmupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 2 96 with "LC") as "[LC _]".
    iMod (thread_expr_terminate_finally with "TE LC TG Kkl HF") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. iFrame "Td". done.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := main #() ]} →
    Φ = (λ μ, (∃ kl kc, finallyI Nl kl 1 (exits #1@i) ∗
                        finallyI Nc kc 1 ((∃ x k ℓ, is_flag x k ℓ) ∗ (∃ ql γ ℓ, is_task_queue ql γ ℓ)) ∗
                        (thP_kids i {[kl; kc]} ∗ oblP_kids kl ∅ ∗ oblP_kids kc ∅ ∗ ⌜kl ≠ kc⌝ ∗
                         ([∗ set] g ∈ {[kl; kc]}, oblP_fuel g (ℓq ⊕ 3)%ordi μ)))%I) →
    Ψs = ({[i := (λ _ v, ⌜v = #1⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_kids i ∅) -∗
     |={⊤}=>m ∃ μ, (Φ μ ∗
                   (Φ μ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lWP e @ i; ⊤ {{ lift_term i Ψ }}))).
  Proof using queueG0 ticket_lockG0.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (main_spec) as (μ) "main_spec".
    iMod (untilI_alloc _ _ _ (ℓq ⊕ 3)%ordi μ with "[] TGs") as "(%kl1& %Hkl1& TG1& Kkl1& Ofkl1& #Wlkl1& Akl1)".
    { iApply parP_le_thread. }
    iMod ("Akl1" $! _ Nl True%I (exits #1@i)%I with "[]") as "Ukl1".
    { done. }
    iMod (untilI_alloc _ _ _ (ℓq ⊕ 3)%ordi μ with "[] TG1") as "(%kc& %Hkc& TG1& Kkc& Ofkc& #Wlkc& Akc)".
    { iApply parP_le_thread. }
    iMod ("Akc" $! _ Nc True%I ((∃ x k ℓ, is_flag x k ℓ) ∗ (∃ ql γ ℓ, is_task_queue ql γ ℓ))%I
            with "[]") as "Ukc".
    { done. }
    iModIntro. iExists μ. iSplitL "Ukl1 Ukc TG1 Kkl1 Kkc Ofkl1 Ofkc".
    { subst Φ. rewrite !union_empty_r_L.
      replace ({[kc]} ∪ {[kl1]}) with ({[kl1; kc]} : gset oid) by set_solver.
      iExists kl1, kc. iFrame "Ukl1 Ukc TG1 Kkl1 Kkc".
      rewrite (big_sepS_union _ {[kl1]} {[kc]}); last set_solver. rewrite !big_sepS_singleton.
      iFrame "Ofkl1 Ofkc". iPureIntro. set_solver. }
    iClear "Wlkl1 Wlkc". clear dependent kl1 kc.
    iIntros "HP". subst Φ.
    iDestruct "HP" as (kl1 kc) "(HF& HC& TG& Kkl& Kkc& %Hklc& GF)".
    iEval (rewrite HT big_sepM_singleton) in "TEs".
    iPoseProof ("main_spec" $! i kl1 kc (λ v, lift_term i (λ _ v, ⌜v = #1⌝)%I v) with "[TEs TG Kkl Kkc GF HF HC]") as "WP".
    { iFrame "∗ #". iPureIntro. done. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iIntros (?) "[_ $]". }
    done.
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let Θ0 : thread_pool heap_lang := {[i := main #()]}.
  Let σ0 : gmap loc (option val) := ∅.

  (** The main thread returns 1, and a flag gets created that is [0] until it is [1] and
      then stays [1]; in particular, the task chain run by the worker sets it. *)
  Let R_main : trProp heap_lang :=
        (tr_eventually (exits #1@i) ∧ tr_eventually (∃ x : loc, is_flag_tr x))%R.

  (** Moreover, a task queue gets created whose lock makes release progress: whenever its
      lock is held, it is eventually released. *)
  Let R_queue : trProp heap_lang :=
    tr_eventually (λ τ, ∃ lhptr ltptr next curr : loc, release_progress next curr τ).

  Let Nl := nroot.@ "return".
  Let Nc := nroot.@ "flag".
  Let ℓq : ord.t := (1 ⊕ 1)%ordi.

  Let Φ_P `{!heapGS Σ, !queueG Σ, !ticket_lockG Σ} : _ → iProp Σ :=
        λ μ,
          (∃ kl kc,
              finallyI Nl kl 1 (exits #1@i) ∗
              finallyI Nc kc 1 ((∃ x k ℓ, is_flag x k ℓ) ∗ (∃ ql γ ℓ, is_task_queue ql γ ℓ)) ∗
              (thP_kids i {[kl; kc]} ∗ oblP_kids kl ∅ ∗ oblP_kids kc ∅ ∗ ⌜kl ≠ kc⌝ ∗
               ([∗ set] g ∈ {[kl; kc]}, oblP_fuel g (ℓq ⊕ 3)%ordi μ)))%I.

  Let G_main {Σ} : tps heap_lang Σ :=
        (tps_finally (exits #1@i) ∧
         tps_finally (tps_exist (λ x : loc, flag_tps x) ∧ tps_exist (λ ql : val, task_queue_tps ql)) ∧
         tps_true)%S.

  Lemma Φ_P_temporal `{!heapGS Σ, !queueG Σ, !ticket_lockG Σ} m : ⊢ Φ_P m ⊨ₜ G_main.
  Proof. apply (into_temporal _ _). Qed.

  Remark G_main_impl {Σ} τ : tps_tr (G_main (Σ:=Σ)) τ → R_main τ ∧ R_queue τ.
  Proof.
    intros (Hr& Hf& _). destruct τ as [n τf]. destruct Hf as (m& Hm& [[x Hx] [ql Hq]]& Hb).
    split; [split; first exact Hr|].
    - exists m. split_and!; [done| |done]. exists x. exact (flag_tps_impl x (m, τf) Hx).
    - exists m. split_and!; [done| |done].
      destruct (task_queue_release_progress ql (m, τf) Hq) as (lhptr & ltptr & next & curr & _ & Hrp).
      by exists lhptr, ltptr, next, curr.
  Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          tregGS.tregΣ heap_lang;
          heap_stateΣ;
          queueΣ;
          ticket_lockΣ
          ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := (λ _ v, ⌜v = #1⌝)%I]}.

  Theorem task_queue_client_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    R_main τ ∧ R_queue τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_temporal Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] G_main
              (λ τ, R_main τ ∧ R_queue τ)).
    { apply G_main_impl. }
    1,2,3,4: eauto.
    iIntros (?). exists (Ord.from_nat 2).
    iMod (gen_heap_init σ0) as "(%Hheap& HI& Ptrs& _)".
    iMod (thread_map_init Θ0) as "(%Hthread& TI& Tis)".
    iMod (proph_map_init ([] : list observation) (∅ : gset proph_id)) as "(%Hproph& PI)".
    iMod (inv_heap_init loc (option val) (⊤ : coPset)) as "(%Hinv_heap& >HHI)".
    set (Hheap_stateGS := @HeapStateGS Σ Hheap Hinv_heap Hproph Hthread).
    set (HHeapGS := @HeapGS Σ Htemporal Hheap_stateGS).
    set (HlantanaGS := @heapGS_lantanaGS Σ HHeapGS).
    iExists (lantana_state_interp_class), (@fork_post Σ), (@Ψs Σ).
    iSplitL "HI TI PI".
    { iDestruct "PI" as "[PI _]". by iFrame. }
    iSplitR; first done.
    iModIntro. iIntros "LC TGs".
    iMod (main_pre (heapGS0:=HHeapGS) (queueG0:=QueueG Σ _) Θ0 i (Φ_P (heapGS0:=HHeapGS) (queueG0:=QueueG Σ _)) with "[Tis] [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iModIntro. iExists (Φ_P (heapGS0:=HHeapGS) (queueG0:=QueueG Σ _) μ). iFrame "HP H".
    iApply Φ_P_temporal.
  Qed.

End adequacy.
