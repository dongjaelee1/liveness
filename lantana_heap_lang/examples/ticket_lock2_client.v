From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation.
From lantana.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

From lantana.heap_lang.examples Require Export ticket_lock2.

(** A client that creates a ticket lock at runtime. Its adequacy theorem exports, besides
    termination, the starvation freedom of that lock, which comes from the lock library's
    guarantee ([is_fair_lock_temporal]) through a commitment obligation. *)
Module TicketLockClient.

  Definition main : val :=
    λ: <>,
      let: "l" := TicketLock.init #() in
      #42.

End TicketLockClient.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Ltac post_lwp :=
    simpl; iFrame "TG GF"; iExists ∅, 0; iSplitR; [by eauto | iIntros "TG GF _ _ TE"].

  Ltac lwp_pure_one := (lwp_pure; post_lwp).
  Ltac lwp_pures := repeat (iModIntro; lwp_pure_one).

  Ltac post_lwp_lc n :=
    simpl; iFrame "TG GF"; iExists ∅, n; iSplitR; [by eauto | iIntros "TG GF _ LC TE"].

  Ltac lwp_pure_lc n := (lwp_pure; post_lwp_lc n).

  Let Nr := nroot.@ "tl_client_ret".
  Let Nc := nroot.@ "tl_client_lock".

  (** Besides returning, the main thread commits to creating a fair lock. *)
  Lemma TicketLockClient_main_spec :
    ⊢ ∃ μ, ∀ i g kr kc,
    l{{{ thread_expr i [] (TicketLockClient.main #()) ∗ thP_carriers i {[g]} ∗
         ([∗ set] g ∈ {[g]}, crP_fuel g (1)%ordi μ) ∗
         crP_obls g 1 {[kr; kc]} ∗ ⌜kr ≠ kc⌝ ∗
         finallyT Nr kr 1 (exits #42@i) ∗
         finallyT Nc kc 1 (∃ tl γ, is_fair_lock tl γ True) }}}
      TicketLockClient.main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ ⌜v = #42⌝ ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof (TicketLock_init_spec) as (μ_i) "TicketLock_init_spec".
    iExists (10 ⊕ μ_i)%M. iIntros (i g kr kc Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& Cg& %Hkrc& HF& HC)".
    iPoseProof (crP_fuel_add_set with "GF") as "[GF GF_i]".
    iPoseProof (crP_fuels_init with "GF") as "GF".
    rewrite /TicketLockClient.main /=.
    lwp_pure_lc 100.
    lwp_bind (TicketLock.init _).
    iModIntro.
    iApply ("TicketLock_init_spec" $! 0 0 with "[$TE $TG GF_i]").
    { iApply (big_sepS_mono with "GF_i"). iIntros (??) "F". by iExists _. }
    iIntros (tl γ) "(TE& _& TG& _& Hmk)".
    iMod ("Hmk" $! ⊤ True%I with "[//]") as "#IFL".
    (* Keep the commitment: the lock exists. *)
    iPoseProof (tlc_split_nat 2 98 with "LC") as "[LCc LC]".
    replace ({[kr; kc]} : gset oid) with ({[kc]} ∪ {[kr]} : gset oid) by set_solver.
    iMod (finallyT_discharge with "LCc Cg HC [IFL]") as "(_& Cg& _)".
    { set_solver. }
    { set_solver. }
    { iExists tl, γ. iFrame "IFL". }
    lwp_pures.
    iApply lwpupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 2 96 with "LC") as "[LC _]".
    iMod (thread_expr_terminateT with "TE LC TG Cg HF") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. iFrame "Td". done.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := TicketLockClient.main #() ]} →
    Φ = (λ μ, (∃ g kr kc, finallyT Nr kr 1 (exits #42@i) ∗
                          finallyT Nc kc 1 (∃ tl γ, is_fair_lock tl γ True) ∗
                          (thP_carriers i {[g]} ∗ crP_obls g 1 {[kr; kc]} ∗ ⌜kr ≠ kc⌝ ∗
                           crP_fuel g 1 μ))%I) →
    Ψs = ({[i := (λ _ v, ⌜v = #42⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
     |={⊤}=>m ∃ μ, (Φ μ ∗
                   (Φ μ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ i; ⊤ {{ lift_term i Ψ }})))).
  Proof.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (TicketLockClient_main_spec) as (μ) "main_spec".
    iMod (carrier_alloc _ _ _ 1 μ with "TGs") as "(%g1& %Ning1& TG1& Gg1& Gf1)".
    iMod (untilI_alloc _ _ _ false 1 1 0 with "Gg1") as "(%kr& %Hkr& Gg1& Ofkr& #Wlkr& Akr)". 1: done.
    iMod ("Akr" $! _ Nr True%I (exits #42@i)%I (tsem (exits #42@i)%I) with "[]") as "Ukr".
    { done. }
    iMod (untilI_alloc _ _ _ false 1 1 0 with "Gg1") as "(%kc& %Hkc& Gg1& Ofkc& #Wlkc& Akc)". 1: done.
    iMod ("Akc" $! _ Nc True%I (∃ tl γ, is_fair_lock tl γ True)%I
            (tsem (∃ tl γ, is_fair_lock tl γ True)%I) with "[]") as "Ukc".
    { done. }
    iModIntro. iExists μ. iSplitL "Ukr Ukc TG1 Gg1 Gf1 Ofkr Ofkc".
    { subst Φ. rewrite !union_empty_r_L.
      replace ({[kc]} ∪ {[kr]}) with ({[kr; kc]} : gset oid) by set_solver.
      iExists g1, kr, kc. iFrame "Ukr Ukc TG1 Gf1 Gg1". iPureIntro. set_solver. }
    iClear "Wlkr Wlkc". clear dependent g1 kr kc.
    iIntros "HP". subst Φ.
    iDestruct "HP" as (g1 kr kc) "(HF& HC& TG& Cg& %Hkrc& GF)".
    iEval (rewrite HT big_sepM_singleton) in "TEs".
    iPoseProof ("main_spec" $! i g1 kr kc (λ v, lift_term i (λ _ v, ⌜v = #42⌝)%I v)
                 with "[TEs TG Cg GF HF HC]") as "WP".
    { iFrame. iSplitL; [by iApply big_sepS_singleton|done]. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iModIntro. eauto. iIntros (?) "(_& %& H)". rewrite /lift_term.
      iDestruct "H" as "[$ _]". eauto. }
    done.
  Qed.

End proof.

Section adequacy.

  Let i : thread_id := 1%positive.
  Let Θ0 : thread_pool heap_lang := {[i := TicketLockClient.main #()]}.
  Let σ0 : gmap loc (option val) := ∅.

  (** The main thread returns 42, and a ticket lock gets created that is starvation free. *)
  Definition client_spec : trProp heap_lang :=
    tr_and (tp_trace (tp_finally (exits #42@i)))
           (tr_eventually (λ τ, ∃ next curr : loc, starvation_free next curr τ)).

  Let Nr := nroot.@ "tl_client_ret".
  Let Nc := nroot.@ "tl_client_lock".

  Let Φ_P `{!heapGS Σ, !ticket_lockG Σ} : _ → iProp Σ :=
        λ μ,
          (∃ g kr kc,
              finallyT Nr kr 1 (exits #42@i) ∗
              finallyT Nc kc 1 (∃ tl γ, is_fair_lock tl γ True) ∗
              (thP_carriers i {[g]} ∗ crP_obls g 1 {[kr; kc]} ∗ ⌜kr ≠ kc⌝ ∗ crP_fuel g 1 μ))%I.

  Let G_main {Σ} : tps heap_lang Σ :=
        (tps_finally (exits #42@i) ∧ tps_finally (tps_exist (λ tl : val, fair_lock_tps tl)) ∧
         tps_true)%S.

  Lemma Φ_P_temporal `{!heapGS Σ, !ticket_lockG Σ} m : ⊢ Φ_P m ⊨ₜ G_main.
  Proof. apply (into_temporal _ _). Qed.

  Remark G_main_impl {Σ} τ : tps_tr (G_main (Σ:=Σ)) τ → client_spec τ.
  Proof.
    intros (Hr& Hf& _). split; first exact Hr.
    destruct τ as [n τf]. destruct Hf as (m& Hm& [tl Htl]& Hb).
    exists m. split_and!; [done| |done].
    destruct (fair_lock_starvation_free (Σ:=Σ) tl _ Htl) as (next& curr& _& Hsf).
    by exists next, curr.
  Qed.

  Let Σ : gFunctors :=
        #[mupdΣ;
          histGS.histΣ (state * thread_pool heap_lang * list (observation));
          heap_stateΣ;
          ticket_lockΣ
          ].

  Let fork_post {Σ} : thread_id → language.val heap_lang → iProp Σ := λ _ _, (True)%I.
  Let Ψs {Σ} : gmap thread_id (thread_id → language.val heap_lang → iProp Σ) :=
        {[i := (λ _ v, ⌜v = #42⌝)%I]}.

  Theorem ticket_lock_client_adequacy :
    ∀ (τ : trace heap_lang),
    behavior τ →
    fair_scheduling τ →
    (τ.1 = 0) →
    (τ.2 0 = ((Θ0, (Build_state σ0 ∅), i, []))) →
    client_spec τ.
  Proof.
    intros τ Beh FS Init1 Init2.
    eapply (lwp_adequacy_temporal Σ heap_lang NotStuck (Build_state σ0 ∅) Θ0 i [] G_main client_spec).
    { apply G_main_impl. }
    1,2,3,4: eauto.
    iIntros (?). exists 0%ord.
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
    iMod (main_pre (heapGS0:=HHeapGS) Θ0 i (Φ_P (heapGS0:=HHeapGS)) with "[Tis] [TGs]") as "H".
    { done. }
    { reflexivity. }
    { reflexivity. }
    { rewrite /thread_expr /=. iFrame. }
    { iFrame. }
    iDestruct "H" as (μ) "(HP& H)".
    iModIntro. iExists (Φ_P μ). iFrame "HP H". iApply Φ_P_temporal.
  Qed.

End adequacy.

(* Print Assumptions ticket_lock_client_adequacy. *)
