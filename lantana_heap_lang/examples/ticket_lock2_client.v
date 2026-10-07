From lantana.base_logic Require Export invariants.
From lantana.heap_lang Require Export lang.
From lantana.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.
From lantana.heap_lang.examples Require Export ticket_lock2.
From lantana.heap_lang.examples Require Import step_tactics.

(** * A client that creates a ticket lock, acquires and releases it. Besides termination, its
    adequacy theorem exports the starvation freedom of the lock, from the lock's guarantee
    ([is_fair_lock_temporal]) through a commitment obligation. *)
Module TicketLockClient.

  Definition main : val :=
    λ: <>,
      let: "l" := TicketLock.init #() in
      TicketLock.acquire "l";;
      TicketLock.release "l";;
      #42.

End TicketLockClient.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

  Let Nr := nroot.@ "tl_client_ret".
  Let Nc := nroot.@ "tl_client_lock".

  (** Besides returning, the main thread commits to creating a fair lock. Its obligations
      live at layer [ℵ], above the lock's waiting ([TicketLock_acquire_spec] at lock level 0). *)
  Lemma TicketLockClient_main_spec :
    ⊢ ∃ μ, ∀ i kr kc,
    l{{{ thread_expr i [] (TicketLockClient.main #()) ∗ thP_kids i {[kr; kc]} ∗
         ([∗ set] g ∈ {[kr; kc]}, oblP_fuel g ℵ%ordi μ) ∗
         ⌜kr ≠ kc⌝ ∗ oblP_kids kr ∅ ∗ oblP_kids kc ∅ ∗
         finallyI Nr kr 1 (exits #42@i) ∗
         finallyI Nc kc 1 (∃ tl γ, is_fair_lock tl γ True) }}}
      TicketLockClient.main #() @ i
    l{{{ v, RET v; thread_expr i [] (of_val v) ∗ ⌜v = #42⌝ ∗ lift_term i fork_post v }}}.
  Proof.
    iPoseProof (TicketLock_init_spec) as (μ_i) "TicketLock_init_spec".
    iPoseProof (TicketLock_acquire_spec) as (μ_a) "TicketLock_acquire_spec".
    iPoseProof (TicketLock_release_spec) as (μ_r) "TicketLock_release_spec".
    iExists (100 ⊕ μ_i ⊕ μ_a ⊕ μ_r)%M. iIntros (i kr kc Φ) "!> HP HΦ".
    iDestruct "HP" as "(TE& TG& GF& %Hkrc& Kkr& Kkc& HF& HC)".
    iPoseProof (oblP_fuel_add_set with "GF") as "[GF GF_m]".
    iPoseProof (oblP_fuel_add_set with "GF_m") as "[GF_i GF_m]".
    iPoseProof (oblP_fuel_add_set with "GF_m") as "[GF_a GF_r]".
    iPoseProof (oblP_fuels_init with "GF") as "GF".
    rewrite /TicketLockClient.main /=.
    lwp_pure_lc 100.
    lwp_bind (TicketLock.init _).
    iModIntro.
    iApply ("TicketLock_init_spec" $! 0 0 with "[$TE $TG GF_i]").
    { iApply (big_sepS_mono with "GF_i"). iIntros (??) "F". by iExists _. }
    iIntros (tl γ) "(TE& _& TG& CF& Hmk)".
    iMod ("Hmk" $! ⊤ True%I with "[//]") as "#IFL".
    (* Keep the commitment: the lock exists. *)
    iPoseProof (tlc_split_nat 1 99 with "LC") as "[LCc LC]".
    iMod (finallyI_discharge with "LCc TG Kkc HC [IFL]") as "(_& TG& _)".
    { set_solver. }
    { set_solver. }
    { iExists tl, γ. iFrame "IFL". }
    iPoseProof (oblP_fuels_remove_obl kc with "GF") as "GF".
    iPoseProof (big_sepS_delete _ _ kc with "GF_a") as "[_ GF_a]"; first set_solver.
    iPoseProof (big_sepS_delete _ _ kc with "GF_r") as "[_ GF_r]"; first set_solver.
    replace ({[kr; kc]} ∖ {[kc]}) with ({[kr]} : gset oid) by set_solver.
    lwp_pures.
    (* Acquire. *)
    lwp_bind (TicketLock.acquire _).
    iModIntro.
    iApply ("TicketLock_acquire_spec" $! 0 (10 ⊕ μ_r)%M with "[$TE $TG GF_a $CF $IFL]").
    { iApply oblP_fuel_layer_eq_set. 2: iFrame. by rewrite hessenberg.add_O_l. }
    iIntros (κu) "(TE& _& %Hku& TG& Kku& Fku& CF& Tok& _)".
    iPoseProof (oblP_fuel_add with "Fku") as "[Fku Fku_r]".
    iPoseProof (oblP_fuels_add 87 10 with "GF") as "[_ GF]".
    iPoseProof (oblP_fuels_add_obl with "Fku GF") as "GF".
    lwp_pures.
    (* Release. *)
    iPoseProof (oblP_fuels_init with "GF_r") as "GF_r".
    iPoseProof (oblP_fuels_add_obl with "Fku_r GF_r") as "GF_r".
    lwp_bind (TicketLock.release _).
    iModIntro.
    iApply ("TicketLock_release_spec" $! 0 with "[$TE $TG $GF_r $Kku $Tok $IFL]").
    { iPureIntro. set_solver. }
    iIntros "(TE& _& TG)".
    iPoseProof (oblP_fuels_remove_obl κu with "GF") as "GF".
    replace (({[κu]} ∪ {[kr]}) ∖ {[κu]}) with ({[kr]} : gset oid) by set_solver.
    lwp_pures.
    iApply sfmupd_lwp_sfmupd.
    iPoseProof (tlc_split_nat 1 98 with "LC") as "[LC _]".
    iMod (thread_expr_terminate_finally with "TE LC TG Kkr HF") as "[TE #Td]"; first set_solver.
    iModIntro. lwp_finish.
    iApply "HΦ". iFrame "TE". rewrite /lift_term. iFrame "Td". done.
  Qed.

  Lemma main_pre Θ i Φ Ψs :
    Θ = {[i := TicketLockClient.main #() ]} →
    Φ = (λ μ, (∃ kr kc, finallyI Nr kr 1 (exits #42@i) ∗
                        finallyI Nc kc 1 (∃ tl γ, is_fair_lock tl γ True) ∗
                        (thP_kids i {[kr; kc]} ∗ oblP_kids kr ∅ ∗ oblP_kids kc ∅ ∗ ⌜kr ≠ kc⌝ ∗
                         ([∗ set] g ∈ {[kr; kc]}, oblP_fuel g ℵ%ordi μ)))%I) →
    Ψs = ({[i := (λ _ v, ⌜v = #42⌝)%I]}) →
    (([∗ map] i ↦ e ∈ Θ, thread_expr i [] e) -∗
     ([∗ set] i ∈ dom Θ, thP_kids i ∅) -∗
     |={⊤}=>m ∃ μ, (Φ μ ∗
                   (Φ μ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lWP e @ i; ⊤ {{ lift_term i Ψ }}))).
  Proof.
    iIntros (HT HP HQ) "TEs TGs".
    iEval (rewrite HT !dom_insert_L dom_empty_L union_empty_r_L) in "TGs".
    rewrite !big_sepS_singleton.
    iPoseProof (TicketLockClient_main_spec) as (μ) "main_spec".
    iMod (untilI_alloc _ _ _ ℵ%ordi μ with "[] TGs") as "(%kr& %Hkr& TG1& Kkr& Ofkr& #Wlkr& Akr)".
    { iApply parP_le_thread. }
    iMod ("Akr" $! _ Nr True%I (exits #42@i)%I with "[]") as "Ukr".
    { done. }
    iMod (untilI_alloc _ _ _ ℵ%ordi μ with "[] TG1") as "(%kc& %Hkc& TG1& Kkc& Ofkc& #Wlkc& Akc)".
    { iApply parP_le_thread. }
    iMod ("Akc" $! _ Nc True%I (∃ tl γ, is_fair_lock tl γ True)%I with "[]") as "Ukc".
    { done. }
    iModIntro. iExists μ. iSplitL "Ukr Ukc TG1 Kkr Kkc Ofkr Ofkc".
    { subst Φ. rewrite !union_empty_r_L.
      replace ({[kc]} ∪ {[kr]}) with ({[kr; kc]} : gset oid) by set_solver.
      iExists kr, kc. iFrame "Ukr Ukc TG1 Kkr Kkc".
      rewrite (big_sepS_union _ {[kr]} {[kc]}); last set_solver. rewrite !big_sepS_singleton.
      iFrame "Ofkr Ofkc". iPureIntro. set_solver. }
    iClear "Wlkr Wlkc". clear dependent kr kc.
    iIntros "HP". subst Φ.
    iDestruct "HP" as (kr kc) "(HF& HC& TG& Kkr& Kkc& %Hkrc& GF)".
    iEval (rewrite HT big_sepM_singleton) in "TEs".
    iPoseProof ("main_spec" $! i kr kc (λ v, lift_term i (λ _ v, ⌜v = #42⌝)%I v)
                 with "[TEs TG Kkr Kkc GF HF HC]") as "WP".
    { iFrame "∗ #". iPureIntro. done. }
    iModIntro. subst Θ Ψs. iApply big_sepM2_insert.
    { done. }
    { done. }
    iSplitL "WP".
    { iApply "WP". iIntros (?) "(_& %& H)". rewrite /lift_term.
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
    tr_and (tr_eventually (exits #42@i)%R)
           (tr_eventually (λ τ, ∃ next curr : loc, starvation_free next curr τ)).

  Let Nr := nroot.@ "tl_client_ret".
  Let Nc := nroot.@ "tl_client_lock".

  Let Φ_P `{!heapGS Σ, !ticket_lockG Σ} : _ → iProp Σ :=
        λ μ,
          (∃ kr kc,
              finallyI Nr kr 1 (exits #42@i) ∗
              finallyI Nc kc 1 (∃ tl γ, is_fair_lock tl γ True) ∗
              (thP_kids i {[kr; kc]} ∗ oblP_kids kr ∅ ∗ oblP_kids kc ∅ ∗ ⌜kr ≠ kc⌝ ∗
               ([∗ set] g ∈ {[kr; kc]}, oblP_fuel g ℵ%ordi μ)))%I.

  Let G_main {Σ} : itProp heap_lang Σ :=
        (itProp_finally (exits #42@i) ∧ itProp_finally (itProp_exist (λ tl : val, fair_lock_itProp tl)) ∧
         itProp_true)%IT.

  Lemma Φ_P_temporal `{!heapGS Σ, !ticket_lockG Σ} m : ⊢ Φ_P m ⊨ₜ G_main.
  Proof. apply (into_temporal _ _). Qed.

  Remark G_main_impl {Σ} τ : itProp_external (G_main (Σ:=Σ)) τ → client_spec τ.
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
          tregGS.tregΣ heap_lang;
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
