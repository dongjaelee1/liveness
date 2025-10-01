(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From liris.program_logic Require Export weakestpre.
From liris Require Import ordinal_wfocm.
From iris.prelude Require Import options.

Section lifting.
Context `{SI : indexT} `{!lirisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Section liveness.

  (* For lwp_step, enable progress and fork. *)
  Lemma lwp_step_progress_no_lc s i E e1 ν :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ if s is NotStuck then reducible e1 σ1 Θ else True ⌝) ∗
       |={∅}=> ∀ e2 σ2 efs, (⌜ prim_step e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                           ([∗ set] j ∈ dom efs, othreadG_elem j ∗ othreadG_obls j ∅ 1 ∗ othreadG_exec j (1/2)) -∗
                           |={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs)
    ⊢ lwp_step s i E e1 ν.
  Proof.
    rewrite /lwp_step. iIntros "H % % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%Hstuck& H)".
    iModIntro. iSplitR; first done. iExists false. iMod "H" as "H".
    iModIntro. iExists Ω1. iSplitR; first done. iIntros (??? Hstep).
    iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
    { symmetry. eapply fork_thread_ids; eauto. }
    iMod ("H" with "[//] Efs") as "[I H]". iModIntro. iExists Ω1, Ω1.
    iFrame. iPureIntro. split; done.
  Qed.

  Lemma lwp_step_progress_get_lc_with_obls q Ψ s i E e1 ν :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ if s is NotStuck then reducible e1 σ1 Θ else True ⌝) ∗
       (othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗
        [∗ set] ρ ∈ Ψ, oblG_elem ρ ∗ othreadG_owns i ρ true q ∗ oblG_progress ρ Ord.one) ∗
       ALC (|={∅}=>
              ∀ e2 σ2 efs, (⌜ prim_step e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                           othreadG_obls i Ψ 1 -∗ ([∗ set] ρ ∈ Ψ, othreadG_owns i ρ true q) -∗
                           ([∗ set] j ∈ dom efs, othreadG_elem j ∗ othreadG_obls j ∅ 1 ∗ othreadG_exec j (1/2)) -∗
                           |={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs))
    ⊢ lwp_step s i E e1 ν.
  Proof.
    rewrite /lwp_step. iIntros "H % % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%Hstuck& (#Tei& Tbsi& Bps)& H)".
    iModIntro. iSplitR; first done. iExists true. iMod "H" as ">H".
    iModIntro. iExists Ω1. iSplitR; first done. iIntros (??? Hstep).
    iMod (oforest_progress_one_thread _ _ _ Ψ (gset_to_gmap (true, q) Ψ) with "[S T F Tbsi Bps]")
      as "(%& %Hprog& S& T& F& Tbsi &Tos)".
    { by rewrite dom_gset_to_gmap. }
    { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap. iApply (big_sepS_impl with "Bps").
      iIntros "!>" (??). iIntros "(E& O& P)". iFrame. iPureIntro. apply Ord.S_lt. }
    rewrite big_sepM_gset_to_gmap.
    iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
    { symmetry. eapply fork_thread_ids; eauto. }
    iMod ("H" with "[//] Tbsi Tos Efs") as "[I H]". iModIntro. iExists Ω', Ω'.
    assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
    iFrame. iPureIntro. split; done.
  Qed.

  Lemma lwp_step_progress_get_lc_suspended_obls s i E e1 ν :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
       (⌜ if s is NotStuck then reducible e1 σ1 Θ else True ⌝) ∗
       ∃ π Ψ K,
         (⌜Ψ = dom K⌝ ∗ othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗ oblG_elem π ∗ otreeG_elem π ∗
          ([∗ set] ρ ∈ Ψ, oblG_elem ρ ∗ oblG_progress ρ Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_elem k ∗ otreeG_suspend k x i π ψ ∗ otreeG_wait k x (1/2))) ∗
         ALC (|={∅}=>
                ∀ e2 σ2 efs, (⌜ prim_step e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                             othreadG_obls i Ψ 1 -∗
                             ((([∗ set] ρ ∈ Ψ, oblG_progress ρ Ord.one) ∗
                               ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_wait k x (1/2))) ∨
                                (oblG_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k true (1/2) ∗ oblG_progress k ψ))) -∗
                             ([∗ set] j ∈ dom efs, othreadG_elem j ∗ othreadG_obls j ∅ 1 ∗ othreadG_exec j (1/2)) -∗
                             |={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs))
    ⊢ lwp_step s i E e1 ν.
  Proof.
    rewrite /lwp_step. iIntros "H % % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%Hstuck& %&%&%& (%Dom& #Tei& Tbsi& Bps)& H)".
    iModIntro. iSplitR; first done. iExists true. iMod "H" as ">H".
    iModIntro. iExists Ω1. iSplitR; first done. iIntros (??? Hstep).
    iDestruct "Bps" as "(#Beπ& #Feπ& Bps& M)".
    iAssert ([∗ map] k ↦ _ ∈ K, oblG_elem k)%I with "[Bps]" as "#Bes".
    { rewrite Dom -big_sepM_dom. iApply (big_sepM_impl with "Bps"). iIntros "!>" (???) "[H _]". iFrame. }
    iMod (oforest_wait_cases_many _ _ _ ((λ '(x, ψ), (x, i, ψ)) <$>K) with "[S U F M]") as "(S& F& [(Fws& Fos& U) | (U& #Bdπ& M)])".
    { iFrame. iSplitR; first eauto. iSplitR; first eauto.
      rewrite big_sepM_fmap. iApply (big_sepM_impl with "M"). iIntros "!>" (???). destruct x. by iIntros. }
    - rewrite !big_sepM_fmap.
      iAssert (
          ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k false (1/2)) ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_edge π k 1)
        )%I with "[Fos]" as "[Fos Fes]".
      { iApply big_sepM_sep. iApply (big_sepM_impl with "Fos"). iIntros "!>" (???) "A". destruct x. iFrame. }
      iMod (oforest_progress_one_thread _ _ _ Ψ (gset_to_gmap (false, (1/2)%Qp) Ψ) with "[S T F Tbsi Fos]")
        as "(%& %Hprog& S& T& F& Tbsi& Fos)".
      { by rewrite dom_gset_to_gmap. }
      { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap big_sepS_sep Dom -!big_sepM_dom.
        iSplitR; first auto. iApply (big_sepM_impl with "Fos"). iIntros "!>" (???) "H". by destruct x. }
      iPoseProof (big_sepM_gset_to_gmap with "Fos") as "Fos". iPoseProof ("U" with "[Fes Fos]") as "U".
      { subst Ψ. rewrite -big_sepM_dom. iPoseProof (big_sepM_sep_2 with "Fos Fes") as "Fs".
        iApply (big_sepM_impl with "Fs"). iIntros "!>" (???) "H". by destruct x. }
      iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
      { symmetry. eapply fork_thread_ids; eauto. }
      iMod ("H" with "[//] Tbsi [Bps Fws] Efs") as "[I H]".
      { iLeft. iSplitR "Fws".
        - iPoseProof (big_sepS_sep with "Bps") as "[H1 H2]". iFrame.
        - iApply (big_sepM_impl with "Fws"). iIntros "!>" (???) "H". by destruct x. }
      iModIntro. iExists Ω', Ω'.
      assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
      iFrame. iPureIntro. split; done.
    - rewrite !big_sepM_fmap.
      iAssert (
          ([∗ map] k ↦ _ ∈ K, othreadG_owns i k true (1/2) ∗ oblG_progress k Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, oblG_progress k ψ)
        )%I with "[Bps M]" as "[Tos Bps]".
      { subst Ψ. rewrite -big_sepM_dom -big_sepM_sep. iPoseProof (big_sepM_sep_2 with "Bps M") as "M".
        iApply (big_sepM_impl with "M"). iIntros "!>" (???) "H". destruct x. iDestruct "H" as "((_&B)&C&D)". iFrame. }
      iMod (oforest_progress_one_thread _ _ _ Ψ (gset_to_gmap (true, (1/2)%Qp) Ψ) with "[S T F Tbsi Tos]")
        as "(%& %Hprog& S& T& F& Tbsi& Fos)".
      { by rewrite dom_gset_to_gmap. }
      { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap big_sepS_sep Dom -!big_sepM_dom.
        iSplitR; first auto. iApply (big_sepM_impl with "Tos"). iIntros "!>" (???) "[H1 H2]".
        iFrame. iPureIntro. apply Ord.S_pos. }
      iPoseProof (big_sepM_gset_to_gmap with "Fos") as "Fos".
      iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
      { symmetry. eapply fork_thread_ids; eauto. }
      iMod ("H" with "[//] Tbsi [Bps Fos] Efs") as "[I H]".
      { iRight. iSplitR; first auto. subst Ψ. rewrite -big_sepM_dom.
        iPoseProof (big_sepM_sep_2 with "Fos Bps") as "H".
        iApply (big_sepM_impl with "H"). iIntros "!>" (???) "H". by destruct x. }
      iModIntro. iExists Ω', Ω'.
      assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
      iFrame. iPureIntro. split; done.
  Qed.

  (* For ghost_step, enable allocating, transferring, resolving and waiting for obligations. *)
  Lemma ghost_step_wait_obls E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ i π Ψ K,
         (⌜Ψ = dom K⌝ ∗ othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗ oblG_elem π ∗ otreeG_elem π ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_elem k ∗ otreeG_suspend k x i π ψ ∗ otreeG_wait k x (1/2))) ∗
         (othreadG_obls i Ψ 1 -∗
          (([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_wait k x (1/2)) ∨
             (oblG_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k true (1/2) ∗ oblG_progress k ψ))) -∗
          |={∅,E}=> state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%&%&%&%& (%Dom& #Tei& Tbsi& Bps)& H)".
    iDestruct "Bps" as "(#Beπ& #Feπ& M)".
    iMod (oforest_wait_cases_many _ _ _ ((λ '(x, ψ), (x, i, ψ)) <$>K) with "[S U F M]") as "(S& F& [(Fws& Fos& U) | (U& #Bdπ& M)])".
    { iFrame. iSplitR; first eauto. iSplitR; first eauto.
      rewrite big_sepM_fmap. iApply (big_sepM_impl with "M"). iIntros "!>" (???). destruct x. by iIntros. }
    - rewrite !big_sepM_fmap.
      iPoseProof ("U" with "Fos") as "U".
      iMod ("H" with "Tbsi [Fws]") as "[I H]".
      { iLeft. iApply (big_sepM_impl with "Fws"). iIntros "!>" (???) "H". by destruct x. }
      iModIntro. iExists Ω. iFrame. done.
    - rewrite !big_sepM_fmap.
      iMod ("H" with "Tbsi [M]") as "[I H]".
      { iRight. iSplitR; first auto. iApply (big_sepM_impl with "M"). iIntros "!>" (???) "H". by destruct x. }
      iModIntro. iExists Ω. iFrame. done.
  Qed.

  Lemma ghost_step_alloc_obl E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ i Ψ q,
         othreadG_elem i ∗ othreadG_obls i Ψ q ∗
         (∃ T P α β, ∀ k,
            ⌜k ∉ Ψ⌝ -∗ othreadG_obls i ({[k]} ∪ Ψ) q -∗
            oblG_elem k -∗ oblG_goal k T P -∗
            oblG_transfer_bound k α -∗ oblG_transfer k α -∗ oblG_progress k β -∗
            othreadG_owns i k true (1/2)%Qp -∗ otreeG_elem k -∗
            |={∅,E}=> state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%&%&%& #Tei& Tbs& %&%&%&%& H)".
    iMod (osat_alloc_obl _ α i  β T P with "S") as "(%k& %Nink& S& #Bgk& Blk& Btk& #Btbk& Bok& Bpsk& Bpk)".
    iPoseProof (oblG_elem_unfold with "[Bgk]") as "#Bek"; first eauto.
    assert (Nink2 : k ∉ dom Ω) by (by apply not_elem_of_dom in Nink).
    iMod (osuspend_alloc_obl _ _ Nink2 with "U") as "(U& #Fek)".
    iMod (othread_alloc_obl with "[S T Tbs Blk]") as "(S& T& %NinkΨ& Tbs& Tok& Blk)"; first (iFrame; eauto).
    iPoseProof (oblG_owner_div_2 _ _ (1/2)%Qp with "Bok") as "[Bok1 Bok2]".
    iMod (othread_obl_acquire with "[T Tok Bok1]") as "(T& Tok)"; first (iFrame; eauto).
    iPoseProof (othreadG_owns_div_2 _ _ _ (1)%Qp with "Tok") as "[Tok1 Tok2]".
    iMod (oforest_alloc_obl _ _ _ α β Nink2 with "[F Tok1 Blk Bok2 Bpsk]") as "F"; first (iFrame; eauto).
    iMod ("H" with "[//] Tbs Bek Bgk Btbk Btk Bpk Tok2 Fek") as "[I H]".
    iModIntro. iExists (<[k:=olive α i β]> Ω). rewrite !dom_insert_L. iFrame.
    iPureIntro. eapply rtc_l; last reflexivity. eapply obl_states_step_alloc.
    exists k. eauto.
  Qed.

  Lemma ghost_step_resolve_obl E ν :
    (∀ Θ σ κs,
       state_interp σ Θ κs ={E,∅}=∗
       ∃ i Ψ q k T P,
         othreadG_elem i ∗ othreadG_obls i Ψ q ∗ othreadG_owns i k true (1/2)%Qp ∗ ⌜k ∈ Ψ⌝ ∗
         oblG_goal k T P ∗ ⌜T σ⌝ ∗ (▷ P) ∗
         (othreadG_obls i (Ψ ∖ {[k]}) q -∗ oblG_done k -∗
          |={∅,E}=> state_interp σ Θ κs ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
    iMod ("H" with "I") as "(%&%&%&%&%&%& #Tei& Tbs& Toi& %Ink& #Bgk& GT& GP& H)".
    iMod (oforest_resolve_one with "[$]") as "(%&%&%&%Prog& S& T& U& F& #Bdk& Tbs)"; first auto.
    iMod ("H" with "Tbs Bdk") as "[I H]". iModIntro. iFrame. iPureIntro. destruct Prog as [Prog1 Prog2].
    eapply rtc_l.
    - eapply obl_states_step_resolve; eauto.
    - eapply rtc_l; last reflexivity. eapply obl_states_step_transfer; eauto.
  Qed.


  (* lwp versions *)
  Lemma lwp_progress s i E e1 Φ :
    to_val e1 = None →
    (∀ σ1 ns κ κs τ,
       state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
       ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈Λ⌉)) ∗
              (⌜ if s is NotStuck then reducible e1 σ1 τ else True ⌝) ∗
              ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                           toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] i ∈ dom efs, toL_thread i 1 []) -∗
                           £ (S (num_laters_per_step ns)) ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
       state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
       lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (He) "H". rewrite lwp_unfold /lwp_pre He. iApply lwp_step_progress. iFrame.
  Qed.

  Lemma lwp_alloc_obl a T R s i E e Φ :
    (∀ σ ns κs τ,
       state_interp σ ns κs τ ={E,∅}=∗
       ∃ j L, toL_thread j 1 L ∗
              ∀ κ, (toL_thread j 1 (κ :: L) ∗ oblG_goal κ T R ∗ oblS_active κ ∗ toS_assigned j κ ∗ oblS_credit κ a ∗ ∃ b, oblS_bound κ b) ={∅,E}=∗
                   state_interp σ ns κs τ ∗ lWP e @ s; i; E {{ Φ }})
    ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". iApply ghost_step_elim. iApply (ghost_step_alloc_obl a T R). iFrame.
  Qed.

  Lemma lwp_fulfill_obl κ s i E e Φ :
    (∀ σ ns κs τ,
       state_interp σ ns κs τ ={E,∅}=∗
       ∃ j L T R, (toL_thread j 1 (κ :: L) ∗ oblG_goal κ T R ∗ oblS_active κ ∗ ⌜ T σ ⌝ ∗ ▷ R) ∗
                  (toL_thread j 1 L ∗ oblS_done κ ={∅,E}=∗
                   state_interp σ ns κs τ ∗ lWP e @ s; i; E {{ Φ }}))
    ⊢ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "H". iApply ghost_step_elim. iApply (ghost_step_fulfill_obl κ). iFrame.
  Qed.

End liveness.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma lwp_lift_step_fupdN s i E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ,
     state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
     ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈Λ⌉)) ∗
            (⌜ if s is NotStuck then reducible e1 σ1 τ else True ⌝) ∗
            ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                         toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗
                         £ (S (num_laters_per_step ns)) ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
     state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
     lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof. apply lwp_progress. Qed.

Lemma lwp_lift_step_fupd s i E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ,
     state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
     ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈Λ⌉)) ∗
            (⌜ if s is NotStuck then reducible e1 σ1 τ else True ⌝) ∗
            ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                         toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗
                         £ 1 ={∅}=∗ ▷ |={∅,E}=>
     state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
     lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "Hlwp". rewrite -lwp_lift_step_fupdN; [|done].
  iIntros (?????) "Hσ". iMod ("Hlwp" with "Hσ") as "(% & % & Ht & Hcs & % & Hlwp)".
  iModIntro. iExists _, _. iFrame "Ht Hcs". iSplit; first done. iIntros (??? ?) "Ht Hc Hts Hcred".
  iPoseProof (lc_weaken 1 with "Hcred") as "Hcred"; first lia.
  simpl. rewrite -step_fupdN_intro; [|done]. rewrite -bi.laterN_intro.
  iMod ("Hlwp" with "[//] Ht Hc Hts Hcred") as "Hlwp".
  iApply step_fupd_intro; done.
Qed.

Lemma lwp_lift_stuck i E Φ e :
  to_val e = None →
  (∀ δ (Ω : obl_statesL Λ) γ σ ns κs τ,
     (⌜ τ = dom δ ⌝ ∗ schedfairIL Λ δ ∗ osat Ω ∗ toIL Λ γ ∗ oftIL Λ Ω δ γ ∗ state_interp σ ns κs τ) ={E,∅}=∗
     ⌜ stuck e σ τ ⌝)
  ⊢ lWP e @ i; E ?{{ Φ }}.
Proof.
  rewrite lwp_unfold /lwp_pre /lwp_step =>->. iIntros "H" (??? σ ns κ κs nt) "Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iExists Ω1. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.

(** Derived lifting lemmas. *)
Lemma lwp_lift_step s i E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ,
     state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
     ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈Λ⌉)) ∗
            (⌜ if s is NotStuck then reducible e1 σ1 τ else True ⌝) ∗
            ▷ ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                           toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗
                           £ 1 ={∅,E}=∗
                           state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
                           lWP e2 @ s; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_step_fupd; [done|]. iIntros (?????) "Hσ".
  iMod ("H" with "Hσ") as "(%&%&H1&H2&$&H)". iModIntro. iExists _, _. iFrame "H1 H2".
  iIntros (??? ?) "Ht Hfc Hts Hcred !> !>". iApply ("H" with "[//] Ht Hfc Hts Hcred").
Qed.

Lemma lwp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s i E E' Φ e1 :
  (∀ σ1 τ, if s is NotStuck then reducible e1 σ1 τ else to_val e1 = None) →
  (∀ κ σ1 τ e2 σ2 efs, prim_step e1 σ1 τ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
  (|={E,E'}=> ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈Λ⌉)) ∗
                    ▷ (toL_thread i q L ={E',E}=∗ ∀ κ τ e2 efs σ,
     ⌜prim_step e1 σ τ κ e2 σ efs⌝ -∗ sfS_fuel_credit_forallL Λ -∗ £ 1 -∗ lWP e2 @ s; i; E {{ Φ }}))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply lwp_lift_step.
  { specialize (Hsafe inhabitant ∅). destruct s; eauto using reducible_not_val. }
  iIntros (σ1 ns κ κs τ) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iDestruct "H" as "(%&%&Ht&Hcs&H)". iFrame "Ht Hcs". iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 efs ?) "Ht Hcf Hts Hcred".
  destruct (Hstep κ σ1 τ e2 σ2 efs) as (-> & <- & ->); auto.
  replace (τ ∪ dom ∅) with τ by set_solver.
  iMod (state_interp_mono with "Hσ") as "$". iMod "Hclose" as "_".
  iMod ("H" with "Ht") as "H".
  iModIntro. rewrite big_sepM_empty. iSplitL; [|done].
  iApply ("H" with "[//] Hcf Hcred").
Qed.

Lemma lwp_lift_pure_stuck `{!Inhabited (state Λ)} i E Φ e :
  (∀ σ τ, stuck e σ τ) →
  True ⊢ lWP e @ i; E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply lwp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case (Hstuck inhabitant ∅).
  - iIntros (???????) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.

(* To fetch toL_thread from the invariant, atomic step needs to update mask. *)
Lemma lwp_lift_atomic_step_fupd {s i E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ, state_interp σ1 ns (κ ++ κs) τ ={E1,∅}=∗
    ∃ (q : Qp) (L : list obl_id), toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
    ⌜if s is NotStuck then reducible e1 σ1 τ else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝ -∗
    toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗ £ 1 ={∅,E1}=∗ |={E1}[E2]▷=>
      state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (lwp_lift_step_fupd s i E1 _ e1)=>//; iIntros (σ1 ns κ κs τ) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "(%&%&Ht&Hcs&$&H)".
  iModIntro. iFrame "Ht Hcs". iIntros (????) "Ht Hcf Hts Hcred".
  iMod ("H" with "[//] Ht Hcf Hts Hcred") as "H".
  iMod "H" as "H". iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
  iNext. iMod "Hclose" as "_". iMod "H" as "(Hs&Hq&Hefs)". iFrame.
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply lwp_value; last done. by apply of_to_val.
Qed.

Lemma lwp_lift_atomic_step {s i E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs τ, state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
    ∃ (q : Qp) (L : list obl_id), toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
    ⌜if s is NotStuck then reducible e1 σ1 τ else True⌝ ∗
      ∀ e2 σ2 efs, ⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝ -∗
      toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗ £ 1 ={∅,E}=∗ |={E}▷=>
      state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗
      from_option Φ False (to_val e2) ∗
      [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply lwp_lift_atomic_step_fupd; [done|].
  iIntros (?????) "?". iMod ("H" with "[$]") as "(%&%&$&$&$&H)".
  iIntros "!> *". iIntros (Hstep) "Ht Hcf Hts Hcred".
  iMod ("H" with "[//] Ht Hcf Hts Hcred") as "H".
  by iApply "H".
Qed.

Lemma lwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s i E E' Φ} e1 e2 :
  (∀ σ1 τ, if s is NotStuck then reducible e1 σ1 τ else to_val e1 = None) →
  (∀ σ1 κ τ e2' σ2 efs', prim_step e1 σ1 τ κ e2' σ2 efs' →
                         κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
  (|={E,E'}=> ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)) ∗
                    ▷ (toL_thread i q L ={E',E}=∗ sfS_fuel_credit_forallL Λ -∗ £ 1 -∗
                    lWP e2 @ s; i; E {{ Φ }})) ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (lwp_lift_pure_step_no_fork s i E E'); try done.
  { naive_solver. }
  iMod "H" as "(%&%&$&$&H)". iIntros "!> !> Ht". iMod ("H" with "Ht") as "H".
  iIntros "!> % % % % %". iIntros ((_&?&->&?)%Hpuredet); auto.
Qed.

Lemma lwp_pure_step_fupd `{!Inhabited (state Λ)} s i E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (Nat.iter n (λ P, |={E,E'}=> ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈ Λ ⌉)%ord) ∗
                                     ▷ (toL_thread i q L ={E',E}=∗ P))
     ((Nat.iter n (λ C, C ∗ sfS_fuel_credit_forallL Λ) emp) -∗ £ n -∗ lWP e2 @ s; i; E {{ Φ }}))
  ⊢ lWP e1 @ s; i; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hlwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
  { iMod lc_zero as "Hz". by iApply "Hlwp". }
  iApply (lwp_lift_pure_det_step_no_fork (E':=E')).
  - intros σ. specialize (Hsafe σ). intros. specialize (Hsafe τ). destruct s; eauto using reducible_not_val.
  - done.
  - iDestruct "Hlwp" as ">(%&%&Ht&Hcs&Hlwp)". iFrame "Ht Hcs". iIntros "!> !> Ht".
    iMod ("Hlwp" with "Ht") as "Hlwp". iIntros "!> Hcf Hcred".
    iApply "IH". iApply (bi.iter_modal_mono with "[Hcf Hcred] [Hlwp]").
    { iIntros (P Q) "PQ H". iMod "H" as "(%&%&$&$&H)". iIntros "!> !> Ht".
      iMod ("H" with "Ht") as "H". iModIntro. by iApply "PQ".
    }
    2:{ iApply "Hlwp". }
    iIntros "Hs H Hl". iPoseProof ((lc_succ n) with "[Hcred Hl]") as "Hcred"; first iFrame.
    iApply ("Hs" with "[Hcf H] Hcred"). iFrame.
Qed.

(* Need to fetch toL_thread anyways (most of the times), this lemma not useful w/ obligations? *)

(* Lemma lwp_pure_step_later `{!Inhabited (state Λ)} s i E e1 e2 φ n Φ : *)
(*   PureExec φ n e1 e2 → *)
(*   φ → *)
(*   ▷^n (£ n -∗ LWP e2 @ s; E {{ Φ }}) ⊢ LWP e1 @ s; E {{ Φ }}. *)
(* Proof. *)
(*   intros Hexec ?. rewrite -lwp_pure_step_fupd //. clear Hexec. *)
(*   enough (∀ P, ▷^n P ⊢ |={E}▷=>^n P) as Hlwp by apply Hlwp. intros ?. *)
(*   induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH. *)
(* Qed. *)
End lifting.
