(** Lifting lemmas: the rules of the operational semantics as rules of [lWP]. Only
    [lwp_step_step] and [lwp_lift_step] see the history and the model updates around a step;
    the others are stated with the state interpretation and the obligation interface.
    Adapted from Iris's [iris.program_logic.lifting]. *)

From iris.proofmode Require Import proofmode.
From lantana.program_logic Require Export weakestpre.

Class PureExecSI `{SI : sidx} `{!lantanaGS Λ Σ}
    (ς : thread_id → expr Λ → iProp Σ) i :=
  pure_exec_si : ∀ K e1 e2 σ Θ κ,
  LanguageCtx K → Θ !! i = Some (K e1) → prim_step i e1 σ (dom Θ) [] e2 σ ∅ →
  ((ς i e1 ∗ state_interp σ Θ κ ∗ state_interp_aux σ Θ κ)
   ⊢ |==> (ς i e2 ∗ state_interp σ (<[i:=K e2]>Θ) κ ∗ state_interp_aux σ (<[i:=K e2]>Θ) κ)).

Section lifting.
  Context `{SI : sidx} `{!lantanaGS Λ Σ} `{!TemporalInterp Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types i : thread_id.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  (* [lwp_step] with the progress and fork updates applied, and a model update after it. *)
  Lemma lwp_step_step s i E e1 ν :
    (∀ K h n σ1 Θ κ κs,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
       (history_tinterp h n σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E,∅}=∗
       |=[n,dom Θ]=>m
       (⌜ if s is NotStuck then reducible i e1 σ1 (dom Θ) else True ⌝) ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
            ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                               thP_kids i G -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                               ([∗ set] j ∈ dom efs, thP_kids j ∅) -∗
                               ALC (|={∅,E:S n,dom (<[i:=K e2]> Θ) ∪ dom efs}=>m
                                      (history_tinterp (h ++ [(σ2, ((<[i:=K e2]>Θ) ∪ efs), κs)])
                                                       (S n) σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                       state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
                                      ((|={E}=>m (ν e2 efs))))))
    ⊢ lwp_step s i E e1 ν.
  Proof.
    iIntros "H". iApply lwp_step_post_sfmupd. iIntros (??????? ??) "SI".
    iMod ("H" with "[//] [//] SI") as "H". iModIntro.
    iMod "H" as "($& %& GOs& GFs& %& #REs& H)".
    iIntros "!> % % % %Step".
    iApply (mprog_step). iModIntro. iFrame "GOs GFs REs". iIntros "(GOs& Ws)".
    iApply (mphys_step _ (S n) _ _ (dom efs)). 1: eauto.
    { rewrite dom_insert_lookup_L; auto. }
    { eapply fork_thread_ids; eauto. }
    iIntros "!> !> Efs".
    iMod ("H" with "[//] GOs Ws Efs") as "H".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    iMod "H". iMod "close" as "_". iMod "H" as "[HI H]".
    iModIntro. by iFrame.
  Qed.

  Lemma lwp_lift_step s i E e1 Φ :
    to_val e1 = None →
    (∀ K h n σ1 Θ κ κs,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
       (history_tinterp h n σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E,∅}=∗
       |=[n,dom Θ]=>m
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 (dom Θ) else True ⌝) ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
            ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                               thP_kids i G -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                               ([∗ set] j ∈ dom efs, thP_kids j ∅) -∗
                               ALC (|={∅,E:S n,dom (<[i:=K e2]> Θ) ∪ dom efs}=>m
                                      (history_tinterp (h ++ [(σ2, ((<[i:=K e2]>Θ) ∪ efs), κs)])
                                                       (S n) σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                       state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
                                      (|={E}=>m ((lWP e2 @ s; i; E {{ Φ }}) ∗
                                                     ([∗ map] j ↦ ef ∈ efs,
                                                        lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))))))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (He) "H". rewrite lwp_unfold /lwp_pre. rewrite He.
    iApply lwp_step_step. iIntros (??????? ??) "I".
    iMod ("H" $! K with "[//] [//] I") as "H". iModIntro.
    iMod "H" as "(%& H)". destruct H1 as [_ H1].
    iModIntro. iSplitR; first done. iDestruct "H" as "(%& $& $& %& $& H)".
    iIntros (????). iMod ("H" with "[//]") as "H". iIntros "!> TG RWs Efs".
    iMod ("H" with "TG RWs Efs") as "H".
    iMod "H" as "[$ H]". iModIntro. iMod "H" as "[H Efs]". iFrame. auto.
  Qed.

  (** [lwp_lift_step] over the state interpretation: the history and the interpretation of
      the temporal layer are threaded, and no model update is taken around the step. *)
  Lemma lwp_lift_step_si s i E e1 Φ :
    to_val e1 = None →
    (∀ K σ1 Θ κ κs,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
       (state_interp σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E,∅}=∗
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 (dom Θ) else True ⌝) ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
            ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                               thP_kids i G -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                               ([∗ set] j ∈ dom efs, thP_kids j ∅) -∗
                               ALC (|={∅,E}=>
                                      (state_interp σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                       state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
                                      (|={E}=>m ((lWP e2 @ s; i; E {{ Φ }}) ∗
                                                     ([∗ map] j ↦ ef ∈ efs,
                                                        lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))))))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (He) "H". iApply lwp_lift_step; first done.
    iIntros (K h n σ1 Θ κ κs HK HΘ) "[[(%Hh& Ha& SI) TI] SIa]".
    iMod ("H" $! K with "[//] [//] [$SI $SIa]") as "H". iModIntro. iModIntro.
    iDestruct "H" as "($& %G& $& $& %R& $& H)".
    iIntros (e2 σ2 efs Hstep). iMod ("H" with "[//]") as "H". iIntros "!> TG Ws Efs".
    iApply (ALC_wand with "[Ha TI] (H TG Ws Efs)"). iIntros "H".
    iApply fupd_fmupd. iMod "H" as "[[SI SIa] H]".
    iMod (hG_history_auth_app _ [(σ2, (<[i:=K e2]> Θ ∪ efs), κs)] with "Ha") as "Ha".
    iModIntro. iFrame. iPureIntro. destruct Hh as [Hl Hlast].
    rewrite length_app last_app Hl. simpl. split; [lia|done].
  Qed.

  Local Hint Resolve reducible_no_obs_reducible : core.

  Lemma lwp_lift_stuck i E Φ e :
    to_val e = None →
    (∀ K σ κ Θ, ⌜LanguageCtx K⌝ → ⌜Θ !! i = Some (K e)⌝ →
                (state_interp σ Θ κ ∗ state_interp_aux σ Θ κ) ={E,∅}=∗
                ⌜ stuck i e σ (dom Θ) ⌝)
    ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    rewrite lwp_unfold /lwp_pre /lwp_step =>->.
    iIntros "H" (K h n σ Θ κ κs ??) "[[(_& _& SI) _] SIa]".
    iMod ("H" $! K with "[//] [//] [$SI $SIa]") as "[% %Hirr]".
    iModIntro. iSplitR; first done.
    iModIntro. iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
  Qed.

  (** Derived lifting lemmas. *)
  Lemma lwp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s i E E' e1 Φ ς :
    (∀ σ1 Θ, if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ κ σ1 Θ e2 σ2 efs, prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
    PureExecSI ς i →
    (|={E,E'}=>
       ς i e1 ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
         (∀ σ Θ κ e2 efs, ⌜prim_step i e1 σ Θ κ e2 σ efs⌝ -∗
          ς i e2 -∗
          thP_kids i G -∗
          ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
          ALC (|={E',E}=> (|={E}=>m (lWP e2 @ s; i; E {{ Φ }})))))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep HCS) "H".
    iApply lwp_lift_step_si.
    { specialize (Hsafe inhabitant inhabitant). destruct s; eauto using reducible_not_val. }
    iIntros (K σ1 Θ κ κs HK HΘ) "[SI SIa]".
    iMod "H" as "(Hc& (%& Tb& Gfs& %& #Rs& H))".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. split.
      - specialize (Hsafe σ1 ∅). destruct s; eauto using reducible_not_val.
      - destruct s; auto. }
    iExists _. iFrame "Tb Gfs". iExists _. iFrame "Rs".
    iIntros (e2 σ2 efs ?).
    destruct (Hstep κ σ1 (dom Θ) e2 σ2 efs) as (-> & <- & ->); auto.
    rewrite !map_union_empty. rewrite app_nil_l.
    iMod (pure_exec_si (ς:=ς) _ _ _ _ _ _ HK HΘ H with "[$Hc $SI $SIa]") as "(Hc& SI& SIa)".
    iIntros "!> Tb Wcs Efs". iMod ("H" with "[//] Hc Tb Wcs") as "H".
    iMod "Hclose" as "_". iMod "H". iModIntro. rewrite big_sepM_empty. iFrame.
    iMod "H". iModIntro. by iFrame.
  Qed.

  Lemma lwp_lift_pure_stuck `{!Inhabited (state Λ)} i E Φ e :
    (∀ σ τ, stuck i e σ τ) →
    True ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    iIntros (Hstuck) "_". iApply lwp_lift_stuck.
    - destruct(to_val e) as [v|] eqn:He; last done.
      rewrite -He. by case (Hstuck inhabitant ∅).
    - iIntros (???? ??) "_". iApply fupd_mask_intro; auto with set_solver.
  Qed.

  Lemma lwp_lift_atomic_step {s i E1 E2 Φ} e1 :
    to_val e1 = None →
    (∀ K σ1 Θ κ κs,
       (⌜(LanguageCtx K)⌝) → (⌜(Θ !! i = Some (K e1))⌝) →
       (state_interp σ1 Θ (κ ++ κs) ∗ state_interp_aux σ1 Θ (κ ++ κs)) ={E1,E2}=∗
       (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 (dom Θ) else True ⌝) ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
            ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                 (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝) ={∅}=∗
                               thP_kids i G -∗
                               ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                               ([∗ set] j ∈ dom efs, thP_kids j ∅) -∗
                               ALC (|={E2,E1}=>
                                      (state_interp σ2 ((<[i:=K e2]>Θ) ∪ efs) κs ∗
                                       state_interp_aux σ2 ((<[i:=K e2]>Θ) ∪ efs) κs) ∗
                                      |={E1}=>m
                                               (from_option (λ v, (|={E1}=>m (Φ v))) False (to_val e2)) ∗
                                             [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})))
    ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros (He) "H". iApply (lwp_lift_step_si s i E1 e1). 1: auto.
    iIntros (K σ1 Θ κ κs HK HΘ) "Hσ1".
    iMod ("H" $! K with "[//] [//] Hσ1") as "(%& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first auto.
    iDestruct "H" as "(%& Tb& Gfs& %& #Rs& H)".
    iExists _. iFrame "Tb Gfs". iExists _. iFrame "Rs".
    iIntros (????). iMod ("H" with "[//]") as "H".
    iIntros "!> Tb Wcs Efs". iMod ("H" with "Tb Wcs Efs") as "H".
    iMod "Hclose" as "_". iMod "H" as "($&Hq)".
    iModIntro. iMod "Hq" as "[Hq $]".
    destruct (to_val e2) eqn:?; last by iExFalso.
    simpl. iMod "Hq". iModIntro.
    iApply lwp_value; last eauto. by apply of_to_val.
  Qed.

  Lemma lwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s i E E' Φ ς} e1 e2 :
    (∀ σ1 Θ, if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ σ1 κ Θ e2' σ2 efs', prim_step i e1 σ1 Θ κ e2' σ2 efs' →
                           κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    PureExecSI ς i →
    (|={E,E'}=>
       ς i e1 ∗
       ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
       ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
         (ς i e2 -∗
          thP_kids i G -∗
          ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
          ALC (|={E',E}=> (|={E}=>m (lWP e2 @ s; i; E {{ Φ }})))))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet HCS) "H". iApply (lwp_lift_pure_step_no_fork s i E E'); eauto.
    { naive_solver. }
    iMod "H" as "($& %& $& $& %& $& H)". iModIntro.
    iIntros (σ Θ κ e2' efs Hstep) "Hc Tb Wcs".
    destruct (Hpuredet σ κ Θ e2' σ efs Hstep) as (_ & _ & -> & _).
    iApply ("H" with "Hc Tb Wcs").
  Qed.

  Lemma lwp_pure_step `{!Inhabited (state Λ)} (n : nat) (o : Ord.t) s i E E' e1 e2 φ Φ ς :
    PureExec φ n e1 e2 →
    φ →
    PureExecSI ς i →
    (ς i e1 ∗ Nat.iter n (λ P, |={E,E'}=>
                   ∃ G, thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1) ∗
                   ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                   (thP_kids i G -∗
                    ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r) -∗
                    ALC (£ o ={E',E}=∗ |={E}=>m P)))
       (ς i e2 -∗ (|={E}=>m (lWP e2 @ s; i; E {{ Φ }}))))
    ⊢ (lWP e1 @ s; i; E {{ Φ }}).
  Proof.
    iIntros (Hexec Hφ HCS) "[Hc Hlwp]". specialize (Hexec Hφ). destruct Hexec as [Hn Hexec].
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
    { lia. }
    destruct (gt_dec n 0); cycle 1.
    { assert (n = 0) by lia. subst n. clear n0 Hn.
      simpl in *. inv Hexec. iApply (lwp_lift_pure_det_step_no_fork (E':=E')).
      - intros σ Θ. specialize (Hsafe i σ Θ). destruct s; eauto using reducible_not_val.
      - eauto.
      - iDestruct "Hlwp" as ">(%& $& $& %& $& H)". iFrame "Hc".
        iModIntro. iIntros "Hc Gb Wcs". iDestruct ("H" with "Gb Wcs") as "H".
        iDestruct "H" as "(%& H)". iExists (o ⊕ x)%ord. iIntros "LC".
        iPoseProof (tlc_split with "LC") as "[LC LC2]".
        iMod ("H" with "LC2") as "H". iModIntro. iPoseProof ("H" with "LC") as "H".
        iMod "H". iModIntro. iMod "H". by iApply "H". }
    iApply (lwp_lift_pure_det_step_no_fork (E':=E')).
    - intros σ Θ. specialize (Hsafe i σ Θ). destruct s; eauto using reducible_not_val.
    - eauto.
    - iDestruct "Hlwp" as ">(%& $& $& %& $& H)". iFrame "Hc".
      iModIntro. iIntros "Hc Gb Wcs". iDestruct ("H" with "Gb Wcs") as "H".
      iDestruct "H" as "(%& H)". iExists (o ⊕ x)%ord. iIntros "LC".
      iPoseProof (tlc_split with "LC") as "[LC LC2]".
      iMod ("H" with "LC2") as "H". iModIntro. iPoseProof ("H" with "LC") as "H".
      iMod "H". iModIntro. iMod "H". iApply ("IH" with "[//] Hc H").
  Qed.

  Lemma lwp_pure_step_simple `{!Inhabited (state Λ)} n G R (o : Ord.t) s i E e1 e2 φ Φ ς :
    PureExec φ n e1 e2 →
    φ →
    PureExecSI ς i →
    (ς i e1 ∗ thP_kids i G ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ n) ∗
     ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
     (ς i e2 -∗ thP_kids i G -∗ ([∗ set] r ∈ R, witP_cred r n ∨ oblP_discharged r) -∗
      £ (o × n)%ord -∗ (|={E}=>m (lWP e2 @ s; i ; E {{ Φ }}))))
    ⊢ (lWP e1 @ s; i; E {{ Φ }}).
  Proof.
    iIntros (Hexec HΦ HCS) "(Hc& TG& Gfs& #Rs& Hlwp)".
    iApply (lwp_pure_step n o _ _ E E). 1: auto.
    iFrame "Hc".
    iStopProof. clear Hexec. pattern n. induction n.
    { iIntros "(#Rs& TG& Gfs& IH)". simpl. iIntros "Hc".
      iMod tlc_zero as "Hz". iPoseProof (tlc_equiv Ord.O (o × 0)%ord with "Hz") as "Hz".
      { by rewrite Jacobsthal.mult_O_r. }
      iMod (obl_check_witnesses with "Rs") as "Ws".
      iApply ("IH" with "Hc TG [Ws] Hz").
      rewrite Ord.from_nat_O. done. }
    iIntros "(#Rs& TG& Gfs& IH)". simpl.
    iAssert (([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ n) ∗ ([∗ set] g ∈ G, ∃ ℓ, oblP_fuel g ℓ 1))%I
      with "[Gfs]" as "[Gfs Gf]".
    { iApply big_sepS_sep. iApply (big_sepS_impl with "Gfs"). iIntros "!> %% (%& F)".
      rewrite (oblP_fuel_eq _ _ (S n)%M (n ⊕ 1)%M); cycle 1.
      { rewrite measure_rep_nat_S measure_rep_add. by rewrite Hessenberg.add_comm. }
      iPoseProof (oblP_fuel_add with "F") as "($& $)". }
    iModIntro. iFrame "TG Gf Rs". iIntros "TG RWs".
    iIntros "!> LC !>". iApply IHn. iFrame "Rs TG Gfs".
    iIntros "!> Hc TG Ws LC2". iApply ("IH" with "Hc TG [Ws RWs] [LC LC2]").
    { iCombine "Ws RWs" as "Ws". rewrite -big_sepS_sep. iApply (big_sepS_impl with "Ws").
      iIntros "!> %% [[Wc1 | #Gd1] [Wc2 | #Gd2]]"; auto.
      iLeft. rewrite (witP_cred_eq _ (n ⊕ Ord.one)%ord (S n)).
      - iApply witP_cred_split. iFrame.
      - rewrite -Ord.from_nat_1 -Hessenberg.add_from_nat comm. done. }
    { rewrite (tlc_equiv (o × S n)%ord ((o × n) ⊕ o)%ord).
      - rewrite tlc_split. iFrame.
      - rewrite Ord.from_nat_S Jacobsthal.mult_S comm. done. }
  Qed.

End lifting.
