(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From liveness.program_logic Require Export weakestpre.
From liveness Require Import ordinal_wfocm.
From iris.prelude Require Import options.

Notation sfS_fuel_credit_forallL Λ := (sfS_fuel_credit_forall (H:=@fuel_wf Λ)).

Section lifting.
Context `{SI : indexT} `{!lirisGS_gen hlc Λ Σ}.
Implicit Types s : stuckness.
Implicit Types i : thread_id.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Section liveness.

  (* For lwp_step, enable progress and fork. *)
  Lemma lwp_step_progress s i E e1 ν :
    (∀ σ1 ns κ κs τ,
       state_interp σ1 ns (κ ++ κs) τ ={E,∅}=∗
       ∃ q L, toL_thread i q L ∗ ([∗ list] α ∈ L, oblS_credit α (Ord.S ⌈Λ⌉)) ∗
              (⌜ if s is NotStuck then reducible e1 σ1 τ else True ⌝) ∗
              ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                           toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] j ∈ dom efs, toL_thread j 1 []) -∗
                           £ (S (num_laters_per_step ns)) ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
       state_interp σ2 (S ns) κs (τ ∪ dom efs) ∗ ν e2 efs)
    ⊢ lwp_step s i E e1 ν.
  Proof.
    rewrite /lwp_step. iIntros "H % % % % % % % % I". iDestruct "I" as "(%Idom&Id1&IO1&Ig1&#Ioft1&Is1)".
    iMod ("H" with "Is1") as "(%&%&Ht&Hcs&Hstuck&H)".
    iPoseProof (oblS_credit_eq_list with "Hcs") as "Hcs".
    { rewrite ord_S_add. reflexivity. }
    iPoseProof (oblS_credit_split_list with "Hcs") as "[Hcs0 Hcs]".
    iModIntro. iSplitL "Hstuck"; first done.
    iExists Ω1. iSplit; first done. iIntros (??? Hstep ?? Hsf) "Hlc".
    destruct Hsf as [Hffu Hfff].
    iPoseProof (toI_toL_thread_lookup with "[Ig1 Ht]") as "%LUg"; first iFrame. destruct LUg as (L'&LUg&PermL).
    symmetry in PermL. iPoseProof (toL_thread_perm _ _ _ _ PermL with "Ht") as "Ht". rewrite !(big_opL_permutation _ _ _ PermL).
    iPoseProof "Ioft1" as "Ioft1'". iDestruct "Ioft1'" as "[IoftO IoftM]".
    iPoseProof (big_sepM2_lookup_iff with "IoftM") as "%A".
    specialize (A i). destruct A. destruct H0 as [f LUd1]; first eauto. clear H.
    iPoseProof (toI_obl_reset_fuel with "[Ig1 Ht Hcs]") as "[[% Hfb] Ig]"; first iFrame.
    destruct (WFOCM.exists_pos (t:=@fuel_wf Λ)) as [c LTc].
    simpl.
    iMod (schedfairI_credit_from_all _ _ _ c Hffu with "[Id1 Hfb]") as "(Id2&Hfb&Hc)".
    { iFrame. apply elem_of_dom_2 in LUd1. iApply (big_sepS_delete _ _ _ LUd1 with "[Hfb]"). iSplitL.
      - case_decide; [iFrame|done].
      - iApply big_sepS_intro. iModIntro. iIntros. case_decide; [set_solver|done].
    }
    iPoseProof (sfS_fuel_credit_forall_get with "Hc") as "Hc"; first done.
    assert (∃ f2, δ2 !! i = Some f2).
    { pose proof (map_Forall2_lookup_l _ _ _ Hffu _ _ LUd1). destruct H as (?&?&?). eauto. }
    destruct H as [f2 LUd2]. iAssert (∃ f1, sfS_fuel_bound i f1 1)%I with "[Hfb]" as "Hfb".
    { apply elem_of_dom_2 in LUd2. iPoseProof (big_sepS_delete _ _ _ LUd2 with "Hfb") as "[H _]".
      case_decide; first iFrame. exfalso. set_solver.
    }
    iDestruct "Hfb" as "[% Hfb]". iDestruct ("Ig" with "Hfb") as "[Ig1 Ht]".
    iPoseProof (toL_thread_perm _ _ _ _ PermL with "Ht") as "Ht".
    rename L into L_orig, L' into L.

    iPoseProof (toI_assigned_obls_split_dom _ (dom Ω1) with "[Ig1]") as "(%&%&%HDD&#HD1&#HD2)"; first by iFrame.
    destruct HDD as [HOD HDD].
    set (FR:=λ (α : obl_id) (f : fuel Λ), ∃ (i' : thread_id) (L' : list obl_id),
            γ1 !! i' = Some L' ∧ α ∈ L' ∧ ∃ f', δ2 !! i' = Some f' ∧ (fuel_leR f' f)).
    iMod (osat_progress _ L FR FR with "[IO1 Hcs0]") as "(%Ω2&IO2&%HOP&%HMF)".
    { clear L_orig PermL.
      iPoseProof (osat_obl_is_done_weak_set _ D1 with "[IO1]") as "%HD1"; first by iFrame.
      iFrame "IO1". iPoseProof (big_sepM2_forall with "IoftM") as "%M". destruct M as [M1 M2].
      iPoseProof "HD2" as "%HD2".
      assert (mp : ∀ (P Q : Type), P → (P → Q) → Q) by intuition. eapply mp; [eapply oftI_schedule_1|]; eauto.
      { intros. apply elem_of_list_lookup_1 in H1. destruct H1. eapply M2; eauto. Unshelve. all: try apply _. }
      intros MF. pose proof (dom_union_inv_L _ _ _ HDD HOD). destruct H as (m1&m2&HOm&Hmm&Hm1&Hm2).
      subst. rewrite big_sepM_union; [|auto]. iSplitR.
      - iApply (big_sepM_impl (λ _ _, emp)%I); first done.
        iModIntro. iIntros (k o LUk) "_". assert (k ∈ dom m1) by (eapply elem_of_dom_2; eauto).
        specialize (HD1 _ H). destruct HD1. rewrite lookup_union_l in H0.
        2:{ apply not_elem_of_dom. set_solver. }
        rewrite LUk in H0. inv H0. auto.
      - iAssert (
  ([∗ map] k↦y ∈ m2, match y with
                    | obl_live (_, b) =>
                        if decide (k ∈ L)
                        then ∃ c0 : Ord.t, ⌜WFOCM.ltR OCM.unit c0⌝ ∧ oblS_credit k c0 ∧ ⌜∃ b' : fuel Λ, FR k b'⌝
                        else True
                    | _ => True
                    end) ∗
  ([∗ map] k↦y ∈ m2, match y with
                    | obl_live (_, b) =>
                        if decide (k ∈ L)
                        then True
                        else ⌜∃ b' : fuel Λ, fuelR b' b ∧ FR k b'⌝
                    | _ => True
                     end))%I with "[-]" as "H".
        2:{ rewrite -big_sepM_sep. iApply (big_sepM_impl with "H"). iModIntro. iIntros (k o LUk) "[H1 H2]".
            destruct o; try auto. destruct a. destruct (decide (k ∈ L)); iFrame.
        }
        iSplitL.
        + iAssert (
  ([∗ map] k↦y ∈ m2, match y with
                    | obl_live (_, _) =>
                        if decide (k ∈ L)
                        then ∃ c0 : Ord.t, ⌜WFOCM.ltR OCM.unit c0⌝ ∧ oblS_credit k c0
                        else True
                    | _ => True
                    end) ∗
  ([∗ map] k↦y ∈ m2, match y with
                    | obl_live (_, _) =>
                        if decide (k ∈ L)
                        then ⌜∃ b' : fuel Λ, FR k b'⌝
                        else True
                    | _ => True
                     end))%I with "[-]" as "H".
          2:{ rewrite -big_sepM_sep. iApply (big_sepM_impl with "H"). iModIntro. iIntros (k o LUk) "[H1 H2]".
              destruct o; try auto. destruct a. destruct (decide (k ∈ L)); iFrame.
          }
          iSplitL.
          * iClear (HOD HDD HD1 M2 MF HD2 Hmm LUg) "#". iStopProof. revert m2. induction L.
            { iIntros. iApply (big_sepM_impl (λ _ _, True)%I); first done. iModIntro. iIntros.
              destruct x; try auto. destruct a. destruct (decide (k ∈ [])); [set_solver|auto].
            }
            iIntros (m2) "Hc". iPoseProof (big_sepL_cons with "Hc") as "[C Hc]".
            iAssert (
  ([∗ map] k↦y ∈ m2, match y with
                    | obl_live (_, _) =>
                        if decide (k = a)
                        then ∃ c0 : Ord.t, ⌜WFOCM.ltR OCM.unit c0⌝ ∧ oblS_credit k c0
                        else True
                    | _ => True
                    end) ∗
  ([∗ map] k↦y ∈ m2, match y with
                    | obl_live (_, _) =>
                        if decide (k ∈ L)
                        then ∃ c0 : Ord.t, ⌜WFOCM.ltR OCM.unit c0⌝ ∧ oblS_credit k c0
                        else True
                    | _ => True
                     end))%I with "[-]" as "H".
            2:{ rewrite -big_sepM_sep. iApply (big_sepM_impl with "H"). iModIntro.
                iIntros (k o LU) "[H1 H2]". destruct (decide (k ∈ a :: L)).
                - apply elem_of_cons in e. destruct e.
                  + subst. destruct o; auto. destruct a0. rewrite decide_True; done.
                  + destruct o; auto. destruct a0. iClear "H1". rewrite decide_True; done.
                - destruct o; auto. destruct a0. auto.
            }
            iSplitL "C".
            { destruct (m2 !! a) eqn:LU.
              - iApply (big_sepM_delete _ _ _ _ LU with "[C]"). iSplitL.
                + destruct o; auto. destruct a0. rewrite decide_True; [|auto].
                  iFrame. iPureIntro. apply Ord.S_pos.
                + iApply (big_sepM_impl (λ _ _, True)%I); first done.
                  iModIntro. iIntros (k x LU2) "_". destruct x; auto. destruct a0.
                  destruct (decide (k = a)); auto. subst. rewrite lookup_delete in LU2. inv LU2.
              - iApply (big_sepM_impl (λ _ _, True)%I); first done.
                iModIntro. iIntros (k x LU2) "_". destruct x; auto. destruct a0.
                destruct (decide (k = a)); auto. subst. rewrite LU in LU2. inv LU2.
            }
            iApply (IHL with "Hc").
          * iApply big_sepM_forall; first apply _.
            iIntros (k o LU). destruct o; auto. destruct a. destruct (decide (k ∈ L)); auto.
            iPureIntro. subst FR. simpl.
            specialize (Hffu i). rewrite LUd1 in Hffu. inv Hffu. symmetry in H0.
            exists y, i, L. repeat split; eauto. exists y. split; auto.
            eapply (@PreOrder_Reflexive _ _ (OCM.le_PreOrder (t:=(@fuel_wf Λ).(WFOCM.ocm)))).
        + iApply big_sepM_forall; first apply _. iIntros (k o LU). destruct o; auto. destruct a.
          destruct (decide (k ∈ L)); auto. iPureIntro. subst FR.
          pose proof (map_Forall_union_1_2 _ _ _ Hmm MF) as MF2. specialize (MF2 _ _ LU).
          destruct MF2 as (i'&L'&LUg1'&INL'&MF2). destruct (decide (i' = i)).
          * subst. rewrite LUg in LUg1'. inv LUg1'. done.
          * rewrite decide_False in MF2; [|set_solver]. destruct MF2 as (f'&LTf'&f2'&LUd2'&LEf2).
            exists f'. split; [auto|]. exists i', L'. repeat split; auto. exists f2'. split; auto.
    }
    destruct Hfff as (δ'&Hd1&Hd2). apply thread_pool_inv_dom in Hd1. pose proof (fork_thread_ids _ _ _ _ _ _ _ Hstep) as Hefs.
    assert (Hd3 : dom δ2 ## dom δ').
    { subst. rewrite -Hd1. apply fuels_fair_update_dom in Hffu. rewrite -Hffu. auto. }
    iPoseProof (big_sepM2_dom with "IoftM") as "%Hg1".
    assert (Hg2 : dom γ1 ## dom δ').
    { rewrite -Hg1. subst. rewrite -Hd1. auto. }
    pose proof (fuels_fair_update_dom _ _ _ Hffu) as Hddd.
    iPoseProof (oftI_schedule_2 _ _ _ _ _ Hddd with "[Ig1 Ioft1]") as "#Ioft2".
    { econstructor 2; first eapply HOP. reflexivity. }
    { subst FR. simpl in HMF. eapply map_Forall_impl; first eauto. intros. destruct x; auto. destruct a.
      case_decide; eauto.
    }
    { iFrame. iApply "Ioft1". }
    iMod (schedfairI_alloc_threads _ _ _ Hd2 Hd3 with "Id2") as "[Id2 Hfbs]".
    set (γ2 := γ1 ∪ (gset_to_gmap [] (dom δ'))).
    iMod (toI_alloc_threads _ γ2 with "[Ig1 Hfbs]") as "[Ig2 Hts]".
    1,2: eauto.
    { iFrame. }
    iPoseProof (oftI_alloc_threads _ _ δ3 _ γ2 δ' with "Ioft2") as "#Ioft3".
    1,2,3: auto.

    rewrite -Hd1. iDestruct ("H" with "[//] Ht Hc Hts Hlc") as "H".
    iApply (step_fupdN_wand with "H"). iNext. iIntros ">[Is2 H]".
    iModIntro. iExists Ω2, Ω2. iSplit.
    { iPureIntro. split.
      - by econstructor 1.
      - reflexivity.
    }
    iExists γ2. by iFrame.
  Qed.

  (* For ghost_step, enable allocating and fulfilling an obligation. *)
  Lemma ghost_step_alloc_obl a T R E ν :
    (∀ σ ns κs τ,
       state_interp σ ns κs τ ={E,∅}=∗
       ∃ i L, toL_thread i 1 L ∗
              ∀ κ, (toL_thread i 1 (κ :: L) ∗ oblG_goal κ T R ∗ oblS_active κ ∗ toS_assigned i κ ∗ oblS_credit κ a ∗ ∃ b, oblS_bound κ b) ={∅,E}=∗
                   state_interp σ ns κs τ ∗ ν)
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % % % % I". iDestruct "I" as "(%Idom&Id1&IO1&Ig1&#Ioft1&Is1)".
    iDestruct ("H" with "Is1") as ">(%&%&Ht&H)".
    iPoseProof (toI_toL_thread_lookup with "[Ig1 Ht]") as "(%&%LUg&%PermL)"; first iFrame.
    iPoseProof "Ioft1" as "Ioft1'". iDestruct "Ioft1'" as "[IoftO IoftM]".
    iPoseProof (big_sepM2_lookup_iff with "IoftM") as "%A".
    specialize (A i). destruct A. destruct H0 as [f LUd]; first eauto. clear H.
    iMod (osat_alloc_obl _ (a ⊕ ⌈Λ⌉)%ord f T R with "IO1") as "(%κ & %LUκ & IO2 & #Hog & Hoi & Hol & Hoc & #Hob)".
    iPoseProof (oblS_credit_split with "Hoc") as "[Hoc1 Hoc2]".
    iMod (osat_step_one_obl_init_live with "[IO2 Hoi]") as "[IO2 #Hoa]"; first apply lookup_insert.
    { iFrame. rewrite /oblG_elem. eauto. }
    rewrite insert_insert.
    iMod (toI_alloc_obl with "[Ig1 Ht Hol Hoc2]") as "(Ig1 & Ht & #Hta)".
    { iFrame. rewrite /oblG_elem. iSplit; eauto. }
    iPoseProof (oftI_alloc_obl _ _ _ κ i f f _ (a ⊕ ⌈Λ⌉)%ord LUκ LUd _ LUg with "[]") as "#Ioft2"; first auto.
    Unshelve.
    2:{ eapply (@PreOrder_Reflexive _ _ (OCM.le_PreOrder (t:=(@fuel_wf Λ).(WFOCM.ocm)))). }
    iMod ("H" with "[Ht Hoc1]") as "[Hs H]".
    { iFrame. eauto. }
    iModIntro. iExists (<[κ:=obl_live ((a ⊕ ⌈ Λ ⌉)%ord, f)]> Ω). iSplit.
    { iPureIntro. econstructor 2.
      - econstructor 1. exists κ. exists ((a ⊕ ⌈ Λ ⌉)%ord, f). split; [auto | reflexivity].
      - econstructor 2; [|reflexivity]. eapply (obl_states_step_step_one _ κ).
        apply map_Forall2_insert; auto. split.
        + rewrite decide_True; done.
        + intros j. destruct (decide (j = κ)).
          * subst. rewrite !LUκ. econstructor.
          * destruct (Ω !! j); done.
    }
    iExists (<[i:=κ :: L]> γ). iPoseProof (oftI_one_permutation _ _ _ i (κ :: l') (κ :: L) with "Ioft2") as "Ioft3".
    { apply lookup_insert. }
    { econstructor. auto. }
    rewrite insert_insert. by iFrame.
  Qed.

  Lemma ghost_step_fulfill_obl κ E ν :
    (∀ σ ns κs τ,
       state_interp σ ns κs τ ={E,∅}=∗
       ∃ i L T R, (toL_thread i 1 (κ :: L) ∗ oblG_goal κ T R ∗ oblS_active κ ∗ ⌜ T σ ⌝ ∗ ▷ R) ∗
                  (toL_thread i 1 L ∗ oblS_done κ ={∅,E}=∗
                   state_interp σ ns κs τ ∗ ν))
    ⊢ ghost_step E ν.
  Proof.
    rewrite /ghost_step. iIntros "H % % % % % % % I". iDestruct "I" as "(%Idom&Id1&IO1&Ig1&#Ioft1&Is1)".
    iDestruct ("H" with "Is1") as ">(%&%&%&%& (Ht&#Hog&#Hoa&%HT&HR) &H)".
    iPoseProof (toI_toL_thread_lookup with "[Ig1 Ht]") as "(%&%LUg&%PermL)"; first iFrame.
    iMod (toI_fulfill_obl with "[Ig1 Ht]") as "[Hol Htt]"; first iFrame.
    iPoseProof (osat_obl_is_live with "[IO1 Hol]") as "[% %LUO]".
    { iFrame. rewrite /oblG_elem. eauto. }
    iMod (osat_step_one_obl_live_done with "[IO1 Hol HR]") as "[IO2 #Hod]"; first (iFrame; eauto).
    iPoseProof ("Htt" with "Hod") as "[Ig2 Ht]".
    iPoseProof (toI_oblS_done_notin with "[Ig2]") as "%NIN"; first by iFrame.
    assert (IN : is_Some (Ω !! κ)) by eauto.
    iPoseProof (oftI_fulfill_obl _ _ _ κ i _ _ T IN LUg PermL NIN with "Ioft1") as "Ioft2".
    iMod ("H" with "[Ht]") as "[Hs H]"; first by iFrame.
    iModIntro. iExists (<[κ:=obl_done T]> Ω). iSplit.
    { iPureIntro. econstructor 2; [|reflexivity]. eapply (obl_states_step_step_one _ κ).
      intros x. destruct (decide (x = κ)).
      - subst. rewrite LUO lookup_insert. econstructor. simpl. auto.
      - rewrite lookup_insert_ne; auto. destruct (Ω !! x); econstructor; auto.
    }
    iExists (<[i:=L]> γ). iFrame. auto.
  Qed.

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
  (∀ δ1 (Ω1 : obl_statesL Λ) γ1 σ1 ns κ κs τ,
     (⌜ τ = dom δ1 ⌝ ∗ schedfairIL Λ δ1 ∗ osat Ω1 ∗ toIL Λ γ1 ∗ oftIL Λ Ω1 δ1 γ1 ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
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
  - iIntros (????????) "_". iApply fupd_mask_intro; auto with set_solver.
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
