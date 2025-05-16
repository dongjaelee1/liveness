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
                           toL_thread i q L -∗ sfS_fuel_credit_forallL Λ -∗ ([∗ set] i ∈ dom efs, toL_thread i 1 []) -∗
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
              ∀ κ, toL_thread i 1 (κ :: L) -∗
                   (oblG_goal κ T R ∗ oblS_active κ ∗ toS_assigned i κ ∗ oblS_credit κ a ∗ ∃ b, oblS_bound κ b) ={∅,E}=∗
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
    iMod ("H" with "Ht [Hoc1]") as "[Hs H]".
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

  Lemma ghost_step_fulfill_obl a T R E ν :
    (∀ σ ns κs τ,
       state_interp σ ns κs τ ={E,∅}=∗
       ∃ i L, toL_thread i 1 L ∗
              ∀ κ, toL_thread i 1 (κ :: L) -∗
                   (oblG_goal κ T R ∗ oblS_active κ ∗ toS_assigned i κ ∗ oblS_credit κ a ∗ ∃ b, oblS_bound κ b) ={∅,E}=∗
                   state_interp σ ns κs τ ∗ ν)
    ⊢ ghost_step E ν.
  Proof.


    TODO

oftI_alloc_obl:
  ∀ {SI : indexT} {A : Type} {leR : A → A → Prop} {addO : A → A → A} {ltR : A → A → Prop} {WF : WFOCM.t leR addO ltR} 
    {ps : Type} {OC : obl_class ps (Ord.t * A)} {Σ : gFunctors} {H1 : threadoblGS.threadoblGS Σ} (Ω : obl_states' OC) 
    (δ : gmap thread_id A) (γ : gmap thread_id (list obl_id)) (κ : obl_id) i (f f' : A) (l : list obl_id) 
    (a : Ord.t),
    Ω !! κ = None
    → δ !! i = Some f
      → leR f f' → γ !! i = Some l → oftI Ω δ γ ∗ toS_assigned i κ ⊢ oftI (<[κ:=obl_live (a, f')]> Ω) δ (<[i:=κ :: l]> γ)

(* Ω must make strict progress *)
Definition lwp_step `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ)
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ) : iPropO Σ :=
  (∀ δ1 (Ω1 : obl_statesL Λ) γ1 σ1 ns κ κs τ,
     (schedfairIL Λ δ1 ∗ osat Ω1 ∗ toIL Λ γ1 ∗ oftIL Λ Ω1 δ1 γ1 ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
     (⌜if s is NotStuck then reducible e1 σ1 τ else True⌝) ∗
     ∃ Ω2, (⌜(Ω1 ↪ₛ⋆ Ω2 @ σ1)⌝) ∗
           ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗
                        ∀ δ2 δ3, (⌜fuels_fair_update {[i]} δ1 δ2 ∧ fuels_fair_fork efs δ2 δ3⌝) -∗
                                    £ (S (num_laters_per_step ns)) ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
     ∃ Ω3 Ω4, (⌜(Ω2 ↪ₚ⁺ Ω3) ∧ (Ω3 ↪ₛ⋆ Ω4 @ σ2)⌝) ∗
              ∃ γ2, (schedfairIL Λ δ3 ∗ osat Ω4 ∗ toIL Λ γ2 ∗ oftIL Λ Ω4 δ3 γ2 ∗ state_interp σ2 (S ns) κs (τ ∪ dom efs)) ∗
                    ν e2 efs
  )%I.
(* Ω can allocate, progress, or fulfills obligations. Note this has no later modality. *)
Definition ghost_step `{SI : indexT} `{!lirisGS_gen hlc Λ Σ} (E : coPset)
  (ν : iPropO Σ) : iPropO Σ :=
  (∀ δ (Ω : obl_statesL Λ) γ σ ns κs τ,
     (schedfairIL Λ δ ∗ osat Ω ∗ toIL Λ γ ∗ oftIL Λ Ω δ γ ∗ state_interp σ ns κs τ) ={E}=∗
     ∃ Ω', (⌜(Ω ↪ₛ⋆ Ω' @ σ)⌝) ∗
           ∃ γ', (schedfairIL Λ δ ∗ osat Ω' ∗ toIL Λ γ' ∗ oftIL Λ Ω' δ γ' ∗ state_interp σ ns κs τ) ∗
                 ν
  )%I.

End liveness.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma lwp_lift_step_fupdN s i E Φ e1 :
  to_val e1 = None →
  (∀ δ1 (Ω1 : obl_statesL Λ) γ1 σ1 ns κ κs τ,
     (schedfairIL Λ δ1 ∗ osat Ω1 ∗ toIL Λ γ1 ∗ oftIL Λ Ω1 δ1 γ1 ∗ state_interp σ1 ns (κ ++ κs) τ) ={E,∅}=∗
     ⌜if s is NotStuck then reducible e1 σ1 τ else True⌝ ∗ ∃ Ω2,
       (⌜(Ω1 ↪ₛ⋆ Ω2 @ σ1)⌝) ∗ ∀ e2 σ2 efs, (⌜prim_step e1 σ1 τ κ e2 σ2 efs⌝) -∗ ∀ δ2 δ3,
     (⌜fuels_fair_update {[i]} δ1 δ2 ∧ fuels_fair_fork efs δ2 δ3⌝) -∗
     £ (S $ num_laters_per_step ns) ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
     ∃ Ω3 Ω4, (⌜(Ω2 ↪ₚ⁺ Ω3) ∧ (Ω3 ↪ₛ⋆ Ω4 @ σ2)⌝) ∗
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
     ∃ Ω3 Ω4, (⌜(Ω2 ↪ₚ⁺ Ω3) ∧ (Ω3 ↪ₛ⋆ Ω4 @ σ2)⌝) ∗
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
     ∃ Ω3 Ω4, (⌜(Ω2 ↪ₚ⁺ Ω3) ∧ (Ω3 ↪ₛ⋆ Ω4 @ σ2)⌝) ∗
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
