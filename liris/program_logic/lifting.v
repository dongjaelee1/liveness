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
    try rewrite !gupd.wit_credit_unseal /gupd.wit_credit_def;
    try rewrite !gupd.wit_unseal /gupd.wit_def;
    try rewrite !gupd.th_term_unseal /gupd.th_term_def;
    try rewrite !gupd.th_obls_unseal /gupd.th_obls_def;
    try rewrite !gupd.gl_variant_cases_unseal /gupd.gl_variant_cases_def;
    try rewrite !gupd.gl_variant_unseal /gupd.gl_variant_def;
    try rewrite !gupd.gl_fuel_unseal /gupd.gl_fuel_def;
    try rewrite !gupd.gl_expired_unseal /gupd.gl_expired_def;
    try rewrite !gupd.gl_current_unseal /gupd.gl_current_def;
    try rewrite !gupd.gl_done_unseal /gupd.gl_done_def;
    try rewrite !gupd.gl_locked_unseal /gupd.gl_locked_def;
    try rewrite !gupd.gl_witfun_unseal /gupd.gl_witfun_def;
    try rewrite !gupd.gl_unseal /gupd.gl_def.

  Section sfoupd.

    Lemma gl_alloc_obl E i G q ξ N v P Q R :
      th_obls i G q -∗
      (▷ P) -∗
      |={E}=>g ∃ k, (⌜ G !! k = None ⌝) ∗
                   th_obls i (<[k:=v]>G) q ∗
                   gl_witfun k ξ ∗ gl k v ∗ gl_fuel k (Σ[ξ] v) ∗
                   gl_variant N k v P Q R ∗
                   wit k v (gupd_η (Σ[ξ] v)) ∗
                   ([∗ set] u ∈ set_seq 0 v, gl_done k u).
    Proof.
      iIntros "Tb HP %%% $". iApply (gl_alloc_obl_0 _ Θ with "Tb HP").
    Qed.

    Lemma gl_alloc_done E ξ N v P Q R :
      (▷ Q) -∗
      |={E}=>g ∃ k, gl_witfun k ξ ∗ gl k v ∗ gl_current k v ∗ gl_done k v ∗ gl_fuel k (Σ[ξ] v) ∗
                   gl_variant N k v P Q R ∗
                   wit k v (gupd_η (Σ[ξ] v)) ∗
                   ([∗ set] u ∈ set_seq 0 (S v), gl_done k u).
    Proof.
      iIntros "HQ %%% $". iApply (gl_alloc_done_0 _ Θ with "HQ").
    Qed.

    Lemma gl_lock E i G q k ξ N v1 v2 P1 Q1 R1 P2 Q2 R2 :
      v1 < v2 →
      ↑N ⊆ E →
      gl_current k v1 -∗
      gl_done k v1 -∗
      gl_variant N k v1 P1 Q1 R1 -∗
      |={E,E ∖ ↑N}=> (▷ (gl_current k v1 ∗ Q1)) ∗
                    (th_obls i G q -∗
                     gl_current k v1 -∗
                     gl_witfun k ξ -∗
                     (▷ R1) -∗
                     (▷ P2) -∗
                     |={∅}=>g |={E ∖ ↑N,E}=> 
                       (th_obls i (<[k:=v2]>G) q ∗
                        gl k v2 ∗ gl_fuel k (Σ[ξ]{S v1, v2}) ∗
                        gl_variant N k v2 P2 Q2 R2 ∗
                        wit k v2 (gupd_η (Σ[ξ] v2)) ∗
                        ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), wit k u (gupd_η (Σ[ξ] u))) ∗
                        ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), gl_done k u))).
    Proof.
      iIntros (Hv Mask) "Gc Gd Gv". iMod (gl_lock_0 with "Gc Gd Gv") as "[$ H]". 1,2: eauto.
      iIntros "!> Tb Gc Gw HR HP". iPoseProof ("H" with "Tb Gc Gw HR HP") as "H".
      iIntros "%%% $". iMod ("H" $! Θ) as "H". iModIntro. done.
    Qed.

    Lemma gl_unlock E i G q N k v P Q R :
      ↑N ⊆ E →
      G !! k = Some v →
      th_obls i G q -∗
      gl_variant N k v P Q R -∗
      |={E,E ∖ ↑N}=> (▷ (th_obls i G q ∗ gl_locked k v ∗ P)) ∗
                    (th_obls i G q -∗
                     gl_locked k v -∗
                     (▷ Q) -∗
                     |={∅}=>g |={E ∖ ↑N,E}=>
                       (th_obls i (delete k G) q ∗ gl_current k v ∗ gl_done k v)).
    Proof.
      iIntros (Mask LUGk) "Tb Gv". iMod (gl_unlock_0 with "Tb Gv") as "[$ H]". 1,2: eauto.
      iIntros "!> Tb Gl HQ". iPoseProof ("H" with "Tb Gl HQ") as "H".
      iIntros "%%% $". iMod ("H" $! Θ) as "H". iModIntro. done.
    Qed.

    Lemma gl_change_owner i1 i2 G1 G2 q1 q2 k v :
      G1 !! k = Some v →
      th_obls i1 G1 q1 -∗
      th_obls i2 G2 q2 -∗
      gl_fuel k Ord.one -∗
      |={∅}=>g th_obls i1 (delete k G1) q1 ∗ th_obls i2 (<[k:=v]>G2) q2 ∗ ⌜ G2 !! k = None ⌝.
    Proof.
      iIntros (LUG1) "Tb1 Tb2 Gf %%% $".
      iMod (gl_change_owner_0 with "Tb1 Tb2 Gf") as "H". 1: eauto.
      by iModIntro.
    Qed.

  End sfoupd.

  Section lwp_step.

    (* For lwp_step, enable progress and fork. *)
    Lemma lwp_step_step s i E e1 ν :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
         (⌜ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗
         ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
           (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
              th_obls i G 1 -∗ ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
              ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
              ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs)))
      ⊢ lwp_step s i E e1 ν.
    Proof.
      unfold_defs. iIntros "H". iIntros (????) "SI".
      iMod ("H" with "SI") as "($& %& (#Oe& Ox& Ob& OS)& GFs& %& #REs& H)".
      iIntros "!> !> % % % %Step % % (S& O& A& W& %GWI1)".
      iAssert (⌜ dom G ⊆ dom Ω1 ⌝)%I as "%GOSub".
      { rewrite elem_of_subseteq. iIntros (x INGx).
        apply elem_of_dom in INGx. destruct INGx as (?& INGx).
        iPoseProof (big_sepM_delete _ _ _ _ INGx with "GFs") as "[(#Bex& _) _]".
        iApply (glsat_elem with "[$S $Bex]").
      }
      iAssert ([∗ map] k ↦ _ ∈ Ω1, (⌜ k ∈ dom G ⌝ ∗ glG_fuel (GL:=ord_ghost_lock_class) k Ord.one) ∨ (⌜ k ∉ dom G ⌝))%I with "[GFs]" as "GFs".
      { rewrite !big_sepM_dom. replace (dom Ω1) with ((dom G) ∪ (dom Ω1 ∖ (dom G))).
        2:{ rewrite -union_difference_L; auto. }
        iApply (big_sepS_union). 1: set_solver.
        iSplitL.
        - iApply (big_sepS_impl with "GFs"). iIntros "!>" (??) "(_& Bfx)". iLeft. iFrame. done.
        - iApply big_sepS_intro. iIntros "!>" (??). iRight. iPureIntro. set_solver + H.
      }
      iAssert (∀ g, ⌜ g ∈ dom G ⌝ → ∃ o, ⌜ Ω1 !! g = Some o ∧ gl_cond_owner i g o ⌝)%I as "%LUG".
      { iIntros (g INGg). pose proof INGg. apply elem_of_dom in H. destruct H as (?& LUGg).
        iPoseProof (big_sepM_delete _ _ _ _ LUGg with "OS") as "[(#Ge& Gl& Gv& Go& Oo) _]".
        iPoseProof (globl_obls_lookup _ _ g _ _ _ INGg with "[$S $O $Oe $Ob $Ge]") as "(%& %& %)".
        iExists _. iPureIntro. done.
      }
      iAssert (∀ k, ⌜ k ∈ dom Ω1 ⌝ → ⌜ k ∉ dom G ⌝ → ∃ o, ⌜ Ω1 !! k = Some o ∧ ¬ gl_cond_owner i k o ⌝)%I as "%NotG".
      { iIntros (k INOk NINGk). apply elem_of_dom in INOk. destruct INOk.
        destruct (decide (gl_cond_owner i k x)); eauto.
        iExFalso. destruct x. destruct g1; last done. simpl in *. subst.
        iPoseProof (globl_assigned_obls_lookup _ _ k with "[$S $O $A $Ob]") as "%".
        { apply H. }
        done.
      }
      iAssert ([∗ map] k ↦ o ∈ Ω1, (⌜ gl_cond_owner i k o ⌝ ∗ (∃ c, ⌜ WFOCM.ltR OCM.unit c ⌝ ∗ glG_fuel k c)) ∨ (⌜ ¬ gl_cond_owner i k o ⌝))%I with "[GFs]" as "GFs".
      { iApply (big_sepM_impl with "GFs"). iIntros "!>" (???) "[(%& Bfk) | %]".
        - iLeft. iFrame "Bfk". iPureIntro; split.
          + apply LUG in H0. destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
          + apply Ord.S_pos.
        - iRight. iPureIntro. apply NotG in H0.
          + destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
          + apply elem_of_dom; eauto.
      }
      assert (DomOW : dom Ω1 = dom W1) by (eapply glwit_inv_dom; eauto).
      iAssert (⌜ dom R ⊆ dom W1 ⌝)%I as "%RWSub".
      { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
        pose proof INRx. apply elem_of_dom in H. destruct H.
        iPoseProof (big_sepM_delete _ _ _ _ H with "REs") as "[[#Beg _] _]".
        iPoseProof (glsat_elem with "[$S $Beg]") as "%". done.
      }
      iMod (glsat_progress with "[$S $GFs]") as "(%Ω2& S& %ProgO)".
      { intros. destruct g. destruct g0; eauto. done. }
      iModIntro. iExists Ω2. iSplitR; first done. iIntros (W2 (ProgW& GWI2)).
      iMod (glwit_progress with "W") as "[W Ws]". 1: eauto.
      assert (HW1 : ∃ WR WR', WR ##ₘ WR' ∧ W1 = WR ∪ WR' ∧ dom R = dom WR).
      { clear GWI1 DomOW ProgW.
        revert R RWSub. induction W1 using map_ind; intros.
        { assert (dom R = ∅) by (set_solver). apply dom_empty_inv_L in H. subst. exists ∅, ∅. done. }
        rename i0 into r. rewrite dom_insert_L in RWSub. destruct (decide (r ∈ dom R)).
        - set (R2 := delete r R). assert (dom R2 ⊆ dom m).
          { subst R2. rewrite dom_delete_L. set_solver + RWSub. }
          apply elem_of_dom in e. destruct e. rename H1 into LUR.
          destruct (IHW1 _ H0) as (WR&WR'&?&?&?).
          exists (<[r:=x]>WR), WR'. subst R2.
          assert (WR !! r = None ∧ WR' !! r = None).
          { apply lookup_union_None. rewrite -H2; auto. }
          destruct H4. split_and !.
          + apply map_disjoint_insert_l. split; auto.
          + subst. rewrite insert_union_l. done.
          + replace R with (<[r:=x0]> (delete r R)).
            * rewrite !dom_insert_L H3. auto.
            * rewrite insert_delete_id; auto.
        - assert (dom R ⊆ dom m).
          { set_solver + RWSub n. }
          pose proof H0. apply IHW1 in H1. destruct H1 as (WR& WR'& ?&?&?).
          assert (WR !! r = None ∧ WR' !! r = None).
          { apply lookup_union_None. rewrite -H2; auto. }
          destruct H4. exists WR, (<[r:=x]>WR'). split_and !; auto.
          + apply map_disjoint_insert_r. split; auto.
          + subst. rewrite insert_union_r; done.
      }
      destruct HW1 as (WR& WR'& DisjWR& EQWR& DomWR).
      assert (DomO : fst <$> Ω1 = fst <$> Ω2).
      { destruct ProgO. apply map_eq. intros j. rewrite !lookup_fmap. specialize (H0 j).
        destruct (Ω1 !! j) eqn:LUO1.
        - inv H0. destruct g, y. inv H3. rewrite LUO1 -H2. done.
        - inv H0. rewrite LUO1 -H1. done.
      }
      assert (EQfst : fst <$> Ω2 = fst <$> W1).
      { rewrite -DomO. apply map_eq. intros j. destruct ProgO.
        specialize (GWI1 j). rewrite !lookup_fmap. destruct (W1 !! j) eqn:LUW1.
        - rewrite LUW1. rewrite LUW1 in GWI1. inv GWI1. destruct x. destruct w. destruct H3. by subst.
        - rewrite LUW1. rewrite LUW1 in GWI1. inv GWI1. done.
      }
      iAssert (⌜ ∀ k v, R !! k = Some v → ∃ w, WR !! k = Some w ∧ v ≤ w.1 ⌝)%I as "%Rver".
      { iIntros (k v LUR). iPoseProof (big_sepM_delete _ _ _ _ LUR with "REs") as "[(#Ge& #Gvl) _]".
        iPoseProof (glsat_lookup_version_lb with "[$S $Ge $Gvl]")as "(%&%&%&%)".
        rewrite map_eq_iff in EQfst. specialize (EQfst k). rewrite !lookup_fmap H in EQfst.
        assert (is_Some (WR !! k)).
        { apply elem_of_dom. rewrite -DomWR. apply elem_of_dom; eauto. }
        destruct H1 as (?& LUWRk).
        assert (WR' !! k = None).
        { eapply map_disjoint_Some_l; eauto.  }
        destruct (W1 !! k) eqn:LUW1.
        - rewrite LUW1 in EQfst. inv EQfst. apply lookup_union_Some_inv_l in LUW1; eauto.
        - rewrite LUW1 in EQfst. inv EQfst.
      }
      iAssert (|==> [∗ map] r↦v ∈ R, (witG_credit (GL:=ord_ghost_lock_class) r v Ord.one) ∨
                                    (glG_unlocked r v))%I
        with "[Ws]" as ">Rs".
      { subst W1. iPoseProof (big_sepM_union with "Ws") as "[Ws1 _]"; first auto.
        iApply big_sepM_bupd. iClear "Oe REs". clear dependent WR'.
        iStopProof. revert R DomWR Rver. induction WR using map_ind; iIntros (R DomWR Rver) "M".
        { apply dom_empty_inv_L in DomWR. subst. done. }
        rename i0 into r. rewrite dom_insert_L in DomWR. destruct (R !! r) eqn:LUR; cycle 1.
        { exfalso. apply not_elem_of_dom in LUR. set_solver + DomWR LUR. }
        remember (delete r R) as R0.
        assert (dom R0 = dom m).
        { subst. rewrite dom_delete_L. apply not_elem_of_dom in H. rewrite DomWR. set_solver + H. }
        assert (R0 !! r = None).
        { subst. apply lookup_delete_eq. }
        assert (R = <[r:=g]>R0).
        { subst. rewrite insert_delete_id; auto. }
        rewrite H2.
        assert (∀ k v, R0 !! k = Some v → ∃ w, m !! k = Some w ∧ v ≤ w.1).
        { intros. specialize (Rver k v). subst. destruct (decide (k = r)).
          { subst. rewrite lookup_delete_eq in H3. inv H3. }
          rewrite lookup_delete_ne in H3; auto. apply Rver in H3. destruct H3 as (?&?&?).
          rewrite lookup_insert_ne in H3; eauto.
        }
        destruct (Rver _ _ LUR) as (w& LUmk& LEv). rewrite lookup_insert_eq in LUmk.
        clear dependent R. inv LUmk. rewrite !big_sepM_insert; auto.
        destruct w. iDestruct "M" as "[H M]". iPoseProof (IHWR _ H0 H3 with "M") as "$".
        iDestruct "H" as "(#H1& #H2& H)". simpl in LEv. destruct w.
        - assert (g = n ∨ g < n) by lia. destruct H2.
          + subst. iDestruct "H" as "(%& %& Wc)". apply ord_lt_one in H2.
            iLeft. iMod (witG_credit_mon_split with "Wc") as "[_ $]"; done.
          + assert (g ∈ (set_seq 0 n : gset _)).
            { apply elem_of_set_seq. lia. }
            iPoseProof (big_sepS_delete _ _ _ H4 with "H1") as "[(_& Gu) _]".
            iRight. auto.
        - assert (g = n ∨ g < n) by lia. destruct H2.
          + subst. iRight. auto.
          + assert (g ∈ (set_seq 0 n : gset _)).
            { apply elem_of_set_seq. lia. }
            iPoseProof (big_sepS_delete _ _ _ H4 with "H1") as "[(_& Gu) _]".
            iRight. auto.
      }
      iAssert ([∗ map] r↦v ∈ R,
                 ((glG_elem r ∗ glG_version_lb r v) ∗
                  witG_credit (GL:=ord_ghost_lock_class) r v Ord.one) ∨
                   ((glG_elem r ∗ glG_version_lb r v) ∗ glG_unlocked r v))%I
        with "[Rs]" as "Rs".
      { iPoseProof (big_sepM_sep with "[$Rs $REs]") as "H". iApply (big_sepM_impl with "H").
        iIntros "!> %%% ([Wc | #Gu]& #Ge& #Gvl)".
        - iLeft. iFrame. auto.
        - iRight. auto.
      }
      iMod (globl_alloc_threads (dom efs) with "O") as "[O Efs]".
      { symmetry. eapply fork_thread_ids; eauto. }
      iMod ("H" with "[//] [$Ob $Ox $Oe $OS] Rs [Efs]") as "H".
      { iApply (big_sepS_impl with "Efs"). iIntros "!> %% ($& $& $)". done. }
      iModIntro. rewrite DomO /gproto. iFrame. iSplitR.
      { done. }
      iMod "H". iModIntro. done.
    Qed.

    TODO


      Lemma lwp_step_account_pc s i E e1 ν :
        (∀ Θ σ1 κ κs,
           state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
           (⌜ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
           ∃ G q,
             (othreadG_elem i ∗ othreadG_obls i G 1 ∗
              [∗ set] ρ ∈ G, oblG_elem ρ ∗ othreadG_owns i ρ true q ∗ glG_fuel ρ Ord.one) ∗
             ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                          othreadG_obls i G 1 -∗ ([∗ set] ρ ∈ G, othreadG_owns i ρ true q) -∗
                          ([∗ set] j ∈ dom efs, othreadG_elem j ∗ othreadG_obls j ∅ 1 ∗ othreadG_exec j (1/2)) -∗
                          ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs))
        ⊢ lwp_step s i E e1 ν.
      Proof.
        rewrite /lwp_step. iIntros "H % % % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" with "I") as "(%Hstuck& %&%& (#Tei& Tbsi& Bps)& H)".
        iModIntro. iSplitR; first done. iExists Ω1. iSplitR; first done.
        iIntros (??? Hstep).
        iMod (oforest_progress_one_thread _ _ _ G (gset_to_gmap (true, q) G) with "[S T F Tbsi Bps]")
          as "(%& %Hprog& S& T& F& Tbsi &Tos)".
        { by rewrite dom_gset_to_gmap. }
        { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap. iApply (big_sepS_impl with "Bps").
          iIntros "!>" (??). iIntros "(E& O& P)". iFrame. iPureIntro. apply Ord.S_lt. }
        rewrite big_sepM_gset_to_gmap.
        iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
        { symmetry. eapply fork_thread_ids; eauto. }
        iModIntro. iMod ("H" with "[//] Tbsi Tos Efs") as ">[I H]".
        iModIntro. iExists Ω1, Ω', Ω'.
        assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
        iFrame. iPureIntro. split; done.
      Qed.

      Lemma lwp_step_suspended_pc s i E e1 ν :
        (∀ Θ σ1 κ κs,
           state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
           (⌜ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
           ∃ π G K,
             (⌜G = dom K⌝ ∗ othreadG_elem i ∗ othreadG_obls i G 1 ∗ oblG_elem π ∗ otreeG_elem π ∗
              ([∗ set] ρ ∈ G, oblG_elem ρ ∗ glG_fuel ρ Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_elem k ∗ otreeG_suspend k x i π ψ ∗ otreeG_wait k x (1/2))) ∗
             ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                          othreadG_obls i G 1 -∗
                          ((([∗ set] ρ ∈ G, glG_fuel ρ Ord.one) ∗
                            ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_wait k x (1/2))) ∨
                             (oblG_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k true (1/2) ∗ glG_fuel k ψ))) -∗
                          ([∗ set] j ∈ dom efs, othreadG_elem j ∗ othreadG_obls j ∅ 1 ∗ othreadG_exec j (1/2)) -∗
                          ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗ ν e2 efs))
        ⊢ lwp_step s i E e1 ν.
      Proof.
        rewrite /lwp_step. iIntros "H % % % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" with "I") as "(%Hstuck& %&%&%& (%Dom& #Tei& Tbsi& Bps)& H)".
        iModIntro. iSplitR; first done. iExists Ω1. iSplitR; first done.
        iIntros (??? Hstep).
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
          iMod (oforest_progress_one_thread _ _ _ G (gset_to_gmap (false, (1/2)%Qp) G) with "[S T F Tbsi Fos]")
            as "(%& %Hprog& S& T& F& Tbsi& Fos)".
          { by rewrite dom_gset_to_gmap. }
          { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap big_sepS_sep Dom -!big_sepM_dom.
            iSplitR; first auto. iApply (big_sepM_impl with "Fos"). iIntros "!>" (???) "H". by destruct x. }
          iPoseProof (big_sepM_gset_to_gmap with "Fos") as "Fos". iPoseProof ("U" with "[Fes Fos]") as "U".
          { subst G. rewrite -big_sepM_dom. iPoseProof (big_sepM_sep_2 with "Fos Fes") as "Fs".
            iApply (big_sepM_impl with "Fs"). iIntros "!>" (???) "H". by destruct x. }
          iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
          { symmetry. eapply fork_thread_ids; eauto. }
          iModIntro. iMod ("H" with "[//] Tbsi [Bps Fws] Efs") as ">[I H]".
          { iLeft. iSplitR "Fws".
            - iPoseProof (big_sepS_sep with "Bps") as "[H1 H2]". iFrame.
            - iApply (big_sepM_impl with "Fws"). iIntros "!>" (???) "H". by destruct x. }
          iModIntro. iExists Ω1, Ω', Ω'.
          assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
          iFrame. iPureIntro. split; done.
        - rewrite !big_sepM_fmap.
          iAssert (
              ([∗ map] k ↦ _ ∈ K, othreadG_owns i k true (1/2) ∗ glG_fuel k Ord.one) ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, glG_fuel k ψ)
            )%I with "[Bps M]" as "[Tos Bps]".
          { subst G. rewrite -big_sepM_dom -big_sepM_sep. iPoseProof (big_sepM_sep_2 with "Bps M") as "M".
            iApply (big_sepM_impl with "M"). iIntros "!>" (???) "H". destruct x. iDestruct "H" as "((_&B)&C&D)". iFrame. }
          iMod (oforest_progress_one_thread _ _ _ G (gset_to_gmap (true, (1/2)%Qp) G) with "[S T F Tbsi Tos]")
            as "(%& %Hprog& S& T& F& Tbsi& Fos)".
          { by rewrite dom_gset_to_gmap. }
          { iFrame. iSplitR; first auto. rewrite big_sepM_gset_to_gmap big_sepS_sep Dom -!big_sepM_dom.
            iSplitR; first auto. iApply (big_sepM_impl with "Tos"). iIntros "!>" (???) "[H1 H2]".
            iFrame. iPureIntro. apply Ord.S_pos. }
          iPoseProof (big_sepM_gset_to_gmap with "Fos") as "Fos".
          iMod (othread_alloc_threads (dom efs) with "T") as "[T Efs]".
          { symmetry. eapply fork_thread_ids; eauto. }
          iModIntro. iMod ("H" with "[//] Tbsi [Bps Fos] Efs") as ">[I H]".
          { iRight. iSplitR; first auto. subst G. rewrite -big_sepM_dom.
            iPoseProof (big_sepM_sep_2 with "Fos Bps") as "H".
            iApply (big_sepM_impl with "H"). iIntros "!>" (???) "H". by destruct x. }
          iModIntro. iExists Ω1, Ω', Ω'.
          assert (dom Ω1 = dom Ω') by (eapply obl_states_cond_rel_dom; eauto). rewrite !H.    
          iFrame. iPureIntro. split; done.
      Qed.

      (* For ghost_step, enable allocating, progressing, suspendring, resolving and waiting for obligations. *)
      Lemma ghost_step_wait_obls E ν :
        (∀ Θ σ κs,
           state_interp σ Θ κs ={E,∅}=∗
           ∃ i G π K,
             (⌜G = dom K⌝ ∗ othreadG_elem i ∗ othreadG_obls i G 1 ∗ oblG_elem π ∗ otreeG_elem π ∗
              ([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_elem k ∗ otreeG_suspend k x i π ψ ∗ otreeG_wait k x (1/2))) ∗
             (othreadG_obls i G 1 -∗
              (([∗ map] k ↦ '(x, ψ) ∈ K, otreeG_wait k x (1/2)) ∨
                 (oblG_done π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othreadG_owns i k true (1/2) ∗ glG_fuel k ψ))) -∗
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
           ∃ i G q,
             othreadG_elem i ∗ othreadG_obls i G q ∗
             (∃ T P α β, ∀ k,
                ⌜k ∉ G⌝ -∗ othreadG_obls i ({[k]} ∪ G) q -∗
                oblG_elem k -∗ oblG_goal k T P -∗
                oblG_suspend_bound k α -∗ oblG_suspend k α -∗ glG_fuel k β -∗
                othreadG_owns i k true (1/2)%Qp -∗ otreeG_elem k -∗
                |={∅,E}=> state_interp σ Θ κs ∗ ν))
        ⊢ ghost_step E ν.
      Proof.
        rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" with "I") as "(%&%&%& #Tei& Tbs& %&%&%&%& H)".
        iMod (osat_alloc_obl _ α i  β T P with "S") as "(%k& %Nink& S& #Bgk& #Bek& Blk& Btk& #Btbk& Bok& Bpsk& Bpk)".
        assert (Nink2 : k ∉ dom Ω) by (by apply not_elem_of_dom in Nink).
        iMod (osuspend_alloc_obl _ _ Nink2 with "U") as "(U& #Fek)".
        iMod (othread_alloc_obl with "[S T Tbs Blk]") as "(S& T& %NinkG& Tbs& Tok& Blk)"; first (iFrame; eauto).
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
           ∃ i G q k T P,
             othreadG_elem i ∗ othreadG_obls i G q ∗ othreadG_owns i k true (1/2)%Qp ∗ ⌜k ∈ G⌝ ∗
             oblG_elem k ∗ oblG_goal k T P ∗ ⌜T σ⌝ ∗ (▷ P) ∗
             (othreadG_obls i (G ∖ {[k]}) q -∗ oblG_done k -∗
              |={∅,E}=> state_interp σ Θ κs ∗ ν))
        ⊢ ghost_step E ν.
      Proof.
        rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" with "I") as "(%&%&%&%&%&%& #Tei& Tbs& Toi& %Ink& #Bek& #Bgk& GT& GP& H)".
        iMod (oforest_resolve_one with "[$]") as "(%&%&%&%Prog& S& T& U& F& #Bdk& Tbs)"; first auto.
        iMod ("H" with "Tbs Bdk") as "[I H]". iModIntro. iFrame. iPureIntro. destruct Prog as [Prog1 Prog2].
        eapply rtc_l.
        - eapply obl_states_step_resolve; eauto.
        - eapply rtc_l; last reflexivity. eapply obl_states_step_suspend; eauto.
      Qed.

      Lemma ghost_step_suspend_obls_gen E ν :
        (∀ Θ σ κs,
           state_interp σ Θ κs ={E,∅}=∗
           ∃ π ℵ K,
             (oblG_elem π ∗ oblG_suspend_bound π ℵ ∗
              ([∗ map] k ↦ '(θ, ψ, α, β) ∈ K,
                 ⌜(ℵ < α)%ord ∧ (Ord.O < β)%ord⌝ ∗ othreadG_elem θ ∗ othreadG_owns θ k true (1/2)%Qp ∗
                 oblG_elem k ∗ otreeG_elem k ∗ oblG_suspend k α ∗ oblG_suspend k β)) ∗
             (((oblG_done π ∗
                [∗ map] k ↦ '(θ, ψ, α, β) ∈ K, othreadG_owns θ k true (1/2)%Qp ∗ oblG_suspend k α ∗ oblG_suspend k β) ∨
                 ([∗ map] k ↦ '(θ, ψ, α, β) ∈ K, ∃ x, otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2)%Qp)) -∗
              |={∅,E}=> state_interp σ Θ κs ∗ ν))
        ⊢ ghost_step E ν.
      Proof.
        rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" with "I") as "(%&%&%& (#Beπ& #Btbπ& M)& H)".
        iPoseProof (osat_elem_cases _ π with "[S]") as "[%Live | #Bdπ]"; first (iFrame; eauto); cycle 1.
        { iMod ("H" with "[M]") as "[I H]".
          - iLeft. iSplitR; first eauto. iApply (big_sepM_impl with "M"). iIntros "!>" (???) "H".
            destruct x as [[[? ?] ?] ?]. iDestruct "H" as "(%& H1& H2& H3& H4& H5)". iFrame.
          - iModIntro. iExists Ω. iFrame. done. }
        iAssert (([∗ map] k↦'(θ, ψ, _, _) ∈ K, ∃ x : positive, otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1 / 2)) ={∅,E}=∗
                 state_interp σ Θ κs ∗ ν)%I with "[H]" as "H".
        { iIntros "A". iApply "H". by iRight. }
        iStopProof. revert Ω Live. induction K using map_ind; iIntros (Ω Live) "((#Beπ& #Btbπ)& S& T& U& F& M& K)".
        { iMod ("K" with "[]") as "[I K]".
          - done.
          - iModIntro. iExists Ω. iFrame. done. }
        rewrite !big_sepM_insert; auto. destruct x as [[[θ ψ] α] β].
        iDestruct "M" as "[(%LT& #Teθ& Toi& #Bii& #Tei& Bti1& Bti2) M]". destruct LT as [LT1 LT2].
        destruct Live as [d Live].
        iDestruct (oforest_suspend_one_tree _ _ i θ π ψ ℵ α β with "[$]")
          as "[(S& T& U& F& Toi& Bti1& Bti2& #Bdπ) | >(%&%&%Prog1& S& T& U& F& Susi)]".
        1,2: simpl; auto.
        { iPoseProof (osat_obl_is_done_weak _ π with "[S]") as "%"; first (iFrame; eauto).
          destruct H0. by rewrite Live in H0. }
        destruct Prog1 as [Prog1 DecC]. iMod (IHK Ω' with "[-]") as "H".
        { specialize (Prog1 π). rewrite Live in Prog1. inv Prog1. destruct H2. destruct (DecC π (obl_live d)).
          - apply H0 in H3 . destruct y; try done. rewrite -H1. eauto.
          - apply H2 in H3. rewrite -H1 -H3. eauto. }
        2:{ iDestruct "H" as "(%& %Prog2& H)". iModIntro. iFrame. iPureIntro. etrans; last eauto.
            eapply rtc_l; last reflexivity. eapply obl_states_step_suspend; eauto. }
        clear IHK. iSplitR; first eauto. iFrame. iIntros "M". iApply "K". iFrame.
      Qed.

      Lemma ghost_step_progress_obls_gen E ν :
        (∀ Θ σ κs,
           state_interp σ Θ κs ={E,∅}=∗
           ∃ K,
             (([∗ map] k ↦ '(θ, ψ) ∈ K,
                 othreadG_elem θ ∗ othreadG_owns θ k true (1/2)%Qp ∗
                 ∃ a, ⌜(Ord.O < a)%ord⌝ ∗ oblG_elem k ∗ oblG_suspend k a) ∗
              (([∗ map] k ↦ '(θ, ψ) ∈ K, othreadG_owns θ k true (1/2)%Qp ∗ glG_fuel k ψ) -∗
               |={∅,E}=> state_interp σ Θ κs ∗ ν)))
        ⊢ ghost_step E ν.
      Proof.
        rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" with "I") as "(%& M& H)".
        iStopProof. revert Ω. induction K using map_ind; iIntros (Ω) "(S& T& U& F& M& K)".
        { iMod ("K" with "[]") as "[I K]".
          - done.
          - iModIntro. iExists Ω. iFrame. done. }
        rewrite !big_sepM_insert; auto. destruct x as [θ ψ].
        iDestruct "M" as "((#Teθ& Toi& %& %LTa& #Bei& Bti)& M)".
        iMod (oforest_get_progress_one _ _ θ i a ψ with "[S T F Toi Bti]") as "(%&%&%& S& T& F& Toi& Bpi)".
        { simpl; auto. }
        { iFrame. auto. }
        destruct H0 as [Prog1 DecC]. iMod (IHK Ω' with "[-]") as "H".
        2:{ iDestruct "H" as "(%& %Prog2& H)". iModIntro. iFrame. iPureIntro. etrans; last eauto.
            eapply rtc_l; last reflexivity. eapply obl_states_step_suspend; eauto. }
        clear IHK. assert (dom Ω' = dom Ω).
        { apply obl_states_cond_rel_dom in Prog1. auto. }
        rewrite -!H0. iFrame. iIntros "M". iApply "K". iFrame.
      Qed.

      Lemma ghost_step_terminate E ν :
        (∀ Θ σ κs,
           state_interp σ Θ κs ={E,∅}=∗
           ∃ i,
             othreadG_obls i ∅ 1 ∗ othreadG_exec i (1/2) ∗
             (othreadG_term i -∗
              |={∅,E}=> state_interp σ Θ κs ∗ ν))
        ⊢ ghost_step E ν.
      Proof.
        rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" with "I") as "(%& Tbs& Tei& H)".
        iMod (othread_exec_to_term with "[T Tei Tbs]") as "(T& #Tti)"; first iFrame.
        iMod ("H" with "Tti") as "[I H]". iModIntro. iFrame. done.
      Qed.

      Lemma ghost_step_done_acc E ν :
        (∀ Θ σ κs,
           state_interp σ Θ κs ={E,∅}=∗
           ∃ k T P,
             oblG_goal k T P ∗ oblG_done k ∗
             ((▷ P) ={∅,E}=∗ (▷ P) ∗ state_interp σ Θ κs ∗ ν))
        ⊢ ghost_step E ν.
      Proof.
        rewrite /ghost_step. iIntros "H % % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" with "I") as "(%&%&%& #Bg& #Bd& H)".
        iPoseProof (osat_done_open _ k T P with "[$S $Bg $Bd]") as "[HP S]".
        iMod ("H" with "HP") as "(HP& $& $)".
        iFrame. iModIntro. iSplitR; first done. by iApply "S".
      Qed.

      Lemma ghost_step_done_pers E ν k T P :
        Persistent P →
        oblG_goal k T P -∗ oblG_done k -∗ ((▷ P) -∗ ν) -∗ ghost_step E ν.
      Proof.
        iIntros (?) "#Bg #Bd H". iApply ghost_step_done_acc.
        iIntros (???) "I".
        iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
        iFrame "Bg Bd". iIntros "#HP". iMod "Hclose" as "_". iFrame.
        iModIntro. iFrame "HP". by iApply "H".
      Qed.

  End lwp_step.

  Section lwp.

    (* lwp versions with interface definitions *)
    Lemma lwp_lift_step_fupd s ς i E e1 Φ :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
         (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                      ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                      |={∅,E}=>
         state_interp σ2 (Θ ∪ dom efs) κs ∗
         lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
      ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". rewrite lwp_unfold /lwp_pre. iIntros "Hc". destruct (to_val e1) eqn:He.
      { rewrite /ghost_step. iIntros "% % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" $! _ _ [] with "I") as "((%&%)& _)". done. }
      iApply lwp_step_progress_no_lc.
      iIntros (????) "I". iMod ("H" with "I") as "(%& H)". destruct H as [_ H].
      iModIntro. iSplitR; first done.
      iIntros (????) "Efs". iMod ("H" with "[//] [Efs]") as "(I& H& Efs)".
      - iApply (big_sepS_impl with "Efs"). iIntros "!>" (??) "(?&?&?)". iFrame. done.
      - iFrame. iApply (lwp_cond_elim with "H Hc").
    Qed.

    Lemma lwp_lift_step_fupd_lc s ς i E e1 Φ :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
         (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∃ G q,
           (th_obls i G 1 ∗ [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
           ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                        th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
                        ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                        ALC (|={∅,E}=>
                               state_interp σ2 (Θ ∪ dom efs) κs ∗
                               lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
      ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". rewrite lwp_unfold /lwp_pre. iIntros "Hc". destruct (to_val e1) eqn:He.
      { rewrite /ghost_step. iIntros "% % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" $! _ _ [] with "I") as "((%&%)& _)". done. }
      iApply lwp_step_progress_get_lc_with_obls.
      iIntros (????) "I". iMod ("H" with "I") as "(%HS& (%&%& ((Tbs& Te& #Tei& #Es)& Ds)& H))".
      destruct HS as [_ HS]. iModIntro. iSplitR; first done.
      iExists G, q. iFrame "Tbs". iSplitL "Ds".
      { iFrame "Tei". iApply (big_sepS_impl with "Ds"). iIntros "!>" (??) "((To& [Be Fe]& Te)& P& _)". iFrame. }
      iIntros (????) "A B Efs".
      iMod ("H" with "[//] [A Te] [B] [Efs]") as ">(I& H& Efs)"; iFrame; auto.
      - iCombine "Es B" as "B". iPoseProof (big_sepS_sep with "B") as "B".
        iApply (big_sepS_impl with "B"). iIntros "!>" (??) "(#Esx& To)". iFrame. auto.
      - iApply (big_sepS_impl with "Efs"). iIntros "!>" (??) "(?&?&?)". iFrame. done.
      - iApply (lwp_cond_elim with "H Hc").
    Qed.

    Lemma lwp_lift_step_fupd_suspended s ς i E e1 Φ :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
         (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∃ π G K,
           (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
            ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
            ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
           ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                        th_obls i G 1 -∗
                        ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                          ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                           (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
                        ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                        ALC (|={∅,E}=>
                               state_interp σ2 (Θ ∪ dom efs) κs ∗
                               lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
      ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". rewrite lwp_unfold /lwp_pre. iIntros "Hc". destruct (to_val e1) eqn:He.
      { rewrite /ghost_step. iIntros "% % % % I". iDestruct "I" as "(S& T& U& F& I)".
        iMod ("H" $! _ _ [] with "I") as "((%&%)& _)". done. }
      iApply lwp_step_progress_get_lc_suspended_obls.
      iIntros (????) "I". iMod ("H" with "I") as "(%HS& (%& %& %& (%& (Tbs& Txi& #Tei& #Es)& (#Bep& #Fep)& Ps& Ws)& H))".
      destruct HS as [_ HS]. iModIntro. iSplitR; first done.
      iExists π, G, K. iFrame "Tbs".
      iAssert ([∗ map] k↦'(x, ψ) ∈ K, otreeG_suspend k x i π ψ ∗ (oblG_elem k ∗ otreeG_elem k) ∗ (oblG_elem π ∗ otreeG_elem π) ∗ othreadG_elem i)%I with "[Ws]" as "#HK".
      { iApply (big_sepM_impl with "Ws"). iIntros (???) "!>". destruct x. iIntros "(W&S&A&B&C)". iFrame. }
      iSplitR "Hc Txi H".
      { iFrame "Tei Bep Fep". iSplit; first done. iSplitL "Ps".
        - iApply (big_sepS_impl with "Ps"). iIntros "!>" (??) "(P& Ex& _)". iFrame.
        - iApply (big_sepM_impl with "Ws"). iIntros "!>" (???). destruct x. iIntros "(W& S& (E1& E2)& _)". iFrame. }
      iIntros (????) "A B Efs".
      iMod ("H" with "[//] [A Txi] [B] [Efs]") as ">(I& H& Efs)"; iFrame; auto.
      - iDestruct "B" as "[[A B] | [A B]]".
        + iLeft. iSplitL "A".
          * iCombine "Es A" as "A". iPoseProof (big_sepS_sep with "A") as "A".
            iApply (big_sepS_impl with "A"). iIntros "!>" (??) "(#Esx& P)". iFrame. auto.
          * iCombine "HK B" as "A". iPoseProof (big_sepM_sep with "A") as "A".
            iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x. iIntros "(A& B)". iFrame.
        + iRight. iFrame "A Bep Fep". 
          iCombine "HK B" as "A". iPoseProof (big_sepM_sep with "A") as "A".
          iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x. iIntros "((S&E1&E2&E3)& (O&P))". iFrame.
          iPoseProof (big_sepS_elem_of_acc _ G k with "Es") as "[$ _]". subst. by apply elem_of_dom.
      - iApply (big_sepS_impl with "Efs"). iIntros "!>" (??) "(?&?&?)". iFrame. done.
      - iApply (lwp_cond_elim with "H Hc").
    Qed.

    Inductive get_lc := NoLc | GetLc | GetLcSus.

    Lemma lwp_lift_step_fupd_gen (glc : get_lc) s ς i E e1 Φ :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
         (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         match glc with
         | NoLc =>
             (∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                           ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                           |={∅,E}=>
                state_interp σ2 (Θ ∪ dom efs) κs ∗
                lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
         | GetLc =>
             (∃ G q,
                 (th_obls i G 1 ∗ [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
                 ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                              th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
                              ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                              ALC (|={∅,E}=>
                                     state_interp σ2 (Θ ∪ dom efs) κs ∗
                                     lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
         | GetLcSus =>
             (∃ π G K,
                 (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
                  ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                  ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
                 ∀ e2 σ2 efs, (⌜ prim_step i e1 σ1 Θ κ e2 σ2 efs ⌝) -∗
                              th_obls i G 1 -∗
                              ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                                ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                                 (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
                              ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                              ALC (|={∅,E}=>
                                     state_interp σ2 (Θ ∪ dom efs) κs ∗
                                     lWP e2 @ s; ς; i; E {{ Φ }} ∗ [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
         end)
      ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
    Proof.
      destruct glc.
      - apply lwp_lift_step_fupd.
      - apply lwp_lift_step_fupd_lc.
      - apply lwp_lift_step_fupd_suspended.
    Qed.

    Lemma lwp_wait_obls s ς i E e Φ :
      (∀ Θ σ κs,
         state_interp σ Θ κs ={E,∅}=∗
         ∃ j G π K,
           (⌜G = dom K⌝ ∗ th_obls j G 1 ∗ obl π ∗
            ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x j π ψ (1/2))) ∗
           (th_obls j G 1 -∗
            (([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x j π ψ (1/2)) ∨
               (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns j k (1/2) ∗ gl_fuel k ψ))) -∗
            |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
      ⊢ lWP e @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". iApply ghost_step_elim. iApply ghost_step_wait_obls.
      iIntros (???) "I". iMod ("H" with "I") as "(%&%&%&%& (%& (Tbs& Txi& #Tei& #Es)& (#Bep& #Fep)& Ws)& H)".
      iModIntro. iExists j, G, π, K. iFrame "Tbs".
      iAssert ([∗ map] k↦'(x, ψ) ∈ K, otreeG_suspend k x j π ψ ∗ (oblG_elem k ∗ otreeG_elem k) ∗ (oblG_elem π ∗ otreeG_elem π) ∗ othreadG_elem j)%I with "[Ws]" as "#HK".
      { iApply (big_sepM_impl with "Ws"). iIntros (???) "!>". destruct x. iIntros "(W&S&A&B&C)". iFrame. }
      iSplitR "Txi H".
      { iFrame "Tei Bep Fep". iSplit; first done.
        iApply (big_sepM_impl with "Ws"). iIntros "!>" (???). destruct x. iIntros "(W& S& (E1& E2)& _)". iFrame. }
      iIntros "A B".
      iMod ("H" with "[A Txi] [B]") as "(I& H)"; iFrame; auto.
      iDestruct "B" as "[A | [A B]]".
      - iLeft. iCombine "HK A" as "A". iPoseProof (big_sepM_sep with "A") as "A".
        iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x. iIntros "(A& B)". iFrame.
      - iRight. iFrame "A Bep Fep".
        iCombine "HK B" as "A". iPoseProof (big_sepM_sep with "A") as "A".
        iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x. iIntros "((S&E1&E2&E3)& (O&P))". iFrame.
        iPoseProof (big_sepS_elem_of_acc _ G k with "Es") as "[$ _]". subst. by apply elem_of_dom.
    Qed.

    Lemma lwp_alloc_obl s ς i E e Φ :
      (∀ Θ σ κs,
         state_interp σ Θ κs ={E,∅}=∗
         ∃ j G q,
           th_obls j G q ∗
           (∃ T P α β, ∀ k,
              ⌜k ∉ G⌝ -∗ th_obls j ({[k]} ∪ G) q -∗
              oGoal k T P -∗
              obl_bound k α -∗ obl_sc k α -∗ gl_fuel k β -∗
              othread_owns j k (1/2)%Qp -∗
              |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
      ⊢ lWP e @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". iApply ghost_step_elim. iApply ghost_step_alloc_obl.
      iIntros (???) "I". iMod ("H" with "I") as "(%&%&%& (Tbs& Txi& #Tei& #Es)& %&%&%&%& H)".
      iModIntro. iExists j, G, q. iFrame "Tbs Tei". iExists T, P, α, β.
      iIntros (k) "% Tbs #Bek #Bgk #Btbk Btk Bpk Tok #Fek".
      iApply ("H" $! k with "[//] [Tbs Txi] [] [] [Btk] [Bpk] [Tok]"); auto.
      iFrame. iFrame "Tei". iApply big_sepS_union. 1: set_solver.
      rewrite big_sepS_singleton. auto.
    Qed.

    Lemma lwp_resolve_obl s ς i E e Φ :
      (∀ Θ σ κs,
         state_interp σ Θ κs ={E,∅}=∗
         ∃ j G q k T P,
           th_obls j G q ∗ othread_owns j k (1/2)%Qp ∗ ⌜k ∈ G⌝ ∗
           oGoal k T P ∗ ⌜T σ⌝ ∗ (▷ P) ∗
           (th_obls j (G ∖ {[k]}) q -∗ oDone k -∗
            |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
      ⊢ lWP e @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". iApply ghost_step_elim. iApply ghost_step_resolve_obl.
      iIntros (???) "I".
      iMod ("H" with "I") as "(%&%&%&%&%&%& (Tbs& Txi& #Tei& #Es)& (Tok& [#Bek #Fek]& #Tej)& %& (#Bgk& _)& %HT& P& H)".
      iModIntro. iExists j, G, q, k, T, P. iFrame. iFrame "Tei Bek Bgk". iSplitR; first auto. iSplitR; first auto.
      iIntros "Tbs #Bdk".
      iApply ("H" with "[Tbs Txi] []"); auto.
      iFrame. iFrame "Tei". iPoseProof (big_sepS_delete _ _ k with "Es") as "[_ Es2]"; auto.
    Qed.

    Lemma lwp_suspend_obls_gen s ς i E e Φ :
      (∀ Θ σ κs,
         state_interp σ Θ κs ={E,∅}=∗
         ∃ π ℵ K,
           (obl_bound π ℵ ∗
            ([∗ map] k ↦ '(θ, ψ, α, β) ∈ K,
               ⌜(ℵ < α)%ord ∧ (Ord.O < β)%ord⌝ ∗ othread_owns θ k (1/2)%Qp ∗ obl_sc k α ∗ obl_sc k β)) ∗
           (((oDone π ∗
              [∗ map] k ↦ '(θ, ψ, α, β) ∈ K, othread_owns θ k (1/2)%Qp ∗ obl_sc k α ∗ obl_sc k β) ∨
               ([∗ map] k ↦ '(θ, ψ, α, β) ∈ K, ∃ x, obl_wait k x θ π ψ (1/2))) -∗
            |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
      ⊢ lWP e @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". iApply ghost_step_elim. iApply ghost_step_suspend_obls_gen.
      iIntros (???) "I".
      iMod ("H" with "I") as "(%&%&%& ((#Btbp& #Bep& #Fep)& M)& H)".
      iModIntro. iExists π, ℵ, K. iFrame "Bep Btbp".
      iAssert ([∗ map] k↦'(θ, _, α, β) ∈ K, ⌜(ℵ < α)%ord ∧ (Ord.O < β)%ord⌝ ∗ oblG_elem k ∗ otreeG_elem k ∗ othreadG_elem θ)%I with "[M]" as "#MM".
      { iApply (big_sepM_impl with "M"). iIntros (???). destruct x as [[[? ?] ?] ?].
        iIntros "!> (%& (A1& [A2 A3]& A4)& [B _]& [C _])". iFrame. done. }
      iSplitL "M".
      { iApply (big_sepM_impl with "M"). iIntros (???) "!>". destruct x as [[[? ?] ?] ?].
        iIntros "(%& (A1& [A2 A3]& A4)& [B _]& [C _])". iFrame. done. }
      iIntros "A". iApply "H". iDestruct "A" as "[ [A B] | A]".
      - iLeft. iFrame. iFrame "Bep Fep". iApply (big_sepM_impl with "B").
        iIntros "!>" (???). destruct x as [[[? ?] ?] ?]. iIntros "($&$&$)".
        iPoseProof (big_sepM_lookup_acc _ _ _ _ H with "MM") as "[A _]". iDestruct "A" as "(%& #Bek& #Fek& #Te)". auto.
      - iRight. iApply (big_sepM_impl with "A").
        iIntros "!>" (???). destruct x as [[[? ?] ?] ?]. iIntros "(%&$&$)".
        iPoseProof (big_sepM_lookup_acc _ _ _ _ H with "MM") as "[A _]". iDestruct "A" as "(%& #Bek& #Fek& #Te)". auto.
    Qed.

    Lemma lwp_progress_obls_gen s ς i E e Φ :
      (∀ Θ σ κs,
         state_interp σ Θ κs ={E,∅}=∗
         ∃ K,
           (([∗ map] k ↦ '(θ, ψ) ∈ K, othread_owns θ k (1/2)%Qp ∗ ∃ a, ⌜(Ord.O < a)%ord⌝ ∗ obl_sc k a) ∗
            (([∗ map] k ↦ '(θ, ψ) ∈ K, othread_owns θ k (1/2)%Qp ∗ gl_fuel k ψ) -∗
             |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }})))
      ⊢ lWP e @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". iApply ghost_step_elim. iApply ghost_step_progress_obls_gen.
      iIntros (???) "I".
      iMod ("H" with "I") as "(%& M& H)".
      iAssert ([∗ map] k↦'(θ, _) ∈ K, oblG_elem k ∗ otreeG_elem k ∗ othreadG_elem θ)%I with "[M]" as "#MM".
      { iApply (big_sepM_impl with "M"). iIntros (???) "!>". destruct x as [? ?].
        iIntros "((_& A& B)& _)". iFrame. }
      iModIntro. iExists K.
      iSplitL "M".
      { iApply (big_sepM_impl with "M"). iIntros (???) "!>". destruct x as [? ?].
        iIntros "((To& He& Te)& (%& %& T& Be& Fe))". iFrame. auto. }
      iIntros "A". iApply "H".
      iApply (big_sepM_impl with "A"). iIntros "!>" (???). destruct x as [? ?].
      iIntros "(O& P)". iFrame.
      iPoseProof (big_sepM_lookup_acc _ _ _ _ H with "MM") as "[A _]". iDestruct "A" as "(#Bek& #Fek& #Te)". auto.
    Qed.

    Lemma lwp_terminate s ς i E e Φ :
      (∀ Θ σ κs,
         state_interp σ Θ κs ={E,∅}=∗
         ∃ j,
           th_obls j ∅ 1 ∗
           (tTerm j -∗
            |={∅,E}=> state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
      ⊢ lWP e @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs.
      iIntros "H". iApply ghost_step_elim. iApply ghost_step_terminate.
      iIntros (???) "I". iMod ("H" with "I") as "(%& (Tbs& Tx& #Te& _)& H)".
      iModIntro. iExists j. iFrame. iIntros "A". iApply "H". auto.
    Qed.

    Lemma lwp_done_acc s ς i E e Φ :
      (∀ Θ σ κs,
         state_interp σ Θ κs ={E,∅}=∗
         ∃ k T P,
           oGoal k T P ∗ oDone k ∗
           ((▷ P) ={∅,E}=∗ (▷ P) ∗ state_interp σ Θ κs ∗ lWP e @ s; ς; i; E {{ Φ }}))
      ⊢ lWP e @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs. iIntros "H". iApply ghost_step_elim. iApply ghost_step_done_acc.
      iIntros (???) "I". iMod ("H" with "I") as "(%&%&%& (Bg& Bg0)& (Bd& Bd0)& H)".
      iModIntro. iFrame.
    Qed.

    Lemma lwp_done_pers s ς i E e Φ k T P :
      Persistent P →
      oGoal k T P -∗ oDone k -∗ ((▷ P) -∗ lWP e @ s; ς; i; E {{ Φ }}) -∗
      lWP e @ s; ς; i; E {{ Φ }}.
    Proof.
      unfold_defs. iIntros (?) "[#Bg _] [#Bd _] H". iApply ghost_step_elim.
      iApply (ghost_step_done_pers with "Bg Bd H").
    Qed.

  End lwp.

  Local Hint Resolve reducible_no_obs_reducible : core.

  Lemma lwp_lc_later_ord s ς i E e Φ :
    £ Ord.one -∗ (▷ lWP e @ s; ς; i; E {{ Φ }}) -∗ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". by iMod (lc_fupd_elim_later_ord with "LC H") as "H".
  Qed.
  Lemma lwp_lc_later s ς i E e Φ :
    £n 1 -∗ (▷ lWP e @ s; ς; i; E {{ Φ }}) -∗ lWP e @ s; ς; i; E {{ Φ }}.
  Proof. iApply lwp_lc_later_ord. Qed.
  Lemma lwp_lc_laterN n s ς i E e Φ :
    £n n -∗ (▷^n lWP e @ s; ς; i; E {{ Φ }}) -∗ lWP e @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". iApply fupd_lwp. iApply (lc_fupd_add_laterN E E with "LC"). iNext. by iModIntro.
  Qed.

  Lemma lwp_lift_stuck ς i E Φ e :
    to_val e = None →
    (∀ Ω Θ σ κs,
       (ς ∗ osat Ω ∗ othread Θ ∗ osuspend (dom Ω) ∗ oforest (dom Ω) ∗ state_interp σ Θ κs)
       ={E,∅}=∗
       ⌜ stuck i e σ Θ ⌝)
    ⊢ lWP e @ ς; i; E ?{{ Φ }}.
  Proof.
    rewrite lwp_unfold /lwp_pre /lwp_step =>->. iIntros "H Hc" (?? σ κ κs) "Hσ".
    iMod ("H" with "[Hc Hσ]") as %[? Hirr]; first iFrame.
    iModIntro. iSplit; first done.
    iExists Ω1. iSplit; first done.
    iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
  Qed.

  (** Derived lifting lemmas. *)
  Lemma lwp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s ς i E Φ e1 C :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
    (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
    (∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep HCC) "H". iApply lwp_cond_intro. iIntros "Hc".
    iApply lwp_lift_step_fupd. iIntros (Θ σ1 κ κs) "Hσ".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iPoseProof (HCC with "Hc Hσ") as "%HC".
    iSplit.
    { iPureIntro. split.
      - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
      - destruct s; auto. }
    iIntros (e2 σ2 efs ?) "Hefs".
    destruct (Hstep κ σ1 Θ e2 σ2 efs HC) as (-> & <- & ->); auto.
    replace (Θ ∪ dom ∅) with Θ by set_solver.
    iMod "Hclose" as "_". iModIntro. rewrite big_sepM_empty.
    iFrame. iSplitL; last auto. iApply (lwp_cond_elim with "[H] Hc").
    iApply "H"; eauto.
  Qed.

  Lemma lwp_lift_pure_step_no_fork_lc `{!Inhabited (state Λ)} s ς i E E' Φ e1 C :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
    (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
    (|={E,E'}=>
       ∃ G q,
       (th_obls i G 1 ∗
        [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
       (th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
        ALC (|={E',E}=> ∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep HCC) "H". iApply lwp_cond_intro. iIntros "Hc".
    iApply lwp_lift_step_fupd_lc. iIntros (Θ σ1 κ κs) "Hσ".
    iPoseProof (HCC with "Hc Hσ") as "%HC".
    iMod "H" as "(%&%& D& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. split.
      - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
      - destruct s; auto. }
    iExists _, _. iFrame "D".
    iIntros (e2 σ2 efs ?) "Tbs Bos Efs".
    destruct (Hstep κ σ1 Θ e2 σ2 efs HC) as (-> & <- & ->); auto.
    replace (Θ ∪ dom ∅) with Θ by set_solver.
    iMod ("H" with "Tbs Bos [//]") as "H".
    iMod "Hclose" as "_". iMod "H". iModIntro. rewrite big_sepM_empty. iFrame.
    iSplitL; last auto. iApply (lwp_cond_elim with "H Hc").
  Qed.

  Lemma lwp_lift_pure_step_no_fork_suspended `{!Inhabited (state Λ)} s ς i E E' Φ e1 C :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
    (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
    (|={E,E'}=>
       ∃ π G K,
       (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
        ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       (th_obls i G 1 -∗
        ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
           (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
        ALC (|={E',E}=> ∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep HCC) "H". iApply lwp_cond_intro. iIntros "Hc".
    iApply lwp_lift_step_fupd_suspended. iIntros (Θ σ1 κ κs) "Hσ".
    iMod "H" as "(%&%&%& D& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iPoseProof (HCC with "Hc Hσ") as "%HC".
    iSplit.
    { iPureIntro. split.
      - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
      - destruct s; auto. }
    iExists _, _, _. iFrame "D". iIntros (e2 σ2 efs ?) "Tbs Bos Efs".
    destruct (Hstep κ σ1 Θ e2 σ2 efs HC) as (-> & <- & ->); auto.
    replace (Θ ∪ dom ∅) with Θ by set_solver.
    iMod ("H" with "Tbs Bos [//]") as "H".
    iMod "Hclose" as "_". iMod "H". iModIntro. rewrite big_sepM_empty. iFrame.
    iSplitL; last auto. iApply (lwp_cond_elim with "H Hc").
  Qed.

  Lemma lwp_lift_pure_step_no_fork_gen (glc : get_lc) `{!Inhabited (state Λ)} s ς i E E' Φ e1 C :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
    (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
    (match glc with
     | NoLc =>
         (∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})
     | GetLc =>
         |={E,E'}=>
           (∃ G q,
               (th_obls i G 1 ∗
                [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
               (th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
                ALC (|={E',E}=> ∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})))
     | GetLcSus =>
         |={E,E'}=>
           (∃ π G K,
               (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
                ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
               (th_obls i G 1 -∗
                ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                  ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                   (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
                ALC (|={E',E}=> ∀ κ Θ e2 efs σ, ⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝ -∗ lWP e2 @ s; ς; i; E {{ Φ }})))
     end)
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    destruct glc.
    - apply lwp_lift_pure_step_no_fork.
    - apply lwp_lift_pure_step_no_fork_lc.
    - apply lwp_lift_pure_step_no_fork_suspended.
  Qed.

  Lemma lwp_lift_pure_stuck `{!Inhabited (state Λ)} ς i E Φ e :
    (∀ σ τ, stuck i e σ τ) →
    True ⊢ lWP e @ ς; i; E ?{{ Φ }}.
  Proof.
    iIntros (Hstuck) "_". iApply lwp_lift_stuck.
    - destruct(to_val e) as [v|] eqn:He; last done.
      rewrite -He. by case (Hstuck inhabitant ∅).
    - iIntros (????) "_". iApply fupd_mask_intro; auto with set_solver.
  Qed.

  Lemma lwp_lift_atomic_step_fupd {s ς i E1 E2 Φ} e1 :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
       (⌜to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
       ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                    ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                    |={E2,E1}=>
       state_interp σ2 (Θ ∪ dom efs) κs ∗
       (ς -∗ from_option Φ False (to_val e2)) ∗
       [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
    ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (lwp_lift_step_fupd s _ i E1 e1); iIntros (Θ σ1 κ κs) "Hσ1".
    iMod ("H" with "Hσ1") as "(%& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first auto. iIntros (????) "Hefs".
    iMod "Hclose" as "_". iMod ("H" with "[//] Hefs") as "H".
    iDestruct "H" as "(Hs&Hq&Hefs)". iFrame.
    iModIntro. iApply lwp_cond_intro. iIntros "Hc". iPoseProof ("Hq" with "Hc") as "Hq".
    destruct (to_val e2) eqn:?; last by iExFalso.
    iApply lwp_value; last eauto. by apply of_to_val.
  Qed.

  Lemma lwp_lift_atomic_step_fupd_lc {s ς i E1 E2 Φ} e1 :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
       (⌜to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
       ∃ G q,
         (th_obls i G 1 ∗
          [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
         ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                      th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
                      ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                      ALC (|={E2,E1}=>
                             state_interp σ2 (Θ ∪ dom efs) κs ∗
                             (ς -∗ from_option Φ False (to_val e2)) ∗
                             [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
    ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (lwp_lift_step_fupd_lc s _ i E1 e1).
    iIntros (Θ σ1 κ κs) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first auto.
    iDestruct "H" as "(%&%& D& H)". iExists _, _. iFrame "D".
    iIntros (????) "H1 H2 Hefs".
    iMod ("H" with "[//] H1 H2 Hefs") as "H".
    iMod "Hclose" as "_".
    iMod "H" as "(Hs&Hq&Hefs)". iFrame.
    iModIntro. iApply lwp_cond_intro. iIntros "Hc". iPoseProof ("Hq" with "Hc") as "Hq".
    destruct (to_val e2) eqn:?; last by iExFalso.
    iApply lwp_value; last eauto. by apply of_to_val.
  Qed.

  Lemma lwp_lift_atomic_step_fupd_suspended {s ς i E1 E2 Φ} e1 :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
       (⌜to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
       ∃ π G K,
         (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
          ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
         ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                      th_obls i G 1 -∗
                      ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                         (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
                      ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                      ALC (|={E2,E1}=>
                             state_interp σ2 (Θ ∪ dom efs) κs ∗
                             (ς -∗ from_option Φ False (to_val e2)) ∗
                             [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
    ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (lwp_lift_step_fupd_suspended s _ i E1 e1).
    iIntros (Θ σ1 κ κs) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first auto.
    iDestruct "H" as "(%&%&%& D& H)". iExists _, _, _. iFrame "D".
    iIntros (????) "H1 H2 Hefs".
    iMod ("H" with "[//] H1 H2 Hefs") as "H".
    iMod "Hclose" as "_".
    iMod "H" as "(Hs&Hq&Hefs)". iFrame.
    iModIntro. iApply lwp_cond_intro. iIntros "Hc". iPoseProof ("Hq" with "Hc") as "Hq".
    destruct (to_val e2) eqn:?; last by iExFalso.
    iApply lwp_value; last eauto. by apply of_to_val.
  Qed.

  Lemma lwp_lift_atomic_step_fupd_gen (glc : get_lc) {s ς i E1 E2 Φ} e1 :
    (∀ Θ σ1 κ κs,
       state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
       (⌜to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True⌝) ∗
       match glc with
       | NoLc =>
           (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                         ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                         |={E2,E1}=>
              state_interp σ2 (Θ ∪ dom efs) κs ∗
              (ς -∗ from_option Φ False (to_val e2)) ∗
              [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})
       | GetLc =>
           (∃ G q,
               (th_obls i G 1 ∗
                [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
               ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                            th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
                            ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                            ALC (|={E2,E1}=>
                                   state_interp σ2 (Θ ∪ dom efs) κs ∗
                                   (ς -∗ from_option Φ False (to_val e2)) ∗
                                   [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
       | GetLcSus =>
           (∃ π G K,
               (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
                ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
               ∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) -∗
                            th_obls i G 1 -∗
                            ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                              ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                               (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
                            ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
                            ALC (|={E2,E1}=>
                                   state_interp σ2 (Θ ∪ dom efs) κs ∗
                                   (ς -∗ from_option Φ False (to_val e2)) ∗
                                   [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }}))
       end)
    ⊢ lWP e1 @ s; ς; i; E1 {{ Φ }}.
  Proof.
    destruct glc.
    - apply lwp_lift_atomic_step_fupd.
    - apply lwp_lift_atomic_step_fupd_lc.
    - apply lwp_lift_atomic_step_fupd_suspended.
  Qed.

  Lemma lwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s ς i E Φ C} e1 e2 :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
    (lWP e2 @ s; ς; i; E {{ Φ }})
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet HCC) "H". iApply (lwp_lift_pure_step_no_fork s _ i E); try done.
    { naive_solver. }
    iIntros "% % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
  Qed.

  Lemma lwp_lift_pure_det_step_no_fork_lc `{!Inhabited (state Λ)} {s ς i E E' Φ C} e1 e2 :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
    (|={E,E'}=>
       ∃ G q,
       (th_obls i G 1 ∗
        [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
       (th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
        ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet HCC) "H". iApply (lwp_lift_pure_step_no_fork_lc s _ i E E'); try done.
    { naive_solver. }
    iMod "H" as "(%&%& $& H)". iModIntro.
    iIntros "H1 H2". iMod ("H" with "H1 H2") as ">H".
    iIntros "!> % % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
  Qed.

  Lemma lwp_lift_pure_det_step_no_fork_suspended `{!Inhabited (state Λ)} {s ς i E E' Φ C} e1 e2 :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
    (|={E,E'}=>
       ∃ π G K,
       (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
        ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
        ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
       (th_obls i G 1 -∗
        ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
          ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
           (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
        ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet HCC) "H". iApply (lwp_lift_pure_step_no_fork_suspended s _ i E E'); try done.
    { naive_solver. }
    iMod "H" as "(%&%&%& $& H)". iModIntro.
    iIntros "H1 H2". iMod ("H" with "H1 H2") as ">H".
    iModIntro. iIntros "% % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
  Qed.

  Lemma lwp_lift_pure_det_step_no_fork_gen (glc : get_lc) `{!Inhabited (state Λ)} {s ς i E E' Φ C} e1 e2 :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    (∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝) →
    (match glc with
     | NoLc =>
         (lWP e2 @ s; ς; i; E {{ Φ }})
     | GetLc =>
         |={E,E'}=>
           (∃ G q,
               (th_obls i G 1 ∗
                [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
               (th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
                ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
     | GetLcSus =>
         |={E,E'}=>
           (∃ π G K,
               (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
                ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
               (th_obls i G 1 -∗
                ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                  ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                   (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
                ALC (|={E',E}=> lWP e2 @ s; ς; i; E {{ Φ }})))
     end)
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    destruct glc.
    - apply lwp_lift_pure_det_step_no_fork.
    - apply lwp_lift_pure_det_step_no_fork_lc.
    - apply lwp_lift_pure_det_step_no_fork_suspended.
  Qed.

  Class PureExecCond (C : thread_id → state Λ → Prop) ς (i : thread_id) :=
    pure_exec_cond : ∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝.

  Lemma lwp_pure_step `{!Inhabited (state Λ)} s ς i E e1 e2 φ n Φ C :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς i →
    (lWP e2 @ s; ς; i; E {{ Φ }})
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ HCC) "Hlwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
    { by iApply "Hlwp". }
    iApply (lwp_lift_pure_det_step_no_fork).
    - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
    - eauto.
    - eauto.
    - by iApply "IH".
  Qed.

  Lemma lwp_pure_step_lc `{!Inhabited (state Λ)} s ς i E E' e1 e2 φ n Φ C :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς i →
    (Nat.iter n (λ P, |={E,E'}=>
                   ∃ G q,
                   (th_obls i G 1 ∗
                    [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
                   (th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
                    ALC (|={E',E}=> P)))
       (£n n -∗ (lWP e2 @ s; ς; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ HCC) "Hlwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
    { iMod tlc_zero as "Hz". by iApply "Hlwp". }
    iApply (lwp_lift_pure_det_step_no_fork_lc (E':=E')).
    - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
    - eauto.
    - eauto.
    - iDestruct "Hlwp" as ">(%&%& $& H)".
      iModIntro. iIntros "H1 H2". iDestruct ("H" with "H1 H2") as "H".
      iDestruct "H" as "(%& H)". iExists (Ord.S x). iIntros "LC".
      iPoseProof (tlc_succ with "LC") as "[LC LC2]".
      iMod ("H" with "LC2") as "H". iModIntro. iMod "H".
      iApply "IH". iModIntro.
      iRevert "H". iApply (bi.iter_modal_mono with "[-]").
      + iIntros (??) "PQ >H". iDestruct "H" as "(%&%& $& H)".
        iIntros "!> H1 H2". iMod ("H" with "H1 H2") as ">H". by iApply "PQ".
      + iIntros "H1 H2". iApply "H1". iApply tlc_succ_nat. iFrame.
  Qed.

  Lemma lwp_pure_step_suspended `{!Inhabited (state Λ)} s ς i E E' e1 e2 φ n Φ C :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς i →
    (Nat.iter n (λ P, |={E,E'}=>
                   ∃ π G K,
                   (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
                    ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                    ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
                   (th_obls i G 1 -∗
                    ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                      ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                       (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
                    ALC (|={E',E}=> P)))
       (£n n -∗ (lWP e2 @ s; ς; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ HCC) "Hlwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
    { iMod tlc_zero as "Hz". by iApply "Hlwp". }
    iApply (lwp_lift_pure_det_step_no_fork_suspended (E':=E')).
    - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
    - eauto.
    - eauto.
    - iDestruct "Hlwp" as ">(%&%&%& $& H)".
      iModIntro. iIntros "H1 H2". iPoseProof ("H" with "H1 H2") as "H".
      iDestruct "H" as "(%& H)". iExists (Ord.S x). iIntros "LC".
      iPoseProof (tlc_succ with "LC") as "[LC LC2]".
      iMod ("H" with "LC2") as "H". iModIntro. iMod "H".
      iApply "IH". iModIntro.
      iRevert "H". iApply (bi.iter_modal_mono with "[-]").
      + iIntros (??) "PQ >H". iDestruct "H" as "(%&%&%& $& H)".
        iIntros "!> H1 H2". iMod ("H" with "H1 H2") as ">H". by iApply "PQ".
      + iIntros "H1 H2". iApply "H1". iApply tlc_succ_nat. iFrame.
  Qed.

  Lemma lwp_pure_step_gen (glc : get_lc) `{!Inhabited (state Λ)} s ς i E E' e1 e2 φ n Φ C :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς i →
    (match glc with
     | NoLc =>
         (lWP e2 @ s; ς; i; E {{ Φ }})
     | GetLc =>
         (Nat.iter n (λ P, |={E,E'}=>
                        ∃ G q,
                        (th_obls i G 1 ∗
                         [∗ set] ρ ∈ G, othread_owns i ρ q ∗ gl_fuel ρ Ord.one) ∗
                        (th_obls i G 1 -∗ ([∗ set] ρ ∈ G, othread_owns i ρ q) -∗
                         ALC (|={E',E}=> P)))
            (£n n -∗ (lWP e2 @ s; ς; i; E {{ Φ }})))
     | GetLcSus =>
         (Nat.iter n (λ P, |={E,E'}=>
                        ∃ π G K,
                        (⌜G = dom K⌝ ∗ th_obls i G 1 ∗ obl π ∗
                         ([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                         ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∗
                        (th_obls i G 1 -∗
                         ((([∗ set] ρ ∈ G, gl_fuel ρ Ord.one) ∗
                           ([∗ map] k ↦ '(x, ψ) ∈ K, obl_wait k x i π ψ (1/2))) ∨
                            (oDone π ∗ ([∗ map] k ↦ '(x, ψ) ∈ K, othread_owns i k (1/2) ∗ gl_fuel k ψ))) -∗
                         ALC (|={E',E}=> P)))
            (£n n -∗ (lWP e2 @ s; ς; i; E {{ Φ }})))
     end)
    ⊢ lWP e1 @ s; ς; i; E {{ Φ }}.
  Proof.
    destruct glc.
    - apply lwp_pure_step.
    - apply lwp_pure_step_lc.
    - apply lwp_pure_step_suspended.
  Qed.

End lifting.
