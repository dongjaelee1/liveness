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

    Lemma gl_terminate i :
      th_obls i ∅ 1 -∗ |={∅}=>g th_term i.
    Proof.
      iIntros "Tb %%% $". iMod (gl_terminate_0 with "Tb") as "#Tt". auto.
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
              th_obls i G 1 -∗
              ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
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
      { iIntros (k v LUR). iPoseProof (big_sepM_delete _ _ _ _ LUR with "REs") as "[(#Ge& #Gvl& #His) _]".
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
                 ((glG_elem r ∗ glG_version_lb r v ∗ ([∗ set] u ∈ set_seq 0 v, glG_version_lb r u ∗ glG_unlocked r u)) ∗ witG_credit (GL:=ord_ghost_lock_class) r v Ord.one) ∨
                   ((glG_elem r ∗ glG_version_lb r v ∗ ([∗ set] u ∈ set_seq 0 v, glG_version_lb r u ∗ glG_unlocked r u)) ∗ glG_unlocked r v))%I
        with "[Rs]" as "Rs".
      { iPoseProof (big_sepM_sep with "[$Rs $REs]") as "H". iApply (big_sepM_impl with "H").
        iIntros "!> %%% ([Wc | #Gu]& #Ge& #Gvl& #His)".
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

  End lwp_step.

  Section lwp.

    Lemma lwp_lift_step s i E e1 Φ :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E,∅}=∗
         (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗
         ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
           (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
              th_obls i G 1 -∗
              ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
              ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
              ALC (|={∅,E}=> state_interp σ2 (Θ ∪ dom efs) κs ∗
                            lWP e2 @ s; i; E {{ Φ }} ∗
                            [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})))
      ⊢ lWP e1 @ s; i; E {{ Φ }}.
    Proof.
      iIntros "H". rewrite lwp_unfold /lwp_pre. destruct (to_val e1) eqn:He.
      { iIntros "%%% I". iMod ("H" $! _ _ [] with "I") as "((%&%)& _)". done. }
      iApply lwp_step_step.
      iIntros (????) "I". iMod ("H" with "I") as "(%& H)". destruct H as [_ H].
      iModIntro. iSplitR; first done. auto.
    Qed.

  End lwp.

  Local Hint Resolve reducible_no_obs_reducible : core.

  Lemma lwp_lc_later_ord s i E e Φ :
    £ Ord.one -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". by iMod (lc_fupd_elim_later_ord with "LC H") as "H".
  Qed.
  Lemma lwp_lc_later s i E e Φ :
    £n 1 -∗ (▷ lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof. iApply lwp_lc_later_ord. Qed.
  Lemma lwp_lc_laterN n s i E e Φ :
    £n n -∗ (▷^n lWP e @ s; i; E {{ Φ }}) -∗ lWP e @ s; i; E {{ Φ }}.
  Proof.
    iIntros "LC H". iApply fupd_lwp. iApply (lc_fupd_add_laterN E E with "LC"). iNext. by iModIntro.
  Qed.

  Lemma lwp_lift_stuck i E Φ e :
    to_val e = None →
    (∀ Θ σ κs, state_interp σ Θ κs ={E,∅}=∗ |=[Θ]=>g ⌜ stuck i e σ Θ ⌝)
    ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    rewrite lwp_unfold /lwp_pre /lwp_step =>->. iIntros "H" (Θ σ κ κs) "Hσ".
    iMod ("H" with "Hσ") as "H". iModIntro. iMod "H" as %[? Hirr].
    iModIntro. iSplit; first done.
    iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
  Qed.

  (** Derived lifting lemmas. *)
  Class PureExecCond (C : thread_id → state Λ → Prop) ς (i : thread_id) :=
    pure_exec_cond : ∀ σ Θ κ, ς -∗ state_interp σ Θ κ -∗ ⌜C i σ⌝.

  Lemma lwp_lift_pure_step_no_fork s i E E' e1 Φ ς C :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ κ σ1 Θ e2 σ2 efs, C i σ1 → prim_step i e1 σ1 Θ κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = ∅) →
    PureExecCond C ς i →
    (|={E,E'}=>
       ς ∗
       ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗
       ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
         (ς -∗
          th_obls i G 1 -∗
          ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
          ALC (|={E',E}=>
                 ∀ σ Θ κ e2 efs, (⌜C i σ ∧ prim_step i e1 σ Θ κ e2 σ efs⌝) -∗
                                 lWP e2 @ s; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep HCC) "H".
    iApply lwp_lift_step. iIntros (Θ σ1 κ κs) "Hσ".
    iMod "H" as "[Hc (%& Tb& Gfs& %& #Rs& H)]". iPoseProof (HCC with "Hc Hσ") as "%HC".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. split.
      - specialize (Hsafe σ1 ∅ HC). destruct s; eauto using reducible_not_val.
      - destruct s; auto. }
    iExists _. iFrame "Tb Gfs". iExists _. iFrame "Rs".
    iIntros (e2 σ2 efs ?) "!> Tb Wcs Efs".
    destruct (Hstep κ σ1 Θ e2 σ2 efs HC) as (-> & <- & ->); auto.
    replace (Θ ∪ dom ∅) with Θ by set_solver.
    iMod ("H" with "Hc Tb Wcs [//]") as "H".
    iMod "Hclose" as "_". iMod "H". iModIntro. rewrite big_sepM_empty. iFrame.
  Qed.

  Lemma lwp_lift_pure_stuck `{!Inhabited (state Λ)} i E Φ e :
    (∀ σ τ, stuck i e σ τ) →
    True ⊢ lWP e @ i; E ?{{ Φ }}.
  Proof.
    iIntros (Hstuck) "_". iApply lwp_lift_stuck.
    - destruct(to_val e) as [v|] eqn:He; last done.
      rewrite -He. by case (Hstuck inhabitant ∅).
    - iIntros (???) "_". iApply fupd_mask_intro; auto with set_solver.
  Qed.

  Lemma lwp_lift_atomic_step {s i E1 E2 Φ} e1 :
      (∀ Θ σ1 κ κs,
         state_interp σ1 Θ (κ ++ κs) ={E1,E2}=∗
         (⌜ to_val e1 = None ∧ if s is NotStuck then reducible i e1 σ1 Θ else True ⌝) ∗
         ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗
         ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
           (∀ e2 σ2 efs, (⌜prim_step i e1 σ1 Θ κ e2 σ2 efs⌝) ={∅}=∗
              th_obls i G 1 -∗
              ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
              ([∗ set] j ∈ dom efs, th_obls j ∅ 1) -∗
              ALC (|={E2,E1}=> state_interp σ2 (Θ ∪ dom efs) κs ∗
                            (from_option Φ False (to_val e2)) ∗
                            [∗ map] j ↦ ef ∈ efs, lWP ef @ s; j; ⊤ {{ lift_term j fork_post }})))
      ⊢ lWP e1 @ s; i; E1 {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (lwp_lift_step s i E1 e1).
    iIntros (Θ σ1 κ κs) "Hσ1". iMod ("H" with "Hσ1") as "(%& H)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first auto.
    iDestruct "H" as "(%& Tb& Gfs& %& #Rs& H)".
    iExists _. iFrame "Tb Gfs". iExists _. iFrame "Rs".
    iIntros (????). iMod ("H" with "[//]") as "H".
    iIntros "!> Tb Wcs Efs". iMod ("H" with "Tb Wcs Efs") as "H".
    iMod "Hclose" as "_". iMod "H" as "($&Hq&$)".
    iModIntro. destruct (to_val e2) eqn:?; last by iExFalso.
    iApply lwp_value; last eauto. by apply of_to_val.
  Qed.

  Lemma lwp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s ς i E E' Φ C} e1 e2 :
    (∀ σ1 Θ, C i σ1 → if s is NotStuck then reducible i e1 σ1 Θ else to_val e1 = None) →
    (∀ σ1 κ Θ e2' σ2 efs', C i σ1 → prim_step i e1 σ1 Θ κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = ∅) →
    PureExecCond C ς i →
    (|={E,E'}=>
       ς ∗
       ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗
       ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
         (ς -∗
          th_obls i G 1 -∗
          ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
          ALC (|={E',E}=> lWP e2 @ s; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet HCC) "H". iApply (lwp_lift_pure_step_no_fork s i E E'); eauto.
    { naive_solver. }
    iMod "H" as "($& %& $& $& %& $& H)". iModIntro.
    iIntros "Hc Tb Wcs". iMod ("H" with "Hc Tb Wcs") as ">H".
    iIntros "!> % % % % %". iIntros ([? ?]). edestruct Hpuredet as (?&?&?&?); eauto. by subst.
  Qed.

  Lemma lwp_pure_step `{!Inhabited (state Λ)} s ς i E E' e1 e2 φ n Φ C :
    PureExec φ C n e1 e2 →
    φ →
    PureExecCond C ς i →
    (Nat.iter n (λ P, |={E,E'}=>
                   ς ∗
                   ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, gl_fuel g Ord.one) ∗
                   ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
                   (ς -∗
                    th_obls i G 1 -∗
                    ([∗ map] r ↦ v ∈ R, wit_credit r v Ord.one ∨ gl_done r v) -∗
                    ALC (|={E',E}=> P)))
       (£n n -∗ (lWP e2 @ s; i; E {{ Φ }})))
    ⊢ lWP e1 @ s; i; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ HCC) "Hlwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?] ? IH]; simpl.
    { iMod tlc_zero as "Hz". by iApply "Hlwp". }
    iApply (lwp_lift_pure_det_step_no_fork (E':=E')).
    - intros σ Θ HC. specialize (Hsafe i σ Θ HC). destruct s; eauto using reducible_not_val.
    - eauto.
    - iDestruct "Hlwp" as ">($& %& $& $& %& $& H)".
      iModIntro. iIntros "Hc Gb Wcs". iDestruct ("H" with "Hc Gb Wcs") as "H".
      iDestruct "H" as "(%& H)". iExists (Ord.S x). iIntros "LC".
      iPoseProof (tlc_succ with "LC") as "[LC LC2]".
      iMod ("H" with "LC2") as "H". iModIntro. iMod "H".
      iApply "IH". iModIntro.
      iRevert "H". iApply (bi.iter_modal_mono with "[-]").
      + iIntros (??) "PQ >H". iDestruct "H" as "($& %& $& $& %& $& H)".
        iIntros "!> Hc Tb Wcs". iMod ("H" with "Hc Tb Wcs") as ">H". by iApply "PQ".
      + iIntros "H1 H2". iApply "H1". iApply tlc_succ_nat. iFrame.
  Qed.

End lifting.
