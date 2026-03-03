From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From liris.base_logic Require Export opreds.
Import uPred.

(* Ensure progress of thread i's obligations and every live witnesses. *)
Definition mprog `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class} n Θ i : iPropO Σ -d> iPropO Σ :=
  (λ P,
     ∀ h a Ω1 W1,
     (model_interp h a Ω1 W1 n Θ) ={∅}=∗
     ∃ Ω2, (⌜(Ω1 ↪ₚ Ω2 | obl_cond_owner i)⌝) ∗
     ∀ W2, (⌜(W1 ↓ₚ W2 | wit_cond_assigned) ∧ owit_inv Ω2 W2 ⌝) ={∅}=∗
           (model_interp (h ++ [(n, Ω2)]) (S a) Ω2 W2 n Θ) ∗ P)%I.

Section mprog.
  Context `{SI : indexT} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Global Instance mprog_ne n Θ i : NonExpansive (mprog n Θ i).
  Proof. intros ? P1 P2 HP. rewrite /mprog. do 20 (f_equiv || done). Qed.
  Global Instance mprog_proper n Θ i : Proper ((≡) ==> (≡)) (mprog n Θ i).
  Proof. intros P P' ?. apply equiv_dist=>?. apply mprog_ne. apply equiv_dist. done. Qed.

  Lemma mprog_mono n Θ i P Q : (P ⊢ Q) → (mprog n Θ i P) ⊢ (mprog n Θ i Q).
  Proof.
    intros Hent. rewrite /mprog. iIntros "P %%%% I".
    iMod ("P" with "I") as "(%& $& P)". iModIntro.
    iIntros (??). iMod ("P" with "[//]") as "[$ P]".
    by iApply Hent.
  Qed.
  Lemma mprog_wand_l n Θ i P Q : (P -∗ Q) ∗ (mprog n Θ i P) ⊢ (mprog n Θ i Q).
  Proof.
    iIntros "[PQ P]".
    rewrite /mprog. iIntros "%%%% I".
    iMod ("P" with "I") as "(%& $& P)". iModIntro.
    iIntros (??). iMod ("P" with "[//]") as "[$ P]".
    by iApply "PQ".
  Qed.

  Global Instance mprog_ent_proper n Θ i : Proper ((⊢) ==> (⊢)) (mprog n Θ i).
  Proof. intros P Q PQ. by apply mprog_mono. Qed.
  Global Instance mprog_flip_ent_proper n Θ i : Proper (flip (⊢) ==> flip (⊢)) (mprog n Θ i).
  Proof. intros P Q PQ; by apply mprog_mono. Qed.
  Global Instance mprog_equiv_proper n Θ i : Proper ((≡) ==> (≡)) (mprog n Θ i) := ne_proper _.

  Global Instance elim_mprog (p : bool) n Θ i P Q :
    ElimModal True p false (mprog n Θ i P) P (mprog n Θ i Q) Q.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply (mprog_wand_l with "[$HPQ $HP]").
  Qed.

  Lemma fupd_mprog n Θ i P : (|={∅}=> mprog n Θ i P) ⊢ mprog n Θ i P.
  Proof.
    rewrite /mprog. iIntros "H %%%% IP". iMod ("H" with "IP") as "H". done.
  Qed.
  Global Instance elim_fupd_mprog (p : bool) n Θ i P Q :
    ElimModal True p false (|={∅}=> P) P (mprog n Θ i Q) (mprog n Θ i Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_mprog. iMod "HP".
    iModIntro. iApply ("HPQ" with "HP").
  Qed.

  (** Step rule *)
  Lemma mprog_step n Θ i P :
    (|={∅}=> ∃ G, thP_obls i G 1 ∗ ([∗ set] g ∈ G, oblP_fuel g 0 1) ∗
                 ∃ R, ([∗ set] r ∈ R, oblP_id r) ∗
                      ((thP_obls i G 1 ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_fulfilled r))
                       ={∅}=∗ P))
    ⊢ mprog n Θ i P.
  Proof.
    unfold_opreds. iIntros "H". iMod "H" as "(%& (#Oe& Ox& Ob& OS)& GFs& %& #REs& H)".
    iAssert ([∗ set] g ∈ G, oblG_elem g ∗ oblG_fuel g Ord.one)%I with "[GFs]" as "GFs".
    { iApply (big_sepS_impl with "GFs"). iIntros "!> %% H".
      rewrite (oblG_fuel_eq _ (measure (0 : layer) 1) Ord.one); auto. rewrite measure_nat Ord.from_nat_1. done. }
    iIntros "%%%% (MH& S& O& A& W& %GWI1)".
    iAssert (⌜ G ⊆ dom Ω1 ⌝)%I as "%GOSub".
    { rewrite elem_of_subseteq. iIntros (x INGx).
      iPoseProof (big_sepS_delete _ _ _ INGx with "GFs") as "[(#Bex& _) _]".
      iApply (osat_elem with "[$S $Bex]").
    }
    iAssert ([∗ map] k ↦ _ ∈ Ω1, (⌜ k ∈ G ⌝ ∗ oblG_fuel k Ord.one) ∨ (⌜ k ∉ G ⌝))%I with "[GFs]" as "GFs".
    { rewrite !big_sepM_dom. replace (dom Ω1) with (G ∪ (dom Ω1 ∖ G)).
      2:{ rewrite -union_difference_L; auto. }
      iApply (big_sepS_union). 1: set_solver.
      iSplitL.
      - iApply (big_sepS_impl with "GFs"). iIntros "!>" (??) "(_& Bfx)". iLeft. iFrame. done.
      - iApply big_sepS_intro. iIntros "!>" (??). iRight. iPureIntro. set_solver + H.
    }
    iAssert (∀ g, ⌜ g ∈ G ⌝ → ∃ o, ⌜ Ω1 !! g = Some o ∧ obl_cond_owner i g o ⌝)%I as "%LUG".
    { iIntros (g INGg). pose proof INGg.
      iPoseProof (big_sepS_delete _ _ _ INGg with "OS") as "[(#Ge& Gl& Go& Oo) _]".
      iPoseProof (othread_obls_lookup _ _ g _ _ _ INGg with "[$S $O $Oe $Ob $Ge]") as "(%& %)".
      iExists _. iPureIntro. done.
    }
    iAssert (∀ k, ⌜ k ∈ dom Ω1 ⌝ → ⌜ k ∉ G ⌝ → ∃ o, ⌜ Ω1 !! k = Some o ∧ ¬ obl_cond_owner i k o ⌝)%I as "%NotG".
    { iIntros (k INOk NINGk). apply elem_of_dom in INOk. destruct INOk.
      destruct (decide (obl_cond_owner i k x)); eauto.
      iExFalso. destruct x; try done. simpl in o. subst.
      iPoseProof (othread_assigned_obls_lookup _ _ k with "[$S $O $A $Ob]") as "%"; eauto.
    }
    iAssert ([∗ map] k ↦ o ∈ Ω1, (⌜ obl_cond_owner i k o ⌝ ∗ (∃ c, ⌜ WFOCM.ltR OCM.unit c ⌝ ∗ oblG_fuel k c)) ∨ (⌜ ¬ obl_cond_owner i k o ⌝))%I with "[GFs]" as "GFs".
    { iApply (big_sepM_impl with "GFs"). iIntros "!>" (???) "[(%& Bfk) | %]".
      - iLeft. iFrame "Bfk". iPureIntro; split.
        + apply LUG in H0. destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
        + apply Ord.S_pos.
      - iRight. iPureIntro. apply NotG in H0.
        + destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
        + apply elem_of_dom; eauto.
    }
    assert (DomOW : dom Ω1 = dom W1) by (eapply owit_inv_dom; eauto).
    iAssert (⌜ R ⊆ dom W1 ⌝)%I as "%RWSub".
    { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
      iPoseProof (big_sepS_delete _ _ _ INRx with "REs") as "[#Beg _]".
      iPoseProof (osat_elem with "[$S $Beg]") as "%". done.
    }
    iMod (osat_progress with "[$S $GFs]") as "(%Ω2& S& %ProgO)".
    { intros. destruct g; try done. eauto. }
    iMod (model_history_interp_step _ _ n n _ Ω2 with "MH") as "MH". 1: done.
    { eapply obls_cond_progress_obls_le; eauto. }
    iModIntro. iExists Ω2. iSplitR; first done. iIntros (W2 (ProgW& GWI2)).
    iMod (owit_progress with "W") as "[W Ws]". 1: eauto.
    assert (HW1 : ∃ WR WR', WR ##ₘ WR' ∧ W1 = WR ∪ WR' ∧ R = dom WR).
    { clear GWI1 DomOW ProgW.
      revert R RWSub. induction W1 using map_ind; intros.
      { assert (R = ∅) by (set_solver). exists ∅, ∅. done. }
      rename i0 into r. rewrite dom_insert_L in RWSub. destruct (decide (r ∈ R)).
      - set (R2 := R ∖ {[r]}). assert (R2 ⊆ dom m).
        { subst R2. set_solver. }
        destruct (IHW1 _ H0) as (WR&WR'&?&?&?).
        exists (<[r:=x]>WR), WR'. subst R2.
        assert (WR !! r = None ∧ WR' !! r = None).
        { apply lookup_union_None. rewrite -H2; auto. }
        destruct H4. split_and !.
        + apply map_disjoint_insert_l. split; auto.
        + subst. rewrite insert_union_l. done.
        + replace R with ({[r]} ∪ (R ∖ {[r]})).
          * rewrite !dom_insert_L H3. auto.
          * rewrite -union_difference_L; set_solver.
      - assert (R ⊆ dom m).
        { set_solver + RWSub n0. }
        pose proof H0. apply IHW1 in H1. destruct H1 as (WR& WR'& ?&?&?).
        assert (WR !! r = None ∧ WR' !! r = None).
        { apply lookup_union_None. rewrite -H2; auto. }
        destruct H4. exists WR, (<[r:=x]>WR'). split_and !; auto.
        + apply map_disjoint_insert_r. split; auto.
        + subst. rewrite insert_union_r; done.
    }
    destruct HW1 as (WR& WR'& DisjWR& EQWR& DomWR).
    iAssert (⌜ ∀ k, k ∈ R → ∃ w, WR !! k = Some w ⌝)%I as "%Rver".
    { iPureIntro. intros. subst. apply elem_of_dom in H. destruct H. eauto. }
    iAssert (|==> [∗ set] r ∈ R, (witG_witness r Ord.one) ∨ (oblG_fulfilled r))%I with "[Ws]" as ">Rs".
    { subst W1. iPoseProof (big_sepM_union with "Ws") as "[Ws1 _]"; first auto. iClear "REs".
      subst R. rewrite -big_sepS_bupd -big_sepM_dom. iApply (big_sepM_impl with "Ws1").
      iIntros "!> %%% H".  destruct x; eauto.
      - iDestruct "H" as "(%&%& Wc)". iLeft. iApply (witG_witness_mon with "Wc").
        apply Ord.S_supremum. eauto.
      - iPoseProof (oblG_expired_fulfilled with "H") as "$". done. }
    iCombine "REs Rs" as "Rs". iPoseProof (big_sepS_sep with "Rs") as "Rs".
    iMod ("H" with "[$Ob $Ox $Oe $OS Rs]") as "H".
    { iApply (big_sepS_impl with "Rs"). iIntros "!> %% (#Ge& [Ww | Gf])"; eauto. }
    iModIntro. assert (dom Ω1 = dom Ω2) by (destruct ProgO; eapply obls_cond_rel_dom; eauto).
    rewrite /model_interp H. iFrame. done.
  Qed.

End mprog.

(* Update physical states. *)
Definition mphys `{SI : indexT} `{!lirisGS Λ Σ} n1 n2 n Θ : iPropO Σ -d> iPropO Σ :=
  (λ P,
     ∀ h a Ω W,
     (model_interp h a Ω W n1 Θ1) ={∅}=∗
     (model_interp (h ++ [(n2, Ω)]) (S a) Ω W n2 Θ2) ∗ P)%I.

Section mphys.
  Context `{SI : indexT} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Global Instance mphys_ne n Θ i : NonExpansive (mphys n Θ i).
  Proof. intros ? P1 P2 HP. rewrite /mphys. do 20 (f_equiv || done). Qed.
  Global Instance mphys_proper n Θ i : Proper ((≡) ==> (≡)) (mphys n Θ i).
  Proof. intros P P' ?. apply equiv_dist=>?. apply mphys_ne. apply equiv_dist. done. Qed.

  Lemma mphys_mono n Θ i P Q : (P ⊢ Q) → (mphys n Θ i P) ⊢ (mphys n Θ i Q).
  Proof.
    intros Hent. rewrite /mphys. iIntros "P %%%% I".
    iMod ("P" with "I") as "(%& $& P)". iModIntro.
    iIntros (??). iMod ("P" with "[//]") as "[$ P]".
    by iApply Hent.
  Qed.
  Lemma mphys_wand_l n Θ i P Q : (P -∗ Q) ∗ (mphys n Θ i P) ⊢ (mphys n Θ i Q).
  Proof.
    iIntros "[PQ P]".
    rewrite /mphys. iIntros "%%%% I".
    iMod ("P" with "I") as "(%& $& P)". iModIntro.
    iIntros (??). iMod ("P" with "[//]") as "[$ P]".
    by iApply "PQ".
  Qed.

  Global Instance mphys_ent_proper n Θ i : Proper ((⊢) ==> (⊢)) (mphys n Θ i).
  Proof. intros P Q PQ. by apply mphys_mono. Qed.
  Global Instance mphys_flip_ent_proper n Θ i : Proper (flip (⊢) ==> flip (⊢)) (mphys n Θ i).
  Proof. intros P Q PQ; by apply mphys_mono. Qed.
  Global Instance mphys_equiv_proper n Θ i : Proper ((≡) ==> (≡)) (mphys n Θ i) := ne_proper _.

  Global Instance elim_mphys (p : bool) n Θ i P Q :
    ElimModal True p false (mphys n Θ i P) P (mphys n Θ i Q) Q.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply (mphys_wand_l with "[$HPQ $HP]").
  Qed.

  Lemma fupd_mphys n Θ i P : (|={∅}=> mphys n Θ i P) ⊢ mphys n Θ i P.
  Proof.
    rewrite /mphys. iIntros "H %%%% IP". iMod ("H" with "IP") as "H". done.
  Qed.
  Global Instance elim_fupd_mphys (p : bool) n Θ i P Q :
    ElimModal True p false (|={∅}=> P) P (mphys n Θ i Q) (mphys n Θ i Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_mphys. iMod "HP".
    iModIntro. iApply ("HPQ" with "HP").
  Qed.

  (** Step rule *)
  Lemma mphys_step n Θ π i P :
    Θ2 = Θ1 ∪ π →
    Θ1 ## π →
    (|={∅}=> ∃ G, th_obls i G 1 ∗ ([∗ map] g ↦ v ∈ G, oblP_fuel g 0 1) ∗
                 ∃ R, ([∗ map] r ↦ v ∈ R, gl r v) ∗
                      ((th_obls i G 1 ∗ ([∗ map] r ↦ v ∈ R, wit r v Ord.one ∨ oblP_done r v) ∗ ([∗ set] j ∈ π, th_obls j ∅ 1))
                       ={∅}=∗ P))
    ⊢ mphys n Θ i P.
  Proof.
    intros ->. unfold_defs. iIntros (DisjTP) "H". iMod "H" as "(%& (#Oe& Ox& Ob& OS)& GFs& %& #REs& H)".
    iAssert ([∗ map] g↦_ ∈ G, oblG_elem g ∗ oblG_fuel g Ord.one)%I with "[GFs]" as "GFs".
    { iApply (big_sepM_impl with "GFs"). iIntros "!> %%% H".
      rewrite (oblG_fuel_eq _ (measure (0 : layer) 1) Ord.one); auto. rewrite measure_nat Ord.from_nat_1. done. }
    iIntros "% % (S& O& A& W& %GWI1)".
    iAssert (⌜ dom G ⊆ dom Ω1 ⌝)%I as "%GOSub".
    { rewrite elem_of_subseteq. iIntros (x INGx).
      apply elem_of_dom in INGx. destruct INGx as (?& INGx).
      iPoseProof (big_sepM_delete _ _ _ _ INGx with "GFs") as "[(#Bex& _) _]".
      iApply (osat_elem with "[$S $Bex]").
    }
    iAssert ([∗ map] k ↦ _ ∈ Ω1, (⌜ k ∈ dom G ⌝ ∗ oblG_fuel k Ord.one) ∨ (⌜ k ∉ dom G ⌝))%I with "[GFs]" as "GFs".
    { rewrite !big_sepM_dom. replace (dom Ω1) with ((dom G) ∪ (dom Ω1 ∖ (dom G))).
      2:{ rewrite -union_difference_L; auto. }
      iApply (big_sepS_union). 1: set_solver.
      iSplitL.
      - iApply (big_sepS_impl with "GFs"). iIntros "!>" (??) "(_& Bfx)". iLeft. iFrame. done.
      - iApply big_sepS_intro. iIntros "!>" (??). iRight. iPureIntro. set_solver + H.
    }
    iAssert (∀ g, ⌜ g ∈ dom G ⌝ → ∃ o, ⌜ Ω1 !! g = Some o ∧ oblP_cond_owner i g o ⌝)%I as "%LUG".
    { iIntros (g INGg). pose proof INGg. apply elem_of_dom in H. destruct H as (?& LUGg).
      iPoseProof (big_sepM_delete _ _ _ _ LUGg with "OS") as "[((#Ge& _)& Gl& [#Gseq Gv]& Go& Oo) _]".
      iPoseProof (othread_obls_lookup _ _ g _ _ _ INGg with "[$S $O $Oe $Ob $Ge]") as "(%& %& %)".
      iExists _. iPureIntro. done.
    }
    iAssert (∀ k, ⌜ k ∈ dom Ω1 ⌝ → ⌜ k ∉ dom G ⌝ → ∃ o, ⌜ Ω1 !! k = Some o ∧ ¬ oblP_cond_owner i k o ⌝)%I as "%NotG".
    { iIntros (k INOk NINGk). apply elem_of_dom in INOk. destruct INOk.
      destruct (decide (oblP_cond_owner i k x)); eauto.
      iExFalso. destruct x. destruct g1; last done. simpl in *. subst.
      iPoseProof (othread_assigned_obls_lookup _ _ k with "[$S $O $A $Ob]") as "%".
      { apply H. }
      done.
    }
    iAssert ([∗ map] k ↦ o ∈ Ω1, (⌜ oblP_cond_owner i k o ⌝ ∗ (∃ c, ⌜ WFOCM.ltR OCM.unit c ⌝ ∗ oblG_fuel k c)) ∨ (⌜ ¬ oblP_cond_owner i k o ⌝))%I with "[GFs]" as "GFs".
    { iApply (big_sepM_impl with "GFs"). iIntros "!>" (???) "[(%& Bfk) | %]".
      - iLeft. iFrame "Bfk". iPureIntro; split.
        + apply LUG in H0. destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
        + apply Ord.S_pos.
      - iRight. iPureIntro. apply NotG in H0.
        + destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
        + apply elem_of_dom; eauto.
    }
    assert (DomOW : dom Ω1 = dom W1) by (eapply owit_inv_dom; eauto).
    iAssert (⌜ dom R ⊆ dom W1 ⌝)%I as "%RWSub".
    { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
      pose proof INRx. apply elem_of_dom in H. destruct H.
      iPoseProof (big_sepM_delete _ _ _ _ H with "REs") as "[[#Beg _] _]".
      iPoseProof (osat_elem with "[$S $Beg]") as "%". done.
    }
    iMod (osat_progress with "[$S $GFs]") as "(%Ω2& S& %ProgO)".
    { intros. destruct g. destruct g0; eauto. done. }
    iModIntro. iExists Ω2. iSplitR; first done. iIntros (W2 (ProgW& GWI2)).
    iMod (owit_progress with "W") as "[W Ws]". 1: eauto.
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
      iPoseProof (osat_lookup_version_lb with "[$S $Ge $Gvl]")as "(%&%&%&%)".
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
    iAssert (|==> [∗ map] r↦v ∈ R, (witG_witness r v Ord.one) ∨ (oblG_unlocked r v))%I with "[Ws]" as ">Rs".
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
          iLeft. iMod (witG_witness_mon_split with "Wc") as "[_ $]"; done.
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
               ((oblG_elem r ∗ oblG_version_lb r v ∗ ([∗ set] u ∈ set_seq 0 v, oblG_version_lb r u ∗ oblG_unlocked r u)) ∗ witG_witness r v Ord.one) ∨
                 ((oblG_elem r ∗ oblG_version_lb r v ∗ ([∗ set] u ∈ set_seq 0 v, oblG_version_lb r u ∗ oblG_unlocked r u)) ∗ oblG_unlocked r v))%I
      with "[Rs]" as "Rs".
    { iPoseProof (big_sepM_sep with "[$Rs $REs]") as "H". iApply (big_sepM_impl with "H").
      iIntros "!> %%% ([Wc | #Gu]& #Ge& #Gvl& #His)".
      - iLeft. iFrame. auto.
      - iRight. auto.
    }
    iMod (othread_alloc_threads π with "O") as "[O Efs]".
    { eauto. }
    iMod ("H" with "[$Ob $Ox $Oe $OS $Rs Efs]") as "H".
    { iApply (big_sepS_impl with "Efs"). iIntros "!> %% ($& $& $)". done. }
    iModIntro. rewrite DomO /gproto. iFrame. done.
  Qed.

End mphys.
