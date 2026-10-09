From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From lantana.base_logic Require Export opreds.
Import uPred.

(** [mprog n Θ i P], written [@={n,Θ,i}=↓ P]: the progress update of a step of
    thread [i]. The obligations owned by [i] make progress, and the witnesses of
    assigned obligations decrease. *)
Definition mprog `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class} n Θ i : iPropO Σ -d> iPropO Σ :=
  (λ P,
     ∀ h a Ω1 W1,
     (model_interp h a Ω1 W1 n Θ) ={∅}=∗
     ∃ Ω2, (⌜(Ω1 ↪ₚ Ω2 | obl_cond_owner i)⌝) ∗
     ∀ W2, (⌜(W1 ↓ₚ W2 | wit_cond_assigned) ∧ owit_inv Ω2 W2 ⌝) ={∅}=∗
           (model_interp (h ++ [(n, Ω2)]) (S a) Ω2 W2 n Θ) ∗ P)%I.

Notation "'@={' n , Θ , i '}=↓' P" := (mprog n Θ i P) (at level 99, P at level 200, format "@={ n , Θ , i }=↓  P").

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

  (** Introduction rule: thread [i] spends one unit of fuel of each carrier in [U],
      and gets a witness credit (or a proof of discharge) for each obligation in
      [R]. *)
  Lemma mprog_step n Θ i P :
    (|={∅}=> ∃ U, thP_carriers i U ∗ ([∗ set] u ∈ U, ∃ ℓ, crP_fuel u ℓ 1) ∗
                   ∃ R, ([∗ set] r ∈ R, ∃ ℓ, witP_layer r ℓ) ∗
                        ((thP_carriers i U ∗ ([∗ set] r ∈ R, witP_cred r Ord.one ∨ oblP_discharged r))
                         ={∅}=∗ P))
    ⊢ mprog n Θ i P.
  Proof.
    unfold_opreds. iIntros "H". iMod "H" as "(%& (#Oe& Ox& Ob& Ow)& GFs& %& #REs& H)".
    iIntros "%%%% (MH& S& O& A& G& W& %GWI1)".
    iAssert (|==> [∗ set] u ∈ U, ocarrierG_fuel u Ord.one)%I with "[GFs]" as ">GFs".
    { iApply big_sepS_bupd. iApply (big_sepS_impl with "GFs"). iIntros "!> % % (%& F)".
      iApply (ocarrierG_fuel_mon with "F"). 
      rewrite measure_rep_mult measure_rep_nat Jacobsthal.mult_1_r. rewrite measure_rep_add measure_rep_nat.
      eapply Hessenberg.add_base_l. }
    iPoseProof (othread_elem with "[$O $Oe]") as "%Ini".
    iMod (ocarrier_exchange_fuel with "[$G $Ob $GFs]") as "(%& ACC& Gta& Ox2& Ob& GFs)". 1: auto.
    { apply Ord.S_lt. }
    iAssert ([∗ set] k ∈ G, oblG_elem k)%I as "#Ges".
    { iApply (big_sepS_impl with "GFs"). iIntros "!> %% [_ $]". }
    iAssert (⌜ G ⊆ dom Ω1 ⌝)%I as "%GOSub".
    { rewrite elem_of_subseteq. iIntros (x INGx).
      iPoseProof (big_sepS_delete _ _ _ INGx with "GFs") as "[(_& #Bex) _]".
      iApply (osat_elem with "[$S $Bex]"). }
    iAssert ([∗ map] k ↦ _ ∈ Ω1, (⌜ k ∈ G ⌝ ∗ oblG_fuel k Ord.one) ∨ (⌜ k ∉ G ⌝))%I with "[GFs]" as "GFs".
    { rewrite !big_sepM_dom. replace (dom Ω1) with (G ∪ (dom Ω1 ∖ G)).
      2:{ rewrite -union_difference_L; auto. }
      iApply (big_sepS_union). 1: set_solver.
      iSplitL.
      - iApply (big_sepS_impl with "GFs"). iIntros "!>" (??) "(H& Bfx)". iLeft. iFrame. done.
      - iApply big_sepS_intro. iIntros "!>" (??). iRight. iPureIntro. set_solver + H. }
    iAssert (∀ g, ⌜ g ∈ G ⌝ → ∃ o, ⌜ Ω1 !! g = Some o ∧ obl_cond_owner i g o ⌝)%I as "%LUG".
    { iIntros (g INGg). pose proof INGg.
      iPoseProof (big_sepS_delete _ _ _ INGg with "Ges") as "[#Ge _]".
      iPoseProof (othread_obls_lookup _ _ g _ _ INGg with "[$S $O $Oe $Ob $Ge]") as "(%& %)".
      iExists _. iPureIntro. done. }
    iAssert (∀ k, ⌜ k ∈ dom Ω1 ⌝ → ⌜ k ∉ G ⌝ → ∃ o, ⌜ Ω1 !! k = Some o ∧ ¬ obl_cond_owner i k o ⌝)%I as "%NotG".
    { iIntros (k INOk NINGk). apply elem_of_dom in INOk. destruct INOk.
      destruct (decide (obl_cond_owner i k x)); eauto.
      iExFalso. destruct x; try done. simpl in o. subst.
      iPoseProof (othread_assigned_obls_lookup _ _ k with "[$S $O $A $Ob]") as "%"; eauto. }
    iAssert ([∗ map] k ↦ o ∈ Ω1, (⌜ obl_cond_owner i k o ⌝ ∗ (∃ c, ⌜ WFOCM.ltR OCM.unit c ⌝ ∗ oblG_fuel k c)) ∨ (⌜ ¬ obl_cond_owner i k o ⌝))%I with "[GFs]" as "GFs".
    { iApply (big_sepM_impl with "GFs"). iIntros "!>" (???) "[(%& Bfk) | %]".
      - iLeft. iFrame "Bfk". iPureIntro; split.
        + apply LUG in H0. destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
        + apply Ord.S_pos.
      - iRight. iPureIntro. apply NotG in H0.
        + destruct H0 as (?& ?& ?). rewrite H in H0. inv H0. auto.
        + apply elem_of_dom; eauto. }
    assert (DomOW : dom Ω1 = dom W1) by (eapply owit_inv_dom; eauto).
    iAssert (⌜ R ⊆ dom W1 ⌝)%I as "%RWSub".
    { rewrite -DomOW. rewrite elem_of_subseteq. iIntros (x INRx).
      iPoseProof (big_sepS_delete _ _ _ INRx with "REs") as "[#Beg _]".
      iDestruct "Beg" as "(%&%& Beg& _)".
      iPoseProof (osat_elem with "[$S $Beg]") as "%". done. }
    iMod (osat_progress with "[$S $GFs]") as "(%Ω2& S& %ProgO)".
    { intros. destruct g; try done. eauto. }
    iMod (model_history_interp_step _ _ n n _ Ω2 with "MH") as "MH". 1: done.
    { eapply obls_cond_progress_obls_le; eauto. }
    iPoseProof ("ACC" with "Ox2 Ob") as "G".
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
        + subst. rewrite insert_union_r; done. }
    destruct HW1 as (WR& WR'& DisjWR& EQWR& DomWR).
    iAssert (⌜ ∀ k, k ∈ R → ∃ w, WR !! k = Some w ⌝)%I as "%Rver".
    { iPureIntro. intros. subst. apply elem_of_dom in H. destruct H. eauto. }
    iAssert (|==> [∗ set] r ∈ R, (witG_witness r Ord.one) ∨ (oblG_discharged r))%I with "[Ws]" as ">Rs".
    { subst W1. iPoseProof (big_sepM_union with "Ws") as "[Ws1 _]"; first auto. iClear "REs".
      subst R. rewrite -big_sepS_bupd -big_sepM_dom. iApply (big_sepM_impl with "Ws1").
      iIntros "!> %%% H".  destruct x; eauto.
      - iDestruct "H" as "(%&%& Wc)". iLeft. iApply (witG_witness_mon with "Wc").
        apply Ord.S_supremum. eauto. }
    iCombine "REs Rs" as "Rs". iPoseProof (big_sepS_sep with "Rs") as "Rs".
    iMod ("H" with "[$Oe $Ox $Ow $Gta Rs]") as "H".
    { iApply (big_sepS_impl with "Rs"). iIntros "!> %% ((%&%& #Ge& #Wb)& [Ww | Gf])"; eauto. }
    iModIntro. assert (dom Ω1 = dom Ω2) by (destruct ProgO; eapply obls_cond_rel_dom; eauto).
    rewrite /model_interp H. iFrame. done.
  Qed.

End mprog.

(** [mphys n1 n2 Θ1 Θ2 P], written [@={n1,n2,Θ1,Θ2}=> P]: the physical update of a
    step, from step [n1] with threads [Θ1] to step [n2] with threads [Θ2]. *)
Definition mphys `{SI : indexT} `{!mupdGS Σ} `{!ord_mono_fun_class} n1 n2 Θ1 Θ2 : iPropO Σ -d> iPropO Σ :=
  (λ P,
     ∀ h a Ω W,
     (model_interp h a Ω W n1 Θ1) ={∅}=∗
     (model_interp (h ++ [(n2, Ω)]) (S a) Ω W n2 Θ2) ∗ P)%I.

Notation "'@={' n1 , n2 , Θ1 , Θ2 '}=>' P" := (mphys n1 n2 Θ1 Θ2 P) (at level 99, P at level 200, format "@={ n1 , n2 , Θ1 , Θ2 }=>  P").

Section mphys.
  Context `{SI : indexT} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.

  Global Instance mphys_ne n1 n2 Θ1 Θ2 : NonExpansive (mphys n1 n2 Θ1 Θ2).
  Proof. intros ? P1 P2 HP. rewrite /mphys. do 20 (f_equiv || done). Qed.
  Global Instance mphys_proper n1 n2 Θ1 Θ2 : Proper ((≡) ==> (≡)) (mphys n1 n2 Θ1 Θ2).
  Proof. intros P P' ?. apply equiv_dist=>?. apply mphys_ne. apply equiv_dist. done. Qed.

  Lemma mphys_mono n1 n2 Θ1 Θ2 P Q : (P ⊢ Q) → (mphys n1 n2 Θ1 Θ2 P) ⊢ (mphys n1 n2 Θ1 Θ2 Q).
  Proof.
    intros Hent. rewrite /mphys. iIntros "P %%%% I".
    iMod ("P" with "I") as "[$ P]". iModIntro.
    by iApply Hent.
  Qed.
  Lemma mphys_wand_l n1 n2 Θ1 Θ2 P Q : (P -∗ Q) ∗ (mphys n1 n2 Θ1 Θ2 P) ⊢ (mphys n1 n2 Θ1 Θ2 Q).
  Proof.
    iIntros "[PQ P]".
    rewrite /mphys. iIntros "%%%% I".
    iMod ("P" with "I") as "($& P)". iModIntro.
    by iApply "PQ".
  Qed.

  Global Instance mphys_ent_proper n1 n2 Θ1 Θ2 : Proper ((⊢) ==> (⊢)) (mphys n1 n2 Θ1 Θ2).
  Proof. intros P Q PQ. by apply mphys_mono. Qed.
  Global Instance mphys_flip_ent_proper n1 n2 Θ1 Θ2 : Proper (flip (⊢) ==> flip (⊢)) (mphys n1 n2 Θ1 Θ2).
  Proof. intros P Q PQ; by apply mphys_mono. Qed.
  Global Instance mphys_equiv_propern1 n1 n2 Θ1 Θ2 : Proper ((≡) ==> (≡)) (mphys n1 n2 Θ1 Θ2) := ne_proper _.

  Global Instance elim_mphys (p : bool) n1 n2 Θ1 Θ2 P Q :
    ElimModal True p false (mphys n1 n2 Θ1 Θ2 P) P (mphys n1 n2 Θ1 Θ2 Q) Q.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply (mphys_wand_l with "[$HPQ $HP]").
  Qed.

  Lemma fupd_mphys n1 n2 Θ1 Θ2 P : (|={∅}=> mphys n1 n2 Θ1 Θ2 P) ⊢ mphys n1 n2 Θ1 Θ2 P.
  Proof.
    rewrite /mphys. iIntros "H %%%% IP". iMod ("H" with "IP") as "H". done.
  Qed.
  Global Instance elim_fupd_mphys (p : bool) n1 n2 Θ1 Θ2 P Q :
    ElimModal True p false (|={∅}=> P) P (mphys n1 n2 Θ1 Θ2 Q) (mphys n1 n2 Θ1 Θ2 Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim //=.
    iIntros "_ [HP HPQ]". iApply fupd_mphys. iMod "HP".
    iModIntro. iApply ("HPQ" with "HP").
  Qed.

  (** Introduction rule: the new threads [π] start with empty carrier sets. *)
  Lemma mphys_step n1 n2 Θ1 Θ2 π P :
    n1 ≤ n2 →
    Θ2 = Θ1 ∪ π →
    Θ1 ## π →
    (|={∅}=> ([∗ set] j ∈ π, thP_carriers j ∅) ={∅}=∗ P)
    ⊢ mphys n1 n2 Θ1 Θ2 P.
  Proof.
    intros LE ->. unfold_opreds. iIntros (DisjTP) "H". iMod "H".
    iIntros "%%%% (MH& S& O& A& G& W& %GWI1)".
    iMod (model_history_interp_step _ _ n1 n2 _ Ω with "MH") as "MH". 1,2: done.
    iMod (othread_alloc_threads π with "O") as "[O Efs]". 1: eauto.
    iAssert (([∗ set] i ∈ π, othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅) ∗
             ([∗ set] i ∈ π, othreadG_elem i ∗ othreadG_exec i (1/2)))%I with "[Efs]" as "[TGs Efs]".
    { iApply big_sepS_sep. iApply (big_sepS_impl with "Efs"). iIntros "!> %% ($& $& [$ $])". }
    iMod (ocarrier_alloc_threads π with "[$G $TGs]") as "[G Gtas]". 1: eauto.
    iMod ("H" with "[Efs Gtas]") as "H".
    { iPoseProof (big_sepS_sep with "[$Efs $Gtas]") as "Efs".
      iApply (big_sepS_impl with "Efs"). iIntros "!> %% (($& $)& $)". done. }
    iModIntro. rewrite /model_interp. iFrame. done.
  Qed.

End mphys.
