From iris.algebra Require Import gmap_view reservation_map.
From iris.bi.lib Require Import cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From lantana.algebra Require Export wfocm.
From lantana.algebra Require Import bcred.
From lantana.base_logic Require Export witness osat.

(** The ghost state for witnesses *)
Module owitGS.

  Class owitGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OwitGpreS {
        owitGpreS_witness : inG Σ (reservation_mapUR (bcredUR));
      }.

  Class owitGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OwitG {
        owit_inG : owitGpreS Σ;
        witness_name : gname;
      }.

  Definition owitΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (bcredUR))
      ].

  Global Instance subG_owitΣ `{SI : indexT} {Σ} : subG (owitΣ) Σ → (owitGpreS Σ).
  Proof. solve_inG. Qed.

End owitGS.
Import owitGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances owit_inG owitGpreS_witness.

(* Witness credits of obligation [k], spent against the bound [witG_bound]. *)
Definition witG_bound `{SI : indexT} `{!owitGS Σ}
  (k : oid) (ℵ : obl_fuel) : iProp Σ :=
  own witness_name (reservation_map_data (A:=bcredUR) k (credit_bound ℵ)).
Global Typeclasses Opaque witG_bound.
Global Instance: Params (@witG_bound) 3 := {}.

Definition witG_witness `{SI : indexT} `{!owitGS Σ}
  (k : oid) (a : obl_fuel) : iProp Σ :=
  own witness_name (reservation_map_data (A:=bcredUR) k (credit a)).
Global Typeclasses Opaque witG_witness.
Global Instance: Params (@witG_witness) 3 := {}.

Local Definition witG_bound_token_id `{SI : indexT} `{!owitGS Σ}
  (E : coPset) : iProp Σ :=
  own witness_name (reservation_map_token (A:=bcredUR) E).

(* Global invariant for the witness ghost state *)
Definition owit `{SI : indexT} {Σ}
  `{!@osatGS.osatGS _ Σ} `{!owitGS Σ}
  (W : witnesses) : iProp Σ :=
  locked
    (witG_bound_token_id (⊤ ∖ gset_to_coPset (dom W)) ∗
     ([∗ map] k ↦ w ∈ W,
        match w with
        | witness_assigned b =>
            (∃ α, (⌜ WFOCM.leR b α ⌝) ∗ witG_witness k α)
        | witness_discharged =>
            (oblG_discharged k)
        end)
    )%I.

(* Relates witnesses to obligations: an assigned obligation with fuel [a] has an
   assigned witness [b] with [b ≤ η a], and a discharged obligation has a discharged
   witness. *)
Definition owit_inv `{!ord_mono_fun_class}
  (Ω : obls) (W : witnesses) : Prop :=
  map_Forall2 (λ k g w,
                 match g, w with
                 | (obl_assigned a _), (witness_assigned b) => (b w≤ η a)
                 | (obl_discharged), (witness_discharged) => True
                 | _, _ => False
                 end
    ) Ω W.

(** Properties *)
Section owit.
  Context `{SI : indexT} `{OSAT : !osatGS.osatGS Σ} `{!owitGS Σ} `{OMF : !ord_mono_fun_class}.

  (* witness *)
  Global Instance witG_bound_persistent k ℵ : Persistent (witG_bound k ℵ).
  Proof. rewrite /witG_bound. apply _. Qed.
  Global Instance witG_bound_timeless k ℵ : Timeless (witG_bound k ℵ).
  Proof. rewrite /witG_bound. apply _. Qed.

  Global Instance witG_witness_timeless k a : Timeless (witG_witness k a).
  Proof. rewrite /witG_witness. apply _. Qed.

  Local Instance witG_bound_token_id_timeless E : Timeless (witG_bound_token_id E).
  Proof. rewrite /witG_bound_token_id. apply _. Qed.

  (* owit *)
  Global Instance owit_timeless W : Timeless (owit W).
  Proof. rewrite /owit -lock. apply _. Qed.

  (** Witness credit rules *)
  Lemma witG_witness_eq k a0 a1 :
    a0 w= a1 →
    witG_witness k a0 = witG_witness k a1.
  Proof. intros EQ. rewrite /witG_witness. by erewrite credit_eq. Qed.

  Lemma witG_witness_mon k a0 a1 :
    a0 w≤ a1 →
    witG_witness k a1 ⊢ |==> witG_witness k a0.
  Proof.
    intros LE. rewrite /witG_witness. apply own_update.
    by apply reservation_map_update, credit_update.
  Qed.

  Lemma witG_witness_split k a0 a1 :
    witG_witness k (a0 w+ a1) ⊣⊢ witG_witness k a0 ∗ witG_witness k a1.
  Proof.
    rewrite /witG_witness. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite credit_split). iSplitL "H1"; iFrame.
  Qed.

  Lemma witG_witness_mon_split k a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    witG_witness k a2 ⊢ |==> witG_witness k a0 ∗ witG_witness k a1.
  Proof.
    intros LE. iIntros "H". iApply witG_witness_split. iApply witG_witness_mon; done.
  Qed.

  Lemma witG_witness_lt k a0 a1 :
    a0 w< a1 →
    witG_witness k a1 ⊢ |==> witG_witness k a0 ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ witG_witness k c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (witG_witness_mon_split _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.

  Lemma witG_bound_mon k a0 a1 :
    a0 w≤ a1 →
    witG_bound k a0 ⊢ |==> witG_bound k a1.
  Proof.
    intros LE. rewrite /witG_bound. apply own_update.
    by apply reservation_map_update, cmra_update_included, credit_bound_included.
  Qed.

  Lemma witG_witness_spend_gen k a0 a1 :
    witG_bound k a0 ∗ witG_witness k a1
    ⊢ |==> ∃ a2, ⌜(a1 w+ a2) w≤ a0⌝ ∗ witG_bound k a2.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -!reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ x, ∃ a2, (x = (credit_bound a2)) ∧ (a1 w+ a2 w≤ a0))
                (λ r, ∃ a2, (r = {[k := (credit_bound a2)]}) ∧ (a1 w+ a2 w≤ a0))
             ).
      { eapply credit_spend. }
      { intros. destruct H as (a2&A0&A1). eexists. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplitR; done.
  Qed.
  Lemma witG_witness_spend k a0 a1 :
    wzero w< a1 →
    witG_bound k a0 ∗ witG_witness k a1 ⊢ |==> ∃ a2, ⌜a2 w< a0⌝ ∗ witG_bound k a2.
  Proof.
    iIntros (LT) "[Ow Oc]". iMod (witG_witness_spend_gen with "[$]") as "(%&%&$)".
    iPureIntro. eapply WFOCM.lt_exists_right; eauto.
  Qed.

  Lemma witG_compare k a0 a1 :
    witG_bound k a0 ∗ witG_witness k a1 ⊢ ⌜ a1 w≤ a0 ⌝.
  Proof.
    rewrite -own_op -!reservation_map_data_op. iIntros "H".
    iPoseProof (own_valid with "H") as "%". apply reservation_map_data_valid in H.
    apply credit_bound_credit_valid_compare in H. done.
  Qed.

  Lemma witG_bound_id_alloc D k a :
    k ∉ D →
    witG_bound_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> witG_bound_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        witG_bound k a ∗ witG_witness k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (credit_bound a ⋅ credit a) with "Htk") as "[Htk >H]"; auto.
    { apply credit_bound_credit_valid_eq. }
    iDestruct "H" as "[H1 H2]". rewrite /witG_bound /witG_witness. by iFrame.
  Qed.

  (** owit rules *)
  Lemma owit_alloc_witness_assigned W k a :
    k ∉ dom W →
    owit W
    ⊢ |==> owit (<[k:=(witness_assigned a)]>W) ∗ witG_bound k a.
  Proof.
    iIntros (Nink) "W".
    rewrite /owit -!lock. iDestruct "W" as "(Wti& WM)".
    iMod (witG_bound_id_alloc _ _ a Nink with "Wti") as "(Wti& #Wb& Ww)".
    iModIntro. iFrame "Wb".
    rewrite dom_insert_L. iFrame "Wti".
    iApply big_sepM_insert.
    { apply not_elem_of_dom. auto. }
    iFrame. done.
  Qed.

  Lemma owit_alloc_witness_discharged W k a :
    k ∉ dom W →
    owit W ∗ oblG_discharged k
    ⊢ |==> owit (<[k:=(witness_discharged)]>W) ∗ witG_bound k a.
  Proof.
    iIntros (Nink) "(W& #Gu)".
    rewrite /owit -!lock. iDestruct "W" as "(Wti& WM)".
    iMod (witG_bound_id_alloc _ _ a Nink with "Wti") as "(Wti& #Wb& Ww)".
    iModIntro. iFrame "Wb".
    rewrite dom_insert_L. iFrame "Wti".
    iApply big_sepM_insert.
    { apply not_elem_of_dom. auto. }
    iFrame. eauto.
  Qed.

  Lemma owit_mon W1 W2 :
    wits_mon W1 W2 →
    owit W1 ⊢ owit W2.
  Proof.
    iIntros (Step) "W".
    assert (Dom : dom W1 = dom W2) by (eapply map_Forall2_dom_L; eauto).
    rewrite /owit -!lock. iDestruct "W" as "(Wti& WM)".
    rewrite -Dom. iFrame "Wti".
    iStopProof. clear Dom.
    revert W2 Step. induction W1 using map_ind; iIntros (W2 Step) "WM".
    { apply map_Forall2_empty_inv_l in Step. subst. by iFrame. }
    apply map_Forall2_insert_inv_l in Step; last auto.
    destruct Step as (w2& m2& EqW2& LUm2& Stepi& Step). subst. rewrite !big_sepM_insert; auto.
    rename x into w1. iDestruct "WM" as "(WH1& WM)".
    iPoseProof (IHW1 _ Step with "WM") as "WM". clear IHW1. iFrame "WM".
    destruct w1, w2; try done.
    iDestruct "WH1" as "(%& %& $)". iPureIntro. etransitivity; eauto.
  Qed.

  (* Witness steps: progress and discharge. *)
  Lemma owit_progress_one W k w1 w2 :
    W !! k = Some (witness_assigned w1) →
    witness_step (witness_assigned w1) (witness_assigned w2) →
    owit W
    ⊢ |==> owit (<[k:=(witness_assigned w2)]>W) ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ witG_witness k c.
  Proof.
    iIntros (Luk Prog) "W".
    rewrite /owit -!lock. iDestruct "W" as "(Wti& WM)".
    assert (Ink : k ∈ dom W).
    { apply elem_of_dom. eauto. }
    assert (DomEq : {[k]} ∪ dom W = dom W).
    { set_solver + Ink. }
    rewrite !dom_insert_L !DomEq. iFrame "Wti". inv Prog. 2: inv H. inv H.
    iPoseProof (big_sepM_delete _ _ _ _ Luk with "WM") as "[Mk WM]".
    iDestruct "Mk" as "(%& %& Wck)".
    assert (Lt : w2 w< α).
    { eapply WFOCM.lt_le_lt; eauto. }
    apply WFOCM.lt_exists_left in Lt. destruct Lt as (?& Lt& Le).
    iMod (witG_witness_mon_split _ _ _ _ Le with "Wck") as "[Wck Wck0]".
    iModIntro. iFrame "Wck0". iSplitL; last done.
    rewrite -(insert_delete_eq W k). iApply big_sepM_insert.
    { apply lookup_delete_eq. }
    iFrame. auto.
  Qed.

  Lemma owit_progress W1 W2 :
    (W1 ↓ₚ W2 | wit_cond_assigned) →
    owit W1
    ⊢ |==> owit W2 ∗
        ([∗ map] k ↦ w ∈ W1,
           match w with
           | witness_assigned _ =>
               (∃ c, ⌜ wzero w< c ⌝ ∗ witG_witness k c)
           | witness_discharged =>
               (oblG_discharged k)
           end).
  Proof.
    iIntros ([Step Keep]) "W".
    assert (Dom : dom W1 = dom W2) by (eapply wits_cond_rel_dom; eauto).
    rewrite /owit -!lock. iDestruct "W" as "(Wti& WM)".
    rewrite -Dom. iFrame "Wti".
    iStopProof. clear Dom.
    revert W2 Step Keep. induction W1 using map_ind; iIntros (W2 Step Keep) "WM".
    { apply map_Forall2_empty_inv_l in Step. subst. iModIntro. iFrame. done. }
    apply map_Forall2_insert_inv_l in Keep; last auto.
    destruct Keep as (w2& m2& EqW2& LUm2& Keepi& Keep). subst. rewrite !big_sepM_insert; auto.
    apply map_Forall2_insert in Step; auto.
    rename x into w1. iDestruct "WM" as "(Mi& M)".
    destruct Step as [HC Step].
    iMod (IHW1 _ Step Keep with "M") as "[M Rs]". clear IHW1.
    iFrame "M Rs". destruct HC as [[HC Stepi] | [HC Eqi]].
    - destruct w1. 2: done. destruct w2. 2: done. inv Stepi. 2: inv H0. inv H0.
      iDestruct "Mi" as "(%& %& Mci)". assert (Lt : wit0 w< α).
      { eapply WFOCM.lt_le_lt; eauto. }
      apply WFOCM.lt_exists_left in Lt. destruct Lt as (?& Lt& Le).
      iMod (witG_witness_mon_split _ _ _ _ Le with "Mci") as "[Mci Mci0]".
      iModIntro. iSplitL "Mci".
      + iFrame. done.
      + iFrame. done.
    - subst. destruct w2. 2: eauto. done.
  Qed.

  Lemma owit_progress_any C W1 W2 :
    (W1 ↓ₚ W2 | C) →
    owit W1 ⊢ owit W2.
  Proof.
    iIntros (Prog) "W".
    iApply (owit_mon with "W").
    eapply wits_cond_progress_mon; eauto.
  Qed.

  Lemma owit_discharge W k a :
    W !! k = Some (witness_assigned a) →
    owit W ∗ oblG_discharged k
    ⊢ owit (<[k:=(witness_discharged)]>W).
  Proof.
    iIntros (Luk) "[W #Guk]".
    rewrite /owit -!lock. iDestruct "W" as "(Wti& WM)".
    iPoseProof (big_sepM_delete _ _ _ _ Luk with "WM") as "[Wk WM]".
    rewrite !dom_insert_L. replace ({[k]} ∪ dom W) with (dom W); cycle 1.
    { apply elem_of_dom_2 in Luk. set_solver. }
    iFrame. rewrite -(insert_delete_eq W k). iApply big_sepM_insert.
    { apply lookup_delete_eq. }
    iFrame. eauto.
  Qed.

  Lemma owit_get_credit_zero W :
    owit W
    ⊢ owit W ∗
    ([∗ map] k ↦ w ∈ W,
       match w with
       | witness_assigned _ =>
           (witG_witness k wzero)
       | witness_discharged =>
           (oblG_discharged k)
       end).
  Proof.
    iIntros "W".
    rewrite /owit -!lock. iDestruct "W" as "(Wti& WM)".
    iFrame "Wti".
    iStopProof. induction W using map_ind; iIntros "WM".
    { iFrame. done. }
    rewrite !big_sepM_insert; auto.
    rename  x into w1. iDestruct "WM" as "(Mi& M)".
    iPoseProof (IHW with "M") as "[M Rs]". clear IHW.
    iFrame "M Rs". destruct w1.
    - iDestruct "Mi" as "(%& %& Wc)". rewrite (witG_witness_eq _ α (α w+ wzero)); cycle 1.
      { rewrite right_id. done. }
      iPoseProof (witG_witness_split with "Wc") as "[Wc Wcz]". iSplitR "Wcz"; iFrame; eauto.
    - iPoseProof "Mi" as "#Mi". auto.
  Qed.

  (** owit_inv rules *)
  Lemma owit_inv_empty :
    owit_inv ∅ ∅.
  Proof. apply map_Forall2_empty. Qed.

  Lemma owit_inv_dom Ω W :
    owit_inv Ω W → dom Ω = dom W.
  Proof. intros. eapply map_Forall2_dom_L; eauto. Qed.

  Lemma owit_inv_cond_step_same_gls C Ω W1 W2 :
    owit_inv Ω W1 →
    (W1 ↓ₛ W2 | C) →
    owit_inv Ω W2 →
    wits_mon W1 W2.
  Proof.
    revert Ω W2. induction W1 using map_ind; intros.
    { apply map_Forall2_empty_inv_l in H0. subst. done. }
    rename x into w1, m into W1, W2 into W2', Ω into Ω'.
    apply map_Forall2_insert_inv_r in H0; auto. destruct H0 as (g& Ω& EQO& LUOi& HO1& MFO).
    apply map_Forall2_insert_inv_l in H1; auto. destruct H1 as (w2& W2& EQW2& LUWi2& HC& MFW).
    subst. apply map_Forall2_insert in H2; auto. destruct H2 as (How& MFW2).
    pose proof (IHW1 _ _ MFO MFW MFW2) as IH.
    apply map_Forall2_insert; auto. split; auto.
    clear MFW2 MFW MFO IHW1 IH.
    destruct HC as [[HC Step] | [HC EQ]].
    - destruct g, w1, w2; inv Step; inv H0; try done. eapply WFOCM.lt_le; auto.
    - subst. destruct g, w2; try done.
  Qed.
  Lemma owit_inv_one_step_same_gls Ω W1 W2 :
    owit_inv Ω W1 →
    W1 ↓₁ W2 →
    owit_inv Ω W2 →
    wits_mon W1 W2.
  Proof.
    intros. apply wits_one_to_wits_cond in H0. destruct H0. eapply (owit_inv_cond_step_same_gls _ Ω W1 W2); eauto.
  Qed.

  Lemma owit_inv_alloc_same_gls_dom Ω1 Ω2 W1 W2 :
    dom Ω1 = dom Ω2 →
    owit_inv Ω1 W1 →
    (W1 ↓ₐ W2) →
    owit_inv Ω2 W2 →
    False.
  Proof.
    intros. destruct H1 as (k& LU& g& HE); subst.
    apply owit_inv_dom in H0, H2. rewrite -H H0 dom_insert_L in H2.
    apply not_elem_of_dom in LU. set_solver.
  Qed.

  Lemma owit_inv_step_same_gls Ω W1 W2 :
    owit_inv Ω W1 →
    (W1 ↓ W2) →
    owit_inv Ω W2 →
    wits_mon W1 W2.
  Proof.
    intros. inv H0.
    - eapply owit_inv_one_step_same_gls; eauto.
    - exfalso. eapply (owit_inv_alloc_same_gls_dom Ω Ω W1 W2); eauto.
  Qed.
  Lemma owit_inv_rc_step_same_gls Ω W1 W2 :
    owit_inv Ω W1 →
    (W1 ↓∘ W2) →
    owit_inv Ω W2 →
    wits_mon W1 W2.
  Proof.
    intros. inv H0.
    - done.
    - eapply owit_inv_step_same_gls; eauto.
  Qed.

  Lemma owit_inv_alloc_same_wits_dom Ω1 Ω2 W1 W2 :
    dom W1 = dom W2 →
    owit_inv Ω1 W1 →
    (Ω1 ↪ₐ Ω2) →
    owit_inv Ω2 W2 →
    False.
  Proof.
    intros. destruct H1 as (k& LU& ?& HE); subst.
    apply owit_inv_dom in H0, H2. rewrite -H -H0 dom_insert_L in H2.
    apply not_elem_of_dom in LU. set_solver.
  Qed.

  Lemma owit_inv_progress_owner Ω k a t1 W1 :
    Ω !! k = Some (obl_assigned a t1) →
    owit_inv Ω W1 →
    ∀ a' t2,
    obl_step (obl_assigned a t1) (obl_assigned a' t2) →
    ∀ W2,
    W1 ↓∘ W2 →
    owit_inv (<[k:=(obl_assigned a' t2)]> Ω) W2 →
    wits_mon W1 W2.
  Proof.
    intros LUO INV1 a' t2 GStep W2 WSStep INV2.
    inv GStep; inv H.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    destruct y; try done. symmetry in H0.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    destruct y; try done. symmetry in H2.
    eapply (owit_inv_rc_step_same_gls Ω). 1: eapply INV1. 1: eauto.
    intros i. specialize (INV2 i). destruct (decide (k = i)).
    - subst. rewrite lookup_insert_eq H2 in INV2. rewrite LUO H2.
      inv INV2. econstructor.
      apply η_lt_proper in LTf. etrans; first eauto. eapply WFOCM.lt_le; eauto.
    - rewrite lookup_insert_ne in INV2; auto.
  Qed.

  Lemma owit_inv_discharge Ω k a t W1 :
    Ω !! k = Some (obl_assigned a t) →
    owit_inv Ω W1 →
    obl_step (obl_assigned a t) (obl_discharged) →
    ∀ W2,
    W1 ↓∘ W2 →
    owit_inv (<[k:=(obl_discharged)]> Ω) W2 →
    (∃ b, W1 !! k = Some (witness_assigned b) ∧ wits_mon (<[k:=(witness_discharged)]> W1) W2).
  Proof.
    intros LUO INV1 GStep W2 WSStep INV2.
    inv GStep; inv H.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    destruct y; try done. symmetry in H0.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    destruct y; try done. symmetry in H2.
    eexists. split; first eauto.
    inv WSStep. inv H; cycle 1.
    { eapply (owit_inv_alloc_same_gls_dom Ω (<[k:=(obl_discharged)]> Ω)) in H4; eauto; first done.
      rewrite dom_insert_L. apply elem_of_dom_2 in LUO. set_solver + LUO. }
    apply wits_one_to_wits_cond in H4. destruct H4 as (?&H4). assert (x = k).
    { specialize (H4 k). rewrite H0 H2 in H4. inv H4. destruct H6.
      - destruct H; done.
      - destruct H; done. }
    subst x.
    intros i. specialize (H4 i). destruct (decide (i = k)).
    { subst. rewrite H2 lookup_insert_eq. econstructor. done. }
    rewrite lookup_insert_ne; auto.
    destruct (Ω !! i) eqn:LUO2.
    - pose proof INV1 as I3. specialize (I3 i). rewrite LUO2 in I3. inv I3.
      pose proof INV2 as I4. specialize (I4 i). rewrite lookup_insert_ne in I4; auto.
      rewrite LUO2 in I4. inv I4. symmetry in H5, H7.
      rewrite H5 H7 in H4. inv H4. econstructor.
      destruct H10 as [[HC WS] | [HC WS]]; cycle 1.
      { inv WS. destruct o, y0; try done. }
      inv WS.
    - pose proof INV1 as I3. specialize (I3 i). rewrite LUO2 in I3. inv I3.
      symmetry in H.
      pose proof INV2 as I4. specialize (I4 i). rewrite lookup_insert_ne in I4; auto.
      rewrite LUO2 in I4. inv I4.
      symmetry in H5. econstructor.
  Qed.

  Lemma owit_inv_alloc_assigned Ω k W1 :
    k ∉ dom Ω →
    owit_inv Ω W1 →
    ∀ a t W2,
    W1 ↓∘ W2 →
    owit_inv (<[k:=(obl_assigned a t)]> Ω) W2 →
    (k ∉ dom W1 ∧ wits_mon (<[k:=(witness_assigned (η a))]> W1) W2).
  Proof.
    intros LUO INV1 a t W2 WSStep INV2.
    apply not_elem_of_dom in LUO.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    symmetry in H.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    rename y into w. destruct w; try done. symmetry in H1.
    split.
    { apply not_elem_of_dom. auto. }
    inv WSStep. inv H0.
    { apply wits_one_dom in H3. exfalso. apply elem_of_dom_2 in H1. apply not_elem_of_dom in H.
      rewrite H3 in H. set_solver. }
    destruct H3 as (?&?&?&?).
    subst. destruct (decide (k = x)).
    - subst x. rewrite lookup_insert_eq in H1. inv H1. apply map_Forall2_insert; auto.
      split; auto. reflexivity.
    - rewrite lookup_insert_ne in H1; auto. rewrite H in H1. inv H1.
  Qed.

  Lemma owit_inv_alloc_discharged Ω k W1 :
    k ∉ dom Ω →
    owit_inv Ω W1 →
    ∀ W2,
    W1 ↓∘ W2 →
    owit_inv (<[k:=(obl_discharged)]> Ω) W2 →
    (k ∉ dom W1 ∧ wits_mon (<[k:=(witness_discharged)]> W1) W2).
  Proof.
    intros LUO INV1 W2 WSStep INV2.
    apply not_elem_of_dom in LUO.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    symmetry in H.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    rename y into w. destruct w; try done. symmetry in H1.
    split.
    { apply not_elem_of_dom. auto. }
    inv WSStep. inv H0.
    { apply wits_one_dom in H3. exfalso. apply elem_of_dom_2 in H1. apply not_elem_of_dom in H.
      rewrite H3 in H. set_solver. }
    destruct H3 as (?&?&?&?).
    subst. destruct (decide (k = x)).
    - subst x. rewrite lookup_insert_eq in H1. inv H1. done.
    - rewrite lookup_insert_ne in H1; auto. rewrite H in H1. inv H1.
  Qed.

End owit.

(* Allocation of the initial witness protocol. *)
Lemma owit_alloc `{SI : indexT} {Σ}
  `{!@osatGS.osatGS _ Σ} `{!owitGpreS Σ} :
  ⊢ |==> ∃ _ : owitGS Σ, owit ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=bcredUR) ⊤)) as (γC) "HC";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (OwitG SI _ _ γC).
  rewrite /owit -lock.
  replace (⊤ ∖ gset_to_coPset (dom (∅ : witnesses))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
