From iris.algebra Require Import reservation_map.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Export obligation.
From liveness Require Import ordinal_wfocm bcred.

Module ofuelGS.
  Class ofuelGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OfuelGpreS {
        ofuelGpreS_state : inG Σ (reservation_mapUR bcredUR);
      }.

  Class ofuelGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OfuelG {
        ofuel_inG : ofuelGpreS Σ;
        state_name : gname;
      }.

  Definition ofuelΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR bcredUR)
      ].

  Global Instance subG_ofuelΣ `{SI : indexT} {Σ} : subG ofuelΣ Σ → (ofuelGpreS Σ).
  Proof.
    solve_inG.
  Qed.

End ofuelGS.
Import ofuelGS.

(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances ofuel_inG ofuelGpreS_state.

Definition ofuelS_fuel `{SI : indexT} `{!ofuelGS Σ} (i : obl_id) (a : Ord.t) : iProp Σ :=
  own state_name (reservation_map_data i (credit a)).
Global Typeclasses Opaque ofuelS_fuel.
Global Instance: Params (@ofuelS_fuel) 4 := {}.

Definition ofuelS_bound `{SI : indexT} `{!ofuelGS Σ} (i : obl_id) (a : Ord.t) : iProp Σ :=
  own state_name (reservation_map_data i (credit_bound a)).
Global Typeclasses Opaque ofuelS_bound.
Global Instance: Params (@ofuelS_bound) 4 := {}.

Definition ofuelI `{SI : indexT} {Π : Type} `{!ofuelGS Σ}
  (c : Ord.t) (Ω : obl_states' Π) : iProp Σ :=
  locked
    (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom Ω))) ∗
     [∗ map] i ↦ o ∈ Ω,
       match o with
       | obl_init a =>
           (∃ a', ⌜ (a <= a')%ord ⌝ ∗ ofuelS_fuel i (c × a')%ord)
       | obl_live a =>
           (∃ a', ⌜ (a <= a')%ord ⌝ ∗ ofuelS_fuel i (c × a')%ord)
       | obl_done _ =>
           (⌜ True ⌝)
       end
    )%I.

Section ofuel.
  Context `{SI : indexT} {Π : Type} `{!ofuelGS Σ}.

  Global Instance ofuelS_bound_persistent i a : Persistent (ofuelS_bound i a).
  Proof. rewrite /ofuelS_bound. apply _. Qed.

  Local Infix "/≤" := Ord.le (at level 70).
  Local Infix "/+" := Hessenberg.add (at level 70).
  Local Infix "/<" := Ord.lt (at level 70).
  Local Notation "/0" := Ord.O.

  Lemma ofuelS_fuel_mon i a0 a1 :
    a0 /≤ a1 →
    ofuelS_fuel i a1 ⊢ |==> ofuelS_fuel i a0.
  Proof.
    intros LE. rewrite /ofuelS_fuel. apply own_update.
    apply reservation_map_update. by apply credit_update.
  Qed.

  Lemma ofuelS_fuel_split i a0 a1 :
    ofuelS_fuel i (a0 /+ a1) ⊣⊢ ofuelS_fuel i a0 ∗ ofuelS_fuel i a1.
  Proof.
    rewrite /ofuelS_fuel. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iApply own_op.
      iApply own_mono; [| iFrame]. rewrite reservation_map_data_op. done.
    - iCombine "H1 H2" as "H". iEval (rewrite credit_split). iFrame.
  Qed.

  Lemma ofuelS_fuel_mon_split i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ofuelS_fuel i a2 ⊢ |==> ofuelS_fuel i a0 ∗ ofuelS_fuel i a1.
  Proof.
    intros LE. iIntros "H". iApply ofuelS_fuel_split. iApply ofuelS_fuel_mon; done.
  Qed.

  Lemma ofuelS_bound_mon i a0 a1 :
    a0 /≤ a1 →
    ofuelS_bound i a0 ⊢ |==> ofuelS_bound i a1.
  Proof.
    intros LE. rewrite /ofuelS_bound. apply own_update.
    apply reservation_map_update. by apply cmra_update_included, credit_bound_included.
  Qed.

  Lemma ofuelS_fuel_spend i a0 a1 :
    ofuelS_bound i a0 ∗ ofuelS_fuel i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ ofuelS_bound i a2.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ k, ∃ a2, (k = credit_bound a2) ∧ (a1 /+ a2 /≤ a0))
                (λ k, ∃ a2, (k = reservation_map_data i (credit_bound a2)) ∧ (a1 /+ a2 /≤ a0))
             ).
      { eapply credit_spend. }
      { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplit; done.
  Qed.

  Lemma ofuelS_induction i a P :
    ofuelS_bound i a ∗ □(∃ c, ⌜/0 /< c⌝ ∧ ((ofuelS_fuel i c ==∗ P) ==∗ P)) ⊢ |==> P.
  Proof.
    iIntros "[#Hb (%c & %LTc & #HI)]".
    iStopProof. pattern a. revert a. apply (well_founded_induction WFOCM.lt_wf).
    intros a IND. iIntros "[#Hb #HI]".
    iApply "HI". iIntros "Hc".
    iMod (ofuelS_fuel_spend with "[Hb Hc]") as "(%a' & %LE & #Hb')"; [iFrame; done |].
    iClear "Hb". iApply (IND a'); [| iModIntro; iSplit; done].
    apply WFOCM.lt_exists_left. exists c. split; [auto | by rewrite OCM.add_comm_le ].
  Qed.

  Lemma ofuelI_alloc c (Ω : obl_states' Π) a i :
    (Ω !! i = None) →
    ofuelI c Ω
    ⊢ |==> ofuelI c (<[i:=obl_init a]>Ω) ∗ ofuelS_bound i (c × a)%ord.
  Proof.
    rewrite /ofuelI -!lock. iIntros (LU) "[Htk Hs]".
    pose proof LU as LU'. apply not_elem_of_dom in LU.
    assert (Fresh : {[ i ]} ⊆ (⊤ ∖ gset_to_coPset (dom Ω))).
    { apply elem_of_subseteq_singleton. apply elem_of_difference. split; [set_solver|].
      intros F. apply elem_of_gset_to_coPset in F. done.
    }
    rewrite (reservation_map_token_difference _ _ Fresh). iDestruct "Htk" as "[Htki Htk]".
    assert (New : (⊤ ∖ gset_to_coPset (dom Ω) ∖ {[i]}) = (⊤ ∖ gset_to_coPset ({[i]} ∪ dom Ω))).
    { rewrite difference_difference_l_L. f_equal. rewrite -leibniz_equiv_iff.
      intros x. split; intros IN.
      - apply elem_of_gset_to_coPset. apply elem_of_union in IN. destruct IN.
        + apply elem_of_gset_to_coPset in H. set_solver.
        + set_solver.
      - apply elem_of_union. apply elem_of_gset_to_coPset in IN. apply elem_of_union in IN. destruct IN.
        + set_solver.
        + left. apply elem_of_gset_to_coPset. done.
    }
    iMod (own_update with "Htki") as "Hi".
    { apply (reservation_map_alloc _ i (credit_bound (c × a)%ord ⋅ credit (c × a)%ord));
        [set_solver| apply credit_bound_credit_valid_eq].
    }
    iAssert (ofuelS_bound i (c × a)%ord ∗ ofuelS_fuel i (c × a)%ord)%I with "[Hi]" as "[Hb Hf]".
    { rewrite /ofuelS_bound /ofuelS_fuel -own_op -reservation_map_data_op. done. }
    iModIntro. iFrame. iSplitL "Htk".
    - rewrite New dom_insert_L. done.
    - iApply big_sepM_insert; [auto|]. iFrame. done.
  Qed.

  Lemma ofuelI_progress_one c (Ω : obl_states' Π) i o1 o2 :
    (Ω !! i = Some (obl_live o1)) →
    (o2 < o1)%ord →
    ofuelI c Ω
    ⊢ |==> ofuelI c (<[i:=obl_live o2]>Ω) ∗ ofuelS_fuel i c.
  Proof.
    intros LU LT. rewrite /ofuelI -!lock. iIntros "(Htk & Hs)".
    rewrite (dom_insert_lookup_L Ω i (obl_live o2)); [iFrame | done].
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&Hf)".
    apply ord_lt_one in LT.
    iMod (ofuelS_fuel_mon_split _ (c × o2)%ord c with "Hf") as "[Hf Hf']".
    { rewrite Hessenberg.add_comm -Jacobsthal.mult_S.
      eapply Jacobsthal.le_mult_r. etrans; [|eauto].
      by rewrite Hessenberg.add_S_r Hessenberg.add_O_r in LT.
    }
    iFrame. iPoseProof (big_sepM_insert _ (delete i Ω) i (obl_live o2) with "[Hs Hf]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists o2. by iFrame. }
    iModIntro. rewrite insert_delete_insert. iFrame.
  Qed.

  Lemma ofuelI_done_one c (Ω : obl_states' Π) i o P :
    (Ω !! i = Some o) →
    ofuelI c Ω
    ⊢ |==> ofuelI c (<[i:=obl_done P]>Ω).
  Proof.
    intros LU. rewrite /ofuelI -!lock. iIntros "(Htk & Hs)".
    rewrite (dom_insert_lookup_L Ω i (obl_done P)); [iFrame | done].
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iPoseProof (big_sepM_insert _ (delete i Ω) i (obl_done P) with "[Hs]") as "Hs".
    { apply lookup_delete. }
    { iFrame. }
    iModIntro. rewrite insert_delete_insert. iFrame.
  Qed.

End ofuel.

(* Allocation of an initial obligation fuel variant. *)
Lemma ofuel_alloc `{SI : indexT} {Π : Type} `{!ofuelGpreS Σ} c : ⊢ |==> ∃ _ : ofuelGS Σ, ofuelI (Π:=Π) c ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (OfuelG SI _ _ γS).
  rewrite /ofuelI -lock.
  rewrite big_opM_empty. replace (⊤ ∖ gset_to_coPset (dom ∅)) with (⊤ : coPset); [by iFrame|].
  rewrite -leibniz_equiv_iff. intros x. split; intros IN.
  - apply elem_of_difference. split; [set_solver|].
    intros F. apply elem_of_gset_to_coPset in F. set_solver.
  - set_solver.
Qed.
