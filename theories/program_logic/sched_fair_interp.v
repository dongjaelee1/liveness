From iris.algebra Require Import gmap mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Import bank language.

Module schedfairGS.
  Class schedfairGpreS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    SchedfairGpreS {
        schedfairGpreS_state : inG Σ (gmapUR thread_id (prodUR bankUR mono_natUR));
      }.

  Class schedfairGS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    SchedfairG {
        schedfair_inG : schedfairGpreS Σ;
        state_name : gname;
      }.

  Definition schedfairΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} : gFunctors :=
    #[GFunctor (gmapTRF thread_id (prodTRF bankUR mono_natUR))
      ].

  Global Instance subG_schedfairΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} {Σ} : subG schedfairΣ Σ → (schedfairGpreS Σ).
  Proof.
    solve_inG.
  Qed.

End schedfairGS.
Import schedfairGS.

(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances schedfair_inG schedfairGpreS_state.

Definition sfS_exec `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (ε, ●MN{#q} 0) ]} : gmap _ _).
Global Typeclasses Opaque sfS_exec.
Global Instance: Params (@sfS_exec) 9 := {}.

Definition sfS_term_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) : iProp Σ :=
  own state_name ({[ i := (ε : bankUR, ●MN 1) ]} : gmap _ _).
Global Typeclasses Opaque sfS_term_auth.
Global Instance: Params (@sfS_term_auth) 9 := {}.

Definition sfS_term `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) : iProp Σ :=
  own state_name ({[ i := (ε : bankUR, ◯MN 1) ]} : gmap _ _).
Global Typeclasses Opaque sfS_term.
Global Instance: Params (@sfS_term) 9 := {}.

Definition sfS_fuel_bound `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (a : A) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (debt a q, ε) ]} : gmap _ _).
Global Typeclasses Opaque sfS_fuel_bound.
Global Instance: Params (@sfS_fuel_bound) 9 := {}.

Definition sfS_fuel_credit `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (a : A) : iProp Σ :=
  own state_name ({[ i := (cash a, ε) ]} : gmap _ _).
Global Typeclasses Opaque sfS_fuel_credit.
Global Instance: Params (@sfS_fuel_credit) 9 := {}.

Definition schedfairI `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ}
  (ϕ : gmap thread_id (option A)) : iProp Σ :=
  locked
    ([∗ map] i ↦ oF ∈ ϕ,
       match oF with
       | Some f =>
           (∃ f', ⌜leR f f'⌝ ∗ sfS_fuel_credit i f' ∗ sfS_exec i (1/2)%Qp)
       | None =>
           (∃ f', sfS_fuel_bound i f' 1 ∗ sfS_term_auth i)
       end
    )%I.

Section sfi.
  Context `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ}.

  Global Instance sfS_term_persistent i : Persistent (sfS_term i).
  Proof. rewrite /sfS_term. apply _. Qed.

  Local Infix "/=" := OrderedCM.eq (at level 70).
  Local Infix "/≤" := leR (at level 70).
  Local Infix "/+" := addO (at level 70).
  Local Infix "/<" := ltR (at level 70).
  Local Infix "/∧" := OrderedCM.meet (at level 70).
  Local Notation "/0" := OrderedCM.unit.

  Lemma sfS_exec_term_false i q :
    sfS_exec i q ∗ sfS_term i ⊢ False.
  Proof.
    rewrite /sfS_exec /sfS_term. iIntros "[Hi Ha]".
    iCombine "Hi Ha" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro.
    apply singleton_valid in V. rewrite pair_valid in V. destruct V as [_ V].
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma sfS_term_auth_term i :
    sfS_term_auth i ⊢ sfS_term i.
  Proof.
    rewrite /sfS_term_auth /sfS_term. apply own_mono.
    apply singleton_included, option_included. right.
    do 2 eexists. split; [eauto|]. split; [eauto|]. right.
    apply prod_included. simpl. split; [done | apply mono_nat_included].
  Qed.

  Lemma sfS_exec_to_term i :
    sfS_exec i 1 ⊢ |==> sfS_term_auth i.
  Proof.
    rewrite /sfS_exec /sfS_term_auth. apply own_update.
    apply singleton_update, prod_update; [done|].
    simpl. apply mono_nat_update. auto.
  Qed.

  Lemma sfS_fuel_credit_eq i a0 a1 :
    a0 /= a1 →
    sfS_fuel_credit i a0 = sfS_fuel_credit i a1.
  Proof.
    intros EQ. rewrite /sfS_fuel_credit. by erewrite cash_eq.
  Qed.

  Lemma sfS_fuel_credit_mon i a0 a1 :
    a0 /≤ a1 →
    sfS_fuel_credit i a1 ⊢ |==> sfS_fuel_credit i a0.
  Proof.
    intros LE. rewrite /sfS_fuel_credit. apply own_update.
    apply singleton_update.
    apply prod_update; [by apply cash_update | reflexivity].
  Qed.

  Lemma sfS_fuel_credit_add i a0 a1 :
    sfS_fuel_credit i (a0 /+ a1) ⊣⊢ sfS_fuel_credit i a0 ∗ sfS_fuel_credit i a1.
  Proof.
    rewrite /sfS_fuel_credit. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -cash_add) in "H". iApply own_op.
      iApply own_mono; [| iFrame]. rewrite singleton_op. done.
    - iCombine "H1 H2" as "H". iEval (rewrite -cash_add). iFrame.
  Qed.

  Lemma sfS_fuel_credit_mon_add i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    sfS_fuel_credit i a2 ⊢ |==> sfS_fuel_credit i a0 ∗ sfS_fuel_credit i a1.
  Proof.
    intros LE. iIntros "H". iApply sfS_fuel_credit_add. by iApply sfS_fuel_credit_mon.
  Qed.

  Lemma sfS_fuel_bound_eq i a0 a1 q :
    a0 /= a1 →
    sfS_fuel_bound i a0 q = sfS_fuel_bound i a1 q.
  Proof.
    intros EQ. rewrite /sfS_fuel_bound. by erewrite debt_eq.
  Qed.

  Lemma sfS_fuel_bound_mon i a0 a1 q:
    a0 /≤ a1 →
    sfS_fuel_bound i a0 q ⊢ |==> sfS_fuel_bound i a1 q.
  Proof.
    intros LE. rewrite /sfS_fuel_bound. apply own_update.
    apply singleton_update.
    apply prod_update; [by apply debt_update | reflexivity].
  Qed.

  Lemma sfS_fuel_bound_add i a0 a1 q0 q1 :
    sfS_fuel_bound i (a0 /∧ a1) (q0 + q1) ⊣⊢ sfS_fuel_bound i a0 q0 ∗ sfS_fuel_bound i a1 q1.
  Proof.
    rewrite /sfS_fuel_bound. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -debt_add) in "H". iApply own_op.
      iApply own_mono; [| iFrame]. rewrite singleton_op. done.
    - iCombine "H1 H2" as "H". iEval (rewrite -debt_add). iFrame.
  Qed.

  Lemma sfS_fuel_pay i a0 a1 q :
    sfS_fuel_bound i a0 q ∗ sfS_fuel_credit i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ sfS_fuel_bound i a2 q.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite singleton_op -!pair_op !left_id.
      eapply (singleton_updateP
                (λ k, ∃ a2, (k = (debt a2 q, ε)) ∧ (a1 /+ a2 /≤ a0))
                (λ k, ∃ a2, (k = {[i := (debt a2 q, ε)]}) ∧ (a1 /+ a2 /≤ a0))
             ).
      { eapply (prod_updateP (λ k, ∃ a2, (k = (debt a2 q)) ∧ (a1 /+ a2 /≤ a0)) (eq ε)).
        { eapply debt_pay. }
        { eapply cmra_update_updateP. reflexivity. }
        { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
      }
      { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplit; done.
  Qed.

  Lemma sfS_fuel_owe i a0 a1 :
    sfS_fuel_bound i a0 1 ⊢ |==> sfS_fuel_bound i (a0 /+ a1) 1 ∗ sfS_fuel_credit i a1.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_update with "H") as "H".
    { eapply (singleton_update i _ (debt (a0 /+ a1) 1 ⋅ cash a1, ε)), prod_update; [apply debt_owe | reflexivity]. }
    iModIntro. by rewrite singleton_op.
  Qed.

  TODO



  Lemma oblG_elem_unfold i : oblG_elem i ⊢ ∃ P R, oblG_goal i P R.
  Proof. done. Qed.

  Lemma osat_oblG_elem i O :
    osat O ∗ oblG_elem i ⊢ ⌜i ∈ dom O⌝.
  Proof.
    rewrite /osat -!lock. iIntros "(Ho & He)". iPoseProof (oblG_elem_unfold with "He") as "(%&%&Hg)".
    iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iPoseProof (oblG_goal_lookup with "[Hoa Hg]") as "(%&%&%&%&%&_)"; [iFrame; done |].
    iPureIntro. subst O. apply elem_of_dom_2 in H. set_solver.
  Qed.

  Lemma osat_obl_is_init O i q :
    osat O ∗ oblG_elem i ∗ sfS_exec i q
    ⊢ ∃ a, ⌜O !! i = Some (obl_init a)⌝.
  Proof.
    iIntros "(Ho & #He & Hi)".
    iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [by iFrame |].
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (o, Q)).
    { subst O. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    destruct o.
    - iExists a. done.
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & ACT & _)".
      iPoseProof (sfS_exec_term_false with "[Hi ACT]") as "%F"; [iFrame | done].
      iPoseProof (sfS_term_auth_term with "ACT") as "#D". done.
    - iExFalso. subst. destruct Q. iDestruct "LU" as "(_ & _ & ACT & _)".
      iPoseProof (sfS_exec_term_false with "[Hi ACT]") as "%F"; [iFrame | done].
      iPoseProof (sfS_term_auth_term with "ACT") as "#D". done.
  Qed.

  Lemma osat_obl_is_live O i q :
    osat O ∗ oblG_elem i ∗ sfS_term i ∗ sfS_live i q
    ⊢ ∃ a, ⌜O !! i = Some (obl_live a)⌝.
  Proof.
    iIntros "(Ho & #He & #Ha & Hl)".
    iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [by iFrame |].
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (o, Q)).
    { subst O. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    destruct o.
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & EXEC & _)".
      iPoseProof (sfS_exec_term_false with "[EXEC Ha]") as "%F"; [iFrame; done | done].
    - iExists a. done.
    - iExFalso. subst. destruct Q. iDestruct "LU" as "(_ & _ & _ & DONE)".
      iPoseProof (sfS_live_done_false with "[Hl DONE]") as "%F"; [iFrame | done].
      iPoseProof (sfS_done_auth_done with "DONE") as "#D". done.
  Qed.

  Lemma osat_obl_is_done O i P R :
    osat O ∗ oblG_goal i P R ∗ sfS_done i
    ⊢ ⌜O !! i = Some (obl_done P)⌝.
  Proof.
    iIntros "(Ho & #He & #Hd)".
    iPoseProof (osat_oblG_elem with "[Ho]") as "%Hin"; [rewrite /oblG_elem; iFrame; eauto |].
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (o, Q)).
    { subst O. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    destruct o.
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & _ & LIVE)".
      iPoseProof (sfS_live_done_false with "[LIVE Hd]") as "%F"; [iFrame; done | done].
    - iExFalso. subst. iDestruct "LU" as "(% & _ & _ & _ & LIVE)".
      iPoseProof (sfS_live_done_false with "[LIVE Hd]") as "%F"; [iFrame; done | done].
    - iPoseProof (oblG_goal_lookup with "[Hoa]") as "(%&%&%&%&%&_)"; [iFrame; done |].
      destruct Q. iDestruct "LU" as "[% _]". iPureIntro. subst.
      rewrite LU2 in H. inv H. rewrite LU. auto.
  Qed.

  Lemma obl_alloc O a P R :
    osat O
    ⊢ |==> ∃ i, ⌜O !! i = None⌝ ∗ osat (<[i:=obl_init a]>O) ∗
                oblG_goal i P R ∗ sfS_exec i 1%Qp ∗ sfS_live i 1 ∗ sfS_credit i a.
  Proof.
    rewrite /osat -!lock.
    iIntros "Ho". iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iMod (@own_unit _ _ _ osatGpreS_state state_name) as "HU".
    iMod ((@own_updateP _ _ _ osatGpreS_state _ state_name) with "HU") as "H".
    { apply (alloc_updateP_cofinite' ∅ ((credit_bound a ⋅ credit a : bcred (H:=WFOrderedCM.orderedCM)), ●MN 0, ●MN 0) (dom O)).
      rewrite pair_valid. split; [| apply mono_nat_auth_valid].
      rewrite pair_valid. split; [| apply mono_nat_auth_valid].
      apply credit_bound_credit_valid_eq.
    }
    iSimpl. iDestruct "H" as (a' (i & NIN & Ha' & _)) "H". rewrite insert_empty in Ha'. subst a'.
    iAssert (sfS_bound i a ∗ sfS_credit i a ∗ sfS_exec i 1 ∗ sfS_exec i 1 ∗ sfS_live i 1 ∗ sfS_live i 1)%I
      with "[H]" as "(Sb & Sc & Si1 & Si2 & Sl1 & Sl2)".
    { rewrite /sfS_bound /sfS_credit /sfS_exec /sfS_live -!own_op !singleton_op -!pair_op. iSimpl.
      iApply own_mono; [|done].
      apply singleton_included, option_included. right. do 2 eexists. do 2 split; [eauto|].
      left. rewrite !left_id !right_id. rewrite -!mono_nat_auth_dfrac_op dfrac_op_own Qp.half_half.
      done.
    }
    iMod (own_update with "Hoa") as "Hoa".
    { eapply (gmap_view_alloc _ i DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)); [| done | done].
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; [done | set_solver].
    }
    iDestruct "Hoa" as "[Hoa #Hg]".
    iModIntro. iExists i. iFrame. rewrite -!lock. iSplitR.
    { iPureIntro. subst O. apply not_elem_of_dom_1. set_solver. }
    iSplit; [|done].
    { iClear "Hg". iExists (<[i:=(obl_init a, (P, R))]>Obls). iSplit.
      { iPureIntro. subst O. by rewrite fmap_insert. }
      iSplitL "Hoa".
      { iEval (rewrite !fmap_insert). iFrame. }
      { iApply big_sepM_insert.
        { subst O. apply not_elem_of_dom_1. set_solver. }
        iFrame. done.
      }
    }
  Qed.

  Lemma osat_step_one_obl_live_live O i a c :
    (O !! i = Some (obl_live a)) →
    (/0 /< c) →
    osat O ∗ sfS_credit i c
    ⊢ |==> ∃ o, osat (<[i:=o]> O) ∗ ∀ s, ⌜obl_state_step s (obl_live a) o⌝.
  Proof.
    intros LU Hc. iIntros "(Ho & CR)".
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    assert (LU2 : exists Q, Obls !! i = Some (obl_live a, Q)).
    { subst O. apply lookup_fmap_Some in LU. destruct LU as ((t&Q)&EQ&LU).
      simpl in *. subst t. eauto.
    }
    destruct LU2 as (Q&LU2).
    iPoseProof (big_sepM_delete with "Hom") as "[LU Hom]"; [eapply LU2 |].
    iDestruct "LU" as "(%a' & %LE & BND & ACTa & LIVE)".
    iPoseProof (sfS_credit_spend with "[BND CR]") as ">(%&%&BND)"; [by iFrame |].
    assert (LT : a2 /< a).
    { apply WFOrderedCM.lt_exists_right. exists c. split; [auto | etransitivity; eauto]. }
    iPoseProof ((big_sepM_insert _ (delete i Obls) i (obl_live a2, Q))  with "[Hom ACTa LIVE BND]") as "Hom".
    { apply lookup_delete. }
    { iFrame. iExists a2. iFrame. done. }
    iModIntro. iFrame. iExists (obl_live a2). iSplit; [|done].
    assert (snd <$> Obls = (snd <$> <[i:=(obl_live a2, Q)]> (delete i Obls))).
    { rewrite fmap_insert fmap_delete. simpl. symmetry. apply insert_delete.
      rewrite lookup_fmap. rewrite LU2. done.
    }
    rewrite -lock. iExists _. iFrame. iSplit; [|by rewrite -!H0].
    { iPureIntro. rewrite fmap_insert fmap_delete.
      rewrite -HO. simpl. symmetry. apply insert_delete_insert.
    }
  Qed.

  Lemma osat_step_one_obl_live_done O i P R :
    osat O ∗ sfS_term i ∗ sfS_live i 1 ∗ oblG_goal i P R ∗ ▷ R
    ⊢ |==> osat (<[i:=obl_done P]>O) ∗ sfS_done i.
  Proof.
    iIntros "(Ho & #Ha & Hl & #Hg & R)".
    iPoseProof (osat_obl_is_live with "[Ho Hl]") as "[% %Hlive]".
    { iFrame. rewrite /oblG_elem. iSplit; [|done]. by iExists P, R. }
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iDestruct (oblG_goal_lookup Obls i P with "[Hoa]") as (o P' R' IN HP') "#HPQ"; [iFrame; done| subst].
    iDestruct (big_sepM_delete _ _ i _ IN with "Hom") as "[Hc Hom]".
    assert (o = obl_live a).
    { rewrite lookup_fmap in Hlive. rewrite IN in Hlive. inv Hlive. done. }
    subst o.
    iDestruct "Hc" as "(%&_&_&Haa&Hl2)". iMod (sfS_live_to_done with "[$]") as "Hda".
    iPoseProof (sfS_done_auth_done with "[$]") as "#DONE".
    iModIntro. iSplitL; [|done]. iExists (<[i := (obl_done P, (P, R'))]>Obls). iSplit.
    { iPureIntro. by rewrite fmap_insert. }
    iSplitL "Hoa".
    { rewrite fmap_insert insert_id; [iFrame|]. rewrite lookup_fmap IN. done. }
    iApply (big_sepM_delete _ _ i); [apply lookup_insert |].
    iFrame. iSplitL "R".
    { iSplit; [done|]. iNext. by iRewrite "HPQ". }
    rewrite delete_insert_delete. iFrame.
  Qed.

  Lemma osat_done_open O i P R :
    osat O ∗ sfS_done i ∗ oblG_goal i P R
    ⊢ (▷ R) ∗ (▷ R -∗ osat O).
  Proof.
    iIntros "(Ho & #Hd & #Hg)".
    iPoseProof (osat_obl_is_done with "[Ho]") as "%Hdone"; [iFrame; eauto|].
    rewrite /osat -!lock. iDestruct "Ho" as (Obls) "(%HO & Hoa & Hom)".
    iDestruct (oblG_goal_lookup Obls i P with "[Hoa]") as (o P' R' IN HP') "#HPQ"; [iFrame; done|].
    iDestruct (big_sepM_delete _ _ i _ IN with "Hom") as "[Hc Hom]".
    subst. assert (o = obl_done P).
    { rewrite lookup_fmap IN in Hdone. by inv Hdone. }
    subst. iDestruct "Hc" as "(HP&HQ&Haa&Hda)". iSplitL "HQ".
    { iNext. by iRewrite "HPQ" in "HQ". }
    { iIntros "HR". iExists Obls. iSplit; [iPureIntro; done |].
      iFrame. iApply (big_sepM_delete _ _ i); [eauto |].
      iFrame. iNext. by iRewrite "HPQ".
    }
  Qed.

  Lemma osat_done_open_pers O i P R :
    Persistent R →
    osat O ∗ sfS_done i ∗ oblG_goal i P R
    ⊢ osat O ∗ ▷ R.
  Proof.
    iIntros (PP) "H". iPoseProof (osat_done_open with "H") as "[#HP Ho]".
    iSplitL; [|done]. iApply "Ho". done.
  Qed.

End sfi.

(* Allocation of an initial obligation protocol. *)
Lemma osat_alloc `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{obl_ps} `{!osatGpreS Σ} : ⊢ |==> ∃ _ : osatGS Σ, osat ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γG) "HG";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γS) "HS";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OsatG SI _ _ _ _ WF _ _ _ γG γS).
  rewrite /osat -lock.
  iExists ∅. rewrite !fmap_empty big_opM_empty. by iFrame.
Qed.
