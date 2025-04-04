From iris.algebra Require Import reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Import bank language.

Module schedfairGS.
  (* We assume thread_id = positive. To generalize, we need a general version of reservation_map. *)
  Class schedfairGpreS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    SchedfairGpreS {
        schedfairGpreS_state : inG Σ (reservation_mapUR (prodUR bankUR mono_natUR));
      }.

  Class schedfairGS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    SchedfairG {
        schedfair_inG : schedfairGpreS Σ;
        state_name : gname;
      }.

  (* Do we need reservation_map version of gmapTRF? Why do we even need Functor? *)
  Definition schedfairΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} : gFunctors :=
    #[GFunctor (reservation_mapUR (prodUR bankUR mono_natUR))
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
  own state_name (reservation_map_data i (ε, ●MN{#q} 0)).
Global Typeclasses Opaque sfS_exec.
Global Instance: Params (@sfS_exec) 9 := {}.

Definition sfS_term_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) : iProp Σ :=
  own state_name (reservation_map_data i (ε, ●MN 1)).
Global Typeclasses Opaque sfS_term_auth.
Global Instance: Params (@sfS_term_auth) 9 := {}.

Definition sfS_term `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) : iProp Σ :=
  own state_name (reservation_map_data i (ε, ◯MN 1)).
Global Typeclasses Opaque sfS_term.
Global Instance: Params (@sfS_term) 9 := {}.

Definition sfS_fuel_bound `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (a : A) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data i (debt a q, ε)).
Global Typeclasses Opaque sfS_fuel_bound.
Global Instance: Params (@sfS_fuel_bound) 9 := {}.

Definition sfS_fuel_credit `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (a : A) : iProp Σ :=
  own state_name (reservation_map_data i (cash a, ε)).
Global Typeclasses Opaque sfS_fuel_credit.
Global Instance: Params (@sfS_fuel_credit) 9 := {}.

Definition schedfairI `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ}
  (ϕ : gmap thread_id (option A)) : iProp Σ :=
  locked
    (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom ϕ))) ∗
     [∗ map] i ↦ oF ∈ ϕ,
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
    apply reservation_map_data_valid in V. rewrite pair_valid in V. destruct V as [_ V].
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma sfS_term_auth_term i :
    sfS_term_auth i ⊢ sfS_term i.
  Proof.
    rewrite /sfS_term_auth /sfS_term. apply own_mono.
    apply reservation_map_data_mono, prod_included.
    simpl. split; [done | apply mono_nat_included].
  Qed.

  Lemma sfS_exec_to_term i :
    sfS_exec i 1 ⊢ |==> sfS_term_auth i.
  Proof.
    rewrite /sfS_exec /sfS_term_auth. apply own_update.
    apply reservation_map_update, prod_update; [done|].
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
    apply reservation_map_update.
    apply prod_update; [by apply cash_update | reflexivity].
  Qed.

  Lemma sfS_fuel_credit_add i a0 a1 :
    sfS_fuel_credit i (a0 /+ a1) ⊣⊢ sfS_fuel_credit i a0 ∗ sfS_fuel_credit i a1.
  Proof.
    rewrite /sfS_fuel_credit. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -cash_add) in "H". iApply own_op.
      iApply own_mono; [| iFrame]. rewrite -reservation_map_data_op. done.
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
    apply reservation_map_update.
    apply prod_update; [by apply debt_update | reflexivity].
  Qed.

  Lemma sfS_fuel_bound_add i a0 a1 q0 q1 :
    sfS_fuel_bound i (a0 /∧ a1) (q0 + q1) ⊣⊢ sfS_fuel_bound i a0 q0 ∗ sfS_fuel_bound i a1 q1.
  Proof.
    rewrite /sfS_fuel_bound. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -debt_add) in "H". iApply own_op.
      iApply own_mono; [| iFrame]. rewrite -reservation_map_data_op. done.
    - iCombine "H1 H2" as "H". iEval (rewrite -debt_add). iFrame.
  Qed.

  Lemma sfS_fuel_pay i a0 a1 q :
    sfS_fuel_bound i a0 q ∗ sfS_fuel_credit i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ sfS_fuel_bound i a2 q.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -reservation_map_data_op -!pair_op !left_id.
      eapply (reservation_map_updateP
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
    { eapply (reservation_map_update i _ (debt (a0 /+ a1) 1 ⋅ cash a1, ε)), prod_update; [apply debt_owe | reflexivity]. }
    iModIntro. by rewrite -reservation_map_data_op.
  Qed.

  Lemma schedfairI_thread_is_exec ϕ i oF q :
    (ϕ !! i = Some oF) →
    schedfairI ϕ ∗ sfS_exec i q
    ⊢ ∃ f, ⌜oF = Some f⌝.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU) "([Htk Hs] & He)".
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eapply LU |].
    destruct oF.
    - by iExists a.
    - iExFalso. iDestruct "LU" as "(%&_&Hta)". iPoseProof (sfS_term_auth_term with "Hta") as "#Ht".
      iDestruct (sfS_exec_term_false with "[He]") as "%F"; [by iFrame | done].
  Qed.

  Lemma schedfairI_fork ϕ i f :
    (ϕ !! i = None) →
    schedfairI ϕ
    ⊢ |==> schedfairI (<[i:=Some f]>ϕ) ∗
           sfS_exec i (1/2) ∗ sfS_fuel_bound i f 1.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU) "[Htk Hs]".
    pose proof LU as LU'. apply not_elem_of_dom in LU.
    assert (Fresh : {[ i ]} ⊆ (⊤ ∖ gset_to_coPset (dom ϕ))).
    { apply elem_of_subseteq_singleton. apply elem_of_difference. split; [set_solver|].
      intros F. apply elem_of_gset_to_coPset in F. done.
    }
    rewrite (reservation_map_token_difference _ _ Fresh). iDestruct "Htk" as "[Htki Htk]".
    assert (New : (⊤ ∖ gset_to_coPset (dom ϕ) ∖ {[i]}) = (⊤ ∖ gset_to_coPset ({[i]} ∪ dom ϕ))).
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
    { apply (reservation_map_alloc _ i (debt /0 1, ●MN 0)); [set_solver|].
      rewrite pair_valid. split; [by apply bank_valid_debt | apply mono_nat_auth_valid].
    }
    iAssert (sfS_fuel_bound i /0 1 ∗ sfS_exec i (1/2) ∗ sfS_exec i (1/2))%I with "[Hi]" as "(Hfb&He1&He2)".
    { rewrite /sfS_fuel_bound /sfS_exec. do 2 rewrite -own_op. rewrite -!reservation_map_data_op.
      rewrite -!pair_op. simpl. rewrite -mono_nat_auth_dfrac_op dfrac_op_own Qp.div_2.
      by rewrite !left_id !right_id_L.
    }
    iMod (sfS_fuel_owe i _ f with "Hfb") as "[Hfb Hfc]". rewrite (sfS_fuel_bound_eq _ _ f); [| by rewrite left_id].
    iModIntro. iFrame. iSplitL "Htk".
    - rewrite New dom_insert_L. done.
    - iApply big_sepM_insert; [auto|]. iFrame. done.
  Qed.

  Lemma schedfairI_decr_one ϕ i f f' :
    (ϕ !! i = Some (Some f)) →
    (f' /< f) →
    schedfairI ϕ
    ⊢ |==> schedfairI (<[i:=Some f']>ϕ) ∗ ∃ c, ⌜/0 /< c⌝ ∗ sfS_fuel_credit i c.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU Hf) "[Htk Hs]".
    rewrite (dom_insert_lookup_L ϕ i (Some f')); [iFrame | done].
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&Hfc&He)".
    assert (∃ f1, (/0 /< f1) ∧ (f' /+ f1) /≤ f'0).
    { apply WFOrderedCM.lt_exists_left in Hf. destruct Hf as (?&?&?). exists x. split; [auto | etransitivity; eauto]. }
    destruct H0 as (f1&Hpos&Hf1). 
    iMod (sfS_fuel_credit_mon_add _ _ _ _ Hf1 with "Hfc") as "[Hfc1 Hfc2]".
    iPoseProof (big_sepM_insert _ (delete i ϕ) i (Some f') with "[Hs He Hfc1]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists f'. iFrame. done. }
    iModIntro. rewrite insert_delete_insert. iFrame. done.
  Qed.

  Lemma schedfairI_reset_one ϕ i f f0 f' :
    (ϕ !! i = Some (Some f)) →
    schedfairI ϕ ∗ sfS_fuel_bound i f0 1
    ⊢ |==> schedfairI (<[i:=Some f']>ϕ) ∗ sfS_fuel_bound i (f0 /+ f') 1.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU) "[[Htk Hs] Hfb]".
    rewrite dom_insert_lookup_L; [iFrame|done].
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&_&He)".
    iMod (sfS_fuel_owe i _ f' with "Hfb") as "[Hfb Hfc]". iFrame.
    iPoseProof (big_sepM_insert _ (delete i ϕ) i (Some f') with "[Hs He Hfc]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists f'. iFrame. done. }
    iModIntro. rewrite insert_delete_insert. iFrame.
  Qed.

  Lemma schedfairI_term_one ϕ i oF f :
    (ϕ !! i = Some oF) →
    schedfairI ϕ ∗ sfS_exec i (1/2) ∗ sfS_fuel_bound i f 1
    ⊢ |==> schedfairI (<[i:=None]>ϕ) ∗ sfS_term i.
  Proof.
    iIntros (LU) "(Hs&He&Hfb)". iDestruct (schedfairI_thread_is_exec _ _ _ _ LU with "[Hs He]") as "[% %]"; [iFrame|subst].
    rewrite /schedfairI -!lock. iDestruct "Hs" as "[Htk Hs]".
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&Hfc&He2)".
    iMod (sfS_exec_to_term with "[He He2]") as "Hta".
    { rewrite /sfS_exec. iPoseProof (own_op with "[He He2]") as "He"; [iFrame|].
      by rewrite -reservation_map_data_op -pair_op -mono_nat_auth_dfrac_op dfrac_op_own Qp.div_2 left_id.
    }
    iPoseProof (sfS_term_auth_term with "Hta") as "#Hterm".
    iPoseProof (big_sepM_insert _ (delete i ϕ) i None with "[Hs Hta Hfb]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists f. iFrame. }
    iModIntro. rewrite insert_delete_insert. iFrame. iSplit; [by rewrite dom_insert_lookup_L | done].
  Qed.

End sfi.

(* Allocation of an initial obligation protocol. *)
Lemma schedfairI_alloc `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!schedfairGpreS Σ} : ⊢ |==> ∃ _ : schedfairGS Σ, schedfairI ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (SchedfairG SI _ _ _ _ WF _ _ γS).
  rewrite /schedfairI -lock.
  rewrite big_opM_empty. replace (⊤ ∖ gset_to_coPset (dom ∅)) with (⊤ : coPset); [by iFrame|].
  rewrite -leibniz_equiv_iff. intros x. split; intros IN.
  - apply elem_of_difference. split; [set_solver|].
    intros F. apply elem_of_gset_to_coPset in F. set_solver.
  - set_solver.
Qed.
