From iris.algebra Require Import functions reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Import bank language.

Module schedfairGS.

  Class schedfairGpreS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    SchedfairGpreS {
        schedfairGpreS_state : inG Σ (discrete_funUR (λ (k : thread_id), (prodUR bankUR mono_natUR)));
      }.

  Class schedfairGS `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} (Σ : gFunctors) : Set :=
    SchedfairG {
        schedfair_inG : schedfairGpreS Σ;
        state_name : gname;
      }.

  (* Do we need discrete_fun version of gmapTRF? Why do we even need Functor? *)
  Definition schedfairΣ `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} : gFunctors :=
    #[GFunctor (discrete_funUR (λ (k : thread_id), prodUR bankUR mono_natUR))
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
  own state_name (discrete_fun_singleton i (ε, ●MN{#q} 0)).
Global Typeclasses Opaque sfS_exec.
Global Instance: Params (@sfS_exec) 9 := {}.

Definition sfS_term_auth `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) : iProp Σ :=
  own state_name (discrete_fun_singleton i (ε, ●MN 1)).
Global Typeclasses Opaque sfS_term_auth.
Global Instance: Params (@sfS_term_auth) 9 := {}.

Definition sfS_term `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) : iProp Σ :=
  own state_name (discrete_fun_singleton i (ε, ◯MN 1)).
Global Typeclasses Opaque sfS_term.
Global Instance: Params (@sfS_term) 9 := {}.

Definition sfS_fuel_bound `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (a : A) (q : Qp) : iProp Σ :=
  own state_name (discrete_fun_singleton i (debt a q, ε)).
Global Typeclasses Opaque sfS_fuel_bound.
Global Instance: Params (@sfS_fuel_bound) 9 := {}.

Definition sfS_fuel_credit `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ} (i : thread_id) (a : A) : iProp Σ :=
  own state_name (discrete_fun_singleton i (cash a, ε)).
Global Typeclasses Opaque sfS_fuel_credit.
Global Instance: Params (@sfS_fuel_credit) 9 := {}.

Definition schedfairI `{SI : indexT} `{WFOrderedCM.t A leR addO ltR} `{!schedfairGS Σ}
  (δ : gmap thread_id (option A)) : iProp Σ :=
  locked
    (∃ a, own state_name ((λ k, if (decide (k ∈ dom δ)) then ε else (debt a 1, ●MN 0)) : discrete_fun _) ∗
     [∗ map] i ↦ oF ∈ δ,
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
    iCombine "Hi Ha" as "V". rewrite discrete_fun_singleton_op.
    iPoseProof (own_valid with "V") as "%V". iPureIntro.
    apply discrete_fun_singleton_valid in V. rewrite pair_valid in V. destruct V as [_ V].
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma sfS_term_auth_term i :
    sfS_term_auth i ⊢ sfS_term i.
  Proof.
    rewrite /sfS_term_auth /sfS_term. apply own_mono.
    exists (discrete_fun_singleton i (ε, ●MN 1)).
    rewrite comm discrete_fun_singleton_op -pair_op. apply discrete_fun_singleton_proper, pair_proper.
    - by rewrite left_id.
    - apply mono_nat_auth_lb_op.
  Qed.

  Lemma sfS_exec_to_term i :
    sfS_exec i 1 ⊢ |==> sfS_term_auth i.
  Proof.
    rewrite /sfS_exec /sfS_term_auth. apply own_update.
    apply discrete_fun_singleton_update, prod_update; [done|].
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
    apply discrete_fun_singleton_update.
    apply prod_update; [by apply cash_update | reflexivity].
  Qed.

  Lemma sfS_fuel_credit_add i a0 a1 :
    sfS_fuel_credit i (a0 /+ a1) ⊣⊢ sfS_fuel_credit i a0 ∗ sfS_fuel_credit i a1.
  Proof.
    rewrite /sfS_fuel_credit -own_op discrete_fun_singleton_op -pair_op cash_add. f_equal.
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
    apply discrete_fun_singleton_update.
    apply prod_update; [by apply debt_update | reflexivity].
  Qed.

  Lemma sfS_fuel_bound_add i a0 a1 q0 q1 :
    sfS_fuel_bound i (a0 /∧ a1) (q0 + q1) ⊣⊢ sfS_fuel_bound i a0 q0 ∗ sfS_fuel_bound i a1 q1.
  Proof.
    rewrite /sfS_fuel_bound -own_op discrete_fun_singleton_op -pair_op debt_add. f_equal.
  Qed.

  Lemma sfS_fuel_pay i a0 a1 q :
    sfS_fuel_bound i a0 q ∗ sfS_fuel_credit i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ sfS_fuel_bound i a2 q.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite discrete_fun_singleton_op -!pair_op.
      eapply (discrete_fun_singleton_updateP' i (λ k, ∃ a2, (k = (debt a2 q, ε)) ∧ (a1 /+ a2 /≤ a0))).
      eapply (prod_updateP (λ k, ∃ a2, (k = (debt a2 q)) ∧ (a1 /+ a2 /≤ a0)) (eq ε)).
      { eapply debt_pay. }
      { eapply cmra_update_updateP. reflexivity. }
      { intros. destruct H as (a2&A0&A1). exists a2. by subst. }
    }
    iSimpl. iDestruct "H" as "((% & % & %a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplit; done.
  Qed.

  Lemma sfS_fuel_owe i a0 a1 :
    sfS_fuel_bound i a0 1 ⊢ |==> sfS_fuel_bound i (a0 /+ a1) 1 ∗ sfS_fuel_credit i a1.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_update with "H") as "H".
    { eapply (discrete_fun_singleton_update i _ (debt (a0 /+ a1) 1 ⋅ cash a1, ε)), prod_update; [apply debt_owe | reflexivity]. }
    iModIntro. by rewrite discrete_fun_singleton_op.
  Qed.

  Lemma schedfairI_thread_is_exec δ i q :
    schedfairI δ ∗ sfS_exec i q
    ⊢ ∃ f, ⌜δ !! i = Some (Some f)⌝.
  Proof.
    rewrite /schedfairI -!lock. iIntros "((% & Htk & Hs) & He)".
    iAssert (∃ oF, ⌜δ !! i = Some oF⌝)%I with "[Htk He]" as "[% %LU]".
    { destruct (decide (i ∈ dom δ)).
      { apply elem_of_dom in e. destruct e. iExists x. done. }
      { iExFalso. rewrite /sfS_exec. iCombine "Htk He" as "H". iPoseProof (own_valid with "H") as "V".
        rewrite /discrete_fun_singleton /discrete_fun_insert.
        iPoseProof (discrete_fun_validI with "V") as "%V". iPureIntro.
        specialize (V i). rewrite discrete_fun_lookup_op in V. destruct (decide (i ∈ dom δ)); [done|].
        destruct (decide (i = i)); [|done]. rewrite rew_const -pair_op pair_valid in V. destruct V as [_ V].
        apply mono_nat_auth_dfrac_op_valid in V. destruct V as [V _]. apply dfrac_valid_own_l in V. done.
      }
    }
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eapply LU |].
    destruct oF.
    - by iExists a0.
    - iExFalso. iDestruct "LU" as "(%&_&Hta)". iPoseProof (sfS_term_auth_term with "Hta") as "#Ht".
      iDestruct (sfS_exec_term_false with "[He]") as "%F"; [by iFrame | done].
  Qed.

  Lemma schedfairI_thread_is_term δ i :
    schedfairI δ ∗ sfS_term i
    ⊢ ⌜δ !! i = Some None⌝.
  Proof.
    rewrite /schedfairI -!lock. iIntros "((% & Htk & Hs) & Ht)".
    iAssert (∃ oF, ⌜δ !! i = Some oF⌝)%I with "[Htk Ht]" as "[% %LU]".
    { destruct (decide (i ∈ dom δ)).
      { apply elem_of_dom in e. destruct e. iExists x. done. }
      { iExFalso. rewrite /sfS_term. iCombine "Htk Ht" as "H". iPoseProof (own_valid with "H") as "V".
        rewrite /discrete_fun_singleton /discrete_fun_insert.
        iPoseProof (discrete_fun_validI with "V") as "%V". iPureIntro.
        specialize (V i). rewrite discrete_fun_lookup_op in V. destruct (decide (i ∈ dom δ)); [done|].
        destruct (decide (i = i)); [|done]. rewrite rew_const -pair_op pair_valid in V. destruct V as [_ V].
        apply mono_nat_both_valid in V. lia.
      }
    }
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eapply LU |].
    destruct oF.
    - iExFalso. iDestruct "LU" as "(%&_&_&He)". iPoseProof (sfS_exec_term_false with "[He Ht]") as "%F"; [iFrame|done].
    - done.
  Qed.

  Lemma schedfairI_reserved_fork (S : gset _) (i : thread_id) a :
    (i ∉ S) →
    own state_name ((λ k : thread_id, if decide (k ∈ S) then ε else (debt a 1, ●MN 0)) : discrete_fun _)
    ⊢ (own state_name ((λ k : thread_id, if decide (k ∈ {[i]} ∪ S) then ε else (debt a 1, ●MN 0)) : discrete_fun _) ∗
       own state_name (discrete_fun_singleton i (debt a 1, ●MN 0))).
  Proof.
    iIntros (LU) "Htk".
    assert (FORK : ((λ k : thread_id, if decide (k ∈ S) then ε else (debt a 1, ●MN 0)) : discrete_fun _)
                     ≡
                     (((λ k : thread_id, if decide (k ∈ {[i]} ∪ S) then ε else (debt a 1, ●MN 0)) : discrete_fun _)
                      ⋅ discrete_fun_singleton i (debt a 1, ●MN 0))).
    { intros x. rewrite discrete_fun_lookup_op. destruct (decide (x ∈ S)).
      - destruct (decide (x ∈ {[i]} ∪ S)).
        + rewrite discrete_fun_lookup_singleton_ne; [by rewrite left_id | set_solver].
        + exfalso. set_solver.
      - destruct (decide (x = i)).
        + subst. destruct (decide (i ∈ {[i]} ∪ S)); [|exfalso; set_solver].
          by rewrite discrete_fun_lookup_singleton left_id.
        + destruct (decide (x ∈ {[i]} ∪ S)); [exfalso; set_solver |].
          rewrite discrete_fun_lookup_singleton_ne; [by rewrite right_id | done].
    }
    rewrite FORK own_op. iDestruct "Htk" as "[Htk Hi]". iFrame.
  Qed.

  Lemma schedfairI_fork δ i f :
    (δ !! i = None) →
    schedfairI δ
    ⊢ |==> schedfairI (<[i:=Some f]>δ) ∗
           sfS_exec i (1/2) ∗ ∃ fb, (* ⌜f /≤ fb⌝ ∗ *) sfS_fuel_bound i fb 1.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU) "(% & Htk & Hs)".
    pose proof LU as LU'. apply not_elem_of_dom in LU.
    iDestruct (schedfairI_reserved_fork _ _ _ LU with "Htk") as "[Htk Hi]".
    iAssert (sfS_fuel_bound i a 1 ∗ sfS_exec i (1/2) ∗ sfS_exec i (1/2))%I with "[Hi]" as "(Hfb&He1&He2)".
    { rewrite /sfS_fuel_bound /sfS_exec. do 2 rewrite -own_op. rewrite !discrete_fun_singleton_op.
      rewrite -!pair_op. simpl. iApply own_mono; [|done]. exists ε. rewrite right_id.
      apply discrete_fun_singleton_proper. rewrite -mono_nat_auth_dfrac_op dfrac_op_own Qp.div_2.
      by rewrite !left_id !right_id_L.
    }
    iMod (sfS_fuel_owe i _ f with "Hfb") as "[Hfb Hfc]".
    iModIntro. iFrame.
    (* iSplit; [|iPureIntro; apply OrderedCM.add_base_right_le]. *)
    iExists a. iSplitL "Htk".
    - rewrite dom_insert_L. done.
    - iApply big_sepM_insert; [auto|]. iFrame. done.
  Qed.

  Lemma schedfairI_decr_one δ i f f' :
    (δ !! i = Some (Some f)) →
    (f' /< f) →
    schedfairI δ
    ⊢ |==> schedfairI (<[i:=Some f']>δ) ∗ ∃ c, ⌜/0 /< c⌝ ∗ sfS_fuel_credit i c.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU Hf) "(%&Htk&Hs)".
    rewrite (dom_insert_lookup_L δ i (Some f')); [iFrame | done].
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&Hfc&He)".
    assert (∃ f1, (/0 /< f1) ∧ (f' /+ f1) /≤ f'0).
    { apply WFOrderedCM.lt_exists_left in Hf. destruct Hf as (?&?&?). exists x. split; [auto | etransitivity; eauto]. }
    destruct H0 as (f1&Hpos&Hf1). 
    iMod (sfS_fuel_credit_mon_add _ _ _ _ Hf1 with "Hfc") as "[Hfc1 Hfc2]".
    iPoseProof (big_sepM_insert _ (delete i δ) i (Some f') with "[Hs He Hfc1]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists f'. iFrame. done. }
    iModIntro. rewrite insert_delete_insert. iFrame. done.
  Qed.

  Lemma schedfairI_credit_one_reserved δ c :
    schedfairI δ
    ⊢ |==> schedfairI δ ∗
           (own state_name ((λ k : thread_id, if decide (k ∈ dom δ) then ε else (cash c, ε)) : discrete_fun _)).
  Proof.
    rewrite /schedfairI -!lock. iIntros "(%&Htk&Hs)".
    iMod (own_update with "Htk") as "Htk".
    { apply (discrete_fun_update _ (λ k, if decide (k ∈ dom δ) then ε else (debt (a /+ c) 1 ⋅ cash c, ●MN 0))).
      intros. destruct (decide (a0 ∈ dom δ)); [done|]. apply prod_update; [apply debt_owe|done].
    }
    assert (ADD : ((λ k : thread_id, if decide (k ∈ dom δ) then ε else (debt (a /+ c) 1 ⋅ cash c, ●MN 0)) : discrete_fun _)
                    ≡
                    (((λ k : thread_id, if decide (k ∈ dom δ) then ε else (debt (a /+ c) 1, ●MN 0)) : discrete_fun _)
                     ⋅ ((λ k : thread_id, if decide (k ∈ dom δ) then ε else (cash c, ε)) : discrete_fun _))).
    { intros x. rewrite discrete_fun_lookup_op. destruct (decide (x ∈ dom δ)); [by rewrite left_id | by rewrite -pair_op]. }
    rewrite ADD. clear ADD. iDestruct "Htk" as "[Htk Hc]". iModIntro. iFrame.
  Qed.

  Lemma schedfairI_reset_one δ i f f0 f' :
    (δ !! i = Some (Some f)) →
    schedfairI δ ∗ sfS_fuel_bound i f0 1
    ⊢ |==> schedfairI (<[i:=Some f']>δ) ∗ sfS_fuel_bound i (f0 /+ f') 1.
  Proof.
    rewrite /schedfairI -!lock. iIntros (LU) "[(%&Htk&Hs) Hfb]".
    rewrite dom_insert_lookup_L; [iFrame|done].
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&_&He)".
    iMod (sfS_fuel_owe i _ f' with "Hfb") as "[Hfb Hfc]". iFrame.
    iPoseProof (big_sepM_insert _ (delete i δ) i (Some f') with "[Hs He Hfc]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists f'. iFrame. done. }
    iModIntro. rewrite insert_delete_insert. iFrame.
  Qed.

  Lemma schedfairI_term_one δ i oF f :
    (δ !! i = Some oF) →
    schedfairI δ ∗ sfS_exec i (1/2) ∗ sfS_fuel_bound i f 1
    ⊢ |==> schedfairI (<[i:=None]>δ) ∗ sfS_term i.
  Proof.
    iIntros (LU) "(Hs&He&Hfb)". iDestruct (schedfairI_thread_is_exec with "[Hs He]") as "[% %]"; [iFrame|subst].
    rewrite /schedfairI -!lock. iDestruct "Hs" as "(%&Htk&Hs)".
    iPoseProof (big_sepM_delete with "Hs") as "[LU Hs]"; [eauto |].
    iDestruct "LU" as "(%&%&Hfc&He2)".
    iMod (sfS_exec_to_term with "[He He2]") as "Hta".
    { rewrite /sfS_exec. iPoseProof (own_op with "[He He2]") as "He"; [iFrame|].
      iApply own_mono; [|done]. exists ε. rewrite right_id.
      rewrite discrete_fun_singleton_op -pair_op. apply discrete_fun_singleton_proper.
      rewrite -mono_nat_auth_dfrac_op dfrac_op_own Qp.div_2. by rewrite !left_id.
    }
    iPoseProof (sfS_term_auth_term with "Hta") as "#Hterm".
    iPoseProof (big_sepM_insert _ (delete i δ) i None with "[Hs Hta Hfb]") as "Hs".
    { apply lookup_delete. }
    { iFrame. iExists f. iFrame. }
    iModIntro. rewrite insert_delete_insert. iFrame. iSplit; [iExists _; by rewrite dom_insert_lookup_L | done].
  Qed.

End sfi.

(* Allocation of an initial obligation protocol. *)
Lemma schedfairI_alloc `{SI : indexT} `{WF : WFOrderedCM.t A leR addO ltR} `{!schedfairGpreS Σ} : ⊢ |==> ∃ _ : schedfairGS Σ, schedfairI ∅.
Proof.
  iIntros.
  iMod (own_alloc ((λ k, if (decide (k ∈ dom (∅ : gmap thread_id (option A)))) then ε else (debt OrderedCM.unit 1, ●MN 0)) : discrete_fun _)) as (γS) "HS".
  { intros x. destruct (decide (x ∈ dom ∅)).
    - apply ucmra_unit_valid.
    - apply pair_valid. split; [by apply bank_valid_debt | apply mono_nat_auth_valid].
  }
  iModIntro; iExists (SchedfairG SI _ _ _ _ WF _ _ γS).
  rewrite /schedfairI -lock.
  iExists OrderedCM.unit. rewrite big_opM_empty. by iFrame.
Qed.
