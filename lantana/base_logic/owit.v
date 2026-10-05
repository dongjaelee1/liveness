(** * Ghost state of witnesses

    The invariant [owit W] holds a credit for every assigned witness of [W] and [owit_inv Ω W]
    relates witnesses to obligations. Rules for witness credits and witness steps. *)

From iris.algebra Require Import reservation_map.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From lantana.algebra Require Export wfocm.
From lantana.algebra Require Import bcred.
From lantana.base_logic Require Export witness osat.

(** The ghost state for witnesses *)
Module owitGS.

  Class owitGpreS `{SI : sidx} (Σ : gFunctors) : Set :=
    OwitGpreS {
        owitGpreS_witness : inG Σ (reservation_mapUR (bcredUR));
      }.

  Class owitGS `{SI : sidx} (Σ : gFunctors) : Set :=
    OwitG {
        owit_inG : owitGpreS Σ;
        witness_name : gname;
      }.

  Definition owitΣ `{SI : sidx} : gFunctors :=
    #[GFunctor (reservation_mapUR (bcredUR))
      ].

  Global Instance subG_owitΣ `{SI : sidx} {Σ} : subG (owitΣ) Σ → (owitGpreS Σ).
  Proof. solve_inG. Qed.

End owitGS.
Import owitGS.

Local Existing Instances owit_inG owitGpreS_witness.

(* Witness: manage credits for an obl's witness progress *)
Definition witG_bound `{SI : sidx} `{!owitGS Σ}
  (k : oid) (ℵ : obl_fuel) : iProp Σ :=
  own witness_name (reservation_map_data (A:=bcredUR) k (credit_bound ℵ)).
Global Typeclasses Opaque witG_bound.
Global Instance: Params (@witG_bound) 3 := {}.

Definition witG_witness `{SI : sidx} `{!owitGS Σ}
  (k : oid) (a : obl_fuel) : iProp Σ :=
  own witness_name (reservation_map_data (A:=bcredUR) k (credit a)).
Global Typeclasses Opaque witG_witness.
Global Instance: Params (@witG_witness) 3 := {}.

Local Definition witG_bound_token_id `{SI : sidx} `{!owitGS Σ}
  (E : coPset) : iProp Σ :=
  own witness_name (reservation_map_token (A:=bcredUR) E).

(* Global invariant for the witness ghost state *)
Definition owit `{SI : sidx} {Σ}
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

(* Global invariant that relates witnesses to obls *)
Definition owit_inv `{!ord_mono_fun_class}
  (Ω : obls) (W : witnesses) : Prop :=
  map_Forall2 (λ k g w,
                 match g, w with
                 | (obl_assigned a _), (witness_assigned b) => (b w≤ η a)
                 | (obl_discharged), (witness_discharged) => True
                 | _, _ => False
                 end
    ) Ω W.

Section owit.
  Context `{SI : sidx} `{OSAT : !osatGS.osatGS Σ} `{!owitGS Σ} `{OMF : !ord_mono_fun_class}.

  (* witness *)
  Global Instance witG_bound_persistent k ℵ : Persistent (witG_bound k ℵ).
  Proof. rewrite /witG_bound. apply _. Qed.
  Global Instance witG_bound_timeless k ℵ : Timeless (witG_bound k ℵ).
  Proof. rewrite /witG_bound. apply _. Qed.

  Global Instance witG_witness_timeless k a : Timeless (witG_witness k a).
  Proof. rewrite /witG_witness. apply _. Qed.

  Local Instance witG_bound_token_id_timeless E : Timeless (witG_bound_token_id E).
  Proof. rewrite /witG_bound_token_id. apply _. Qed.

  (* Invariant *)
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

  (** Witness steps: progress and discharge *)
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

End owit.

Lemma owit_alloc `{SI : sidx} {Σ}
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
