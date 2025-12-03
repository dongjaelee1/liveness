From iris.algebra Require Import gmap_view reservation_map dfrac_agree mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Export wfocm.
From liris.algebra Require Import bcred.
From liris.base_logic Require Export witness osat.

(** The ghost state for liveness obligations *)
Module owitnessGS.

  Class owitnessGpreS `{SI : indexT} `{WF : WFOCM.pack A} (Σ : gFunctors) : Set :=
    OwitnessGpreS {
        owitnessGpreS_witness : inG Σ (reservation_mapUR bcredUR);
      }.

  Class owitnessGS `{SI : indexT} `{WF : WFOCM.pack A} (Σ : gFunctors) : Set :=
    OwitnessG {
        owitness_inG : owitnessGpreS Σ;
        witness_name : gname;
      }.

  Definition owitnessΣ `{SI : indexT} `{WF : WFOCM.pack A} : gFunctors :=
    #[GFunctor (reservation_mapUR bcredUR)
      ].

  Global Instance subG_owitnessΣ `{SI : indexT} `{WF : WFOCM.pack A} {Σ} : subG (owitnessΣ) Σ → (owitnessGpreS Σ).
  Proof. solve_inG. Qed.

End owitnessGS.
Import owitnessGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances owitness_inG
  owitnessGpreS_witness.

(* Witness: manage credits for logical progress *)
Definition owitnessG_witness `{SI : indexT} `{WFOCM.pack A} `{!owitnessGS Σ} (k : obl_id) (ℵ : A) : iProp Σ :=
  own witness_name (reservation_map_data k (credit_bound ℵ)).
Global Typeclasses Opaque owitnessG_witness.
Global Instance: Params (@owitnessG_witness) 6 := {}.

Definition owitnessG_credit `{SI : indexT} `{WF : WFOCM.pack A} `{!owitnessGS Σ} (k : obl_id) (α : A) : iProp Σ :=
  own witness_name (reservation_map_data k (credit α)).
Global Typeclasses Opaque owitnessG_credit.
Global Instance: Params (@owitnessG_credit) 6 := {}.

(* Global invariant for the obligation ghost state *)
Definition owitness `{SI : indexT} `{WFA : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps T Σ} `{!owitnessGS Σ}
  `{wit_live_class A WFOCM.ltR}
  (W : wit_states) : iProp Σ :=
  locked
    ((own witness_name (reservation_map_token (A:=bcredUR) (⊤ ∖ gset_to_coPset (dom W)))) ∗
     ([∗ map] k ↦ w ∈ W,
        match w with
        | inl d =>
            ∃ α, (⌜ WFOCM.leR (wit_credit d) α ⌝) ∗ owitnessG_credit k α
        | inr _ =>
            oblG_done k
        end)
    )%I.

(* Global invariant that relates witnesses to obligations *)
Definition obl_wit `{WFA : WFOCM.pack A}
  `{Ξl : obl_live_class A T WFOCM.ltR} `{Ξd : obl_done_class ps}
  `{Ξw : wit_live_class A WFOCM.ltR}
  (ξ : A → A)
  (Ω : obl_states) (W : wit_states) : Prop :=
  map_Forall2 (λ k o w,
                 match o, w with
                 | inl d, inl e =>
                     WFOCM.leR (wit_credit e) (ξ (obl_fuel d))
                     (* WFOCM.leR (obl_fuel d) (wit_credit e) ∧ WFOCM.leR (wit_credit e) (ξ (obl_fuel d)) *)
                 | inr _, inr _ => True
                 | _, _ => False
                 end
    ) Ω W.

(** Properties *)
Section owitness.
  Context `{SI : indexT} `{WFA : WFOCM.pack A}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps T Σ} `{!owitnessGS Σ}.
  Context `{Ξl : obl_live_class A T WFOCM.ltR} `{Ξd : obl_done_class ps}.
  Context `{Ξw : wit_live_class A WFOCM.ltR}.

  Global Instance owitnessG_witness_persistent k ℵ : Persistent (owitnessG_witness k ℵ).
  Proof. rewrite /owitnessG_witness. apply _. Qed.

  Global Instance owitnessG_witness_timeless k ℵ : Timeless (owitnessG_witness k ℵ).
  Proof. rewrite /owitnessG_witness. apply _. Qed.
  Global Instance owitnessG_credit_timeless k ℵ : Timeless (owitnessG_credit k ℵ).
  Proof. rewrite /owitnessG_credit. apply _. Qed.

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

  (** Witness credit rules *)
  Lemma owitnessG_credit_eq i a0 a1 :
    a0 /= a1 →
    owitnessG_credit i a0 = owitnessG_credit i a1.
  Proof. intros EQ. rewrite /owitnessG_credit. by erewrite credit_eq. Qed.
  Lemma owitnessG_credit_eq_list L a0 a1 :
    a0 /= a1 →
    ([∗ list] i ∈ L, owitnessG_credit i a0)%I ≡ ([∗ list] i ∈ L, owitnessG_credit i a1)%I.
  Proof. intros. apply big_opL_proper. intros. erewrite owitnessG_credit_eq; eauto. Qed.
  Lemma owitnessG_credit_eq_set L a0 a1 :
    a0 /= a1 →
    ([∗ set] i ∈ L, owitnessG_credit i a0)%I ≡ ([∗ set] i ∈ L, owitnessG_credit i a1)%I.
  Proof. intros. apply big_opS_proper. intros. erewrite owitnessG_credit_eq; eauto. Qed.

  Lemma owitnessG_credit_mon i a0 a1 :
    a0 /≤ a1 →
    owitnessG_credit i a1 ⊢ |==> owitnessG_credit i a0.
  Proof.
    intros LE. rewrite /owitnessG_credit. apply own_update.
    by apply reservation_map_update, credit_update.
  Qed.
  Lemma owitnessG_credit_mon_list L a0 a1 :
    a0 /≤ a1 →
    ([∗ list] i ∈ L, owitnessG_credit i a1) ⊢ |==> ([∗ list] i ∈ L, owitnessG_credit i a0).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply owitnessG_credit_mon.
  Qed.
  Lemma owitnessG_credit_mon_set L a0 a1 :
    a0 /≤ a1 →
    ([∗ set] i ∈ L, owitnessG_credit i a1) ⊢ |==> ([∗ set] i ∈ L, owitnessG_credit i a0).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply owitnessG_credit_mon.
  Qed.

  Lemma owitnessG_credit_split i a0 a1 :
    owitnessG_credit i (a0 /+ a1) ⊣⊢ owitnessG_credit i a0 ∗ owitnessG_credit i a1.
  Proof.
    rewrite /owitnessG_credit. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite credit_split). iSplitL "H1"; iFrame.
  Qed.
  Lemma owitnessG_credit_split_list L a0 a1 :
    ([∗ list] i ∈ L, owitnessG_credit i (a0 /+ a1)) ⊣⊢ ([∗ list] i ∈ L, owitnessG_credit i a0) ∗ ([∗ list] i ∈ L, owitnessG_credit i a1).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply owitnessG_credit_split.
  Qed.
  Lemma owitnessG_credit_split_set L a0 a1 :
    ([∗ set] i ∈ L, owitnessG_credit i (a0 /+ a1)) ⊣⊢ ([∗ set] i ∈ L, owitnessG_credit i a0) ∗ ([∗ set] i ∈ L, owitnessG_credit i a1).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply owitnessG_credit_split.
  Qed.

  Lemma owitnessG_credit_mon_split i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    owitnessG_credit i a2 ⊢ |==> owitnessG_credit i a0 ∗ owitnessG_credit i a1.
  Proof.
    intros LE. iIntros "H". iApply owitnessG_credit_split. iApply owitnessG_credit_mon; done.
  Qed.
  Lemma owitnessG_credit_mon_split_list L a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ list] i ∈ L, owitnessG_credit i a2) ⊢ |==> ([∗ list] i ∈ L, owitnessG_credit i a0) ∗ ([∗ list] i ∈ L, owitnessG_credit i a1).
  Proof.
    iIntros (LE) "H". iPoseProof (owitnessG_credit_mon_list with "H") as ">H"; first done.
    by iApply owitnessG_credit_split_list.
  Qed.
  Lemma owitnessG_credit_mon_split_set L a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ set] i ∈ L, owitnessG_credit i a2) ⊢ |==> ([∗ set] i ∈ L, owitnessG_credit i a0) ∗ ([∗ set] i ∈ L, owitnessG_credit i a1).
  Proof.
    iIntros (LE) "H". iPoseProof (owitnessG_credit_mon_set with "H") as ">H"; first done.
    by iApply owitnessG_credit_split_set.
  Qed.

  Lemma owitnessG_credit_lt i a0 a1 :
    a0 /< a1 →
    owitnessG_credit i a1 ⊢ |==> owitnessG_credit i a0 ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ owitnessG_credit i c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (owitnessG_credit_mon_split _ _ _ _ H1 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.
  Lemma owitnessG_credit_lt_list L a0 a1 :
    a0 /< a1 →
    ([∗ list] i ∈ L, owitnessG_credit i a1) ⊢ |==> ([∗ list] i ∈ L, owitnessG_credit i a0 ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ owitnessG_credit i c).
  Proof.
    iIntros (LT) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply owitnessG_credit_lt.
  Qed.
  Lemma owitnessG_credit_lt_set L a0 a1 :
    a0 /< a1 →
    ([∗ set] i ∈ L, owitnessG_credit i a1) ⊢ |==> ([∗ set] i ∈ L, owitnessG_credit i a0 ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ owitnessG_credit i c).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply owitnessG_credit_lt.
  Qed.

  Lemma owitnessG_witness_mon k a0 a1 :
    a0 /≤ a1 →
    owitnessG_witness k a0 ⊢ |==> owitnessG_witness k a1.
  Proof.
    intros LE. rewrite /owitnessG_witness. apply own_update.
    by apply reservation_map_update, cmra_update_included, credit_bound_included.
  Qed.

  Lemma owitnessG_credit_spend_gen i a0 a1 :
    owitnessG_witness i a0 ∗ owitnessG_credit i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ owitnessG_witness i a2.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ k, ∃ a2, (k = (credit_bound a2)) ∧ (a1 /+ a2 /≤ a0))
                (λ k, ∃ a2, (k = {[i := (credit_bound a2)]}) ∧ (a1 /+ a2 /≤ a0))
             ).
      { eapply credit_spend. }
      { intros. destruct H0 as (a2&A0&A1). eexists. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplitR; done.
  Qed.
  Lemma owitnessG_credit_spend i a0 a1 :
    /0 /< a1 →
    owitnessG_witness i a0 ∗ owitnessG_credit i a1 ⊢ |==> ∃ a2, ⌜a2 /< a0⌝ ∗ owitnessG_witness i a2.
  Proof.
    iIntros (LT) "[Ow Oc]". iMod (owitnessG_credit_spend_gen with "[$]") as "(%&%&$)".
    iPureIntro. eapply WFOCM.lt_exists_right; eauto.
  Qed.

  Lemma owitnessG_compare i a0 a1 :
    owitnessG_witness i a0 ∗ owitnessG_credit i a1 ⊢ ⌜ a1 /≤ a0 ⌝.
  Proof.
    rewrite -own_op -reservation_map_data_op. iIntros "H".
    iPoseProof (own_valid with "H") as "%". apply reservation_map_data_valid in H0.
    apply credit_bound_credit_valid_compare in H0. done.
  Qed.

  Lemma owitnessG_witness_alloc D k a :
    k ∉ D →
    (own witness_name (reservation_map_token (A:=bcredUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own witness_name (reservation_map_token (A:=bcredUR) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           owitnessG_witness k a ∗ owitnessG_credit k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (credit_bound a ⋅ credit a) with "Htk") as "[Htk >H]"; auto.
    { apply credit_bound_credit_valid_eq. }
    iDestruct "H" as "[H1 H2]". rewrite /owitnessG_witness /owitnessG_credit.
    by iFrame.
  Qed.

  (** owitness rules *)
  Lemma owitness_alloc_wit W k ℵ :
    k ∉ dom W →
    owitness W
    ⊢ |==> owitness (<[k:=wlive ℵ]>W) ∗ owitnessG_witness k ℵ.
  Proof.
    iIntros (Nink) "N".
    rewrite /owitness -!lock. iDestruct "N" as "(Ow& NM)".
    iMod (owitnessG_witness_alloc _ k ℵ with "Ow") as "(Ow& Nw& Nc)"; first done.
    iModIntro. rewrite dom_insert_L. iFrame "Ow Nw".
    iApply big_sepM_insert.
    { by eapply not_elem_of_dom. }
    iFrame. simpl. done.
  Qed.

  Lemma owitness_wit_progress_one W k w1 w2 :
    W !! k = Some w1 →
    wit_state_progress w1 w2 →
    owitness W
    ⊢ |==> owitness (<[k:=w2]>W) ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ owitnessG_credit k c.
  Proof.
    iIntros (Luk Prog) "N".
    rewrite /owitness -!lock. iDestruct "N" as "(On& Nm)".
    assert (Ink : k ∈ dom W).
    { apply elem_of_dom. eauto. }
    rewrite dom_insert_L.
    destruct w1, w2; try done. destruct w as [α], w0 as [α0]; simpl in *.
    iPoseProof (big_sepM_delete _ _ _ _ Luk with "Nm") as "[Mk Nm]".
    simpl. iDestruct "Mk" as "(%& %& Nck)".
    assert (Lt : α0 /< α1).
    { eapply WFOCM.lt_le_lt; eauto. }
    apply WFOCM.lt_exists_left in Lt. destruct Lt as (?& Lt& Le).
    iMod (owitnessG_credit_mon_split _ _ _ _ Le with "Nck") as "[Nck Nck0]".
    iModIntro. iFrame "Nck0". iSplitL; last done. iSplitL "On".
    { replace ({[k]} ∪ dom W) with (dom W); eauto. set_solver. }
    rewrite -(insert_delete_eq W k). iApply big_sepM_insert.
    { apply lookup_delete_eq. }
    iFrame. simpl. done.
  Qed.

  Lemma owitness_wit_progress W1 W2 :
    (W1 ↓ₚ W2 | wit_cond_live) →
    owitness W1
    ⊢ |==> owitness W2 ∗
        ([∗ map] k ↦ w ∈ W1, match w with
                             | inl _ => (∃ c, ⌜ /0 /< c ⌝ ∗ owitnessG_credit k c)
                             | inr _ => oblG_done k
                             end).
  Proof.
    iIntros (Prog) "N".
    assert (Dom : dom W1 = dom W2) by (eapply wit_states_cond_rel_dom; eauto).
    rewrite /owitness -!lock. iDestruct "N" as "(On& Nm)".
    rewrite -Dom. iFrame "On".
    iStopProof. clear Dom. revert W2 Prog. induction W1 using map_ind; iIntros (W2 Prog) "Nm".
    { apply map_Forall2_empty_inv_l in Prog. subst. iModIntro. iFrame. done. }
    apply map_Forall2_insert_inv_l in Prog; last auto. destruct Prog as (w2& m2& EqW2& LUm2& (HC1& HC2)& Prog).
    subst. rewrite !big_sepM_insert; auto.
    iDestruct "Nm" as "[Nmx Nm]". iMod (IHW1 _ Prog with "Nm") as "[Nm Cs]". clear IHW1.
    iFrame "Nm Cs". destruct x; simpl in *.
    - pose proof (HC1 I). destruct w2; simpl in *; last done.
      destruct w as [α], w0 as [α0]; simpl in *. iDestruct "Nmx" as "(%& %& Nck)".
      assert (Lt : α0 /< α1).
      { eapply WFOCM.lt_le_lt; eauto. }
      apply WFOCM.lt_exists_left in Lt. destruct Lt as (?& Lt& Le).
      iMod (owitnessG_credit_mon_split _ _ _ _ Le with "Nck") as "[Nck Nck0]".
      iModIntro. iSplitL "Nck"; by iFrame.
    - assert (inr u = w2) by (by apply HC2).
      destruct w2; first done. inv H1. iPoseProof "Nmx" as "#H". by auto.
  Qed.

  Lemma owitness_wit_progress_any C W1 W2 :
    (∀ k o, Decision (C k o)) →
    (W1 ↓ₚ W2 | C) →
    owitness W1 ⊢ owitness W2.
  Proof.
    iIntros (DC Prog) "N".
    assert (Dom : dom W1 = dom W2) by (eapply wit_states_cond_rel_dom; eauto).
    rewrite /owitness -!lock. iDestruct "N" as "(On& Nm)".
    rewrite -Dom. iFrame "On".
    iStopProof. clear Dom. revert W2 Prog. induction W1 using map_ind; iIntros (W2 Prog) "Nm".
    { apply map_Forall2_empty_inv_l in Prog. subst. iFrame. }
    apply map_Forall2_insert_inv_l in Prog; last auto. destruct Prog as (w2& m2& EqW2& LUm2& (HC1& HC2)& Prog).
    subst. rewrite !big_sepM_insert; auto.
    iDestruct "Nm" as "[Nmx Nm]". iPoseProof (IHW1 _ Prog with "Nm") as "Nm". clear IHW1.
    iFrame "Nm". destruct x; simpl in *.
    - destruct (decide (C i (inl w))).
      + pose proof (HC1 c). destruct w2; simpl in *; last done.
        iDestruct "Nmx" as "(%& %& NC)". iExists α. iFrame. iPureIntro.
        etransitivity; last eauto. eapply WFOCM.lt_le; eauto.
      + pose proof (HC2 n). subst. iFrame.
    - destruct (decide (C i (inr u))).
      + apply HC1 in c. done.
      + apply HC2 in n. subst. auto.
  Qed.

  Lemma owitness_wit_resolve_one W1 W2 k :
    (W1 ↓ᵣ W2 | wit_cond_one k) →
    owitness W1 ∗ oblG_done k
    ⊢ |==> owitness W2.
  Proof.
    iIntros (Prog) "(N& #Bdk)".
    assert (Dom : dom W1 = dom W2) by (eapply wit_states_cond_rel_dom; eauto).
    rewrite /owitness -!lock. iDestruct "N" as "(On& Nm)".
    rewrite -Dom. iFrame "On".
    iStopProof. clear Dom. revert W2 k Prog. induction W1 using map_ind; iIntros (W2 k Prog) "(#Bdk& Nm)".
    { apply map_Forall2_empty_inv_l in Prog. subst. iModIntro. iFrame. }
    apply map_Forall2_insert_inv_l in Prog; last auto. destruct Prog as (w2& m2& EqW2& LUm2& (HC1& HC2)& Prog).
    subst. rewrite !big_sepM_insert; auto.
    iDestruct "Nm" as "[Nmx Nm]". iMod (IHW1 _ k Prog with "[$Bdk $Nm]") as "Nm". clear IHW1.
    iFrame "Nm". destruct x; simpl in *.
    - destruct (decide (wit_cond_one k i (inl w))).
      + pose proof w0. apply HC1 in w0. rewrite /wit_cond_one in H1. subst. destruct w2; try done.
      + apply HC2 in n. subst. by iFrame.
    - destruct (decide (wit_cond_one k i (inr u))).
      + apply HC1 in w. done.
      + apply HC2 in n. subst. by iFrame.
  Qed.

  (** obl_wit rules *)
  Lemma obl_wit_init ξ :
    obl_wit ξ ∅ ∅.
  Proof. apply map_Forall2_empty. Qed.

  Lemma obl_wit_dom ξ Ω W :
    obl_wit ξ Ω W → dom Ω = dom W.
  Proof.
    intros. eapply map_Forall2_dom_L; eauto.
  Qed.

  Lemma obl_wit_resolve_same ξ C Ω W1 W2 :
    (∀ (k : obl_id) (o : wit_state), Decision (C k o)) →
    obl_wit ξ Ω W1 →
    (W1 ↓ᵣ W2 | C) →
    obl_wit ξ Ω W2 →
    W1 = W2.
  Proof.
    revert Ω W2. induction W1 using map_ind; intros.
    { apply map_Forall2_empty_inv_l in H1. subst. apply map_Forall2_empty_inv_r in H0. by subst. }
    rename x into w1, m into W1, W2 into W2', Ω into Ω'.
    apply map_Forall2_insert_inv_r in H1; auto. destruct H1 as (o& Ω& EQO& LUOi& HO1& MFO).
    apply map_Forall2_insert_inv_l in H2; auto. destruct H2 as (w2& W2& EQW2& LUWi2& (HC1& HC2)& MFW).
    subst. apply map_Forall2_insert in H3; auto. destruct H3 as (How& MFW2).
    pose proof (IHW1 _ _ X MFO MFW MFW2).
    subst. clear MFO MFW2. destruct o, w1, w2; simpl in *; try done.
    - destruct (decide (C i (inl w))).
      + by apply HC1 in c.
      + apply HC2 in n. inv n. done.
    - clear How. destruct (decide (C i (inr u))).
      + by apply HC1 in c.
      + apply HC2 in n. inv n. done.
  Qed.

  Lemma obl_wit_same_obl_alloc_false ξ Ω W1 W2 :
    obl_wit ξ Ω W1 →
    (W1 ↓ₐ W2) →
    obl_wit ξ Ω W2 →
    False.
  Proof.
    intros. destruct H1 as (k& d& LU& EQ). subst.
    apply obl_wit_dom in H0, H2. rewrite H0 dom_insert_L in H2.
    apply not_elem_of_dom in LU. set_solver + LU H2.
  Qed.

  Lemma obl_wit_same_wit_alloc_false ξ Ω1 Ω2 W :
    obl_wit ξ Ω1 W →
    (Ω1 ↪ₐ Ω2) →
    obl_wit ξ Ω2 W →
    False.
  Proof.
    intros. destruct H1 as (k& d& LU& EQ). subst.
    apply obl_wit_dom in H0, H2. rewrite -H0 dom_insert_L in H2.
    apply not_elem_of_dom in LU. set_solver + LU H2.
  Qed.

  Lemma owitness_obl_wit_step_same_obl ξ Ω W1 W2 :
    obl_wit ξ Ω W1 →
    W1 ↓ₛ W2 →
    obl_wit ξ Ω W2 →
    owitness W1 ⊢ owitness W2.
  Proof.
    iIntros (OW1 Prog OW2) "N". inv Prog.
    - iPoseProof (owitness_wit_progress_any with "N") as "N"; eauto.
    - pose proof (obl_wit_resolve_same _ _ _ _ _ X OW1 H0 OW2). by subst.
    - pose proof (obl_wit_same_obl_alloc_false _ _ _ _ OW1 H0 OW2). done.
  Qed.

  Lemma owitness_obl_wit_rc_step_same_obl ξ Ω W1 W2 :
    obl_wit ξ Ω W1 →
    W1 ↓ₛ∘ W2 →
    obl_wit ξ Ω W2 →
    owitness W1 ⊢ owitness W2.
  Proof.
    iIntros (OW1 Prog OW2) "N". inv Prog; first done.
    iApply (owitness_obl_wit_step_same_obl _ Ω W1 W2 with "N"); eauto.
  Qed.

  Lemma obl_wit_alloc ξ Ω k i a W1 W2 :
    k ∉ dom Ω →
    obl_wit ξ Ω W1 ->
    W1 ↓ₛ∘ W2 ->
    obl_wit ξ (<[k:=olive i a]> Ω) W2 ->
    ∃ b, b /≤ (ξ a) ∧ W2 = (<[k:=wlive b]>W1).
  Proof.
    intros Nink OW1 ProgW OW2. inv ProgW.
    { exfalso. eapply obl_wit_same_wit_alloc_false. 1: eapply OW1. 2: eapply OW2.
      do 2 eexists. split; eauto. by apply not_elem_of_dom. }
    inv H0.
    - exfalso. apply wit_states_cond_rel_dom in H1. apply obl_wit_dom in OW1, OW2.
      rewrite H1 in OW1. rewrite -OW1 in OW2. rewrite dom_insert_L in OW2. set_solver + Nink OW2.
    - exfalso. apply wit_states_cond_rel_dom in H1. apply obl_wit_dom in OW1, OW2.
      rewrite H1 in OW1. rewrite -OW1 in OW2. rewrite dom_insert_L in OW2. set_solver + Nink OW2.
    - apply map_Forall2_insert_inv_l in OW2.
      2: by apply not_elem_of_dom.
      destruct OW2 as (w'& W'& EQW2& LUW2& MP& MF). subst.
      simpl in *. destruct w'; last done.
      destruct w as [b]. simpl in *.
      destruct H1 as (?& ?& ?& ?).
      assert (Dom' : dom W' = dom W1).
      { apply obl_wit_dom in OW1, MF. by rewrite -OW1 -MF. }
      destruct (decide (k = x)).
      2:{ exfalso. apply (f_equal dom) in H1. rewrite !dom_insert_L in H1.
          apply not_elem_of_dom in LUW2, H0. rewrite Dom' in LUW2, H1. set_solver + n LUW2 H0 H1.
      }
      subst. destruct x0 as [c].
      assert (b = c).
      { rewrite map_eq_iff in H1. specialize (H1 x). rewrite !lookup_insert_eq in H1. by inv H1. }
      subst. exists c. split; auto.
  Qed.

  Lemma owitness_obl_wit_alloc ξ Ω k i a W1 W2 :
    k ∉ dom Ω →
    obl_wit ξ Ω W1 ->
    W1 ↓ₛ∘ W2 ->
    obl_wit ξ (<[k:=olive i a]> Ω) W2 ->
    owitness (<[k:=wlive (ξ a)]> W1)
    ⊢ |==> owitness W2.
  Proof.
    iIntros (Nink OW1 ProgW OW2) "N".
    edestruct obl_wit_alloc as (?& LE& Eq); eauto. subst.
    rewrite /owitness -!lock. iDestruct "N" as "[N1 NM]".
    iSplitL "N1".
    { rewrite !dom_insert_L. done. }
    assert (Dom : dom Ω = dom W1) by (by apply obl_wit_dom in OW1).
    assert (LUWk : W1 !! k = None).
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    rewrite !(big_sepM_insert _ _ _ _ LUWk). iDestruct "NM" as "[N $]".
    simpl. iDestruct "N" as "(%&%&Nc)". iFrame.
    iPureIntro. etransitivity; eauto.
  Qed.

  (* Maybe we don't need this *)
  (* Lemma owitness_obl_wit_steps_same_obl ξ Ω W1 W2 : *)
  (*   obl_wit ξ Ω W1 → *)
  (*   W1 ↓ₛ⋆ W2 → *)
  (*   obl_wit ξ Ω W2 → *)
  (*   owitness W1 ⊢ owitness W2. *)
  (* Proof. *)
  (*   iIntros (OW1 Prog OW2). revert Ω OW1 OW2. *)
  (*   induction Prog; iIntros (Ω OW1 OW2) "N". *)
  (*   1: done. *)
  (*   rename x into W1, y into W2, z into W3. *)
  (*   iPoseProof (owitness_obl_wit_step_same_obl _ _ W1 W2 with "N") as "N"; eauto. *)

  (*   pattern W2, W1. revert W1 W2 Prog. apply rtc_ind_r_weak; intros. *)
  (*   { done. } *)
  (*   rename x into W1, y into W2, z into W3, H0 into Steps, H1 into Step, H2 into IH. *)


  (* Lemma obl_wit_credit ξ Ω1 Ω2 W1 (i : T) : *)
  (*   Proper (WFOCM.ltR ==> WFOCM.ltR) ξ → *)
  (*   obl_wit ξ Ω1 W1 → *)
  (*   (Ω1 ↪ₚ Ω2 | obl_cond_owner i) → *)
  (*   ∃ W2, (W1 ↓ₚ W2 | λ k _, ∃ d, Ω1 !! k = Some (obl_live d) ∧ (obl_owner d = i)) ∧ *)
  (*         obl_wit ξ Ω2 W2. *)
  (* Proof. *)
  (*   intros Hξ. revert Ω2 W1. induction Ω1 using map_ind; intros Ω2 W1 OW OP. *)
  (*   { apply map_Forall2_empty_inv_l in OP, OW. subst. exists ∅. split; apply map_Forall2_empty. } *)
  (*   rename m into Ω1, W1 into W1', Ω2 into Ω2', i0 into k, x into o. *)
  (*   apply map_Forall2_insert_inv_l in OP; last auto. destruct OP as (o2& Ω2& EqO2& LUO2& (HCO1& HCO2)& OP). *)
  (*   apply map_Forall2_insert_inv_l in OW; last auto. destruct OW as (w2& W2& EqW2& LUW2& HW2& OW). *)
  (*   pose proof (IHΩ1 _ _ OW OP) as IH. clear IHΩ1 OW OP. destruct IH as (Wi& WPi& OWi). subst. *)
  (*   assert (WDom : dom W2 = dom Wi) by (eapply wit_states_cond_rel_dom; eauto). *)
  (*   assert (LUWi : Wi !! k = None). *)
  (*   { apply not_elem_of_dom. rewrite -WDom. apply not_elem_of_dom. auto. } *)
  (*   destruct o, w2; try done. *)
  (*   - destruct o as [θ α], w as [ℵ]. simpl in *. destruct (decide (θ = i)). *)
  (*     + subst. pose proof (HCO1 eq_refl). clear HCO1 HCO2. destruct o2; last done. *)
  (*       destruct o as [θ' α']. simpl in *. destruct H1; subst. *)
  (*       exists (<[k:=wlive (ξ α')]>Wi). split. *)
  (*       * apply map_Forall2_insert; auto. simpl. split_and !; auto. *)
  (*         -- intros. destruct H1 as (?&?&?). subst. rewrite HW2. apply Hξ. auto. *)
  (*         -- intros. exfalso. apply H1; clear H1. eexists. split. *)
  (*             { apply lookup_insert_eq. } *)
  (*            done. *)
  (*         -- intros ?. specialize (WPi i). destruct (W2 !! i) eqn:LUi1. *)
  (*            ++ destruct (decide (i = k)). *)
  (*               { subst. rewrite LUW2 in LUi1; done. } *)
  (*               rewrite LUi1 in WPi. destruct (Wi !! i) eqn:LUi2. *)
  (*               ** rewrite LUi1. inv WPi. destruct H4. econstructor. split; intro. *)
  (*                  { destruct H4 as (?&?&?). rewrite lookup_insert_ne in H4; eauto. } *)
  (*                  { apply H3. intros ?. apply H4. destruct H5 as (?&?&?). rewrite lookup_insert_ne; eauto. } *)
  (*               ** inv WPi. *)
  (*            ++ rewrite LUi1 in WPi. destruct (Wi !! i) eqn:LUi2. *)
  (*               ** inv WPi. *)
  (*               ** rewrite LUi1. econstructor. *)
  (*       * apply map_Forall2_insert; auto. simpl. split_and !; auto. done. *)
  (*     + pose proof (HCO2 n). subst. clear HCO1 HCO2. *)
  (*       exists (<[k:=wlive ℵ]>Wi). split; apply map_Forall2_insert; auto. *)
  (*       simpl. split_and !; auto. *)
  (*       -- intros. exfalso. destruct H1 as (?&?&?). subst. rewrite lookup_insert_eq in H1. inv H1. *)
  (*       -- intros j. specialize (WPi j). destruct (W2 !! j) eqn:LUj1. *)
  (*          ++ destruct (decide (j = k)). *)
  (*             { subst. rewrite LUW2 in LUj1; done. } *)
  (*             rewrite LUj1 in WPi. destruct (Wi !! j) eqn:LUj2. *)
  (*             ** rewrite LUj1. inv WPi. destruct H3. econstructor. split; intro. *)
  (*                { destruct H3 as (?&?&?). rewrite lookup_insert_ne in H3; eauto. } *)
  (*                { apply H2. intros ?. apply H3. destruct H4 as (?&?&?). rewrite lookup_insert_ne; eauto. } *)
  (*             ** inv WPi. *)
  (*          ++ rewrite LUj1 in WPi. destruct (Wi !! j) eqn:LUj2. *)
  (*             ** inv WPi. *)
  (*             ** rewrite LUj1. econstructor. *)
  (*   - simpl in *. assert (inr o = o2) by (by apply HCO2). clear HCO1 HCO2. subst. *)
  (*     exists (<[k:=wdone]>Wi). split; apply map_Forall2_insert; auto. *)
  (*     simpl. split_and !; auto. *)
  (*     * intros. destruct H1 as (?&?&?). rewrite lookup_insert_eq in H1. inv H1. *)
  (*     * intros. destruct u. done. *)
  (*     * intros j. specialize (WPi j). destruct (W2 !! j) eqn:LUj1. *)
  (*       -- destruct (decide (j = k)). *)
  (*          { subst. rewrite LUW2 in LUj1; done. } *)
  (*          rewrite LUj1 in WPi. destruct (Wi !! j) eqn:LUj2. *)
  (*          ++ rewrite LUj1. inv WPi. destruct H3. econstructor. split; intro. *)
  (*             { destruct H3 as (?&?&?). rewrite lookup_insert_ne in H3; eauto. } *)
  (*             { apply H2. intros ?. apply H3. destruct H4 as (?&?&?). rewrite lookup_insert_ne; eauto. } *)
  (*          ++ inv WPi. *)
  (*       -- rewrite LUj1 in WPi. destruct (Wi !! j) eqn:LUj2. *)
  (*          ++ inv WPi. *)
  (*          ++ rewrite LUj1. econstructor. *)
  (* Qed. *)

  (* TODO : sched fair case *)

End owitness.

(* Allocation of the initial witness protocol. *)
Lemma owitness_alloc `{SI : indexT} `{WFA : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps T Σ} `{!owitnessGpreS Σ}
  `{wit_live_class A WFOCM.ltR} :
  ⊢ |==> ∃ _ : owitnessGS Σ, owitness ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=bcredUR) ⊤)) as (γC) "HC";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (OwitnessG SI _ WFA _ _ γC).
  rewrite /owitness -lock.
  replace (⊤ ∖ gset_to_coPset (dom (∅ : wit_states))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
