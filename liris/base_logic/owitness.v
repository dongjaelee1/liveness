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

(* Progress: manage credits for logical progress *)
Definition owitnessG_witness `{SI : indexT} `{WFOCM.pack A} `{!owitnessGS Σ} (k : obl_id) (α : A) : iProp Σ :=
  own witness_name (reservation_map_data k (credit_bound α)).
Global Typeclasses Opaque owitnessG_witness.
Global Instance: Params (@owitnessG_witness) 6 := {}.

Definition owitnessG_credit `{SI : indexT} `{WF : WFOCM.pack A} `{!owitnessGS Σ} (k : obl_id) (α : A) : iProp Σ :=
  own witness_name (reservation_map_data k (credit α)).
Global Typeclasses Opaque owitnessG_credit.
Global Instance: Params (@owitnessG_credit) 6 := {}.

(* Global invariant for the obligation ghost state. *)
Definition owitness `{SI : indexT} `{WFA : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps T Σ} `{!owitnessGS Σ}
  `{wit_live_class A WFOCM.ltR}
  (W : wit_states) : iProp Σ :=
  locked
    ((own witness_name (reservation_map_token (A:=bcredUR) (⊤ ∖ gset_to_coPset (dom W)))) ∗
     ([∗ map] k ↦ w ∈ W,
        match w with
        | inl d =>
            ∃ α ℵ, (⌜ WFOCM.leR (wit_progress d) α ⌝) ∗ owitnessG_credit k α ∗ owitnessG_witness k ℵ
        | inr _ =>
            oblG_done k
        end)
    )%I.

(** Properties *)
Section owitness.
  Context `{SI : indexT} `{WFA : WFOCM.pack A} `{!owitnessGS ps T Σ}.
  Context `{Ξl : obl_live_class A T WFOCM.ltR} `{Ξd : obl_done_class ps}.

  Local Instance goal_unfold_contractive : Contractive (@goal_unfold SI Σ).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_contractive k P : Contractive (@oblG_goal SI _ WFA ps T Σ _ k P).
  Proof. solve_contractive. Qed.

  Global Instance oblG_goal_persistent k P R : Persistent (oblG_goal k P R).
  Proof. rewrite /oblG_goal. apply _. Qed.
  Global Instance oblG_elem_persistent k : Persistent (oblG_elem k).
  Proof. rewrite /oblG_elem. apply _. Qed.
  Global Instance oblG_done_persistent k : Persistent (oblG_done k).
  Proof. rewrite /oblG_done. apply _. Qed.
  (* Global Instance oblG_bound_persistent k ℵ : Persistent (oblG_bound k ℵ). *)
  (* Proof. rewrite /oblG_bound. apply _. Qed. *)

  Global Instance oblG_elem_timeless k : Timeless (oblG_elem k).
  Proof. rewrite /oblG_elem. apply _. Qed.
  Global Instance oblG_live_timeless k q : Timeless (oblG_live k q).
  Proof. rewrite /oblG_live. apply _. Qed.
  Global Instance oblG_done_timeless k : Timeless (oblG_done k).
  Proof. rewrite /oblG_done. apply _. Qed.
  Global Instance oblG_progress_timeless k b : Timeless (oblG_progress k b).
  Proof. rewrite /oblG_progress. apply _. Qed.
  (* Global Instance oblG_bound_timeless k a : Timeless (oblG_bound k a). *)
  (* Proof. rewrite /oblG_bound. apply _. Qed. *)

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

  (** Goal rules *)
  Lemma oblG_goal_lookup (OProp : gmap positive (prop_of ps * iProp Σ)) k P R :
    own goal_name (gmap_view_auth (DfracOwn 1) ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> OProp)) ∗
    oblG_goal k P R
    ⊢ ∃ P' R', ⌜ OProp !! k = Some (P', R') ⌝ ∗ ⌜ P' = P ⌝ ∗ ▷ (R' ≡ R).
  Proof.
    rewrite /oblG_goal -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
    case: (OProp !! k)=> [Q|] /=; last first.
    { by iDestruct "HQ'" as %?. }
    destruct Q as (P'&R'). iDestruct "HQ'" as %[= <-]. iExists P', R'; iSplit; first done.
    rewrite prod_includedI !to_agree_includedI; simpl. iDestruct "Hincl" as "[H1 H2]".
    rewrite /goal_unfold -later_equivI. iSplit.
    - iPoseProof (internal_eq_sym with "H1") as "H1". iPoseProof (discrete_eq with "H1") as "%HG". done.
    - iPoseProof (internal_eq_sym with "H2") as "H2". done.
  Qed.

  Lemma oblG_goal_agree k P0 P1 R0 R1 :
    oblG_goal k P0 R0 ∗ oblG_goal k P1 R1 ⊢ ⌜ P0 ≡ P1 ⌝ ∗ ▷ (R0 ≡ R1).
  Proof.
    rewrite /oblG_goal -own_op own_valid gmap_view_frag_op_validI.
    iIntros "(_&H)". rewrite -pair_op prod_validI; simpl. iDestruct "H" as "[% H]".
    rewrite /goal_unfold to_agree_op_validI -later_equivI. iFrame.
    iPureIntro. apply to_agree_op_valid in H. rewrite H. done.
  Qed.

  Lemma oblG_goal_elem (OProp : gmap positive (prop_of ps * iProp Σ)) k P R :
    own goal_name (gmap_view_auth (DfracOwn 1) ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> OProp)) ∗
    oblG_goal k P R
    ⊢ ⌜ k ∈ dom OProp ⌝.
  Proof.
    iIntros "[H Hg]". iPoseProof (oblG_goal_lookup with "[$]") as "(%&%&%&_)".
    iPureIntro. by apply elem_of_dom.
  Qed.

  (** Elem rules *)
  Lemma oblG_elem_alloc (Ω : obl_states) k M :
    Ω !! k = None →
    (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom Ω))))
    ⊢  |==> (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom (<[k:=M]>Ω))))) ∗
            oblG_elem k.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ k (DfracDiscarded) ()); try done.
      by apply lookup_gset_to_gmap_None, not_elem_of_dom.
    }
    iDestruct "H" as "[H He]". rewrite /oblG_elem. iFrame "He".
    rewrite dom_insert_L gset_to_gmap_union_singleton. done.
  Qed.

  Lemma oblG_elem_elem k (Ω : obl_states) :
    (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom Ω)))) ∗
    oblG_elem k
    ⊢ ⌜ k ∈ dom Ω ⌝.
  Proof.
    rewrite /oblG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro.
    apply lookup_gset_to_gmap_Some in H. by destruct H.
  Qed.

  (** Status rules *)
  Lemma oblG_live_done_false k q :
    oblG_live k q ∗ oblG_done k ⊢ False.
  Proof.
    rewrite /oblG_live /oblG_done. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma oblG_done_auth_done k :
    oblG_done_auth k ⊢ oblG_done k.
  Proof.
    rewrite /oblG_done_auth /oblG_done.
    apply own_mono.
    apply reservation_map_data_mono. apply mono_nat_included.
  Qed.

  Lemma oblG_live_to_done k :
    oblG_live k 1 ⊢ |==> oblG_done_auth k.
  Proof.
    rewrite /oblG_live /oblG_done_auth.
    apply own_update.
    apply reservation_map_update. apply mono_nat_update. auto.
  Qed.

  Lemma oblG_live_frac_op k q1 q2 q :
    q = (q1 + q2)%Qp →
    oblG_live k q1 ∗ oblG_live k q2 ⊣⊢ oblG_live k q.
  Proof.
    intros; subst. rewrite /oblG_live. iSplit; [iIntros "[H1 H2]" | iIntros "H"].
    - iCombine "H1 H2" as "H". done.
    - iDestruct "H" as "[H1 H2]". iFrame.
  Qed.
  Lemma oblG_live_div_2 k q :
    oblG_live k (q/2) ∗ oblG_live k (q/2) ⊣⊢ oblG_live k q.
  Proof. rewrite oblG_live_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma oblG_live_valid k q :
    oblG_live k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblG_live. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply mono_nat_auth_dfrac_valid in V. by apply dfrac_valid in V.
  Qed.

  Lemma oblG_live_alloc D k :
    k ∉ D →
    (own status_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own status_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           oblG_live k 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN 0) with "Htk") as "[Htk >H]"; auto.
    { apply mono_nat_auth_valid. }
    rewrite /oblG_live. by iFrame.
  Qed.

  (** Progress rules *)
  Lemma oblG_progress_eq i a0 a1 :
    a0 /= a1 →
    oblG_progress i a0 = oblG_progress i a1.
  Proof. intros EQ. rewrite /oblG_progress. by erewrite cash_eq. Qed.
  Lemma oblG_progress_eq_list L a0 a1 :
    a0 /= a1 →
    ([∗ list] i ∈ L, oblG_progress i a0)%I ≡ ([∗ list] i ∈ L, oblG_progress i a1)%I.
  Proof. intros. apply big_opL_proper. intros. erewrite oblG_progress_eq; eauto. Qed.
  Lemma oblG_progress_eq_set L a0 a1 :
    a0 /= a1 →
    ([∗ set] i ∈ L, oblG_progress i a0)%I ≡ ([∗ set] i ∈ L, oblG_progress i a1)%I.
  Proof. intros. apply big_opS_proper. intros. erewrite oblG_progress_eq; eauto. Qed.

  Lemma oblG_progress_mon i a0 a1 :
    a0 /≤ a1 →
    oblG_progress i a1 ⊢ |==> oblG_progress i a0.
  Proof.
    intros LE. rewrite /oblG_progress. apply own_update.
    by apply reservation_map_update, cash_update.
  Qed.
  Lemma oblG_progress_mon_list L a0 a1 :
    a0 /≤ a1 →
    ([∗ list] i ∈ L, oblG_progress i a1) ⊢ |==> ([∗ list] i ∈ L, oblG_progress i a0).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblG_progress_mon.
  Qed.
  Lemma oblG_progress_mon_set L a0 a1 :
    a0 /≤ a1 →
    ([∗ set] i ∈ L, oblG_progress i a1) ⊢ |==> ([∗ set] i ∈ L, oblG_progress i a0).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblG_progress_mon.
  Qed.

  Lemma oblG_progress_split i a0 a1 :
    oblG_progress i (a0 /+ a1) ⊣⊢ oblG_progress i a0 ∗ oblG_progress i a1.
  Proof.
    rewrite /oblG_progress. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -cash_add) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite -cash_add). iSplitL "H1"; iFrame.
  Qed.
  Lemma oblG_progress_split_list L a0 a1 :
    ([∗ list] i ∈ L, oblG_progress i (a0 /+ a1)) ⊣⊢ ([∗ list] i ∈ L, oblG_progress i a0) ∗ ([∗ list] i ∈ L, oblG_progress i a1).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oblG_progress_split.
  Qed.
  Lemma oblG_progress_split_set L a0 a1 :
    ([∗ set] i ∈ L, oblG_progress i (a0 /+ a1)) ⊣⊢ ([∗ set] i ∈ L, oblG_progress i a0) ∗ ([∗ set] i ∈ L, oblG_progress i a1).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oblG_progress_split.
  Qed.

  Lemma oblG_progress_mon_split i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    oblG_progress i a2 ⊢ |==> oblG_progress i a0 ∗ oblG_progress i a1.
  Proof.
    intros LE. iIntros "H". iApply oblG_progress_split. iApply oblG_progress_mon; done.
  Qed.
  Lemma oblG_progress_mon_split_list L a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ list] i ∈ L, oblG_progress i a2) ⊢ |==> ([∗ list] i ∈ L, oblG_progress i a0) ∗ ([∗ list] i ∈ L, oblG_progress i a1).
  Proof.
    iIntros (LE) "H". iPoseProof (oblG_progress_mon_list with "H") as ">H"; first done.
    by iApply oblG_progress_split_list.
  Qed.
  Lemma oblG_progress_mon_split_set L a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ set] i ∈ L, oblG_progress i a2) ⊢ |==> ([∗ set] i ∈ L, oblG_progress i a0) ∗ ([∗ set] i ∈ L, oblG_progress i a1).
  Proof.
    iIntros (LE) "H". iPoseProof (oblG_progress_mon_set with "H") as ">H"; first done.
    by iApply oblG_progress_split_set.
  Qed.

  Lemma oblG_progress_lt i a0 a1 :
    a0 /< a1 →
    oblG_progress i a1 ⊢ |==> oblG_progress i a0 ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ oblG_progress i c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (oblG_progress_mon_split _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.
  Lemma oblG_progress_lt_list L a0 a1 :
    a0 /< a1 →
    ([∗ list] i ∈ L, oblG_progress i a1) ⊢ |==> ([∗ list] i ∈ L, oblG_progress i a0 ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ oblG_progress i c).
  Proof.
    iIntros (LT) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblG_progress_lt.
  Qed.
  Lemma oblG_progress_lt_set L a0 a1 :
    a0 /< a1 →
    ([∗ set] i ∈ L, oblG_progress i a1) ⊢ |==> ([∗ set] i ∈ L, oblG_progress i a0 ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ oblG_progress i c).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblG_progress_lt.
  Qed.

  Lemma oblG_progress_supply_mon k a0 a1 q :
    a0 /≤ a1 →
    oblG_progress_supply k a0 q ⊢ |==> oblG_progress_supply k a1 q.
  Proof.
    intros LE. rewrite /oblG_progress_supply. apply own_update.
    by apply reservation_map_update, debt_update.
  Qed.

  Lemma oblG_progress_supply_add i a0 a1 q0 q1 :
    oblG_progress_supply i a0 q0 ∗ oblG_progress_supply i a1 q1
    ⊢ ∃ b, oblG_progress_supply i b (q0 + q1) ∗ ⌜ b /≤ a0 ∧ b /≤ a1 ⌝.
  Proof.
    rewrite /oblG_progress_supply. iIntros "[H1 H2]".
    iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame).
    iEval (rewrite -reservation_map_data_op) in "H".
    destruct (debt_add a0 a1 q0 q1) as (b&Heq&Hle0&Hle1). rewrite Heq.
    iExists _. iSplitL; done.
  Qed.

  Lemma oblG_progress_supply_split i a q0 q1 q :
    q = (q0 + q1)%Qp →
    oblG_progress_supply i a q ⊢ oblG_progress_supply i a q0 ∗ oblG_progress_supply i a q1.
  Proof.
    rewrite /oblG_progress_supply. iIntros (Hq) "H".
    iApply own_op. iEval (rewrite -reservation_map_data_op).
    subst. rewrite debt_split. done.
  Qed.
  Lemma oblG_progress_supply_div_2 k a q :
    oblG_progress_supply k a q ⊢ oblG_progress_supply k a (q/2) ∗ oblG_progress_supply k a (q/2).
  Proof. rewrite oblG_progress_supply_split; first done. by rewrite Qp.div_2. Qed.
  Lemma oblG_progress_supply_dfrac_valid k a q :
    oblG_progress_supply k a q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblG_progress_supply. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    rewrite bank_valid_debt in V. destruct V. auto.
  Qed.

  Lemma oblG_progress_supply_issue i q0 q1 a0 a1 :
    (q0 + q1 = 1)%Qp →
    oblG_progress_supply i a0 (q0 + q1)%Qp ⊢ |==> oblG_progress_supply i (a0 /+ a1) (q0 + q1)%Qp ∗ oblG_progress i a1.
  Proof.
    rewrite /oblG_progress_supply -own_op. intros Heq. apply own_update.
    rewrite -reservation_map_data_op. apply reservation_map_update.
    rewrite Heq. apply debt_owe.
  Qed.
  Lemma oblG_progress_supply_issue_2 i q0 q1 a0 a1 b :
    (q0 + q1 = 1)%Qp →
    oblG_progress_supply i a0 q0 ∗ oblG_progress_supply i a1 q1
    ⊢ |==> oblG_progress_supply i (a0 /+ b) q0 ∗ oblG_progress_supply i (a0 /+ b) q1 ∗ oblG_progress i b.
  Proof.
    iIntros (Heq) "H". iDestruct (oblG_progress_supply_add with "H") as "(%&H&%)".
    iMod (oblG_progress_supply_mon _ _ a0 with "H") as "H".
    { destruct H. auto. }
    iMod (oblG_progress_supply_issue _ _ _ _ b with "H") as "[H Hp]"; first done.
    iDestruct (oblG_progress_supply_split _ _ q0 q1 with "H") as "[H0 H1]"; first done.
    by iFrame.
  Qed.

  Lemma oblG_progress_spend i a0 a1 q :
    oblG_progress_supply i a0 q ∗ oblG_progress i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ oblG_progress_supply i a2 q.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ k, ∃ a2, (k = (debt a2 q)) ∧ (a1 /+ a2 /≤ a0))
                (λ k, ∃ a2, (k = {[i := (debt a2 q)]}) ∧ (a1 /+ a2 /≤ a0))
             ).
      { eapply debt_pay. }
      { intros. destruct H as (a2&A0&A1). eexists. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplitR; done.
  Qed.
  Lemma oblG_progress_spend_2 i a0 a1 q0 q1 c :
    oblG_progress_supply i a0 q0 ∗ oblG_progress_supply i a1 q1 ∗ oblG_progress i c
    ⊢ |==> ∃ a2, ⌜(c /+ a2) /≤ a0 ∧ (c /+ a2) /≤ a1⌝ ∗ oblG_progress_supply i a2 q0 ∗ oblG_progress_supply i a2 q1.
  Proof.
    iIntros "(H0&H1&H2)". iDestruct (oblG_progress_supply_add with "[H0 H1]") as "(%&H&%)"; first iFrame.
    iMod (oblG_progress_spend with "[H H2]") as "(%&%&H)"; first iFrame.
    iDestruct (oblG_progress_supply_split with "H") as "[H0 H1]"; first reflexivity.
    iModIntro. iFrame. iPureIntro. destruct H. split.
    - etransitivity; [eapply H0 | eauto].
    - etransitivity; [eauto | eapply H].
  Qed.

  Lemma oblG_progress_alloc D k a :
    k ∉ D →
    (own progress_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own progress_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           oblG_progress_supply k a 1 ∗ oblG_progress k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (debt a 1 ⋅ cash a) with "Htk") as "[Htk >H]"; auto.
    { rewrite bank_valid_debt_cash. done. }
    iDestruct "H" as "[H1 H2]". rewrite /oblG_progress_supply /oblG_progress.
    by iFrame.
  Qed.

  (* (** Progress bound rules *) *)
  (* Lemma oblG_bound_auth_alloc D k a : *)
  (*   k ∉ D → *)
  (*   (own bound_name (reservation_map_token (A:=auth_mraUR (wfocm_geR)) (⊤ ∖ gset_to_coPset D))) *)
  (*   ⊢ |==> (own bound_name (reservation_map_token (A:=auth_mraUR (wfocm_geR)) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗ *)
  (*          oblG_bound_auth k a. *)
  (* Proof. *)
  (*   iIntros (Hk) "Htk". *)
  (*   iPoseProof (reservation_map_token_alloc_singleton _ _ k (●AM[wfocm_geR] a) with "Htk") as "[Htk >H]"; auto. *)
  (*   - apply auth_mra_auth_valid. *)
  (*   - rewrite /oblG_bound_auth. by iFrame. *)
  (* Qed. *)

  (* Lemma oblG_bound_know k a : *)
  (*   oblG_bound_auth k a ⊢ oblG_bound k a. *)
  (* Proof. *)
  (*   rewrite /oblG_bound_auth /oblG_bound. rewrite auth_mra_auth_know_op. *)
  (*   rewrite reservation_map_data_op. iIntros "[H1 H2]". iFrame. *)
  (* Qed. *)

  (* Lemma oblG_bound_know_bound k a0 a1 : *)
  (*   oblG_bound_auth k a0 ∗ oblG_bound k a1 ⊢ ⌜ a0 /≤ a1 ⌝. *)
  (* Proof. *)
  (*   rewrite /oblG_bound_auth /oblG_bound -own_op -reservation_map_data_op. *)
  (*   iIntros "H". iPoseProof (own_valid with "H") as "%V". apply reservation_map_data_valid in V. *)
  (*   apply (auth_mra_both_valid wfocm_geR) in V. done. *)
  (* Qed. *)

  (* Lemma oblG_bound_auth_mon k a0 a1 : *)
  (*   a1 /≤ a0 → *)
  (*   oblG_bound_auth k a0 ⊢ |==> oblG_bound_auth k a1. *)
  (* Proof. iIntros (Ha). apply own_update, reservation_map_update, auth_mra_update; eauto. apply _. Qed. *)

  (* Lemma oblG_bound_mon k a0 a1 : *)
  (*   a0 /≤ a1 → *)
  (*   oblG_bound k a0 ⊢ oblG_bound k a1. *)
  (* Proof. iIntros (Ha). apply own_mono, reservation_map_data_mono, auth_mra_know_mono; eauto. apply _. Qed. *)

  (** Owner rules *)
  Lemma oblG_owner_agree k θ0 θ1 q0 q1 :
    oblG_owner k θ0 q0 ∗ oblG_owner k θ1 q1 ⊢ ⌜ θ0 = θ1 ∧ (q0 + q1 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblG_owner. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    apply frac_agree_op_valid in Hv. iPureIntro. destruct Hv. done.
  Qed.

  Lemma oblG_owner_frac_op k θ q0 q1 q :
    q = (q0 + q1)%Qp →
    oblG_owner k θ q0 ∗ oblG_owner k θ q1 ⊣⊢ oblG_owner k θ q.
  Proof.
    intros; subst. rewrite /oblG_owner. iSplit; [iIntros "[H1 H2]" | iIntros "H"].
    - iCombine "H1 H2" as "H". rewrite frac_agree_op. done.
    - rewrite frac_agree_op. iDestruct "H" as "[H1 H2]". iFrame.
  Qed.
  Lemma oblG_owner_div_2 k θ q :
    oblG_owner k θ (q/2) ∗ oblG_owner k θ (q/2) ⊣⊢ oblG_owner k θ q.
  Proof. rewrite oblG_owner_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma oblG_owner_valid k θ q :
    oblG_owner k θ q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblG_owner. iIntros "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    by iApply (frac_agree_validI).
  Qed.

  Lemma oblG_owner_update_2 k θ0 θ1 q0 q1 θ :
    (q0 + q1 = 1)%Qp →
    oblG_owner k θ0 q0 ∗ oblG_owner k θ1 q1 ⊢ |==> oblG_owner k θ q0 ∗ oblG_owner k θ q1.
  Proof.
    rewrite /oblG_owner -!own_op -!reservation_map_data_op.
    intros Heq. by apply own_update, reservation_map_update, frac_agree_update_2.
  Qed.
  Lemma oblG_owner_update k θ0 θ1 :
    oblG_owner k θ0 1 ⊢ |==> oblG_owner k θ1 1.
  Proof.
    iIntros "H". iPoseProof (oblG_owner_div_2 with "H") as "[H1 H2]".
    iMod (oblG_owner_update_2 _ _ _ _ _ θ1 with "[H1 H2]") as "[H1 H2]"; [| iFrame |].
    { by rewrite Qp.div_2. }
    iCombine "H1 H2" as "H". by iPoseProof (oblG_owner_div_2 with "H") as "H".
  Qed.

  Lemma oblG_owner_alloc D k θ :
    k ∉ D →
    (own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO T)) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO T)) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           oblG_owner k θ 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (to_frac_agree 1 (θ : leibnizO _)) with "Htk") as "[Htk >H]"; auto.
    { done. }
    rewrite /oblG_owner. by iFrame.
  Qed.

  (** owitness rules *)
  Lemma owitness_elem k Ω :
    owitness Ω ∗ oblG_elem k ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /owitness -!lock. iIntros "(Hsat & He)".
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (oblG_elem_elem with "[$]") as "%".
    done.
  Qed.
  Lemma owitness_goal_elem k P R Ω :
    owitness Ω ∗ oblG_goal k P R ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /owitness -!lock. iIntros "(Hsat & He)".
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (oblG_goal_elem with "[$]") as "%".
    by rewrite -Hdom.
  Qed.
  Lemma owitness_elem_cases Ω k :
    owitness Ω ∗ oblG_elem k ⊢ ⌜ ∃ d, Ω !! k = Some (obl_live d) ⌝ ∨ oblG_done k.
  Proof.
    iIntros "(Hsat & He)". iPoseProof (owitness_elem with "[$]") as "%".
    apply elem_of_dom in H. destruct H.
    rewrite /owitness -!lock.
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    destruct x.
    - iLeft. eauto.
    - iPoseProof (big_sepM_delete _ _ _ _ H with "Hm") as "[H _]".
      iDestruct "H" as "(%&%&_&_&_&DA&_)". iRight. by iApply oblG_done_auth_done.
  Qed.

  Lemma owitness_obl_is_live Ω k q :
    owitness Ω ∗ oblG_elem k ∗ oblG_live k q
    ⊢ ∃ d, ⌜Ω !! k = Some (obl_live d)⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (owitness_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExists o. done.
    - iExFalso. iDestruct "LU" as "(% & % & _ & _ & _ & DONE & _)".
      iPoseProof (oblG_live_done_false with "[Hl DONE]") as "%F"; [iFrame | done].
      iPoseProof (oblG_done_auth_done with "[$]") as "#D". done.
  Qed.
  Lemma owitness_obl_is_live_olive Ω k q :
    owitness Ω ∗ oblG_elem k ∗ oblG_live k q
    ⊢ ∃ θ α, ⌜Ω !! k = Some (olive θ α)⌝.
  Proof.
    iIntros "H". iPoseProof (owitness_obl_is_live with "H") as "(%&%)".
    iPureIntro. destruct d. eauto.
  Qed.

  Lemma owitness_obl_is_done Ω k (P : prop_of ps) R :
    owitness Ω ∗ oblG_goal k P R ∗ oblG_done k
    ⊢ ∃ P', ⌜Ω !! k = Some (odone P') ∧ P' ≡ P⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (owitness_goal_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExFalso. iDestruct "LU" as "(LIVE & _)".
      iPoseProof (oblG_live_done_false with "[LIVE Hl]") as "%F"; [iFrame | done].
    - iPoseProof (oblG_goal_lookup with "[$]") as "(%&%&%&%&_)".
      iDestruct "LU" as "(%&%&Hg2&%&_)". iPoseProof (oblG_goal_agree with "[He Hg2]") as "[% HR]".
      { iFrame "Hg2". eauto. }
      subst. iPureIntro. exists (obl_atom o). destruct o. rewrite -H2 /odone. simpl. split; eauto.
  Qed.

  Lemma owitness_obl_is_done_weak Ω k :
    owitness Ω ∗ oblG_elem k ∗ oblG_done k
    ⊢ ∃ P, ⌜Ω !! k = Some (obl_done P)⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (owitness_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExFalso. iDestruct "LU" as "(LIVE & _)".
      iPoseProof (oblG_live_done_false with "[LIVE Hl]") as "%F"; [iFrame | done].
    - iExists o. done.
  Qed.
  Lemma owitness_obl_is_done_weak_set Ω D :
    owitness Ω ∗ ([∗ set] k ∈ D, oblG_elem k ∗ oblG_done k)
    ⊢ [∗ set] k ∈ D, ⌜ ∃ P, Ω !! k = Some (obl_done P) ⌝.
  Proof.
    revert Ω. pattern D. revert D. apply set_ind.
    { solve_proper. }
    { iIntros (Ω) "[Hsat Hs]". rewrite big_opS_empty. done. }
    iIntros (k D NIN IH Ω) "[Hsat Hs]". rewrite !big_sepS_union; [|set_solver|set_solver].
    rewrite !big_sepS_singleton. iDestruct "Hs" as "[[Hi1 Hi2] Hs]".
    iPoseProof (owitness_obl_is_done_weak with "[Hsat Hi1 Hi2]") as "[% %]"; first iFrame. iSplitR.
    - iPureIntro. exists P. done.
    - iApply IH. iFrame.
  Qed.

  Lemma owitness_alloc_obl Ω θ α P R :
    owitness Ω
    ⊢ |==> ∃ k, ⌜Ω !! k = None⌝ ∗ owitness (<[k:=olive θ α]>Ω) ∗
                oblG_goal k P R ∗
                oblG_elem k ∗
                oblG_live k (1/2)%Qp ∗
                oblG_owner k θ (1/2)%Qp ∗
                oblG_progress k α.
  Proof.
    iIntros "Hsat".
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    assert (∃ k, k ∉ dom Ω).
    { exists (fresh (dom Ω)). apply is_fresh. }
    destruct H as [k Hk].
    iMod (own_update with "HG") as "[HG Hg]".
    { eapply (gmap_view_alloc _ k DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)); try done.
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; [done | set_solver].
    }
    iMod (oblG_live_alloc _ k with "HS") as "[HS Hs]"; first done.
    iMod (oblG_owner_alloc _ k θ with "HO") as "[HO Ho]"; first done.
    iMod (oblG_progress_alloc _ k α with "HP") as "(HP & Hps & Hp)"; first done.
    iPoseProof (oblG_live_div_2 with "Hs") as "[Hs1 Hs2]".
    iPoseProof (oblG_owner_div_2 with "Ho") as "[Ho1 Ho2]".
    iMod (oblG_elem_alloc _ k (olive θ α) with "HE") as "[HE He]"; first (by apply not_elem_of_dom).
    iModIntro. iExists k. rewrite /oblG_goal. iFrame "Hg Hs2 Hp He Ho2".
    iSplitR.
    { iPureIntro. by apply not_elem_of_dom. }
    rewrite -!lock. iSplitL "HG".
    { iExists (<[k:=(P, R)]>OProp). iSplitR.
      - iPureIntro. set_solver.
      - rewrite fmap_insert. done.
    }
    rewrite dom_insert_L. iFrame "HS HO HP HE".
    iApply big_sepM_insert.
    { by apply not_elem_of_dom_1. }
    iFrame. eauto.
  Qed.

  Lemma owitness_obl_progress_one Ω k θ α c :
    (Ω !! k = Some (olive θ α)) →
    (/0 /< c) →
    owitness Ω ∗ oblG_progress k c
    ⊢ |==> ∃ α', owitness (<[k:=olive θ α']>Ω) ∗
              ⌜ obl_state_progress (olive θ α) (olive θ α') ⌝.
  Proof.
    intros LU Hc. iIntros "(Hsat & Hp)".
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[Hk Hm]"; [eapply LU |].
    iDestruct "Hk" as "(Hs& Ho& (%&%&Hps))".
    iMod (oblG_progress_spend _ α0 with "[$Hps $Hp]") as "(%&%&Hps)".
    assert (LT : a2 /< α0).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (olive θ a2)) with "[Hm Hs Ho Hps]") as "Hm".
    { apply lookup_delete_eq. }
    { iFrame "Hm". iFrame. simpl. done. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HS HE HP".
    rewrite insert_delete_eq. iFrame. simpl; iPureIntro; split_and !; auto.
    eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma owitness_obl_resolve_one Ω k P R x0 :
    owitness Ω ∗ oblG_elem k ∗ oblG_goal k P R ∗ (▷ R) ∗
    oblG_live k (1/2)%Qp ∗
    oblG_owner k x0 (1/2)%Qp
    ⊢ |==> owitness (<[k:=odone P]>Ω) ∗ oblG_done k.
  Proof.
    iIntros "(Hsat & #He & #Hg & HR & Hs0 & Ho0)".
    iDestruct (owitness_obl_is_live with "[Hsat He Hs0]") as "(%&%LU)".
    { iFrame. eauto. }
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[Hk Hm]"; [eapply LU |].
    iDestruct "Hk" as "(Hs& Ho& (%&%&Hps))".
    iMod (oblG_live_to_done with "[Hs Hs0]") as "Hs".
    { iApply oblG_live_frac_op; last iFrame. by rewrite Qp.div_2. }
    iPoseProof (oblG_done_auth_done with "Hs") as "#Hsd".
    iPoseProof (oblG_owner_agree with "[Ho Ho0]") as "%"; first iFrame.
    destruct H0. clear H1. subst x0.
    iCombine "Ho Ho0" as "Ho". iPoseProof (oblG_owner_frac_op with "Ho") as "Ho".
    { by rewrite Qp.div_2. }
    iModIntro.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (odone P)) with "[Hm Hs Ho Hps HR]") as "Hm".
    { apply lookup_delete_eq. }
    { iFrame "Hm". iFrame. eauto. }
    rewrite dom_insert_lookup_L; last done. iFrame "HS HP".
    rewrite insert_delete_eq. iFrame. eauto.
  Qed.

  Lemma owitness_done_open Ω k P R :
    owitness Ω ∗ oblG_goal k P R ∗ oblG_done k
    ⊢ (▷ R) ∗ (▷ R -∗ owitness Ω).
  Proof.
    iIntros "(Hsat & #Hg0 & #Hs0)".
    iPoseProof (owitness_obl_is_done with "[Hsat]") as "%Hdone"; [iFrame; eauto|].
    destruct Hdone as (?&LU&HP).
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iDestruct (big_sepM_delete _ _ k _ LU with "Hm") as "[Hk Hm]".
    iDestruct "Hk" as "( %&% & #Hg & %HPeq & HR & Hsa & %& Hps)".
    iPoseProof (oblG_goal_agree with "[Hg Hg0]") as "(%Hpeq1 & HReq)".
    { iSplit; [iFrame "Hg" | iFrame "Hg0"]. }
    iSplitL "HR".
    { iNext. by iRewrite "HReq" in "HR". }
    iIntros "HR". iFrame "HS HP HG".
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (odone x)) with "[Hm Hsa Hps HR]") as "Hm".
    { apply lookup_delete_eq. }
    { iFrame "Hm". iFrame. iExists P. eauto. }
    rewrite insert_delete_eq insert_id; last done. iFrame. eauto.
  Qed.

  Lemma owitness_done_open_pers Ω k P R :
    Persistent R →
    owitness Ω ∗ oblG_goal k P R ∗ oblG_done k
    ⊢ owitness Ω ∗ ▷ R.
  Proof.
    iIntros (PP) "H". iPoseProof (owitness_done_open with "H") as "[#HP Ho]".
    iSplitL; [|done]. iApply "Ho". done.
  Qed.

  Lemma owitness_live_open_owner Ω k q :
    owitness Ω ∗ oblG_elem k ∗ oblG_live k q
    ⊢ ∃ i, oblG_live k q ∗ oblG_live k (1/2)%Qp ∗ oblG_owner k i (1/2) ∗
           ((oblG_live k (1/2)%Qp ∗ oblG_owner k i (1/2)) -∗ owitness Ω).
  Proof.
    iIntros "(Hsat & #He0 & Hs0)".
    iPoseProof (owitness_obl_is_live with "[Hsat Hs0]") as "%Hlive"; [iFrame; eauto|].
    destruct Hlive as (?&LU).
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS&HO&HP&HE & Hm)".
    iDestruct (big_sepM_delete _ _ k _ LU with "Hm") as "[Hk Hm]".
    iDestruct "Hk" as "( Hs & Ho & (%&%&Hps) )".
    iFrame "Hs0 Hs Ho". iIntros "[Hs Ho]". iFrame "HG HS HO HP HE". iSplitR; first done.
    iApply (big_sepM_delete _ _ k _ LU). iFrame. done.
  Qed.
  Lemma owitness_live_open Ω k q :
    owitness Ω ∗ oblG_elem k ∗ oblG_live k q
    ⊢ oblG_live k q ∗ oblG_live k (1/2)%Qp ∗ (oblG_live k (1/2)%Qp -∗ owitness Ω).
  Proof.
    iIntros "(Hsat & #He0 & Hs0)".
    iPoseProof (owitness_live_open_owner with "[$]") as "(%&Bl&Bl2&Bo&S)". iFrame.
    iIntros "Bl". iApply "S". iFrame.
  Qed.

  Lemma owitness_lookup_owner Ω k τ q :
    owitness Ω ∗ oblG_elem k ∗ oblG_owner k τ q ⊢ ∃ d, ⌜ Ω !! k = Some (obl_live d) ∧ obl_owner d = τ ⌝.
  Proof.
    iIntros "(Hsat & #Hek1 & Hok)".
    iPoseProof (owitness_elem k with "[Hsat]") as "%Helem"; first iFrame; eauto.
    apply elem_of_dom in Helem. destruct Helem as [o LU].
    rewrite /owitness -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS&HO&HP&HE & Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[Hk Hm]"; [eapply LU |].
    destruct o.
    - iDestruct "Hk" as "( Hs & Ho & (%&%&Hps) )".
      iPoseProof (oblG_owner_agree with "[Hok Ho]") as "%"; first iFrame. destruct H0.
      iExists o. iPureIntro. split; auto.
    - iDestruct "Hk" as "( %&% & #Hg & %HPeq & HR & Hsa & %&%& Ho & Hps)".
      iPoseProof (oblG_owner_agree with "[Hok Ho]") as "%"; first iFrame. destruct H.
      exfalso. apply Qp.not_add_le_l in H0. auto.
  Qed.

End owitness.

(* Allocation of an initial obligation protocol. *)
Lemma owitness_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!owitnessGpreS ps T Σ}
  `{obl_live_class A T WFOCM.ltR} `{obl_done_class ps} :
  ⊢ |==> ∃ _ : owitnessGS ps T Σ, owitness ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id (prodR _ _))) as (γG) "HG";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=dfrac_agreeR (leibnizO T))⊤)) as (γO) "HO";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bankUR) ⊤)) as (γC) "HC";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id unitUR)) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OwitnessG SI _ WFA _ _ _ _ γG γS γO γC γE).
  rewrite /owitness -lock.
  iSplitL "HG"; first (iExists ∅; by iFrame).
  replace (⊤ ∖ gset_to_coPset (dom (∅ : obl_states))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
