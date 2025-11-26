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
            ∃ α, (⌜ WFOCM.leR (wit_progress d) α ⌝) ∗ owitnessG_credit k α
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
                 | inl d, inl e => WFOCM.leR (wit_progress e) (ξ (obl_progress d))
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

  Lemma owitnessG_credit_spend i a0 a1 :
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

  Lemma owitnessG_compare i a0 a1 :
    owitnessG_witness i a0 ∗ owitnessG_credit i a1 ⊢ |==> ⌜ a1 /≤ a0 ⌝.
  Proof.
    rewrite -own_op -reservation_map_data_op. iIntros "H".
    iPoseProof (own_valid with "H") as "%". apply reservation_map_data_valid in H0.
    apply credit_bound_credit_valid_compare in H0. done.
  Qed.

  Lemma owitnessG_credit_alloc D k a :
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

  TODO

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
