From iris.algebra Require Import gmap_view reservation_map dfrac_agree mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Export wfocm.
From liris.base_logic Require Export obligation.
From liris.algebra Require Import auth_mra bank.

Section aux.
  (* Maybe move to somewhere *)
  Context `{SI : indexT} {Σ : gFunctors} {A : cmra} {GA : inG Σ A} {GR : inG Σ (reservation_mapR A)}.

  Lemma reservation_map_token_alloc_singleton (name : gname) D k a :
    k ∉ D →
    ✓ a →
    (own name (reservation_map_token (A:=A) (⊤ ∖ gset_to_coPset D)))
    ⊢ (own name (reservation_map_token (A:=A) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
        |==> (own name (reservation_map_data k a)).
  Proof.
    iIntros (Hk Ha) "Htk". rewrite (reservation_map_token_difference (gset_to_coPset {[k]}) (⊤ ∖ gset_to_coPset D)); cycle 1.
    { apply elem_of_subseteq. intros. rewrite elem_of_difference. split; first set_solver.
      intro F. rewrite !elem_of_gset_to_coPset in H F. set_solver.
    }
    iDestruct "Htk" as "[Htk H]".
    assert (⊤ ∖ gset_to_coPset D ∖ gset_to_coPset {[k]} = ⊤ ∖ gset_to_coPset ({[k]} ∪ D)).
    { apply leibniz_equiv. intros x. rewrite !elem_of_difference. split; intros.
      - destruct H as ((_&?)&?). split; first set_solver. intros F. apply elem_of_gset_to_coPset, elem_of_union in F.
        destruct F; [apply H0 | apply H]; apply elem_of_gset_to_coPset; set_solver.
      - destruct H as (_&?). split; first (split; first set_solver);
          intros F; apply elem_of_gset_to_coPset in F; apply H, elem_of_gset_to_coPset; set_solver.
    }
    rewrite H. iFrame "H".
    iMod (own_update with "Htk") as "H".
    { eapply (reservation_map_alloc _ k a); auto. apply elem_of_gset_to_coPset; set_solver. }
    by iFrame.
  Qed.

End aux.

Definition obl_idO `{SI : indexT} := leibnizO obl_id.

(** The ghost state for liveness obligations *)
Module osatGS.

  Class osatGpreS `{SI : indexT} `{WF : WFOCM.pack A} (ps : Type) (Σ : gFunctors) : Set :=
    OsatGpreS {
        osatGpreS_goal : inG Σ (gmap_viewR obl_id (prodR (agreeR $ (prop_ofO ps)) (agreeR $ (laterO (iPropO Σ)))));
        osatGpreS_status : inG Σ (reservation_mapUR mono_natUR);
        osatGpreS_progress : inG Σ (reservation_mapUR bankUR);
        osatGpreS_elem : inG Σ (gmap_viewR obl_id unitUR);
      }.

  Class osatGS `{SI : indexT} `{WF : WFOCM.pack A} (ps : Type) (Σ : gFunctors) : Set :=
    OsatG {
        osat_inG : osatGpreS ps Σ;
        goal_name : gname;
        status_name : gname;
        progress_name : gname;
        elem_name : gname;
      }.

  Definition osatΣ `{SI : indexT} `{WF : WFOCM.pack A} (ps : Type) : gFunctors :=
    #[GFunctor (gmap_viewTRF obl_id (prodTRF (agreeTRF $ (prop_ofO ps)) (agreeTRF $ (laterTF idTF))));
      GFunctor (reservation_mapUR mono_natUR);
      GFunctor (reservation_mapUR bankUR);
      GFunctor (gmap_viewR positive unitUR)
      ].

  Global Instance subG_osatΣ `{SI : indexT} `{WF : WFOCM.pack A} {ps : Type} {Σ} : subG (osatΣ ps) Σ → (osatGpreS ps Σ).
  Proof. solve_inG. Qed.

End osatGS.
Import osatGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances osat_inG osatGpreS_goal osatGpreS_status osatGpreS_progress osatGpreS_elem.

(* Goal *)
Definition goal_unfold `{SI : indexT} {Σ} (R : iProp Σ) : later (iProp Σ) := Next R.
Definition oblG_goal `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (k : obl_id) (P : prop_of ps) (R : iProp Σ) : iProp Σ :=
  own goal_name (gmap_view_frag k DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)).
Global Typeclasses Opaque oblG_goal.
Global Instance: Params (@goal_unfold) 2 := {}.
Global Instance: Params (@oblG_goal) 7 := {}.

(* Elem *)
Definition oblG_elem `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (k : obl_id) : iProp Σ :=
  own elem_name (gmap_view_frag k DfracDiscarded ()).
Global Typeclasses Opaque oblG_elem.
Global Instance: Params (@oblG_elem) 7 := {}.

(* Status: live or done *)
Definition oblG_live `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (k : obl_id) (q : Qp) : iProp Σ :=
  own status_name (reservation_map_data k (●MN{#q} 0)).
Global Typeclasses Opaque oblG_live.
Global Instance: Params (@oblG_live) 7 := {}.

Definition oblG_done_auth `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (k : obl_id) : iProp Σ :=
  own status_name (reservation_map_data k (●MN 1)).
Global Typeclasses Opaque oblG_done_auth.
Global Instance: Params (@oblG_done_auth) 7 := {}.

Definition oblG_done `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (k : obl_id) : iProp Σ :=
  own status_name (reservation_map_data k (◯MN 1)).
Global Typeclasses Opaque oblG_done.
Global Instance: Params (@oblG_done) 7 := {}.

(* Progress: manage credits for logical progress *)
Definition oblG_progress `{SI : indexT} `{WFOCM.pack A} `{!osatGS ps Σ} (k : obl_id) (α : A) : iProp Σ :=
  own progress_name (reservation_map_data k (cash α)).
Global Typeclasses Opaque oblG_progress.
Global Instance: Params (@oblG_progress) 7 := {}.

Definition oblG_progress_supply `{SI : indexT} `{WF : WFOCM.pack A} `{!osatGS ps Σ} (k : obl_id) (α : A) (q : Qp) : iProp Σ :=
  own progress_name (reservation_map_data k (debt α q)).
Global Typeclasses Opaque oblG_progress_supply.
Global Instance: Params (@oblG_progress_supply) 7 := {}.

(* Global invariant for the obligation ghost state. *)
Definition osat `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGS ps Σ}
  `{obl_live_class A WFOCM.ltR} `{obl_done_class ps}
  (Ω : obl_states) : iProp Σ :=
  locked
    ((∃ (OProp : gmap obl_id (prop_of ps * iProp Σ)),
         (⌜ dom OProp = dom Ω ⌝) ∗
         own goal_name (gmap_view_auth (DfracOwn 1) ((λ '(P, R), (to_agree P, to_agree $ (goal_unfold R))) <$> OProp))) ∗
     (own status_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own progress_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom Ω)))) ∗
     ([∗ map] k ↦ o ∈ Ω,
        match o with
        | inl d =>
            oblG_live k (1/2)%Qp ∗
            (∃ α, ⌜ WFOCM.leR α (obl_progress d) ⌝ ∗ oblG_progress_supply k α (1/2)%Qp)
        | inr d =>
            let P1 := (obl_atom d) in
            ∃ P2 R, oblG_goal k P2 R ∗ ⌜ P1 ≡ P2 ⌝ ∗ ▷ R ∗
                    oblG_done_auth k ∗ ∃ α, oblG_progress_supply k α 1
        end)
    )%I.

(** Properties *)
Section osat.
  Context `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGS ps Σ}.
  Context `{Ξl : obl_live_class A WFOCM.ltR} `{Ξd : obl_done_class ps}.

  Local Instance goal_unfold_contractive : Contractive (@goal_unfold SI Σ).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_contractive k P : Contractive (@oblG_goal SI _ WFA ps Σ _ k P).
  Proof. solve_contractive. Qed.
  Global Instance oblG_goal_persistent k P R : Persistent (oblG_goal k P R).
  Proof. rewrite /oblG_goal. apply _. Qed.
  Global Instance oblG_elem_persistent k : Persistent (oblG_elem k).
  Proof. rewrite /oblG_elem. apply _. Qed.
  Global Instance oblG_done_persistent k : Persistent (oblG_done k).
  Proof. rewrite /oblG_done. apply _. Qed.

  Global Instance oblG_elem_timeless k : Timeless (oblG_elem k).
  Proof. rewrite /oblG_elem. apply _. Qed.
  Global Instance oblG_live_timeless k q : Timeless (oblG_live k q).
  Proof. rewrite /oblG_live. apply _. Qed.
  Global Instance oblG_done_timeless k : Timeless (oblG_done k).
  Proof. rewrite /oblG_done. apply _. Qed.
  Global Instance oblG_progress_timeless k b : Timeless (oblG_progress k b).
  Proof. rewrite /oblG_progress. apply _. Qed.

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

  (** osat rules *)
  Lemma osat_elem k Ω :
    osat Ω ∗ oblG_elem k ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /osat -!lock. iIntros "(Hsat & He)".
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    iPoseProof (oblG_elem_elem with "[$]") as "%".
    done.
  Qed.
  Lemma osat_goal_elem k P R Ω :
    osat Ω ∗ oblG_goal k P R ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /osat -!lock. iIntros "(Hsat & He)".
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    iPoseProof (oblG_goal_elem with "[$]") as "%".
    by rewrite -Hdom.
  Qed.
  Lemma osat_elem_cases Ω k :
    osat Ω ∗ oblG_elem k ⊢ ⌜ ∃ d, Ω !! k = Some (obl_live d) ⌝ ∨ oblG_done k.
  Proof.
    iIntros "(Hsat & He)". iPoseProof (osat_elem with "[$]") as "%".
    apply elem_of_dom in H. destruct H.
    rewrite /osat -!lock.
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    destruct x.
    - iLeft. eauto.
    - iPoseProof (big_sepM_delete _ _ _ _ H with "Hm") as "[H _]".
      iDestruct "H" as "(%&%&_&_&_&DA&_)". iRight. by iApply oblG_done_auth_done.
  Qed.

  Lemma osat_obl_is_live Ω k q :
    osat Ω ∗ oblG_elem k ∗ oblG_live k q
    ⊢ ∃ d, ⌜Ω !! k = Some (obl_live d)⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (osat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExists o. done.
    - iExFalso. iDestruct "LU" as "(% & % & _ & _ & _ & DONE & _)".
      iPoseProof (oblG_live_done_false with "[Hl DONE]") as "%F"; [iFrame | done].
      iPoseProof (oblG_done_auth_done with "[$]") as "#D". done.
  Qed.
  Lemma osat_obl_is_live_olive Ω k q :
    osat Ω ∗ oblG_elem k ∗ oblG_live k q
    ⊢ ∃ α, ⌜Ω !! k = Some (olive α)⌝.
  Proof.
    iIntros "H". iPoseProof (osat_obl_is_live with "H") as "(%&%)".
    iPureIntro. destruct d. eauto.
  Qed.

  Lemma osat_obl_is_done Ω k (P : prop_of ps) R :
    osat Ω ∗ oblG_goal k P R ∗ oblG_done k
    ⊢ ∃ P', ⌜Ω !! k = Some (odone P') ∧ P' ≡ P⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (osat_goal_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExFalso. iDestruct "LU" as "(LIVE & _)".
      iPoseProof (oblG_live_done_false with "[LIVE Hl]") as "%F"; [iFrame | done].
    - iPoseProof (oblG_goal_lookup with "[$]") as "(%&%&%&%&_)".
      iDestruct "LU" as "(%&%&Hg2&%&_)". iPoseProof (oblG_goal_agree with "[He Hg2]") as "[% HR]".
      { iFrame "Hg2". eauto. }
      subst. iPureIntro. exists (obl_atom o). destruct o. rewrite -H2 /odone. simpl. split; eauto.
  Qed.

  Lemma osat_obl_is_done_weak Ω k :
    osat Ω ∗ oblG_elem k ∗ oblG_done k
    ⊢ ∃ P, ⌜Ω !! k = Some (obl_done P)⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (osat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExFalso. iDestruct "LU" as "(LIVE & _)".
      iPoseProof (oblG_live_done_false with "[LIVE Hl]") as "%F"; [iFrame | done].
    - iExists o. done.
  Qed.
  Lemma osat_obl_is_done_weak_set Ω D :
    osat Ω ∗ ([∗ set] k ∈ D, oblG_elem k ∗ oblG_done k)
    ⊢ [∗ set] k ∈ D, ⌜ ∃ P, Ω !! k = Some (obl_done P) ⌝.
  Proof.
    revert Ω. pattern D. revert D. apply set_ind.
    { solve_proper. }
    { iIntros (Ω) "[Hsat Hs]". rewrite big_opS_empty. done. }
    iIntros (k D NIN IH Ω) "[Hsat Hs]". rewrite !big_sepS_union; [|set_solver|set_solver].
    rewrite !big_sepS_singleton. iDestruct "Hs" as "[[Hi1 Hi2] Hs]".
    iPoseProof (osat_obl_is_done_weak with "[Hsat Hi1 Hi2]") as "[% %]"; first iFrame. iSplitR.
    - iPureIntro. exists P. done.
    - iApply IH. iFrame.
  Qed.

  Lemma osat_alloc_obl Ω α P R :
    osat Ω
    ⊢ |==> ∃ k, ⌜Ω !! k = None⌝ ∗ osat (<[k:=olive α]>Ω) ∗
                oblG_goal k P R ∗
                oblG_elem k ∗
                oblG_live k (1/2)%Qp ∗
                oblG_progress_supply k α (1/2)%Qp ∗ oblG_progress k α.
  Proof.
    iIntros "Hsat".
    rewrite /osat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    assert (∃ k, k ∉ dom Ω).
    { exists (fresh (dom Ω)). apply is_fresh. }
    destruct H as [k Hk].
    iMod (own_update with "HG") as "[HG Hg]".
    { eapply (gmap_view_alloc _ k DfracDiscarded (to_agree $ P, to_agree $ goal_unfold R)); try done.
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; [done | set_solver].
    }
    iMod (oblG_live_alloc _ k with "HS") as "[HS Hs]"; first done.
    iMod (oblG_progress_alloc _ k α with "HP") as "(HP & Hps & Hp)"; first done.
    iPoseProof (oblG_live_div_2 with "Hs") as "[Hs1 Hs2]".
    iPoseProof (oblG_progress_supply_div_2 with "Hps") as "[Hps1 Hps2]".
    iMod (oblG_elem_alloc _ k (olive α) with "HE") as "[HE He]"; first (by apply not_elem_of_dom).
    iModIntro. iExists k. rewrite /oblG_goal. iFrame "Hg Hs2 Hps2 Hp He".
    iSplitR.
    { iPureIntro. by apply not_elem_of_dom. }
    rewrite -!lock. iSplitL "HG".
    { iExists (<[k:=(P, R)]>OProp). iSplitR.
      - iPureIntro. set_solver.
      - rewrite fmap_insert. done.
    }
    rewrite dom_insert_L. iFrame "HS HP HE".
    iApply big_sepM_insert.
    { by apply not_elem_of_dom_1. }
    iFrame. eauto.
  Qed.

  Lemma osat_obl_progress_one Ω k α c x0 q :
    (Ω !! k = Some (olive α)) →
    (/0 /< c) →
    osat Ω ∗ oblG_progress k c ∗ oblG_progress_supply k x0 q
    ⊢ |==> ∃ α', osat (<[k:=olive α']>Ω) ∗
                 ⌜ obl_state_progress (olive α) (olive α') ∧ α' /< x0  ⌝ ∗
                 oblG_progress_supply k α' q.
  Proof.
    intros LU Hc. iIntros "(Hsat & Hp & Hps0)".
    rewrite /osat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[Hk Hm]"; [eapply LU |].
    iDestruct "Hk" as "(Hs& (%&%&Hps))".
    iMod (oblG_progress_spend_2 _ α0 with "[Hps Hps0 Hp]") as "(%&%&Hps&Hps0)"; first iFrame. destruct H0 as [Hc1 Hc2].
    assert (LT : a2 /< α0).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iModIntro. iExists a2. 
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (olive a2)) with "[Hm Hs Hps]") as "Hm".
    { apply lookup_delete_eq. }
    { iFrame "Hm". iFrame. simpl. done. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HS HE HP".
    rewrite insert_delete_eq. iFrame. simpl; iPureIntro; split_and !; auto.
    - eapply WFOCM.lt_le_lt; eauto.
    - eapply WFOCM.lt_exists_right; eauto.
  Qed.

  Lemma osat_obl_resolve_one Ω k P R x0 :
    osat Ω ∗ oblG_elem k ∗ oblG_goal k P R ∗ (▷ R) ∗
    oblG_live k (1/2)%Qp ∗
    oblG_progress_supply k x0 (1/2)%Qp
    ⊢ |==> osat (<[k:=odone P]>Ω) ∗ oblG_done k.
  Proof.
    iIntros "(Hsat & #He & #Hg & HR & Hs0 & Hps0)".
    iDestruct (osat_obl_is_live with "[Hsat He Hs0]") as "(%&%LU)".
    { iFrame. eauto. }
    rewrite /osat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[Hk Hm]"; [eapply LU |].
    iDestruct "Hk" as "(Hs & (%&%&Hps))".
    iMod (oblG_live_to_done with "[Hs Hs0]") as "Hs".
    { iApply oblG_live_frac_op; last iFrame. by rewrite Qp.div_2. }
    iPoseProof (oblG_done_auth_done with "Hs") as "#Hsd".
    iPoseProof (oblG_progress_supply_add with "[Hps Hps0]") as "(%&Hps&_)"; first iFrame.
    rewrite (Qp.div_2 1).
    iModIntro.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (odone P)) with "[Hm Hs Hps HR]") as "Hm".
    { apply lookup_delete_eq. }
    { iFrame "Hm". iFrame. eauto. }
    rewrite dom_insert_lookup_L; last done. iFrame "HS HP".
    rewrite insert_delete_eq. iFrame. eauto.
  Qed.

  Lemma osat_done_open Ω k P R :
    osat Ω ∗ oblG_goal k P R ∗ oblG_done k
    ⊢ (▷ R) ∗ (▷ R -∗ osat Ω).
  Proof.
    iIntros "(Hsat & #Hg0 & #Hs0)".
    iPoseProof (osat_obl_is_done with "[Hsat]") as "%Hdone"; [iFrame; eauto|].
    destruct Hdone as (?&LU&HP).
    rewrite /osat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
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

  Lemma osat_done_open_pers Ω k P R :
    Persistent R →
    osat Ω ∗ oblG_goal k P R ∗ oblG_done k
    ⊢ osat Ω ∗ ▷ R.
  Proof.
    iIntros (PP) "H". iPoseProof (osat_done_open with "H") as "[#HP Ho]".
    iSplitL; [|done]. iApply "Ho". done.
  Qed.

  Lemma osat_live_open Ω k q :
    osat Ω ∗ oblG_elem k ∗ oblG_live k q
    ⊢ oblG_live k q ∗ oblG_live k (1/2)%Qp ∗
    ((oblG_live k (1/2)%Qp) -∗ osat Ω).
  Proof.
    iIntros "(Hsat & #He0 & Hs0)".
    iPoseProof (osat_obl_is_live with "[Hsat Hs0]") as "%Hlive"; [iFrame; eauto|].
    destruct Hlive as (?&LU).
    rewrite /osat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HP& HE& Hm)".
    iDestruct (big_sepM_delete _ _ k _ LU with "Hm") as "[Hk Hm]".
    iDestruct "Hk" as "(Hs& (%&%&Hps))".
    iFrame "Hs0 Hs". iIntros "Hs". iFrame "HG HS HP HE". iSplitR; first done.
    iApply (big_sepM_delete _ _ k _ LU). iFrame. done.
  Qed.

End osat.

(* Allocation of an initial obligation protocol. *)
Lemma osat_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!osatGpreS ps Σ}
  `{obl_live_class A WFOCM.ltR} `{obl_done_class ps} :
  ⊢ |==> ∃ _ : osatGS ps Σ, osat ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id (prodR _ _))) as (γG) "HG";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bankUR) ⊤)) as (γC) "HC";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id unitUR)) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OsatG SI _ WFA _ _ _ γG γS γC γE).
  rewrite /osat -lock.
  iSplitL "HG"; first (iExists ∅; by iFrame).
  replace (⊤ ∖ gset_to_coPset (dom (∅ : obl_states))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
