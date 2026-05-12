From iris.algebra Require Import agree gset gmap gmap_view reservation_map mono_nat.
From iris.bi Require Import lib.cmra lib.fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.algebra Require Import map_of_sets bcred ordinal_ucmra.
From liris.base_logic Require Export osat othread.

Definition ogid := positive.

(** The ghost state for maintaining obligation groups *)
Module ogroupGS.

  (* Assumes thread ids are positive *)
  Class ogroupGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OgroupGpreS {
        ogroupGpreS_thread : inG Σ (gmap_viewR positive (gsetUR ogid));
        ogroupGpreS_group : inG Σ (gmap_viewR ogid (gsetUR oid));
        ogroupGpreS_fuel : inG Σ (reservation_mapUR (bcredUR));
      }.

  Class ogroupGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OgroupG {
        ogroup_inG : ogroupGpreS Σ;
        thread_name : gname;
        group_name : gname;
        fuel_name : gname;
      }.

  Definition ogroupΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (gmap_viewR positive (gsetUR ogid));
      GFunctor (gmap_viewR ogid (gsetUR oid));
      GFunctor (reservation_mapUR bcredUR)
      ].

  Global Instance subG_ogroupΣ `{SI : indexT} {Σ} : subG (ogroupΣ) Σ → (ogroupGpreS Σ).
  Proof. solve_inG. Qed.

End ogroupGS.
Import ogroupGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances ogroup_inG ogroupGpreS_thread ogroupGpreS_group ogroupGpreS_fuel.

(* Thread *)
Definition ogroupG_thread `{SI : indexT} `{!ogroupGS Σ} (i : positive) (G : gset ogid) : iProp Σ :=
  own thread_name (gmap_view_frag i (DfracOwn 1) G).
Global Typeclasses Opaque ogroupG_thread.
Global Instance: Params (@ogroupG_thread) 3 := {}.

Local Definition ogroupG_thread_auth `{SI : indexT} `{!ogroupGS Σ} (GM : gmap positive (gset ogid)) : iProp Σ :=
  (own thread_name (gmap_view_auth (DfracOwn 1) GM)).

(* Group *)
Definition ogroupG_group `{SI : indexT} `{!ogroupGS Σ} (g : ogid) (K : oids) : iProp Σ :=
  own group_name (gmap_view_frag g (DfracOwn 1) K).
Global Typeclasses Opaque ogroupG_group.
Global Instance: Params (@ogroupG_group) 3 := {}.

Local Definition ogroupG_group_auth `{SI : indexT} `{!ogroupGS Σ} (KM : gmap ogid oids) : iProp Σ :=
  (own group_name (gmap_view_auth (DfracOwn 1) KM)).

(* Fuel: manage fuels for ogroups *)
Definition ogroupG_bound `{SI : indexT} `{!ogroupGS Σ} (g : ogid) (β : obl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bcredUR) g (credit_bound β)).
Global Typeclasses Opaque ogroupG_bound.
Global Instance: Params (@ogroupG_bound) 3 := {}.

Definition ogroupG_fuel `{SI : indexT} `{!ogroupGS Σ} (g : ogid) (a : obl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bcredUR) g (credit a)).
Global Typeclasses Opaque ogroupG_fuel.
Global Instance: Params (@ogroupG_fuel) 3 := {}.

Local Definition ogroupG_fuel_token_id `{SI : indexT} `{!ogroupGS Σ} (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_token (A:=bcredUR) E).

(* Global invariant for the obligation groups. *)
Definition ogroup `{SI : indexT} `{!@osatGS.osatGS _ Σ} `{!othreadGS.othreadGS Σ} `{!ogroupGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (GM : gmap positive (gset ogid)) (KM : gmap ogid oids),
        ⌜ dom GM = TP ∧ disjoint_sets GM ∧ disjoint_sets KM ∧ union_sets GM ⊆ dom KM⌝ ∗
        (* ⌜ dom GM = TP ∧ union_sets GM ⊆ dom KM⌝ ∗ *)
        ogroupG_thread_auth GM ∗
        ogroupG_group_auth KM ∗
        ogroupG_fuel_token_id (⊤ ∖ (gset_to_coPset (dom KM))) ∗
        ([∗ map] i ↦ G ∈ GM,
           ((othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i (union_sets (filter_sets KM G)))
            ∨ (othreadG_done i ∗ ogroupG_thread i ∅ ∗ ⌜G = ∅⌝))) ∗
        ([∗ map] g ↦ K ∈ KM,
           ∃ β, ogroupG_bound g β ∗
                ([∗ set] k ∈ K, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)))%I.

Section ogroup.
  Context `{SI : indexT} `{OSAT : !osatGS.osatGS Σ} `{OTH : !othreadGS.othreadGS Σ} `{!ogroupGS Σ} `{OMF : !ord_mono_fun_class}.

  Global Instance ogroupG_thread_timeless i G : Timeless (ogroupG_thread i G).
  Proof. rewrite /ogroupG_thread. apply _. Qed.
  Global Instance ogroupG_thread_auth_timeless GM : Timeless (ogroupG_thread_auth GM).
  Proof. rewrite /ogroupG_thread_auth. apply _. Qed.

  Global Instance ogroupG_group_timeless g K : Timeless (ogroupG_group g K).
  Proof. rewrite /ogroupG_group. apply _. Qed.
  Global Instance ogroupG_group_auth_timeless KM : Timeless (ogroupG_group_auth KM).
  Proof. rewrite /ogroupG_group_auth. apply _. Qed.

  (* Fuel *)
  Global Instance ogroupG_bound_persistent g β : Persistent (ogroupG_bound g β).
  Proof. rewrite /ogroupG_bound. apply _. Qed.
  Global Instance ogroupG_bound_timeless g β : Timeless (ogroupG_bound g β).
  Proof. rewrite /ogroupG_bound. apply _. Qed.

  Global Instance ogroupG_fuel_timeless g a : Timeless (ogroupG_fuel g a).
  Proof. rewrite /ogroupG_fuel. apply _. Qed.

  Local Instance ogroupG_fuel_token_id_timeless E : Timeless (ogroupG_fuel_token_id E).
  Proof. rewrite /ogroupG_fuel_token_id. apply _. Qed.

  (** Thread rules *)
  Lemma ogroupG_thread_alloc GM i :
    GM !! i = None →
    ogroupG_thread_auth GM
    ⊢ |==> ogroupG_thread_auth (<[i:=∅]>GM) ∗ ogroupG_thread i ∅.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread.
    iIntros (Hi) "H".
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracOwn 1) (∅ : oids)); try done. }
    iDestruct "H" as "[H Ho]". by iFrame.
  Qed.

  Lemma ogroupG_thread_update GM i G1 G2 :
    ogroupG_thread_auth GM ∗
    ogroupG_thread i G1
    ⊢ |==> ogroupG_thread_auth (<[i:=G2]>GM) ∗
        ogroupG_thread i G2.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread -!own_op.
    apply own_update, gmap_view_replace. done.
  Qed.

  Lemma ogroupG_thread_delete GM i G :
    ogroupG_thread_auth GM ∗
    ogroupG_thread i G
    ⊢ |==> ogroupG_thread_auth (delete i GM).
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread -!own_op.
    apply own_update, gmap_view_delete.
  Qed.

  Lemma ogroupG_thread_lookup GM i G :
    ogroupG_thread_auth GM ∗
    ogroupG_thread i G
    ⊢ ⌜ GM !! i = Some G ⌝.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H. destruct H as (_&_&?).
    iPureIntro. apply leibniz_equiv in H. auto.
  Qed.

  Lemma ogroupG_thread_valid i G1 G2 :
    ogroupG_thread i G1 ∗ ogroupG_thread i G2 ⊢ False.
  Proof.
    rewrite /ogroupG_thread -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_frag_op_valid in H. destruct H as (?&?). done.
  Qed.

  (** Group rules *)
  Lemma ogroupG_group_alloc KM g :
    KM !! g = None →
    ogroupG_group_auth KM
    ⊢ |==> ogroupG_group_auth (<[g:=∅]>KM) ∗ ogroupG_group g ∅.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group.
    iIntros (Hi) "H".
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ g (DfracOwn 1) (∅ : oids)); try done. }
    iDestruct "H" as "[H Ho]". by iFrame.
  Qed.

  Lemma ogroupG_group_update KM g K1 K2 :
    ogroupG_group_auth KM ∗
    ogroupG_group g K1
    ⊢ |==> ogroupG_group_auth (<[g:=K2]>KM) ∗
        ogroupG_group g K2.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -!own_op.
    apply own_update, gmap_view_replace. done.
  Qed.

  Lemma ogroupG_group_delete KM g K :
    ogroupG_group_auth KM ∗
    ogroupG_group g K
    ⊢ |==> ogroupG_group_auth (delete g KM).
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -!own_op.
    apply own_update, gmap_view_delete.
  Qed.

  Lemma ogroupG_group_lookup KM g K :
    ogroupG_group_auth KM ∗
    ogroupG_group g K
    ⊢ ⌜ KM !! g = Some K ⌝.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H. destruct H as (_&_&?).
    iPureIntro. apply leibniz_equiv in H. auto.
  Qed.

  Lemma ogroupG_group_valid g K1 K2 :
    ogroupG_group g K1 ∗ ogroupG_group g K2 ⊢ False.
  Proof.
    rewrite /ogroupG_group -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_frag_op_valid in H. destruct H as (?&?). done.
  Qed.

  (** Fuel rules *)
  Lemma ogroupG_fuel_eq k a0 a1 :
    a0 w= a1 →
    ogroupG_fuel k a0 = ogroupG_fuel k a1.
  Proof. intros EQ. rewrite /ogroupG_fuel. by erewrite credit_eq. Qed.

  Lemma ogroupG_fuel_mon k a0 a1 :
    a0 w≤ a1 →
    ogroupG_fuel k a1 ⊢ |==> ogroupG_fuel k a0.
  Proof.
    intros LE. rewrite /ogroupG_fuel. apply own_update.
    by apply reservation_map_update, credit_update.
  Qed.

  Lemma ogroupG_fuel_split k a0 a1 :
    ogroupG_fuel k (a0 w+ a1) ⊣⊢ ogroupG_fuel k a0 ∗ ogroupG_fuel k a1.
  Proof.
    rewrite /ogroupG_fuel. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite credit_split). iSplitL "H1"; iFrame.
  Qed.

  Lemma ogroupG_fuel_mon_split k a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    ogroupG_fuel k a2 ⊢ |==> ogroupG_fuel k a0 ∗ ogroupG_fuel k a1.
  Proof.
    intros LE. iIntros "H". iApply ogroupG_fuel_split. iApply ogroupG_fuel_mon; done.
  Qed.

  Lemma ogroupG_fuel_lt k a0 a1 :
    a0 w< a1 →
    ogroupG_fuel k a1 ⊢ |==> ogroupG_fuel k a0 ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ ogroupG_fuel k c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (ogroupG_fuel_mon_split _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.

  Lemma ogroupG_bound_mon k a0 a1 :
    a0 w≤ a1 →
    ogroupG_bound k a0 ⊢ |==> ogroupG_bound k a1.
  Proof.
    intros LE. rewrite /ogroupG_bound. apply own_update.
    by apply reservation_map_update, cmra_update_included, credit_bound_included.
  Qed.

  Lemma ogroupG_fuel_spend_gen k a0 a1 :
    ogroupG_bound k a0 ∗ ogroupG_fuel k a1
    ⊢ |==> ∃ a2, ⌜(a1 w+ a2) w≤ a0⌝ ∗ ogroupG_bound k a2.
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
  Lemma ogroupG_fuel_spend k a0 a1 :
    wzero w< a1 →
    ogroupG_bound k a0 ∗ ogroupG_fuel k a1 ⊢ |==> ∃ a2, ⌜a2 w< a0⌝ ∗ ogroupG_bound k a2.
  Proof.
    iIntros (LT) "[Ow Oc]". iMod (ogroupG_fuel_spend_gen with "[$]") as "(%&%&$)".
    iPureIntro. eapply WFOCM.lt_exists_right; eauto.
  Qed.

  Lemma ogroupG_bound_fuel_compare k a0 a1 :
    ogroupG_bound k a0 ∗ ogroupG_fuel k a1 ⊢ ⌜ a1 w≤ a0 ⌝.
  Proof.
    rewrite -own_op -!reservation_map_data_op. iIntros "H".
    iPoseProof (own_valid with "H") as "%". apply reservation_map_data_valid in H.
    apply credit_bound_credit_valid_compare in H. done.
  Qed.

  Lemma ogroupG_bound_id_alloc D k a :
    k ∉ D →
    ogroupG_fuel_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> ogroupG_fuel_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        ogroupG_bound k a ∗ ogroupG_fuel k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (credit_bound a ⋅ credit a) with "Htk") as "[Htk >H]"; auto.
    { apply credit_bound_credit_valid_eq. }
    iDestruct "H" as "[H1 H2]". rewrite /ogroupG_bound /ogroupG_fuel. by iFrame.
  Qed.

  Lemma ogroupG_bound_op k a0 a1 :
    ogroupG_bound k a0 ∗ ogroupG_bound k a1 ⊢ ∃ a2, ogroupG_bound k a2 ∧ ⌜ a2 w≤ a0 ∧ a2 w≤ a1 ⌝.
  Proof.
    rewrite -own_op -!reservation_map_data_op. destruct (credit_bound_op a0 a1) as (?&?&?&?).
    rewrite H. rewrite /ogroupG_bound. iIntros "$". iPureIntro. split; auto.
  Qed.

  (** ogroup rules *)
  Lemma ogroup_alloc_thread i TP :
    i ∉ TP →
    ogroup TP ∗ othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅
    ⊢ |==> ogroup ({[i]} ∪ TP) ∗ ogroupG_thread i ∅.
  Proof.
    iIntros (Hi) "(G& Tx& TG)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& %& (%GDom& %GDisj& %KDisj& %KDom)& TA& GA& FT& GM& KM)".
    iMod (ogroupG_thread_alloc _ i with "TA") as "(TA& Ti)".
    { apply not_elem_of_dom. simplify_eq. auto. }
    iModIntro. iFrame "GA FT TA Ti". iSplit.
    { iPureIntro. simplify_eq. split_and !; auto.
      - by rewrite dom_insert_L.
      - apply disjoint_sets_insert_2; auto. 1: by apply not_elem_of_dom. set_solver.
      - rewrite union_sets_insert_L; auto. 1: set_solver. by apply not_elem_of_dom. }
    iFrame "KM". iApply big_sepM_insert. 1: by subst; apply not_elem_of_dom.
    iFrame "GM". iLeft. rewrite filter_sets_empty union_sets_empty. iFrame.
  Qed.

  Lemma ogroup_alloc_threads Θ TP :
    Θ ## TP →
    ogroup TP ∗ ([∗ set] i ∈ Θ, othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅)
    ⊢ |==> ogroup (TP ∪ Θ) ∗ ([∗ set] i ∈ Θ, ogroupG_thread i ∅).
  Proof.
    revert TP. pattern Θ. revert Θ. apply set_ind.
    { solve_proper. }
    { iIntros (??) "[T _]". rewrite union_empty_r_L. iFrame. by iModIntro. }
    iIntros (i Θ Nin IH TP Disj) "[F M]".
    rewrite !big_sepS_union. 2,3: set_solver. rewrite !big_sepS_singleton. iDestruct "M" as "(Mi& M)".
    iMod (IH with "[$F $M]") as "(F& $)". 1: set_solver.
    iMod (ogroup_alloc_thread i with "[$F $Mi]") as "(F& Hi)"; first set_solver.
    iModIntro. replace ({[i]} ∪ (TP ∪ Θ)) with (TP ∪ ({[i]} ∪ Θ)) by set_solver.
    iFrame.
  Qed.

  Lemma ogroup_alloc_group TP i G β :
    ogroup TP ∗ ogroupG_thread i G
    ⊢ |==> ∃ g, ogroup TP ∗
             ⌜ g ∉ G ⌝ ∗ ogroupG_thread i (G ∪ {[g]}) ∗
             ogroupG_group g ∅ ∗ ogroupG_bound g β ∗ ogroupG_fuel g β.
  Proof.
    iIntros "(G& Ti)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& %& (%GDom& %GDisj& %KDisj& %KDom)& TA& GA& FT& GM& KM)".
    assert (∃ g, g ∉ dom KM) as (g&Hg).
    { eexists. eapply is_fresh. }
    iMod (ogroupG_bound_id_alloc _ _ β Hg with "FT") as "(FT& #Bg& Hfg)".
    iPoseProof (ogroupG_thread_lookup with "[$TA $Ti]") as "%LUi".
    iPoseProof (big_sepM_delete _ _ _ _ LUi with "GM") as "[Hex GM]".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Ti0& _)". by iPoseProof (ogroupG_thread_valid with "[$Ti $Ti0]") as "%". }
    iDestruct "Hex" as "(TTx& TTG)".
    iMod (ogroupG_thread_update _ _ _ (G ∪ {[g]}) with "[$TA $Ti]") as "(TA& Ti)".
    assert (LUg : KM !! g = None) by (apply not_elem_of_dom; auto).
    iMod (ogroupG_group_alloc _ _ LUg with "GA") as "(GA& Gg)".
    assert (Ning : g ∉ G).
    { eapply not_elem_of_weaken. 1: eapply Hg. etrans; last eapply KDom. by eapply union_sets_lookup_subseteq. }
    iModIntro. iFrame "Hfg Bg TA Ti GA Gg". iSplit. 2: auto. iSplit.
    { iPureIntro. simplify_eq. assert (i ∈ dom GM) by (apply elem_of_dom; eauto). split_and !; auto.
      - rewrite dom_insert_L. set_solver.
      - eapply disjoint_sets_insert_union_singleton_not_in; auto.
      - apply disjoint_sets_insert_2; auto. set_solver.
      - rewrite union_sets_insert_union_L; auto. rewrite dom_insert_L. set_solver. }
    iSplitL "FT".
    { rewrite dom_insert_L. iFrame. }
    iSplitL "GM TTx TTG".
    { iApply big_sepM_insert_delete. iSplitR "GM".
      { iLeft. iFrame. erewrite union_sets_filter_sets_add_key; eauto. 2: by rewrite lookup_insert_eq.
        rewrite union_empty_l_L. rewrite union_sets_filter_sets_insert_notin; auto. }
      iApply (big_sepM_impl with "GM"). iIntros "!> %%% [(H1& H2) | $]". iLeft. iFrame.
      rewrite union_sets_filter_sets_insert_notin; auto.
      eapply not_elem_of_weaken. 1: eapply Hg. etrans; last eapply KDom.
      apply lookup_delete_Some in H. destruct H. by eapply union_sets_lookup_subseteq. }
    iApply big_sepM_insert. 1: auto.
    iFrame "KM Bg". done.
  Qed.

  Lemma ogroup_delete_group TP i G g :
    ogroup TP ∗ ogroupG_thread i G ∗ ogroupG_group g ∅
    ⊢ |==> ogroup TP ∗ ogroupG_thread i (G ∖ {[g]}) ∗ ogroupG_group g ∅.
  Proof.
    iIntros "(G& Ti& Gg)".
    destruct (decide (g ∈ G)); cycle 1.
    { replace (G ∖ {[g]}) with G by set_solver. by iFrame. }
    rename e into Ing.
    rewrite /ogroup -!lock. iDestruct "G" as "(%& %& (%GDom& %GDisj& %KDisj& %KDom)& TA& GA& FT& GM& KM)".
    iPoseProof (ogroupG_thread_lookup with "[$TA $Ti]") as "%LUi".
    iPoseProof (ogroupG_group_lookup with "[$GA $Gg]") as "%LUg".
    iPoseProof (big_sepM_delete _ _ _ _ LUi with "GM") as "[Hex GM]".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Ti0& _)". by iPoseProof (ogroupG_thread_valid with "[$Ti $Ti0]") as "%". }
    iDestruct "Hex" as "(TTx& TTG)".
    iMod (ogroupG_thread_update _ _ _ (G ∖ {[g]}) with "[$TA $Ti]") as "(TA& Ti)".
    (* iMod (ogroupG_group_delete with "[$GA $Gg]") as "GA". *)
    iModIntro. iFrame "GA FT Gg TA Ti". iSplit.
    { iPureIntro. simplify_eq. assert (i ∈ dom GM) by (apply elem_of_dom; eauto). split_and !; auto.
      - rewrite dom_insert_L. set_solver.
      - eapply disjoint_sets_insert_difference; eauto.
      - etrans; first eapply union_sets_insert_difference_subseteq; eauto. }
    iSplitL "GM TTx TTG".
    { iApply big_sepM_insert_delete. iFrame "GM". iLeft. iFrame.
      erewrite (union_sets_filter_sets_remove_key _ _ g); eauto. rewrite union_empty_l_L. auto. }
    iFrame.
  Qed.

  Lemma ogroup_renew_group TP i G g1 K β :
    ogroup TP ∗ ogroupG_thread i G ∗ ogroupG_group g1 K ∗
    ([∗ set] k ∈ K, ∃ a, ⌜(β ≤ a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)
    ⊢ |==> ∃ g2, ogroup TP ∗
              ⌜ g2 ∉ G ⌝ ∗ ogroupG_thread i ((G ∖ {[g1]}) ∪ {[g2]}) ∗
              ogroupG_group g2 K ∗ ogroupG_bound g2 β ∗ ogroupG_fuel g2 β ∗
              ogroupG_group g1 K.
  Proof.
    iIntros "(G& Ti& Gg1& SFs)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& %& (%GDom& %GDisj& %KDisj& %KDom)& TA& GA& FT& GM& KM)".
    assert (∃ g2, g2 ∉ dom KM) as (g2&Hg2).
    { eexists. eapply is_fresh. }
    iMod (ogroupG_bound_id_alloc _ _ β Hg2 with "FT") as "(FT& #Bg2& Hfg2)".
    iPoseProof (ogroupG_group_lookup with "[$GA $Gg1]") as "%LUg1".
    iPoseProof (ogroupG_thread_lookup with "[$TA $Ti]") as "%LUi".
    iPoseProof (big_sepM_delete _ _ _ _ LUi with "GM") as "[Hex GM]".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Ti0& _)". by iPoseProof (ogroupG_thread_valid with "[$Ti $Ti0]") as "%". }
    iDestruct "Hex" as "(TTx& TTG)".
    iMod (ogroupG_thread_update _ _ _ ((G ∖ {[g1]}) ∪ {[g2]}) with "[$TA $Ti]") as "(TA& Ti)".
    assert (LUg2 : KM !! g2 = None) by (apply not_elem_of_dom; auto).
    iMod (ogroupG_group_alloc _ _ LUg2 with "GA") as "(GA& Gg2)".
    iMod (ogroupG_group_update _ _ _ K with "[$GA $Gg2]") as "(GA& Gg2)". rewrite insert_insert_eq.
    assert (Ning : g2 ∉ G).
    { eapply not_elem_of_weaken. 1: eapply Hg2. etrans; last eapply KDom. by eapply union_sets_lookup_subseteq. }
    iModIntro. iFrame "Hfg2 Bg2 TA Ti GA Gg2 Gg1". iSplit. 2: auto. iSplit.
    { iPureIntro. simplify_eq. assert (i ∈ dom GM) by (apply elem_of_dom; eauto). split_and !; auto.
      - rewrite dom_insert_L. set_solver.
      - rewrite -(insert_insert_eq _ i _ (G ∖ {[g1]})).
        eapply disjoint_sets_insert_union_singleton_not_in; auto.
        + by rewrite lookup_insert_eq.
        + eapply disjoint_sets_insert_difference; eauto.
        + eapply not_elem_of_weaken. 1: eapply Hg2. etrans; last eapply KDom.
          eapply union_sets_insert_difference_subseteq; eauto.
      -

        TODO

        apply disjoint_sets_insert_2; auto. set_solver.
      - rewrite union_sets_insert_union_L; auto. rewrite dom_insert_L. set_solver. }
    iSplitL "FT".
    { rewrite dom_insert_L. iFrame. }
    iSplitL "GM TTx TTG".
    { iApply big_sepM_insert_delete. iSplitR "GM".
      { iLeft. iFrame. erewrite union_sets_filter_sets_add_key; eauto. 2: by rewrite lookup_insert_eq.
        rewrite union_empty_l_L. rewrite union_sets_filter_sets_insert_notin; auto. }
      iApply (big_sepM_impl with "GM"). iIntros "!> %%% [(H1& H2) | $]". iLeft. iFrame.
      rewrite union_sets_filter_sets_insert_notin; auto.
      eapply not_elem_of_weaken. 1: eapply Hg. etrans; last eapply KDom.
      apply lookup_delete_Some in H. destruct H. by eapply union_sets_lookup_subseteq. }
    iApply big_sepM_insert. 1: auto.
    iFrame "KM Bg". done.
  Qed.
    
              


  Lemma ogroup_alloc_obl Ω TP i π s q K β k :
    i ∈ TP →
    osat Ω ∗ othread TP ∗ ogroup TP ∗
    othreadG_proxy_obls i π K ∗ othreadG_proxy_session i π s q ∗ othreadG_bound s β ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp ∗ oblG_fuel k β
    ⊢ |==> osat Ω ∗ othread TP ∗ ogroup TP ∗
        ⌜k ∉ K⌝ ∗ othreadG_proxy_obls i π ({[k]} ∪ K) ∗ othreadG_proxy_session i π s q ∗
        othreadG_owns i k 1 ∗ oblG_owner k i (1/2 + 1/2/2/2 + 1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ini) "(S& T& P& Po& Ps& #Tb& #Oe& Oo& Of)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_lookup with "[$Psa $Ps]") as "%LUs".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po]") as "%LUo".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo LUs with "OFs") as "[Hp OFs]".
    iDestruct "Hp" as "(%& #Tb0& Hfs)".
    iPoseProof (othreadG_bound_op _ β β0 with "[$Tb $Tb0]") as "(%β1& #Tb1& %Hb)".
    destruct Hb as [Hb1 Hb2]. iClear "Tb Tb0".
    iMod (othread_alloc_obl with "[$S $T $TG $Oe $Oo]") as "(S& T& %Nink& TG& To& Oo)".
    iMod (othreadG_proxy_obls_update _ _ _ _ ({[k]} ∪ K) with "[$Poa $Po]") as "[Poa Po]".
    iModIntro. iFrame "S T FT ST PT Ps To Oo Po".
    assert (Nink2 : k ∉ K).
    { simplify_eq. rewrite not_elem_of_union_sets in Nink. eapply Nink; eauto. }
    iSplit. 2: auto.
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Poa Psa". iSplitR.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUo. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. replace ({[k]} ∪ K) with (K ∪ {[k]}) by set_solver. simplify_eq. split.
      - rewrite union_sets_insert_union_L; auto.
      - apply disjoint_sets_insert_union_singleton_not_in; auto. }
    iEval (rewrite -(insert_id _ _ _ LUs)). iApply big_sepM2_insert_delete.
    iFrame "OFs Tb1". iApply (big_sepS_union). 1: set_solver.
    iSplitR "Hfs".
    { iApply big_sepS_singleton. iFrame "Of Oe". iPureIntro. eauto. }
    { iApply (big_sepS_impl with "Hfs"). iIntros "!> %% (%&%&$&$)". iPureIntro. etrans; eauto. }
  Qed.

  Lemma ogroup_delete_obl TP i π K k :
    i ∈ TP →
    k ∈ K →
    othread TP ∗ ogroup TP ∗
    othreadG_proxy_obls i π K ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ ogroup TP ∗
        othreadG_proxy_obls i π (K ∖ {[k]}) ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ini Ink) "(T& P& Po& To)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa& Hex& OFs)".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po]") as "%LUo".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (big_sepM2_delete_l _ _ _ _ _ LUo with "OFs") as "(%s& %LUs& Hp& OFs)".
    iDestruct "Hp" as "(%& #Tb& Hfs)".
    iMod (othread_delete_obl with "[$T $TG $To]") as "(T& TG& Oo)".
    iMod (othreadG_proxy_obls_update _ _ _ _ (K ∖ {[k]}) with "[$Poa $Po]") as "[Poa Po]".
    iModIntro. iFrame "T FT ST PT Oo Po".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Poa Psa". iSplitR.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUo. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. simplify_eq. split.
      - rewrite union_sets_insert_difference_singleton_L; auto.
      - apply disjoint_sets_insert_difference; auto. }
    iEval (rewrite -(insert_id _ _ _ LUs)). iApply big_sepM2_insert_delete.
    iFrame "OFs". iFrame "Tb". iPoseProof (big_sepS_delete with "Hfs") as "[_ $]". auto.
  Qed.

  Lemma ogroup_obl_change_proxy TP i π1 π2 K1 K2 s2 q2 β k :
    i ∈ TP →
    k ∈ K1 →
    ogroup TP ∗
    othreadG_proxy_obls i π1 K1 ∗
    othreadG_proxy_obls i π2 K2 ∗ othreadG_proxy_session i π2 s2 q2 ∗
    othreadG_bound s2 β ∗ oblG_fuel k β
    ⊢ |==> ogroup TP ∗
        othreadG_proxy_obls i π1 (K1 ∖ {[k]}) ∗
        othreadG_proxy_obls i π2 (K2 ∪ {[k]}) ∗ othreadG_proxy_session i π2 s2 q2.
  Proof.
    iIntros (Ini Ink) "(P& Po1& Po2& Ps2& #Tb& Of)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa& Hex& OFs)".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po1]") as "%LUo1".
    assert (is_Some (Ss !! π1)) as (s1& LUs1).
    { apply elem_of_dom. apply elem_of_dom_2 in LUo1. rewrite -Dom. auto. }
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po2]") as "%LUo2".
    iPoseProof (othreadG_proxy_session_lookup with "[$Psa $Ps2]") as "%LUs2".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (othreadG_proxy_obls_valid _ π1 π2 with "[$Po1 $Po2]") as "%Neqp".
    iMod (othreadG_proxy_obls_update _ _ _ _ (K1 ∖ {[k]}) with "[$Poa $Po1]") as "[Poa Po1]".
    iMod (othreadG_proxy_obls_update _ _ _ _ (K2 ∪ {[k]}) with "[$Poa $Po2]") as "[Poa Po2]".
    iModIntro. iFrame "FT ST PT Po1 Po2 Ps2".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Poa Psa". iSplitR.
    { iPureIntro. rewrite !dom_insert_L. apply elem_of_dom_2 in LUo1, LUo2. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. assert (Ink2 : k ∈ union_sets Ks).
      { apply elem_of_union_sets; eauto. }
      simplify_eq. split.
      - rewrite union_sets_insert_union_L; cycle 1.
        { rewrite lookup_insert_ne; auto. }
        rewrite union_sets_insert_difference_singleton_L; auto. rewrite -union_difference_L; set_solver.
      - apply disjoint_sets_insert_union_singleton_not_in.
        { rewrite lookup_insert_ne; auto. }
        { apply disjoint_sets_insert_difference; auto. }
        { apply not_elem_of_union_sets. intros. destruct (decide (k0 = π1)).
          - subst. rewrite lookup_insert_eq in H. simplify_eq. set_solver.
          - rewrite lookup_insert_ne in H; auto. specialize (Disj _ _ _ _ n H LUo1). set_solver. }
    }
    iEval (rewrite -(insert_id _ _ _ LUs1)). assert (LUs3 : <[π1:=s1]> Ss !! π2 = Some s2).
    { rewrite lookup_insert_ne; auto. }
    iEval (rewrite -(insert_id _ _ _ LUs3)). iApply big_sepM2_insert_delete.
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo2 LUs2 with "OFs") as "[Fs2 OFs]".
    iPoseProof (big_sepM2_delete _ _ _ π1 K1 s1 with "OFs") as "[Fs1 OFs]".
    { rewrite lookup_delete_ne; auto. }
    { rewrite lookup_delete_ne; auto. }
    iDestruct "Fs1" as "(%βp1& #Bp1& Fs1)". iPoseProof (big_sepS_delete _ _ _ Ink with "Fs1") as "[Fk Fs1]".
    iSplitL "Of Fk Fs2".
    { iDestruct "Fk" as "(%&%&_&#Oe)". iDestruct "Fs2" as "(%& #Tb0& Fs)".
      iPoseProof (othreadG_bound_op _ β β0 with "[$Tb $Tb0]") as "(%β1& #Tb1& %Hb)".
      destruct Hb as [Hb1 Hb2]. iClear "Tb Tb0".
      iFrame "Tb1". iApply big_sepS_union.
      { specialize (Disj _ _ _ _ Neqp LUo1 LUo2). set_solver. }
      iSplitL "Fs".
      { iApply (big_sepS_impl with "Fs"). iIntros "!> %% (%& %& $& $)". iPureIntro. etrans; eauto. }
      iApply big_sepS_singleton. iFrame "Oe Of". iPureIntro. auto. }
    rewrite !delete_insert_ne; auto. iApply big_sepM2_insert_delete. iFrame "OFs".
    iFrame "Bp1". iFrame.
  Qed.

  Lemma ogroup_exec_to_done TP i :
    i ∈ TP →
    othread TP ∗ ogroup TP ∗
    othreadG_exec i (1/2)%Qp ∗ othreadG_proxy_session_auth i ∅ (1/2)%Qp
    ⊢ |==> othread TP ∗ ogroup TP ∗ othreadG_done i.
  Proof.
    iIntros (Ini) "(T& P& Tx& Psa)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa0& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H as [<- _].
    apply dom_empty_inv_L in Dom. subst. iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Psa1& _)". iCombine "Psa Psa0" as "Psa".
      iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa1]") as "%". destruct H. done. }
    iDestruct "Hex" as "(%& Tx2& TG& %)". destruct H as [Uni Disj].
    rewrite union_sets_empty in Uni. subst.
    iCombine "Tx Tx2" as "Tx".
    iMod (othread_exec_to_done with "[$T $Tx $TG]") as "[T #Td]".
    iModIntro. iFrame "T FT ST PT Td".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Psa0 Poa". iSplit. 1: done.
    iSplitL "Psa".
    { iRight. iFrame. eauto. }
    done.
  Qed.

  Lemma ogroup_proxy_new_session TP i π K PS s1 β :
    i ∈ TP →
    ogroup TP ∗ othreadG_proxy_obls i π K ∗
    othreadG_proxy_session_auth i PS (1/2)%Qp ∗ othreadG_proxy_session i π s1 1 ∗
    ([∗ set] k ∈ K, oblG_fuel k β)
    ⊢ |==> ∃ s2, ogroup TP ∗ othreadG_proxy_obls i π K ∗
              othreadG_proxy_session_auth i (<[π:=s2]>PS) (1/2)%Qp ∗ othreadG_proxy_session i π s2 1 ∗
              othreadG_bound s2 β ∗ othreadG_fuel s2 β.
  Proof.
    iIntros (Ini) "(P& Po& Psa& Ps& KFs)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa0& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H as [<- _].
    iCombine "Psa Psa0" as "Psa".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po]") as "%LUo".
    iPoseProof (othreadG_proxy_session_lookup with "[$Psa $Ps]") as "%LUs".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Psa1& _)".
      iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa1]") as "%". destruct H. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    assert (∃ s2, s2 ∉ Df) as (s2&Hs).
    { eexists. eapply is_fresh. }
    iMod (othreadG_bound_id_alloc _ _ β Hs with "FT") as "(FT& #Tb& Hfs)".
    iMod (othreadG_proxy_session_update _ _ _ _ s2 with "[$Psa $Ps]") as "[[Psa Psa0] Ps]".
    iModIntro. iFrame "FT ST PT Po Hfs Psa Ps Tb".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Poa Psa0". iSplit.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUs. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. eauto. }
    iEval (rewrite -(insert_id _ _ _ LUo)). iApply big_sepM2_insert_delete.
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo LUs with "OFs") as "[Fs $]".
    iDestruct "Fs" as "(%& _& Fs)". iPoseProof (big_sepS_sep_2 with "KFs Fs") as "Fs".
    iFrame "Tb". iApply (big_sepS_impl with "Fs"). iIntros "!> %% ($& %& _& _& $)". auto.
  Qed.

  Lemma ogroup_exchange_fuel TP i PS q c :
    i ∈ TP →
    (Ord.O < c)%ord →
    ogroup TP ∗
    othreadG_proxy_session_auth i PS q ∗
    ([∗ map] s ∈ PS, othreadG_fuel s c)
    ⊢ |==> ∃ G, (othreadG_exec i (1 / 2 / 2) -∗ othreadG_obls i G -∗ ogroup TP) ∗
             othreadG_proxy_session_auth i PS q ∗
             othreadG_exec i (1 / 2 / 2) ∗ othreadG_obls i G ∗
             ([∗ set] k ∈ G, oblG_fuel k Ord.one ∗ oblG_elem k).
  Proof.
    iIntros (Ini Ltc) "(P& Psa& Tfs)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa0& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H as [<- _].
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Psa1& _)". iCombine "Psa0 Psa1" as "Psa0".
      iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H.
      apply Qp.not_add_le_r in H0. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iAssert (
        |==> ([∗ map] K;s ∈ Ks;PS,
             ∃ β : obl_fuel, othreadG_bound s β ∗ ([∗ set] k ∈ K, ∃ a : Ord.t, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)) ∗
          ([∗ map] K ∈ Ks, ([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k)))%I
      with "[Tfs OFs]" as ">[OFs Fs]".
    { iAssert ([∗ map] K;s ∈ Ks;PS, True ∗ othreadG_fuel s c)%I with "[Tfs]" as "Tfs".
      { iApply big_sepM2_sepM.
        - intros. rewrite -!elem_of_dom Dom. auto.
        - iFrame. done. }
      iAssert (|==> ([∗ map] K;s ∈ Ks;PS,
                    (([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k) ∗ True) ∗
                    (∃ β, othreadG_bound s β ∗ ([∗ set] k ∈ K, ∃ a : Ord.t, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k))))%I
        with "[-]" as ">H"; cycle 1.
      { iPoseProof (big_sepM2_sep with "H") as "[H1 H2]". iFrame.
        iPoseProof (big_sepM2_sepM with "H1") as "[H _]".
        - intros. rewrite -!elem_of_dom Dom. auto.
        - iFrame. done. }
      iPoseProof (big_sepM2_sep with "[$Tfs $OFs]") as "OFs".
      iPoseProof (big_sepM2_alt with "OFs") as "[_ OFs]".
      iApply big_sepM2_alt. iSplitR. 1: eauto. iApply big_sepM_bupd.
      iApply (big_sepM_impl with "OFs"). iIntros "!> %%% [(_& F) H]".
      destruct x as [K s]. simpl. iDestruct "H" as "(%& #Tb& KFs)".
      iMod (othreadG_fuel_spend with "[$Tb $F]") as "(%β1& %HB& #Tb1)". 1: auto.
      iAssert (|==> ([∗ set] k ∈ K, ∃ a : Ord.t, ⌜(β1 <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k) ∗
                 ([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k))%I with "[KFs]" as ">[Fvs Rvs]".
      { iApply big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "KFs").
        iIntros "!> %% (%&%& F& #E)". iFrame "E". iMod (oblG_fuel_lt _ β1 with "F") as "(F& %& %& F1)".
        { eapply Ord.lt_le_lt; eauto. }
        iMod (oblG_fuel_mon _ Ord.one with "F1") as "F1".
        { apply Ord.S_supremum. auto. }
        iModIntro. iSplitR "F1"; iFrame. done. }
      iFrame. eauto. }
    iModIntro. iFrame "Psa Tx TG". iSplitR "Fs".
    - iIntros "Tx TG". iFrame "FT ST PT". 
      iApply (big_sepS_delete _ _ _ Ini). iFrame "M". iFrame "Psa0 Poa". iSplit. 1: done.
      iFrame "OFs". iLeft. iFrame. eauto.
    - subst. clear dependent TP i PS q c Df. iInduction Ks as [ | π K ?? LUp] using map_ind.
      { rewrite union_sets_empty. done. }
      rewrite union_sets_insert_L; last auto. iApply (big_sepS_union).
      { eapply disjoint_sets_insert_disjoint_union_sets; eauto. }
      iPoseProof (big_sepM_insert with "Fs") as "[F Fs]". 1: auto.
      apply disjoint_sets_insert in Disj; last auto. destruct Disj as [MF Disj].
      iPoseProof ("LUp" with "[//] Fs") as "$". iFrame.
  Qed.

  Lemma ogroup_obl_change_thread TP i1 i2 π1 π2 K1 K2 s q β k :
    i1 ∈ TP →
    i2 ∈ TP →
    k ∈ K1 →
    i1 ≠ i2 →
    ogroup TP ∗
    othreadG_proxy_obls i1 π1 K1 ∗
    othreadG_proxy_obls i2 π2 K2 ∗ othreadG_proxy_session i2 π2 s q ∗
    othreadG_bound s β ∗ oblG_fuel k β
    ⊢ |==> ∃ G1 G2,
      (⌜ k ∉ G2 ⌝ -∗ othreadG_exec i1 (1/2/2) -∗ othreadG_obls i1 (G1 ∖ {[k]}) -∗
       othreadG_exec i2 (1/2/2) -∗ othreadG_obls i2 ({[k]} ∪ G2) -∗ ogroup TP) ∗
      ⌜ k ∈ G1 ⌝ ∗
      othreadG_exec i1 (1/2/2) ∗ othreadG_obls i1 G1 ∗
      othreadG_exec i2 (1/2/2) ∗ othreadG_obls i2 G2 ∗
      othreadG_proxy_obls i1 π1 (K1 ∖ {[k]}) ∗ othreadG_proxy_obls i2 π2 (K2 ∪ {[k]}) ∗
      othreadG_proxy_session i2 π2 s q.
  Proof.
    iIntros (Ini1 Ini2 Ink Nei) "(P& Po1& Po2& Ps2& #Tb& Of)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini1 with "M") as "[Mi M]".
    iDestruct "Mi" as "(%Ks1& %Ss1& %Dom1& Poa1& Psa1& Hex1& OFs1)".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa1 $Po1]") as "%LUo1".
    assert (is_Some (Ss1 !! π1)) as (s1& LUs1).
    { apply elem_of_dom. apply elem_of_dom_2 in LUo1. rewrite -Dom1. auto. }
    assert (Ini2' : i2 ∈ (TP ∖ {[i1]})) by set_solver.
    iPoseProof (big_sepS_delete _ _ _ Ini2' with "M") as "[Mi M]".
    iDestruct "Mi" as "(%Ks2& %Ss2& %Dom2& Poa2& Psa2& Hex2& OFs2)".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa2 $Po2]") as "%LUo2".
    iPoseProof (othreadG_proxy_session_lookup with "[$Psa2 $Ps2]") as "%LUs2". rename s into s2.
    iDestruct "Hex1" as "[Hex1 | Hex1]"; cycle 1.
    { iDestruct "Hex1" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex1" as "(%G1& Tx1& TG1& %)". destruct H as [Uni1 Disj1].
    iDestruct "Hex2" as "[Hex2 | Hex2]"; cycle 1.
    { iDestruct "Hex2" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex2" as "(%G2& Tx2& TG2& %)". destruct H as [Uni2 Disj2].
    iMod (othreadG_proxy_obls_update _ _ _ _ (K1 ∖ {[k]}) with "[$Poa1 $Po1]") as "[Poa1 Po1]".
    iMod (othreadG_proxy_obls_update _ _ _ _ (K2 ∪ {[k]}) with "[$Poa2 $Po2]") as "[Poa2 Po2]".
    assert (Ink2 : k ∈ G1).
    { subst. apply elem_of_union_sets; eauto. }
    iModIntro. iFrame "Tx1 Tx2 TG1 TG2 Po1 Po2 Ps2". iSplit; last auto.
    iIntros (Nink) "Tx1 TG1 Tx2 TG2". iFrame "FT ST PT".
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo1 LUs1 with "OFs1") as "[OF OFs1]".
    iDestruct "OF" as "(%& #Tb0& OF)". iPoseProof (big_sepS_delete _ _ _ Ink with "OF") as "[Hof OF]".
    iApply (big_sepS_delete _ _ _ Ini1). iSplitL "Psa1 Poa1 Tx1 TG1 OFs1 OF".
    { iFrame "Psa1 Poa1". iSplit.
      { iPureIntro. rewrite dom_insert_L Dom1. apply elem_of_dom_2 in LUs1. set_solver. }
      iSplitL "Tx1 TG1".
      { iLeft. iFrame. iPureIntro. simplify_eq. split.
        - rewrite union_sets_insert_difference_singleton_L; auto.
        - apply disjoint_sets_insert_difference; auto. }
      iEval (rewrite -(insert_id _ _ _ LUs1)). iApply big_sepM2_insert_delete. iFrame "OFs1".
      iFrame "Tb0 OF". }
    iApply (big_sepS_delete _ _ _ Ini2'). iFrame "M".
    iFrame "Psa2 Poa2". iSplitR.
    { iPureIntro. rewrite !dom_insert_L. apply elem_of_dom_2 in LUo2. set_solver. }
    iSplitL "Tx2 TG2".
    { iLeft. iFrame. iPureIntro. simplify_eq. split.
      - rewrite union_sets_insert_union_L; auto.
      - apply disjoint_sets_insert_union_singleton_not_in; auto. }
    iEval (rewrite -(insert_id _ _ _ LUs2)). iApply big_sepM2_insert_delete.
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo2 LUs2 with "OFs2") as "[Fs2 OFs2]". iFrame "OFs2".
    iDestruct "Fs2" as "(%& #Tb1& F)". iPoseProof (othreadG_bound_op _ β β1 with "[$Tb $Tb1]") as "(%& #Tb'& %)".
    destruct H. iFrame "Tb'". iApply (big_sepS_union_2 with "[F] [-]").
    { iApply (big_sepS_impl with "F"). iIntros "!> %% (%& %& $& $)". iPureIntro. etrans; eauto. }
    { iDestruct "Hof" as "(%& _& _& #Ok)". iApply big_sepS_singleton. iFrame "Of Ok". iPureIntro. auto. }
  Qed.


  

  (* TODO?: more to somewhere *)
  Lemma big_sepM_forest_fold {V : Type} `{Countable V} (f : forest V) (Φ : V → gset V → iProp Σ) :
    forest_trees_disjoint f →
    ([∗ map] v ↦ vC ∈ (forest_fold f), Φ v vC) ⊣⊢ [∗ map] ρ ↦ ρt ∈ f, ([∗ map] v ↦ vC ∈ ρt, Φ v vC).
  Proof.
    intros Disj. iSplit; iIntros "H".
    - iStopProof. revert Disj. induction f using map_ind; iIntros (Disj) "H"; first done.
      rewrite forest_fold_insert_L; auto.
      apply forest_trees_disjoint_insert in Disj; auto. destruct Disj as [Dx Disj].
      iPoseProof (big_sepM_union with "H") as "[Hx H]".
      { apply forest_tree_disjoint_forest_fold; auto. }
      iPoseProof (IHf Disj with "H") as "H". iApply big_sepM_insert; auto. iFrame.
    - iStopProof. revert Disj. induction f using map_ind; iIntros (Disj) "H"; first done.
      rewrite forest_fold_insert_L; auto.
      apply forest_trees_disjoint_insert in Disj; auto. destruct Disj as [Dx Disj].
      iPoseProof (big_sepM_insert with "H") as "[Hx H]"; auto.
      iPoseProof (IHf Disj with "H") as "H". iApply big_sepM_union.
      { apply forest_tree_disjoint_forest_fold; auto. }
      iFrame.
  Qed.

  (** TODO: move to map_of_forests *)
  Section map_of_forests.
    Context {K V : Type}.
    Context `{!EqDecision K} `{!Countable K} `{!EqDecision V} `{!Countable V}.
    Implicit Type t : tree V.
    Implicit Type F f : forest V.
    Implicit Type Rs : gmap K (gset V).
    Implicit Type rs : gset V.

    Lemma forest_to_forests_dom F Rs :
      dom (forest_to_forests F Rs) = dom Rs.
    Proof. apply dom_fmap_L. Qed.

    Lemma forest_to_forests_lookup_None F Rs k :
      Rs !! k = None →
      forest_to_forests F Rs !! k = None.
    Proof. rewrite -!not_elem_of_dom. intros. rewrite forest_to_forests_dom. auto. Qed.

    Lemma forest_to_forests_forest_insert_new F Rs ρ t :
      ρ ∉ union_sets Rs →
      forest_to_forests (forest_insert F ρ t) Rs = forest_to_forests F Rs.
    Proof.
      intros. rewrite forest_to_forests_forest_insert. apply map_eq. intros.
      rewrite lookup_fmap. destruct (Rs !! i) eqn:LUi.
      - erewrite (forest_to_forests_lookup_eq _ Rs); eauto. simpl. assert (ρ ∉ g).
        { rewrite not_elem_of_union_sets in H. eapply H; eauto. }
        rewrite decide_False; auto.
      - rewrite forest_to_forests_lookup_None; auto.
    Qed.

    Lemma forest_filter_roots_not_roots F R :
      R ## dom F →
      forest_filter_roots F R = ∅.
    Proof.
      intros. apply map_empty_filter. intros ???. apply elem_of_dom_2 in H0. set_solver.
    Qed.

    Lemma forest_trees_disjoint_subseteq f1 f2 :
      forest_subseteq f1 f2 →
      forest_trees_disjoint f2 →
      forest_trees_disjoint f1.
    Proof.
      intros. rewrite /forest_subseteq map_subseteq_spec in H.
      eapply forest_trees_disjoint_spec. intros.
      rewrite forest_trees_disjoint_spec in H0. eapply H0; eauto.
    Qed.

    Lemma forest_fold_subseteq f1 f2 :
      forest_trees_disjoint f2 →
      forest_subseteq f1 f2 →
      forest_fold f1 ⊆ forest_fold f2.
    Proof.
      intros. assert (forest_trees_disjoint f1) by (eapply forest_trees_disjoint_subseteq; eauto).
      apply map_subseteq_spec. rewrite /forest_subseteq map_subseteq_spec in H0.
      intros. eapply (forest_fold_lookup_Some_inv) in H2; eauto. destruct H2 as (?&?&?&?).
      apply H0 in H2. eapply lookup_weaken. 1: eauto. eapply forest_fold_lookup_subseteq; eauto.
    Qed.

  End map_of_forests.

  Lemma ogroup_alloc_thread i LO TP :
    i ∉ TP →
    ogroup LO TP ∗ othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i ∅
    ⊢ |==> ogroup LO ({[i]} ∪ TP) ∗ ogroupG_group i ∅.
  Proof.
    iIntros (Hi) "(F& Tx& TG)".
    rewrite /ogroup -!lock. iDestruct "F" as "(%& %& [%DomR %DomF]& %FFwf& EA& RA& EM& RM)".
    assert (LUi : Rs !! i = None).
    { apply not_elem_of_dom. rewrite DomR. auto. }
    iMod (ogroupG_group_alloc _ i with "RA") as "(RA& Ri)". 1: auto.
    iModIntro. iFrame "RA EA Ri". iSplit.
    { iPureIntro. split; auto. rewrite dom_insert_L DomR. auto. }
    iSplit.
    { iPureIntro. apply forest_to_forests_wf_roots_insert_empty; auto. }
    iFrame "EM".
    rewrite forest_to_forests_roots_insert delete_id. 2: auto.
    iApply big_sepM_insert.
    { apply forest_to_forests_lookup_None; auto. }
    iFrame "RM".
    iLeft. rewrite forest_filter_roots_empty forest_fold_empty. iFrame.
  Qed.

  Lemma ogroup_alloc_threads Θ LO TP :
    Θ ## TP →
    ogroup LO TP ∗ ([∗ set] i ∈ Θ, othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i ∅)
    ⊢ |==> ogroup LO (TP ∪ Θ) ∗
        ([∗ set] i ∈ Θ, ogroupG_group i ∅).
  Proof.
    revert TP. pattern Θ. revert Θ. apply set_ind.
    { solve_proper. }
    { iIntros (??) "T". rewrite union_empty_r_L. iDestruct "T" as "[$ _]". by iModIntro. }
    iIntros (i Θ Nin IH TP Disj) "(F& Ts)".
    iPoseProof (big_sepS_union with "Ts") as "[Ti Ts]". 1: set_solver.
    iEval (rewrite big_sepS_singleton) in "Ti".
    iMod (IH with "[$F $Ts]") as "(F& Hs)"; first set_solver.
    iMod (ogroup_alloc_thread i with "[$F $Ti]") as "(F& Hi)"; first set_solver.
    iModIntro. replace ({[i]} ∪ (TP ∪ Θ)) with (TP ∪ ({[i]} ∪ Θ)) by set_solver.
    iFrame. iApply big_sepS_union; first set_solver. rewrite big_sepS_singleton. iFrame.
  Qed.

  Lemma ogroup_exec_to_done LO TP i :
    i ∈ TP →
    othread TP ∗ ogroup LO TP ∗
    othreadG_exec i (1/2)%Qp ∗ ogroupG_group i ∅
    ⊢ |==> othread TP ∗ ogroup LO TP ∗ othreadG_done i.
  Proof.
    iIntros (Ini) "(T& F& Tx& Ri)".
    rewrite /ogroup -!lock. iDestruct "F" as "(%& %& [%DomR %DomF]& %FFwf& EA& RA& EM& RM)".
    iPoseProof (ogroupG_group_lookup with "[$RA $Ri]") as "%LUR".
    pose proof (forest_to_forests_lookup_eq F Rs _ _ LUR) as LUFF.
    rewrite forest_filter_roots_empty in LUFF.
    iPoseProof (big_sepM_delete _ _ _ _ LUFF with "RM") as "[Hex RM]".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Ri2& _)". by iPoseProof (ogroupG_group_valid with "[$Ri $Ri2]") as "%". }
    iDestruct "Hex" as "(Tx2& TG)". iCombine "Tx Tx2" as "Tx".
    rewrite forest_fold_empty.
    iMod (othread_exec_to_done with "[$T $Tx $TG]") as "[T #Td]".
    iModIntro. iFrame "T Td". iFrame "EA RA". iSplit. 1: auto. iSplit. 1: auto.
    iFrame "EM". iApply (big_sepM_delete _ _ _ _ LUFF). iFrame "RM".
    iRight. iFrame. iFrame "Td". done.
  Qed.

  Lemma ogroup_alloc_obl Ω LO TP i R k o a :
    (LO = dom (obls_filter_live Ω)) →
    (k ∉ dom Ω) →
    osat (<[k:=o]>Ω) ∗ othread TP ∗ ogroup LO TP ∗
    ogroupG_group i R ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp ∗ oblG_fuel_supply k a (1/2/2)%Qp
    ⊢ |==> osat (<[k:=o]>Ω) ∗ othread TP ∗ ogroup ({[k]} ∪ LO) TP ∗
        ⌜k ∉ R⌝ ∗ ogroupG_group i ({[k]} ∪ R) ∗ ogroupG_thread k ∅ ∗
        othreadG_owns i k 1 ∗ oblG_owner k i (1/2 + 1/2/2/2 + 1/2/2/2/2)%Qp.
  Proof.
    iIntros (HLO HFk) "(S& T& F& Ri& #Oe& Oo& Ofs)".
    iPoseProof (osat_lookup_owner with "[$S $Oe $Oo]") as "(%& %LUk)".
    rewrite lookup_insert_eq in LUk. simplify_eq.
    rewrite /ogroup -!lock. iDestruct "F" as "(%& %& [%DomR %DomF]& %FFwf& EA& RA& EM& RM)".
    iPoseProof (ogroupG_group_lookup with "[$RA $Ri]") as "%LUR".
    pose proof (forest_to_forests_lookup_eq F Rs _ _ LUR) as LUFF.
    iPoseProof (big_sepM_delete _ _ _ _ LUFF with "RM") as "[Hex RM]".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Ri2& _)". by iPoseProof (ogroupG_group_valid with "[$Ri $Ri2]") as "%". }
    iDestruct "Hex" as "(Tx& TG)".
    iMod (othread_alloc_obl with "[$S $T $TG $Oe $Oo]") as "(S& T& %Nink& TG& To& Oo)".
    assert (NLukFf : forest_fold F !! k = None).
    { apply not_elem_of_dom. rewrite DomF. eapply not_elem_of_weaken. 1: eapply HFk.
      apply subseteq_dom, obls_filter_live_subseteq. }
    iMod (ogroupG_thread_alloc _ k with "EA") as "(EA& Ek)". 1: auto.
    iMod (ogroupG_group_update _ _ _  ({[k]} ∪ R) with "[$RA $Ri]") as "[RA Ri]".
    assert (NLuk : (forest_filter_roots F R) !! k = None).
    { subst. apply not_elem_of_dom. eapply not_elem_of_weaken. 1: eapply Nink.
      unshelve epose proof (forest_to_forests_lookup_eq_wf F Rs _ _ FFwf LUR). destruct H. destruct H0.
      eapply dom_subseteq_forest_fold_dom; auto.
      eapply map_Forall_impl. 1: eapply H1. simpl. intros. apply tree_wf_root_elem. auto. }
    assert (NinkR : k ∉ R).
    { simplify_eq. apply not_elem_of_dom in NLuk. eapply not_elem_of_weaken. 1: eapply NLuk.
      destruct FFwf as (?&?&?). rewrite forest_filter_roots_dom H0.
      pose proof (union_sets_lookup_subseteq _ _ _ LUR). set_solver. }
    assert (Ini : i ∈ TP).
    { apply elem_of_dom_2 in LUR. subst. auto. }
    assert (NLukF : F !! k = None).
    { apply not_elem_of_dom. eapply not_elem_of_weaken.
      { apply not_elem_of_dom in NLukFf. eapply NLukFf. }
      destruct FFwf as (?&?&?). destruct H1. eapply dom_subseteq_forest_fold_dom; auto.
      eapply map_Forall_impl. 1: eapply H2. simpl. intros. apply tree_wf_root_elem. auto. }
    iModIntro. iFrame "S T Ri Ek To Oo". iSplit; cycle 1. 1: auto.
    assert (Eqk : <[k:=∅]> (forest_fold F) = forest_fold (<[k:=tree_singleton k]> F)).
    { rewrite forest_fold_insert_L; auto.
      - apply insert_union_singleton_l.
      - apply forest_trees_disjoint_insert; auto. destruct FFwf as (?&?&?). destruct H1. split; auto.
        apply forest_tree_disjoint_tree_singleton; auto.
        eapply map_Forall_impl; eauto. simpl. intros. apply tree_wf_root_elem. auto. }
    rewrite Eqk. iFrame "EA RA". iSplit.
    { iPureIntro. simplify_eq. rewrite !dom_insert_L. split_and !. 1: set_solver.
      rewrite forest_fold_insert_L; auto.
      - rewrite dom_union_L DomF. set_solver.
      - apply forest_trees_disjoint_insert; auto. destruct FFwf as (?&?&?). destruct H1. split; auto.
        apply forest_tree_disjoint_tree_singleton; auto.
        eapply map_Forall_impl; eauto. simpl. intros. apply tree_wf_root_elem. auto. }
    iSplit.
    { iPureIntro. replace ({[k]} ∪ R) with (R ∪ {[k]}) by set_solver.
      apply forest_to_forests_wf_forest_insert_singleton; auto. }
    assert (EqFF : forest_to_forests (<[k:=tree_singleton k]> F) (<[i:={[k]} ∪ R]> Rs)
                   = <[i:= <[k:=tree_singleton k]> (forest_filter_roots F R)]> (delete i (forest_to_forests F Rs))).
    { rewrite forest_to_forests_roots_insert forest_to_forests_forest_insert_new.
      2:{ simplify_eq. destruct FFwf as (?&?&?). eapply (not_elem_of_weaken _ _ (union_sets Rs)).
          2:{ apply elem_of_dom in Ini. destruct Ini.
              rewrite (union_sets_delete_L Rs i _ H2). set_solver. }
          rewrite -H0. eapply (not_elem_of_weaken _ _ (dom (forest_fold F))).
          2:{ destruct H1. apply dom_subseteq_forest_fold_dom; auto.
              eapply map_Forall_impl. 1: eapply H2. simpl. intros. apply tree_wf_root_elem. auto. }
          rewrite DomF. eapply (not_elem_of_weaken _ _ (dom Ω)); eauto.
          apply subseteq_dom. apply obls_filter_live_subseteq. }
      assert (forest_filter_roots (<[k:=tree_singleton k]> F) ({[k]} ∪ R) = <[k:=tree_singleton k]> (forest_filter_roots F R)).
      { rewrite forest_filter_roots_insert_in. 2: set_solver. f_equal.
        rewrite forest_filter_roots_union (forest_filter_roots_not_roots _ {[k]}).
        1: by rewrite map_empty_union.
        apply not_elem_of_dom in NLukF. set_solver. }
      rewrite H forest_to_forests_roots_delete. auto. }
    rewrite EqFF. iSplitL "EM Ofs".
    { rewrite forest_fold_insert_L; auto.
      - iApply big_sepM_union.
        { apply map_disjoint_dom. rewrite tree_singleton_dom. apply not_elem_of_dom in NLukFf. set_solver. }
        iFrame "EM". iApply big_sepM_singleton. iFrame. eauto.
      - eapply forest_trees_disjoint_insert; auto. destruct FFwf as (?&?&?). destruct H1. split; auto.
        apply forest_tree_disjoint_tree_singleton; auto.
        eapply map_Forall_impl. 1: eapply H2. simpl. intros. apply tree_wf_root_elem. auto. }
    iApply big_sepM_insert. 1: apply lookup_delete_eq.
    iFrame "RM". iLeft. iFrame "Tx". rewrite forest_fold_insert_singleton_dom; auto.
  Qed.

  (* TODO?: ogroup_alloc_obl_edge *)

  Lemma ogroup_push_obl Ω LO TP i r R k Ch α β q :
    (LO = dom (obls_filter_live Ω)) →
    r ∈ R →
    (β < α)%ord →
    osat Ω ∗ othread TP ∗ ogroup LO TP ∗
    ogroupG_group i R ∗ oblG_fuel r α ∗
    ogroupG_thread k Ch ∗ oblG_bound k β ∗ othreadG_owns i k q
    ⊢ |==> osat Ω ∗ othread TP ∗ ogroup LO TP ∗ ogroupG_group i (R ∖ {[r]}) ∗
        ogroupG_thread k ({[r]} ∪ Ch) ∗ othreadG_owns i k q.
  Proof.
    iIntros (HLO Ink LTa) "(S& T& F& Ri& Gfr& Ek& #Gbk& Tok)".
    rewrite /ogroup -!lock. iDestruct "F" as "(%& %& [%DomR %DomF]& %FFwf& EA& RA& EM& RM)".
    iPoseProof (ogroupG_group_lookup with "[$RA $Ri]") as "%LURi".
    iPoseProof (ogroupG_thread_lookup with "[$EA $Ek]") as "%LUEk".
    assert (LUi : i ∈ TP).
    { subst. apply elem_of_dom; eauto. }
    iPoseProof (osat_bound_fuel_valid_1 with "[$S $Gbk $Gfr]") as "%Nerk". 1: auto.
    pose proof (forest_to_forests_lookup_eq F Rs _ _ LURi) as LUFF.
    iPoseProof (big_sepM_delete _ _ _ _ LUFF with "RM") as "[Hex RM]".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Ri2& _)". by iPoseProof (ogroupG_group_valid with "[$Ri $Ri2]") as "%". }
    iDestruct "Hex" as "(Tx& TG)".
    iPoseProof (othread_obls_owns_elem with "[$T $TG $Tok]") as "%Ink2".
    assert (∃ ρ tρ, (forest_filter_roots F R) !! ρ = Some tρ ∧ tρ !! k = Some Ch).
    { apply elem_of_dom in Ink2. destruct Ink2.
      assert (forest_fold (forest_filter_roots F R) ⊆ forest_fold F).
      { destruct FFwf as (?&?&?). destruct H2. apply forest_fold_subseteq; auto. apply forest_filter_roots_subseteq. }
      pose proof H. eapply lookup_weaken in H. 2: eauto. rewrite LUEk in H. simplify_eq.
      eapply forest_fold_lookup_Some_inv; eauto.
      destruct FFwf as (?&?&?). destruct H3. eapply forest_trees_disjoint_subseteq; eauto. apply forest_filter_roots_subseteq. }
    destruct H as (ρ& tρ& LUρ& LUktρ).
    assert (∃ tr, forest_filter_roots F R !! r = Some tr).
    { destruct FFwf as (?&?&?). assert (r ∈ dom F).
      { rewrite H0. apply elem_of_union_sets. eauto. }
      apply elem_of_dom in H2. destruct H2. exists x. apply forest_filter_roots_lookup_Some. auto. }
    destruct H as (tr& LUr). iAssert (⌜ρ ≠ r⌝)%I as "%Ner".
    { destruct (decide (ρ = r)); auto. subst ρ. iExFalso.
      rewrite LUr in LUρ. simplify_eq. rename tρ into tr. destruct FFwf as (?&?&?).
      iClear "T EA RA Ri Ek Tok Tx TG RM".
      rewrite big_sepM_forest_fold. 2: by destruct H1.
      apply forest_filter_roots_lookup_Some in LUr. destruct LUr.
      iPoseProof (big_sepM_delete _ _ _ _ H2 with "EM") as "[EMr _]".
      destruct H1. specialize (H4 _ _ H2). simpl in H4. assert (Domk : node tr k) by (eexists; eauto).
      clear dependent i R Rs F q Ch. iStopProof. revert Ω α β LTa k Nerk Domk.
      pattern r, tr. revert r tr H4. apply tree_wf_internal_ind.
      iIntros (r tr Twfr IH ???????) "(#Gbk& S& Gfr& M)".
      pose proof Twfr. inv H. destruct (Cf !! k) eqn:LUk.
      - iPoseProof (big_sepM_insert with "M") as "[Mr _]". 1: auto.
        iDestruct "Mr" as "(%& #Ge& Gfs& Cs)". apply elem_of_dom_2 in LUk.
        iPoseProof (big_sepS_elem_of _ _ _ LUk with "Cs") as "(%& %& #Gec& Gfc)".
        iPoseProof (oblG_fuel_supply_compare with "[$Gfs $Gfr]") as "%".
        iPoseProof (osat_bound_fuel_valid_2 with "[$S $Gbk $Gfc]") as "%".
        assert (α <= β)%ord.
        { etrans; first eauto. etrans; eauto. }
        iPureIntro. eapply (Ord.lt_not_le LTa H5).
      - assert (∃ c ct, Cf !! c = Some ct ∧ node ct k).
        { eapply forest_merge_not_child_of_root; eauto. apply not_elem_of_dom; auto. }
        destruct H as (c& ct& LUc& Inck).
        iPoseProof (big_sepM_insert with "M") as "[Mr MC]". 1: auto.
        iDestruct "Mr" as "(%& #Ge& Gfs& Cs)".
        iPoseProof (big_sepS_delete _ _ c with "Cs") as "[(%γ& %LEc& #Gec& Gfc) _]". 1: by apply elem_of_dom.
        pose proof H3. specialize (H3 _ _ LUc). simpl in H3.
        iPoseProof (oblG_fuel_supply_compare with "[$Gfs $Gfr]") as "%".
        iPoseProof (IH c ct with "[$Gbk $S $Gfc MC]") as "%"; auto.
        { eapply forest_merge_internal_Forall; eauto. }
        { eapply forest_merge_subseteq_Forall; eauto. }
        { eapply Ord.lt_le_lt. 1: eapply LTa. etrans; eauto. }
        { intro. simplify_eq. }
        { iApply (big_sepM_subseteq with "MC"). eapply forest_fold_lookup_subseteq; eauto. }
    }
    iPoseProof (big_sepM_delete _ _ _ _ LUEk with "EM") as "[EMk EM]".
    iDestruct "EMk" as "(%& #Gek& Gfsk& Chk)".
    iMod (osat_bound_fuel_supply with "[$S $Gbk $Gfsk]") as "(%& S& [%LE1 %LE2]& Gfsk)".
    iMod (ogroupG_group_update _ _ _ (R ∖ {[r]}) with "[$RA $Ri]") as "(RA& Ri)".
    iMod (ogroupG_thread_update _ _ _ ({[r]} ∪ Ch) with "[$EA $Ek]") as "(EA& Ek)".
    iModIntro. iFrame "S T Ri Ek Tok".
    iExists (<[i:=R ∖ {[r]}]> Rs), (forest_move_tree F ρ tρ r tr k Ch).
    assert (LUFr : F !! r = Some tr).
    { eapply lookup_weaken. 1: eauto. apply forest_filter_roots_subseteq. }
    assert (LUFρ : F !! ρ = Some tρ).
    { eapply lookup_weaken. 1: eauto. apply forest_filter_roots_subseteq. }
    iSplit.
    { iPureIntro. split.
      { rewrite dom_insert_L DomR. set_solver. }
      rewrite forest_fold_move_tree_dom; auto. }
    iSplit.
    { iPureIntro. eapply forest_to_forests_wf_forest_move_tree; eauto. }
    iFrame "RA". iSplitL "EA".
    { destruct FFwf as (?&?&?).
      replace (forest_fold (forest_move_tree F ρ tρ r tr k Ch)) with (<[k:={[r]} ∪ Ch]> (forest_fold F)); first auto.
      assert (FW' : forest_wf (forest_move_tree F ρ tρ r tr k Ch)).
      { apply forest_move_tree_wf; auto. }
      rewrite /forest_move_tree. rewrite forest_fold_insert_L; auto.
      { destruct H1. rewrite (forest_fold_delete_L _ _ _ H1 LUFr).
        rewrite (forest_fold_delete_L (delete r F) ρ tρ).
        { rewrite /tree_insert. rewrite map_union_assoc -insert_union_l. auto. }
        { apply forest_trees_disjoint_delete; auto. }
        { rewrite lookup_delete_ne; auto. }
      }
      { destruct FW'. auto. }
      { apply lookup_delete_eq. }
    }
    iSplitR "RM Tx TG".
    { rewrite /forest_move_tree.

      TODO

        apply forest_trees_disjoint_insert. 1: apply lookup_delete_eq. split.
        - apply forest_tree_disjoint_forest_fold_inv. rewrite /tree_insert.
          eapply map_disjoint_insert_l_2.
          {

            TODO

          apply map_disjoint_dom.

          apply forest_tree_disjoint_insert. :
  ∀ {V : Type} {EqDecision0 : EqDecision V} {H : Countable V} (f : forest V) (ρ : V) (t s : tree V),
    f !! ρ = None → forest_tree_disjoint (<[ρ:=t]> f) s ↔ t ##ₘ s ∧ forest_tree_disjoint f s


    TODO


forest_to_forests_wf_forest_move_tree:
  ∀ {K V : Type} {EqDecision0 : EqDecision K} {Countable0 : Countable K} {EqDecision1 : EqDecision V} 
    {Countable1 : Countable V} (F : forest V) (Rs : gmap K (gset V)) (k : K) (rs : gset V) (ρ : V) (ρt : tree V) 
    (r : V) (rt : tree V) (π : V) (πC : gset V),
    forest_to_forests_wf F Rs
    → Rs !! k = Some rs
      → r ∈ rs
        → ρ ≠ r
          → F !! r = Some rt
            → F !! ρ = Some ρt
              → ρt !! π = Some πC → forest_to_forests_wf (forest_move_tree F ρ ρt r rt π πC) (<[k:=rs ∖ {[r]}]> Rs)
forest_to_forests_forest_move_tree:
  ∀ {K V : Type} {EqDecision0 : EqDecision K} {Countable0 : Countable K} {EqDecision1 : EqDecision V} 
    {Countable1 : Countable V} (F : forest V) (Rs : gmap K (gset V)) (ρ : V) (ρt : tree V) (r : V) (rt : tree V) 
    (π : V) (πC : gset V),
    ρ ≠ r
    → forest_to_forests (forest_move_tree F ρ ρt r rt π πC) Rs =
      (λ rs : gset V,
         if decide (ρ ∈ rs)
         then <[ρ:=tree_insert ρt r rt π πC]> (delete r (forest_filter_roots F rs))
         else delete r (forest_filter_roots F rs)) <$>
      Rs
    
    

  Lemma ogroup_delete_obl TP LO i R k :
    k ∈ R →
    othread TP ∗ ogroup LO TP ∗
    ogroupG_group i R ∗ ogroupG_thread k ∅ ∗
    othreadG_owns i k 1
    ⊢ |==> othread TP ∗ ogroup (LO ∖ {[k]}) TP ∗
        ogroupG_group i (R ∖ {[k]}) ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ink) "(T& F& Ri& Ek& To)".
    rewrite /ogroup -!lock. iDestruct "F" as "(%& %& [%DomR %DomE]& EA& RA& M)".
    iPoseProof (ogroupG_thread_lookup with "[$EA $Ek]") as "%LUk".
    iPoseProof (ogroupG_group_lookup with "[$RA $Ri]") as "%LUR".
    assert (Ini : i ∈ TP).
    { apply elem_of_dom_2 in LUR. subst. auto. }
    iPoseProof (big_sepM_delete _ _ _ _ LUR with "M") as "[Mi M]".
    iDestruct "Mi" as "(%& [%DomF %WFF]& Hex& HF)".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Ri2& _)". by iPoseProof (ogroupG_group_valid with "[$Ri $Ri2]") as "%". }
    iDestruct "Hex" as "(Tx& TG)".
    iPoseProof (othread_obls_owns_elem with "[$T $TG $To]") as "%Ink2".
    iMod (othread_delete_obl with "[$T $TG $To]") as "(T& TG& Oo)".
    iMod (ogroupG_thread_delete with "[$EA $Ek]") as "EA".
    iMod (ogroupG_group_update _ _ _  (R ∖ {[k]}) with "[$RA $Ri]") as "[RA Ri]".
    iModIntro. iFrame "T Ri Oo".
    iFrame "EA RA". iSplit.
    { iPureIntro. subst. rewrite !dom_insert_L. split_and !. 1: set_solver.
      rewrite dom_delete_L. auto. }
    iApply big_sepM_insert_delete. iSplitR "M"; cycle 1.
    { iApply (big_sepM_impl with "M"). iIntros "!> %%% (%& %& $& M)". iSplit; first auto.
      iApply (big_sepM_impl with "M"). iIntros "!> %%% M".
      iApply (big_sepM_impl with "M"). iIntros "!> %%% H". iDestruct "H" as "(%& $)".
      iPureIntro. assert (k ≠ k2); [| rewrite lookup_delete_ne; auto].
      destruct H0. simplify_eq.

      TODO

      apply elem_of_dom_2 in H3. rewrite DomE in H3.
      pose proof (obls_filter_live_subseteq Ω).
      intros <-. apply subseteq_dom in H0. set_solver + HFk H3 H0. }
    iExists (forest_insert Fo k (tree_singleton k)). iSplit.
    { iPureIntro. split.
      - rewrite /forest_insert dom_insert_L. subst. auto.
      - apply forest_insert_singleton_wf; auto. apply not_elem_of_dom; auto. }
    iSplitL "Tx TG".
    { iLeft. iFrame "Tx". rewrite forest_fold_insert_singleton_dom; auto. }
    iApply big_sepM_insert. 1: auto.
    iSplitR "HF"; cycle 1.
    { iApply (big_sepM_impl with "HF"). iIntros "!> %%% M".
      iApply (big_sepM_impl with "M"). iIntros "!> %%% H". iDestruct "H" as "(%& $)".
      iPureIntro.  assert (k ≠ k1); [| rewrite lookup_insert_ne; auto].
      simplify_eq. apply elem_of_dom_2 in H1. rewrite DomE in H1.
      pose proof (obls_filter_live_subseteq Ω).
      intros <-. apply subseteq_dom in H2. set_solver + HFk H1 H2. }
    iApply big_sepM_singleton. iFrame. iSplit; auto.
    rewrite lookup_insert_eq; auto.
  Qed.

    TODO

    iMod (othread_alloc_obl with "[$S $T $TG $Oe $Oo]") as "(S& T& %Nink& TG& To& Oo)".
    iMod (ogroupG_thread_alloc _ k with "EA") as "(EA& Ek)".
    { apply not_elem_of_dom. rewrite DomE. eapply not_elem_of_weaken. 1: eapply HFk.
      apply subseteq_dom, obls_filter_live_subseteq. }
    iMod (ogroupG_group_update _ _ _  ({[k]} ∪ R) with "[$RA $Ri]") as "[RA Ri]".
    assert (NinkR : k ∉ R).
    { simplify_eq. eapply not_elem_of_weaken. 1: eapply Nink.
      destruct WFF. apply dom_subseteq_forest_fold_dom; auto.
      eapply map_Forall_impl. 1: eapply H0.
      simpl. intros. apply tree_wf_root_elem. auto. }
    assert (NLuk : Fo !! k = None).
    { subst. apply not_elem_of_dom; auto. }
    iModIntro. iFrame "S T Ri Ek To Oo". iSplit; cycle 1. 1: auto.
    iFrame "EA RA". iSplit.
    { iPureIntro. subst. rewrite !dom_insert_L. split_and !. 1: set_solver.
      rewrite DomE. set_solver. }
    iApply big_sepM_insert_delete. iSplitR "M"; cycle 1.
    { iApply (big_sepM_impl with "M"). iIntros "!> %%% (%& %& $& M)". iSplit; first auto.
      iApply (big_sepM_impl with "M"). iIntros "!> %%% M".
      iApply (big_sepM_impl with "M"). iIntros "!> %%% H". iDestruct "H" as "(%& $)".
      iPureIntro.  assert (k ≠ k2); [| rewrite lookup_insert_ne; auto].
      destruct H0. simplify_eq. apply elem_of_dom_2 in H3. rewrite DomE in H3.
      pose proof (obls_filter_live_subseteq Ω).
      intros <-. apply subseteq_dom in H0. set_solver + HFk H3 H0. }
    iExists (forest_insert Fo k (tree_singleton k)). iSplit.
    { iPureIntro. split.
      - rewrite /forest_insert dom_insert_L. subst. auto.
      - apply forest_insert_singleton_wf; auto. apply not_elem_of_dom; auto. }
    iSplitL "Tx TG".
    { iLeft. iFrame "Tx". rewrite forest_fold_insert_singleton_dom; auto. }
    iApply big_sepM_insert. 1: auto.
    iSplitR "HF"; cycle 1.
    { iApply (big_sepM_impl with "HF"). iIntros "!> %%% M".
      iApply (big_sepM_impl with "M"). iIntros "!> %%% H". iDestruct "H" as "(%& $)".
      iPureIntro.  assert (k ≠ k1); [| rewrite lookup_insert_ne; auto].
      simplify_eq. apply elem_of_dom_2 in H1. rewrite DomE in H1.
      pose proof (obls_filter_live_subseteq Ω).
      intros <-. apply subseteq_dom in H2. set_solver + HFk H1 H2. }
    iApply big_sepM_singleton. iFrame. iSplit; auto.
    rewrite lookup_insert_eq; auto.
  Qed.




  TODO

  (* TODO *)
    (* alloc obl (root), delete obl (root & Ch = ∅) *)
    (* move obl: root-edge (burns fuel), edge-root (no fuel), edge-edge (burns fuel) *)
    (* replace node obl *)
    (* progress of a tree & a forest *)


End ogroup.

(* Allocation of an initial ogroup protocol. *)
Definition ogroup_alloc `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!ogroupGS A Σ} :
  ⊢ |==> ∃ _ : ogroupGS A Σ, osuspend ∅ ∗ ogroup ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=gmap_viewR oid unitUR) ⊤)) as (γE) "HE";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO (prodO positiveO oidO) (leibnizO A)))) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=reservation_mapUR mono_natUR) ⊤)) as (γW) "HW";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR oid unitUR)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OgroupG SI A _ _ γE γS γW γI).
  rewrite /ogroup /osuspend -!lock /ogroup_aux.
  iSplitR "HE".
  - iExists ∅.
    replace (⊤ ∖ gset_to_coPset (∅ : gset oid)) with (⊤ : coPset); [| set_solver].
    replace (gset_to_gmap () ∅) with (∅ : gmap oid unit); [| set_solver].
    iFrame. iSplitR; done.
  - iExists ∅.
    replace (⊤ ∖ gset_to_coPset (∅ : gset oid)) with (⊤ : coPset); [| set_solver].
    iFrame. iSplitR; done.
Qed.
