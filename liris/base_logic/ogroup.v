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
        ⌜ dom GM = TP ∧ disjoint_sets GM ∧ disjoint_sets KM ⌝ ∗
        ogroupG_thread_auth GM ∗
        ogroupG_group_auth KM ∗
        ogroupG_fuel_token_id (⊤ ∖ (gset_to_coPset (dom KM))) ∗
        ([∗ map] i ↦ G ∈ GM,
           ((othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i ∅)
            ∨ (othreadG_done i ∗ ogroupG_thread i ∅ ∗ ⌜G = ∅⌝)) ∗
           ([∗ set] g ∈ G,
              ∃ (K : oids) β, ⌜KM !! g = Some K⌝ ∗ ogroupG_bound g β ∗
                              ([∗ set] k ∈ K, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k))))%I.

TODO

        ([∗ map] π ↦ Ch ∈ forest_fold F,
           ∃ β, oblG_elem π ∗ oblG_fuel_supply π β (1/2/2)%Qp ∗
                ([∗ set] c ∈ Ch, ∃ a, ⌜ WFOCM.leR β a ⌝ ∗ oblG_elem c ∗ oblG_fuel c a)) ∗
        ([∗ map] i ↦ f ∈ forest_to_forests F Rs,
           ((othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i (dom (forest_fold f))) ∨
              (othreadG_done i ∗ ogroupG_group i ∅ ∗ ⌜ f = ∅ ⌝))))%I.

(* Global invariant for threads' obligation fragments and sessions. *)
Definition oproxy `{SI : indexT} {Σ} `{!@osatGS.osatGS _ Σ} `{!othreadGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (Df : gset session),
        othreadG_fuel_token_id (⊤ ∖ (gset_to_coPset Df)) ∗
        othreadG_proxy_session_token TP ∗
        othreadG_proxy_obls_token TP ∗
        ([∗ set] i ∈ TP,
           ∃ (Ks : gmap proxy (oids)) (Ss : gmap proxy (session)),
             ⌜ dom Ks = dom Ss ⌝ ∗
             othreadG_proxy_obls_auth i Ks ∗
             othreadG_proxy_session_auth i Ss (1/2)%Qp ∗
             ((∃ G, othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i G ∗
                    ⌜ G = union_sets Ks ∧ disjoint_sets Ks ⌝) ∨
                (othreadG_done i ∗ othreadG_proxy_session_auth i Ss (1/2)%Qp ∗ ⌜ Ks = ∅ ∧ Ss = ∅ ⌝)) ∗
             ([∗ map] K;s ∈ Ks;Ss,
                ∃ β, othreadG_bound s β ∗
                     ([∗ set] k ∈ K, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)))
    )%I.

Section ogroup.
  Context `{SI : indexT} `{OSAT : !osatGS.osatGS Σ} `{OTH : !othreadGS.othreadGS Σ} `{!ogroupGS Σ} `{OMF : !ord_mono_fun_class}.

  Global Instance ogroupG_thread_timeless π Ch : Timeless (ogroupG_thread π Ch).
  Proof. rewrite /ogroupG_thread. apply _. Qed.
  Global Instance ogroupG_thread_auth_timeless Es : Timeless (ogroupG_thread_auth Es).
  Proof. rewrite /ogroupG_thread_auth. apply _. Qed.

  Global Instance ogroupG_group_timeless i R : Timeless (ogroupG_group i R).
  Proof. rewrite /ogroupG_group. apply _. Qed.
  Global Instance ogroupG_group_auth_timeless Rs : Timeless (ogroupG_group_auth Rs).
  Proof. rewrite /ogroupG_group_auth. apply _. Qed.

  (** Edge rules *)
  Lemma ogroupG_thread_alloc Es π :
    Es !! π = None →
    ogroupG_thread_auth Es
    ⊢ |==> ogroupG_thread_auth (<[π:=∅]>Es) ∗ ogroupG_thread π ∅.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread.
    iIntros (Hi) "H".
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ π (DfracOwn 1) (∅ : oids)); try done. }
    iDestruct "H" as "[H Ho]". by iFrame.
  Qed.

  Lemma ogroupG_thread_update Es π Ch1 Ch2 :
    ogroupG_thread_auth Es ∗
    ogroupG_thread π Ch1
    ⊢ |==> ogroupG_thread_auth (<[π:=Ch2]>Es) ∗
        ogroupG_thread π Ch2.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread -!own_op.
    apply own_update, gmap_view_replace. done.
  Qed.

  Lemma ogroupG_thread_delete Es π Ch :
    ogroupG_thread_auth Es ∗
    ogroupG_thread π Ch
    ⊢ |==> ogroupG_thread_auth (delete π Es).
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread -!own_op.
    apply own_update, gmap_view_delete.
  Qed.

  Lemma ogroupG_thread_lookup Es π Ch :
    ogroupG_thread_auth Es ∗
    ogroupG_thread π Ch
    ⊢ ⌜ Es !! π = Some Ch ⌝.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H. destruct H as (_&_&?).
    iPureIntro. apply leibniz_equiv in H. auto.
  Qed.

  Lemma ogroupG_thread_valid π Ch1 Ch2 :
    ogroupG_thread π Ch1 ∗ ogroupG_thread π Ch2 ⊢ False.
  Proof.
    rewrite /ogroupG_thread -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_frag_op_valid in H. destruct H as (?&?). done.
  Qed.

  (** Root rules *)
  Lemma ogroupG_group_alloc Rs i :
    Rs !! i = None →
    ogroupG_group_auth Rs
    ⊢ |==> ogroupG_group_auth (<[i:=∅]>Rs) ∗ ogroupG_group i ∅.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group.
    iIntros (Hi) "H".
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracOwn 1) (∅ : oids)); try done. }
    iDestruct "H" as "[H Ho]". by iFrame.
  Qed.

  Lemma ogroupG_group_update Rs i R1 R2 :
    ogroupG_group_auth Rs ∗
    ogroupG_group i R1
    ⊢ |==> ogroupG_group_auth (<[i:=R2]>Rs) ∗
        ogroupG_group i R2.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -!own_op.
    apply own_update, gmap_view_replace. done.
  Qed.

  Lemma ogroupG_group_delete Rs i R :
    ogroupG_group_auth Rs ∗
    ogroupG_group i R
    ⊢ |==> ogroupG_group_auth (delete i Rs).
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -!own_op.
    apply own_update, gmap_view_delete.
  Qed.

  Lemma ogroupG_group_lookup Rs i R :
    ogroupG_group_auth Rs ∗
    ogroupG_group i R
    ⊢ ⌜ Rs !! i = Some R ⌝.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H. destruct H as (_&_&?).
    iPureIntro. apply leibniz_equiv in H. auto.
  Qed.

  Lemma ogroupG_group_valid i R1 R2 :
    ogroupG_group i R1 ∗ ogroupG_group i R2 ⊢ False.
  Proof.
    rewrite /ogroupG_group -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_frag_op_valid in H. destruct H as (?&?). done.
  Qed.

  (** ogroup rules *)

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
