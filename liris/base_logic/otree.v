From iris.algebra Require Import agree gmap gmap_view reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.algebra Require Export tree.
From liris.base_logic Require Import osat othread.

(** The ghost state for liveness obligation forest *)
Module otreeGS.

  Class otreeGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OtreeGpreS {
        otreeGpreS_edge : inG Σ (reservation_mapUR (gmap_viewR obl_id unitUR));
        (* Data for suspending an obligation: returning thread_id, blocking parent id *)
        otreeGpreS_suspend : inG Σ (reservation_mapUR (gmap_viewR positive (agreeR (prodO positiveO obl_idO))));
        otreeGpreS_wait : inG Σ (reservation_mapUR (reservation_mapUR mono_natUR));
        otreeGpreS_elem : inG Σ (gmap_viewR obl_id unitUR);
      }.

  Class otreeGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OtreeG {
        otree_inG : otreeGpreS Σ;
        edge_name : gname;
        suspend_name : gname;
        wait_name : gname;
        elem_name : gname;
      }.

  Definition otreeΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR obl_id unitUR));
      GFunctor (reservation_mapUR (gmap_viewR positive (agreeR (prodO positiveO obl_idO))));
      GFunctor (reservation_mapUR (reservation_mapUR mono_natUR));
      GFunctor (gmap_viewR positive unitUR)
      ].

  Global Instance subG_otreeΣ `{SI : indexT} {Σ} : subG (otreeΣ) Σ → (otreeGpreS Σ).
  Proof. solve_inG. Qed.

End otreeGS.
Import otreeGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances otree_inG
  otreeGpreS_edge otreeGpreS_suspend otreeGpreS_wait otreeGpreS_elem.

(* Edge *)
Definition otreeG_edge `{SI : indexT} `{!otreeGS Σ} (π k : obl_id) (q : Qp) : iProp Σ :=
  own edge_name (reservation_map_data π (gmap_view_frag k (DfracOwn q) ())).
Global Typeclasses Opaque otreeG_edge.
Global Instance: Params (@otreeG_edge) 5 := {}.

(* Suspend knowledge *)
Definition otreeG_suspend `{SI : indexT} `{!otreeGS Σ} (k : obl_id) (x : positive) (θ : positive) (π : obl_id) : iProp Σ :=
  own suspend_name (reservation_map_data k (gmap_view_frag x DfracDiscarded (to_agree (θ, π)))).
Global Typeclasses Opaque otreeG_suspend.
Global Instance: Params (@otreeG_suspend) 7 := {}.

(* Wait token *)
Definition otreeG_wait `{SI : indexT} `{!otreeGS Σ} (k : obl_id) (x : positive) (q : Qp) : iProp Σ :=
  own wait_name (reservation_map_data k (reservation_map_data x (●MN{#q} 0))).
Global Typeclasses Opaque otreeG_wait.
Global Instance: Params (@otreeG_wait) 5 := {}.

Definition otreeG_wait_null `{SI : indexT} `{!otreeGS Σ} (k : obl_id) (x : positive) : iProp Σ :=
  own wait_name (reservation_map_data k (reservation_map_data x (●MN 1))).
Global Typeclasses Opaque otreeG_wait_null.
Global Instance: Params (@otreeG_wait_null) 5 := {}.

(* Elem: keeps the fact that a key is inside a map *)
Definition otreeG_elem `{SI : indexT} `{!otreeGS Σ} (k : obl_id) : iProp Σ :=
  own elem_name (gmap_view_frag k DfracDiscarded ()).
Global Typeclasses Opaque otreeG_elem.
Global Instance: Params (@otreeG_elem) 4 := {}.

(* Global invariant for suspending obligations and waiting. *)
Definition osuspend `{SI : indexT} `{WF : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WF ps T Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OSus : gmap obl_id (gmap positive (prod positive obl_id))),
        (⌜ dom OSus = D ⌝) ∗
        (own suspend_name (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO positiveO obl_idO))) (⊤ ∖ gset_to_coPset D))) ∗
        (own wait_name (reservation_map_token (A:=reservation_mapUR mono_natUR) (⊤ ∖ gset_to_coPset D))) ∗
        (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () D))) ∗
        ([∗ map] k ↦ KSus ∈ OSus,
           (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> KSus)))) ∗
           (own wait_name (reservation_map_data k (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset (dom KSus))))) ∗
           ([∗ map] x ↦ '(θ, π) ∈ KSus,
              ((othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1) ∨
                 (othreadG_owns θ k true (1/2)%Qp ∗ otreeG_wait k x (1/2)%Qp ∗ oblG_done π)) ∨
                otreeG_wait_null k x)
        )
    )%I.

(* Global invariant for the obligation forest state. *)
Definition otree `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OTree : cgraph obl_id unitO) (OOwner : gmap obl_id (option positive)),
        (⌜ dom OTree = D ∧ dom OOwner = D ∧ cgraph_wf OTree ⌝) ∗
        (⌜ ∀ π k, descendant OTree π k → OOwner !! π = OOwner !! k ⌝) ∗
        (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D))) ∗
        ([∗ map] k ↦ KCh ∈ OTree,
           (own edge_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) KCh))) ∗
           ((* This obligation is live and has enough transfer and progress credits for chiledren and... *)
             ((∃ α β, oblG_transfer_supply k α (1/2)%Qp ∗ oblG_progress_supply k β (1/2)%Qp ∗
                      ([∗ set] c ∈ (dom KCh),
                         ∃ α' β', ⌜ WFOCM.leR α α' ∧ WFOCM.leR β β' ⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')
              ) ∗
              (* is a root or... *)
              (∃ θ, ⌜ root OTree k ∧ OOwner !! k = Some (Some θ) ⌝ ∗
                    oblG_owner k θ (1/2/2)%Qp ∗
                    othreadG_owns θ k true (1/2)%Qp) ∨
                (* is an internal node, and is suspended *)
                (∃ τ π, ⌜ parent OTree k π ∧ OOwner !! k = Some (Some τ) ⌝ ∗
                        oblG_owner k τ (1/2)%Qp ∗
                        ∃ θ, othreadG_owns θ k false (1/2)%Qp ∗
                             (∃ x, otreeG_suspend k x θ π ∗ otreeG_wait k x (1/2)%Qp))
             ) ∨
               (* Or this obligation is done *)
               (oblG_done k ∗ ⌜ root OTree k ∧ KCh = ∅ ∧ OOwner !! k = Some None ⌝)
        ))
    )%I.

Section otree.
  Context `{SI : indexT} `{WFA : WFOCM.pack A}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}.
  Context `{Ξ : obl_class A ps positive WFOCM.ltR}.

  Global Instance otreeG_suspend_persistent k x θ π : Persistent (otreeG_suspend k x θ π).
  Proof. rewrite /otreeG_suspend. apply _. Qed.
  Global Instance otreeG_elem_persistent k : Persistent (otreeG_elem k).
  Proof. rewrite /otreeG_elem. apply _. Qed.

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

  (** Elem rules *)
  Lemma otreeG_elem_alloc (D : gset obl_id) k :
    k ∉ D →
    (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () D)))
    ⊢  |==> (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () ({[k]} ∪ D)))) ∗
            otreeG_elem k.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ k (DfracDiscarded) ()); try done.
      rewrite lookup_gset_to_gmap_None; done.      
    }
    iDestruct "H" as "[H He]". rewrite /otreeG_elem. iFrame "He".
    rewrite gset_to_gmap_union_singleton. done.
  Qed.

  Lemma otreeG_elem_elem k (D : gset obl_id) :
    (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () D))) ∗
    otreeG_elem k
    ⊢ ⌜ k ∈ D ⌝.
  Proof.
    rewrite /otreeG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro. apply lookup_gset_to_gmap_Some in H1.
    by destruct H1.
  Qed.

  (** Suspend rules *)
  Lemma otreeG_suspend_alloc_map D k :
    k ∉ D →
    (own suspend_name (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO positiveO obl_idO))) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own suspend_name (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO positiveO obl_idO))) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap positive _))))).
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap positive _))) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma otreeG_suspend_alloc k (KSus : gmap positive (prod positive obl_id)) x θ π :
    KSus !! x = None →
    (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> KSus))))
    ⊢ |==> (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> (<[x := (θ, π)]>KSus))))) ∗
           otreeG_suspend k x θ π.
  Proof.
    iIntros (Hx) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ x (DfracDiscarded) (to_agree (θ, π))); try done.
      rewrite lookup_fmap Hx. done.
    }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Hs]".
    rewrite /otreeG_suspend. iFrame "Hs".
    rewrite fmap_insert. by iFrame.
  Qed.
  Lemma otreeG_suspend_lookup k KSus x θ π :
    (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> KSus)))) ∗
    otreeG_suspend k x θ π
    ⊢ ⌜ KSus !! x = Some (θ, π) ⌝.
  Proof.
    rewrite /otreeG_suspend -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H1.
    destruct H1 as (?&_&_&?&?&?). iPureIntro.
    rewrite lookup_fmap in H1. destruct (KSus !! x) eqn:HK.
    - inv H1. apply to_agree_included_L in H3. by subst.
    - done.
  Qed.

  Lemma otreeG_suspend_agree k x θ1 θ2 π1 π2 :
    otreeG_suspend k x θ1 π1 ∗ otreeG_suspend k x θ2 π2 ⊢ ⌜ θ1 = θ2 ∧ π1 = π2 ⌝.
  Proof.
    rewrite /otreeG_suspend -own_op -reservation_map_data_op -gmap_view_frag_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%". iPureIntro.
    apply reservation_map_data_valid, gmap_view_frag_valid in H1.
    destruct H1 as [_ ?]. apply to_agree_op_valid_L in H1. by inv H1.
  Qed.

  (** Wait rules *)
  Lemma otreeG_wait_alloc_map D k :
    k ∉ D →
    (own wait_name (reservation_map_token (A:=reservation_mapUR mono_natUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own wait_name (reservation_map_token (A:=reservation_mapUR mono_natUR) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           (own wait_name (reservation_map_data k (reservation_map_token (A:=mono_natUR) ⊤))).
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (reservation_map_token ⊤ : reservation_mapUR mono_natUR) with "Htk") as "[Htk >H]"; auto.
    { apply reservation_map_token_valid. }
    by iFrame.
  Qed.

  Lemma otreeG_wait_alloc k X x :
    x ∉ X →
    own wait_name (reservation_map_data k (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset X)))
    ⊢ |==> (own wait_name (reservation_map_data k (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset ({[x]} ∪ X))))) ∗
           otreeG_wait k x 1.
  Proof.
    iIntros (Hx) "H".
    rewrite (reservation_map_token_difference (gset_to_coPset {[x]}) (⊤ ∖ gset_to_coPset X)); cycle 1.
    { apply elem_of_subseteq. intros. rewrite elem_of_difference. split; first set_solver.
      intro F. rewrite !elem_of_gset_to_coPset in H1 F. set_solver.
    }
    rewrite reservation_map_data_op. iDestruct "H" as "[Htk H]".
    assert (⊤ ∖ gset_to_coPset X ∖ gset_to_coPset {[x]} = ⊤ ∖ gset_to_coPset ({[x]} ∪ X)).
    { apply leibniz_equiv. intros y. rewrite !elem_of_difference. split; intros.
      - destruct H1 as ((_&?)&?). split; first set_solver. intros F. apply elem_of_gset_to_coPset, elem_of_union in F.
        destruct F; [apply H2 | apply H1]; apply elem_of_gset_to_coPset; set_solver.
      - destruct H1 as (_&?). split; first (split; first set_solver);
          intros F; apply elem_of_gset_to_coPset in F; apply H1, elem_of_gset_to_coPset; set_solver.
    }
    rewrite H1. iFrame "H".
    iMod (own_update with "Htk") as "H".
    { eapply reservation_map_update. eapply (reservation_map_alloc _ x (●MN 0)).
      - apply elem_of_gset_to_coPset; set_solver.
      - apply mono_nat_auth_valid.
    }
    by iFrame.
  Qed.

  Lemma otreeG_wait_to_null k x :
    otreeG_wait k x 1 ⊢ |==> otreeG_wait_null k x.
  Proof.
    rewrite /otreeG_wait /otreeG_wait_null.
    apply own_update, reservation_map_update, reservation_map_update, mono_nat_update.
    auto.
  Qed.
  Lemma otreeG_wait_null_false k x q :
    otreeG_wait k x q ∗ otreeG_wait_null k x ⊢ False.
  Proof.
    rewrite /otreeG_wait /otreeG_wait_null -own_op -!reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    iPureIntro. apply reservation_map_data_valid, reservation_map_data_valid, mono_nat_auth_dfrac_op_valid in H1.
    by destruct H1.
  Qed.

  Lemma otreeG_wait_frac_op k x q1 q2 q :
    q = (q1 + q2)%Qp →
    otreeG_wait k x q1 ∗ otreeG_wait k x q2 ⊣⊢ otreeG_wait k x q.
  Proof.
    intros; subst. rewrite /otreeG_wait.
    rewrite -own_op -!reservation_map_data_op -mono_nat_auth_dfrac_op dfrac_op_own.
    done.
  Qed.
  Lemma otreeG_wait_div_2 k x q:
    otreeG_wait k x (q/2) ∗ otreeG_wait k x (q/2) ⊣⊢ otreeG_wait k x q.
  Proof. rewrite otreeG_wait_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma otreeG_wait_valid k x q :
    otreeG_wait k x q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /otreeG_wait. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply reservation_map_data_valid, mono_nat_auth_dfrac_valid in V. done.
  Qed.

  Lemma otreeG_wait_to_null_2 k x q1 q2 :
    (q1 + q2 = 1)%Qp →
    otreeG_wait k x q1 ∗ otreeG_wait k x q2 ⊢ |==> otreeG_wait_null k x.
  Proof.
    iIntros (Hq) "H".
    iPoseProof (otreeG_wait_frac_op with "H") as "H"; first (rewrite Hq; reflexivity).
    by iApply otreeG_wait_to_null.
  Qed.

  (** Edge rules *)
  Lemma otreeG_edge_alloc_map D π :
    π ∉ D →
    (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset ({[π]} ∪ D)))) ∗
           (own edge_name (reservation_map_data π (gmap_view_auth (DfracOwn 1) (∅ : gmap obl_id unit)))).
  Proof.
    iIntros (Hπ) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ π (gmap_view_auth (DfracOwn 1) (∅ : gmap obl_id unit)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma otreeG_edge_alloc π (KCh : gmap obl_id unit) k :
    KCh !! k = None →
    (own edge_name (reservation_map_data π (gmap_view_auth (DfracOwn 1) KCh)))
    ⊢ |==> (own edge_name (reservation_map_data π (gmap_view_auth (DfracOwn 1) (<[k:=()]>KCh)))) ∗
           otreeG_edge π k 1.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ k (DfracOwn 1) ()); try done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]".
    rewrite /otreeG_edge. by iFrame.
  Qed.
  Lemma otreeG_edge_delete π (KCh : gmap obl_id unit) k :
    (own edge_name (reservation_map_data π (gmap_view_auth (DfracOwn 1) KCh))) ∗
    otreeG_edge π k 1
    ⊢ |==> (own edge_name (reservation_map_data π (gmap_view_auth (DfracOwn 1) (delete k KCh)))).
  Proof.
    rewrite -own_op -reservation_map_data_op. apply own_update, reservation_map_update.
    apply gmap_view_delete.
  Qed.
  Lemma otreeG_edge_lookup π (KCh : gmap obl_id ()) k q :
    (own edge_name (reservation_map_data π (gmap_view_auth (DfracOwn 1) KCh))) ∗
    otreeG_edge π k q
    ⊢ ⌜ KCh !! k = Some tt ⌝.
  Proof.
    rewrite /otreeG_edge -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H1.
    destruct H1 as (?&_&_&?&?&?). iPureIntro.
    rewrite H1. by destruct x.
  Qed.

  Lemma otreeG_edge_frac_op π k q1 q2 q :
    q = (q1 + q2)%Qp →
    otreeG_edge π k q1 ∗ otreeG_edge π k q2 ⊣⊢ otreeG_edge π k q.
  Proof.
    intros; subst. rewrite /otreeG_edge.
    rewrite -own_op -reservation_map_data_op -gmap_view_frag_op dfrac_op_own.
    done.
  Qed.
  Lemma otreeG_edge_div_2 π k q:
    otreeG_edge π k (q/2) ∗ otreeG_edge π k (q/2) ⊣⊢ otreeG_edge π k q.
  Proof. rewrite otreeG_edge_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma otreeG_edge_valid π k q :
    otreeG_edge π k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /otreeG_edge. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. done.
  Qed.

  (** osuspend rules *)
  Lemma osuspend_alloc_obl D k :
    k ∉ D →
    osuspend D ⊢ |==> osuspend ({[k]} ∪ D) ∗ otreeG_elem k.
  Proof.
    iIntros (Hk) "Hsus".
    rewrite /osuspend -lock. iDestruct "Hsus" as "( % & %Hdom & HS & HW & HE & HM )".
    iMod (otreeG_elem_alloc _ k with "HE") as "[HE He]"; first done.
    iMod (otreeG_suspend_alloc_map _ k with "HS") as "[HS Hs]"; first done.
    iMod (otreeG_wait_alloc_map _ k with "HW") as "[HW Hw]"; first done.
    iModIntro. rewrite -lock. iFrame "He". iExists (<[k:=∅]>OSus). iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom. done. }
    iFrame "HE HS HW". iApply (big_sepM_insert _ OSus k ∅).
    { by rewrite -not_elem_of_dom Hdom. }
    iFrame "HM Hs". replace (⊤ ∖ gset_to_coPset (dom ∅)) with (⊤ : coPset).
    - iFrame. done.
    - set_solver.
  Qed.

  Lemma osuspend_elem_elem D k :
    osuspend D ∗ otreeG_elem k ⊢ ⌜ k ∈ D ⌝.
  Proof.
    iIntros "[Hsus He]".
    rewrite /osuspend -lock. iDestruct "Hsus" as "( % & %Hdom & HS & HW & HE & HM )".
    iPoseProof (otreeG_elem_elem with "[HE He]") as "%Hin"; first iFrame. done.
  Qed.

  Lemma osuspend_suspend D k θ π :
    osuspend D ∗ otreeG_elem k ∗ othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1
    ⊢ |==> osuspend D ∗ ∃ x, otreeG_suspend k x θ π ∗ otreeG_wait k x 1.
  Proof.
    iIntros "(Hsus & He & Ho & Hg)".
    iPoseProof (osuspend_elem_elem with "[$]") as "%Hkin".
    rewrite /osuspend -lock. iDestruct "Hsus" as "( % & %Hdom & HS & HW & HE & HM )".
    assert (is_Some (OSus !! k)).
    { apply elem_of_dom. rewrite Hdom. auto. }
    destruct H1 as (KSus&Hklu).
    iDestruct (big_sepM_delete _ _ k _ Hklu with "HM") as "[Hk HM]".
    iDestruct "Hk" as "(HkS & HkW & HkM)".
    assert (∃ x, KSus !! x = None).
    { exists (fresh (dom KSus)). apply not_elem_of_dom, is_fresh. }
    destruct H1 as (x&Hxlu).
    iMod (otreeG_wait_alloc _ _ x with "HkW") as "(HkW&Hw)".
    { by apply not_elem_of_dom. }
    iMod (otreeG_suspend_alloc _ _ _ θ π Hxlu with "HkS") as "[HkS Hs]".
    iFrame "Hw Hs". iModIntro. iExists (<[k:=<[x:=(θ, π)]>KSus]>OSus). iSplitR.
    { iPureIntro. rewrite dom_insert_lookup_L; eauto. }
    iFrame "HS HW HE". iApply (big_sepM_delete _ _ k).
    { apply lookup_insert_eq. }
    rewrite delete_insert_eq. iFrame "HM".
    iFrame "HkS". rewrite dom_insert_L. iFrame "HkW".
    iApply (big_sepM_insert _ _ x); first auto.
    iFrame "HkM". iLeft. iLeft. iFrame.
  Qed.

  Lemma osuspend_open D k x θ π :
    osuspend D ∗ otreeG_suspend k x θ π
    ⊢ (((othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1) ∨
          (othreadG_owns θ k true (1/2)%Qp ∗ otreeG_wait k x (1/2)%Qp ∗ oblG_done π)) ∨
         otreeG_wait_null k x) ∗
    ((((othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1) ∨
         (othreadG_owns θ k true (1/2)%Qp ∗ otreeG_wait k x (1/2)%Qp ∗ oblG_done π)) ∨
        otreeG_wait_null k x) -∗ osuspend D).
  Proof.

    TODO
    

(* Global invariant for suspending obligations and waiting. *)
Definition osuspend `{SI : indexT} `{WF : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WF ps T Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OSus : gmap obl_id (gmap positive (prod positive obl_id))),
        (⌜ dom OSus = D ⌝) ∗
        (own suspend_name (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO positiveO obl_idO))) (⊤ ∖ gset_to_coPset D))) ∗
        (own wait_name (reservation_map_token (A:=gmapUR positive mono_natUR) (⊤ ∖ gset_to_coPset D))) ∗
        (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () D))) ∗
        ([∗ map] k ↦ KSus ∈ OSus,
           (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> KSus)))) ∗
           (own wait_name (reservation_map_data k (∅ : gmap positive mono_natUR))) ∗
           ([∗ map] x ↦ '(θ, π) ∈ KSus,
              ((othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1) ∨
                 (othreadG_owns θ k true (1/2)%Qp ∗ otreeG_wait k x (1/2)%Qp ∗ oblG_done π)) ∨
                otreeG_wait_null k x)
        )
    )%I.


  (** otree rules *)


(* Global invariant for the obligation forest state. *)
Definition otree `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OTree : cgraph obl_id unitO) (OOwner : gmap obl_id (option positive)),
        (⌜ dom OTree = D ∧ dom OOwner = D ∧ cgraph_wf OTree ⌝) ∗
        (⌜ ∀ π k, descendant OTree π k → OOwner !! π = OOwner !! k ⌝) ∗
        (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D))) ∗
        ([∗ map] k ↦ KCh ∈ OTree,
           (own edge_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) KCh))) ∗
           ((* This obligation is live and has enough transfer and progress credits for chiledren and... *)
             ((∃ α β, oblG_transfer_supply k α (1/2)%Qp ∗ oblG_progress_supply k β (1/2)%Qp ∗
                      ([∗ set] c ∈ (dom KCh),
                         ∃ α' β', ⌜ WFOCM.leR α α' ∧ WFOCM.leR β β' ⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')
              ) ∗
              (* is a root or... *)
              (∃ θ, ⌜ root OTree k ∧ OOwner !! k = Some (Some θ) ⌝ ∗
                    oblG_owner k θ (1/2/2)%Qp ∗
                    othreadG_owns θ k true (1/2)%Qp) ∨
                (* is an internal node, and is suspended *)
                (∃ τ π, ⌜ parent OTree k π ∧ OOwner !! k = Some (Some τ) ⌝ ∗
                        oblG_owner k τ (1/2)%Qp ∗
                        ∃ θ, othreadG_owns θ k false (1/2)%Qp ∗
                             (∃ x, otreeG_suspend k x θ π ∗ otreeG_wait k x (1/2)%Qp))
             ) ∨
               (* Or this obligation is done *)
               (oblG_done k ∗ ⌜ root OTree k ∧ KCh = ∅ ∧ OOwner !! k = Some None ⌝)
        ))
    )%I.


End otree.

(* Allocation of an initial obligation protocol. *)
(* Lemma otree_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!otreeGpreS ps T Σ} `{obl_class A ps T} : *)
(*   ⊢ |==> ∃ _ : otreeGS ps T Σ, otree ∅. *)
(* Proof. *)
(*   iIntros. *)
(*   iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id (prodR _ _))) as (γG) "HG"; *)
(*     first by apply gmap_view_auth_valid. *)
(*   iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id (agreeR $ metaO))) as (γM) "HM"; *)
(*     first by apply gmap_view_auth_valid. *)
(*   iMod (own_alloc (ε : gmap positive mono_natUR)) as (γS) "HS"; *)
(*     first done. *)
(*   iMod (own_alloc (ε : gmap positive bankUR)) as (γT) "HT"; *)
(*     first done. *)
(*   iMod (own_alloc (ε : gmap positive (dfrac_agreeR (leibnizO T)))) as (γO) "HO"; *)
(*     first done. *)
(*   iMod (own_alloc (ε : gmap positive bankUR)) as (γC) "HC"; *)
(*     first done. *)
(*   iModIntro; iExists (OtreeG SI _ WFA _ _ _ _ γG γM γS γT γO γC). *)
(*   rewrite /otree -lock. *)
(*   iSplitL "HG"; first (iExists ∅; by iFrame). *)
(*   iSplitL "HM"; first (iExists ∅; by iFrame). *)
(*   by iFrame. *)
(* Qed. *)
