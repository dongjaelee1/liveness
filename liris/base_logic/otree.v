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
Definition oforest_aux `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) (OForest : forest obl_id) : iProp Σ :=
  ((⌜ dom (forest_fold OForest) = D ∧ forest_wf OForest ⌝) ∗
   (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D))) ∗
   ([∗ map] ρ ↦ ρTree ∈ OForest,
      (* If the root is live... *)
      (∃ τ, oblG_owner ρ τ (1/2/2)%Qp ∗ othreadG_owns τ ρ true (1/2)%Qp ∗
            ([∗ map] v ↦ vCh ∈ ρTree,
               (own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap tt vCh)))) ∗
               (* Obligation is live and has enough transfer (+ 1 to go back) and progress credits for chiledren and... *)
               oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
               (∃ α β, oblG_transfer_supply v α (1/2)%Qp ∗ oblG_progress_supply v β (1/2)%Qp ∗
                       ([∗ set] c ∈ vCh,
                          ∃ α' β', ⌜ WFOCM.ltR α α' ∧ WFOCM.leR β β' ⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')
               ) ∗
               ((⌜ v = ρ ⌝) ∨
                  (* if it's an internal node, it's suspended *)
                  (∃ π, (⌜ child ρTree π v ⌝) ∗
                        oblG_owner v τ (1/2)%Qp ∗
                        ∃ θ, othreadG_owns θ v false (1/2)%Qp ∗
                             (∃ x, otreeG_suspend v x θ π ∗ otreeG_wait v x (1/2)%Qp)))
      )) ∨
        (* Or the root is done *)
        ((own edge_name (reservation_map_data ρ (gmap_view_auth (DfracOwn 1) ∅))) ∗
         oblG_elem ρ ∗ oblG_done ρ ∗ ⌜ ρTree = tree_singleton ρ ⌝)
   )
  )%I.
Definition oforest `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked (∃ (OForest : forest obl_id), oforest_aux D OForest)%I.

(* Definition otree `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ} *)
(*   `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ} *)
(*   (D : gset obl_id) : iProp Σ := *)
(*   locked *)
(*     (∃ (OTree : cgraph obl_id unitO) (ORoot : gmap obl_id positive), *)
(*         (⌜ dom OTree = D ∧ cgraph_wf OTree ⌝) ∗ *)
(*         (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D))) ∗ *)
(*         ([∗ map] k ↦ KCh ∈ OTree, *)
(*            (own edge_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) KCh))) ∗ *)
(*            ((* This obligation is live and has enough transfer (+ one to go back) and progress credits for chiledren and... *) *)
(*              ((∃ α β, oblG_transfer_supply k α (1/2)%Qp ∗ oblG_progress_supply k β (1/2)%Qp ∗ *)
(*                       ([∗ set] c ∈ (dom KCh), *)
(*                          ∃ α' β', ⌜ WFOCM.ltR α α' ∧ WFOCM.leR β β' ⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β') *)
(*               ) ∗ *)
(*               (* is a root or... *) *)
(*               (∃ τ, ⌜ root OTree k ∧ ORoot !! k = Some τ ⌝ ∗ *)
(*                     oblG_owner k τ (1/2/2)%Qp ∗ *)
(*                     othreadG_owns τ k true (1/2)%Qp) ∨ *)
(*                 (* is an internal node, and is suspended *) *)
(*                 (∃ τ π, (⌜ parent OTree k π ∧ (∀ π', parent OTree k π' → π' = π) ∧ *)
(*                          ∃ ρ, root OTree ρ ∧ descendant OTree ρ k ∧ ORoot !! ρ = Some τ ⌝) ∗ *)
(*                         oblG_owner k τ (1/2)%Qp ∗ *)
(*                         ∃ θ, othreadG_owns θ k false (1/2)%Qp ∗ *)
(*                              (∃ x, otreeG_suspend k x θ π ∗ otreeG_wait k x (1/2)%Qp)) *)
(*              ) ∨ *)
(*                (* Or this obligation is done *) *)
(*                (oblG_done k ∗ ⌜ root OTree k ∧ KCh = ∅ ⌝) *)
(*         )) *)
(*     )%I. *)

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

  Lemma osuspend_done_parent D k x θ π TP :
    osuspend D ∗ otreeG_elem k ∗ otreeG_suspend k x θ π ∗ otreeG_wait k x (1/2)%Qp ∗
    othread TP ∗ othreadG_elem θ ∗ othreadG_owns θ k false (1/2)%Qp ∗
    oblG_owner k θ (1/2/2)%Qp ∗ oblG_done π
    ⊢ |==> osuspend D ∗ othreadG_owns θ k true (1/2)%Qp ∗ otreeG_edge π k 1 ∗ othread TP.
  Proof.
    iIntros "(Rsus & Re & Rs & Rw & Tthr & Te & To & Bo & Bs)".
    iPoseProof (osuspend_elem_elem with "[Rsus Re]") as "%Hkin"; first iFrame.
    rewrite /osuspend -lock. iDestruct "Rsus" as "( % & %Hdom & RS & RW & RE & RM )".
    assert (is_Some (OSus !! k)).
    { apply elem_of_dom. rewrite Hdom. auto. }
    destruct H1 as (KSus&Hklu).
    iDestruct (big_sepM_delete _ _ k _ Hklu with "RM") as "[Rk RM]".
    iDestruct "Rk" as "(RkS & RkW & RkM)".
    iPoseProof (otreeG_suspend_lookup with "[RkS Rs]") as "%Hxlu"; first iFrame.
    iDestruct (big_sepM_delete _ _ x _ Hxlu with "RkM") as "[Rkx RkM]".
    iDestruct "Rkx" as "[[Rkx | Rkx] | Rkx]".
    - iDestruct "Rkx" as "(Rkx1 & Rkx2)".
      iMod (othread_obl_acquire_2 with "[Tthr Te To Rkx1 Bo]") as "(Tthr & To1 & To2)"; first iFrame.
      iFrame "Rkx2 Tthr To2".
      iPoseProof (big_sepM_delete _ _ x _ Hxlu with "[RkM To1 Rw Bs]") as "RkM".
      { iFrame "RkM". iLeft. iRight. iFrame. }
      iPoseProof (big_sepM_delete _ _ k _ Hklu with "[RM RkM RkS RkW]") as "RM".
      { iFrame "RM". iFrame. }
      iModIntro. iExists OSus. iFrame. done.
    - iDestruct "Rkx" as "(Rko & Rkw & Rks)".
      iPoseProof (othreadG_owns_agree with "[To Rko]") as "%"; first iFrame. done.
    - iPoseProof (otreeG_wait_null_false with "[Rw Rkx]") as "%"; first iFrame. done.
  Qed.

  Lemma osuspend_wait_cases D k x θ π :
    osuspend D ∗ otreeG_elem k ∗ otreeG_suspend k x θ π ∗ otreeG_wait k x (1/2)%Qp
    ⊢ (otreeG_wait k x (1/2)%Qp ∗
       othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1 ∗
       ((othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1) -∗ osuspend D))
      ∨
        |==> (othreadG_owns θ k true (1/2)%Qp ∗ oblG_done π ∗ osuspend D).
  Proof.
    iIntros "(Rsus & Re & Rs & Rw)".
    iPoseProof (osuspend_elem_elem with "[Rsus Re]") as "%Hkin"; first iFrame.
    rewrite /osuspend -lock. iDestruct "Rsus" as "( % & %Hdom & RS & RW & RE & RM )".
    assert (is_Some (OSus !! k)).
    { apply elem_of_dom. rewrite Hdom. auto. }
    destruct H1 as (KSus&Hklu).
    iDestruct (big_sepM_delete _ _ k _ Hklu with "RM") as "[Rk RM]".
    iDestruct "Rk" as "(RkS & RkW & RkM)".
    iPoseProof (otreeG_suspend_lookup with "[RkS Rs]") as "%Hxlu"; first iFrame.
    iDestruct (big_sepM_delete _ _ x _ Hxlu with "RkM") as "[Rkx RkM]".
    iDestruct "Rkx" as "[[Rkx | Rkx] | Rkx]".
    - iDestruct "Rkx" as "(Rkx1 & Rkx2)". iLeft. iFrame "Rw Rkx1 Rkx2".
      iIntros "[Rkx1 Rkx2]".
      iPoseProof (big_sepM_delete _ _ x _ Hxlu with "[RkM Rkx1 Rkx2]") as "RkM".
      { iFrame "RkM". iLeft. iLeft. iFrame. }
      iPoseProof (big_sepM_delete _ _ k _ Hklu with "[RM RkM RkS RkW]") as "RM".
      { iFrame "RM". iFrame. }
      iExists OSus. iFrame. done.
    - iDestruct "Rkx" as "(Rkx1 & Rkx2 & Rkx3)". iRight. iFrame "Rkx1 Rkx3".
      iMod (otreeG_wait_to_null_2 with "[Rw Rkx2]") as "Rwn".
      2:{ iFrame. }
      { by rewrite Qp.div_2. }
      iPoseProof (big_sepM_delete _ _ x _ Hxlu with "[RkM Rwn]") as "RkM".
      { iFrame "RkM". iRight. iFrame. }
      iPoseProof (big_sepM_delete _ _ k _ Hklu with "[RM RkM RkS RkW]") as "RM".
      { iFrame "RM". iFrame. }
      iModIntro. iExists OSus. iFrame. done.
    - iPoseProof (otreeG_wait_null_false with "[Rw Rkx]") as "%"; first iFrame. done.
  Qed.

  (** oforest rules *)
  Lemma oforest_alloc_obl D ρ θ α β :
    ρ ∉ D →
    oforest D ∗
    othreadG_owns θ ρ true (1/2)%Qp ∗
    oblG_elem ρ ∗ oblG_live ρ (1/2/2)%Qp ∗ oblG_owner ρ θ (1/2/2)%Qp ∗
    oblG_transfer_supply ρ α (1/2)%Qp ∗ oblG_progress_supply ρ β (1/2)%Qp
    ⊢ |==> oforest ({[ρ]} ∪ D).
  Proof.
    iIntros (Hρ) "(Rfor & To & Be & Bl & Bo & Bts & Bps)".
    rewrite /oforest -lock /oforest_aux. iDestruct "Rfor" as "(% & %Hf & Retk & RM)". destruct Hf as [Hf1 Hf2].
    assert (Hρlu : forest_fold OForest !! ρ = None).
    { apply not_elem_of_dom. rewrite Hf1. auto. }
    assert (Hρlu2 : OForest !! ρ = None).
    { apply forest_fold_not_in_forest_not_in; auto. }
    iMod (otreeG_edge_alloc_map D ρ Hρ with "Retk") as "[Retk Reρ]".
    iPoseProof (big_sepM_insert _ _ _ (tree_singleton ρ) Hρlu2 with "[RM To Be Bl Bo Bts Bps Reρ]") as "RM".
    { iFrame "RM". iLeft. iFrame "To Bo". iApply big_sepM_singleton. iFrame. iSplit; first done. by iLeft. }
    iModIntro. rewrite -lock. iExists (forest_insert OForest ρ (tree_singleton ρ)).
    iFrame. iPureIntro. split.
    { subst D. apply forest_fold_insert_singleton_dom; auto. }
    { apply forest_insert_singleton_wf; auto. }
  Qed.

  Lemma oforest_aux_wf D OForest :
    oforest_aux D OForest ⊢ ⌜ dom (forest_fold OForest) = D ∧ forest_wf OForest ⌝.
  Proof. iIntros "F". rewrite /oforest_aux. iDestruct "F" as "(%Hf & Retk & RM)". done. Qed.

  Definition obl_cond_in_tree (t : tree obl_id) : obl_cond :=
    λ k o, node t k.

  Lemma oforest_progress_one_tree Ω OForest ρ ρTree (a : A) :
    /0 /< a →
    (∃ d, Ω !! ρ = Some (obl_live d)) →
    OForest !! ρ = Some ρTree →
    osat Ω ∗ oforest_aux (dom Ω) OForest ∗
    (* from user *)
    oblG_progress ρ a
    ⊢ |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | (obl_cond_in_tree ρTree) ⌝) ∗
                 osat Ω' ∗ oforest_aux (dom Ω') OForest.
  Proof.
    iIntros (Ha ? Hρ) "(S & F & Bp)". destruct H1 as [d Hρlu].
    iPoseProof (oforest_aux_wf with "F") as "%". destruct H1 as [Hfdom Hfwf].
    rewrite /oforest_aux. iDestruct "F" as "(_ & Retk & RM)".
    iPoseProof (big_sepM_delete _ _ _ _ Hρ with "RM") as "[RMρ RM]".
    iAssert (oblG_elem ρ) with "[-]" as "#Be".
    { iDestruct "RMρ" as "[(%&_&_&M) | (_&H&_)]".
      - assert (is_Some (ρTree !! ρ)).
        { apply elem_of_dom. destruct Hfwf. apply tree_wf_root_elem; auto. }
        destruct H1. iPoseProof (big_sepM_delete _ _ _ _ H1 with "M") as "[M1 M2]".
        iDestruct "M1" as "(_&H&_)". iFrame "H".
      - iFrame "H". }
    (* Frame other trees in the forest and also frame some others in the tree *)
    iAssert (
  |==>
    ∃ Ω' : obl_states, ⌜Ω ↪ₚ Ω' | obl_cond_in_tree ρTree⌝ ∗ osat Ω' ∗ ⌜forest_wf OForest⌝ ∗
      ((∃ τ : positive, oblG_owner ρ τ (1 / 2 / 2) ∗ othreadG_owns τ ρ true (1 / 2) ∗
                                       ([∗ map] v↦vCh ∈ ρTree, own edge_name
                                                                  (reservation_map_data v
                                                                     (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗ oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
                                        (∃ α β : A, oblG_transfer_supply v α (1 / 2) ∗ oblG_progress_supply v β (1 / 2) ∗
                                           ([∗ set] c ∈ vCh, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗
                                                               oblG_progress c β')) ∗
                                        (⌜v = ρ⌝
                                         ∨ ∃ π : positive, ⌜child ρTree π v⌝ ∗ oblG_owner v τ (1 / 2) ∗
                                             ∃ θ : positive, othreadG_owns θ v false (1 / 2) ∗
                                               ∃ x : positive, otreeG_suspend v x θ π ∗ otreeG_wait v x (1 / 2))))
                                    ∨ own edge_name (reservation_map_data ρ (gmap_view_auth (DfracOwn 1) ∅)) ∗ oblG_elem ρ ∗
       oblG_done ρ ∗ ⌜ρTree = tree_singleton ρ⌝))%I with "[- RM Retk]" as "H"; cycle 1.
    { iMod "H". iModIntro. iDestruct "H" as "(%&%&H0&%&H1)".
      iExists Ω'. iSplitR; first done. iFrame "H0".
      assert (dom Ω = dom Ω') by (by apply obl_states_cond_rel_dom in H1).
      iSplitR.
      { rewrite -H3. iSplit; auto. }
      iSplitL "Retk".
      { destruct H2. rewrite -H3. done. }
      iApply (big_sepM_delete _ _ _ _ Hρ with "[-]"). iFrame. }
    (* - Resolve done case, fix thread τ *)
    iDestruct "RMρ" as "[RMρ | RMρ]"; cycle 1.
    { iDestruct "RMρ" as "(RMρd & _ & #Bd & %Hρtree)". iPoseProof (osat_obl_is_done_weak with "[$]") as "(%&%)".
      exfalso. rewrite Hρlu in H1. inv H1. }
    iDestruct "RMρ" as "(%& RMρBo& RMρTo& RMρM)".
    iAssert (
  |==>
    ∃ Ω' : obl_states, ⌜Ω ↪ₚ Ω' | obl_cond_in_tree ρTree⌝ ∗ osat Ω' ∗ ⌜forest_wf OForest⌝ ∗
      (oblG_owner ρ τ (1 / 2 / 2) ∗ othreadG_owns τ ρ true (1 / 2) ∗
          ([∗ map] v↦vCh ∈ ρTree, own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗ oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
           (∃ α β : A, oblG_transfer_supply v α (1 / 2) ∗ oblG_progress_supply v β (1 / 2) ∗
              ([∗ set] c ∈ vCh, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
           (⌜v = ρ⌝
            ∨ ∃ π : positive, ⌜child ρTree π v⌝ ∗ oblG_owner v τ (1 / 2) ∗
                ∃ θ : positive, othreadG_owns θ v false (1 / 2) ∗ ∃ x : positive, otreeG_suspend v x θ π ∗ otreeG_wait v x (1 / 2))))
      )%I with "[-]" as "H"; cycle 1.
    { iMod "H" as "(%&%&H0&%&H1)". iModIntro. iExists Ω'. iFrame. iSplitR; auto. }
    iAssert (
        ([∗ map] v↦vCh ∈ ρTree,
           oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
           (∃ α β : A, oblG_transfer_supply v α (1 / 2) ∗ oblG_progress_supply v β (1 / 2) ∗
              ([∗ set] c ∈ vCh, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗
                                             oblG_progress c β')))
        ∗ [∗ map] v↦vCh ∈ ρTree,
           own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗
          (⌜v = ρ⌝
            ∨ ∃ π : positive, ⌜child ρTree π v⌝ ∗ oblG_owner v τ (1 / 2) ∗
                ∃ θ : positive, othreadG_owns θ v false (1 / 2) ∗
                  ∃ x : positive, otreeG_suspend v x θ π ∗ otreeG_wait v x (1 / 2))
      )%I with "[RMρM]" as "[RMρM RMρM0]".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "RMρM").
      iModIntro. iIntros (???) "(?&?&?&?&?)". iFrame. }
    iAssert (
  |==>
    ∃ Ω' : obl_states, ⌜Ω ↪ₚ Ω' | obl_cond_in_tree ρTree⌝ ∗ osat Ω' ∗ ⌜forest_wf OForest⌝ ∗
      ([∗ map] v↦vCh ∈ ρTree,
       oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
       (∃ α β : A, oblG_transfer_supply v α (1 / 2) ∗ oblG_progress_supply v β (1 / 2) ∗
          ([∗ set] c ∈ vCh, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗
                                         oblG_progress c β')))
      )%I with "[- RMρM0 RMρBo RMρTo]" as "H"; cycle 1.
    { iMod "H" as "(%&%&S&%&M)". iModIntro. iFrame. iSplitR; first auto. iSplitR; first auto.
      iPoseProof (big_sepM_sep with "[RMρM0 M]") as "H"; first iFrame. iApply (big_sepM_impl with "H").
      iModIntro. iIntros (???) "(?&?&?)". iFrame. }
    (* First induction: on ρTree. Need to weaken some assumptions *)
    assert (Htwf : tree_wf ρ ρTree).
    { destruct Hfwf. eapply H2; auto. }
    clear Hfdom τ. iStopProof.
    generalize dependent a. generalize dependent d. generalize dependent Ω. generalize dependent OForest.
    pattern ρ, ρTree. revert ρ ρTree Htwf. apply tree_wf_internal_ind.
    intros ρ ρTree HρTreewf IH1 OForest Hρ Hfwf Ω d Hρlu a Ha.
    iIntros "(#Be & S & Bp & RMρ)".
    iAssert (|==> ∃ Ωρ, ⌜ Ω ↪ₚ Ωρ | (λ k o, node ρTree k ∧ root ρTree k) ⌝ ∗ |==> ∃ Ω', ⌜ Ωρ ↪ₚ Ω' | (λ k o, internal ρTree k) ⌝ ∗ osat Ω' ∗
      ⌜forest_wf OForest⌝ ∗
      (([∗ map] v↦vCh ∈ ρTree, oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
           (∃ α β : A, oblG_transfer_supply v α (1 / 2) ∗ oblG_progress_supply v β (1 / 2) ∗
              ([∗ set] c ∈ vCh, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'))))
            )%I with "[-]" as "H"; cycle 1.
    { iMod "H" as "(%&%& H)". iMod "H" as "(%&%&S&%&F)".
      iModIntro. iExists Ω'. iFrame. iPureIntro. split_and !; auto.
      eapply obl_states_cond_rel_split_cond. 6: eapply H1. 6: eapply H2. all: simpl.
      - intros. apply _.
      - intros. apply _.
      - apply _.
      - intros. destruct Hfwf. unfold obl_cond_in_tree. split; intros.
        + pose proof H6. eapply tree_wf_node_root_or_internal in H6; eauto. destruct H6; auto.
        + destruct H6; [destruct H6; auto | eapply tree_wf_internal_node; eauto].
      - intros ?????. auto. }
    (* Progress of the root ρ *)
    assert (Hρtwf : tree_wf ρ ρTree) by (destruct Hfwf; eauto).
    inversion Hρtwf. subst ρ0 t. assert (Hρlutree : ρTree !! ρ = Some (dom Cf)).
    { subst. by rewrite /forest_merge lookup_insert_eq. }
    iPoseProof (big_sepM_delete _ _ _ _ Hρlutree with "RMρ") as "[RMρMρ RMρM]".
    iDestruct "RMρMρ" as "(_ & Hl & (%&%& Hb0 & Hb1 & Hb2))".
    destruct d as [α0 τ0 β0]. iMod (osat_obl_progress_one _ _ _ _ _ _ _ Hρlu with "[S Bp Hb1]") as "(% & S & %Hprog & Hb1)".
    1: eauto. 1: iFrame.
    destruct Hprog as [Hprog Hβ].
    iModIntro. iExists (<[ρ:=olive α0 τ0 β']> Ω). remember (<[ρ:=olive α0 τ0 β']> Ω) as Ω0.
    iSplitR.
    { iPureIntro. subst Ω0. intros ?. destruct (decide (i = ρ)).
      - subst i. rewrite Hρlu lookup_insert_eq. econstructor. simpl. split; auto.
        intros. exfalso. apply H5. split; [apply tree_wf_root_node; auto | apply tree_wf_root_root; auto].
      - rewrite lookup_insert_ne; auto. destruct (Ω !! i) eqn:Hilu; econstructor. split; [intros | auto].
        destruct H5. pose proof (tree_wf_root_node_root _ _ _ Hρtwf H6 H5). subst i. done. }
    (* Second induction: on Cf. Need to weaken some premises *)
    iAssert (
  |==>
    ∃ Ω' : obl_states, ⌜Ω0 ↪ₚ Ω' | λ (k : obl_id) (_ : obl_state), node (forest_fold Cf) k⌝ ∗ osat Ω' ∗
      ⌜forest_wf OForest⌝ ∗
      ([∗ map] v↦vCh ∈ ρTree, oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
           (∃ α1 β1 : A, oblG_transfer_supply v α1 (1 / 2) ∗ oblG_progress_supply v β1 (1 / 2) ∗
                         ([∗ set] c ∈ vCh, ∃ α' β'0 : A, ⌜α1 /< α' ∧ β1 /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0)))
      )%I with "[-]" as "H"; cycle 1.
    { iMod "H" as "(%&%&H)". iModIntro. iFrame. iPureIntro. eapply obl_states_cond_rel_iff; first eapply H5.
      simpl; intros. split; intros; subst.
      - eapply forest_fold_node_forest_merge_internal; eauto.
      - eapply forest_merge_internal_forest_fold_node; eauto. }
    iAssert (
  |==>
    ∃ Ω' : obl_states, ⌜Ω0 ↪ₚ Ω' | λ (k : obl_id) (_ : obl_state), node (forest_fold Cf) k⌝ ∗ osat Ω' ∗
      ⌜forest_wf OForest⌝ ∗
          ([∗ set] c ∈ dom Cf, ∃ α' β'0 : A, ⌜α /< α' ∧ β' /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0) ∗
          ([∗ map] v↦vCh ∈ (forest_fold Cf), oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
           (∃ α1 β1 : A, oblG_transfer_supply v α1 (1 / 2) ∗ oblG_progress_supply v β1 (1 / 2) ∗
              ([∗ set] c ∈ vCh, ∃ α' β'0 : A, ⌜α1 /< α' ∧ β1 /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0)))
      )%I with "[- Hl Hb0 Hb1]" as "H"; cycle 1.
    { iMod "H" as "(%&%& S &%& H)".
      iDestruct "H" as "(HCS&HM)". iModIntro. iExists Ω'. iSplitR; first done. iFrame "S". iSplitR; first done.
      iApply (big_sepM_delete _ _ _ _ Hρlutree with "[-]"). iFrame "Hl Hb0 Hb1". iSplitL "HCS".
      { iSplitR; first auto.
        iApply (big_sepS_impl with "[$]"). iModIntro. iIntros (? ?) "(%&%&%&H1&H2)".
        iExists α', β'0. iFrame. destruct H8. iSplit; done. }
      subst ρTree. rewrite /forest_merge delete_insert_id; auto. }
    iAssert (
  [∗ map] k↦y ∈ (forest_fold Cf), oblG_elem k ∗ oblG_live k (1/2/2)%Qp ∗
           (∃ α1 β1 : A, oblG_transfer_supply k α1 (1 / 2) ∗ oblG_progress_supply k β1 (1 / 2) ∗
              ([∗ set] c ∈ y, ∃ α' β'0 : A, ⌜α1 /< α' ∧ β1 /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0))
      )%I with "[RMρM]" as "RMρ".
    { subst. rewrite /forest_merge delete_insert_id; auto. }
    iAssert (
        |==> ([∗ set] c ∈ dom Cf, ∃ u, ⌜ /0 /< u ⌝ ∗ oblG_progress c u) ∗
             ([∗ set] c ∈ dom Cf, ∃ α' β'0 : A, ⌜α /< α' ∧ β' /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0)
      )%I with "[Hb2]" as ">[Hps HCS]".
    { iApply big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "Hb2"). iModIntro.
      iIntros (i Hi) "(%x&%y&%Hxy&Ht&Hp)". destruct Hxy as [Hx Hy].
      apply WFOCM.lt_exists_left in Hβ. destruct Hβ as (?&?&?).
      assert (Hle : (β' /+ x0) /≤ y) by (by etrans).
      iMod (oblG_progress_mon_split _ _ _ _ Hle with "Hp") as "[Hp Hpc]".
      iModIntro. iSplitL "Hpc"; iFrame; auto. }
    assert (HCfsub : map_Forall (λ _ c, c ⊆ ρTree) Cf).
    { subst. by apply forest_merge_subseteq_Forall. }
    assert (HCfint : map_Forall (λ v _, internal ρTree v) Cf).
    { subst. by apply forest_merge_internal_Forall. }
    clear dependent Ω. clear dependent β0. clear H1 Hρlutree.
    iStopProof. generalize dependent Ω0. generalize dependent Cf.
    induction Cf using map_ind.
    { iIntros (Hρlu HCfdisj HCftwf HCfsub HCfint Ω) "(#Be & S & FρMM & Hps & HCS)".
      iModIntro. iExists Ω. iFrame. iSplitR; last auto.
      iPureIntro. rewrite forest_fold_empty. intros ?. destruct (Ω !! i) eqn:Hlu; econstructor.
      split; intros; auto. rewrite /node lookup_empty in H1. done. }
    iIntros (Hρlu HCfdisj HCftwf HCfsub HCfint Ω) "(#Be & S & FρMM & Hps & HCS)".
    assert (Hm0 : forest_fold m !! ρ = None).
    { apply not_elem_of_dom.
      apply not_elem_of_dom in Hρlu. rewrite forest_fold_insert_dom in Hρlu; auto. set_solver + Hρlu. }
    assert (Hm1 : forest_trees_disjoint m).
    { apply forest_trees_disjoint_insert in HCfdisj; auto. by destruct HCfdisj. }
    assert (Hm2 : map_Forall (λ c ct, tree_wf c ct) m).
    { apply map_Forall_insert in HCftwf; auto. by destruct HCftwf. }
    assert (Hm3 : map_Forall (λ _ c, c ⊆ ρTree) m).
    { apply map_Forall_insert in HCfsub; auto. by destruct HCfsub. }
    assert (Hm4 : map_Forall (λ v _, internal ρTree v) m).
    { apply map_Forall_insert in HCfint; auto. by destruct HCfint. }
    rewrite !(dom_insert_L m i x). rewrite !(forest_fold_insert_L m i x); auto.
    iPoseProof (big_sepS_union with "HCS") as "[HiCS HCS]".
    { apply not_elem_of_dom in H1. set_solver + H1. }
    iPoseProof (big_sepS_union with "Hps") as "[Hips Hps]".
    { apply not_elem_of_dom in H1. set_solver + H1. }
    iPoseProof (big_sepM_union with "FρMM") as "[FρMMx FρMM]".
    { apply forest_trees_disjoint_insert in HCfdisj; auto. destruct HCfdisj. apply tree_disjoint_forest_fold_disjoint; auto. }
    specialize (IHCf Hm0 Hm1 Hm2 Hm3 Hm4 Ω). clear Hm0 Hm1 Hm2 Hm3 Hm4.
    iMod (IHCf with "[S HCS Hps FρMM]") as "(% & %Hprog' & S & %Hwf' & HM)".
    { iFrame. auto. }
    clear IHCf. rewrite !(big_sepS_singleton _ i).
    assert (Hi0 : internal ρTree i).
    { apply map_Forall_insert in HCfint; auto. by destruct HCfint. }
    assert (Hi1 : x ⊆ ρTree).
    { apply map_Forall_insert in HCfsub; auto. by destruct HCfsub. }
    assert (Hi2 : tree_wf i x).
    { apply map_Forall_insert in HCftwf; auto. by destruct HCftwf. }
    assert (Hi3 : (<[i:=x]>m) !! i = Some x).
    { apply lookup_insert_eq. }
    assert (Hi4 : forest_wf (<[i:=x]>m)).
    { split; auto. }
    iAssert (∃ d, ⌜ Ω' !! i = Some (obl_live d) ⌝)%I with "[-]" as "%Hi5".
    { iClear "HiCS Hips HM".
      assert (is_Some (x !! i)).
      { apply elem_of_dom. apply map_Forall_insert in HCftwf; auto. destruct HCftwf.
        apply tree_wf_root_elem; auto. }
      destruct H2. iPoseProof (big_sepM_delete _ _ _ _ H2 with "FρMMx") as "[H1 H2]".
      iClear "H2". iDestruct "H1" as "(Bei & Bli & _)".
      iApply (osat_obl_is_live with "[$]"). }
    destruct Hi5 as (di&Hi5). iDestruct "Hips" as "(%&%Hu&Hip)".
    specialize (IH1 _ _ Hi0 Hi1 Hi2 _ Hi3 Hi4 _ _ Hi5 _ Hu).
    assert (is_Some (x !! i)).
    { by apply elem_of_dom, tree_wf_root_elem. }
    destruct H2. iAssert (oblG_elem i)%I with "[-]" as "#Bei".
    { iPoseProof (big_sepM_delete _ _ _ _ H2 with "FρMMx") as "[[H1 _] H2]". iFrame. }
    iMod (IH1 with "[S Hip FρMMx]") as "(%Ω2 & %Hprog2 & S & _ & HMx)".
    { iFrame. auto. }
    clear IH1. iModIntro. iExists Ω2. iFrame. iSplitR.
    { iPureIntro. eapply obl_states_cond_rel_split_cond. 6: eapply Hprog'. 6: eapply Hprog2.
      all: try apply _.
      - simpl. intros. rewrite /obl_cond_in_tree /node -!elem_of_dom dom_union_L.
        rewrite elem_of_union. split; intros HAns; set_solver + HAns.
      - unfold obl_cond_in_tree. intros ?????. auto. }
    iSplitR; first auto. iDestruct "HM" as "[HM1 HM2]". iSplitL "HiCS HM1".
    { iApply big_sepS_union.
      { apply not_elem_of_dom in H1. set_solver +H1. }
      iFrame. by iApply big_sepS_singleton. }
    iApply big_sepM_union.
    { destruct Hi4. apply forest_trees_disjoint_insert in H3; auto. destruct H3.
      apply tree_disjoint_forest_fold_disjoint; auto. }
    iFrame.
  Qed.

  (* Progress of a thread *)

  (* Move a tree *)
  Lemma oforest_progress_one_tree Ω OForest ρ ρTree (a : A) :
    /0 /< a →
    (∃ d, Ω !! ρ = Some (obl_live d)) →
    OForest !! ρ = Some ρTree →
    osat Ω ∗ oforest_aux (dom Ω) OForest ∗
    (* from user *)
    oblG_progress ρ a
    ⊢ |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | (obl_cond_in_tree ρTree) ⌝) ∗
                 osat Ω' ∗ oforest_aux (dom Ω') OForest.
  Proof.

      (* TODO *)

        

    (*   oforest_progress *)
    (* oforest_transfer > oforest_move_tree *)
    (*   oforest_resolve > oforest_clear_tree *)

(* Global invariant for the obligation forest state. *)
Definition oforest_aux `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) (OForest : forest obl_id) : iProp Σ :=
  ((⌜ dom (forest_fold OForest) = D ∧ forest_wf OForest ⌝) ∗
   (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D))) ∗
   ([∗ map] ρ ↦ ρTree ∈ OForest,
      (* If the root is live... *)
      (∃ τ, oblG_owner ρ τ (1/2/2)%Qp ∗ othreadG_owns τ ρ true (1/2)%Qp ∗
            ([∗ map] v ↦ vCh ∈ ρTree,
               (own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap tt vCh)))) ∗
               (* Obligation is live and has enough transfer (+ 1 to go back) and progress credits for chiledren and... *)
               (∃ α β, oblG_transfer_supply v α (1/2)%Qp ∗ oblG_progress_supply v β (1/2)%Qp ∗
                       ([∗ set] c ∈ vCh,
                          ∃ α' β', ⌜ WFOCM.ltR α α' ∧ WFOCM.leR β β' ⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')
               ) ∗
               ((⌜ v = ρ ⌝) ∨
                  (* if it's an internal node, it's suspended *)
                  (∃ π, (⌜ child ρTree π v ⌝) ∗
                        oblG_owner v τ (1/2)%Qp ∗
                        ∃ θ, othreadG_owns θ v false (1/2)%Qp ∗
                             (∃ x, otreeG_suspend v x θ π ∗ otreeG_wait v x (1/2)%Qp)))
      )) ∨
        (* Or the root is done *)
        ((own edge_name (reservation_map_data ρ (gmap_view_auth (DfracOwn 1) ∅))) ∗
         oblG_done ρ ∗ ⌜ ρTree = tree_singleton ρ ⌝)
   )
  )%I.
Definition oforest `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS Σ}
  (D : gset obl_id) : iProp Σ :=
  locked (∃ (OForest : forest obl_id), oforest_aux D OForest)%I.



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
