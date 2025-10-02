From iris.algebra Require Import agree gmap gmap_view reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.algebra Require Export tree.
From liris.base_logic Require Export othread.

(** The ghost state for liveness obligation forest *)
Module otreeGS.

  Class otreeGpreS `{SI : indexT} (A : Type) (Σ : gFunctors) : Set :=
    OtreeGpreS {
        otreeGpreS_edge : inG Σ (reservation_mapUR (gmap_viewR obl_id unitUR));
        (* Data for suspending an obligation: returning thread_id, blocking parent id, amount of progress credits *)
        otreeGpreS_suspend : inG Σ (reservation_mapUR (gmap_viewR positive
                                                         (agreeR (prodO (prodO positiveO obl_idO) (leibnizO A)))));
        otreeGpreS_wait : inG Σ (reservation_mapUR (reservation_mapUR mono_natUR));
        otreeGpreS_elem : inG Σ (gmap_viewR obl_id unitUR);
      }.

  Class otreeGS `{SI : indexT} (A : Type) (Σ : gFunctors) : Set :=
    OtreeG {
        otree_inG : otreeGpreS A Σ;
        edge_name : gname;
        suspend_name : gname;
        wait_name : gname;
        elem_name : gname;
      }.

  Definition otreeΣ `{SI : indexT} (A : Type) : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR obl_id unitUR));
      GFunctor (reservation_mapUR (gmap_viewR positive
                                     (agreeR (prodO (prodO positiveO obl_idO) (leibnizO A)))));
      GFunctor (reservation_mapUR (reservation_mapUR mono_natUR));
      GFunctor (gmap_viewR positive unitUR)
      ].

  Global Instance subG_otreeΣ `{SI : indexT} (A: Type) {Σ} : subG (otreeΣ A) Σ → (otreeGpreS A Σ).
  Proof. solve_inG. Qed.

End otreeGS.
Import otreeGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances otree_inG
  otreeGpreS_edge otreeGpreS_suspend otreeGpreS_wait otreeGpreS_elem.

(* Edge *)
Definition otreeG_edge `{SI : indexT} `{!otreeGS A Σ} (π k : obl_id) (q : Qp) : iProp Σ :=
  own edge_name (reservation_map_data π (gmap_view_frag k (DfracOwn q) ())).
Global Typeclasses Opaque otreeG_edge.
Global Instance: Params (@otreeG_edge) 6 := {}.

(* Suspend knowledge *)
Definition otreeG_suspend `{SI : indexT} `{!otreeGS A Σ} (k : obl_id) (x θ : positive) (π : obl_id) (ψ : A) : iProp Σ :=
  own suspend_name (reservation_map_data k (gmap_view_frag x DfracDiscarded (to_agree ((θ, π, ψ) : prodO _ (leibnizO _))))).
Global Typeclasses Opaque otreeG_suspend.
Global Instance: Params (@otreeG_suspend) 8 := {}.

(* Wait token *)
Definition otreeG_wait `{SI : indexT} `{!otreeGS A Σ} (k : obl_id) (x : positive) (q : Qp) : iProp Σ :=
  own wait_name (reservation_map_data k (reservation_map_data x (●MN{#q} 0))).
Global Typeclasses Opaque otreeG_wait.
Global Instance: Params (@otreeG_wait) 6 := {}.

Definition otreeG_wait_null `{SI : indexT} `{!otreeGS A Σ} (k : obl_id) (x : positive) : iProp Σ :=
  own wait_name (reservation_map_data k (reservation_map_data x (●MN 1))).
Global Typeclasses Opaque otreeG_wait_null.
Global Instance: Params (@otreeG_wait_null) 6 := {}.

(* Elem: keeps the fact that a key is inside a map *)
Definition otreeG_elem `{SI : indexT} `{!otreeGS A Σ} (k : obl_id) : iProp Σ :=
  own elem_name (gmap_view_frag k DfracDiscarded ()).
Global Typeclasses Opaque otreeG_elem.
Global Instance: Params (@otreeG_elem) 5 := {}.

(* Global invariant for suspending obligations and waiting. *)
Definition osuspend `{SI : indexT} {A : Type} `{WF : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WF ps T Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS A Σ}
  (D : gset obl_id) : iProp Σ :=
  locked
    (∃ (OSus : gmap obl_id (gmap positive (prod (prod positive obl_id) A))),
        (⌜ dom OSus = D ⌝) ∗
        (own suspend_name (reservation_map_token
                             (A:=gmap_viewR positive (agreeR (prodO (prodO positiveO obl_idO) (leibnizO A))))
                             (⊤ ∖ gset_to_coPset D))) ∗
        (own wait_name (reservation_map_token (A:=reservation_mapUR mono_natUR) (⊤ ∖ gset_to_coPset D))) ∗
        (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () D))) ∗
        ([∗ map] k ↦ KSus ∈ OSus,
           (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1)
                                                        (to_agree <$> (KSus : gmap _ (prod _ (leibnizO A))))))) ∗
           (own wait_name (reservation_map_data k (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset (dom KSus))))) ∗
           ([∗ map] x ↦ '(θ, π, ψ) ∈ KSus,
              ((othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1) ∨
                 (othreadG_owns θ k true (1/2)%Qp ∗ otreeG_wait k x (1/2)%Qp ∗ oblG_done π ∗ oblG_progress k ψ)) ∨
                otreeG_wait_null k x)
        )
    )%I.

(* Global invariant for the obligation forest state. *)
Definition oforest_aux `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS A Σ}
  (D : gset obl_id) (OForest : forest obl_id) : iProp Σ :=
  ((⌜ dom (forest_fold OForest) = D ∧ forest_wf OForest ⌝) ∗
   (own edge_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D))) ∗
   ([∗ map] ρ ↦ ρTree ∈ OForest,
      (* If the root is live... *)
      (∃ τ, oblG_owner ρ τ (1/2/2)%Qp ∗ othreadG_owns τ ρ true (1/2)%Qp ∗
            ([∗ map] v ↦ vCh ∈ ρTree,
               (own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap tt vCh)))) ∗
               (* Obligation is live and has enough transfer (+ 1 to go back) and progress credits for chiledren and... *)
               oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗ otreeG_elem v ∗
               (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1/2)%Qp ∗
                       ([∗ set] c ∈ vCh,
                          ∃ α' β', ⌜ WFOCM.ltR α α' ∧ WFOCM.leR β β' ⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')
               ) ∗
               ((⌜ v = ρ ⌝) ∨
                  (* if it's an internal node, it's suspended *)
                  (∃ π, (⌜ child ρTree π v ⌝) ∗
                        oblG_owner v τ (1/2)%Qp ∗
                        ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1/2)%Qp ∗
                             (∃ x ψ, otreeG_suspend v x θ π ψ ∗ otreeG_wait v x (1/2)%Qp)))
      )) ∨
        (* Or the root is done *)
        ((own edge_name (reservation_map_data (A:=gmap_viewR obl_id unitUR) ρ (gmap_view_auth (DfracOwn 1) ∅))) ∗
         oblG_elem ρ ∗ oblG_done ρ ∗ ⌜ ρTree = tree_singleton ρ ⌝)
   )
  )%I.
Definition oforest `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS A Σ}
  (D : gset obl_id) : iProp Σ :=
  locked (∃ (OForest : forest obl_id), oforest_aux D OForest)%I.

Section otree.
  Context `{SI : indexT} `{WFA : WFOCM.pack A}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS A Σ}.
  Context `{Ξ : obl_class A ps positive WFOCM.ltR}.

  Global Instance otreeG_suspend_persistent k x θ π ψ : Persistent (otreeG_suspend k x θ π ψ).
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
    (own suspend_name (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO (prodO positiveO obl_idO) (leibnizO A)))) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own suspend_name (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO (prodO positiveO obl_idO) (leibnizO A)))) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap positive _))))).
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap positive _))) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma otreeG_suspend_alloc k KSus x θ π ψ :
    KSus !! x = None →
    (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> KSus))))
    ⊢ |==> (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> (<[x := (θ, π, ψ)]>KSus))))) ∗
           otreeG_suspend k x θ π ψ.
  Proof.
    iIntros (Hx) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ x (DfracDiscarded) (to_agree (θ, π, ψ))); try done.
      rewrite lookup_fmap Hx. done.
    }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Hs]".
    rewrite /otreeG_suspend. iFrame "Hs".
    rewrite fmap_insert. by iFrame.
  Qed.
  Lemma otreeG_suspend_lookup k KSus x θ π ψ :
    (own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> KSus)))) ∗
    otreeG_suspend k x θ π ψ
    ⊢ ⌜ KSus !! x = Some (θ, π, ψ) ⌝.
  Proof.
    rewrite /otreeG_suspend -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H1.
    destruct H1 as (?&_&_&?&?&?). iPureIntro.
    rewrite lookup_fmap in H1. destruct (KSus !! x) eqn:HK.
    - inv H1. apply to_agree_included_L in H3. by subst.
    - done.
  Qed.

  Lemma otreeG_suspend_agree k x θ1 θ2 π1 π2 ψ1 ψ2 :
    otreeG_suspend k x θ1 π1 ψ1 ∗ otreeG_suspend k x θ2 π2 ψ2 ⊢ ⌜ θ1 = θ2 ∧ π1 = π2 ∧ ψ1 = ψ2 ⌝.
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

  Lemma osuspend_suspend D k θ π ψ :
    osuspend D ∗ otreeG_elem k ∗ othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1
    ⊢ |==> osuspend D ∗ ∃ x, otreeG_suspend k x θ π ψ ∗ otreeG_wait k x 1.
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
    iMod (otreeG_suspend_alloc _ _ _ θ π ψ Hxlu with "HkS") as "[HkS Hs]".
    iFrame "Hw Hs". iModIntro. iExists (<[k:=<[x:=(θ, π, ψ)]>KSus]>OSus). iSplitR.
    { iPureIntro. rewrite dom_insert_lookup_L; eauto. }
    iFrame "HS HW HE". iApply (big_sepM_delete _ _ k).
    { apply lookup_insert_eq. }
    rewrite delete_insert_eq. iFrame "HM".
    iFrame "HkS". rewrite dom_insert_L. iFrame "HkW".
    iApply (big_sepM_insert _ _ x); first auto.
    iFrame "HkM". iLeft. iLeft. iFrame.
  Qed.

  Lemma osuspend_done_parent D k x θ π ψ TP :
    osuspend D ∗ otreeG_elem k ∗ otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2)%Qp ∗
    othread TP ∗ othreadG_elem θ ∗ othreadG_owns θ k false (1/2)%Qp ∗
    oblG_owner k θ (1/2/2)%Qp ∗ oblG_done π ∗ oblG_progress k ψ
    ⊢ |==> osuspend D ∗ othreadG_owns θ k true (1/2)%Qp ∗ otreeG_edge π k 1 ∗ othread TP.
  Proof.
    iIntros "(Rsus & Re & Rs & Rw & Tthr & Te & To & Bo & Bs & Bp)".
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
      iPoseProof (big_sepM_delete _ _ x _ Hxlu with "[RkM To1 Rw Bs Bp]") as "RkM".
      { iFrame "RkM". iLeft. iRight. iFrame. }
      iPoseProof (big_sepM_delete _ _ k _ Hklu with "[RM RkM RkS RkW]") as "RM".
      { iFrame "RM". iFrame. }
      iModIntro. iExists OSus. iFrame. done.
    - iDestruct "Rkx" as "(Rko & Rkw & Rks)".
      iPoseProof (othreadG_owns_agree with "[To Rko]") as "%"; first iFrame. done.
    - iPoseProof (otreeG_wait_null_false with "[Rw Rkx]") as "%"; first iFrame. done.
  Qed.

  Lemma osuspend_wait_cases D k x θ π ψ :
    osuspend D ∗ otreeG_elem k ∗ otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2)%Qp
    ⊢ (otreeG_wait k x (1/2)%Qp ∗
       othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1 ∗
       ((othreadG_owns θ k false (1/2)%Qp ∗ otreeG_edge π k 1) -∗ osuspend D))
      ∨
        |==> (othreadG_owns θ k true (1/2)%Qp ∗ oblG_done π ∗ oblG_progress k ψ ∗ osuspend D).
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
    - iDestruct "Rkx" as "(Rkx1 & Rkx2 & Rkx3 & Rkx4)". iRight. iFrame "Rkx1 Rkx3 Rkx4".
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

  Lemma osuspend_wait_cases_many_live Ω D π (κ : gmap obl_id (positive * positive * A)) :
    (∃ d, Ω !! π = Some (obl_live d)) →
    osat Ω ∗ osuspend D ∗
    (* from user *)
    oblG_elem π ∗
    ([∗ map] k ↦ '(x, θ, ψ) ∈ κ, otreeG_elem k ∗ otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2))
    ⊢ osat Ω ∗
    ([∗ map] k ↦ '(x, θ, ψ) ∈ κ, otreeG_wait k x (1/2)) ∗
    ([∗ map] k ↦ '(x, θ, ψ) ∈ κ, othreadG_owns θ k false (1/2) ∗ otreeG_edge π k 1) ∗
    (([∗ map] k ↦ '(x, θ, ψ) ∈ κ, othreadG_owns θ k false (1/2) ∗ otreeG_edge π k 1) -∗ osuspend D).
  Proof.
    iIntros (Hlive) "(S & U & #Beπ & M)".
    iAssert ([∗ map] k ↦ _ ∈ κ, ⌜ k ∈ D ⌝)%I with "[-]" as "%Hins".
    { iClear "Beπ S". iStopProof. induction κ using map_ind; iIntros "(U& M)"; first done.
      rewrite !big_sepM_insert; auto. destruct x as [[? ?] ?]. iDestruct "M" as "((Fei& _)& M)".
      iPoseProof (IHκ with "[$]") as "#H". iPoseProof (osuspend_elem_elem with "[$]") as "%". iSplit; done. }
    rewrite /osuspend -lock. iDestruct "U" as "(% & %Hdom & RS & RW & RE & RM )".
    iAssert (
        osat Ω ∗
        ([∗ map] k↦'(x, _, _) ∈ κ, otreeG_wait k x (1 / 2)) ∗
        ([∗ map] k↦'(_, θ, _) ∈ κ, othreadG_owns θ k false (1 / 2) ∗ otreeG_edge π k 1) ∗
        (([∗ map] k↦'(_, θ, _) ∈ κ, othreadG_owns θ k false (1 / 2) ∗ otreeG_edge π k 1) -∗
         ([∗ map] k↦KSus ∈ OSus,
            own suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> (KSus : gmap positive (positive * obl_id * leibnizO A))))) ∗
            own wait_name (reservation_map_data k (reservation_map_token (⊤ ∖ gset_to_coPset (dom KSus)))) ∗
            ([∗ map] x↦'(θ, π0, ψ) ∈ KSus,
               (((othreadG_owns θ k false (1 / 2) ∗ otreeG_edge π0 k 1) ∨
                  (othreadG_owns θ k true (1 / 2) ∗ otreeG_wait k x (1 / 2) ∗ oblG_done π0 ∗ oblG_progress k ψ)) ∨
              (otreeG_wait_null k x)))))
      )%I with "[- RS RW RE]" as "H"; cycle 1.
    { iDestruct "H" as "(S& Fws& Hs& M)". iFrame "RS RW RE S Fws Hs". iIntros "Hs".
      iExists OSus. iSplitR; first done. iApply ("M" with "Hs"). }
    iStopProof. subst D. revert OSus Hins. induction κ using map_ind; iIntros (OSus Hins) "(#Beπ& S& M& Ws)".
    { rewrite !big_sepM_empty. by iFrame. }
    apply map_Forall_insert in Hins; last auto. destruct Hins as [Hin Hins].
    rewrite !big_sepM_insert; auto. destruct x as [[x θ] ψ]. iDestruct "Ws" as "((#Fei& #Fsi& Fwi)& Ws)".
    apply elem_of_dom in Hin. destruct Hin as [KSus Hin]. iPoseProof (big_sepM_delete _ _ _ _ Hin with "M") as "[Mi M]".
    assert (Hins2 : map_Forall (λ (k : obl_id) (_ : positive * positive * A), k ∈ dom (delete i OSus)) m).
    { intros ???. specialize (Hins i0 x0 H2). destruct (decide (i0 = i)).
      - subst. by rewrite H1 in H2.
      - rewrite dom_delete_L. set_solver + Hins n. }
    iPoseProof (IHκ _ Hins2 with "[S M Ws]") as "(S& Ws& As& Ms)".
    { iSplitR; first auto. iFrame. }
    clear IHκ. iDestruct "Mi" as "(RkS & RkW & RkM)".
    iPoseProof (otreeG_suspend_lookup with "[RkS]") as "%Hxlu"; first by iFrame.
    iDestruct (big_sepM_delete _ _ x _ Hxlu with "RkM") as "[Rkx RkM]".
    iDestruct "Rkx" as "[[Rkx | Rkx] | Rkx]".
    - iFrame. iIntros "[Hi Hs]". iPoseProof ("Ms" with "Hs") as "Ms".
      iApply (big_sepM_delete _ _ _ _ Hin). iFrame. iApply (big_sepM_delete _ _ _ _ Hxlu). iFrame.
    - iDestruct "Rkx" as "(_&_&Bdπ&_)". iPoseProof (osat_obl_is_done_weak with "[S Bdπ]") as "%"; first by iFrame.
      destruct Hlive, H2. rewrite H3 in H2. done.
    - iPoseProof (otreeG_wait_null_false with "[Fwi Rkx]") as "%"; first iFrame. done.
  Qed.

  (** oforest rules *)
  Lemma oforest_alloc_obl D ρ θ α β :
    ρ ∉ D →
    oforest D ∗
    othreadG_owns θ ρ true (1/2)%Qp ∗
    otreeG_elem ρ ∗
    oblG_elem ρ ∗ oblG_live ρ (1/2/2)%Qp ∗ oblG_owner ρ θ (1/2/2)%Qp ∗
    oblG_transfer_bound ρ α ∗ oblG_progress_supply ρ β (1/2)%Qp
    ⊢ |==> oforest ({[ρ]} ∪ D).
  Proof.
    iIntros (Hρ) "(Rfor & To & Fe & Be & Bl & Bo & Bb & Bps)".
    rewrite /oforest -lock /oforest_aux. iDestruct "Rfor" as "(% & %Hf & Retk & RM)". destruct Hf as [Hf1 Hf2].
    assert (Hρlu : forest_fold OForest !! ρ = None).
    { apply not_elem_of_dom. rewrite Hf1. auto. }
    assert (Hρlu2 : OForest !! ρ = None).
    { apply forest_fold_not_in_forest_not_in; auto. }
    iMod (otreeG_edge_alloc_map D ρ Hρ with "Retk") as "[Retk Reρ]".
    iPoseProof (big_sepM_insert _ _ _ (tree_singleton ρ) Hρlu2 with "[RM To Fe Be Bl Bo Bb Bps Reρ]") as "RM".
    { iFrame "RM". iLeft. iFrame "To Bo". iApply big_sepM_singleton. iFrame. iSplit; first done. by iLeft. }
    iModIntro. rewrite -lock. iExists (forest_insert OForest ρ (tree_singleton ρ)).
    iFrame. iPureIntro. split.
    { subst D. apply forest_fold_insert_singleton_dom; auto. }
    { apply forest_insert_singleton_wf; auto. }
  Qed.

  Lemma oforest_aux_wf D OForest :
    oforest_aux D OForest ⊢ ⌜ dom (forest_fold OForest) = D ∧ forest_wf OForest ⌝.
  Proof. iIntros "F". rewrite /oforest_aux. iDestruct "F" as "(%Hf & Retk & RM)". done. Qed.

  Lemma oforest_in_tree Ω OForest v :
    osat Ω ∗ oforest_aux (dom Ω) OForest ∗ oblG_elem v
    ⊢ ∃ ρ ρt vC, ⌜ OForest !! ρ = Some ρt ∧ ρt !! v = Some vC ⌝.
  Proof.
    iIntros "(S & F & #Bev)".
    rewrite /oforest_aux. iDestruct "F" as "(% & Retk & RM)". destruct H1 as [Hfdom Hfwf].
    iPoseProof (osat_elem with "[S]") as "%Hvelem"; first by iFrame.
    destruct (OForest !! v) eqn:Hπlu.
    - destruct Hfwf. assert (tree_wf v g) by eauto. inversion H3. subst ρ t.
      iExists v, g, (dom Cf). iPureIntro. split; auto. subst g. by rewrite /forest_merge lookup_insert_eq.
    - destruct Hfwf. rewrite -Hfdom in Hvelem. apply elem_of_dom in Hvelem. destruct Hvelem.
      pose proof (forest_fold_lookup_Some_exists_root _ _ _ H1 H3). destruct H4 as (?&?&?&?).
      iExists x0, x1, x. iPureIntro. split; auto.
  Qed.

  Definition obl_cond_in_tree (t : tree obl_id) : obl_cond :=
    λ k o, node t k.
  Definition obl_cond_one (v : obl_id) : obl_cond :=
    λ k o, k = v.
  Definition obl_cond_internal_tree (t : tree obl_id) : obl_cond :=
    λ k o, internal t k.

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
          ∃ Ω', (⌜Ω ↪ₚ Ω' | obl_cond_in_tree ρTree⌝) ∗ osat Ω' ∗ (⌜forest_wf OForest⌝) ∗
                ((∃ τ, oblG_owner ρ τ (1 / 2 / 2) ∗ othreadG_owns τ ρ true (1 / 2) ∗
                       ([∗ map] v↦vCh ∈ ρTree,
                          own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗ oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗ otreeG_elem v ∗
                          (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                                  ([∗ set] c ∈ vCh, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                          (⌜v = ρ⌝
                                ∨ ∃ π , ⌜child ρTree π v⌝ ∗ oblG_owner v τ (1 / 2) ∗
                                        ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                                             ∃ x ψ, otreeG_suspend v x θ π ψ ∗ otreeG_wait v x (1 / 2))))
                 ∨ own edge_name (reservation_map_data ρ (A:=gmap_viewR obl_id unitUR) (gmap_view_auth (DfracOwn 1) ∅)) ∗ oblG_elem ρ ∗
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
          ∃ Ω', (⌜Ω ↪ₚ Ω' | obl_cond_in_tree ρTree⌝) ∗ osat Ω' ∗ (⌜forest_wf OForest⌝) ∗
                (oblG_owner ρ τ (1 / 2 / 2) ∗ othreadG_owns τ ρ true (1 / 2) ∗
                 ([∗ map] v↦vCh ∈ ρTree,
                    own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗ oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗ otreeG_elem v ∗
                    (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                            ([∗ set] c ∈ vCh, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                    (⌜v = ρ⌝
                          ∨ ∃ π, ⌜child ρTree π v⌝ ∗ oblG_owner v τ (1 / 2) ∗
                                 ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗ ∃ x ψ, otreeG_suspend v x θ π ψ ∗ otreeG_wait v x (1 / 2))))
      )%I with "[-]" as "H"; cycle 1.
    { iMod "H" as "(%&%&H0&%&H1)". iModIntro. iExists Ω'. iFrame. iSplitR; auto. }
    iAssert (
        ([∗ map] v↦vCh ∈ ρTree,
           oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
           (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                   ([∗ set] c ∈ vCh, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')))
        ∗ [∗ map] v↦vCh ∈ ρTree,
          own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗ otreeG_elem v ∗
          (⌜v = ρ⌝
                ∨ ∃ π, ⌜child ρTree π v⌝ ∗ oblG_owner v τ (1 / 2) ∗
                       ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                            ∃ x ψ, otreeG_suspend v x θ π ψ ∗ otreeG_wait v x (1 / 2))
      )%I with "[RMρM]" as "[RMρM RMρM0]".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "RMρM").
      iModIntro. iIntros (???) "(?&?&?&?&?&?)". iFrame. }
    iAssert (
        |==>
          ∃ Ω', (⌜Ω ↪ₚ Ω' | obl_cond_in_tree ρTree⌝) ∗ osat Ω' ∗ (⌜forest_wf OForest⌝) ∗
                ([∗ map] v↦vCh ∈ ρTree,
                   oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
                   (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                           ([∗ set] c ∈ vCh, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')))
      )%I with "[- RMρM0 RMρBo RMρTo]" as "H"; cycle 1.
    { iMod "H" as "(%&%&S&%&M)". iModIntro. iFrame. iSplitR; first auto. iSplitR; first auto.
      iPoseProof (big_sepM_sep with "[RMρM0 M]") as "H"; first iFrame. iApply (big_sepM_impl with "H").
      iModIntro. iIntros (???) "(?&?&?&?)". iFrame. }
    (* First induction: on ρTree. Need to weaken some assumptions *)
    assert (Htwf : tree_wf ρ ρTree).
    { destruct Hfwf. eapply H2; auto. }
    clear Hfdom τ. iStopProof.
    generalize dependent a. generalize dependent d. generalize dependent Ω. generalize dependent OForest.
    pattern ρ, ρTree. revert ρ ρTree Htwf. apply tree_wf_internal_ind.
    intros ρ ρTree HρTreewf IH1 OForest Hρ Hfwf Ω d Hρlu a Ha.
    iIntros "(#Be & S & Bp & RMρ)".
    iAssert (|==> ∃ Ωρ, (⌜ Ω ↪ₚ Ωρ | (λ k o, node ρTree k ∧ root ρTree k) ⌝) ∗
             |==> ∃ Ω', (⌜ Ωρ ↪ₚ Ω' | (λ k o, internal ρTree k) ⌝) ∗ osat Ω' ∗ (⌜forest_wf OForest⌝) ∗
                        (([∗ map] v↦vCh ∈ ρTree,
                            oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
                            (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                                    ([∗ set] c ∈ vCh, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'))))
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
          ∃ Ω', (⌜Ω0 ↪ₚ Ω' | λ k _, node (forest_fold Cf) k⌝) ∗ osat Ω' ∗ (⌜forest_wf OForest⌝) ∗
                ([∗ map] v↦vCh ∈ ρTree,
                   oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
                   (∃ α1 β1, oblG_transfer_bound v α1 ∗ oblG_progress_supply v β1 (1 / 2) ∗
                             ([∗ set] c ∈ vCh, ∃ α' β'0, ⌜α1 /< α' ∧ β1 /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0)))
      )%I with "[-]" as "H"; cycle 1.
    { iMod "H" as "(%&%&H)". iModIntro. iFrame. iPureIntro. eapply obl_states_cond_rel_iff; first eapply H5.
      simpl; intros. subst. rewrite forest_merge_internal_forest_fold_node_iff; eauto. }
    iAssert (
        |==>
          ∃ Ω', (⌜Ω0 ↪ₚ Ω' | λ k _, node (forest_fold Cf) k⌝) ∗ osat Ω' ∗ (⌜forest_wf OForest⌝) ∗
                ([∗ set] c ∈ dom Cf, ∃ α' β'0, ⌜α /< α' ∧ β' /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0) ∗
                ([∗ map] v↦vCh ∈ (forest_fold Cf),
                   oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗
                   (∃ α1 β1, oblG_transfer_bound v α1 ∗ oblG_progress_supply v β1 (1 / 2) ∗
                             ([∗ set] c ∈ vCh, ∃ α' β'0, ⌜α1 /< α' ∧ β1 /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0)))
      )%I with "[- Hl Hb0 Hb1]" as "H"; cycle 1.
    { iMod "H" as "(%&%& S &%& H)".
      iDestruct "H" as "(HCS&HM)". iModIntro. iExists Ω'. iSplitR; first done. iFrame "S". iSplitR; first done.
      iApply (big_sepM_delete _ _ _ _ Hρlutree with "[-]"). iFrame "Hl Hb0 Hb1". iSplitL "HCS".
      { iSplitR; first auto.
        iApply (big_sepS_impl with "[$]"). iModIntro. iIntros (? ?) "(%&%&%&H1&H2)".
        iExists α', β'0. iFrame. destruct H8. iSplit; done. }
      subst ρTree. rewrite /forest_merge delete_insert_id; auto. }
    iAssert (
        [∗ map] k↦y ∈ (forest_fold Cf),
          oblG_elem k ∗ oblG_live k (1/2/2)%Qp ∗
          (∃ α1 β1, oblG_transfer_bound k α1 ∗ oblG_progress_supply k β1 (1 / 2) ∗
                    ([∗ set] c ∈ y, ∃ α' β'0, ⌜α1 /< α' ∧ β1 /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0))
      )%I with "[RMρM]" as "RMρ".
    { subst. rewrite /forest_merge delete_insert_id; auto. }
    iAssert (
        |==> ([∗ set] c ∈ dom Cf, ∃ u, ⌜ /0 /< u ⌝ ∗ oblG_progress c u) ∗
             ([∗ set] c ∈ dom Cf, ∃ α' β'0, ⌜α /< α' ∧ β' /≤ β'0⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'0)
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

  Lemma oforest_exceed_not_lineage Ω OForest ρ ρt v ℵ u a :
    ℵ /< a →
    OForest !! ρ = Some ρt →
    node ρt v →
    (∃ d, Ω !! v = Some (obl_live d)) →
    osat Ω ∗ oforest_aux (dom Ω) OForest ∗
    oblG_elem v ∗ oblG_transfer_bound v ℵ ∗
    oblG_transfer u a
    ⊢ ⌜ ¬ lineage ρt u v ⌝.
  Proof.
    iIntros (Ha Hρlu Hv HOlu) "(S & F & #Bev & #Bbv & Btu)".
    iIntros "%Hlin". apply lineage_lineage_up in Hlin.
    iStopProof. revert ℵ Ha Hv HOlu. induction Hlin.
    - iIntros (ℵ Ha Hx1 Hx2) "([#Bex #Bbx] & S & F & Btx)".
      iPoseProof (osat_transfer_bound_exceed with "[S Btx]") as "%".
      { eapply Ha. }
      { iFrame. eauto. }
      done.
    - iIntros (ℵ Ha Hxd Hxl) "([#Bex #Bbx] & S & F & Btz)".
      assert (node ρt y).
      { destruct H1 as (?&?&?). by eexists. }
      iAssert (∃ α, ⌜ α /< a ∧ (∃ d, Ω !! y = Some (obl_live d)) ⌝ ∗ oblG_elem y ∗ oblG_transfer_bound y α)%I
        with "[-]" as "(%&%&#IH1&#IH2)".
      { rewrite /oforest_aux. iDestruct "F" as "(% & Retk & RM)". destruct H3 as [Hfdom Hfwf].
        iPoseProof (big_sepM_delete _ _ _ _ Hρlu with "RM") as "[Rm RM]".
        iDestruct "Rm" as "[(%&Boρ&Toρ&Rm) | (_&Be&Bd&%)]"; cycle 1.
        { iExFalso. destruct (decide (x = ρ)).
          - subst x. iPoseProof (osat_obl_is_done_weak with "[S Be Bd]") as "%"; first iFrame.
            destruct H4 as (?&?). destruct Hxl as (?&?). rewrite H5 in H4. inv H4.
          - destruct Hfwf as [Hfwf1 Hfwf2]. assert (tree_wf ρ ρt) by eauto.
            destruct (tree_wf_child_node _ _ _ _ H4 H1).
            rewrite /node H3 lookup_insert_ne in H6; auto. by destruct H6. }
        destruct H1 as (C&?&?). iPoseProof (big_sepM_delete _ _ _ _ H1 with "Rm") as "[Hy Rm]".
        iDestruct "Hy" as "(_&Bey&Bly&Fe& (%&%&#Btby&_&Cy) & _)".
        iPoseProof (osat_obl_is_live with "[S Bey Bly]") as "%Hyl"; first (iFrame; eauto).
        iPoseProof (big_sepS_delete _ _ _ H3 with "Cy") as "[(%&%&%&Btx&_) Cy]". destruct H4.
        iPoseProof (osat_transfer_bound_transfer_le with "[S Bex Bbx Btx]") as "%"; first (iFrame; eauto).
        iExists α. iFrame "Bey Btby".
        iPureIntro. split; auto. eapply WFOCM.le_lt_lt; last eapply Ha. etrans; eauto. eapply WFOCM.lt_le; eauto. }
      destruct H3 as (?&?). specialize (IHHlin _ H3 H2 H4).
      iApply IHHlin. iFrame. eauto.
  Qed.

  Lemma oforest_tree_live Ω Φ ρ ρt v u :
    Φ !! ρ = Some ρt →
    (∃ d, Ω !! v = Some (obl_live d)) →
    node ρt v →
    node ρt u →
    osat Ω ∗ oforest_aux (dom Ω) Φ ∗ oblG_elem v ⊢ ⌜ ∃ d, Ω !! u = Some (obl_live d) ⌝.
  Proof.
    iIntros (LUρ Livev Nodev Nodeu) "(S & F & #Bev)".
    iDestruct "F" as "(% & Fetk & FM)". destruct H1 as [DomF WFF].
    assert (Nodeρ : node ρt ρ).
    { destruct WFF. apply elem_of_dom, tree_wf_root_elem; auto. }
    iPoseProof (big_sepM_delete _ _ _ _ LUρ with "FM") as "[Fmρ FM]".
    destruct (Ω !! ρ) eqn:LUOρ.
    - destruct o.
      + iDestruct "Fmρ" as "[(%&Bo&To&Fmρ) | (H0&H1&H2&%)]".
        * destruct Nodeu. iPoseProof (big_sepM_delete _ _ _ _ H1 with "Fmρ") as "[Fmρu Fmρ]".
          iDestruct "Fmρu" as "(_&Beu&Blu&_)". iPoseProof (osat_obl_is_live _ u with "[$]") as "%". done.
        * iPoseProof (osat_obl_is_done_weak _ ρ with "[$]") as "%". destruct H2. rewrite LUOρ in H2. inv H2.
      + iDestruct "Fmρ" as "[(%&Bo&To&Fmρ) | (H0&H1&H2&%)]".
        * destruct Nodeρ. iPoseProof (big_sepM_delete _ _ _ _ H1 with "Fmρ") as "[Fmρρ Fmρ]".
          iDestruct "Fmρρ" as "(_&Beρ&Blρ&_)". iPoseProof (osat_obl_is_live _ ρ with "[$]") as "%".
          destruct H2. rewrite LUOρ in H2. inv H2.
        * subst ρt. assert (v = ρ).
          { destruct (decide (v = ρ)); auto. destruct Nodev. rewrite /tree_singleton lookup_singleton_ne in H1; auto. inv H1. }
          subst v. iPoseProof (osat_obl_is_done_weak _ ρ with "[$]") as "%". destruct Livev, H1. rewrite H1 in H2. inv H2.
    - apply not_elem_of_dom in LUOρ. destruct WFF. assert (ρt ⊆ forest_fold Φ) by (eapply forest_fold_subseteq; eauto).
      exfalso. apply subseteq_dom in H3. apply elem_of_dom in Nodeρ. rewrite -DomF in LUOρ. set_solver + Nodeρ H3 LUOρ.
  Qed.

  Lemma big_sepM_forest_fold {V : Type} `{Countable V} (f : forest V) (Φ : V → gset V → iProp Σ) :
    forest_trees_disjoint f →
    ([∗ map] v ↦ vC ∈ (forest_fold f), Φ v vC) ⊣⊢ [∗ map] ρ ↦ ρt ∈ f, ([∗ map] v ↦ vC ∈ ρt, Φ v vC).
  Proof.
    intros Disj. iSplit; iIntros "H".
    - iStopProof. revert Disj. induction f using map_ind; iIntros (Disj) "H"; first done.
      rewrite forest_fold_insert_L; auto.
      apply forest_trees_disjoint_insert in Disj; auto. destruct Disj as [Dx Disj].
      iPoseProof (big_sepM_union with "H") as "[Hx H]".
      { apply tree_disjoint_forest_fold_disjoint; auto. }
      iPoseProof (IHf Disj with "H") as "H". iApply big_sepM_insert; auto. iFrame.
    - iStopProof. revert Disj. induction f using map_ind; iIntros (Disj) "H"; first done.
      rewrite forest_fold_insert_L; auto.
      apply forest_trees_disjoint_insert in Disj; auto. destruct Disj as [Dx Disj].
      iPoseProof (big_sepM_insert with "H") as "[Hx H]"; auto.
      iPoseProof (IHf Disj with "H") as "H". iApply big_sepM_union.
      { apply tree_disjoint_forest_fold_disjoint; auto. }
      iFrame.
  Qed.

  Lemma oforest_aux_othreadG_owns_true_root Ω TP Φ i ρ x :
    osat Ω ∗ othread TP ∗ oforest_aux (dom Ω) Φ ∗
    oblG_elem ρ ∗ othreadG_elem i ∗ othreadG_owns i ρ true x
    ⊢ ∃ ρt, ⌜Φ !! ρ = Some ρt⌝.
  Proof.
    iIntros "(S& T& F& #Beρ& #Tei& Toρ)".
    rewrite /oforest_aux. iDestruct "F" as "(% & Fetk & FM)". destruct H1 as [Dom WFΦ].
    iPoseProof (osat_elem ρ with "[S]") as "%Inρ"; first by iFrame.
    assert (is_Some ((forest_fold Φ) !! ρ)).
    { apply elem_of_dom. rewrite Dom. auto. }
    destruct H1. destruct WFΦ as [DisjΦ TwfsΦ].
    destruct (forest_fold_lookup_Some_exists_root _ _ _ DisjΦ H1) as (r&rt&LUr&LUrt).
    iPoseProof (big_sepM_delete _ _ _ _ LUr with "FM") as "[M _]".
    iDestruct "M" as "[(%&Boρ2&Toρ2&M) | (_& Beρ2& Bdρ& %)]".
    - iPoseProof (big_sepM_delete _ _ _ _ LUrt with "M") as "[(_& Beρ2& Blρ& Teρ& _& [% | H]) _]".
      + subst r. iExists rt. done.
      + iDestruct "H" as "(%&%&Boρ& %&#Teθ& Toρ3& _)".
        iPoseProof (othread_live_open with "[T Tei Toρ]") as "(Toρ& [Blρ2 Boρ3]& T)"; first by iFrame.
        iExFalso. iPoseProof (osat_live_open_owner with "[S Beρ Blρ]") as "(%& _& _& Boρ'& _)"; first by iFrame.
        iPoseProof (oblG_owner_agree with "[Boρ Boρ']") as "%"; first iFrame. destruct H3. subst i0.
        iCombine "Boρ Boρ'" as "Boρ". iPoseProof (oblG_owner_div_2 _ _ (1) with "Boρ") as "Boρ".
        iPoseProof (oblG_owner_agree with "[Boρ Boρ3]") as "%"; first iFrame. destruct H3.
        apply Qp.not_add_le_r in H5. done.
    - subst rt. destruct (decide (r = ρ)); cycle 1.
      { rewrite /tree_singleton lookup_singleton_ne in LUrt; auto. }
      subst r. eauto.
  Qed.

  (* Progress of a thread *)
  Lemma oforest_aux_progress_one_thread Ω TP Φ i Ψ (γ : gmap obl_id (bool * Qp)) :
    Ψ = dom γ →
    osat Ω ∗ othread TP ∗ oforest_aux (dom Ω) Φ ∗
    (* from user *)
    othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗
    ([∗ map] ρ ↦ '(f, q) ∈ γ,
       match f with
       | true => (oblG_elem ρ ∗ othreadG_owns i ρ f q ∗ ∃ a, ⌜ /0 /< a ⌝ ∗ oblG_progress ρ a)
       | false => (oblG_elem ρ ∗ othreadG_owns i ρ f q)
       end)
    ⊢ |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | (obl_cond_owner i) ⌝) ∗
                 osat Ω' ∗ othread TP ∗ oforest_aux (dom Ω') Φ ∗
                 othreadG_obls i Ψ 1 ∗
                 ([∗ map] ρ ↦ '(f, q) ∈ γ,
                    match f with
                    | true => (othreadG_owns i ρ f q)
                    | false => (othreadG_owns i ρ f q)
                    end).
  Proof.
    iIntros (Domγ) "(S& T& F& Tei& Tbi& Tos)".
    iAssert (∃ (γ1 γ2 : gmap obl_id Qp),
                (⌜ (snd <$> γ) = γ1 ∪ γ2 ∧ γ1 ##ₘ γ2 ∧ (γ = ((λ q, (true, q)) <$> γ1) ∪ ((λ q, (false, q)) <$> γ2)) ⌝) ∗
                ([∗ map] ρ ↦ q ∈ γ1,
                   (oblG_elem ρ ∗ othreadG_owns i ρ true q ∗ ∃ a, ⌜ /0 /< a ⌝ ∗ oblG_progress ρ a)) ∗
                ([∗ map] ρ ↦ q ∈ γ2,
                   (oblG_elem ρ ∗ othreadG_owns i ρ false q))
            )%I with "[Tos]" as "TH".
    { clear Domγ. iStopProof. induction γ using map_ind.
      { iIntros "H". iExists ∅, ∅. iSplitR.
        { iPureIntro. rewrite fmap_empty. split; first set_solver. split; first apply map_disjoint_empty_l. done. }
        iSplitR; done. }
      iIntros "H". iPoseProof (big_sepM_insert with "H") as "[Ti H]"; first auto.
      iPoseProof (IHγ with "H") as "(%&%&%&H1&H2)". clear IHγ. destruct H2. destruct H3.
      assert (γ1 !! i0 = None ∧ γ2 !! i0 = None).
      { rewrite map_eq_iff in H2. specialize (H2 i0). rewrite lookup_fmap H1 in H2.
        simpl in H2. symmetry in H2. apply lookup_union_None in H2. destruct H2. auto. }
      destruct H5. destruct x as [b q]. destruct b.
      - iExists (<[i0:=q]>γ1), γ2. iSplitR.
        { iPureIntro. split_and !.
          - rewrite fmap_insert H2 insert_union_l. auto.
          - apply map_disjoint_insert_l. split; auto.
          - rewrite fmap_insert H4. by rewrite insert_union_l. }
        iFrame "H2". iApply big_sepM_insert; first auto. iFrame.
      - iExists γ1, (<[i0:=q]>γ2). iSplitR.
        { iPureIntro. split_and !.
          - rewrite fmap_insert H2 insert_union_r; auto.
          - apply map_disjoint_insert_r. split; auto.
          - rewrite fmap_insert H4. rewrite insert_union_r; auto. by rewrite lookup_fmap H5. }
        iFrame "H1". iApply big_sepM_insert; first auto. iFrame. }
    iDestruct "TH" as "(%&%&%&To1& To2)". destruct H1 as (Eqγ& Disjγ& Eqγf).
    iAssert (∀ k, ⌜ k ∈ dom γ1 ⌝ →  ∃ d, ⌜ Ω !! k = Some (obl_live d) ⌝)%I with "[-]" as "%LUOρs".
    { iIntros (k Ink). subst Ψ. apply elem_of_dom in Ink. destruct Ink.
      iPoseProof (big_sepM_delete _ _ _ _ H1 with "To1") as "[To To1]". iDestruct "To" as "(Bek& Tok& _)".
      iPoseProof (othread_live_open with "[T Tei Tok]") as "(_& [Blk _]& _)"; first iFrame.
      iPoseProof (osat_obl_is_live with "[S Bek Blk]") as "A"; first iFrame. done. }
    set (C:=λ (k : obl_id) (o : obl_state), ∃ ρ, is_Some (γ1 !! ρ) ∧ ∃ ρt, Φ !! ρ = Some ρt ∧ node ρt k).
    iAssert (∀ k o, ⌜ Ω !! k = Some o ⌝ → ⌜ obl_cond_owner i k o ⌝ → ⌜ C k o ⌝)%I with "[-]" as "%OCEq1".
    { subst C. simpl. iIntros (k o LUOk OC). destruct o; last done. rewrite /obl_cond_owner in OC.
      rewrite /oforest_aux. iDestruct "F" as "(% & Fetk & FM)". destruct H1 as [Dom WFΦ].
      assert (LUΦk : is_Some ((forest_fold Φ) !! k)).
      { apply elem_of_dom. rewrite Dom. apply elem_of_dom. auto. }
      destruct LUΦk as [Ck LUΦk]. pose proof WFΦ. destruct H1 as [DisjΦ TwfsΦ].
      pose proof (forest_fold_lookup_Some_exists_root _ _ _ DisjΦ LUΦk). destruct H1 as (ρ&ρt&LUΦρ&LUρtk).
      iPoseProof (big_sepM_delete _ _ _ _ LUΦρ with "FM") as "[M _]".
      iDestruct "M" as "[(%&Boρ&Toρ&M) | (_& Beρ& Bdρ& %)]"; cycle 1.
      { iExFalso. iPoseProof (osat_obl_is_done_weak with "[S Beρ Bdρ]") as "(%&%)"; first by iFrame.
        subst ρt. destruct (decide (ρ = k)); cycle 1.
        { rewrite /tree_singleton lookup_singleton_ne in LUρtk; auto. }
        subst k. rewrite LUOk in H2. inv H2. }
      iPoseProof (big_sepM_delete _ _ _ _ LUρtk with "M") as "[H _]". iDestruct "H" as "(_& Bek& Blk& Tek& _& [% | H])".
      - subst k. iPoseProof (osat_lookup_owner with "[S Bek Boρ]") as "[% %]"; first by iFrame.
        destruct H1. rewrite LUOk in H1. inv H1.
        iPoseProof (othread_obls_owns_elem with "[T Tbi Toρ]") as "%"; first by iFrame.
        apply elem_of_dom in H1. destruct H1. destruct x.
        rewrite map_eq_iff in Eqγ. specialize (Eqγ ρ). rewrite lookup_fmap H1 in Eqγ. simpl in Eqγ. symmetry in Eqγ.
        apply lookup_union_Some in Eqγ; last auto. destruct Eqγ.
        + iPureIntro. exists ρ. split_and !; auto. exists ρt. split; auto. unfold node; eauto.
        + iPoseProof (big_sepM_delete _ _ _ _ H2 with "To2") as "[H To2]". iDestruct "H" as "[H1 H2]".
          iPoseProof (othreadG_owns_agree with "[Toρ H2]") as "%"; first iFrame. inv H3.
      - iDestruct "H" as "(%&%&Bok& %&Teθ& Tok& %&%& Tsk& Twk)".
        iPoseProof (osat_lookup_owner with "[S Bek Bok]") as "[% %]"; first by iFrame.
        destruct H2. rewrite LUOk in H2. inv H2.
        iPoseProof (othread_obls_owns_elem with "[T Tbi Toρ]") as "%"; first by iFrame.
        apply elem_of_dom in H2. destruct H2. destruct x0.
        rewrite map_eq_iff in Eqγ. specialize (Eqγ ρ). rewrite lookup_fmap H2 in Eqγ. simpl in Eqγ. symmetry in Eqγ.
        apply lookup_union_Some in Eqγ; last auto. destruct Eqγ.
        + iPureIntro. exists ρ. split_and !; auto. exists ρt. split; auto. unfold node; eauto.
        + iPoseProof (big_sepM_delete _ _ _ _ H3 with "To2") as "[H To2]". iDestruct "H" as "[H1 H2]".
          iPoseProof (othreadG_owns_agree with "[Toρ H2]") as "%"; first iFrame. inv H4. }
    iAssert (∀ k o, ⌜ Ω !! k = Some o ⌝ → ⌜ C k o ⌝ → ⌜ obl_cond_owner i k o ⌝)%I with "[-]" as "%OCEq2".
    { subst C. simpl. iIntros (k o LUOk OC). destruct OC as (ρ&?&ρt&LUΦρ&Nodek). destruct H1 as [q LUγρ].
      rewrite /oforest_aux. iDestruct "F" as "(% & Fetk & FM)". destruct H1 as [Dom WFΦ].
      iPoseProof (big_sepM_delete _ _ _ _ LUΦρ with "FM") as "[M _]".
      assert (InΨρ : ρ ∈ Ψ).
      { subst. apply elem_of_dom_2 in LUγρ. rewrite -(dom_fmap_L snd). rewrite Eqγ. rewrite dom_union_L. set_solver + LUγρ. }
      iClear "To2". iPoseProof (big_sepM_delete _ _ _ _ LUγρ with "To1") as "[To _]". iDestruct "To" as "(Beρ& Toρ& _)".
      iDestruct "M" as "[(%&Boρ2&Toρ2&M) | (_& Beρ2& Bdρ& %)]"; cycle 1.
      { iPoseProof (othread_obls_open _ _ _ _ InΨρ with "[T Tei Tbi]") as "(Tbi& Blρ& T)"; first by iFrame.
        iPoseProof (oblG_live_done_false with "[Bdρ Blρ]") as "%"; first iFrame. done. }
      destruct Nodek as [Ck LUρtk]. iPoseProof (big_sepM_delete _ _ _ _ LUρtk with "M") as "[H _]".
      iDestruct "H" as "(_& Bek& Blk& Tek& _& [% | H])".
      - subst k. iPoseProof (othread_live_open with "[T Tei Toρ]") as "(Toρ& (Blk2& Bok2)& T)"; first by iFrame.
        iPoseProof (oblG_owner_agree with "[Boρ2 Bok2]") as "%"; first by iFrame. destruct H1. subst i.
        iPoseProof (osat_lookup_owner with "[S Beρ Boρ2]") as "%"; first by iFrame.
        iPureIntro. destruct H1 as (?&?&?). rewrite LUOk in H1. inv H1. done.
      - iDestruct "H" as "(%&%&Bok& %&Teθ& Tok& %&%& Tsk& Twk)".
        iPoseProof (othread_live_open with "[T Tei Toρ]") as "(Toρ& (Blρ2& Boρ)& T)"; first by iFrame.
        iPoseProof (oblG_owner_agree with "[Boρ2 Boρ]") as "%"; first by iFrame. destruct H2. subst i.
        iPoseProof (osat_lookup_owner with "[S Bek Bok]") as "%"; first by iFrame.
        iPureIntro. destruct H2 as (?&?&?). rewrite LUOk in H2. inv H2. done. }
    iAssert (
        |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | C ⌝) ∗
                   osat Ω' ∗ othread TP ∗ oforest_aux (dom Ω') Φ ∗ ([∗ map] ρ ↦ q ∈ γ1, othreadG_owns i ρ true q)
      )%I with "[- Tbi To2]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%Prog& S& T& F& To1)". iModIntro. iExists Ω'. iSplitR.
      { iPureIntro. eapply obl_states_cond_rel_iff_lookup. 1: eapply Prog. intros. split; eauto. }
      iFrame. rewrite Eqγf. iApply big_sepM_union.
      { by apply map_disjoint_fmap. }
      iSplitL "To1".
      - iApply big_sepM_fmap. done.
      - iApply big_sepM_fmap. iApply (big_sepM_impl with "To2"). iModIntro. iIntros (???) "[A B]". iFrame. }
    subst C. clear OCEq1 OCEq2. clear dependent Ψ γ γ2.
    iStopProof. revert Ω TP Φ i LUOρs. induction γ1 using map_ind.
    { iIntros (Ω TP Φ i LUOs) "(S& T& F& Tei& Bps)".
      iModIntro. iExists Ω. iFrame. iSplitR; last done.
      iPureIntro. intro j. destruct (Ω !! j) eqn:LUOj; econstructor. split; intros; auto.
      destruct H1 as (?&?&?&?&?). destruct H1. done. }
    rename i into ρ. iIntros (Ω TP Φ i LUOs) "(S& T& F& #Tei& Bps)".
    iPoseProof (big_sepM_insert with "Bps") as "[Bp Bps]"; first auto.
    iDestruct "Bp" as "(#Beρ& Toρ& %& %LTa& Bpρ)".
    iPoseProof (osat_elem with "[S Beρ]") as "%LUOρ"; first by iFrame.
    iPoseProof (oforest_aux_othreadG_owns_true_root _ _ _ _ ρ with "[$]") as "%LUΦρ".
    destruct LUΦρ as [ρt LUΦρ]. assert (∃ d, Ω !! ρ = Some (obl_live d)).
    { apply LUOs. rewrite dom_insert_L. set_solver. }
    iMod (oforest_progress_one_tree _ _ _ _ _ LTa H2 LUΦρ with "[S F Bpρ]") as "(%Ω1& %Prog1& S& F)"; first iFrame.
    assert (LUO1s : ∀ x0, x0 ∈ dom m → ∃ x, Ω1 !! x0 = Some (obl_live x)).
    { intros. assert (x0 ∈ dom (<[ρ:=x]> m)).
      { rewrite dom_insert_L. set_solver + H3. }
      apply LUOs in H4. destruct H4. specialize (Prog1 x0). inv Prog1.
      - destruct H7. rewrite H4 in H5. inv H5. destruct (decide (obl_cond_in_tree ρt x0 (obl_live x1))).
        + apply H7 in o. destruct y; eauto. done.
        + apply H8 in n. subst y. eauto.
      - by rewrite H4 in H6. }
    iMod (IHγ1 _ _ _ _ LUO1s with "[S T F Tei Bps]") as "(%Ω2& %Prog2& S& T& F& Tos)"; first by iFrame.
    iExists Ω2. iModIntro. iSplitR.
    { iPureIntro. eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1. all: simpl.
      1,2,3: apply _.
      - intros. rewrite /obl_cond_in_tree. split; intros.
        + destruct H3 as (?&?&?&?&?).  apply lookup_insert_is_Some in H3. destruct H3.
          * subst. left. rewrite LUΦρ in H4. inv H4. auto.
          * destruct H3. right. eauto.
        + destruct H3 as [? | (?&?&?&?&?)].
          * exists ρ. split; eauto. by rewrite lookup_insert_eq.
          * exists x0. split; eauto. apply elem_of_dom. apply elem_of_dom in H3. rewrite dom_insert_L. set_solver + H3.
      - repeat intros ?. eauto. }
    rewrite (big_sepM_insert); last auto. iFrame.
  Qed.

  Lemma oforest_progress_one_thread Ω TP i Ψ (γ : gmap obl_id (bool * Qp)) :
    Ψ = dom γ →
    osat Ω ∗ othread TP ∗ oforest (dom Ω) ∗
    (* from user *)
    othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗
    ([∗ map] ρ ↦ '(f, q) ∈ γ,
       match f with
       | true => (oblG_elem ρ ∗ othreadG_owns i ρ f q ∗ ∃ a, ⌜ /0 /< a ⌝ ∗ oblG_progress ρ a)
       | false => (oblG_elem ρ ∗ othreadG_owns i ρ f q)
       end)
    ⊢ |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | (obl_cond_owner i) ⌝) ∗
                 osat Ω' ∗ othread TP ∗ oforest (dom Ω') ∗
                 othreadG_obls i Ψ 1 ∗
                 ([∗ map] ρ ↦ '(f, q) ∈ γ,
                    match f with
                    | true => (othreadG_owns i ρ f q)
                    | false => (othreadG_owns i ρ f q)
                    end).
  Proof.
    iIntros (?) "(H1&H2&H3&H4&H5&H6)".
    iEval (rewrite /oforest -lock) in "H3". iDestruct "H3" as "(%&F)".
    iMod (oforest_aux_progress_one_thread with "[$]") as "H"; first auto.
    iDestruct "H" as "(%&%&S&T&F&H)". iModIntro. iFrame. rewrite /oforest -lock. by iFrame.
  Qed.

  (* Move a tree *)
  Lemma oforest_aux_transfer_one_tree Ω TP Φ θ k kt π ψ ρ ρt ℵ a b :
    ℵ /< a →
    /0 /< b →
    Φ !! ρ = Some ρt →
    node ρt π →
    Φ !! k = Some kt →
    (∃ d, Ω !! π = Some (obl_live d)) →
    osat Ω ∗ othread TP ∗ osuspend (dom Ω) ∗ oforest_aux (dom Ω) Φ ∗
    (* from user *)
    oblG_elem π ∗ oblG_transfer_bound π ℵ ∗
    othreadG_elem θ ∗ othreadG_owns θ k true (1/2)%Qp ∗
    oblG_elem k ∗ otreeG_elem k ∗ oblG_transfer k a ∗ oblG_transfer k b
    ⊢ |==> ∃ Ω' Φ', (⌜ Ω ↪ₜ Ω' | (obl_cond_in_tree kt) ⌝) ∗
                    osat Ω' ∗ othread TP ∗ osuspend (dom Ω') ∗ oforest_aux (dom Ω') Φ' ∗
                    ∃ x, otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2)%Qp.
  Proof.
    iIntros (LTa LTb LUFρ INπ LUFk LUOπ) "(S & T & Sus & F & #Beπ & #Btbπ & #Teθ & Tok & #Bek & #Fek & Btka & Btkb)".
    iPoseProof (oforest_aux_wf with "F") as "%". destruct H1 as [DomF WFF].
    iPoseProof (oforest_exceed_not_lineage _ _ ρ with "[S F Beπ Btbπ Btka]") as "%Linkπ".
    5: iFrame. all: eauto.
    assert (NEk : k ≠ ρ).
    { intros F; subst. apply Linkπ. destruct WFF. apply tree_wf_node_lineage; eauto. }
    clear Linkπ.
    assert (Nodeρ : node ρt ρ).
    { destruct WFF. apply elem_of_dom, tree_wf_root_elem. auto. }
    iAssert (⌜ ∃ d, Ω !! ρ = Some (obl_live d) ⌝)%I with "[-]" as "%LUOρ".
    { iPoseProof (oforest_tree_live _ _ ρ _ _ ρ with "[S F Beπ]") as "%". 5: iFrame. all: eauto. }
    iDestruct "F" as "(_ & Fetk & FM)".
    iPoseProof (big_sepM_delete _ _ _ _ LUFk with "FM") as "[Fmk FM]".
    assert (LUF'ρ : delete k Φ !! ρ = Some ρt).
    { rewrite lookup_delete_ne; auto. }
    iPoseProof (big_sepM_delete _ _ _ _ LUF'ρ with "FM") as "[Fmρ FM]". destruct INπ as [πC LUtπ].
    assert (WF'F : forest_wf (forest_move_tree Φ ρ ρt k kt π πC)).
    { eapply forest_move_tree_wf; eauto. }
    iAssert (⌜ ∃ d, Ω !! k = Some (obl_live d) ⌝)%I with "[-]" as "%LUOk".
    { iPoseProof (othread_live_open with "[T Teθ Tok]") as "(_&[Live _]&_)"; first by iFrame.
      iPoseProof (osat_obl_is_live _ k with "[S Bek Live]") as "%"; first by iFrame. done. }
    iDestruct "Fmk" as "[Fmk | (_&H1&H2&%)]"; cycle 1.
    { iPoseProof (osat_obl_is_done_weak _ k with "[S H1 H2]") as "%"; first iFrame. destruct LUOk, H2. rewrite H3 in H2. inv H2. }
    iDestruct "Fmρ" as "[Fmρ | (_&H1&H2&%)]"; cycle 1.
    { iPoseProof (osat_obl_is_done_weak _ ρ with "[S H1 H2]") as "%"; first iFrame. destruct LUOρ, H2. rewrite H3 in H2. inv H2. }
    iDestruct "Fmk" as "(%τk & Bok & Tok2 & Fmk)".
    iDestruct "Fmρ" as "(%τρ & Boρ & Toρ & Fmρ)".
    iPoseProof (othread_live_open with "[T Tok]") as "(Tok & [H1 H2] & T)"; first by iFrame.
    iPoseProof (oblG_owner_agree with "[Bok H2]") as "%"; first iFrame.
    iPoseProof ("T" with "[H1 H2]") as "T"; first iFrame. destruct H1 as (Heq&_). subst θ.
    iMod (othread_obl_release_2 with "[T Teθ Tok Tok2]") as "(T & Tok & Tok2 & Bok2)"; first by iFrame.
    (* Frame unrelated trees and some unrelated cases *)
    iAssert (
        |==> ∃ Ω', ⌜ (Ω ↪ₜ Ω' | obl_cond_in_tree kt) ∧ dom Ω' = dom Ω ⌝ ∗
                   osat Ω' ∗ osuspend (dom Ω) ∗
                   (oblG_owner ρ τρ (1/2/2)%Qp ∗ othreadG_owns τρ ρ true (1/2)%Qp ∗
                    ([∗ map] v ↦ vCh ∈ (tree_insert ρt k kt π πC),
                       (own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap tt vCh)))) ∗
                       oblG_elem v ∗ oblG_live v (1/2/2)%Qp ∗ otreeG_elem v ∗
                       (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1/2)%Qp ∗
                               ([∗ set] c ∈ vCh,
                                  ∃ α' β', ⌜ WFOCM.ltR α α' ∧ WFOCM.leR β β' ⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')
                       ) ∗
                       ((⌜ v = ρ ⌝) ∨
                          (∃ p, (⌜ child (tree_insert ρt k kt π πC) p v ⌝) ∗
                                oblG_owner v τρ (1/2)%Qp ∗
                                ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1/2)%Qp ∗
                                     (∃ x y, otreeG_suspend v x θ p y ∗ otreeG_wait v x (1/2)%Qp))))) ∗
                   ∃ x, otreeG_suspend k x τk π ψ ∗ otreeG_wait k x (1/2)%Qp)%I
      with "[S Sus Beπ Btbπ Bek Fek Btka Btkb Bok Fmk Boρ Toρ Fmρ Tok Tok2 Bok2]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%&S&Sus&F&H)". iFrame "H". destruct H1.
      iModIntro. iExists Ω', (forest_move_tree Φ ρ ρt k kt π πC). iSplitR; first done. rewrite !H2.
      iFrame "S T Sus". rewrite /oforest_aux. iSplitR.
      { iPureIntro. split; auto. rewrite forest_fold_move_tree_dom; auto. }
      iFrame "Fetk". iApply big_sepM_insert.
      { apply lookup_delete_eq. }
      iFrame "FM". iLeft. iExists τρ. iFrame. }
    (* Make r a child to π *)
    iPoseProof (big_sepM_delete _ _ _ _ LUtπ with "Fmρ") as "[(Fesπ & _ & Blπ & Feπ & Cπ & Sπ) Fmρ]".
    assert (Disjt : ρt ##ₘ kt) by (destruct WFF; eapply (forest_trees_disjoint_lookup_disjoint _ ρ k ρt kt); eauto).
    assert (Nelemk : k ∉ πC).
    { destruct WFF. assert (πC ⊆ dom ρt) by (eapply tree_wf_children_subseteq; eauto).
      assert (k ∈ dom kt) by (eapply tree_wf_root_elem; eauto).
      assert (k ∉ dom ρt).
      { apply map_disjoint_dom in Disjt. set_solver + Disjt H3 H4. }
      set_solver. }
    assert (Nink : (gset_to_gmap () πC) !! k = None).
    { apply lookup_gset_to_gmap_None; auto. }
    iMod (otreeG_edge_alloc _ _ _ Nink with "Fesπ") as "[Fesπ Feπk]".
    replace (<[k:=()]> (gset_to_gmap () πC)) with (gset_to_gmap () ({[k]} ∪ πC)); cycle 1.
    { apply gset_to_gmap_union_singleton. }
    iMod (osuspend_suspend _ k τk π ψ with "[Sus Fek Tok2 Feπk]") as "(Sus & % & #Fsk & Fwk)"; first by iFrame.
    iPoseProof (otreeG_wait_div_2 with "Fwk") as "[Fwk Fwk2]".
    iCombine "Bok Bok2" as "Bok". iPoseProof (oblG_owner_div_2 with "Bok") as "Bok".
    assert (Chπk : child (tree_insert ρt k kt π πC) π k).
    { exists ({[k]} ∪ πC). split; last set_solver. by rewrite /children /tree_insert lookup_insert_eq. }
    iDestruct "Cπ" as "(%απ & %βπ & #Btbπ2 & Bpsπ & Cπ)".
    assert (is_Some (kt !! k)).
    { apply elem_of_dom. destruct WFF. apply tree_wf_root_elem; auto. }
    destruct H1 as (Ck & LUtk). iPoseProof (big_sepM_delete _ _ _ _ LUtk with "Fmk") as "[(Fesk & _ & Blk & _ & Ck & _) Fmk]".
    iDestruct "Ck" as "(%αk & %βk & #Btbk & Bpsk & Ck)".
    destruct LUOπ as [[oaπ otπ obπ] LUOπ], LUOk as [[oak otk obk] LUOk].
    iMod (osat_obl_transfer_one_with_bound _ k _ _ τρ _ βπ _ b _ _ LUOk LTb with "[S Bok Bpsk Btbk Btkb]")
      as "(%α'k & S & % & Bok & Bpsk & #Btbk' & Bpk)"; first by iFrame.
    destruct H1 as [Progk LTαk]. iCombine "Feπ Fesπ Blπ Bpsπ Cπ Sπ Bpk Btka" as "Fmρπ".
    iPoseProof (osat_transfer_bounds_meet _ π ℵ απ with "[S]") as "(%ℵπ&%LEℵπs&#Btbπ3)"; first (iFrame; eauto).
    set (Ω1 := <[k:=olive α'k τρ (obk /+ βπ)]> Ω).
    iAssert (
        |==> ∃ Ω2, (⌜ (Ω1 ↪ₜ Ω2 | (λ v o, internal kt v)) ∧ dom Ω1 = dom Ω2 ⌝) ∗ osat Ω2 ∗
                   ([∗ map] v ↦ vC ∈ kt,
                      own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vC))) ∗
                      oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
                      (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                              ([∗ set] c ∈ vC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                      (∃ p, ⌜child (tree_insert ρt k kt π πC) p v⌝ ∗ oblG_owner v τρ (1 / 2) ∗
                            ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                                 ∃ x y, otreeG_suspend v x θ p y ∗ otreeG_wait v x (1 / 2)))
      )%I with "[- Boρ Toρ Fmρ Sus Fmρπ Fsk Fwk2]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%Progk2& S & Fmk)". destruct Progk2 as [Progk2 DomO].
      iModIntro. iExists Ω2. iFrame "S Sus Boρ Toρ Fsk Fwk2". iSplitR.
      - iPureIntro. split; auto.
        2:{ rewrite -DomO. subst Ω1. rewrite dom_insert_lookup_L; auto. }
        assert (TWFk : tree_wf k kt) by (destruct WFF; auto).
        assert (Progk1 : Ω ↪ₜ Ω1 | (λ v _, node kt v ∧ root kt v)).
        { intros ?. subst Ω1. destruct (decide (i = k)).
          - subst. rewrite LUOk lookup_insert_eq. econstructor. simpl. split; intros; auto.
            exfalso. apply H1. split; [apply tree_wf_root_node; auto | apply tree_wf_root_root; auto].
          - rewrite lookup_insert_ne; auto. destruct (Ω !! i) eqn:LUOi; econstructor.
            split; intros; auto. destruct H1. eapply tree_wf_root_node_root in H2; eauto. subst; done. }
        eapply obl_states_cond_rel_split_cond. 7: eapply Progk2. 6: eapply Progk1. all: simpl.
        1,2,3: apply _.
        + intros. unfold obl_cond_in_tree. split; intros; auto.
          * pose proof H1. eapply tree_wf_node_root_or_internal in H2; eauto. destruct H2; auto.
          * destruct H1; [destruct H1; auto | eapply tree_wf_internal_node; eauto].
        + intros ?????. auto.
      - assert (Ninπ : kt !! π = None).
        { apply not_elem_of_dom. apply elem_of_dom_2 in LUtπ. apply map_disjoint_dom in Disjt. set_solver + LUtπ Disjt. }
        assert (EQt : tree_insert ρt k kt π πC = <[π:={[k]} ∪ πC]> (kt ∪ (delete π ρt))).
        { rewrite /tree_insert !insert_union_r; auto. f_equal. by rewrite insert_delete_eq. }
        rewrite EQt. iApply (big_sepM_insert _ (kt ∪ delete π ρt)).
        { apply lookup_union_None_2; auto. apply lookup_delete_eq. }
        iSplitL "Fmρπ".
        { iDestruct "Fmρπ" as "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)". iFrame "H1 H2 H3 H4 Beπ". iSplitR "H6".
          - iExists ℵπ. iSplitR; first auto. iApply big_sepS_union.
            { set_solver + Nelemk. }
            rewrite big_sepS_singleton. destruct LEℵπs. iSplitR "H5".
            { iFrame. iPureIntro. split; last done. eapply WFOCM.le_lt_lt; last eauto. auto. }
            iApply (big_sepS_impl with "H5"). iModIntro. iIntros (??) "(%&%&%&A&B)". destruct H4.
            iExists α', β'. iFrame. iPureIntro. split; auto. eapply WFOCM.le_lt_lt; last eapply H4. auto.
          - iDestruct "H6" as "[H | H]"; first by iLeft. iRight. iDestruct "H" as "(%&%&H1&%&H4&H2&%&H3)".
            iExists π0. iFrame. iPureIntro. rewrite -EQt. eapply tree_insert_child; eauto. }
        iApply big_sepM_union.
        { symmetry. apply map_disjoint_delete_l; auto. }
        iSplitR "Fmρ"; cycle 1.
        { iApply (big_sepM_impl with "Fmρ"). iModIntro. iIntros (???) "(H1&H2&H3&H4&H5&H6)". iFrame.
          iDestruct "H6" as "[H | H]"; first by iLeft. iRight. iDestruct "H" as "(%&%&H1&%&H4&H2&%&H3)".
          iExists π0. iFrame. iPureIntro. rewrite -EQt. eapply tree_insert_child; eauto. }
        iApply (big_sepM_impl with "Fmk"). iModIntro. iIntros (???) "(H1&H2&H3&H4&H5&H6)". iFrame. }
    (* Frame solved parts *)
    iAssert (
        ([∗ map] v ↦ vC ∈ delete k kt,
           oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
           (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                   ([∗ set] c ∈ vC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
           oblG_owner v τk (1/2)) ∗
        ([∗ map] v ↦ vC ∈ kt,
           own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vC))) ∗
           ∃ p, ⌜child (tree_insert ρt k kt π πC) p v⌝ ∗
                ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                     ∃ x0 y0, otreeG_suspend v x0 θ p y0 ∗ otreeG_wait v x0 (1 / 2))
      )%I with "[Tok Fwk Fesk Fmk]" as "[Fm H]".
    { rewrite (big_sepM_delete _ kt k _ LUtk). iFrame "Fesk Fsk Fwk Tok Teθ". rewrite bi.sep_comm -bi.sep_assoc.
      iSplitR.
      { iPureIntro. exists ({[k]} ∪ πC). split; last set_solver. by rewrite /children /tree_insert lookup_insert_eq. }
      iApply big_sepM_sep. iApply (big_sepM_impl with "Fmk"). iModIntro. iIntros (???) "(H1 & H2 & H3 & H4 & H6 & [% | H5])".
      { exfalso. subst k0. rewrite lookup_delete_eq in H1. inv H1. }
      iFrame. iDestruct "H5" as "(%&%&H1&%&H4&H2&%&H3)". iFrame. iPureIntro. eapply tree_insert_child; eauto. }
    iAssert (
        |==>
          ∃ Ω2, (⌜Ω1 ↪ₜ Ω2 | (λ (v : obl_id) (_ : obl_state), internal kt v) ∧ dom Ω1 = dom Ω2⌝) ∗ 
                osat Ω2 ∗
                ([∗ map] v↦vC ∈ kt,
                   oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
                   (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                           ([∗ set] c ∈ vC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                   oblG_owner v τρ (1 / 2))
      )%I with "[- H]" as ">A"; cycle 1.
    { iDestruct "A" as "(%&%& S& Fm)". iModIntro. iExists Ω2. iFrame "S". iSplitR; first done.
      iCombine "H Fm" as "Fm". iPoseProof (big_sepM_sep with "Fm") as "M". iApply (big_sepM_impl with "M").
      iModIntro. iIntros (???) "((H1&H2) & (H3&H4&H5&H6&H7))". iFrame. }
    (* Set up first induction on the tree kt - clear any unrelated things *)
    iClear "Beπ Btbπ Btbπ2 Btbπ3 Teθ Fsk Btbk".
    assert (WFt : tree_wf k kt) by (destruct WFF; eauto).
    subst Ω1. remember (<[k:=olive α'k τρ (obk /+ βπ)]> Ω) as Ω1. remember (obk /+ βπ) as β'k.
    clear dependent Ω TP Φ π πC ρ ρt ℵ a b. clear dependent oaπ otπ obπ oak otk obk x απ βπ ℵπ.
    iAssert (
        |==> ([∗ set] c ∈ Ck, ∃ α', ⌜α'k /< α'⌝ ∗ oblG_transfer c α') ∗
             ([∗ set] c ∈ Ck, ∃ u : A, ⌜/0 /< u⌝ ∗ oblG_transfer c u)
      )%I with "[Ck]" as ">[Ck Tsk]".
    { rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "Ck"). iModIntro. iIntros (??) "(%&%&%&T&_)".
      destruct H2. apply WFOCM.lt_exists_left in H2. destruct H2 as (?&?&?).
      iMod (oblG_transfer_mon_split _ _ _ _ H4 with "T") as "[T T1]".
      iModIntro. iSplitL "T"; by iFrame. }
    (* First induction *)
    clear dependent αk βk. iStopProof. revert Ck LUtk α'k β'k Ω1 τk τρ.
    pattern k, kt. revert k kt WFt. apply tree_wf_internal_ind.
    intros ρ ρt WFρt IH1. iIntros (Ck LUρC αρ βρ Ω1 τρ τ) "((#Beρ & #Feρ & #Btbρ) & Blρ & S & Boρ & Bpsρ & M & ρC & Ts)".
    pose proof WFρt. inversion H1. subst ρ0 t. assert (Hρlutree : ρt !! ρ = Some (dom Cf)).
    { subst. by rewrite /forest_merge lookup_insert_eq. }
    iEval (rewrite H2 /forest_merge) in "M". rewrite delete_insert_id; last auto.
    iPoseProof (big_sepM_forest_fold with "M") as "M"; first auto.
    iAssert (
        ([∗ map] v ↦ vt ∈ Cf,
           oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
           ∃ vC, (⌜ vt !! v = Some vC ⌝) ∗
                 (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                         ([∗ set] c ∈ vC, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                 oblG_owner v τρ (1 / 2)) ∗
        ([∗ map] v ↦ vt ∈ Cf,
           [∗ map] v ↦ vC ∈ (delete v vt),
             oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
             (∃ α β : A, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                         ([∗ set] c ∈ vC, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
             oblG_owner v τρ (1 / 2))
      )%I with "[M]" as "[R M]".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "M"). iModIntro. iIntros (???) "H".
      assert (is_Some (x !! k)).
      { apply elem_of_dom. eapply tree_wf_root_elem; eauto. }
      destruct H7. iPoseProof (big_sepM_delete _ _ _ _ H7 with "H") as "[A H]". iFrame.
      iDestruct "A" as "(H1&H2&H3&H4)". iFrame. eauto. }
    rewrite LUρC in Hρlutree. inversion Hρlutree. subst Ck. clear Hρlutree.
    iAssert (
        |==>
          ∃ Ωc, (⌜ Ω1 ↪ₜ Ωc | (λ v _, v ∈ dom Cf) ∧ dom Ω1 = dom Ωc ⌝) ∗
                osat Ωc ∗
                ([∗ map] v↦vt ∈ Cf,
                   oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
                   ∃ vC, ⌜vt !! v = Some vC⌝ ∗
                         (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                                 ([∗ set] c ∈ vC, ∃ α', ⌜α /< α'⌝ ∗ oblG_transfer c α') ∗
                                 ([∗ set] c ∈ vC, ∃ u, ⌜/0 /< u⌝ ∗ oblG_transfer c u)) ∗
                         oblG_owner v τ (1 / 2)) ∗
                ([∗ set] c ∈ dom Cf, ∃ β', ⌜ βρ /≤ β' ⌝ ∗ oblG_progress c β')
      )%I with "[S Ts R]" as ">(%& %& S& R& Ps)".
    { iClear "Beρ Feρ Btbρ". clear dependent αρ ρt ρ. iStopProof. revert H4 H5 Ω1.
      induction Cf using map_ind; iIntros (Disj Twfs Ω1) "(S& Ts& M)".
      { iModIntro. iExists Ω1. rewrite !dom_empty_L. iFrame. iSplitR.
        - iPureIntro. split; auto. intros ?. destruct (Ω1 !! i) eqn:LUOi; econstructor. split; intros; done.
        - by rewrite !big_sepM_empty !big_sepS_empty. }
      rewrite !dom_insert_L.
      apply forest_trees_disjoint_insert in Disj; auto. destruct Disj as [Disjx Disj].
      apply map_Forall_insert in Twfs; auto. destruct Twfs as [Twx Twfs].
      iPoseProof (big_sepS_union with "Ts") as "[T Ts]".
      { apply not_elem_of_dom in H1. set_solver + H1. }
      rewrite big_sepS_singleton.
      iPoseProof (big_sepM_insert with "M") as "[M Ms]"; first auto.
      iDestruct "T" as "(%&%LTu&T)". iDestruct "M" as "(#Bei& Bli& #Fei & % & %LUxi& (%&%&#Btbi&Bpsi&Cs)& Boi)".
      iPoseProof (osat_obl_is_live with "[S Bei Bli]") as "(% & %LUOi)"; first by iFrame. destruct d as [ai ti bi].
      iMod (osat_obl_transfer_one_with_bound _ _ _ _ τ _ βρ _ _ _ _ LUOi LTu with "[S Boi Bpsi T]")
        as "(%& S& %Prog& Boi& Bpsi& #Btbi2& Bpi)"; first by iFrame.
      destruct Prog as [Prog LTα]. iMod (IHCf Disj Twfs with "[S Ts Ms]") as "(%& %Progs& S& Ms& Ps)"; first iFrame.
      destruct Progs as [Progs Dom].
      iAssert (
          |==>
            ([∗ set] c ∈ vC, ∃ α1, ⌜α' /< α1⌝ ∗ oblG_transfer c α1) ∗
            ([∗ set] c ∈ vC, ∃ u, ⌜/0 /< u⌝ ∗ oblG_transfer c u)
        )%I with "[Cs]" as ">Cs".
      { rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "Cs"). iModIntro. iIntros (??) "(%&%&%&T&_)".
        destruct H3. apply WFOCM.lt_exists_left in H3. destruct H3 as (?&?&?).
        iMod (oblG_transfer_mon_split _ _ _ _ H5 with "T") as "[T1 T2]". iModIntro. iSplitL "T1"; by iFrame. }
      iModIntro. iExists Ωc. iSplitR.
      { iPureIntro. split; cycle 1.
        { rewrite -Dom. rewrite dom_insert_lookup_L; auto. }
        assert (Prog1 : Ω1 ↪ₜ <[i:=olive α' τ (bi /+ βρ)]> Ω1 | λ v _, v ∈ ({[i]} : gset obl_id)).
        { intros ?. destruct (decide (i = i0)).
          - subst. rewrite LUOi lookup_insert_eq. econstructor. simpl. split; auto. intros FF. set_solver + FF.
          - rewrite lookup_insert_ne; auto. destruct (Ω1 !! i0) eqn:LUOi1; econstructor.
            split; auto. intros FF. set_solver + n FF. }
        eapply obl_states_cond_rel_split_cond. 7: eapply Progs. 6: eapply Prog1. all: simpl.
        1,2,3: apply _.
        - intros. apply elem_of_union.
        - repeat intro. auto. }
      iFrame "S". iSplitR "Bpi Ps".
      - iApply big_sepM_insert; first auto. iFrame. eauto.
      - iApply big_sepS_union.
        { apply not_elem_of_dom in H1. set_solver +H1. }
        rewrite big_sepS_singleton. iFrame. auto. }
    iAssert (
        |==>
          ∃ Ω2, (⌜ Ωc ↪ₜ Ω2 | (λ v _, forest_node_in_tree_internal Cf v) ∧ dom Ωc = dom Ω2 ⌝) ∗
                osat Ω2 ∗
                ([∗ map] v↦vC ∈ (forest_fold Cf),
                   oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
                   (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                           ([∗ set] c ∈ vC,
                              ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                   oblG_owner v τ (1 / 2))
      )%I with "[M S R]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%Prog2&S&M)". destruct Prog2 as [Prog2 Dom2]. iModIntro. iExists Ω2. iSplitR.
      { destruct H6 as [Prog1 Dom1]. iPureIntro. split; last (by rewrite Dom1 Dom2).
        eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1. all: simpl.
        1,2,3: apply _.
        - intros. rewrite -forest_fold_node_in_tree_root_or_internal; auto.
          subst. eapply forest_merge_internal_forest_fold_node_iff; eauto.
        - repeat intro. auto. }
      iFrame "S". subst. rewrite /forest_merge. iApply big_sepM_insert; first auto.
      iFrame. iSplitR; first auto. iSplitR; first auto. iExists αρ. iSplitR; first auto.
      iCombine "ρC Ps" as "C". rewrite -big_sepS_sep. iApply (big_sepS_impl with "C").
      iModIntro. iIntros (??) "((%&%&T) & (%&%&P))". iFrame. done. }
    (* Second induction *)
    iClear "Beρ Feρ Btbρ".
    assert (HCfsub : map_Forall (λ _ c, c ⊆ ρt) Cf).
    { subst. by apply forest_merge_subseteq_Forall. }
    assert (HCfint : map_Forall (λ v _, internal ρt v) Cf).
    { subst. by apply forest_merge_internal_Forall. }
    clear dependent αρ βρ Ω1. clear LUρC H1 H2 H3. iStopProof. revert H4 H5 HCfsub HCfint Ωc. induction Cf using map_ind.
    { iIntros (Disj Twfs Subs Ints Ωc) "(F & S & C)".
      iModIntro. iExists Ωc. iFrame. rewrite forest_fold_empty. iSplitR; last done. iPureIntro. split; auto.
      intros ?. destruct (Ωc !! i) eqn:LUOi; econstructor. split; auto. intros.
      rewrite /forest_node_in_tree_internal /map_fold_or map_fold_empty in H1. done. }
    iIntros (Disj Twfs Subs Ints Ωc) "(F & S & C)".
    rewrite !forest_fold_insert_L; auto.
    iPoseProof (big_sepM_insert with "F") as "[Fi F]"; first auto.
    iPoseProof (big_sepM_insert with "C") as "[Ci C]"; first auto.
    apply forest_trees_disjoint_insert in Disj; auto. destruct Disj as [Disji Disj].
    apply map_Forall_insert in Twfs; auto. destruct Twfs as [Twfsi Twfs].
    apply map_Forall_insert in Subs; auto. destruct Subs as [Subsi Subs].
    apply map_Forall_insert in Ints; auto. destruct Ints as [Intsi Ints].
    specialize (IHCf Disj Twfs Subs Ints).
    iDestruct "Ci" as "(#Bei& Bli& #Fei& %& %LUxi& Ci& Boi)". specialize (IH1 _ _ Intsi Subsi Twfsi _ LUxi).
    iDestruct "Ci" as "(%&%&#Btbi& Bpsi& Ci)". iMod (IH1 with "[S Fi Bli Bpsi Ci Boi]") as "(%&%Prog& S & Mi)".
    { iFrame. eauto. }
    iMod (IHCf Ω2 with "[F C S]") as "(%Ω3& %Prog3& S& M)"; first iFrame.
    iModIntro. iExists Ω3. iSplitR.
    { iPureIntro. destruct Prog as [Prog1 Dom1], Prog3 as [Prog2 Dom2]. split; last by rewrite Dom1 Dom2.
      eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1. all: simpl.
      1,2,3: apply _.
      - intros. apply forest_node_in_tree_internal_insert; auto.
      - repeat intro. auto. }
    iFrame "S". iApply big_sepM_union.
    { apply tree_disjoint_forest_fold_disjoint; auto. }
    iFrame.
  Qed.

  Lemma oforest_transfer_one_tree Ω TP k θ π ψ ℵ a b :
    ℵ /< a →
    /0 /< b →
    osat Ω ∗ othread TP ∗ osuspend (dom Ω) ∗ oforest (dom Ω) ∗
    (* from user *)
    oblG_elem π ∗ oblG_transfer_bound π ℵ ∗
    othreadG_elem θ ∗ othreadG_owns θ k true (1/2)%Qp ∗
    oblG_elem k ∗ otreeG_elem k ∗ oblG_transfer k a ∗ oblG_transfer k b
    ⊢ (osat Ω ∗ othread TP ∗ osuspend (dom Ω) ∗ oforest (dom Ω) ∗
       othreadG_owns θ k true (1/2)%Qp ∗ oblG_transfer k a ∗ oblG_transfer k b ∗
       oblG_done π) ∨
        (|==> ∃ (C : obl_cond) Ω',
            (⌜ (Ω ↪ₜ Ω' | C) ∧ (∀ k o, (C k o ∨ ¬ C k o)) ⌝) ∗
            osat Ω' ∗ othread TP ∗ osuspend (dom Ω') ∗ oforest (dom Ω') ∗
            ∃ x, otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2)%Qp).
  Proof.
    iIntros (LTa LTb) "(S&T&U&F& #Beπ& #Btbπ& #Teθ& Toθ& #Bek& #Tek& Btka& Btkb)".
    rewrite /oforest -lock. iDestruct "F" as "(%&F)".
    iPoseProof (osat_elem_cases _ π with "[S]") as "[%Liveπ | #Bdπ]"; first by iFrame.
    2:{ iLeft. iFrame. auto. }
    iRight. iPoseProof (oforest_aux_wf with "F") as "%". destruct H1 as [Dom [Disj Twfs]].
    iPoseProof (osat_elem π with "[S]") as "%Inπ"; first by iFrame.
    assert (LUπ : is_Some (forest_fold OForest !! π)).
    { rewrite -Dom in Inπ. apply elem_of_dom in Inπ. auto. }
    destruct LUπ as [Cπ LUπ]. destruct (forest_fold_lookup_Some_exists_root _ _ _ Disj LUπ) as (ρ&ρt&LUρ&LUtπ).
    iPoseProof (oforest_aux_othreadG_owns_true_root _ _ _ _ k with "[S T F Toθ]") as "%LUk"; first (iFrame; auto).
    destruct LUk as [kt LUk].
    iMod (oforest_aux_transfer_one_tree _ _ _ θ k kt π ψ ρ ρt ℵ a b with "[$]") as "H".
    1,2,3,4,5,6: eauto.
    { rewrite /node LUtπ. done. }
    iDestruct "H" as "(%&%&%&S&T&U&F&H)". iModIntro. iFrame. iExists _. iSplitR.
    { iPureIntro. split; first eauto. intros. destruct (decide (node kt k0)); auto. }
    rewrite -lock. iFrame.
  Qed.

  Lemma oforest_aux_resolve_one_1 Ω1 TP ρ τρ (m : forest obl_id) i x :
    (m !! i = None) →
    tree_wf i x →
    oblG_done ρ ∗
    osat Ω1 ∗ osuspend (dom Ω1) ∗ othread TP ∗
    own edge_name (reservation_map_data ρ (gmap_view_auth (DfracOwn 1) (gset_to_gmap () ({[i]} ∪ dom m)))) ∗
    (∃ u, ⌜/0 /< u⌝ ∗ oblG_transfer i u) ∗
    (∃ rC, (⌜x !! i = Some rC⌝) ∗
           own edge_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (gset_to_gmap () rC))) ∗ 
           oblG_elem i ∗ oblG_live i (1 / 2 / 2) ∗ otreeG_elem i ∗
           (∃ α β, oblG_transfer_bound i α ∗ oblG_progress_supply i β (1 / 2) ∗
                   ([∗ set] c ∈ rC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
           oblG_owner i τρ (1 / 2) ∗
           ∃ θ, othreadG_elem θ ∗ othreadG_owns θ i false (1 / 2) ∗
                ∃ x0 ψ, otreeG_suspend i x0 θ ρ ψ ∗ otreeG_wait i x0 (1 / 2)) ∗
    ([∗ map] v↦vC ∈ delete i x,
       own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vC))) ∗
       oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
       (∃ α β , oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                ([∗ set] c ∈ vC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
       ∃ π, ⌜child x π v⌝ ∗ oblG_owner v τρ (1 / 2) ∗
            ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                 ∃ x0 ψ, otreeG_suspend v x0 θ π ψ ∗ otreeG_wait v x0 (1 / 2))
    ⊢ |==> ∃ Ω', (⌜Ω1 ↪ₜ Ω' | (λ (v : obl_id) (_ : obl_state), node x v) ∧ dom Ω1 = dom Ω'⌝) ∗
                 osat Ω' ∗ othread TP ∗ osuspend (dom Ω') ∗
                 own edge_name (reservation_map_data ρ (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom m)))) ∗
                 (∃ τ0, oblG_owner i τ0 (1 / 2 / 2) ∗ othreadG_owns τ0 i true (1 / 2) ∗
                        ([∗ map] v↦vCh ∈ x,
                           own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗
                           oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
                           (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                                   ([∗ set] c ∈ vCh, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                           (⌜v = i⌝
                                 ∨ ∃ π, ⌜child x π v⌝ ∗ oblG_owner v τ0 (1 / 2) ∗
                                        ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                                             ∃ x0 ψ, otreeG_suspend v x0 θ π ψ ∗ otreeG_wait v x0 (1 / 2)))).
  Proof.
    iIntros (LUmi Twfi) "(#Bdρ& S& U& T& Fetkρ& (%&%Posu&Bti)& Ri& Mi)".
    iDestruct "Ri" as "(%& %LUxi& Fetki& #Bei& Bli& #Fei& (%&%&#Btbi&Bpsi&Csi)& Boi& %& #Teθ& Toi& %&%& #Fsi& Fwi)".
    (* First update i: transfer and return from suspend, and remove edge *)
    iPoseProof (osat_obl_is_live with "[S Bei Bli]") as "(%&%LUOi)"; first by iFrame. destruct d as [αi τi βi].
    iMod (osat_obl_transfer_one_with_bound _ _ _ _ θ _ ψ _ _ _ _ LUOi Posu with "[S Boi Bpsi Btbi Bti]")
      as "(%α'i& S& %Prog& Boi& Bpsi& #Btbi2& Bpi)"; first by iFrame. destruct Prog as [Prog LTα].
    iPoseProof (oblG_owner_div_2 _ _ (1/2)%Qp with "Boi") as "[Boi Boi2]".
    iMod (osuspend_done_parent with "[U Fei Fsi Fwi T Teθ Toi Boi2 Bdρ Bpi]") as "(U& Toi& Fedgei& T)"; first (iFrame; eauto).
    iMod (otreeG_edge_delete with "[Fetkρ Fedgei]") as "Fetkρ"; first iFrame.
    replace (delete i (gset_to_gmap () ({[i]} ∪ dom m))) with (gset_to_gmap () (dom m)); cycle 1.
    { rewrite gset_to_gmap_union_singleton delete_insert_id; auto. apply lookup_gset_to_gmap_None, not_elem_of_dom; auto. }
    iFrame "Fetkρ". clear dependent m u. iClear "Bdρ Btbi Fsi". 
    iAssert (|==> ([∗ set] c ∈ rC, ∃ α', ⌜ α'i /< α' ⌝ ∗ oblG_transfer c α') ∗
                  ([∗ set] c ∈ rC, ∃ u, ⌜ /0 /< u ⌝ ∗ oblG_transfer c u))%I with "[Csi]" as ">[Csi Cs]".
    { rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "Csi"). iModIntro. iIntros (??) "(%&%&%&T&_)".
      destruct H2. apply WFOCM.lt_exists_left in H2. destruct H2 as (?&?&?).
      iMod (oblG_transfer_mon_split _ α x2 _ H4 with "T") as "[T T2]". iModIntro. iSplitR "T2"; iFrame; auto. }
    iAssert (
        ([∗ map] v↦vC ∈ delete i x,
           oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
           (∃ α0 β0, oblG_transfer_bound v α0 ∗ oblG_progress_supply v β0 (1 / 2) ∗
                     ([∗ set] c ∈ vC, ∃ α' β', ⌜α0 /< α' ∧ β0 /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
           oblG_owner v τρ (1 / 2)) ∗
        ([∗ map] v↦vC ∈ delete i x,
           own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vC))) ∗
           otreeG_elem v ∗
           ∃ π, ⌜child x π v⌝ ∗
                ∃ θ0, othreadG_elem θ0 ∗ othreadG_owns θ0 v false (1 / 2) ∗
                      ∃ x1 ψ0, otreeG_suspend v x1 θ0 π ψ0 ∗ otreeG_wait v x1 (1 / 2))
      )%I with "[Mi]" as "[Mi Mi2]".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "Mi").
      iModIntro. iIntros (???) "(Fetkk& Bek& Blk& Fek& Ck& (%&%&Bok&M))". iFrame. done. }
    remember (<[i:=olive α'i θ (βi /+ ψ)]> Ω1) as Ωi. remember (βi /+ ψ) as β'i.
    iAssert (
        |==> ∃ Ω', (⌜ Ωi ↪ₜ Ω' | (λ k _, internal x k) ∧ dom Ωi = dom Ω' ⌝) ∗
                   osat Ω' ∗
                   (oblG_progress_supply i β'i (1 / 2) ∗ ([∗ set] c ∈ rC, ∃ β', ⌜β'i /≤ β'⌝ ∗ oblG_progress c β')) ∗
                   ([∗ map] v↦vCh ∈ delete i x,
                      oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
                      (∃ α0 β0, oblG_transfer_bound v α0 ∗ oblG_progress_supply v β0 (1 / 2) ∗
                                ([∗ set] c ∈ vCh, ∃ α' β', ⌜α0 /< α' ∧ β0 /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                      oblG_owner v θ (1 / 2))
      )%I with "[- Fetki Bli Boi U Toi T Csi Mi2]" as "H"; cycle 1.
    { iMod "H" as "(%&%& S& (Bpsi& CBps)& M)". destruct H1 as [Prog2 Dom2]. iModIntro.
      iExists Ω'. assert (Dom1 : dom Ω1 = dom Ωi).
      { subst. rewrite dom_insert_lookup_L; auto. }
      rewrite Dom1 Dom2. iFrame "U T S Boi Toi". iSplitR.
      { iPureIntro. split; last auto.
        assert (Prog1 : Ω1 ↪ₜ Ωi | (λ k _, node x k ∧ root x k)).
        { subst. intros ?. destruct (decide (i0 = i)).
          - subst. rewrite LUOi lookup_insert_eq. econstructor. simpl; split; intros; auto. exfalso. apply H1.
            split; [by eapply tree_wf_root_node | by eapply tree_wf_root_root].
          - rewrite lookup_insert_ne; auto. destruct (Ω1 !! i0); econstructor. split; intros; auto. destruct H1.
            pose proof (tree_wf_root_node_root _ _ _ Twfi H2 H1). done. }
        eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1. all: simpl; auto. 1,2,3: apply _.
        - intros. split; intros.
          + pose proof (tree_wf_node_root_or_internal _ _ _ Twfi H1). destruct H2; auto.
          + destruct H1; [by destruct H1 |]. eapply tree_wf_internal_node; eauto.
        - repeat intro. auto. }
      rewrite (big_sepM_delete _ _ _ _ LUxi). iFrame "Fetki Bli". iSplitR "Mi2 M".
      - iFrame "Bei Fei". iSplitL; last by iLeft. iExists α'i, β'i. iFrame "Btbi2 Bpsi". iCombine "Csi CBps" as "C".
        rewrite -big_sepS_sep. iApply (big_sepS_impl with "C"). iModIntro. iIntros (??) "((%&%&T) & (%&%&P))". iFrame; auto.
      - iCombine "Mi2 M" as "M". rewrite -big_sepM_sep. iApply (big_sepM_impl with "M").
        iModIntro. iIntros (???) "((Fetk& Fe& %& %& %& Te& To& %& %& Fs& Fw) & Be& Bl& C& Bo)". iFrame. iRight. iFrame. auto. }
    (* First induction on tree_wf i x *)
    iClear "Bei Fei Teθ Btbi2". clear dependent TP ρ βi ψ Ω1 α β. clear dependent αi x0 τi α'i.
    rename β'i into βi. iStopProof. revert rC LUxi βi Ωi. pattern i, x. revert i x Twfi. apply tree_wf_internal_ind.
    iIntros (ρ ρt Twfρ IH1 ρC LUtρ βρ Ωρ) "(S& Bpsρ& Btsρ& M)".
    (* Solve ρ by transferring its children, and set up for its children *)
    inversion Twfρ. subst ρ0 t. rewrite H1 /forest_merge lookup_insert_eq in LUtρ. inversion LUtρ. subst ρC. clear LUtρ.
    rewrite H1 /forest_merge delete_insert_id; auto. rewrite big_sepM_forest_fold; auto.
    iAssert (
        ([∗ map] r ↦ rt ∈ Cf,
           ∃ rC, (⌜ rt !! r = Some rC ⌝) ∗
                 oblG_elem r ∗ oblG_live r (1 / 2 / 2) ∗
                 (∃ α0 β0, oblG_transfer_bound r α0 ∗ oblG_progress_supply r β0 (1 / 2) ∗
                           ([∗ set] c ∈ rC, ∃ α' β', ⌜α0 /< α' ∧ β0 /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                 oblG_owner r τρ (1 / 2)) ∗
        ([∗ map] r ↦ rt ∈ Cf,
           [∗ map] v ↦ vC ∈ (delete r rt),
             oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
             (∃ α0 β0, oblG_transfer_bound v α0 ∗ oblG_progress_supply v β0 (1 / 2) ∗
                       ([∗ set] c ∈ vC, ∃ α' β', ⌜α0 /< α' ∧ β0 /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
             oblG_owner v τρ (1 / 2))
      )%I with "[M]" as "[MC M]".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "M"). iModIntro. iIntros (?? LUCk) "M".
      assert (Twfk : tree_wf k x) by auto. assert (is_Some (x !! k)) by (apply elem_of_dom, tree_wf_root_elem; eauto).
      destruct H5 as (Cx&LUxk). iPoseProof (big_sepM_delete _ _ _ _ LUxk with "M") as "[Mk M]".
      iFrame. auto. }
    iAssert (
        |==> ∃ Ω1, (⌜ (Ωρ ↪ₜ Ω1 | λ k _, k ∈ dom Cf) ∧ dom Ωρ = dom Ω1 ⌝) ∗
                   osat Ω1 ∗
                   (oblG_progress_supply ρ βρ (1/2) ∗ ([∗ set] c ∈ dom Cf, ∃ β' : A, ⌜βρ /≤ β'⌝ ∗ oblG_progress c β')) ∗
                   ([∗ map] r↦rt ∈ Cf,
                      ∃ rC, ⌜rt !! r = Some rC⌝ ∗ oblG_elem r ∗ oblG_live r (1 / 2 / 2) ∗
                            (∃ α0 β0, oblG_transfer_bound r α0 ∗ oblG_progress_supply r β0 (1 / 2) ∗
                                      ([∗ set] c ∈ rC, ∃ α', ⌜α0 /< α'⌝ ∗ oblG_transfer c α')) ∗
                            ([∗ set] c ∈ rC, ∃ u, ⌜/0 /< u⌝ ∗ oblG_transfer c u) ∗
                            oblG_owner r θ (1 / 2))
      )%I with "[S Bpsρ Btsρ MC]" as ">H".
    { clear dependent ρt. clear H2. iStopProof. revert H3 H4 ρ βρ Ωρ. induction Cf using map_ind.
      { iIntros (Disj Twfs ρ βρ Ωρ) "(S& Bpsρ& Bts& M)".
        iModIntro. iExists Ωρ. iFrame. rewrite !dom_empty_L. iSplitR; last (iSplitL; done).
        iPureIntro . split; auto. intros ?. destruct (Ωρ !! i); econstructor. split; intros; done. }
      iIntros (Disj Twfs ρ βρ Ωρ) "(S& Bpsρ& Bts& M)".
      apply forest_trees_disjoint_insert in Disj; last auto. destruct Disj as [Disjx Disj].
      apply map_Forall_insert in Twfs; last auto. destruct Twfs as [Twfi Twfs].
      rewrite big_sepM_insert; last auto. rewrite dom_insert_L big_sepS_union.
      2:{ apply not_elem_of_dom in H1. set_solver + H1. }
      rewrite big_sepS_singleton. iDestruct "Bts" as "((%&%LTu&Bti) & Bts)".
      iDestruct "M" as "((%&%LUxi&#Bei&Bli& (%&%&#Btbi&Bpsi&Ci) &Boi) & M)".
      iPoseProof (osat_obl_is_live_olive with "[S Bei Bli]") as "(%&%&%&%LUOi)"; first by iFrame.
      iMod (osat_obl_transfer_one_with_bound _ _ _ _ θ _ βρ _ _ _ _ LUOi LTu with "[S Boi Bpsi Btbi Bti]")
        as "(%αi& S& %Prog& Boi& Bpsi& #Btbi2& Bpi)"; first by iFrame.
      remember (<[i:=olive αi θ (β /+ βρ)]> Ωρ) as Ω'. destruct Prog as [Prog0 LTαi].
      assert (Prog1 : (Ωρ ↪ₜ Ω' | λ k _, k ∈ ({[i]} : gset _))).
      { intros ?. subst. destruct (decide (i = i0)).
        - subst. rewrite LUOi lookup_insert_eq. econstructor. simpl; split; intros; auto. set_solver + H2.
        - rewrite lookup_insert_ne; auto. destruct (Ωρ !! i0); econstructor. split; intros; auto. set_solver + n H2. }
      assert (Dom1 : dom Ωρ = dom Ω').
      { subst. rewrite dom_insert_lookup_L; auto. }
      iMod (IHCf Disj Twfs with "[S Bpsρ Bts M]") as "(%& %Prog2& S& Bpss& M)"; first by iFrame.
      iAssert (|==> ([∗ set] c ∈ rC, ∃ α', ⌜αi /< α'⌝ ∗ oblG_transfer c α') ∗
                    ([∗ set] c ∈ rC, ∃ u, ⌜/0 /< u⌝ ∗ oblG_transfer c u))%I with "[Ci]" as ">[Ci Cui]".
      { rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "Ci"). iModIntro. iIntros (??) "(%&%&%&T&P)".
        destruct H3. apply WFOCM.lt_exists_left in H3. destruct H3 as (?&?&?).
        iMod (oblG_transfer_mon_split _ α0 x1 with "T") as "[T Tu]"; first auto. iModIntro. iSplitL "T"; iFrame; auto. }
      iModIntro. iExists Ω1. iSplitR.
      { iPureIntro. destruct Prog2 as [Prog2 Dom2]. split; last by rewrite Dom1 Dom2.
        eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1. all: simpl. 1,2,3: apply _.
        - intros. apply elem_of_union.
        - repeat intro. auto. }
      rewrite big_sepM_insert; last auto. iClear "Btbi". iFrame "Btbi2". iFrame. iSplitL.
      { iDestruct "Bpss" as "[Bpρ Bps]". iFrame. rewrite big_sepS_union.
        2:{ apply not_elem_of_dom in H1. set_solver + H1. }
        rewrite big_sepS_singleton. iFrame. auto. }
      auto. }
    iDestruct "H" as "(%&%& S& Bpρs& MC)".
    iAssert (
        ([∗ map] r↦rt ∈ Cf,
           ∃ rC, (⌜rt !! r = Some rC⌝) ∗
                 (∃ β0, oblG_progress_supply r β0 (1 / 2)) ∗
                 ([∗ set] c ∈ rC, ∃ u : A, ⌜/0 /< u⌝ ∗ oblG_transfer c u)) ∗
        ([∗ map] r↦rt ∈ Cf,
           ∃ rC, (⌜rt !! r = Some rC⌝) ∗ oblG_elem r ∗ oblG_live r (1 / 2 / 2) ∗
                 (∃ α0, oblG_transfer_bound r α0 ∗ ([∗ set] c ∈ rC, ∃ α' : A, ⌜α0 /< α'⌝ ∗ oblG_transfer c α')) ∗
                 oblG_owner r θ (1 / 2))
      )%I with "[MC]" as "[Cs MC]".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "MC"). iModIntro.
      iIntros (???) "(%&%&Bek&Blk& (%&%&Btbk&Bpsk&Bts) & Cu& Bok)". iFrame. auto. }
    iFrame "Bpρs".
    iAssert (
        |==> ∃ Ω2, (⌜ (Ω1 ↪ₜ Ω2 | λ v _, forest_node_in_tree_internal Cf v ) ∧ dom Ω1 = dom Ω2 ⌝) ∗
                   osat Ω2 ∗
                   ([∗ map] r↦rt ∈ Cf,
                      (∃ rC, (⌜rt !! r = Some rC⌝) ∗
                             ∃ βr, oblG_progress_supply r βr (1/2) ∗ ([∗ set] c ∈ rC, ∃ β', ⌜βr /≤ β'⌝ ∗ oblG_progress c β')) ∗
                      [∗ map] v↦vC ∈ delete r rt,
                        oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
                        (∃ α0 β0, oblG_transfer_bound v α0 ∗ oblG_progress_supply v β0 (1 / 2) ∗
                                  ([∗ set] c ∈ vC, ∃ α' β', ⌜α0 /< α' ∧ β0 /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                        oblG_owner v θ (1/2))
      )%I with "[- MC]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%&S&M)". iModIntro. iExists Ω2. iSplitR.
      { iPureIntro. destruct H5, H6. split; last (by rewrite H7 H8).
        eapply obl_states_cond_rel_split_cond. 7: eapply H6. 6: eapply H5. all: simpl. 1,2,3: apply _.
        - intros. rewrite -forest_fold_node_in_tree_root_or_internal; auto.
          rewrite -forest_merge_internal_forest_fold_node_iff; eauto. all: subst; auto.
        - repeat intro. auto. }
      iFrame "S". rewrite big_sepM_forest_fold; last auto. iCombine "MC M" as "M". rewrite -big_sepM_sep.
      iApply (big_sepM_impl with "M"). iModIntro. iIntros (???) "((%&%&Bek&Blk& (%&Btbk&Ck)& Bok) & (%&%&%&Bpsk&Cpsk)& M)".
      rewrite (big_sepM_delete _ _ _ _ H8). iFrame.
      iCombine "Ck Cpsk" as "Ck". rewrite H8 in H9. inv H9. rewrite -big_sepS_sep.
      iApply (big_sepS_impl with "Ck"). iModIntro. iIntros (??) "((%&%&T) & (%&%&P))". iFrame. auto. }
    (* Second induction on Cf *)
    assert (HCfsub : map_Forall (λ _ c, c ⊆ ρt) Cf).
    { subst. by apply forest_merge_subseteq_Forall. }
    assert (HCfint : map_Forall (λ v _, internal ρt v) Cf).
    { subst. by apply forest_merge_internal_Forall. }
    clear dependent ρ βρ Ωρ. iStopProof. revert H3 H4 HCfsub HCfint Ω1. induction Cf using map_ind.
    { iIntros (Disj Twfs Subs Ints Ω1) "(M& S& C)". iModIntro. iExists Ω1. iSplitR.
      { iPureIntro. split; auto. intros ?. destruct (Ω1 !! i); econstructor. split; intros; auto. done. }
      iFrame. done. }
    iIntros (Disj Twfs Subs Ints Ω1) "(M& S& C)". rewrite !big_sepM_insert. 2,3: auto.
    iDestruct "M" as "(Mi& M)". iDestruct "C" as "((%& %LUxi& (%βi& Bpsi)& Btsi)& C)".
    apply forest_trees_disjoint_insert in Disj; last auto. destruct Disj as [Disjx Disj].
    apply map_Forall_insert in Twfs, Subs, Ints. 2,3,4: auto.
    destruct Twfs as [Twfi Twfs], Subs as [Subx Subs], Ints as [Inti Ints].
    iMod (IH1 _ _ Inti Subx Twfi _ LUxi with "[Mi S Bpsi Btsi]") as "H"; first iFrame.
    clear IH1. iDestruct "H" as "(%Ωi& %Prog1& S& Bpi& Ci)". destruct Prog1 as [Prog1 Dom1].
    iMod (IHCf Disj Twfs Subs Ints _ with "[M S C]") as "H"; first iFrame.
    clear IHCf. iDestruct "H" as "(%Ω2& %Prog2& S& M)". destruct Prog2 as [Prog2 Dom2].
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. split; last by rewrite Dom1 Dom2. eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1.
      all: simpl. 1,2,3: apply _.
      - intros. apply forest_node_in_tree_internal_insert; auto.
      - repeat intro. auto. }
    rewrite big_sepM_insert; last auto. iFrame. auto.
  Qed.

  Lemma oforest_aux_resolve_one Ω TP Φ ρ ρt (σ : ps) P R τ Ψ q :
    Φ !! ρ = Some ρt →
    ρ ∈ Ψ →
    osat Ω ∗ othread TP ∗ osuspend (dom Ω) ∗ oforest_aux (dom Ω) Φ ∗
    (* from user *)
    oblG_goal ρ P R ∗ (⌜ P σ ⌝) ∗ (▷ R) ∗
    othreadG_elem τ ∗ othreadG_obls τ Ψ q ∗ othreadG_owns τ ρ true (1/2)%Qp
    ⊢ |==> ∃ Ωρ Ω' Φ', (⌜ (Ω ↪ᵣ Ωρ @ σ | obl_cond_one ρ) ∧ (Ωρ ↪ₜ Ω' | obl_cond_internal_tree ρt) ⌝) ∗
                       osat Ω' ∗ othread TP ∗ osuspend (dom Ω') ∗ oforest_aux (dom Ω') Φ' ∗
                       oblG_done ρ ∗ othreadG_obls τ (Ψ ∖ {[ρ]}) q.
  Proof.
    iIntros (LUFρ INPρ) "(S& T& U& F& #Bgρ & %Pρ & BR & #Teτ & TΨ & Toρ)".
    iPoseProof (oforest_aux_wf with "F") as "%". destruct H1 as [DomF WFF].
    assert (TWFρ : tree_wf ρ ρt) by (destruct WFF; eauto).
    inversion TWFρ. subst ρ0 t. rename H1 into TWFρ1, H2 into TWFρ2, H3 into TWFρ3, H4 into TWFρ4.
    (* Fix the new forest and frame trees except ρt *)
    iPoseProof (othread_live_open with "[T Toρ]") as "(Toρ & ((Blρ & Boρ) & T))"; first by iFrame.
    iAssert (oblG_elem ρ)%I as "#Beρ".
    { rewrite oblG_elem_unfold. eauto. }
    iPoseProof (osat_obl_is_live with "[S Blρ]") as "%LUOρ"; first by iFrame.
    rewrite /oforest_aux. iDestruct "F" as "(_ & Fetk & FM)".
    iPoseProof (big_sepM_delete _ _ _ _ LUFρ with "FM") as "(Fm & FM)".
    iDestruct "Fm" as "[(%τρ& Boρ2& Toρ2& M) | (_&_&#Bdρ&%)]"; cycle 1.
    { iPoseProof (osat_obl_is_done_weak with "[S]") as "(%&%)"; first (iFrame; eauto).
      destruct LUOρ. rewrite H3 in H2. inv H2. }
    iEval (rewrite TWFρ1 /forest_merge) in "M".
    iPoseProof (big_sepM_insert with "M") as "[Mρ M]"; first auto.
    iDestruct "Mρ" as "(Fedρ& _& Blρ2& #Feρ& Cρ & _)".
    iPoseProof (oblG_owner_agree with "[Boρ Boρ2]") as "%"; first iFrame.
    destruct H1 as [? _]. subst τ.
    iAssert (
        |==>
          ∃ Ωρ Ω', 
            (⌜ Ω ↪ᵣ Ωρ @ σ | obl_cond_one ρ ∧ Ωρ ↪ₜ Ω' | obl_cond_internal_tree ρt ∧ dom Ω = dom Ω' ⌝) ∗
            osat Ω' ∗ othread TP ∗ osuspend (dom Ω') ∗
            oblG_done ρ ∗ othreadG_obls τρ (Ψ ∖ {[ρ]}) q ∗
            own edge_name (reservation_map_data ρ (gmap_view_auth (DfracOwn 1) (gset_to_gmap () ∅))) ∗
            ([∗ map] r↦rt ∈ Cf,
               (∃ τ0, oblG_owner r τ0 (1 / 2 / 2) ∗ othreadG_owns τ0 r true (1 / 2) ∗
                      ([∗ map] v↦vCh ∈ rt,
                         own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗
                         oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
                         (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                                 ([∗ set] c ∈ vCh, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                         (⌜v = r⌝
                               ∨ ∃ π, ⌜child rt π v⌝ ∗ oblG_owner v τ0 (1 / 2) ∗
                                      ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                                           ∃ x ψ, otreeG_suspend v x θ π ψ ∗
                                                  otreeG_wait v x (1 / 2)))))
      )%I with "[- Fetk FM]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%&%& S& T& U& #Bdρ& TΨ& Fedρ& M)". destruct H1 as (?&?&?).
      iModIntro. iExists Ωρ, Ω', (tree_clear Φ ρ Cf). iSplitR; first eauto.
      iFrame "S T U Bdρ TΨ". iSplitR.
      { iPureIntro. subst. split.
        - rewrite -H3 tree_clear_dom; auto.
        - apply tree_clear_wf; auto. }
      iSplitL "Fetk"; first (rewrite -H3; iFrame).
      rewrite /tree_clear /forest_union. rewrite big_sepM_union; cycle 1.
      { rewrite /tree_split /forest_insert. apply map_disjoint_spec. intros.
        destruct (decide (i = ρ)).
        { subst. rewrite lookup_delete_eq in H4. inv H4. }
        rewrite lookup_insert_ne in H5; auto. apply elem_of_dom_2 in H5.
        assert (dom Cf ⊆ dom ρt).
        { subst ρt. eapply forest_merge_dom_forest_subseteq; eauto.
          eapply map_Forall_impl; first eapply TWFρ4. simpl. intros. eapply tree_wf_root_elem; eauto. }
        assert (i ∈ dom ρt) by set_solver + H5 H6.
        rewrite lookup_delete_ne in H4; auto. destruct WFF. assert (tree_wf i x) by eauto.
        assert (i ∈ dom x) by (apply tree_wf_root_elem; eauto).
        assert (ρt ##ₘ x).
        { eapply (forest_trees_disjoint_lookup_disjoint Φ ρ i); eauto. }
        apply map_disjoint_dom in H12. set_solver + H7 H11 H12. }
      iFrame "FM". iApply (big_sepM_insert).
      { assert (dom Cf ⊆ dom (forest_fold Cf)).
        { eapply forest_fold_dom_forest_subseteq; eauto. eapply map_Forall_impl; first eapply TWFρ4.
          intros. apply tree_wf_root_elem; auto. }
        apply not_elem_of_dom in TWFρ2. apply not_elem_of_dom. set_solver + TWFρ2 H4. }
      iSplitR "M".
      - iRight. iFrame. auto.
      - iApply (big_sepM_impl with "M"). iModIntro. iIntros (???) "M". iLeft. iFrame. }
    (* Resolve the root ρ: get Ωρ *)
    iPoseProof ("T" with "[Blρ2 Boρ2]") as "T"; first iFrame.
    iMod (othread_delete_obl_frac _ _ _ _ _ _ INPρ with "[T TΨ Toρ Toρ2]") as "(T& TΨ& Blρ2& Boρ2)".
    { iFrame. iApply othreadG_owns_div_2. iFrame. }
    simpl. iDestruct "Cρ" as "(%αρ& %βρ& _& Bpsρ & Cρ)".
    iMod (osat_obl_resolve_one with "[S BR Blρ Blρ2 Boρ Boρ2 Bpsρ]") as "(S & #Bdρ)".
    { iFrame. iSplitR; first auto.  rewrite -(oblG_live_div_2 _ (1/2)) -(oblG_owner_div_2 _ _ (1/2)). iFrame. }
    remember (<[ρ:=odone P]> Ω) as Ωρ.
    iAssert (
        (* |==> ∃ Ω', (⌜ Ωρ ↪ₜ Ω' | obl_cond_internal_tree ρt ∧ dom Ωρ = dom Ω' ⌝) ∗ *)
        |==> ∃ Ω', (⌜ (Ωρ ↪ₜ Ω' | λ v _, forest_node_in_tree Cf v) ∧ dom Ωρ = dom Ω' ⌝) ∗
                   osat Ω' ∗ othread TP ∗ osuspend (dom Ω') ∗
                   own edge_name (reservation_map_data ρ (gmap_view_auth (DfracOwn 1) (gset_to_gmap () ∅))) ∗
                   ([∗ map] r↦rt ∈ Cf,
                      ∃ τ0, oblG_owner r τ0 (1 / 2 / 2) ∗ othreadG_owns τ0 r true (1 / 2) ∗
                            ([∗ map] v↦vCh ∈ rt,
                               own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗
                               oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
                               (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                                       ([∗ set] c ∈ vCh, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                               (⌜v = r⌝
                                     ∨ ∃ π, ⌜child rt π v⌝ ∗ oblG_owner v τ0 (1 / 2) ∗
                                            ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                                                 ∃ x ψ, otreeG_suspend v x θ π ψ ∗ otreeG_wait v x (1 / 2))))
      )%I with "[- TΨ]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%&S& U& Fetk& M)". iModIntro. iExists Ωρ, Ω'. destruct H1. iSplitR; last iFrame; auto.
      iPureIntro. subst Ωρ. destruct LUOρ. split_and !; auto.
      - intros ?. destruct (decide (i = ρ)).
        + subst. rewrite H3 lookup_insert_eq. econstructor. simpl. split; intros; auto. done.
        + rewrite lookup_insert_ne; auto. destruct (Ω !! i) eqn:LUOi; econstructor. split; intros; auto. done.
      - eapply obl_states_cond_rel_iff; first eauto. simpl. intros. rewrite -forest_fold_node_in_tree; auto.
        rewrite /obl_cond_internal_tree. subst ρt. rewrite forest_merge_internal_forest_fold_node_iff; auto.
      - rewrite -H2. rewrite dom_insert_lookup_L; auto. }
    (* Induction on ρ's children Cf. *)
    iAssert (|==> [∗ set] c ∈ dom Cf, ∃ u, ⌜ /0 /< u ⌝ ∗ oblG_transfer c u)%I with "[Cρ]" as ">Cs".
    { rewrite -big_sepS_bupd. iApply (big_sepS_impl with "Cρ"). iModIntro. iIntros (??) "(%&%&%&T&_)".
      destruct H2. apply WFOCM.lt_exists_left in H2. destruct H2 as (?&?&?).
      iMod (oblG_transfer_mon_split _ _ _ _ H4 with "T") as "[_ T]". iModIntro. iFrame; auto. }
    iPoseProof (big_sepM_forest_fold with "M") as "M"; first auto.
    iAssert (
        ([∗ map] r ↦ rt ∈ Cf,
           ∃ rC, (⌜ rt !! r = Some rC ⌝) ∗
                 own edge_name (reservation_map_data r (gmap_view_auth (DfracOwn 1) (gset_to_gmap () rC))) ∗
                 oblG_elem r ∗ oblG_live r (1 / 2 / 2) ∗ otreeG_elem r ∗
                 (∃ α β, oblG_transfer_bound r α ∗ oblG_progress_supply r β (1 / 2) ∗
                         ([∗ set] c ∈ rC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                 (oblG_owner r τρ (1 / 2) ∗
                       ∃ θ, othreadG_elem θ ∗ othreadG_owns θ r false (1 / 2) ∗
                            ∃ x ψ, otreeG_suspend r x θ ρ ψ ∗ otreeG_wait r x (1 / 2))) ∗
        ([∗ map] r ↦ rt ∈ Cf,
           [∗ map] v ↦ vC ∈ (delete r rt),
             own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vC))) ∗
             oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗ otreeG_elem v ∗
             (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                     ([∗ set] c ∈ vC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
             (∃ π, ⌜child rt π v⌝ ∗ oblG_owner v τρ (1 / 2) ∗
                   ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗
                        ∃ x ψ, otreeG_suspend v x θ π ψ ∗ otreeG_wait v x (1 / 2)))
      )%I with "[M]" as "(Mrs& M)".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "M"). iModIntro. iIntros (???) "M".
      assert (is_Some (x !! k)).
      { apply elem_of_dom, tree_wf_root_elem. eauto. }
      destruct H2. iPoseProof (big_sepM_delete _ _ _ _ H2 with "M") as "[R M]". iSplitL "R".
      - iDestruct "R" as "(Fetk& Bek& Blk& Fek& Cs& R)". iFrame. iDestruct "R" as "[% | (%&%&Bok&%&Teθ&Toθ&%&%&R)]".
        + exfalso. subst k. assert (dom Cf ⊆ dom (forest_fold Cf)).
          { eapply forest_fold_dom_forest_subseteq; eauto. eapply map_Forall_impl; first eapply TWFρ4.
            intros. apply tree_wf_root_elem; auto. }
          apply not_elem_of_dom in TWFρ2. apply elem_of_dom_2 in H1. set_solver + TWFρ2 H1 H3.
        + iFrame. assert (π = ρ).
          { assert (child ρt ρ k).
            { subst. exists (dom Cf). split.
              - by rewrite /children /forest_merge lookup_insert_eq.
              - apply elem_of_dom; auto. }
            subst ρt. pose proof (tree_wf_child_parent_unique _ _ _ _ _ TWFρ H3 H4). auto. }
          subst π. iFrame. auto.
      - iApply (big_sepM_impl with "M"). iModIntro. iIntros (i??) "(Feti& Bei& Bli& Tei& Ci& Mi)". iFrame.
        iDestruct "Mi" as "[% | Mi]".
        + exfalso. subst i. assert (x ⊆ forest_fold Cf) by (by eapply forest_fold_subseteq).
          assert (ρ ∈ dom x).
          { apply elem_of_dom. apply lookup_delete_Some in H3. by destruct H3. }
          apply not_elem_of_dom in TWFρ2. apply subseteq_dom in H4. set_solver + TWFρ2 H4 H5.
        + iDestruct "Mi" as "(%&%&Boi&%&Teθ&Toi&%&%&Fsi&Fwi)". iFrame. iPureIntro.
          subst ρt. assert (π ≠ ρ).
          { intros F; subst. destruct H4 as (?&?&?). rewrite /children lookup_insert_eq in H4. inv H4. destruct (decide (i = k)).
            { subst. rewrite lookup_delete_eq in H3. inv H3. }
            rewrite lookup_delete_ne in H3; auto. apply elem_of_dom in H5. destruct H5.
            assert (dom x ## dom x3).
            { apply map_disjoint_dom. eapply (forest_trees_disjoint_lookup_disjoint _ k i); eauto. }
            assert (i ∈ dom x) by (eapply elem_of_dom; eauto). assert (i ∈ dom x3) by (eapply tree_wf_root_elem; eauto).
            set_solver + H5 H6 H7. }
          eapply forest_merge_child_inv; eauto.
          destruct H4 as (?&?&?). rewrite /children lookup_insert_ne in H4; auto.
          destruct (forest_fold_lookup_Some_exists_root _ _ _ TWFρ3 H4) as (?&?&?&?). assert (x4 = k).
          { destruct (decide (x4 = k)); auto. exfalso. assert (x3 ⊆ dom x5).
            { eapply tree_wf_children_subseteq; eauto. }
            assert (i ∈ dom x5) by (set_solver + H6 H9).
            assert (i ∈ dom x).
            { apply lookup_delete_Some in H3. destruct H3. apply elem_of_dom; eauto. }
            assert (dom x ## dom x5).
            { apply map_disjoint_dom. eapply (forest_trees_disjoint_lookup_disjoint _ k x4); eauto. }
            set_solver + H10 H11 H12. }
          subst x4. rewrite H1 in H7. inv H7. apply elem_of_dom; auto. }
    replace (dom Ω) with (dom Ωρ); cycle 1.
    { subst. destruct LUOρ. rewrite dom_insert_lookup_L; auto. }
    iClear "Bgρ Teτ Beρ Feρ". clear dependent Ω Φ ρt σ P R Ψ q. clear TWFρ2 αρ βρ.
    iStopProof. revert TWFρ3 TWFρ4 Ωρ. induction Cf using map_ind.
    { iIntros (Disj Twfs Ω1) "(#Bdρ& U& Feρ& T& S& TCs& Mrs& M)".
      iModIntro. iExists Ω1. iFrame "U Feρ T S". iSplitR; last done. iPureIntro. split; auto.
      rewrite /forest_node_in_tree /map_fold_or. intros ?. destruct (Ω1 !! i); econstructor. rewrite map_fold_empty. done. }
    iIntros (Disj Twfs Ω1) "(#Bdρ& U& Feρ& T& S& TCs& Mrs& M)".
    (* Make ρ's children roots: transfer to update tid, update suspend state, delete edge *)
    rewrite !dom_insert_L. rewrite !big_sepM_insert; auto. rewrite big_sepS_union; cycle 1.
    { apply not_elem_of_dom in H1. set_solver + H1. }
    iDestruct "Mrs" as "[Ri Mrs]". iDestruct "M" as "[Mi M]". iDestruct "TCs" as "[TCi TCs]". rewrite big_sepS_singleton.
    apply forest_trees_disjoint_insert in Disj; last auto. destruct Disj as [Disjx Disj].
    apply map_Forall_insert in Twfs; last auto. destruct Twfs as [Twfi Twfs].
    (* Solve i first, and use IHCf *)
    iMod (oforest_aux_resolve_one_1 _ _ _ _ _ _ _ H1 Twfi with "[S U T Feρ TCi Ri Mi]") as "H"; first by iFrame.
    iDestruct "H" as "(%Ωi& %Prog1& S& T& U& Fetkρ& Mi)".
    iMod (IHCf Disj Twfs with "[U Fetkρ T S TCs Mrs M]") as "H"; first by iFrame.
    iDestruct "H" as "(%Ω'& %Prog2& S& T& U& Tetkρ& M)".
    destruct Prog1 as [Prog1 Dom1], Prog2 as [Prog2 Dom2]. iModIntro. iExists Ω'. iSplitR.
    { iPureIntro. split; last by rewrite Dom1 Dom2. eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1.
      all: simpl. 1,2,3: apply _.
      - intros. apply forest_node_in_tree_insert; auto.
      - repeat intro. auto. }
    rewrite big_sepM_insert; last auto. iFrame.
  Qed.

  Lemma oforest_resolve_one Ω TP ρ (σ : ps) P R τ Ψ q :
    ρ ∈ Ψ →
    osat Ω ∗ othread TP ∗ osuspend (dom Ω) ∗ oforest (dom Ω) ∗
    (* from user *)
    oblG_goal ρ P R ∗ (⌜ P σ ⌝) ∗ (▷ R) ∗
    othreadG_elem τ ∗ othreadG_obls τ Ψ q ∗ othreadG_owns τ ρ true (1/2)%Qp
    ⊢ |==> ∃ Ωρ (C : obl_cond) Ω',
      (⌜ (Ω ↪ᵣ Ωρ @ σ | obl_cond_one ρ) ∧ (Ωρ ↪ₜ Ω' | C) ⌝) ∗
      osat Ω' ∗ othread TP ∗ osuspend (dom Ω') ∗ oforest (dom Ω') ∗
      oblG_done ρ ∗ othreadG_obls τ (Ψ ∖ {[ρ]}) q.
  Proof.
    iIntros (Inρ) "(S& T& U& F& #Bgρ & %Pρ & BR & #Teτ & TΨ & Toρ)".
    rewrite /oforest -lock. iDestruct "F" as "(%& F)".
    iPoseProof (oforest_aux_othreadG_owns_true_root _ _ _ τ ρ with "[S T F Toρ]") as "%LUρ".
    { iFrame. iSplit; auto. iApply oblG_elem_unfold. eauto. }
    destruct LUρ as [ρt LUρ]. iMod (oforest_aux_resolve_one _ _ _ ρ ρt σ P R τ _ _ LUρ Inρ with "[-]") as "H".
    { iFrame. auto. }
    iDestruct "H" as "(%&%&%&%& S& T& U& F& #Bdρ& Tbs)". destruct H1.
    iModIntro. iExists Ωρ, _, Ω'. iFrame. iSplitR.
    { iPureIntro. eauto. }
    rewrite -lock. iFrame. auto.
  Qed.

  Lemma oforest_aux_done_suspend D Φ k x θ π ψ :
    osuspend D ∗ oforest_aux D Φ ∗
    (* from user *)
    otreeG_elem k ∗ otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2) ∗
    otreeG_elem π ∗ oblG_done π
    ⊢ |==> osuspend D ∗ oforest_aux D Φ ∗ othreadG_owns θ k true (1/2) ∗ oblG_progress k ψ.
  Proof.
    iIntros "(U&F&#Tek&#Tsk&Twk&#Teπ&Bdπ)".
    iPoseProof (osuspend_elem_elem _ k with "[$]") as "%Ink". iPoseProof (osuspend_elem_elem _ π with "[$]") as "%Inπ".
    iPoseProof (osuspend_wait_cases with "[$]") as "[W | W]".
    - iExFalso. iDestruct "W" as "(Twk& Tok& Tedgek& U)".
      rewrite /oforest_aux. iDestruct "F" as "(% & Fetk & FM)". destruct H1 as [Dom WFF].
      assert (LUπ : is_Some ((forest_fold Φ) !! π)).
      { apply elem_of_dom. rewrite Dom. auto. }
      destruct LUπ as [Cπ LUπ]. destruct WFF as [Disj Wfts].
      destruct (forest_fold_lookup_Some_exists_root _ _ _ Disj LUπ) as (ρ&ρt&LUρ&LUtπ).
      iPoseProof (big_sepM_delete _ _ _ _ LUρ with "FM") as "(Fm & _)".
      iDestruct "Fm" as "[(%τρ& Boρ2& Toρ2& M) | (Eρ&#Beρ&#Bdρ&%)]".
      + iPoseProof (big_sepM_delete _ _ _ _ LUtπ with "M") as "[H _]".
        iDestruct "H" as "(_&_&Blπ&_)". by iPoseProof (oblG_live_done_false with "[Blπ Bdπ]") as "%"; first by iFrame.
      + destruct (decide (π = ρ)); cycle 1.
        { subst. rewrite /tree_singleton lookup_singleton_ne in LUtπ; auto. }
        subst π. iPoseProof (otreeG_edge_lookup with "[Eρ Tedgek]") as "%"; first iFrame. done.
    - iMod "W" as "(?&?&?&?)". by iFrame.
  Qed.

  Lemma oforest_done_suspend D k x θ π ψ :
    osuspend D ∗ oforest D ∗
    (* from user *)
    otreeG_elem k ∗ otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2) ∗
    otreeG_elem π ∗ oblG_done π
    ⊢ |==> osuspend D ∗ oforest D ∗ othreadG_owns θ k true (1/2) ∗ oblG_progress k ψ.
  Proof.
    rewrite /oforest -!lock. iIntros "(U&F&#Tek&#Tsk&Twk&#Teπ&Bdπ)".
    iDestruct "F" as "[% F]". iMod (oforest_aux_done_suspend with "[$]") as "H".
    iDestruct "H" as "(U&F&Tok&Bpk)". iModIntro. iFrame.
  Qed.

  Lemma osuspend_wait_cases_many_done D π (κ : gmap obl_id (positive * positive * A)) :
    osuspend D ∗ oforest D ∗
    (* from user *)
    otreeG_elem π ∗ oblG_done π ∗
    ([∗ map] k ↦ '(x, θ, ψ) ∈ κ, otreeG_elem k ∗ otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2))
    ⊢ |==> osuspend D ∗ oforest D ∗
           ([∗ map] k ↦ '(x, θ, ψ) ∈ κ, othreadG_owns θ k true (1/2) ∗ oblG_progress k ψ).
  Proof.
    induction κ using map_ind; iIntros "(U & F & #Feπ & #Bdπ & M)".
    { iFrame. by iModIntro. }
    rewrite !big_sepM_insert; auto. destruct x as [[x θ] ψ]. iDestruct "M" as "((#Fei& #Fsi& Fwi)& M)".
    iMod (IHκ with "[U F M]") as "(U& F& M)"; first (iFrame; eauto).
    iMod (oforest_done_suspend with "[U F Fwi]") as "(U& F& Toi& Bpi)"; first (iFrame; eauto).
    iModIntro. iFrame.
  Qed.

  Lemma oforest_wait_cases_many Ω D π (κ : gmap obl_id (positive * positive * A)) :
    osat Ω ∗ osuspend D ∗ oforest D ∗
    (* from user *)
    oblG_elem π ∗ otreeG_elem π ∗
    ([∗ map] k ↦ '(x, θ, ψ) ∈ κ, otreeG_elem k ∗ otreeG_suspend k x θ π ψ ∗ otreeG_wait k x (1/2))
    ⊢ |==> osat Ω ∗ oforest D ∗
           ((([∗ map] k ↦ '(x, θ, ψ) ∈ κ, otreeG_wait k x (1/2)) ∗
             ([∗ map] k ↦ '(x, θ, ψ) ∈ κ, othreadG_owns θ k false (1/2) ∗ otreeG_edge π k 1) ∗
             (([∗ map] k ↦ '(x, θ, ψ) ∈ κ, othreadG_owns θ k false (1/2) ∗ otreeG_edge π k 1) -∗ osuspend D)) ∨
              (osuspend D ∗ oblG_done π ∗ ([∗ map] k ↦ '(x, θ, ψ) ∈ κ, othreadG_owns θ k true (1/2) ∗ oblG_progress k ψ))).
  Proof.
    iIntros "(S& U& F& #Beπ& #Feπ& M)". iPoseProof (osat_elem_cases with "[S]") as "[% | #Bdπ]"; first (iFrame; eauto).
    - iPoseProof (osuspend_wait_cases_many_live _ _ _ _ H1 with "[S U M]") as "[S M]"; first by iFrame.
      by iFrame.
    - iMod (osuspend_wait_cases_many_done with "[U F M]") as "(U& F& M)"; first (iFrame; eauto).
      iFrame. iModIntro. iRight. by iFrame.
  Qed.

  (* Convert a transfer credit to progress credits *)
  Lemma oforest_aux_get_progress_one Ω TP Φ θ k kt a ψ :
    /0 /< a →
    Φ !! k = Some kt →
    osat Ω ∗ othread TP ∗ oforest_aux (dom Ω) Φ ∗
    (* from user *)
    othreadG_elem θ ∗ othreadG_owns θ k true (1/2)%Qp ∗
    oblG_elem k ∗ oblG_transfer k a
    ⊢ |==> ∃ Ω' Φ', (⌜ Ω ↪ₜ Ω' | (obl_cond_in_tree kt) ⌝) ∗
                    osat Ω' ∗ othread TP ∗ oforest_aux (dom Ω') Φ' ∗
                    othreadG_owns θ k true (1/2)%Qp ∗ oblG_progress k ψ.
  Proof.
    iIntros (LTa LUFk) "(S & T & F & #Teθ & Tok & #Bek &  Btka)".
    iPoseProof (oforest_aux_wf with "F") as "%". destruct H1 as [DomF WFF].
    iDestruct "F" as "(_ & Fetk & FM)".
    iPoseProof (big_sepM_delete _ _ _ _ LUFk with "FM") as "[Fmk FM]".
    iAssert (⌜ ∃ d, Ω !! k = Some (obl_live d) ⌝)%I with "[-]" as "%LUOk".
    { iPoseProof (othread_live_open with "[T Teθ Tok]") as "(_&[Live _]&_)"; first by iFrame.
      iPoseProof (osat_obl_is_live _ k with "[S Bek Live]") as "%"; first by iFrame. done. }
    iDestruct "Fmk" as "[Fmk | (_&H1&H2&%)]"; cycle 1.
    { iPoseProof (osat_obl_is_done_weak _ k with "[S H1 H2]") as "%"; first iFrame. destruct LUOk, H2. rewrite H3 in H2. inv H2. }
    iDestruct "Fmk" as "(%τk & Bok & Tok2 & Fmk)".
    iPoseProof (othread_live_open with "[T Tok]") as "(Tok & [H1 H2] & T)"; first by iFrame.
    iPoseProof (oblG_owner_agree with "[Bok H2]") as "%"; first iFrame.
    iPoseProof ("T" with "[H1 H2]") as "T"; first iFrame. destruct H1 as (Heq&_). subst θ.
    (* Set up first induction on the tree kt - clear any unrelated things *)
    iAssert (
        ([∗ map] v↦vCh ∈ kt,
           oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
           (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                   ([∗ set] c ∈ vCh, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'))) ∗
        ([∗ map] v↦vCh ∈ kt,
           own edge_name (reservation_map_data v (gmap_view_auth (DfracOwn 1) (gset_to_gmap () vCh))) ∗
           otreeG_elem v ∗
           (⌜v = k⌝ ∨ ∃ π, ⌜child kt π v⌝ ∗ oblG_owner v τk (1 / 2) ∗ ∃ θ, othreadG_elem θ ∗ othreadG_owns θ v false (1 / 2) ∗ ∃ x ψ0, otreeG_suspend v x θ π ψ0 ∗ otreeG_wait v x (1 / 2))))%I
      with "[Fmk]" as "[Fmk Fmk2]".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "Fmk"). iIntros "!>" (???) "(Fed& Be& Bl& Fe& Cs& D)". iFrame. }
    iAssert (
        |==> ∃ Ω', ⌜ (Ω ↪ₜ Ω' | obl_cond_in_tree kt) ∧ dom Ω' = dom Ω ⌝ ∗
                   osat Ω' ∗
                   ([∗ map] v ↦ vCh ∈ kt,
                      oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
                      (∃ α β : A, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                                  ([∗ set] c ∈ vCh, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'))) ∗
                   oblG_progress k ψ)%I
      with "[S Btka Fmk]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%& S& Mk& Bpk)". iFrame "Tok2 Bpk". destruct H1.
      iModIntro. iExists Ω', Φ. iSplitR; first done. iFrame. rewrite !H2.
      rewrite /oforest_aux. iSplitR; first auto.
      iFrame "Fetk". iApply (big_sepM_delete _ _ _ _ LUFk).
      iFrame "FM". iLeft. iExists τk. iFrame. iPoseProof (big_sepM_sep with "[Fmk2 Mk]") as "M"; first iFrame.
      iApply (big_sepM_impl with "M"). iIntros "!>" (???) "((Be& Bl& C)& H)". iFrame. iFrame. }
    assert (Twf : tree_wf k kt) by (destruct WFF; eauto).
    assert (LUtk : is_Some (kt !! k)) by (eapply elem_of_dom, tree_wf_root_elem; eauto).
    destruct LUtk as [Ck LUtk]. iClear "Teθ Bek". clear dependent Φ TP τk. clear LUOk.
    iPoseProof (big_sepM_delete _ _ _ _ LUtk with "Fmk") as "[(#Bek& Blk& %ak& %bk& #Btbk& Bpsk& Ck) M]".
    (* iAssert ( *)
    (*     ([∗ set] c ∈ Ck, ∃ a', ⌜ak /< a'⌝ ∗ oblG_transfer c a') ∗ *)
    (*     ([∗ set] c ∈ Ck, ∃ b', ⌜bk /≤ b'⌝ ∗ oblG_progress c b') *)
    (*   )%I with "[Ck]" as "[Ck Ckp]". *)
    (* { rewrite -big_sepS_sep. iApply (big_sepS_impl with "Ck"). iIntros "!>" (??) "(%&%&%& T& P)". iFrame. auto. } *)
    iAssert (
        |==>
          ∃ Ω', (⌜Ω ↪ₜ Ω' | obl_cond_in_tree kt ∧ dom Ω' = dom Ω⌝) ∗ osat Ω' ∗
                oblG_live k (1/2/2)%Qp ∗ oblG_progress k ψ ∗
                (∃ α β, oblG_transfer_bound k α ∗ oblG_progress_supply k β (1 / 2) ∗
                        ([∗ set] c ∈ Ck, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                ([∗ map] v↦vCh ∈ (delete k kt),
                   oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
                   ∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                          ([∗ set] c ∈ vCh, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')))%I
      with "[-]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%& S& Blk& Bpk& Ck& M)". iModIntro. iExists Ω'. iSplitR; first auto.
      iFrame. iApply (big_sepM_delete _ _ _ _ LUtk). iFrame. auto. }
    (* First induction *)
    iStopProof. revert Ck LUtk ak bk ψ a LTa Ω.
    pattern k, kt. revert k kt Twf. apply tree_wf_internal_ind.
    intros ρ ρt WFρt IH1. iIntros (Ck LUtk ak bk ψ a LTa Ω) "((#Beρ& #Btbρ)& S& Btρ& Blρ& Bpsρ& Cρ& M)".
    pose proof WFρt. inversion H1. subst ρ0 t. assert (Hρlutree : ρt !! ρ = Some (dom Cf)).
    { subst. by rewrite /forest_merge lookup_insert_eq. }
    rewrite LUtk in Hρlutree. inversion Hρlutree. subst Ck. clear Hρlutree.
    iEval (rewrite H2 /forest_merge) in "M". rewrite delete_insert_id; last auto.
    iPoseProof (big_sepM_forest_fold with "M") as "M"; first auto.
    iAssert (
        ([∗ map] v ↦ vt ∈ Cf,
           oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
           ∃ vC, (⌜ vt !! v = Some vC ⌝) ∗
                 (∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                         ([∗ set] c ∈ vC, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'))) ∗
        ([∗ map] v ↦ vt ∈ Cf,
           [∗ map] v ↦ vC ∈ (delete v vt),
             oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
             (∃ α β : A, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                         ([∗ set] c ∈ vC, ∃ α' β' : A, ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')))
      )%I with "[M]" as "[R M]".
    { rewrite -big_sepM_sep. iApply (big_sepM_impl with "M"). iIntros "!>" (???) "H".
      assert (is_Some (x !! k)).
      { apply elem_of_dom. eapply tree_wf_root_elem; eauto. }
      destruct H7. iPoseProof (big_sepM_delete _ _ _ _ H7 with "H") as "[A H]". iFrame.
      iDestruct "A" as "(H1&H2&H3)". iFrame. eauto. }
    iPoseProof (osat_obl_is_live with "[S Blρ]") as "(% & %LUOρ)"; first by iFrame. destruct d as [aρ tρ bρ].
    iMod (osat_obl_transfer_one_with_bound_stay _ ρ _ _ _ ψ ak a _ LUOρ LTa with "[S Bpsρ Btρ]")
      as "(%& S& %Prog& Bpsρ& #Btbρ2& Bpρ)"; first by iFrame.
    destruct Prog as [Prog LTak].
    iAssert (
        |==>
          ([∗ set] c ∈ dom Cf, ∃ α1, ⌜α' /< α1⌝ ∗ oblG_transfer c α1) ∗
          ([∗ set] c ∈ dom Cf, ∃ u, ⌜/0 /< u⌝ ∗ oblG_transfer c u)
      )%I with "[Cρ]" as ">[Cρ Cs]".
    { rewrite -big_sepS_sep -big_sepS_bupd. iApply (big_sepS_impl with "Cρ").
      iModIntro. iIntros (??) "(%&%&%&T&_)". destruct H7. apply WFOCM.lt_exists_left in H7. destruct H7 as (?&?&?).
      iMod (oblG_transfer_mon_split _ _ _ _ H9 with "T") as "[T1 T2]". iModIntro. iSplitL "T1"; by iFrame. }
    rename α' into αρ. remember (bρ /+ ψ) as βρ. clear Heqβρ. remember (<[ρ:=olive αρ tρ βρ]> Ω) as Ω1.
    iAssert (
        |==> ∃ Ω2, (⌜Ω1 ↪ₜ Ω2 | (λ v _, node (forest_fold Cf) v) ∧ dom Ω2 = dom Ω1⌝) ∗ osat Ω2 ∗
                   ([∗ set] c ∈ dom Cf, ∃ β', ⌜βρ /≤ β'⌝ ∗ oblG_progress c β') ∗
                   ([∗ map] v↦vt ∈ Cf,
                      oblG_elem v ∗ oblG_live v (1 / 2 / 2) ∗
                      ∃ vC, ⌜vt !! v = Some vC⌝ ∗
                            ∃ α β, oblG_transfer_bound v α ∗ oblG_progress_supply v β (1 / 2) ∗
                                   ([∗ set] c ∈ vC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β')) ∗
                   ([∗ map] v↦vt ∈ Cf,
                      [∗ map] v0↦vC ∈ delete v vt,
                        oblG_elem v0 ∗ oblG_live v0 (1 / 2 / 2) ∗
                        ∃ α β, oblG_transfer_bound v0 α ∗ oblG_progress_supply v0 β (1 / 2) ∗
                               ([∗ set] c ∈ vC, ∃ α' β', ⌜α /< α' ∧ β /≤ β'⌝ ∗ oblG_transfer c α' ∗ oblG_progress c β'))
      )%I with "[- Blρ Bpsρ Bpρ Cρ]" as "H"; cycle 1.
    { iMod "H" as "(%&%& S& Bps& R& M)". iModIntro. iExists Ω2. iSplitR.
      { iPureIntro. destruct H6 as [Prog2 Dom]. split; cycle 1.
        { rewrite Dom. subst. rewrite dom_insert_lookup_L; auto. }
        assert (Prog1 : Ω ↪ₜ Ω1 | λ v _, v ∈ ({[ρ]} : gset obl_id)).
        { subst. intros ?. destruct (decide (ρ = i)).
          - subst. rewrite LUOρ lookup_insert_eq. econstructor. simpl. split; auto. intros FF. set_solver + FF.
          - rewrite lookup_insert_ne; auto. destruct (Ω !! i) eqn:LUOi1; econstructor.
            split; auto. intros FF. set_solver + n FF. }
        eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1. all: simpl.
        1,2,3: apply _.
        - intros. rewrite /obl_cond_in_tree. subst. rewrite /node -!elem_of_dom /forest_merge dom_insert_L. apply elem_of_union.
        - repeat intro. auto. }
      iFrame. iSplitR "R M".
      - iExists αρ. iSplitR; first auto. iPoseProof (big_sepS_sep with "[Cρ Bps]") as "C"; first iFrame.
        iApply (big_sepS_impl with "C"). iIntros "!>" (??) "((%&%&P)& (%&%&T))". iFrame. auto.
      - subst. rewrite /forest_merge delete_insert_id; last auto. iApply big_sepM_forest_fold; first auto.
        iPoseProof (big_sepM_sep with "[R M]") as "M"; first iFrame. iApply (big_sepM_impl with "M").
        iIntros "!>" (???) "(M& (Bek& Blk& %& %& %& %& Btbk& Bpsk& C))".
        iApply (big_sepM_delete _ _ _ _ H7). iFrame. }
    (* Second induction *)
    assert (HCfsub : map_Forall (λ _ c, c ⊆ ρt) Cf).
    { subst. by apply forest_merge_subseteq_Forall. }
    assert (HCfint : map_Forall (λ v _, internal ρt v) Cf).
    { subst. by apply forest_merge_internal_Forall. }
    iClear "Beρ Btbρ Btbρ2". clear dependent Ω. clear dependent ak bk ψ a aρ tρ bρ αρ. rename βρ into ψ.
    clear LUtk H1 H2 H3. iStopProof. revert H4 H5 HCfsub HCfint ψ Ω1.
    induction Cf using map_ind; iIntros (Disj Twfs Subs Ints ψ Ωc) "(M& F& S& C)".
    { iModIntro. iExists Ωc. iFrame. rewrite forest_fold_empty dom_empty_L. iSplitR; last done. iPureIntro.
      split; auto. intros ?. destruct (Ωc !! i) eqn:LUOi; econstructor. split; auto. intros.
      apply elem_of_dom in H1. done. }
    rewrite !forest_fold_insert_L; auto.
    iPoseProof (big_sepM_insert with "M") as "[Mi M]"; first auto.
    iPoseProof (big_sepM_insert with "F") as "[Fi F]"; first auto.
    rewrite !dom_insert_L. iPoseProof (big_sepS_union with "C") as "[Ci C]".
    { apply not_elem_of_dom in H1. set_solver + H1. }
    rewrite big_sepS_singleton.
    apply forest_trees_disjoint_insert in Disj; auto. destruct Disj as [Disji Disj].
    apply map_Forall_insert in Twfs; auto. destruct Twfs as [Twfsi Twfs].
    apply map_Forall_insert in Subs; auto. destruct Subs as [Subsi Subs].
    apply map_Forall_insert in Ints; auto. destruct Ints as [Intsi Ints].
    specialize (IHCf Disj Twfs Subs Ints).
    iDestruct "Ci" as "(%& %LTu& Bti)".
    iDestruct "Mi" as "(#Bei& Bli& %& %LUxi& %&%& #Btbi& Bpsi& Chi)".
    iMod (IH1 i x Intsi Subsi Twfsi _ LUxi α β ψ u LTu Ωc with "[S Bli Bpsi Chi Fi Bti]")
      as "(%Ωi& %Progi& S& Bli& Bpi& Chi& Fi)"; first (iFrame; eauto).
    clear IH1. iMod (IHCf ψ Ωi with "[M F S C]") as "(%& %Prog2& S& Bps& M& F)"; first iFrame.
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. destruct Progi as [Prog1 Dom1], Prog2 as [Prog2 Dom2]. split; last by rewrite -Dom1 Dom2.
      eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1. all: simpl.
      1,2,3: apply _.
      - intros. rewrite /obl_cond_in_tree /node -!elem_of_dom dom_union_L. apply elem_of_union.
      - repeat intro. auto. }
    iFrame "S". rewrite !big_sepM_insert; auto. iFrame. iSplitL; last auto.
    iApply big_sepS_union.
    { apply not_elem_of_dom in H1. set_solver + H1. }
    rewrite big_sepS_singleton. iFrame. auto.
  Qed.

  Lemma oforest_get_progress_one Ω TP θ k a ψ :
    /0 /< a →
    osat Ω ∗ othread TP ∗ oforest (dom Ω) ∗
    (* from user *)
    othreadG_elem θ ∗ othreadG_owns θ k true (1/2)%Qp ∗
    oblG_elem k ∗ oblG_transfer k a
    ⊢ |==> ∃ (C : obl_cond) Ω', (⌜ Ω ↪ₜ Ω' | C ∧ (∀ k o, (C k o ∨ ¬ C k o)) ⌝) ∗
                                osat Ω' ∗ othread TP ∗ oforest (dom Ω') ∗
                                othreadG_owns θ k true (1/2)%Qp ∗ oblG_progress k ψ.
  Proof.
    iIntros (LTa) "(S & T & F & #Teθ & Tok & #Bek &  Btka)".
    rewrite /oforest -lock. iDestruct "F" as "[% F]".
    iPoseProof (oforest_aux_wf with "F") as "%". destruct H1 as [Dom Fwf].
    iPoseProof (oforest_aux_othreadG_owns_true_root _ _ _ _ k with "[S T F Tok]") as "%LUk"; first (iFrame; auto).
    destruct LUk as [kt LUk].
    iMod (oforest_aux_get_progress_one _ _ _ _ _ _ _ ψ LTa LUk with "[$]") as "(%&%&%& S& T& F& Tok& Bpk)".
    iModIntro. iExists _, Ω'. iSplitR.
    { iPureIntro. split; first eauto. intros. destruct (decide (node kt k0)); auto. }
    rewrite -lock. iFrame.
  Qed.

End otree.

(* Allocation of an initial oforest protocol. *)
Definition oforest_alloc `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS A Σ} :
  ⊢ |==> ∃ _ : otreeGS A Σ, osuspend ∅ ∗ oforest ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=gmap_viewR obl_id unitUR) ⊤)) as (γE) "HE";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=gmap_viewR positive (agreeR (prodO (prodO positiveO obl_idO) (leibnizO A)))) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=reservation_mapUR mono_natUR) ⊤)) as (γW) "HW";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR obl_id unitUR)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OtreeG SI A _ _ γE γS γW γI).
  rewrite /oforest /osuspend -!lock /oforest_aux.
  iSplitR "HE".
  - iExists ∅.
    replace (⊤ ∖ gset_to_coPset (∅ : gset obl_id)) with (⊤ : coPset); [| set_solver].
    replace (gset_to_gmap () ∅) with (∅ : gmap obl_id unit); [| set_solver].
    iFrame. iSplitR; done.
  - iExists ∅.
    replace (⊤ ∖ gset_to_coPset (∅ : gset obl_id)) with (⊤ : coPset); [| set_solver].
    iFrame. iSplitR; done.
Qed.
