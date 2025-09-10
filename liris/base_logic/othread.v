From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.base_logic Require Import osat.

(** The ghost state for thread obligations *)
Module othreadGS.

  (* Assumes thread ids are positive *)
  Class othreadGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadGpreS {
        othreadGpreS_status : inG Σ (reservation_mapUR (gmap_viewR obl_id (agreeR (leibnizO bool))));
        othreadGpreS_obls : inG Σ (gmap_viewR positive (gset_disjUR obl_id));
        othreadGpreS_exec : inG Σ (reservation_mapUR mono_natUR);
        othreadGpreS_elem : inG Σ (gmap_viewR positive unitUR);
      }.

  Class othreadGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadG {
        othread_inG : othreadGpreS Σ;
        status_name : gname;
        obls_name : gname;
        exec_name : gname;
        elem_name : gname;
      }.

  Definition othreadΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR obl_id (agreeR (leibnizO bool))));
      GFunctor (gmap_viewR positive (gset_disjUR obl_id));
      GFunctor (reservation_mapUR mono_natUR);
      GFunctor (gmap_viewR positive unitUR)
      ].

  Global Instance subG_othreadΣ `{SI : indexT} {Σ} : subG (othreadΣ) Σ → (othreadGpreS Σ).
  Proof. solve_inG. Qed.

End othreadGS.
Import othreadGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances othread_inG
  othreadGpreS_status othreadGpreS_obls othreadGpreS_exec othreadGpreS_elem.

(* States: thread currently has this obl or not *)
Definition othreadG_owns `{SI : indexT} `{!othreadGS Σ} (i : positive) (k : obl_id) (f : bool) (q : Qp) : iProp Σ :=
  own status_name (reservation_map_data i (gmap_view_frag k (DfracOwn q) (to_agree $ f))).
Global Typeclasses Opaque othreadG_owns.
Global Instance: Params (@othreadG_owns) 5 := {}.

(* Thread: live obligations that this thread knows, also fix to empty when thread terminates *)
Definition othreadG_obls `{SI : indexT} `{!othreadGS Σ} (i : positive) (Ψ : gset obl_id) (q : Qp) : iProp Σ :=
  own obls_name (gmap_view_frag i (DfracOwn q) (GSet Ψ)).
Global Typeclasses Opaque othreadG_obls.
Global Instance: Params (@othreadG_obls) 4 := {}.

(* Exec: tracks whether thread is executing or terminated *)
Definition othreadG_exec `{SI : indexT} `{!othreadGS Σ} (i : positive) (q : Qp) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN{#q} 0)).
Global Typeclasses Opaque othreadG_exec.
Global Instance: Params (@othreadG_exec) 4 := {}.

Definition othreadG_term_auth `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN 1)).
Global Typeclasses Opaque othreadG_term_auth.
Global Instance: Params (@othreadG_term_auth) 4 := {}.

Definition othreadG_term `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (◯MN 1)).
Global Typeclasses Opaque othreadG_term.
Global Instance: Params (@othreadG_term) 4 := {}.

(* Elem: keeps the fact that a key is inside a map *)
Definition othreadG_elem `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own elem_name (gmap_view_frag i DfracDiscarded ()).
Global Typeclasses Opaque othreadG_elem.
Global Instance: Params (@othreadG_elem) 4 := {}.

(* Global invariant for the thread obligations state. *)
Definition othread `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (OThread : gmap positive (gmap obl_id bool)),
        (⌜ dom OThread = TP ⌝) ∗
        (own status_name (reservation_map_token (A:=gmap_viewR obl_id (agreeR (leibnizO bool))) (⊤ ∖ gset_to_coPset TP))) ∗
        (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset TP))) ∗
        (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
        (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> OThread))) ∗
        ([∗ map] i ↦ OObls ∈ OThread,
           (othreadG_exec i (1/2)%Qp ∨ (othreadG_term_auth i ∗ othreadG_obls i ∅ 1)) ∗
           (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
           ([∗ map] k ↦ f ∈ OObls, oblG_live k (1/2/2)%Qp ∗
                                    (match f with | true => oblG_owner k i (1/2/2)%Qp | _ => emp end))
        )
    )%I.

Section othread.
  Context `{SI : indexT} `{WFA : WFOCM.pack A}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS Σ}.
  Context `{Ξ : obl_class A ps positive WFOCM.ltR}.

  Global Instance othreadG_term_persistent i : Persistent (othreadG_term i).
  Proof. rewrite /othreadG_term. apply _. Qed.
  Global Instance othreadG_elem_persistent i : Persistent (othreadG_elem i).
  Proof. rewrite /othreadG_elem. apply _. Qed.

  (** Elem rules *)
  Lemma othreadG_elem_alloc (OThread : gmap positive (gmap obl_id bool)) i M :
    OThread !! i = None →
    (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> OThread)))
    ⊢  |==> (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> (<[i:=M]>OThread)))) ∗
            othreadG_elem i.
  Proof.
    iIntros (Hi) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracDiscarded) ()); try done.
      rewrite !lookup_fmap Hi. done.
    }
    iDestruct "H" as "[H He]". rewrite /othreadG_elem. iFrame "He".
    rewrite fmap_insert. done.
  Qed.

  Lemma othreadG_elem_elem i (OThread : gmap positive (gmap obl_id bool)) :
    (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> OThread))) ∗
    othreadG_elem i
    ⊢ ⌜ i ∈ dom OThread ⌝.
  Proof.
    rewrite /othreadG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro. apply elem_of_dom_2 in H0. by rewrite dom_fmap_L in H0.
  Qed.

  (** Status rules *)
  Lemma othreadG_owns_alloc_map D i :
    i ∉ D →
    (own status_name (reservation_map_token (A:=gmap_viewR obl_id (agreeR (leibnizO bool))) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own status_name (reservation_map_token (A:=gmap_viewR obl_id (agreeR (leibnizO bool))) (⊤ ∖ gset_to_coPset ({[i]} ∪ D)))) ∗
           (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap obl_id bool))))).
  Proof.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap obl_id bool))) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma othreadG_owns_alloc i (OObls : gmap obl_id bool) k (f : bool) :
    OObls !! k = None →
    (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls))))
    ⊢ |==> (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (<[k := f]>OObls))))) ∗
           othreadG_owns i k f 1.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ k (DfracOwn 1) (to_agree $ f)); try done.
      rewrite !lookup_fmap Hk. done.
    }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]".
    rewrite /othreadG_owns. iFrame "Ho".
    rewrite fmap_insert. done.
  Qed.
  Lemma othreadG_owns_delete i (OObls : gmap obl_id bool) k (f : bool) :
    (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
    othreadG_owns i k f 1
    ⊢ |==> (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (delete k OObls))))).
  Proof.
    rewrite -own_op -reservation_map_data_op. apply own_update, reservation_map_update.
    rewrite fmap_delete. apply gmap_view_delete.
  Qed.
  Lemma othreadG_owns_update i OObls k f1 f2 :
    (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
    othreadG_owns i k f1 1
    ⊢ |==> (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (<[k:=f2]>OObls))))) ∗
           othreadG_owns i k f2 1.
  Proof.
    rewrite /othreadG_owns -!own_op -!reservation_map_data_op. apply own_update.
    apply reservation_map_update. rewrite fmap_insert. apply gmap_view_replace. done.
  Qed.
  Lemma othreadG_owns_lookup i OObls k f q :
    (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
    othreadG_owns i k f q
    ⊢ ⌜ OObls !! k = Some f ⌝.
  Proof.
    rewrite /othreadG_owns -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H0.
    destruct H0 as (?&_&_&?&?&?). iPureIntro.
    rewrite lookup_fmap in H0. destruct (OObls !! k) eqn:HO.
    - inv H0. apply to_agree_included_L in H2. by subst.
    - done.
  Qed.

  Lemma othreadG_owns_frac_op i k f q1 q2 q :
    q = (q1 + q2)%Qp →
    othreadG_owns i k f q1 ∗ othreadG_owns i k f q2 ⊣⊢ othreadG_owns i k f q.
  Proof.
    intros; subst. rewrite /othreadG_owns.
    rewrite -own_op -reservation_map_data_op -gmap_view_frag_op dfrac_op_own.
    rewrite agree_idemp. done.
  Qed.
  Lemma othreadG_owns_div_2 i k f q:
    othreadG_owns i k f (q/2) ∗ othreadG_owns i k f (q/2) ⊣⊢ othreadG_owns i k f q.
  Proof. rewrite othreadG_owns_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma othreadG_owns_valid i k f q :
    othreadG_owns i k f q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_owns. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. done.
  Qed.
  Lemma othreadG_owns_valid_2 i k f1 f2 q1 q2 :
    othreadG_owns i k f1 q1 ∗ othreadG_owns i k f2 q2 ⊢ ⌜ (q1 + q2 ≤ 1)%Qp ∧ f1 = f2 ⌝.
  Proof.
    rewrite /othreadG_owns. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. apply to_agree_op_valid in H1. done.
  Qed.
  Lemma othreadG_owns_agree i k f1 f2 q1 q2 :
    othreadG_owns i k f1 q1 ∗ othreadG_owns i k f2 q2 ⊢ ⌜ f1 = f2 ⌝.
  Proof. etransitivity; first eapply othreadG_owns_valid_2. iPureIntro. intros [? ?]. auto. Qed.

  Lemma othreadG_owns_update_2 i OObls k f1 f2 f q1 q2 :
    (q1 + q2 = 1)%Qp →
    (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
    othreadG_owns i k f1 q1 ∗ othreadG_owns i k f2 q2
    ⊢ |==> (own status_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (<[k:=f]>OObls))))) ∗
           othreadG_owns i k f q1 ∗ othreadG_owns i k f q2.
  Proof.
    intros Hq. iIntros "[H Hq]". iPoseProof (othreadG_owns_valid_2 with "Hq") as "%". destruct H0 as [_ ?]. subst.
    rewrite !othreadG_owns_frac_op.
    2,3: rewrite Hq; reflexivity.
    iMod (othreadG_owns_update with "[H Hq]") as "H"; [iFrame | by iFrame].
  Qed.

  (** Thread rules *)
  Lemma othreadG_obls_alloc (OThread : gmap positive (gmap obl_id bool)) i :
    OThread !! i = None →
    (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread))))
    ⊢ |==> (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> <[i:=∅]>OThread)))) ∗
           othreadG_obls i ∅ 1.
  Proof.
    iIntros (Hi) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracOwn 1) (GSet ∅ : gset_disj _)); try done.
      rewrite !lookup_fmap Hi. done.
    }
    iDestruct "H" as "[H Ho]". rewrite /othreadG_obls. iFrame "Ho".
    rewrite !fmap_insert. done.
  Qed.

  Lemma othreadG_obls_lookup (OThread : gmap positive (gmap obl_id bool)) i Ψ :
    (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Ψ 1
    ⊢ ⌜ (dom <$> OThread) !! i = Some Ψ ⌝.
  Proof.
    rewrite /othreadG_obls -!own_op. iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H0. destruct H0 as (_&_&?). iPureIntro.
    apply leibniz_equiv, lookup_fmap_Some in H0. destruct H0 as (?&?&?). inv H0. done.
  Qed.
  Lemma othreadG_obls_lookup_frac (OThread : gmap positive (gmap obl_id bool)) i Ψ q :
    (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Ψ q
    ⊢ ∃ Ψ', ⌜ (dom <$> OThread) !! i = Some Ψ' ∧ Ψ ⊆ Ψ' ⌝.
  Proof.
    rewrite /othreadG_obls -!own_op. iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_dfrac_valid_discrete_total in H0. destruct H0 as (?&_&_&?&?&?). iPureIntro.
    destruct x; last done. apply gset_disj_included in H2. eexists. split; last eauto.
    apply lookup_fmap_Some in H0. destruct H0 as (?&?&?). inv H0. done.
  Qed.

  Lemma othreadG_obls_update (OThread : gmap positive (gmap obl_id bool)) i Ψ M :
    (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Ψ 1
    ⊢ |==> (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> <[i:=M]>OThread)))) ∗
           othreadG_obls i (dom M) 1.
  Proof.
    rewrite /othreadG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. apply gmap_view_replace. done.
  Qed.
  Lemma othreadG_obls_update_local (OThread : gmap positive (gmap obl_id bool)) i q M1 M2 X1 X2 :
    (OThread !! i = Some M1) →
    (GSet (dom M1), GSet X1) ~l~> (GSet (dom M2), GSet X2) →
    (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i X1 q
    ⊢ |==> (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> <[i:=M2]>OThread)))) ∗
           othreadG_obls i X2 q.
  Proof.
    intros Hlookup Hlu. rewrite /othreadG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. eapply gmap_view_update_local; eauto.
    rewrite !lookup_fmap Hlookup. done.
  Qed.

  Lemma othreadG_obls_valid i Ψ q :
    othreadG_obls i Ψ q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_obls. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. apply gmap_view_frag_valid in V. destruct V. done.
  Qed.
  Lemma othreadG_obls_valid_2 i Ψ1 Ψ2 q1 q2 :
    othreadG_obls i Ψ1 q1 ∗ othreadG_obls i Ψ2 q2 ⊢ ⌜ (q1 + q2 ≤ 1)%Qp ∧ Ψ1 ## Ψ2 ⌝.
  Proof.
    rewrite /othreadG_obls. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. apply gmap_view_frag_valid in V. destruct V. split; first done.
    apply gset_disj_valid_op in H1. done.
  Qed.

  Lemma othreadG_obls_op_1 i Ψ1 Ψ2 q1 q2 :
    othreadG_obls i Ψ1 q1 ∗ othreadG_obls i Ψ2 q2 ⊢ othreadG_obls i (Ψ1 ∪ Ψ2) (q1 + q2)%Qp.
  Proof.
    rewrite /othreadG_obls -own_op -gmap_view_frag_op dfrac_op_own.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_frag_valid in H0. destruct H0. apply gset_disj_valid_op in H1.
    rewrite gset_disj_union; done.
  Qed.
  Lemma othreadG_obls_op_2 i Ψ1 Ψ2 q1 q2 :
    Ψ1 ## Ψ2 →
    othreadG_obls i (Ψ1 ∪ Ψ2) (q1 + q2)%Qp ⊢ othreadG_obls i Ψ1 q1 ∗ othreadG_obls i Ψ2 q2.
  Proof.
    intros Hdj. rewrite /othreadG_obls -own_op -gmap_view_frag_op dfrac_op_own.
    rewrite gset_disj_union; done.
  Qed.

  (** Exec rules *)
  Lemma othreadG_exec_term_false k q :
    othreadG_exec k q ∗ othreadG_term k ⊢ False.
  Proof.
    rewrite /othreadG_exec /othreadG_term. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma othreadG_term_auth_term k :
    othreadG_term_auth k ⊢ othreadG_term k.
  Proof.
    rewrite /othreadG_term_auth /othreadG_term.
    apply own_mono.
    apply reservation_map_data_mono. apply mono_nat_included.
  Qed.
  Lemma othreadG_exec_to_term k :
    othreadG_exec k 1 ⊢ |==> othreadG_term_auth k.
  Proof.
    rewrite /othreadG_exec /othreadG_term_auth.
    apply own_update.
    apply reservation_map_update. apply mono_nat_update. auto.
  Qed.

  Lemma othreadG_exec_frac_op k q1 q2 q :
    q = (q1 + q2)%Qp →
    othreadG_exec k q1 ∗ othreadG_exec k q2 ⊣⊢ othreadG_exec k q.
  Proof.
    intros; subst. rewrite /othreadG_exec. iSplit; [iIntros "[H1 H2]" | iIntros "H"].
    - iCombine "H1 H2" as "H". done.
    - iDestruct "H" as "[H1 H2]". iFrame.
  Qed.
  Lemma othreadG_exec_div_2 k q :
    othreadG_exec k (q/2) ∗ othreadG_exec k (q/2) ⊣⊢ othreadG_exec k q.
  Proof. rewrite othreadG_exec_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma othreadG_exec_valid k q :
    othreadG_exec k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_exec. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply mono_nat_auth_dfrac_valid in V. by apply dfrac_valid in V.
  Qed.

  Lemma othreadG_exec_alloc D k :
    k ∉ D →
    (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           othreadG_exec k 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN 0) with "Htk") as "[Htk >H]"; auto.
    { apply mono_nat_auth_valid. }
    rewrite /othreadG_exec. by iFrame.
  Qed.

  (** othread rules *)
  Lemma othread_elem i TP :
    othread TP ∗ othreadG_elem i ⊢ ⌜i ∈ TP⌝.
  Proof.
    rewrite /othread -!lock. iIntros "(Hthread & He)".
    iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (othreadG_elem_elem with "[$]") as "%".
    by rewrite -Hdom.
  Qed.

  Lemma othread_alloc_thread i TP :
    i ∉ TP →
    othread TP
    ⊢ |==> othread ({[i]} ∪ TP) ∗ othreadG_elem i ∗ othreadG_obls i ∅ 1 ∗ othreadG_exec i (1/2)%Qp.
  Proof.
    iIntros (Hi) "Hthread".
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    assert (Hlu : OThread !! i = None).
    { apply not_elem_of_dom. rewrite Hdom. auto. }
    iMod (othreadG_elem_alloc _ i ∅ with "HE") as "[HE He]"; first auto.
    iMod (othreadG_owns_alloc_map with "HS") as "[HS Hs]"; first done.
    iMod (othreadG_obls_alloc _ i with "HO") as "[HO Ho]"; first auto.
    iMod (othreadG_exec_alloc _ i with "HX") as "[HX Hx]"; first auto.
    iDestruct (othreadG_exec_div_2 with "Hx") as "[Hx0 Hx]".
    iModIntro. iFrame "He Ho Hx0". iExists (<[i:=∅]>OThread). iFrame "HE HS HO HX".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom. done. }
    iApply big_sepM_insert; first done.
    iFrame. done.
  Qed.

  Lemma othread_alloc_obl_1 TP i Ψ q k :
    oblG_live k (1/2)%Qp ∗ oblG_live k (1/2)%Qp ∗ othread TP ∗ othreadG_obls i Ψ q
    ⊢ |==> oblG_live k (1/2)%Qp ∗ oblG_live k (1/2/2)%Qp ∗ othread TP ∗ othreadG_obls i ({[k]} ∪ Ψ) q ∗ othreadG_owns i k false 1.
  Proof.
    iIntros "(Os0 & Os & Hthread & Ho)".
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (othreadG_obls_lookup_frac with "[HO Ho]") as "%"; first iFrame.
    destruct H0 as (Ψ0&Hlui0&Hsub).
    assert (Hlui : ∃ m, dom m = Ψ0 ∧ OThread !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. eauto. }
    destruct Hlui as (OObls&Hm&Hlui).
    iAssert (⌜ OObls !! k = None ⌝)%I with "[Os0 Os Hm]" as "%Hluk".
    { destruct (OObls !! k) eqn:LU; last done. iExFalso.
      iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi _]".
      iDestruct "Hi" as "(Hix & His & Him)".
      iDestruct (big_sepM_delete _ _ k _ LU with "Him") as "[Hk Him]".
      iDestruct "Hk" as "(Oks & Oko)".
      iCombine "Os0 Os" as "Os". iPoseProof (oblG_live_div_2 with "Os") as "Os".
      iCombine "Os Oks" as "Os". iPoseProof (oblG_live_frac_op with "Os") as "Os"; first done.
      iPoseProof (oblG_live_valid with "Os") as "%Hv". iPureIntro. done.
    }
    iPoseProof (oblG_live_div_2 with "Os") as "[Os Os']". iFrame "Os0 Os'".
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iMod (othreadG_owns_alloc _ _ _ false Hluk with "His") as "[His Hw]".
    iFrame "Hw".
    iMod (othreadG_obls_update_local _ _ _ OObls (<[k:=false]>OObls) _ ({[k]} ∪ Ψ) with "[HO Ho]") as "[HO Ho]";
      [eauto | | iFrame |].
    { rewrite dom_insert_L. apply gset_disj_alloc_local_update. apply not_elem_of_dom in Hluk. set_solver. }
    iFrame "Ho".
    iModIntro. iExists (<[i:=(<[k:=false]>OObls)]>OThread). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HS HX HO". iSplitL "HE".
    { rewrite !fmap_insert. rewrite insert_id; first done. rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq OThread i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame "Hm Hix His". iApply (big_sepM_insert _ _ k); first done. iFrame.
  Qed.
  Lemma othread_alloc_obl Ω TP i Ψ q k :
    osat Ω ∗ othread TP ∗ othreadG_obls i Ψ q ∗ oblG_elem k ∗ oblG_live k (1/2)%Qp
    ⊢ |==> osat Ω ∗ othread TP ∗ othreadG_obls i ({[k]} ∪ Ψ) q ∗ othreadG_owns i k false 1 ∗ oblG_live k (1/2/2)%Qp.
  Proof.
    iIntros "(Osat & Hthread & Ho & #He & Os)".
    iPoseProof (osat_live_open with "[Osat Os]") as "(Os & Os0 & Osacc)"; first by iFrame.
    iMod (othread_alloc_obl_1 with "[$]") as "(Os0 & Os1 & Hthread & Ho & Hw)".
    iModIntro. iFrame. by iApply "Osacc".
  Qed.

  Lemma othread_obls_owns_elem TP i Ψ k f q :
    othread TP ∗ othreadG_obls i Ψ 1 ∗ othreadG_owns i k f q
    ⊢ ⌜ k ∈ Ψ ⌝.
  Proof.
    iIntros "(Hthread & Ho & Hw)".
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (othreadG_obls_lookup with "[HO Ho]") as "%"; first iFrame.
    assert (Hlui : ∃ m, dom m = Ψ ∧ OThread !! i = Some m).
    { rewrite lookup_fmap_Some in H0. eauto. }
    destruct Hlui as (OObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[His Hw]") as "%Hluk"; first iFrame.
    iPureIntro. rewrite -Hm. by apply elem_of_dom.
  Qed.

  Lemma othread_delete_obl_frac TP i Ψ q k f :
    k ∈ Ψ →
    othread TP ∗ othreadG_obls i Ψ q ∗ othreadG_owns i k f 1
    ⊢ |==> othread TP ∗ othreadG_obls i (Ψ ∖ {[k]}) q ∗
           oblG_live k (1/2/2)%Qp ∗ (if f then oblG_owner k i (1 / 2 / 2) else emp).
  Proof.
    iIntros (Hink) "(Hthread & Ho & Hw)".
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (othreadG_obls_lookup_frac with "[HO Ho]") as "%"; first iFrame.
    destruct H0 as (Ψ0&Hlui0&Hsub).
    assert (Hlui : ∃ m, dom m = Ψ0 ∧ OThread !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. eauto. }
    destruct Hlui as (OObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[His Hw]") as "%Hluk"; first iFrame.
    iMod (othreadG_owns_delete with "[His Hw]") as "His"; first iFrame.
    iMod (othreadG_obls_update_local _ _ _ OObls (delete k OObls) _ (Ψ ∖ {[k]}) with "[HO Ho]") as "[HO Ho]";
      [eauto | | iFrame |].
    { replace (GSet (dom OObls)) with (GSet ({[k]}) ⋅ GSet (dom (delete k OObls))).
      2:{ rewrite dom_delete_L gset_disj_union.
          - f_equal. apply elem_of_dom_2 in Hluk. rewrite -union_difference_L; set_solver.
          - set_solver.
      }
      replace (GSet Ψ) with (GSet {[k]} ⋅ GSet (Ψ ∖ {[k]})).
      2:{ rewrite gset_disj_union; last set_solver. f_equal. rewrite -union_difference_L; auto. set_solver. }
      apply gset_disj_dealloc_op_local_update.
    }
    iFrame "Ho".
    iDestruct (big_sepM_delete _ _ k _ Hluk with "Him") as "[Hik Him]".
    iDestruct "Hik" as "[Hik1 Hik2]". iFrame "Hik1 Hik2".
    iModIntro. iExists (<[i:=(delete k OObls)]>OThread). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HS HX HO". iSplitL "HE".
    { rewrite !fmap_insert. rewrite insert_id; first done. rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq OThread i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame.
  Qed.
  Lemma othread_delete_obl TP i Ψ k f :
    othread TP ∗ othreadG_obls i Ψ 1 ∗ othreadG_owns i k f 1
    ⊢ |==> othread TP ∗ othreadG_obls i (Ψ ∖ {[k]}) 1 ∗
           oblG_live k (1/2/2)%Qp ∗ (if f then oblG_owner k i (1 / 2 / 2) else emp).
  Proof.
    iIntros "(Hthread & Ho & Hw)". iPoseProof (othread_obls_owns_elem with "[$]") as "%Hkin".
    iApply (othread_delete_obl_frac with "[$]"). auto.
  Qed.

  Lemma othread_obl_acquire TP i k :
    othread TP ∗ othreadG_elem i ∗ othreadG_owns i k false 1 ∗ oblG_owner k i (1/2/2)%Qp
    ⊢ |==> othread TP ∗ othreadG_owns i k true 1.
  Proof.
    iIntros "(Hthread & He & Hw & Ow)".
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (othreadG_elem_elem with "[$]") as "%Hini".
    assert (Hlui : ∃ m, OThread !! i = Some m).
    { rewrite elem_of_dom in Hini. eauto. }
    destruct Hlui as (OObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup _ _ k with "[$]") as "%Hluk".
    iMod (othreadG_owns_update _ _ k false true with "[$]") as "[His Hw]".
    iFrame "Hw".
    iModIntro. iExists (<[i:=<[k:=true]>OObls]>OThread). iFrame "HS HX".
    iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    rewrite !fmap_insert. iSplitL "HO".
    { rewrite (insert_id _ i); auto. rewrite dom_insert_lookup_L; auto. rewrite !lookup_fmap Hlui. done. }
    iSplitL "HE".
    { rewrite insert_id; first done. rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq OThread i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame. iSplitL "His".
    { by rewrite !fmap_insert. }
    rewrite -(insert_delete_eq OObls k). iApply (big_sepM_insert _ _ k).
    { apply lookup_delete_eq. }
    iDestruct (big_sepM_delete _ _ k _ Hluk with "Him") as "[Hk Him]".
    iDestruct "Hk" as "[Hk _]". iFrame.
  Qed.
  Lemma othread_obl_acquire_2 TP i k :
    othread TP ∗ othreadG_elem i ∗ othreadG_owns i k false (1/2)%Qp ∗ othreadG_owns i k false (1/2)%Qp ∗ oblG_owner k i (1/2/2)%Qp
    ⊢ |==> othread TP ∗ othreadG_owns i k true (1/2)%Qp ∗ othreadG_owns i k true (1/2)%Qp.
  Proof.
    iIntros "(Hthread & He & Hw1 & Hw2 & Ow)".
    iCombine "Hw1 Hw2" as "Hw". iPoseProof (othreadG_owns_frac_op _ _ _ _ _ 1 with "Hw") as "Hw".
    { by rewrite Qp.div_2. }
    iMod (othread_obl_acquire with "[$]") as "[Hthread Hw]".
    iDestruct (othreadG_owns_frac_op _ _ _ (1/2) (1/2) with "Hw") as "[Hw1 Hw2]".
    { by rewrite Qp.div_2. }
    by iFrame.
  Qed.

  Lemma othread_obl_release TP i k :
    othread TP ∗ othreadG_elem i ∗ othreadG_owns i k true 1
    ⊢ |==> othread TP ∗ othreadG_owns i k false 1 ∗ oblG_owner k i (1/2/2)%Qp.
  Proof.
    iIntros "(Hthread & He & Hw)".
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (othreadG_elem_elem with "[$]") as "%Hini".
    assert (Hlui : ∃ m, OThread !! i = Some m).
    { rewrite elem_of_dom in Hini. eauto. }
    destruct Hlui as (OObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup _ _ k with "[$]") as "%Hluk".
    iMod (othreadG_owns_update _ _ k true false with "[$]") as "[His Hw]".
    iFrame "Hw".
    iDestruct (big_sepM_delete _ _ k _ Hluk with "Him") as "[Hk Him]".
    iDestruct "Hk" as "[Os Ow]". iFrame "Ow".
    iModIntro. iExists (<[i:=<[k:=false]>OObls]>OThread). iFrame "HS HX".
    iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    rewrite !fmap_insert. iSplitL "HO".
    { rewrite (insert_id _ i); auto. rewrite dom_insert_lookup_L; auto. rewrite !lookup_fmap Hlui. done. }
    iSplitL "HE".
    { rewrite insert_id; first done. rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq OThread i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame. iSplitL "His".
    { by rewrite !fmap_insert. }
    rewrite -(insert_delete_eq OObls k). iApply (big_sepM_insert _ _ k).
    { apply lookup_delete_eq. }
    iFrame.
  Qed.
  Lemma othread_obl_release_2 TP i k :
    othread TP ∗ othreadG_elem i ∗ othreadG_owns i k true (1/2)%Qp ∗ othreadG_owns i k true (1/2)%Qp
    ⊢ |==> othread TP ∗ othreadG_owns i k false (1/2)%Qp ∗ othreadG_owns i k false (1/2)%Qp ∗ oblG_owner k i (1/2/2)%Qp.
  Proof.
    iIntros "(Hthread & He & Hw1 & Hw2)".
    iCombine "Hw1 Hw2" as "Hw". iPoseProof (othreadG_owns_frac_op _ _ _ _ _ 1 with "Hw") as "Hw".
    { by rewrite Qp.div_2. }
    iMod (othread_obl_release with "[$]") as "(Hthread & Hw & Ow)".
    iDestruct (othreadG_owns_frac_op _ _ _ (1/2) (1/2) with "Hw") as "[Hw1 Hw2]".
    { by rewrite Qp.div_2. }
    by iFrame.
  Qed.

  Lemma othread_exec_to_term TP i :
    othread TP ∗ othreadG_exec i (1/2)%Qp ∗ othreadG_obls i ∅ 1
    ⊢ |==> othread TP ∗ othreadG_term i.
  Proof.
    iIntros "(Hthread & Hx & Ho)".
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (othreadG_obls_lookup with "[HO Ho]") as "%"; first iFrame.
    assert (Hlui : OThread !! i = Some ∅).
    { rewrite lookup_fmap_Some in H0. destruct H0 as (?&?&?). apply dom_empty_inv_L in H0. subst; eauto. }
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix _]] & His & Him)"; last first.
    { iExFalso. iPoseProof (othreadG_term_auth_term with "[$]") as "Hxt".
      iPoseProof (othreadG_exec_term_false with "[$]") as "%F". inversion F.
    }
    iMod (othreadG_exec_to_term with "[Hx Hix]") as "Hx".
    { rewrite -(othreadG_exec_div_2 _ 1). iFrame. }
    iPoseProof (othreadG_term_auth_term with "Hx") as "#Hxt".
    iModIntro. iSplitL; last done.
    iExists OThread. iSplitR; first done. iFrame "HS HX HO HE".
    iApply (big_sepM_delete _ _ i _ Hlui). iFrame. iRight. iFrame.
  Qed.

  Lemma othread_term_open TP i :
    othread TP ∗ othreadG_elem i ∗ othreadG_term i
    ⊢ othreadG_obls i ∅ 1 ∗ (othreadG_obls i ∅ 1 -∗ othread TP).
  Proof.
    iIntros "(Hthread & He & Hx)".
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (othreadG_elem_elem with "[$]") as "%Hini".
    assert (Hlui : ∃ m, OThread !! i = Some m).
    { rewrite elem_of_dom in Hini. eauto. }
    destruct Hlui as (OObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix Ho]] & His & Him)".
    { iExFalso. iPoseProof (othreadG_exec_term_false with "[$]") as "%F". inversion F. }
    iFrame "Ho". iIntros "Ho".
    iExists OThread. iSplitR; first done. iFrame "HS HX HO HE".
    iApply (big_sepM_delete _ _ i _ Hlui). iFrame. iRight. iFrame.
  Qed.

  Lemma othread_live_open TP i k f q :
    othread TP ∗ othreadG_elem i ∗ othreadG_owns i k f q
    ⊢ othreadG_owns i k f q ∗
    (oblG_live k (1/2/2)%Qp ∗ (if f then oblG_owner k i (1 / 2 / 2) else emp)) ∗
    ((oblG_live k (1/2/2)%Qp ∗ (if f then oblG_owner k i (1 / 2 / 2) else emp)) -∗ othread TP).
  Proof.
    iIntros "(Hthread & He & Hw)".
    iPoseProof (othread_elem with "[Hthread He]") as "%Hin"; first iFrame.
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    assert (Hlui : is_Some (OThread !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (OObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[His Hw]") as "%Hluk"; first iFrame.
    iPoseProof (big_sepM_delete _ _ _ _ Hluk with "Him") as "[Hk Him]".
    iFrame "Hw Hk". iIntros "Hk". iExists OThread. iFrame "HS HX HO HE".
    iSplit; first done. iApply (big_sepM_delete _ _ _ _ Hlui). iFrame.
    iApply (big_sepM_delete _ _ _ _ Hluk). iFrame.
  Qed.

End othread.

(* Allocation of initial invariant. *)
Lemma othread_alloc `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGpreS Σ} :
  ⊢ |==> ∃ _ : othreadGS Σ, othread ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR obl_id (agreeR (leibnizO bool)))) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive (gset_disjUR _))) as (γO) "HO";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γX) "HX";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive unitUR)) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OthreadG SI _ _ γS γO γX γE).
  rewrite /othread -lock. iExists ∅. iSplitR; first done.
  replace (⊤ ∖ gset_to_coPset ∅) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
