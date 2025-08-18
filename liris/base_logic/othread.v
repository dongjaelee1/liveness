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
        othreadGpreS_state : inG Σ (reservation_mapUR (gmap_viewR obl_id (agreeR (leibnizO bool))));
        othreadGpreS_thread : inG Σ (gmap_viewR positive (gset_disjUR obl_id));
        othreadGpreS_exec : inG Σ (reservation_mapUR mono_natUR);
        othreadGpreS_elem : inG Σ (gmap_viewR positive unitUR);
      }.

  Class othreadGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadG {
        othread_inG : othreadGpreS Σ;
        state_name : gname;
        thread_name : gname;
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
  othreadGpreS_state othreadGpreS_thread othreadGpreS_exec othreadGpreS_elem.

(* States: thread currently has this obl or not *)
Definition othreadG_owns `{SI : indexT} `{!othreadGS Σ} (i : positive) (k : obl_id) (f : bool) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data i (gmap_view_frag k (DfracOwn q) (to_agree $ f))).
Global Typeclasses Opaque othreadG_owns.
Global Instance: Params (@othreadG_owns) 5 := {}.

(* Thread: live obligations that this thread knows, also fix to empty when thread terminates *)
Definition othreadG_obls `{SI : indexT} `{!othreadGS Σ} (i : positive) (Θ : gset obl_id) (q : Qp) : iProp Σ :=
  own thread_name (gmap_view_frag i (DfracOwn q) (GSet Θ)).
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
        (own state_name (reservation_map_token (A:=gmap_viewR obl_id (agreeR (leibnizO bool))) (⊤ ∖ gset_to_coPset TP))) ∗
        (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset TP))) ∗
        (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
        (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> OThread))) ∗
        ([∗ map] i ↦ OObls ∈ OThread,
           (othreadG_exec i (1/2)%Qp ∨ (othreadG_term_auth i ∗ othreadG_obls i ∅ 1)) ∗
           (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
           ([∗ map] k ↦ f ∈ OObls, oblG_live k (1/2)%Qp ∗
                                    (match f with | true => oblG_owner k i (1/2/2)%Qp | _ => emp end))
        )
    )%I.

Section othread.
  Context `{SI : indexT} `{WFA : WFOCM.pack A}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS Σ}.

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

  (** State rules *)
  Lemma othreadG_state_alloc D i :
    i ∉ D →
    (own state_name (reservation_map_token (A:=gmap_viewR obl_id (agreeR (leibnizO bool))) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own state_name (reservation_map_token (A:=gmap_viewR obl_id (agreeR (leibnizO bool))) (⊤ ∖ gset_to_coPset ({[i]} ∪ D)))) ∗
           (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap obl_id bool))))).
  Proof.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap obl_id bool))) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma othreadG_owns_alloc i (OObls : gmap obl_id bool) k (f : bool) :
    OObls !! k = None →
    (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls))))
    ⊢ |==> (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (<[k := f]>OObls))))) ∗
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
    (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
    othreadG_owns i k f 1
    ⊢ |==> (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (delete k OObls))))).
  Proof.
    rewrite -own_op -reservation_map_data_op. apply own_update, reservation_map_update.
    rewrite fmap_delete. apply gmap_view_delete.
  Qed.
  Lemma othreadG_owns_update i OObls k f1 f2 :
    (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
    othreadG_owns i k f1 1
    ⊢ |==> (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (<[k:=f2]>OObls))))) ∗
           othreadG_owns i k f2 1.
  Proof.
    rewrite /othreadG_owns -!own_op -!reservation_map_data_op. apply own_update.
    apply reservation_map_update. rewrite fmap_insert. apply gmap_view_replace. done.
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
    (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> OObls)))) ∗
    othreadG_owns i k f1 q1 ∗ othreadG_owns i k f2 q2
    ⊢ |==> (own state_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> (<[k:=f]>OObls))))) ∗
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
    (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread))))
    ⊢ |==> (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> <[i:=∅]>OThread)))) ∗
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

  Lemma othreadG_obls_lookup (OThread : gmap positive (gmap obl_id bool)) i Θ :
    (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Θ 1
    ⊢ ⌜ (dom <$> OThread) !! i = Some Θ ⌝.
  Proof.
    rewrite /othreadG_obls -!own_op. iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H0. destruct H0 as (_&_&?). iPureIntro.
    apply leibniz_equiv, lookup_fmap_Some in H0. destruct H0 as (?&?&?). inv H0. done.
  Qed.
  Lemma othreadG_obls_lookup_frac (OThread : gmap positive (gmap obl_id bool)) i Θ q :
    (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Θ q
    ⊢ ∃ Θ', ⌜ (dom <$> OThread) !! i = Some Θ' ∧ Θ ⊆ Θ' ⌝.
  Proof.
    rewrite /othreadG_obls -!own_op. iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_dfrac_valid_discrete_total in H0. destruct H0 as (?&_&_&?&?&?). iPureIntro.
    destruct x; last done. apply gset_disj_included in H2. eexists. split; last eauto.
    apply lookup_fmap_Some in H0. destruct H0 as (?&?&?). inv H0. done.
  Qed.

  Lemma othreadG_obls_update (OThread : gmap positive (gmap obl_id bool)) i Θ M :
    (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Θ 1
    ⊢ |==> (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> <[i:=M]>OThread)))) ∗
           othreadG_obls i (dom M) 1.
  Proof.
    rewrite /othreadG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. apply gmap_view_replace. done.
  Qed.
  Lemma othreadG_obls_update_local (OThread : gmap positive (gmap obl_id bool)) i q M1 M2 X1 X2 :
    (OThread !! i = Some M1) →
    (GSet (dom M1), GSet X1) ~l~> (GSet (dom M2), GSet X2) →
    (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i X1 q
    ⊢ |==> (own thread_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> <[i:=M2]>OThread)))) ∗
           othreadG_obls i X2 q.
  Proof.
    intros Hlookup Hlu. rewrite /othreadG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. eapply gmap_view_update_local; eauto.
    rewrite !lookup_fmap Hlookup. done.
  Qed.

  Lemma othreadG_obls_valid i Θ q :
    othreadG_obls i Θ q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_obls. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. apply gmap_view_frag_valid in V. destruct V. done.
  Qed.
  Lemma othreadG_obls_valid_2 i Θ1 Θ2 q1 q2 :
    othreadG_obls i Θ1 q1 ∗ othreadG_obls i Θ2 q2 ⊢ ⌜ (q1 + q2 ≤ 1)%Qp ∧ Θ1 ## Θ2 ⌝.
  Proof.
    rewrite /othreadG_obls. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. apply gmap_view_frag_valid in V. destruct V. split; first done.
    apply gset_disj_valid_op in H1. done.
  Qed.

  Lemma othreadG_obls_op_1 i Θ1 Θ2 q1 q2 :
    othreadG_obls i Θ1 q1 ∗ othreadG_obls i Θ2 q2 ⊢ othreadG_obls i (Θ1 ∪ Θ2) (q1 + q2)%Qp.
  Proof.
    rewrite /othreadG_obls -own_op -gmap_view_frag_op dfrac_op_own.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_frag_valid in H0. destruct H0. apply gset_disj_valid_op in H1.
    rewrite gset_disj_union; done.
  Qed.
  Lemma othreadG_obls_op_2 i Θ1 Θ2 q1 q2 :
    Θ1 ## Θ2 →
    othreadG_obls i (Θ1 ∪ Θ2) (q1 + q2)%Qp ⊢ othreadG_obls i Θ1 q1 ∗ othreadG_obls i Θ2 q2.
  Proof.
    intros Hdj. rewrite /othreadG_obls -own_op -gmap_view_frag_op dfrac_op_own.
    rewrite gset_disj_union; done.
  Qed.

  (** Exec rules *)
  Lemma othreadG_exec_done_false k q :
    othreadG_exec k q ∗ othreadG_term k ⊢ False.
  Proof.
    rewrite /othreadG_exec /othreadG_term. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma othreadG_term_auth_done k :
    othreadG_term_auth k ⊢ othreadG_term k.
  Proof.
    rewrite /othreadG_term_auth /othreadG_term.
    apply own_mono.
    apply reservation_map_data_mono. apply mono_nat_included.
  Qed.
  Lemma othreadG_exec_to_done k :
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

End othread.

(* Allocation of an initial obligation protocol. *)
(* Lemma othread_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!othreadGpreS ps T Σ} `{obl_class A ps T} : *)
(*   ⊢ |==> ∃ _ : othreadGS ps T Σ, othread ∅. *)
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
(*   iModIntro; iExists (OthreadG SI _ WFA _ _ _ _ γG γM γS γT γO γC). *)
(*   rewrite /othread -lock. *)
(*   iSplitL "HG"; first (iExists ∅; by iFrame). *)
(*   iSplitL "HM"; first (iExists ∅; by iFrame). *)
(*   by iFrame. *)
(* Qed. *)
