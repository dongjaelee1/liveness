From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.base_logic Require Export osat.

(** The ghost state for thread obligations *)
Module othreadGS.

  (* Assumes thread ids are positive *)
  Class othreadGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadGpreS {
        othreadGpreS_owns : inG Σ (reservation_mapUR (gmap_viewR obl_id unitUR));
        othreadGpreS_obls : inG Σ (gmap_viewR positive (gset_disjUR obl_id));
        othreadGpreS_exec : inG Σ (reservation_mapUR mono_natUR);
        othreadGpreS_elem : inG Σ (gmap_viewR positive unitUR);
      }.

  Class othreadGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadG {
        othread_inG : othreadGpreS Σ;
        owns_name : gname;
        obls_name : gname;
        exec_name : gname;
        elem_name : gname;
      }.

  Definition othreadΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR obl_id unitUR));
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
Local Existing Instances othread_inG othreadGpreS_owns othreadGpreS_obls othreadGpreS_exec othreadGpreS_elem.

(* Owns: thread currently has this obl *)
Definition othreadG_owns `{SI : indexT} `{!othreadGS Σ} (i : positive) (k : obl_id) (q : Qp) : iProp Σ :=
  own owns_name (reservation_map_data i (gmap_view_frag k (DfracOwn q) tt)).
Global Typeclasses Opaque othreadG_owns.
Global Instance: Params (@othreadG_owns) 4 := {}.

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
    (∃ (OThread : gmap positive (gmap obl_id unit)),
        (⌜ dom OThread = TP ⌝) ∗
        (own owns_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset TP))) ∗
        (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset TP))) ∗
        (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
        (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> OThread))) ∗
        ([∗ map] i ↦ OObls ∈ OThread,
           (othreadG_exec i (1/2)%Qp ∨ (othreadG_term_auth i ∗ othreadG_obls i ∅ 1)) ∗
           (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) OObls))) ∗
           ([∗ map] k ↦ f ∈ OObls, oblG_live k (1/2)%Qp ∗ oblG_owner k i (1/2)%Qp)
        )
    )%I.

(* Global invariant that relates obl_states with the thread pool. *)
Definition oassigned `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS Σ}
  (OS : gset obl_id) (TP : gset positive) : iProp Σ :=
  locked
    ([∗ set] k ∈ OS, ∃ i, othreadG_owns i k (1/2)%Qp
    )%I.
  (* locked *)
  (*   ([∗ set] k ∈ OS, ∃ i, oblG_owner k i (1/2/2)%Qp ∗ othreadG_owns i k (1/2)%Qp *)
  (*   )%I. *)

Section othread.
  Context `{SI : indexT} `{WFA : WFOCM.pack A}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS Σ}.
  Context `{Ξl : obl_live_class A positive WFOCM.ltR} `{Ξd : obl_done_class ps}.

  Global Instance othreadG_term_persistent i : Persistent (othreadG_term i).
  Proof. rewrite /othreadG_term. apply _. Qed.
  Global Instance othreadG_elem_persistent i : Persistent (othreadG_elem i).
  Proof. rewrite /othreadG_elem. apply _. Qed.

  Global Instance othreadG_owns_timeless i k q : Timeless (othreadG_owns i k q).
  Proof. rewrite /othreadG_owns. apply _. Qed.
  Global Instance othreadG_obls_timeless i Ψ q : Timeless (othreadG_obls i Ψ q).
  Proof. rewrite /othreadG_obls. apply _. Qed.
  Global Instance othreadG_exec_timeless i q : Timeless (othreadG_exec i q).
  Proof. rewrite /othreadG_exec. apply _. Qed.
  Global Instance othreadG_term_timeless i : Timeless (othreadG_term i).
  Proof. rewrite /othreadG_term. apply _. Qed.
  Global Instance othreadG_elem_timeless i : Timeless (othreadG_elem i).
  Proof. rewrite /othreadG_elem. apply _. Qed.

  (** Elem rules *)
  Lemma othreadG_elem_alloc (OThread : gmap positive (gmap obl_id unit)) i M :
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

  Lemma othreadG_elem_elem i (OThread : gmap positive (gmap obl_id unit)) :
    (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> OThread))) ∗
    othreadG_elem i
    ⊢ ⌜ i ∈ dom OThread ⌝.
  Proof.
    rewrite /othreadG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro. apply elem_of_dom_2 in H0. by rewrite dom_fmap_L in H0.
  Qed.

  (** Owns rules *)
  Lemma othreadG_owns_alloc_map D i :
    i ∉ D →
    (own owns_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own owns_name (reservation_map_token (A:=gmap_viewR obl_id unitUR) (⊤ ∖ gset_to_coPset ({[i]} ∪ D)))) ∗
           (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (∅ : gmap obl_id unit)))).
  Proof.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (∅ : gmap obl_id unit)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma othreadG_owns_alloc i (OObls : gmap obl_id unit) k :
    OObls !! k = None →
    (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) OObls)))
    ⊢ |==> (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (<[k := tt]>OObls)))) ∗
           othreadG_owns i k 1.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ k (DfracOwn 1) tt); try done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]".
    rewrite /othreadG_owns. iFrame "Ho".
    done.
  Qed.
  Lemma othreadG_owns_delete i (OObls : gmap obl_id unit) k :
    (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) OObls))) ∗
    othreadG_owns i k 1
    ⊢ |==> (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (delete k OObls)))).
  Proof.
    rewrite -own_op -reservation_map_data_op. apply own_update, reservation_map_update.
    apply gmap_view_delete.
  Qed.
  Lemma othreadG_owns_lookup i OObls k q :
    (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) OObls))) ∗
    othreadG_owns i k q
    ⊢ ⌜ OObls !! k = Some tt ⌝.
  Proof.
    rewrite /othreadG_owns -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H0.
    destruct H0 as (?&_&_&?&?&?). iPureIntro.
    destruct (OObls !! k) eqn:HO.
    - inv H0.  destruct x. done.
    - done.
  Qed.

  Lemma othreadG_owns_frac_op i k q1 q2 q :
    q = (q1 + q2)%Qp →
    othreadG_owns i k q1 ∗ othreadG_owns i k q2 ⊣⊢ othreadG_owns i k q.
  Proof.
    intros; subst. rewrite /othreadG_owns.
    rewrite -own_op -reservation_map_data_op -gmap_view_frag_op dfrac_op_own.
    done.
  Qed.
  Lemma othreadG_owns_div_2 i k q :
    othreadG_owns i k (q/2) ∗ othreadG_owns i k (q/2) ⊣⊢ othreadG_owns i k q.
  Proof. rewrite othreadG_owns_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma othreadG_owns_valid i k q :
    othreadG_owns i k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_owns. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. done.
  Qed.
  Lemma othreadG_owns_valid_2 i k q1 q2 :
    othreadG_owns i k q1 ∗ othreadG_owns i k q2 ⊢ ⌜ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_owns. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. done.
  Qed.

  (** Thread rules *)
  Lemma othreadG_obls_alloc (OThread : gmap positive (gmap obl_id unit)) i :
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

  Lemma othreadG_obls_lookup (OThread : gmap positive (gmap obl_id unit)) i Ψ :
    (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Ψ 1
    ⊢ ⌜ (dom <$> OThread) !! i = Some Ψ ⌝.
  Proof.
    rewrite /othreadG_obls -!own_op. iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H0. destruct H0 as (_&_&?). iPureIntro.
    apply leibniz_equiv, lookup_fmap_Some in H0. destruct H0 as (?&?&?). inv H0. done.
  Qed.
  Lemma othreadG_obls_lookup_frac (OThread : gmap positive (gmap obl_id unit)) i Ψ q :
    (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Ψ q
    ⊢ ∃ Ψ', ⌜ (dom <$> OThread) !! i = Some Ψ' ∧ Ψ ⊆ Ψ' ⌝.
  Proof.
    rewrite /othreadG_obls -!own_op. iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_dfrac_valid_discrete_total in H0. destruct H0 as (?&_&_&?&?&?). iPureIntro.
    destruct x; last done. apply gset_disj_included in H2. eexists. split; last eauto.
    apply lookup_fmap_Some in H0. destruct H0 as (?&?&?). inv H0. done.
  Qed.

  Lemma othreadG_obls_update (OThread : gmap positive (gmap obl_id unit)) i Ψ M :
    (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> OThread)))) ∗
    othreadG_obls i Ψ 1
    ⊢ |==> (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> <[i:=M]>OThread)))) ∗
           othreadG_obls i (dom M) 1.
  Proof.
    rewrite /othreadG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. apply gmap_view_replace. done.
  Qed.
  Lemma othreadG_obls_update_local (OThread : gmap positive (gmap obl_id unit)) i q M1 M2 X1 X2 :
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

  Lemma othread_alloc_threads Θ TP :
    Θ ## TP →
    othread TP
    ⊢ |==> othread (TP ∪ Θ) ∗ ([∗ set] i ∈ Θ, othreadG_elem i ∗ othreadG_obls i ∅ 1 ∗ othreadG_exec i (1/2)%Qp).
  Proof using Type*.
    (* (* FIXME: if not clear Ξd, used but not delcared error at Qed *) *)
    (* clear Ξd. *)
    revert TP. pattern Θ. revert Θ. apply set_ind.
    { solve_proper. }
    { iIntros (??) "T". rewrite union_empty_r_L. iFrame. by iModIntro. }
    iIntros (i Θ Nin IH TP Disj) "T".
    iMod (IH with "T") as "(T& Hs)"; first set_solver.
    iMod (othread_alloc_thread i with "T") as "(T& Hi)"; first set_solver.
    iModIntro. replace ({[i]} ∪ (TP ∪ Θ)) with (TP ∪ ({[i]} ∪ Θ)); last set_solver.
    iFrame. iApply big_sepS_union; first set_solver. rewrite big_sepS_singleton. iFrame.
  Qed.

  Lemma othread_alloc_obl_1 TP i Ψ q k :
    oblG_live k (1/2)%Qp ∗ oblG_live k (1/2)%Qp ∗ oblG_owner k i (1/2/2)%Qp ∗ othread TP ∗ othreadG_obls i Ψ q
    ⊢ |==> ⌜k ∉ Ψ⌝ ∗ oblG_live k (1/2)%Qp ∗ oblG_live k (1/2/2)%Qp ∗
           othread TP ∗ othreadG_obls i ({[k]} ∪ Ψ) q ∗ othreadG_owns i k 1.
  Proof using Type*.
    iIntros "(Os0 & Os & Oo & Hthread & Ho)".
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
    iMod (othreadG_owns_alloc _ _ _ Hluk with "His") as "[His Hw]".
    iFrame "Hw".
    iMod (othreadG_obls_update_local _ _ _ OObls (<[k:=tt]>OObls) _ ({[k]} ∪ Ψ) with "[HO Ho]") as "[HO Ho]";
      [eauto | | iFrame |].
    { rewrite dom_insert_L. apply gset_disj_alloc_local_update. apply not_elem_of_dom in Hluk. set_solver. }
    iFrame "Ho". iModIntro. iSplitR.
    { iPureIntro. apply not_elem_of_dom in Hluk. rewrite Hm in Hluk. set_solver. }
    iExists (<[i:=(<[k:=tt]>OObls)]>OThread). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HS HX HO". iSplitL "HE".
    { rewrite !fmap_insert. rewrite insert_id; first done. rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq OThread i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame "Hm Hix His". iApply (big_sepM_insert _ _ k); first done. iFrame.
  Qed.
  Lemma othread_alloc_obl Ω TP i Ψ q k :
    osat Ω ∗ othread TP ∗ othreadG_obls i Ψ q ∗ oblG_elem k ∗ oblG_live k (1/2)%Qp ∗ oblG_owner k i (1/2/2)%Qp
    ⊢ |==> osat Ω ∗ othread TP ∗ ⌜k ∉ Ψ⌝ ∗ othreadG_obls i ({[k]} ∪ Ψ) q ∗ othreadG_owns i k 1 ∗ oblG_live k (1/2/2)%Qp.
  Proof.
    iIntros "(Osat & Hthread & Ho & #He & Os & Oo)".
    iPoseProof (osat_live_open with "[Osat Os]") as "(Os & Os0 & Osacc)"; first by iFrame.
    iMod (othread_alloc_obl_1 with "[$]") as "(%& Os0 & Os1 & Hthread & Ho & Hw)".
    iModIntro. iFrame. iSplitL; first by iApply "Osacc". done.
  Qed.

  Lemma othread_obls_owns_elem TP i Ψ k q :
    othread TP ∗ othreadG_obls i Ψ 1 ∗ othreadG_owns i k q
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

  Lemma othread_delete_obl_frac TP i Ψ q k :
    k ∈ Ψ →
    othread TP ∗ othreadG_obls i Ψ q ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ othreadG_obls i (Ψ ∖ {[k]}) q ∗
           oblG_live k (1/2/2)%Qp ∗ oblG_owner k i (1 / 2 / 2)%Qp.
  Proof using Type*.
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
  Lemma othread_delete_obl TP i Ψ k :
    othread TP ∗ othreadG_obls i Ψ 1 ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ othreadG_obls i (Ψ ∖ {[k]}) 1 ∗
           oblG_live k (1/2/2)%Qp ∗ oblG_owner k i (1 / 2 / 2)%Qp.
  Proof using Type*.
    iIntros "(Hthread & Ho & Hw)". iPoseProof (othread_obls_owns_elem with "[$]") as "%Hkin".
    iApply (othread_delete_obl_frac with "[$]"). auto.
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

  Lemma othread_live_open TP i k q :
    othread TP ∗ othreadG_elem i ∗ othreadG_owns i k q
    ⊢ othreadG_owns i k q ∗
    (oblG_live k (1/2/2)%Qp ∗ oblG_owner k i (1 / 2 / 2)%Qp) ∗
    ((oblG_live k (1/2/2)%Qp ∗ oblG_owner k i (1 / 2 / 2)%Qp) -∗ othread TP).
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

  Lemma othread_obls_open TP i k Ψ :
    k ∈ Ψ →
    othread TP ∗ othreadG_elem i ∗ othreadG_obls i Ψ 1
    ⊢ othreadG_obls i Ψ 1 ∗
    (oblG_live k (1/2/2) ∗ oblG_owner k i (1/2/2)) ∗
    ((oblG_live k (1/2/2) ∗ oblG_owner k i (1/2/2)) -∗ othread TP).
  Proof.
    iIntros (Ink) "(Hthread & He & Hobls)". 
    iPoseProof (othread_elem with "[Hthread He]") as "%Hin"; first iFrame.
    rewrite /othread -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    assert (Hlui : is_Some (OThread !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (OObls&Hlui).
    iPoseProof (othreadG_obls_lookup with "[HO Hobls]") as "%"; first iFrame.
    rewrite lookup_fmap in H0. rewrite Hlui in H0. inv H0.
    assert (Hluk : is_Some (OObls !! k)) by (by apply elem_of_dom).
    destruct Hluk as (fk&Hluk).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (big_sepM_delete _ _ _ _ Hluk with "Him") as "[Hk Him]".
    iDestruct "Hk" as "[Bl Hk]". iFrame "Bl Hk Hobls". iIntros "Bl".
    iExists OThread. iFrame. iSplitR; first done.
    iApply (big_sepM_delete _ _ _ _ Hlui). iFrame.
    iApply (big_sepM_delete _ _ _ _ Hluk). iFrame.
  Qed.

End othread.

(* Allocation of initial invariant. *)
Lemma othread_alloc `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGpreS Σ} :
  ⊢ |==> ∃ _ : othreadGS Σ, othread ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR obl_id unitUR)) ⊤)) as (γS) "HS";
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
