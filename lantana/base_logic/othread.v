From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.algebra Require Export wfocm.
From lantana.base_logic Require Export osat.

(** The ghost state for the obligations of threads *)
Module othreadGS.

  (* Assumes thread ids are positive *)
  Class othreadGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadGpreS {
        othreadGpreS_owns : inG Σ (reservation_mapUR (gmap_viewR oid (unitUR)));
        othreadGpreS_obls : inG Σ (gmap_viewR positive (gsetUR oid));
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
    #[GFunctor (reservation_mapUR (gmap_viewR oid (unitUR)));
      GFunctor (gmap_viewR positive (gsetUR oid));
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

(* Owns: thread [i] currently owns obligation [k]. *)
Definition othreadG_owns `{SI : indexT} `{!othreadGS Σ} (i : positive) (k : oid) (q : Qp) : iProp Σ :=
  own owns_name (reservation_map_data i (gmap_view_frag k (DfracOwn q) ())).
Global Typeclasses Opaque othreadG_owns.
Global Instance: Params (@othreadG_owns) 3 := {}.

Local Definition othreadG_owns_token_id `{SI : indexT} `{!othreadGS Σ} TP : iProp Σ :=
  (own owns_name (reservation_map_token (A:=gmap_viewR oid (unitUR)) (⊤ ∖ gset_to_coPset TP))).

Local Definition othreadG_owns_auth_obls `{SI : indexT} `{!othreadGS Σ}
  i (TObls : gmap oid unit) : iProp Σ :=
  (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (TObls)))).

(* Obls: the live obligations of thread [i]. The set is empty once the thread has
   terminated. *)
Definition othreadG_obls `{SI : indexT} `{!othreadGS Σ} (i : positive) (G : oids) : iProp Σ :=
  own obls_name (gmap_view_frag i (DfracOwn 1) (G)).
Global Typeclasses Opaque othreadG_obls.
Global Instance: Params (@othreadG_obls) 3 := {}.

Local Definition othreadG_obls_auth_id `{SI : indexT} `{!othreadGS Σ}
  (Tgls : gmap positive (gmap oid unit)) : iProp Σ :=
  (own obls_name (gmap_view_auth (DfracOwn 1) (dom <$> Tgls))).

(* Exec: tracks whether thread is executing or terminated *)
Definition othreadG_exec `{SI : indexT} `{!othreadGS Σ} (i : positive) (q : Qp) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN{#q} 0)).
Global Typeclasses Opaque othreadG_exec.
Global Instance: Params (@othreadG_exec) 3 := {}.

Definition othreadG_done_auth `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN 1)).
Global Typeclasses Opaque othreadG_done_auth.
Global Instance: Params (@othreadG_done_auth) 3 := {}.

Definition othreadG_done `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (◯MN 1)).
Global Typeclasses Opaque othreadG_done.
Global Instance: Params (@othreadG_done) 3 := {}.

Local Definition othreadG_exec_token_id `{SI : indexT} `{!othreadGS Σ} TP : iProp Σ :=
  (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset TP))).

(* Elem: thread [i] has been allocated. *)
Definition othreadG_elem `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own elem_name (gmap_view_frag i DfracDiscarded ()).
Global Typeclasses Opaque othreadG_elem.
Global Instance: Params (@othreadG_elem) 3 := {}.

Local Definition othreadG_elem_auth_id `{SI : indexT} `{!othreadGS Σ}
  (Tgls : gmap positive (gmap oid unit)) : iProp Σ :=
  (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> Tgls))).

(* Global invariant for threads' obligations. *)
Definition othread `{SI : indexT} {Σ} `{!@osatGS.osatGS _ Σ} `{!othreadGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (Tgls : gmap positive (gmap oid unit)),
        (⌜ dom Tgls = TP ⌝) ∗
        othreadG_owns_token_id TP ∗
        othreadG_obls_auth_id Tgls ∗
        othreadG_exec_token_id TP ∗
        othreadG_elem_auth_id Tgls ∗
        ([∗ map] i ↦ TObls ∈ Tgls,
           (othreadG_exec i (1/2/2)%Qp ∨ (othreadG_done_auth i ∗ othreadG_obls i ∅)) ∗
           othreadG_owns_auth_obls i TObls ∗
           ([∗ map] k ↦ _ ∈ TObls, oblG_owner k i (1/2/2/2/2)%Qp)
        )
    )%I.

(* Global invariant that relates obligations to threads: each obligation is owned by an
   allocated thread, or discharged. *)
Definition oassigned `{SI : indexT} {Σ} `{!@osatGS.osatGS _ Σ} `{!othreadGS Σ}
  (Gls : oids) : iProp Σ :=
  locked
    ([∗ set] k ∈ Gls,
       oblG_elem k ∗
       ((∃ i, oblG_owner k i (1/2/2/2/2)%Qp ∗ othreadG_owns i k (1/2/2)%Qp ∗ othreadG_elem i) ∨
          (oblG_discharged k)))%I.

Section othread.
  Context `{SI : indexT} `{OSAT : !osatGS.osatGS Σ} `{!othreadGS Σ} `{OMF : !ord_mono_fun_class}.

  (* Owns *)
  Global Instance othreadG_owns_timeless i k q : Timeless (othreadG_owns i k q).
  Proof. rewrite /othreadG_owns. apply _. Qed.

  Global Instance othreadG_owns_fractional i k :
    Fractional (othreadG_owns i k).
  Proof.
    rewrite /othreadG_owns. intros p q.
    by rewrite -own_op -!reservation_map_data_op -gmap_view_frag_op.
  Qed.
  Global Instance othreadG_owns_as_fractional i k q :
    AsFractional (othreadG_owns i k q) (othreadG_owns i k) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance othreadG_owns_token_id_timeless TP : Timeless (othreadG_owns_token_id TP).
  Proof. rewrite /othreadG_owns_token_id. apply _. Qed.
  Local Instance othreadG_owns_auth_obls_timeless i TObls : Timeless (othreadG_owns_auth_obls i TObls).
  Proof. rewrite /othreadG_owns_auth_obls. apply _. Qed.

  (* Obls *)
  Global Instance othreadG_obls_timeless i G : Timeless (othreadG_obls i G).
  Proof. rewrite /othreadG_obls. apply _. Qed.

  Local Instance othreadG_obls_auth_id_timeless Tgls : Timeless (othreadG_obls_auth_id Tgls).
  Proof. rewrite /othreadG_obls_auth_id. apply _. Qed.

  (* Exec *)
  Global Instance othreadG_exec_timeless i q : Timeless (othreadG_exec i q).
  Proof. rewrite /othreadG_exec. apply _. Qed.

  Global Instance othreadG_exec_fractional i :
    Fractional (othreadG_exec i).
  Proof.
    rewrite /othreadG_exec. intros p q.
    by rewrite -own_op -!reservation_map_data_op -mono_nat_auth_dfrac_op.
  Qed.
  Global Instance othreadG_exec_as_fractional i q :
    AsFractional (othreadG_exec i q) (othreadG_exec i) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance othreadG_done_auth_timeless i : Timeless (othreadG_done_auth i).
  Proof. rewrite /othreadG_done_auth. apply _. Qed.

  Global Instance othreadG_done_persistent i : Persistent (othreadG_done i).
  Proof. rewrite /othreadG_done. apply _. Qed.
  Global Instance othreadG_done_timeless i : Timeless (othreadG_done i).
  Proof. rewrite /othreadG_done. apply _. Qed.

  Local Instance othreadG_exec_token_id_timeless TP : Timeless (othreadG_exec_token_id TP).
  Proof. rewrite /othreadG_exec_token_id. apply _. Qed.

  (* Elem *)
  Global Instance othreadG_elem_persistent i : Persistent (othreadG_elem i).
  Proof. rewrite /othreadG_elem. apply _. Qed.
  Global Instance othreadG_elem_timeless i : Timeless (othreadG_elem i).
  Proof. rewrite /othreadG_elem. apply _. Qed.

  Local Instance othreadG_elem_auth_id_timeless Tgls : Timeless (othreadG_elem_auth_id Tgls).
  Proof. rewrite /othreadG_elem_auth_id. apply _. Qed.

  (* Invs *)
  Global Instance othread_timeless TP : Timeless (othread TP).
  Proof. rewrite /othread -lock. apply _. Qed.

  Global Instance oassigned_timeless Gls : Timeless (oassigned Gls).
  Proof. rewrite /oassigned -lock. apply _. Qed.

  (** Elem rules *)
  Lemma othreadG_elem_alloc (Tgls : gmap positive (gmap oid unit)) i M :
    Tgls !! i = None →
    othreadG_elem_auth_id Tgls
    ⊢  |==> othreadG_elem_auth_id (<[i:=M]>Tgls) ∗
         othreadG_elem i.
  Proof.
    rewrite /othreadG_elem_auth_id.
    iIntros (Hi) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracDiscarded) ()); try done.
      rewrite !lookup_fmap Hi. done.
    }
    iDestruct "H" as "[H He]". rewrite /othreadG_elem. iFrame "He".
    rewrite fmap_insert. done.
  Qed.

  Lemma othreadG_elem_elem i (Tgls : gmap positive (gmap oid unit)) :
    othreadG_elem_auth_id Tgls ∗ othreadG_elem i
    ⊢ ⌜ i ∈ dom Tgls ⌝.
  Proof.
    rewrite /othreadG_elem_auth_id /othreadG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro. apply elem_of_dom_2 in H. by rewrite dom_fmap_L in H.
  Qed.

  (** Owns rules *)
  Lemma othreadG_owns_alloc_id D i :
    i ∉ D →
    othreadG_owns_token_id D
    ⊢ |==> othreadG_owns_token_id ({[i]} ∪ D) ∗
        othreadG_owns_auth_obls i ∅.
  Proof.
    rewrite /othreadG_owns_token_id /othreadG_owns_auth_obls.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (∅ : gmap oid unit)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma othreadG_owns_alloc i (TObls : gmap oid unit) k :
    TObls !! k = None →
    othreadG_owns_auth_obls i TObls
    ⊢ |==> othreadG_owns_auth_obls i (<[k:=()]>TObls) ∗
        othreadG_owns i k 1.
  Proof.
    rewrite /othreadG_owns_auth_obls /othreadG_owns.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ k (DfracOwn 1) ()); try done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]".
    iFrame "Ho". done.
  Qed.

  Lemma othreadG_owns_delete i (TObls : gmap oid unit) k :
    othreadG_owns_auth_obls i TObls ∗ othreadG_owns i k 1
    ⊢ |==> othreadG_owns_auth_obls i (delete k TObls).
  Proof.
    rewrite /othreadG_owns_auth_obls /othreadG_owns -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update. apply gmap_view_delete.
  Qed.

  Lemma othreadG_owns_lookup i TObls k q :
    othreadG_owns_auth_obls i TObls ∗ othreadG_owns i k q
    ⊢ ⌜ TObls !! k = Some tt ⌝.
  Proof.
    rewrite /othreadG_owns_auth_obls /othreadG_owns -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H.
    destruct H as (?&_&_&?&?&?).
    iPureIntro. by destruct x.
  Qed.

  Lemma othreadG_owns_valid i k q :
    othreadG_owns i k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_owns. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. done.
  Qed.

  (** Obls rules *)
  Lemma othreadG_obls_alloc Tgls i :
    Tgls !! i = None →
    othreadG_obls_auth_id Tgls
    ⊢ |==> othreadG_obls_auth_id (<[i:=∅]>Tgls) ∗
          othreadG_obls i ∅.
  Proof.
    rewrite /othreadG_obls_auth_id /othreadG_obls.
    iIntros (Hi) "H".
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracOwn 1) (∅ : oids)); try done.
      rewrite !lookup_fmap Hi. done. }
    iDestruct "H" as "[H Ho]". iFrame "Ho".
    rewrite !fmap_insert. done.
  Qed.

  Lemma othreadG_obls_lookup Tgls i G :
    othreadG_obls_auth_id Tgls ∗
    othreadG_obls i G
    ⊢ ⌜ (dom <$> Tgls) !! i = Some G ⌝.
  Proof.
    rewrite /othreadG_obls_auth_id /othreadG_obls -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H. destruct H as (_&_&?).
    iPureIntro. apply leibniz_equiv, lookup_fmap_Some in H. destruct H as (?&?&?).
    rewrite lookup_fmap H0. inv H. done.
  Qed.

  Lemma othreadG_obls_update Tgls i G M :
    othreadG_obls_auth_id Tgls ∗
    othreadG_obls i G
    ⊢ |==> othreadG_obls_auth_id (<[i:=M]>Tgls) ∗
        othreadG_obls i (dom M).
  Proof.
    rewrite /othreadG_obls_auth_id /othreadG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. apply gmap_view_replace. done.
  Qed.

  (** Exec rules *)
  Lemma othreadG_exec_done_false k q :
    othreadG_exec k q ∗ othreadG_done k ⊢ False.
  Proof.
    rewrite /othreadG_exec /othreadG_done. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma othreadG_exec_to_done k :
    othreadG_exec k 1 ⊢ |==> othreadG_done_auth k.
  Proof.
    rewrite /othreadG_exec /othreadG_done_auth.
    apply own_update.
    apply reservation_map_update. apply mono_nat_update. auto.
  Qed.
  Lemma othreadG_done_auth_done k :
    othreadG_done_auth k ⊢ othreadG_done k.
  Proof.
    rewrite /othreadG_done_auth /othreadG_done.
    apply own_mono.
    apply reservation_map_data_mono. apply mono_nat_included.
  Qed.

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
    othreadG_exec_token_id D
    ⊢ |==> othreadG_exec_token_id ({[k]} ∪ D) ∗
        othreadG_exec k 1.
  Proof.
    rewrite /othreadG_exec_token_id /othreadG_exec.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN 0) with "Htk") as "[Htk >H]"; auto.
    { apply mono_nat_auth_valid. }
    by iFrame.
  Qed.

  (** othread rules *)
  Lemma othread_elem i TP :
    othread TP ∗ othreadG_elem i ⊢ ⌜i ∈ TP⌝.
  Proof.
    rewrite /othread -!lock. iIntros "(O & He)".
    iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_elem_elem with "[$]") as "%".
    by rewrite -Hdom.
  Qed.

  Lemma othread_alloc_thread i TP :
    i ∉ TP →
    othread TP
    ⊢ |==> othread ({[i]} ∪ TP) ∗
        othreadG_elem i ∗ othreadG_obls i ∅ ∗ othreadG_exec i (1/2 + 1/2/2)%Qp.
  Proof.
    iIntros (Hi) "O".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    assert (Hlu : Tgls !! i = None).
    { apply not_elem_of_dom. rewrite Hdom. auto. }
    iMod (othreadG_elem_alloc _ i ∅ with "HE") as "[HE He]"; first auto.
    iMod (othreadG_owns_alloc_id with "HO") as "[HO Ho]"; first done.
    iMod (othreadG_obls_alloc _ i with "HB") as "[HB Hb]"; first auto.
    iMod (othreadG_exec_alloc _ i with "HX") as "[HX Hx]"; first auto.
    iDestruct "Hx" as "[Hx [Hx' Hx0]]". iCombine "Hx Hx'" as "Hx".
    iModIntro. iFrame "He Hb Hx". iExists (<[i:=∅]>Tgls). iFrame "HE HO HB HX".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom. done. }
    iApply big_sepM_insert; first done.
    iFrame. done.
  Qed.

  Lemma othread_alloc_threads Θ TP :
    Θ ## TP →
    othread TP
    ⊢ |==> othread (TP ∪ Θ) ∗
        ([∗ set] i ∈ Θ, othreadG_elem i ∗ othreadG_obls i ∅ ∗ othreadG_exec i (1/2 + 1/2/2)%Qp).
  Proof.
    revert TP. pattern Θ. revert Θ. apply set_ind.
    { solve_proper. }
    { iIntros (??) "T". rewrite union_empty_r_L. iFrame. by iModIntro. }
    iIntros (i Θ Nin IH TP Disj) "O".
    iMod (IH with "O") as "(O& Hs)"; first set_solver.
    iMod (othread_alloc_thread i with "O") as "(O& Hi)"; first set_solver.
    iModIntro. replace ({[i]} ∪ (TP ∪ Θ)) with (TP ∪ ({[i]} ∪ Θ)) by set_solver.
    iFrame. iApply big_sepS_union; first set_solver. rewrite big_sepS_singleton. iFrame.
  Qed.

  Local Lemma othread_alloc_obl_1 j TP i G k :
    oblG_owner k j (1/2 + 1/2/2/2 + 1/2/2 + 1/2/2/2/2)%Qp ∗
    othread TP ∗ othreadG_obls i G ∗ oblG_owner k i (1/2/2/2/2)%Qp
    ⊢ |==> ⌜k ∉ G⌝ ∗ oblG_owner k j (1/2 + 1/2/2/2 + 1/2/2 + 1/2/2/2/2)%Qp ∗
        othread TP ∗ othreadG_obls i ({[k]} ∪ G) ∗ othreadG_owns i k 1.
  Proof.
    iIntros "(Go0& O& Obs& Go)".
    iPoseProof (oblG_owner_agree with "[$Go0 $Go]") as "(%EQ& %F)". subst j. clear F.
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup with "[$HB $Obs]") as "%Hlui0".
    assert (Hlui : ∃ m, dom m = G ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. destruct Hlui0 as (?&?&?). eauto. }
    destruct Hlui as (TObls& Hm& Hlui).
    iAssert (⌜ TObls !! k = None ⌝)%I with "[Go0 Go Hm]" as "%Hluk".
    { destruct (TObls !! k) eqn:LU; last done. iExFalso.
      iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi _]".
      iDestruct "Hi" as "(Hix & His & Him)".
      iDestruct (big_sepM_delete _ _ k _ LU with "Him") as "[Hk Him]".
      iDestruct "Hk" as "Go1".
      iDestruct "Go0" as "(((Go0& Go2)& Go3)& Go4)".
      iCombine "Go1 Go" as "Go". iCombine "Go2 Go" as "Go". iCombine "Go3 Go" as "Go".
      iCombine "Go0 Go" as "Go". iCombine "Go Go4" as "Go".
      iPoseProof (oblG_owner_valid with "Go") as "%". done.
    }
    iFrame "Go0".
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iMod (othreadG_owns_alloc _ _ _ Hluk with "His") as "[His Hw]".
    iFrame "Hw".
    iMod (othreadG_obls_update _ _ _ (<[k:=tt]>TObls) with "[$HB $Obs]") as "[HB Obs]".
    rewrite dom_insert_L Hm. iFrame "Obs". iModIntro. iSplitR.
    { iPureIntro. apply not_elem_of_dom in Hluk. rewrite Hm in Hluk. set_solver. }
    iExists (<[i:=(<[k:=tt]>TObls)]>Tgls). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HB HX HO". iSplitL "HE".
    { rewrite /othreadG_elem_auth_id. rewrite !fmap_insert insert_id; first done.
      rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq Tgls i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame "Hm Hix His". iApply (big_sepM_insert _ _ k); first done. iFrame.
  Qed.
  Lemma othread_alloc_obl Ω TP i G k :
    osat Ω ∗ othread TP ∗
    othreadG_obls i G ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp
    ⊢ |==> osat Ω ∗ othread TP ∗
        ⌜k ∉ G⌝ ∗ othreadG_obls i ({[k]} ∪ G) ∗
        othreadG_owns i k 1 ∗ oblG_owner k i (1/2 + 1/2/2/2 + 1/2/2/2/2)%Qp.
  Proof.
    iIntros "(S& O& Obs& #Ge& Go)".
    iDestruct "Go" as "(Go& (Go1& Go2))". iDestruct "Go2" as "(Go2& Go3)".
    iPoseProof (osat_open_owner with "[$S $Ge $Go]") as "(Go& (%& Gl'& Go')& ACC)".
    iCombine "Go Go1 Go' Go2" as "Go". rewrite !Qp.add_assoc.
    iMod (othread_alloc_obl_1 with "[$Go $O $Obs $Go3]") as "(%Nin& Go& O& Obs& Oo)".
    iDestruct "Go" as "((Go& Go')& Go0)". iPoseProof ("ACC" with "[$Gl' $Go']") as "S".
    iCombine "Go Go0" as "Go". iFrame. done.
  Qed.

  Lemma othread_obls_owns_elem TP i G k q :
    othread TP ∗ othreadG_obls i G ∗ othreadG_owns i k q
    ⊢ ⌜ k ∈ G ⌝.
  Proof.
    iIntros "(O& Ho& Hw)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup with "[$HB $Ho]") as "%".
    assert (Hlui : ∃ m, dom m = G ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in H. eauto. }
    destruct Hlui as (TObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[$His $Hw]") as "%Hluk".
    iPureIntro. rewrite -Hm. by apply elem_of_dom.
  Qed.

  Lemma othread_delete_obl TP i G k :
    othread TP ∗ othreadG_obls i G ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ othreadG_obls i (G ∖ {[k]}) ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros "(O & Ho & Hw)". iPoseProof (othread_obls_owns_elem with "[$]") as "%Hkin".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup with "[$HB $Ho]") as "%Hlui0".
    assert (Hlui : ∃ m, dom m = G ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. eauto. }
    destruct Hlui as (TObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[$His $Hw]") as "%Hluk".
    iMod (othreadG_owns_delete with "[$His $Hw]") as "His".
    iMod (othreadG_obls_update _ _ _ (delete k TObls) with "[$HB $Ho]") as "[HB Ho]".
    rewrite dom_delete_L Hm. iFrame "Ho".
    iDestruct (big_sepM_delete _ _ k _ Hluk with "Him") as "[Hik Him]".
    iDestruct "Hik" as "$".
    iModIntro. iExists (<[i:=(delete k TObls)]>Tgls). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HO HX HB". iSplitL "HE".
    { rewrite /othreadG_elem_auth_id. rewrite !fmap_insert. rewrite insert_id; first done.
      rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq Tgls i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame.
  Qed.

  Lemma othread_exec_to_done TP i :
    othread TP ∗ othreadG_exec i (1/2 + 1/2/2)%Qp ∗ othreadG_obls i ∅
    ⊢ |==> othread TP ∗ othreadG_done i.
  Proof.
    iIntros "(O& Hx& Ho)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup with "[$HB $Ho]") as "%".
    assert (Hlui : Tgls !! i = Some ∅).
    { rewrite lookup_fmap_Some in H. destruct H as (?&?&?). apply dom_empty_inv_L in H. by subst. }
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix _]] & His & Him)"; last first.
    { iExFalso. iPoseProof (othreadG_done_auth_done with "[$]") as "Hxt".
      iPoseProof (othreadG_exec_done_false with "[$]") as "%F". done. }
    iMod (othreadG_exec_to_done with "[Hx Hix]") as "Hx".
    { iCombine "Hx Hix" as "Hx". rewrite -Qp.add_assoc !Qp.div_2. done. }
    iPoseProof (othreadG_done_auth_done with "Hx") as "#Hxt".
    iModIntro. iSplitL; last done.
    iExists Tgls. iSplitR; first done. iFrame "HO HB HX HE".
    iApply (big_sepM_delete _ _ i _ Hlui). iFrame. iRight. iFrame.
  Qed.

  Lemma othread_done_open TP i :
    othread TP ∗ othreadG_elem i ∗ othreadG_done i
    ⊢ othreadG_obls i ∅ ∗ (othreadG_obls i ∅ -∗ othread TP).
  Proof.
    iIntros "(O & #He & #Hx)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_elem_elem with "[$]") as "%Hini".
    assert (Hlui : ∃ m, Tgls !! i = Some m).
    { rewrite elem_of_dom in Hini. eauto. }
    destruct Hlui as (TObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix Ho]] & His & Him)".
    { iExFalso. iPoseProof (othreadG_exec_done_false with "[$]") as "%F". done. }
    iFrame "Ho". iIntros "Ho".
    iExists Tgls. iSplitR; first done. iFrame "HO HB HX HE".
    iApply (big_sepM_delete _ _ i _ Hlui). iFrame. iRight. iFrame.
  Qed.

  Lemma othread_owns_open TP i k q :
    othread TP ∗ othreadG_elem i ∗ othreadG_owns i k q
    ⊢ othreadG_owns i k q ∗
    (oblG_owner k i (1/2/2/2/2)%Qp) ∗
    ((oblG_owner k i (1/2/2/2/2)%Qp) -∗ othread TP).
  Proof.
    iIntros "(O & #He & Hw)".
    iPoseProof (othread_elem with "[$O $He]") as "%Hin".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    assert (Hlui : is_Some (Tgls !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (TObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[$His $Hw]") as "%Hluk".
    iPoseProof (big_sepM_delete _ _ _ _ Hluk with "Him") as "[Hk Him]".
    iFrame "Hw Hk". iIntros "Hk". iExists Tgls. iFrame "HO HB HX HE".
    iSplit; first done. iApply (big_sepM_delete _ _ _ _ Hlui). iFrame.
    iApply (big_sepM_delete _ _ _ _ Hluk). iFrame.
  Qed.

  Lemma othread_obls_open TP i k G :
    k ∈ G →
    othread TP ∗ othreadG_elem i ∗ othreadG_obls i G
    ⊢ othreadG_obls i G ∗
    (oblG_owner k i (1/2/2/2/2)%Qp) ∗
    ((oblG_owner k i (1/2/2/2/2)%Qp) -∗ othread TP).
  Proof.
    iIntros (Ink) "(O& #He& Hobls)". 
    iPoseProof (othread_elem with "[$O $He]") as "%Hin".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    assert (Hlui : is_Some (Tgls !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (TObls&Hlui).
    iPoseProof (othreadG_obls_lookup with "[$HB $Hobls]") as "%".
    rewrite lookup_fmap in H. rewrite Hlui in H. inv H.
    assert (Hluk : is_Some (TObls !! k)).
    { apply elem_of_dom. set_solver. }
    destruct Hluk as (fk&Hluk).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (big_sepM_delete _ _ _ _ Hluk with "Him") as "[Hk Him]".
    iFrame "Hk Hobls". iIntros "Bl".
    iExists Tgls. iFrame. iSplitR; first done.
    iApply (big_sepM_delete _ _ _ _ Hlui). iFrame.
    iApply (big_sepM_delete _ _ _ _ Hluk). iFrame.
  Qed.

  (** oassigned rules *)
  Lemma oassigned_add_obl Gls k :
    oassigned Gls ∗
    (oblG_elem k ∗ ((∃ i, oblG_owner k i (1/2/2/2/2) ∗ othreadG_owns i k (1/2/2) ∗ othreadG_elem i) ∨ oblG_discharged k))
    ⊢ oassigned ({[k]} ∪ Gls).
  Proof.
    iIntros "(A& H)". rewrite /oassigned -!lock. destruct (decide (k ∈ Gls)).
    - iPoseProof (big_sepS_delete _ _ _ e with "A") as "[_ A]".
      replace ({[k]} ∪ Gls) with ({[k]} ∪ (Gls ∖ {[k]})).
      2:{ rewrite -union_difference_L; set_solver. }
      iApply big_sepS_insert.
      { set_solver. }
      iFrame.
    - iApply big_sepS_insert; first auto. iFrame.
  Qed.

  Lemma oassigned_delete_obl Gls k :
    k ∈ Gls →
    oassigned Gls
    ⊢ oassigned (Gls ∖ {[k]}) ∗
    (oblG_elem k ∗ ((∃ i, oblG_owner k i (1/2/2/2/2) ∗ othreadG_owns i k (1/2/2) ∗ othreadG_elem i) ∨ oblG_discharged k)).
  Proof.
    rewrite /oassigned -!lock. iIntros (INk) "A".
    iPoseProof (big_sepS_delete with "A") as "[$ $]". auto.
  Qed.

  Lemma othread_assigned_obls_lookup Ω TP k a i G :
    Ω !! k = Some (obl_assigned a i) →
    osat Ω ∗ othread TP ∗ oassigned (dom Ω) ∗ othreadG_obls i G
    ⊢ ⌜ k ∈ G ⌝.
  Proof.
    rewrite /oassigned -lock. iIntros (LUOk) "(S& O& A& Tbs)".
    iPoseProof (big_sepS_delete _ _ k with "A") as "[A _]".
    { apply elem_of_dom_2 in LUOk. auto. }
    iDestruct "A" as "(#Gek& [(%& Gok& Ook& #Tei) | #Guk])".
    - iPoseProof (osat_lookup_owner with "[$S $Gek $Gok]") as "(%&%)".
      rewrite LUOk in H. inv H. iApply (othread_obls_owns_elem with "[$O $Tbs $Ook]").
    - iPoseProof (osat_lookup_discharged with "[$S $Gek $Guk]") as "%H".
      rewrite LUOk in H. inv H.
  Qed.

  Lemma othread_obls_lookup Ω TP k i G :
    k ∈ G →
    osat Ω ∗ othread TP ∗ othreadG_elem i ∗ othreadG_obls i G ∗ oblG_elem k
    ⊢ ∃ a, ⌜ Ω !! k = Some (obl_assigned a i) ⌝.
  Proof.
    iIntros (Ink) "(S& O& #Oei& Tbs& #Gek)".
    iPoseProof (othread_obls_open with "[$O $Oei $Tbs]") as "(Tbs& Go& Acc)". 1: eauto.
    iPoseProof (osat_lookup_owner with "[$S $Gek $Go]") as "(%& %)". eauto.
  Qed.

  Lemma othread_assigned_thread_elem Ω TP k a i :
    Ω !! k = Some (obl_assigned a i) →
    osat Ω ∗ othread TP ∗ oassigned (dom Ω)
    ⊢ ⌜i ∈ TP⌝.
  Proof.
    rewrite /oassigned -lock. iIntros (LUOk) "(S& O& A)".
    iPoseProof (big_sepS_delete _ _ k with "A") as "[A _]".
    { apply elem_of_dom_2 in LUOk. auto. }
    iDestruct "A" as "(#Gek& [(%& Gok& Ook& #Tei) | #Guk])".
    - iPoseProof (osat_lookup_owner with "[$S $Gek $Gok]") as "%". destruct H. rewrite LUOk in H. inv H.
      iPoseProof (othread_elem with "[$O $Tei]") as "%".  auto.
    - iPoseProof (osat_lookup_discharged with "[$S $Gek $Guk]") as "%". rewrite LUOk in H. inv H.
  Qed.

  Lemma othread_assigned_done_false Ω TP k a i :
    Ω !! k = Some (obl_assigned a i) →
    osat Ω ∗ othread TP ∗ oassigned (dom Ω) ∗ othreadG_elem i ∗ othreadG_done i ⊢ False.
  Proof.
    iIntros (LUk) "(S& O& A& #He & #Hx)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_elem_elem with "[$HE $He]") as "%Hini".
    assert (Hlui : ∃ m, Tgls !! i = Some m).
    { rewrite elem_of_dom in Hini. eauto. }
    destruct Hlui as (TObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix Ho]] & His & Him)".
    { iExFalso. iPoseProof (othreadG_exec_done_false with "[$Hix $Hx]") as "%F". done. }
    iPoseProof (othreadG_obls_lookup with "[$HB $Ho]") as "%LUempty".
    rewrite /oassigned -lock. iPoseProof (big_sepS_delete _ _ k with "A") as "[A _]".
    { apply elem_of_dom_2 in LUk. auto. }
    iDestruct "A" as "(#Gek& [(%& Gok& Ook& #Tei) | #Guk])".
    - iPoseProof (osat_lookup_owner with "[$S $Gek $Gok]") as "(%&%)". rewrite LUk in H. inv H.
      iPoseProof (othreadG_owns_lookup with "[$His $Ook]") as "%".
      rewrite lookup_fmap_Some in LUempty. destruct LUempty as (?&?&?). apply dom_empty_inv_L in H0. subst x.
      rewrite Hlui in H1. inv H1.
    - iPoseProof (osat_lookup_discharged with "[$S $Gek $Guk]") as "%H".
      rewrite LUk in H. inv H.
  Qed.

End othread.

(* Allocation of initial invariant. *)
Lemma othread_alloc `{SI : indexT} {Σ}
  `{!@osatGS.osatGS _ Σ} `{!othreadGpreS Σ} :
  ⊢ |==> ∃ _ : othreadGS Σ, othread ∅ ∗ oassigned ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR oid (unitUR))) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive (gsetUR _))) as (γO) "HO";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γX) "HX";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive unitUR)) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iModIntro. iExists (OthreadG SI _ _ γS γO γX γE).
  rewrite /othread /oassigned -!lock. iSplitL "HS HO HX HE".
  { iExists ∅. iSplitR; first done. replace (⊤ : coPset) with (⊤ ∖ gset_to_coPset ∅); [iFrame; done|]. set_solver. }
  done.
Qed.
