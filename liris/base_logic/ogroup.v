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
        ogroupGpreS_thread : inG Σ (reservation_mapUR (gmap_viewR ogid unit));
        ogroupGpreS_group : inG Σ (reservation_mapUR (gmap_viewR ogid (gsetUR oid)));
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
    #[GFunctor (reservation_mapUR (gmap_viewR ogid unit));
      GFunctor (reservation_mapUR (gmap_viewR ogid (gsetUR oid)));
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
Definition ogroupG_thread `{SI : indexT} `{!ogroupGS Σ} (i : positive) (g : ogid) : iProp Σ :=
  own thread_name (reservation_map_data (A:=(gmap_viewR ogid (unit)))
                     i (gmap_view_frag g (DfracOwn 1) (tt))).
Global Typeclasses Opaque ogroupG_thread.
Global Instance: Params (@ogroupG_thread) 3 := {}.

Definition ogroupG_thread_auth `{SI : indexT} `{!ogroupGS Σ} (i : positive) (G : gset ogid) (q : Qp) : iProp Σ :=
  own thread_name (reservation_map_data (A:=(gmap_viewR ogid (unit)))
                     i (gmap_view_auth (DfracOwn q) (gset_to_gmap tt G))).
Global Typeclasses Opaque ogroupG_thread_auth.
Global Instance: Params (@ogroupG_thread_auth) 3 := {}.

Local Definition ogroupG_thread_token `{SI : indexT} `{!ogroupGS Σ} TP : iProp Σ :=
  (own thread_name (reservation_map_token (A:=gmap_viewR ogid (unit)) (⊤ ∖ gset_to_coPset TP))).

(* Group *)
Definition ogroupG_group `{SI : indexT} `{!ogroupGS Σ} (i : positive) (g : ogid) (K : oids) : iProp Σ :=
  own group_name (reservation_map_data (A:=(gmap_viewR ogid (gsetUR oid)))
                    i (gmap_view_frag g (DfracOwn 1) K)).
Global Typeclasses Opaque ogroupG_group.
Global Instance: Params (@ogroupG_group) 3 := {}.

Local Definition ogroupG_group_token `{SI : indexT} `{!ogroupGS Σ} TP : iProp Σ :=
  (own group_name (reservation_map_token (A:=gmap_viewR ogid (gsetUR oid)) (⊤ ∖ gset_to_coPset TP))).

Local Definition ogroupG_group_auth `{SI : indexT} `{!ogroupGS Σ} i (KM : gmap ogid oids) : iProp Σ :=
  (own group_name (reservation_map_data (A:=(gmap_viewR ogid (gsetUR oid)))
                     i (gmap_view_auth (DfracOwn 1) (KM)))).

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
    (∃ (Dg : gset ogid),
        ogroupG_fuel_token_id (⊤ ∖ (gset_to_coPset Dg)) ∗
        ogroupG_thread_token TP ∗
        ogroupG_group_token TP ∗
        ([∗ set] i ∈ TP,
           ∃ (KM : gmap ogid (oids)) (G : gset ogid),
             ⌜ dom KM = G ⌝ ∗
             ogroupG_thread_auth i G (1/2)%Qp ∗
             ogroupG_group_auth i KM ∗
             ((∃ K, othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i K ∗ ⌜ K = union_sets KM ∧ disjoint_sets KM ⌝) ∨
                (othreadG_done i ∗ ogroupG_thread_auth i G (1/2)%Qp ∗ ⌜ KM = ∅ ∧ G = ∅ ⌝)) ∗
             ([∗ map] g ↦ K ∈ KM,
                ∃ β, ogroupG_bound g β ∗
                     ([∗ set] k ∈ K, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)))
    )%I.

Section ogroup.
  Context `{SI : indexT} `{OSAT : !osatGS.osatGS Σ} `{OTH : !othreadGS.othreadGS Σ} `{!ogroupGS Σ} `{OMF : !ord_mono_fun_class}.

  (* Thread *)
  Global Instance ogroupG_thread_timeless i g : Timeless (ogroupG_thread i g).
  Proof. rewrite /ogroupG_thread. apply _. Qed.

  Global Instance ogroupG_thread_auth_timeless i G q : Timeless (ogroupG_thread_auth i G q).
  Proof. rewrite /ogroupG_thread_auth. apply _. Qed.

  Global Instance ogroupG_thread_auth_fractional i G :
    Fractional (ogroupG_thread_auth i G).
  Proof.
    rewrite /ogroupG_thread_auth. intros p q.
    by rewrite -own_op -!reservation_map_data_op -gmap_view_auth_dfrac_op.
  Qed.
  Global Instance ogroupG_thread_auth_as_fractional i G q :
    AsFractional (ogroupG_thread_auth i G q) (ogroupG_thread_auth i G) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance ogroupG_thread_token_timeless TP : Timeless (ogroupG_thread_token TP).
  Proof. rewrite /ogroupG_thread_token. apply _. Qed.

  (* Group *)
  Global Instance ogroupG_group_timeless i g K : Timeless (ogroupG_group i g K).
  Proof. rewrite /ogroupG_group. apply _. Qed.

  Local Instance ogroupG_group_token_timeless TP : Timeless (ogroupG_group_token TP).
  Proof. rewrite /ogroupG_group_token. apply _. Qed.

  Local Instance ogroupG_group_auth_timeless i KM : Timeless (ogroupG_group_auth i KM).
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
  Lemma ogroupG_thread_alloc_auth D i :
    i ∉ D →
    ogroupG_thread_token D
    ⊢ |==> ogroupG_thread_token ({[i]} ∪ D) ∗
        ogroupG_thread_auth i ∅ 1.
  Proof.
    rewrite /ogroupG_thread_token /ogroupG_thread_auth.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (∅ : gmap ogid unit)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma ogroupG_thread_alloc i (G : gset ogid) g :
    g ∉ G →
    ogroupG_thread_auth i G 1
    ⊢ |==> ogroupG_thread_auth i ({[g]} ∪ G) 1 ∗ ogroupG_thread i g.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ g (DfracOwn 1) (tt)); try done.
      apply lookup_gset_to_gmap_None. auto. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]". iFrame "Ho".
    rewrite gset_to_gmap_union_singleton. done.
  Qed.

  Lemma ogroupG_thread_delete i (G : gset ogid) g :
    ogroupG_thread_auth i G 1 ∗ ogroupG_thread i g
    ⊢ |==> ogroupG_thread_auth i (G ∖ {[g]}) 1.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update. rewrite gset_to_gmap_difference_singleton. apply gmap_view_delete.
  Qed.

  Lemma ogroupG_thread_elem_of i G q g :
    ogroupG_thread_auth i G q ∗ ogroupG_thread i g
    ⊢ ⌜ g ∈ G ⌝.
  Proof.
    rewrite /ogroupG_thread_auth /ogroupG_thread -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H.
    destruct H as (?&_&_&?&?&?). iPureIntro.
    apply lookup_gset_to_gmap_Some in H. by destruct H.
  Qed.

  Lemma ogroupG_thread_auth_valid i G1 G2 q1 q2 :
    ogroupG_thread_auth i G1 q1 ∗ ogroupG_thread_auth i G2 q2
    ⊢ ⌜ G1 = G2 ∧ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /ogroupG_thread_auth -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_auth_dfrac_op_valid in H.
    destruct H as (?&?). iPureIntro.
    (* FIXME: hacky proof *)
    rewrite /gset_to_gmap in H0. apply map_fmap_equiv_inj in H0.
    2:{ done. }
    apply leibniz_equiv in H0. split; auto.
    destruct G1, G2; simpl in *. subst. auto.
  Qed.

  (** Group rules *)
  Lemma ogroupG_group_alloc_auth D i :
    i ∉ D →
    ogroupG_group_token D
    ⊢ |==> ogroupG_group_token ({[i]} ∪ D) ∗
        ogroupG_group_auth i ∅.
  Proof.
    rewrite /ogroupG_group_token /ogroupG_group_auth.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (∅ : gmap ogid oids)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma ogroupG_group_alloc i (KM : gmap ogid oids) g :
    KM !! g = None →
    ogroupG_group_auth i KM
    ⊢ |==> ogroupG_group_auth i (<[g:=∅]>KM) ∗ ogroupG_group i g ∅.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ g (DfracOwn 1) ∅); done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]". iFrame "Ho". done.
  Qed.

  Lemma ogroupG_group_delete i (KM : gmap ogid oids) g G :
    ogroupG_group_auth i KM ∗ ogroupG_group i g G
    ⊢ |==> ogroupG_group_auth i (delete g KM).
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update. apply gmap_view_delete.
  Qed.

  Lemma ogroupG_group_update i KM g G1 G2 :
    ogroupG_group_auth i KM ∗
    ogroupG_group i g G1
    ⊢ |==> ogroupG_group_auth i (<[g:=G2]>KM) ∗ ogroupG_group i g G2.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -!own_op -!reservation_map_data_op.
    apply own_update, reservation_map_update, gmap_view_replace. done.
  Qed.

  Lemma ogroupG_group_lookup i KM g G :
    ogroupG_group_auth i KM ∗ ogroupG_group i g G
    ⊢ ⌜ KM !! g = Some G ⌝.
  Proof.
    rewrite /ogroupG_group_auth /ogroupG_group -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_valid in H.
    destruct H as (?&?&?). iPureIntro. apply leibniz_equiv in H1. auto.
  Qed.

  Lemma ogroupG_group_valid i g1 g2 K1 K2 :
    ogroupG_group i g1 K1 ∗ ogroupG_group i g2 K2
    ⊢ ⌜ g1 ≠ g2 ⌝.
  Proof.
    rewrite /ogroupG_group -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    destruct (decide (g1 = g2)); auto. subst.
    apply reservation_map_data_valid, gmap_view_frag_op_valid in H. destruct H. done.
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
    ⊢ |==> ogroup ({[i]} ∪ TP) ∗ ogroupG_thread_auth i ∅ (1/2).
  Proof.
    iIntros (Hi) "(F& Tx& TG)".
    rewrite /ogroup -!lock. iDestruct "F" as "(%& FT& ST& OT& M)".
    iMod (ogroupG_thread_alloc_auth _ i with "ST") as "[ST [Sa $]]". 1: auto.
    iMod (ogroupG_group_alloc_auth _ i with "OT") as "[OT Oa]". 1: auto.
    iModIntro. iFrame "ST OT FT". iApply big_sepS_union. 1: set_solver.
    iFrame "M". iApply big_sepS_singleton. iFrame. iSplitR; first done.
    iSplitL; last done. iLeft. iFrame. done.
  Qed.

  Lemma ogroup_alloc_threads Θ TP :
    Θ ## TP →
    ogroup TP ∗ ([∗ set] i ∈ Θ, othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅)
    ⊢ |==> ogroup (TP ∪ Θ) ∗ ([∗ set] i ∈ Θ, ogroupG_thread_auth i ∅ (1/2)).
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

  Lemma ogroup_exec_to_done TP i :
    i ∈ TP →
    othread TP ∗ ogroup TP ∗
    othreadG_exec i (1/2)%Qp ∗ ogroupG_thread_auth i ∅ (1/2)%Qp
    ⊢ |==> othread TP ∗ ogroup TP ∗ othreadG_done i.
  Proof.
    iIntros (Ini) "(T& G& Tx& Gta)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& FT& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta0& Gga& Hex& OFs)".
    iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    apply dom_empty_inv_L in Dom. subst. iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)". iCombine "Gta Gta0" as "Gta".
      iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta1]") as "%". destruct H. done. }
    iDestruct "Hex" as "(%& Tx2& TG& %)". destruct H as [Uni Disj].
    rewrite union_sets_empty in Uni. subst.
    iCombine "Tx Tx2" as "Tx".
    iMod (othread_exec_to_done with "[$T $Tx $TG]") as "[T #Td]".
    iModIntro. iFrame "T FT TT GT Td".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gta0 Gga". iSplit. 1: done.
    iSplitL "Gta".
    { iRight. iFrame. eauto. }
    done.
  Qed.

  Lemma ogroup_alloc_group TP i G β :
    i ∈ TP →
    ogroup TP ∗ ogroupG_thread_auth i G (1/2)
    ⊢ |==> ∃ g, ogroup TP ∗
             ⌜ g ∉ G ⌝ ∗ ogroupG_thread_auth i ({[g]} ∪ G) (1/2) ∗
             ogroupG_thread i g ∗ ogroupG_group i g ∅ ∗
             ogroupG_bound g β ∗ ogroupG_fuel g β.
  Proof.
    iIntros (Ini) "(G& Gta)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& FT& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta0& Gga& Hex& OFs)".
    iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    iCombine "Gta Gta0" as "Gta". iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)".
      iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta1]") as "%". destruct H. done. }
    assert (∃ g, g ∉ (Dg ∪ G)) as (g&Hg).
    { eexists. eapply is_fresh. }
    iMod (ogroupG_bound_id_alloc _ g β with "FT") as "(FT& #Bs& Hfs)". 1: set_solver.
    iMod (ogroupG_thread_alloc _ _ g with "Gta") as "(Gta& Ps)". 1: set_solver.
    assert (LUg : KM !! g = None).
    { apply not_elem_of_dom. simplify_eq. set_solver. }
    iMod(ogroupG_group_alloc _ _ g with "Gga") as "(Gga& Po)". 1: auto.
    iDestruct "Gta" as "[Gta Gta0]".
    iModIntro. iExists g. iFrame "Gta Ps Po Bs Hfs TT GT FT".
    iSplit.
    2:{ iPureIntro. set_solver. }
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gta0 Gga". iSplit.
    { iPureIntro. rewrite !dom_insert_L Dom. auto. }
    iSplitL "Hex".
    { iLeft. iDestruct "Hex" as "(%& $& $& %)". iPureIntro. destruct H. simplify_eq.
      rewrite union_sets_insert_L. 2: auto. split; first set_solver.
      apply disjoint_sets_insert_2; auto. set_solver. }
    iApply big_sepM_insert; auto.
  Qed.

  Lemma ogroup_delete_group TP i G g :
    i ∈ TP →
    ogroup TP ∗ ogroupG_thread_auth i G (1/2) ∗
    ogroupG_thread i g ∗ ogroupG_group i g ∅
    ⊢ |==> ogroup TP ∗ ogroupG_thread_auth i (G ∖ {[g]}) (1/2).
  Proof.
    iIntros (Ini) "(G& Gta& Ps& Po)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& FT& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta0& Gga& Hex& OFs)".
    iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    iCombine "Gta Gta0" as "Gta". iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)".
      iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta1]") as "%". destruct H. done. }
    iPoseProof (ogroupG_thread_elem_of with "[$Gta $Ps]") as "%LUs".
    iMod (ogroupG_thread_delete with "[$Gta $Ps]") as "[Gta Gta0]".
    iPoseProof (ogroupG_group_lookup with "[$Gga $Po]") as "%LUo".
    iMod(ogroupG_group_delete with "[$Gga $Po]") as "Gga".
    iModIntro. iFrame "Gta TT GT FT".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gta0 Gga". iSplit.
    { iPureIntro. rewrite !dom_delete_L Dom. auto. }
    iSplitL "Hex".
    { iLeft. iDestruct "Hex" as "(%& $& $& %)". iPureIntro. destruct H. subst.
      erewrite (union_sets_delete_L KM g). 2: eauto.
      split; first set_solver. apply disjoint_sets_delete; auto. }
    iPoseProof (big_sepM_delete _ _ g with "OFs") as "[_ $]"; eauto.
  Qed.

  Lemma ogroup_alloc_obl Ω TP i g K β k :
    i ∈ TP →
    osat Ω ∗ othread TP ∗ ogroup TP ∗
    ogroupG_group i g K ∗ ogroupG_thread i g ∗ ogroupG_bound g β ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp ∗ oblG_fuel k β
    ⊢ |==> osat Ω ∗ othread TP ∗ ogroup TP ∗
        ⌜k ∉ K⌝ ∗ ogroupG_group i g ({[k]} ∪ K) ∗ ogroupG_thread i g ∗
        othreadG_owns i k 1 ∗ oblG_owner k i (1/2 + 1/2/2/2 + 1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ini) "(S& T& G& Po& Ps& #Tb& #Oe& Oo& Of)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& FT& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta& Gga& Hex& OFs)".
    iPoseProof (ogroupG_thread_elem_of with "[$Gta $Ps]") as "%LUs".
    iPoseProof (ogroupG_group_lookup with "[$Gga $Po]") as "%LUo".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (big_sepM_delete _ _ _ _ LUo with "OFs") as "[Hp OFs]".
    iDestruct "Hp" as "(%& #Tb0& Hfs)".
    iPoseProof (ogroupG_bound_op _ β β0 with "[$Tb $Tb0]") as "(%β1& #Tb1& %Hb)".
    destruct Hb as [Hb1 Hb2]. iClear "Tb Tb0".
    iMod (othread_alloc_obl with "[$S $T $TG $Oe $Oo]") as "(S& T& %Nink& TG& To& Oo)".
    iMod (ogroupG_group_update _ _ _ _ ({[k]} ∪ K) with "[$Gga $Po]") as "[Gga Po]".
    iModIntro. iFrame "S T FT TT GT Ps To Oo Po".
    assert (Nink2 : k ∉ K).
    { simplify_eq. rewrite not_elem_of_union_sets in Nink. eapply Nink; eauto. }
    iSplit. 2: auto.
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gga Gta". iSplitR.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUo. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. replace ({[k]} ∪ K) with (K ∪ {[k]}) by set_solver. simplify_eq. split.
      - rewrite union_sets_insert_union_L; auto.
      - apply disjoint_sets_insert_union_singleton_not_in; auto. }
    iApply big_sepM_insert_delete. iFrame "OFs Tb1". iApply (big_sepS_union). 1: set_solver.
    iSplitR "Hfs".
    { iApply big_sepS_singleton. iFrame "Of Oe". iPureIntro. eauto. }
    { iApply (big_sepS_impl with "Hfs"). iIntros "!> %% (%&%&$&$)". iPureIntro. etrans; eauto. }
  Qed.

  Lemma ogroup_delete_obl TP i g K k :
    i ∈ TP →
    k ∈ K →
    othread TP ∗ ogroup TP ∗
    ogroupG_group i g K ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ ogroup TP ∗
        ogroupG_group i g (K ∖ {[k]}) ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ini Ink) "(T& G& Po& To)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& FT& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta& Gga& Hex& OFs)".
    iPoseProof (ogroupG_group_lookup with "[$Gga $Po]") as "%LUo".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (big_sepM_delete _ _ _ _ LUo with "OFs") as "(Hp& OFs)".
    iDestruct "Hp" as "(%& #Tb& Hfs)".
    iMod (othread_delete_obl with "[$T $TG $To]") as "(T& TG& Oo)".
    iMod (ogroupG_group_update _ _ _ _ (K ∖ {[k]}) with "[$Gga $Po]") as "[Gga Po]".
    iModIntro. iFrame "T FT TT GT Oo Po".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gga Gta". iSplitR.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUo. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. simplify_eq. split.
      - rewrite union_sets_insert_difference_singleton_L; auto.
      - apply disjoint_sets_insert_difference; auto. }
    iApply big_sepM_insert_delete. iFrame "OFs". iFrame "Tb".
    iPoseProof (big_sepS_delete with "Hfs") as "[_ $]". auto.
  Qed.

  Lemma ogroup_exchange_fuel TP i GS q c :
    i ∈ TP →
    (Ord.O < c)%ord →
    ogroup TP ∗
    ogroupG_thread_auth i GS q ∗
    ([∗ set] g ∈ GS, ogroupG_fuel g c)
    ⊢ |==> ∃ G, (othreadG_exec i (1 / 2 / 2) -∗ othreadG_obls i G -∗ ogroup TP) ∗
             ogroupG_thread_auth i GS q ∗
             othreadG_exec i (1 / 2 / 2) ∗ othreadG_obls i G ∗
             ([∗ set] k ∈ G, oblG_fuel k Ord.one ∗ oblG_elem k).
  Proof.
    iIntros (Ini Ltc) "(G& Gta& Tfs)".
    rewrite /ogroup -!lock. iDestruct "G" as "(%& FT& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta0& Gga& Hex& OFs)".
    iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)". iCombine "Gta0 Gta1" as "Gta0".
      iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H.
      apply Qp.not_add_le_r in H0. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iAssert (
        |==> ([∗ map] g ↦ K ∈ KM,
             ∃ β, ogroupG_bound g β ∗ ([∗ set] k ∈ K, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)) ∗
          ([∗ map] K ∈ KM, ([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k)))%I
      with "[Tfs OFs]" as ">[OFs Fs]".
    { simplify_eq. iPoseProof (big_sepM_dom with "Tfs") as "Tfs".
      iPoseProof (big_sepM_sep with "[$OFs $Tfs]") as "F".
      iApply big_sepM_sep. iApply big_sepM_bupd.
      iApply (big_sepM_impl with "F"). iIntros "!> %%% [H F]".
      iDestruct "H" as "(%& #Tb& KFs)". rename x into K.
      iMod (ogroupG_fuel_spend with "[$Tb $F]") as "(%β1& %HB& #Tb1)". 1: auto.
      iAssert (|==> ([∗ set] k ∈ K, ∃ a : Ord.t, ⌜(β1 <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k) ∗
                 ([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k))%I with "[KFs]" as ">[Fvs Rvs]".
      { iApply big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "KFs").
        iIntros "!> %% (%&%& F& #E)". iFrame "E". iMod (oblG_fuel_lt _ β1 with "F") as "(F& %& %& F1)".
        { eapply Ord.lt_le_lt; eauto. }
        iMod (oblG_fuel_mon _ Ord.one with "F1") as "F1".
        { apply Ord.S_supremum. auto. }
        iModIntro. iSplitR "F1"; iFrame. done. }
      iFrame. eauto. }
    iModIntro. iFrame "Gta Tx TG". iSplitR "Fs".
    - iIntros "Tx TG". iFrame "FT TT GT". 
      iApply (big_sepS_delete _ _ _ Ini). iFrame "M". iFrame "Gta0 Gga". iSplit. 1: done.
      iFrame "OFs". iLeft. iFrame. eauto.
    - subst. clear dependent TP i q c Dg. iInduction KM as [ | g K ?? LUp] using map_ind.
      { rewrite union_sets_empty. done. }
      rewrite union_sets_insert_L; last auto. iApply (big_sepS_union).
      { eapply disjoint_sets_insert_disjoint_union_sets; eauto. }
      iPoseProof (big_sepM_insert with "Fs") as "[F Fs]". 1: auto.
      apply disjoint_sets_insert in Disj; last auto. destruct Disj as [MF Disj].
      iPoseProof ("LUp" with "[//] Fs") as "$". iFrame.
  Qed.

  TODO

  Lemma ogroup_obl_change_thread TP i1 i2 g1 g2 K1 K2 β k :
    i1 ∈ TP →
    i2 ∈ TP →
    k ∈ K1 →
    i1 ≠ i2 →
    ogroup TP ∗
    ogroupG_group i1 g1 K1 ∗
    ogroupG_group i2 g2 K2 ∗ ogroupG_thread i2 g2 ∗
    ogroupG_bound g2 β ∗ oblG_fuel k β
    ⊢ |==> ∃ G1 G2,
      (⌜ k ∉ G2 ⌝ -∗ othreadG_exec i1 (1/2/2) -∗ othreadG_obls i1 (G1 ∖ {[k]}) -∗
       othreadG_exec i2 (1/2/2) -∗ othreadG_obls i2 ({[k]} ∪ G2) -∗ ogroup TP) ∗
      ⌜ k ∈ G1 ⌝ ∗
      othreadG_exec i1 (1/2/2) ∗ othreadG_obls i1 G1 ∗
      othreadG_exec i2 (1/2/2) ∗ othreadG_obls i2 G2 ∗
      ogroupG_group i1 π1 (K1 ∖ {[k]}) ∗ ogroupG_group i2 π2 (K2 ∪ {[k]}) ∗
      ogroupG_thread i2 π2 s q.
  Proof.
    iIntros (Ini1 Ini2 Ink Nei) "(P& Po1& Po2& Ps2& #Tb& Of)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini1 with "M") as "[Mi M]".
    iDestruct "Mi" as "(%Ks1& %Ss1& %Dom1& Gga1& Gta1& Hex1& OFs1)".
    iPoseProof (ogroupG_group_lookup with "[$Gga1 $Po1]") as "%LUo1".
    assert (is_Some (Ss1 !! π1)) as (s1& LUs1).
    { apply elem_of_dom. apply elem_of_dom_2 in LUo1. rewrite -Dom1. auto. }
    assert (Ini2' : i2 ∈ (TP ∖ {[i1]})) by set_solver.
    iPoseProof (big_sepS_delete _ _ _ Ini2' with "M") as "[Mi M]".
    iDestruct "Mi" as "(%Ks2& %Ss2& %Dom2& Gga2& Gta2& Hex2& OFs2)".
    iPoseProof (ogroupG_group_lookup with "[$Gga2 $Po2]") as "%LUo2".
    iPoseProof (ogroupG_thread_elem_of with "[$Gta2 $Ps2]") as "%LUs2". rename s into s2.
    iDestruct "Hex1" as "[Hex1 | Hex1]"; cycle 1.
    { iDestruct "Hex1" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex1" as "(%G1& Tx1& TG1& %)". destruct H as [Uni1 Disj1].
    iDestruct "Hex2" as "[Hex2 | Hex2]"; cycle 1.
    { iDestruct "Hex2" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex2" as "(%G2& Tx2& TG2& %)". destruct H as [Uni2 Disj2].
    iMod (ogroupG_group_update _ _ _ _ (K1 ∖ {[k]}) with "[$Gga1 $Po1]") as "[Gga1 Po1]".
    iMod (ogroupG_group_update _ _ _ _ (K2 ∪ {[k]}) with "[$Gga2 $Po2]") as "[Gga2 Po2]".
    assert (Ink2 : k ∈ G1).
    { subst. apply elem_of_union_sets; eauto. }
    iModIntro. iFrame "Tx1 Tx2 TG1 TG2 Po1 Po2 Ps2". iSplit; last auto.
    iIntros (Nink) "Tx1 TG1 Tx2 TG2". iFrame "FT ST PT".
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo1 LUs1 with "OFs1") as "[OF OFs1]".
    iDestruct "OF" as "(%& #Tb0& OF)". iPoseProof (big_sepS_delete _ _ _ Ink with "OF") as "[Hof OF]".
    iApply (big_sepS_delete _ _ _ Ini1). iSplitL "Gta1 Gga1 Tx1 TG1 OFs1 OF".
    { iFrame "Gta1 Gga1". iSplit.
      { iPureIntro. rewrite dom_insert_L Dom1. apply elem_of_dom_2 in LUs1. set_solver. }
      iSplitL "Tx1 TG1".
      { iLeft. iFrame. iPureIntro. simplify_eq. split.
        - rewrite union_sets_insert_difference_singleton_L; auto.
        - apply disjoint_sets_insert_difference; auto. }
      iEval (rewrite -(insert_id _ _ _ LUs1)). iApply big_sepM2_insert_delete. iFrame "OFs1".
      iFrame "Tb0 OF". }
    iApply (big_sepS_delete _ _ _ Ini2'). iFrame "M".
    iFrame "Gta2 Gga2". iSplitR.
    { iPureIntro. rewrite !dom_insert_L. apply elem_of_dom_2 in LUo2. set_solver. }
    iSplitL "Tx2 TG2".
    { iLeft. iFrame. iPureIntro. simplify_eq. split.
      - rewrite union_sets_insert_union_L; auto.
      - apply disjoint_sets_insert_union_singleton_not_in; auto. }
    iEval (rewrite -(insert_id _ _ _ LUs2)). iApply big_sepM2_insert_delete.
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo2 LUs2 with "OFs2") as "[Fs2 OFs2]". iFrame "OFs2".
    iDestruct "Fs2" as "(%& #Tb1& F)". iPoseProof (ogroupG_bound_op _ β β1 with "[$Tb $Tb1]") as "(%& #Tb'& %)".
    destruct H. iFrame "Tb'". iApply (big_sepS_union_2 with "[F] [-]").
    { iApply (big_sepS_impl with "F"). iIntros "!> %% (%& %& $& $)". iPureIntro. etrans; eauto. }
    { iDestruct "Hof" as "(%& _& _& #Ok)". iApply big_sepS_singleton. iFrame "Of Ok". iPureIntro. auto. }
  Qed.

  Lemma ogroup_obl_change_proxy TP i π1 π2 K1 K2 s2 q2 β k :
    i ∈ TP →
    k ∈ K1 →
    ogroup TP ∗
    ogroupG_group i π1 K1 ∗
    ogroupG_group i π2 K2 ∗ ogroupG_thread i π2 s2 q2 ∗
    ogroupG_bound s2 β ∗ oblG_fuel k β
    ⊢ |==> ogroup TP ∗
        ogroupG_group i π1 (K1 ∖ {[k]}) ∗
        ogroupG_group i π2 (K2 ∪ {[k]}) ∗ ogroupG_thread i π2 s2 q2.
  Proof.
    iIntros (Ini Ink) "(P& Po1& Po2& Ps2& #Tb& Of)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Gga& Gta& Hex& OFs)".
    iPoseProof (ogroupG_group_lookup with "[$Gga $Po1]") as "%LUo1".
    assert (is_Some (Ss !! π1)) as (s1& LUs1).
    { apply elem_of_dom. apply elem_of_dom_2 in LUo1. rewrite -Dom. auto. }
    iPoseProof (ogroupG_group_lookup with "[$Gga $Po2]") as "%LUo2".
    iPoseProof (ogroupG_thread_elem_of with "[$Gta $Ps2]") as "%LUs2".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (ogroupG_group_valid _ π1 π2 with "[$Po1 $Po2]") as "%Neqp".
    iMod (ogroupG_group_update _ _ _ _ (K1 ∖ {[k]}) with "[$Gga $Po1]") as "[Gga Po1]".
    iMod (ogroupG_group_update _ _ _ _ (K2 ∪ {[k]}) with "[$Gga $Po2]") as "[Gga Po2]".
    iModIntro. iFrame "FT ST PT Po1 Po2 Ps2".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gga Gta". iSplitR.
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
      iPoseProof (ogroupG_bound_op _ β β0 with "[$Tb $Tb0]") as "(%β1& #Tb1& %Hb)".
      destruct Hb as [Hb1 Hb2]. iClear "Tb Tb0".
      iFrame "Tb1". iApply big_sepS_union.
      { specialize (Disj _ _ _ _ Neqp LUo1 LUo2). set_solver. }
      iSplitL "Fs".
      { iApply (big_sepS_impl with "Fs"). iIntros "!> %% (%& %& $& $)". iPureIntro. etrans; eauto. }
      iApply big_sepS_singleton. iFrame "Oe Of". iPureIntro. auto. }
    rewrite !delete_insert_ne; auto. iApply big_sepM2_insert_delete. iFrame "OFs".
    iFrame "Bp1". iFrame.
  Qed.

  TODO:
    alloc_group, offload, delete_group. don't need ogroupG_thread here, only the two groups. can involve thread change
  Lemma ogroup_proxy_new_session TP i π K PS s1 β :
    i ∈ TP →
    ogroup TP ∗ ogroupG_group i π K ∗
    ogroupG_thread_auth i PS (1/2)%Qp ∗ ogroupG_thread i π s1 1 ∗
    ([∗ set] k ∈ K, oblG_fuel k β)
    ⊢ |==> ∃ s2, ogroup TP ∗ ogroupG_group i π K ∗
              ogroupG_thread_auth i (<[π:=s2]>PS) (1/2)%Qp ∗ ogroupG_thread i π s2 1 ∗
              ogroupG_bound s2 β ∗ ogroupG_fuel s2 β.
  Proof.
    iIntros (Ini) "(P& Po& Gta& Ps& KFs)".
    rewrite /ogroup -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Gga& Gta0& Hex& OFs)".
    iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    iCombine "Gta Gta0" as "Gta".
    iPoseProof (ogroupG_group_lookup with "[$Gga $Po]") as "%LUo".
    iPoseProof (ogroupG_thread_elem_of with "[$Gta $Ps]") as "%LUs".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)".
      iPoseProof (ogroupG_thread_auth_valid with "[$Gta $Gta1]") as "%". destruct H. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    assert (∃ s2, s2 ∉ Df) as (s2&Hs).
    { eexists. eapply is_fresh. }
    iMod (ogroupG_bound_id_alloc _ _ β Hs with "FT") as "(FT& #Tb& Hfs)".
    iMod (ogroupG_thread_update _ _ _ _ s2 with "[$Gta $Ps]") as "[[Gta Gta0] Ps]".
    iModIntro. iFrame "FT ST PT Po Hfs Gta Ps Tb".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gga Gta0". iSplit.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUs. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. eauto. }
    iEval (rewrite -(insert_id _ _ _ LUo)). iApply big_sepM2_insert_delete.
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo LUs with "OFs") as "[Fs $]".
    iDestruct "Fs" as "(%& _& Fs)". iPoseProof (big_sepS_sep_2 with "KFs Fs") as "Fs".
    iFrame "Tb". iApply (big_sepS_impl with "Fs"). iIntros "!> %% ($& %& _& _& $)". auto.
  Qed.




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
