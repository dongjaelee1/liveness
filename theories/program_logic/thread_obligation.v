From iris.algebra Require Import gmap_view reservation_map mono_list mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Export osat sched_fair_interp.
From liveness Require Import language ordinal_wfocm.

(** Enable thread local management of obligations.
    Also connects scheduler fairness with obligations to enable liveness induction. *)
Module threadoblGS.
  Class threadoblGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    ThreadoblGpreS {
        threadoblGpreS_state : inG Σ (reservation_mapUR (mono_listUR obl_id));
        threadoblGpreS_live : inG Σ (gmap_viewR thread_id (agreeR (list obl_id)));
      }.

  Class threadoblGS `{SI : indexT} (Σ : gFunctors) : Set :=
    ThreadoblG {
        threadobl_inG : threadoblGpreS Σ;
        state_name : gname;
        live_name : gname;
      }.

  Definition threadoblΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (mono_listUR obl_id));
      GFunctor (gmap_viewTRF thread_id (agreeTRF (listO obl_id)))
      ].

  Global Instance subG_threadoblΣ `{SI : indexT} {Σ} : subG threadoblΣ Σ → (threadoblGpreS Σ).
  Proof.
    solve_inG.
  Qed.

End threadoblGS.
Import threadoblGS.

(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances threadobl_inG threadoblGpreS_state threadoblGpreS_live.
Local Existing Instances osatGS.osat_inG osatGS.osatGpreS_goal osatGS.osatGpreS_state.
Local Existing Instances schedfairGS.schedfair_inG schedfairGS.schedfairGpreS_state.

(* list l logs every obligation ever allocated to thread i *)
Definition toS_thread `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (l : list obl_id) : iProp Σ :=
  (∃ l', ⌜ l ≡ₚ l' ⌝ ∗ own state_name (reservation_map_data i (●ML l')))%I.
Global Typeclasses Opaque toS_thread.
Global Instance: Params (@toS_thread) 4 := {}.

(* list l is a snapshot of the log of obligations ever allocated to thread i *)
Definition toS_assigned `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (κ : obl_id) : iProp Σ :=
  (∃ l, ⌜ κ ∈ l ⌝ ∗ own state_name (reservation_map_data i (◯ML l)))%I.
Global Typeclasses Opaque toS_assigned.
Global Instance: Params (@toS_assigned) 4 := {}.

(* thread i is currently executing, with live obligations l. *)
Definition toL_thread `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) q (l : list obl_id) : iProp Σ :=
  (∃ l', ⌜ l ≡ₚ l' ⌝ ∗ own live_name (gmap_view_frag i (DfracOwn q) (to_agree l')))%I.
Global Typeclasses Opaque toL_thread.
Global Instance: Params (@toL_thread) 4 := {}.

(* thread i terminated, with no live obligation []. *)
Definition toL_term `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) : iProp Σ :=
  own live_name (gmap_view_frag i DfracDiscarded (to_agree [])).
Global Typeclasses Opaque toL_term.
Global Instance: Params (@toL_term) 4 := {}.

(* thread fork cases: sched fuel for new threads? *)
Definition toI `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} {ps} {Σ}
  `{@osatGS.osatGS SI Ord.t _ ps Σ} `{@schedfairGS.schedfairGS SI _ _ _ _ WF Σ} `{!threadoblGS Σ}
  (γ : gmap thread_id (list obl_id))
  : iProp Σ :=
  locked
    (∃ (Ψ : gmap thread_id (list obl_id)),
        (⌜ map_Forall2 (λ _ l1 l2, l1 ⊆+ l2) γ Ψ ⌝) ∗
        (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom Ψ)))) ∗
        (own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ))) ∗
        ([∗ map] i ↦ W ∈ Ψ,
           toS_thread i W ∗
           ∃ (f : A), sfS_fuel_bound i f 1 ∗
                      (∃ L, ⌜ γ !! i = Some L ⌝ ∗
                            ([∗ list] k ∈ W, (⌜ k ∈ L ⌝ ∨ oblS_done k) ∗ oblG_elem k) ∗
                            ([∗ list] k ∈ L,
                               oblS_live k (1/2 + 1/2/2)%Qp ∗
                               (oblS_active k ∗ ∃ a, ⌜ (Ord.from_wf (WFOCM.lt_wf) f <= a)%ord ⌝ ∗ oblS_credit k a))
                      )
        )
    )%I.

Definition oftI `{SI : indexT} {T : Type} `{WF : WFOCM.t A leR addO ltR} `{OC : obl_class obl_ps (T * A)%type} `{!threadoblGS Σ}
  (Ω : obl_states) (δ : gmap thread_id A) (γ : gmap thread_id (list obl_id)) : iProp Σ :=
  (([∗ set] κ ∈ dom Ω, ∃ i, toS_assigned i κ) ∗
   ([∗ map] f; L ∈ δ; γ, [∗ list] κ ∈ L, ⌜ ∃ c, Ω !! κ = Some (obl_live c) ∧ leR f c.2 ⌝))%I.

Section thread_obl.
  Context `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} `{OC : obl_class ps (Ord.t * A)%type}.
  Context {Σ} `{@osatGS.osatGS SI _ ord_wfocm_pack ps Σ} `{@schedfairGS.schedfairGS SI _ _ _ _ WF Σ} `{!@threadoblGS SI Σ}.

  Global Instance toS_assigned_persistent i κ : Persistent (toS_assigned i κ).
  Proof. rewrite /toS_assigned. apply _. Qed.
  Global Instance toL_term_persistent i : Persistent (toL_term i).
  Proof. rewrite /toL_term. apply _. Qed.
  Global Instance oftI_persistent Ω δ γ : Persistent (oftI Ω δ γ).
  Proof. rewrite /oftI. apply _. Qed.

  Local Infix "/=" := (OCM.eq (car:=A)) (at level 70).
  Local Infix "/≤" := (leR) (at level 70).
  Local Infix "/+" := (addO) (at level 70).
  Local Infix "/<" := (ltR) (at level 70).
  Local Notation "/0" := (OCM.unit (car:=A)).

  Lemma toS_thread_perm i l l' :
    Permutation l l' →
    toS_thread i l ⊣⊢ toS_thread i l'.
  Proof.
    rewrite /toS_thread. iIntros (Hp). iSplit; iIntros "(%&%&H)".
    - iExists l'0. iFrame. iPureIntro. etransitivity; done.
    - iExists l'0. iFrame. iPureIntro. etransitivity; done.
  Qed.

  Lemma toS_thread_assigned i l κ :
    κ ∈ l →
    toS_thread i l ⊢ toS_assigned i κ.
  Proof.
    rewrite /toS_thread /toS_assigned. iIntros (Hin) "(%&%&H)". iExists l'. iSplit.
    - iPureIntro. eapply elem_of_Permutation_proper; done.
    - iApply (own_mono with "H"). apply reservation_map_data_mono. by rewrite mono_list_auth_lb_op.
  Qed.

  Lemma toS_thread_assigned_inv i l κ :
    toS_thread i l ∗ toS_assigned i κ ⊢ ⌜ κ ∈ l ⌝.
  Proof.
    rewrite /toS_thread /toS_assigned. iIntros "[(%&%&H) (%&%&H2)]".
    iCombine "H H2" as "H". iPoseProof (own_valid with "H") as "%". iPureIntro.
    apply reservation_map_data_valid in H4. apply mono_list_both_valid_L in H4.
    rewrite H2. eauto using elem_of_prefix.
  Qed.

  Lemma toS_thread_elem_of D i l :
    own state_name (reservation_map_token (⊤ ∖ D)) ∗ toS_thread i l
    ⊢ ⌜ i ∈ D ⌝.
  Proof.
    rewrite /toS_thread /reservation_map_token /reservation_map_data. iIntros "[Hr (%&%&Ht)]".
    iCombine "Hr Ht" as "H". iPoseProof (own_valid with "H") as "%Hv". iPureIntro.
    rewrite /op /cmra_op /= /reservation_map_op_instance in Hv. simpl in Hv.
    rewrite left_id right_id in Hv. rewrite reservation_map_valid_eq in Hv. simpl in Hv.
    destruct Hv as [? ?]. destruct (H4 i) as [? | ?].
    - rewrite lookup_insert in H5. done.
    - set_solver.
  Qed.

  Lemma toS_assigned_elem_of D i κ :
    own state_name (reservation_map_token (⊤ ∖ D)) ∗ toS_assigned i κ
    ⊢ ⌜ i ∈ D ⌝.
  Proof.
    rewrite /toS_assigned /reservation_map_token /reservation_map_data. iIntros "[Hr (%&_&Ht)]".
    iCombine "Hr Ht" as "H". iPoseProof (own_valid with "H") as "%Hv". iPureIntro.
    rewrite /op /cmra_op /= /reservation_map_op_instance in Hv. simpl in Hv.
    rewrite left_id right_id in Hv. rewrite reservation_map_valid_eq in Hv. simpl in Hv.
    destruct Hv as [? ?]. destruct (H3 i) as [? | ?].
    - rewrite lookup_insert in H4. done.
    - set_solver.
  Qed.

  Lemma toS_alloc_thread D i l :
    i ∉ D →
    own state_name (reservation_map_token (⊤ ∖ D))
    ⊢ |==> own state_name (reservation_map_token (⊤ ∖ ({[i]} ∪ D))) ∗ toS_thread i l.
  Proof.
    iIntros (Hn) "Htk".
    assert (Fresh : {[ i ]} ⊆ (⊤ ∖ D)) by set_solver.
    rewrite (reservation_map_token_difference _ _ Fresh). iDestruct "Htk" as "[Htki Htk]".
    assert (New : (⊤ ∖ D ∖ {[i]}) = (⊤ ∖ ({[i]} ∪ D))) by set_solver.
    iMod (own_update with "Htki") as "Hi".
    { apply (reservation_map_alloc _ i (●ML l)); [set_solver | apply mono_list_auth_valid]. }
    iModIntro. rewrite /toS_thread. iFrame. iSplit; [|done]. by rewrite New.
  Qed.

  (* Print Table Search Blacklist. *)
  (* Shows that _obl_ is blacklisted, and as a result. any lemma that contains _obl_ doesn't show up in Search.  *)
  Lemma toS_alloc_obl i l κ :
    toS_thread i l ⊢ |==> toS_thread i (κ :: l) ∗ toS_assigned i κ.
  Proof.
    rewrite /toS_thread. iIntros "(%&%&H)". iMod (own_update _ _ (reservation_map_data i (●ML (l' ++ [κ]))) with "H") as "H".
    { apply reservation_map_update. apply mono_list_update. apply prefix_app_r. done. }
    iPoseProof (toS_thread_assigned i _ κ with "[H]") as "#Hs".
    2:{ rewrite /toS_thread. iExists (l' ++ [κ]). iFrame. iPureIntro. reflexivity. }
    { set_solver. }
    iFrame. iModIntro. iSplit; [|done]. iPureIntro. rewrite H2. apply Permutation_cons_append.
  Qed.

  Lemma toL_thread_term i q :
    toL_thread i q [] ⊢ |==> toL_term i.
  Proof.
    rewrite /toL_thread /toL_term. iIntros "(%&%&H)". apply Permutation_nil in H2. subst.
    iApply (own_update with "H"). apply gmap_view_frag_persist.
  Qed.

  Lemma toL_thread_perm i q l l' :
    Permutation l l' →
    toL_thread i q l ⊣⊢ toL_thread i q l'.
  Proof.
    rewrite /toL_thread. iIntros (Hp). iSplit; iIntros "(%&%&H)".
    - iExists l'0. iFrame. iPureIntro. etransitivity; done.
    - iExists l'0. iFrame. iPureIntro. etransitivity; done.
  Qed.

  Lemma toL_thread_lookup γ i q l :
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ)) ∗ toL_thread i q l
    ⊢ ∃ l', ⌜ γ !! i = Some l' ⌝ ∧ ⌜ l' ≡ₚ l ⌝.
  Proof.
    rewrite /toL_thread. iIntros "(H&%&%&Ht)". iCombine "H Ht" as "H".
    rewrite own_valid gmap_view_both_validI_total. iDestruct "H" as "(%&%&%&%&%&%)".
    apply lookup_fmap_Some in H5. destruct H5 as (?&?&?). subst. apply to_agree_included in H7.
    iExists l'. iPureIntro. split; [|done].
    rewrite H8. f_equal. by apply leibniz_equiv.
  Qed.

  Lemma toL_term_elem_of γ i :
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ)) ∗ toL_term i
    ⊢ ⌜ γ !! i = Some [] ⌝.
  Proof.
    rewrite /toL_term. iIntros "(H&Ht)". iCombine "H Ht" as "H".
    rewrite own_valid gmap_view_both_validI_total. iDestruct "H" as "(%&%&%&%&%&%)".
    apply lookup_fmap_Some in H4. destruct H4 as (?&?&?). subst. apply to_agree_included in H6.
    iPureIntro. rewrite H7. f_equal. by apply leibniz_equiv.
  Qed.

  Lemma toL_alloc_thread γ i l :
    γ !! i = None →
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ))
    ⊢ |==> own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=l]>γ)) ∗ toL_thread i 1 l.
  Proof.
    iIntros (LU) "H". iMod (own_update with "H") as "[H Ht]".
    { apply (gmap_view_alloc _ i (DfracOwn 1) (to_agree l)); [| done | done]. by rewrite lookup_fmap LU. }
    iModIntro. rewrite /toL_thread. iFrame. iSplit; [|done].
    by rewrite fmap_insert.
  Qed.

  Lemma toL_alloc_obl γ i l κ :
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ)) ∗ toL_thread i 1 l
    ⊢ |==> own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=κ :: l]>γ)) ∗ toL_thread i 1 (κ :: l).
  Proof.
    rewrite /toL_thread. iIntros "[H (%&%&Ht)]". iCombine "H Ht" as "H".
    iMod (own_update _ _ (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=κ :: l]>γ) ⋅ gmap_view_frag i (DfracOwn 1) (to_agree (κ :: l))) with "H") as "[H Ht]".
    { rewrite fmap_insert. apply gmap_view_replace. done. }
    iFrame. iPureIntro. done.
  Qed.

  Lemma toL_obl_free γ i κ l :
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ)) ∗ toL_thread i 1 (κ :: l)
    ⊢ |==> own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=l]>γ)) ∗ toL_thread i 1 l.
  Proof.
    rewrite /toL_thread. iIntros "[H (%&%&Ht)]". iCombine "H Ht" as "H".
    iMod (own_update _ _ (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=l]>γ) ⋅ gmap_view_frag i (DfracOwn 1) (to_agree l)) with "H") as "[H Ht]".
    { rewrite fmap_insert. apply gmap_view_replace. done. }
    iFrame. iPureIntro. done.
  Qed.

  Lemma toI_alloc_thread γ i f :
    γ !! i = None →
    toI γ ∗ sfS_fuel_bound i f 1
    ⊢ |==> toI (<[i:=[]]>γ) ∗ toL_thread i 1 [].
  Proof.
    iIntros (LU) "[HI Hf]". pose proof (not_elem_of_dom_2 _ _ LU) as Hn.
    rewrite /toI -!lock. iDestruct "HI" as "(%&%&Hos&Hol&HM)".
    pose proof (map_Forall2_dom_L _ _ _ H2) as Hde.
    iMod (toS_alloc_thread _ i [] with "Hos") as "[Hos Hts]".
    { intros F. apply Hn. apply elem_of_gset_to_coPset. by rewrite Hde. }
    iMod (toL_alloc_thread _ i [] with "Hol") as "[Hol Htl]".
    { auto. }
    assert ({[i]} ∪ gset_to_coPset (dom Ψ) = gset_to_coPset (dom (<[i:=[]]>Ψ))).
    { rewrite dom_insert_L. apply leibniz_equiv. intros x. rewrite elem_of_gset_to_coPset. split; intros.
      - apply elem_of_union in H3. destruct H3; first set_solver. apply elem_of_gset_to_coPset in H3. set_solver.
      - apply elem_of_union in H3. destruct H3; first set_solver. apply elem_of_gset_to_coPset in H3. set_solver.
    }
    rewrite H3. iModIntro. iFrame. iSplit.
    { iPureIntro. apply map_Forall2_insert_2; done. }
    iApply big_opM_insert.
    { apply not_elem_of_dom. by rewrite -Hde. }
    iFrame. iSplitR.
    { iExists []. iSplit; [by rewrite lookup_insert |]. simpl. done. }
    iApply (big_sepM_impl with "HM"). iModIntro. iIntros (???) "[Hst H]". iFrame.
    destruct (decide (i = k)).
    - subst. iDestruct "H" as "(%&_&%&%&_)". exfalso. by rewrite LU in H5.
    - by rewrite lookup_insert_ne.
  Qed.

  Lemma toI_alloc_obl γ i l κ :
    toI γ ∗ toL_thread i 1 l ∗
    oblG_elem κ ∗ oblS_live κ (1/2 + 1/2/2)%Qp ∗ oblS_active κ ∗ oblS_credit κ (Ord.from_wf_set (WFOCM.lt_wf))
    ⊢ |==> toI (<[i:=κ :: l]>γ) ∗ toL_thread i 1 (κ :: l) ∗ toS_assigned i κ.
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & (Htl&Hge&Hsl&Hsi&Hsc))".
    iPoseProof (toL_thread_lookup with "[Hol Htl]") as "%"; first iFrame.
    destruct H3 as (l'&LU&HP).
    iMod (toL_alloc_obl _ _ _ κ with "[Hol Htl]") as "(Hol&Htl)"; first iFrame.
    assert (∃ W, Ψ !! i = Some W).
    { apply map_Forall2_dom in H2. apply elem_of_dom. rewrite -H2. apply elem_of_dom. done. }
    destruct H3 as (W&LU2). iPoseProof (big_sepM_delete with "HM") as "[H HM]"; first done.
    iDestruct "H" as "(Hm1&%&Hm2&%&%&Hm3&Mm4)".
    iMod (toS_alloc_obl _ _ κ with "Hm1") as "[Hm1 Hsa]".
    iModIntro. iSplitR "Htl Hsa"; [|iFrame].
    iExists (<[i:=κ :: W]>Ψ). replace (dom (<[i:=κ :: W]> Ψ)) with (dom Ψ).
    2:{ rewrite dom_insert_lookup_L; done. }
    iFrame. iSplit.
    { iPureIntro. apply map_Forall2_insert_2; [|done]. specialize (H2 i).
      rewrite LU2 LU in H2. inv H2. rewrite HP in H6. by econstructor.
    }
    iApply (big_sepM_delete _ _ i (κ :: W)); [apply lookup_insert|]. rewrite H3 in LU. inv LU.
    iSplitR "HM".
    - iFrame "Hm1 Hm2". iExists (κ :: l).
      iSplit; [iPureIntro; apply lookup_insert|].
      iAssert (∀ k, ⌜ k ∈ W → k ∉ l' → k ≠ κ ⌝)%I as "%NIN".
      { iIntros (k INW NINl'). destruct (elem_of_list_lookup_1 _ _ INW) as [n LUW].
        iPoseProof (big_sepL_delete _ _ _ _ LUW with "Hm3") as "[[[%IN | NIN] Hge'] Hm3]"; first done.
        destruct (decide (k = κ)); [subst | done]. iPoseProof (oblS_live_done_false with "[$]") as "%F"; done.
      }
      iSplitL "Hge Hm3".
      + rewrite big_opL_cons. iFrame "Hge". iSplit; [iLeft; iPureIntro; set_solver|].
        iApply (big_sepL_impl with "Hm3"). iModIntro. iIntros (???) "[[% | H] He]"; [|iFrame].
        iFrame "He". iLeft. iPureIntro. rewrite -HP. set_solver.
      + rewrite big_opL_permutation'; [|eauto]. iFrame.
        iPureIntro. apply Ord.lt_le, Ord.from_wf_set_upperbound.
    - rewrite delete_insert_delete. iApply (big_sepM_impl with "HM"). iModIntro. iIntros (???) "[Hts (%&H1&%&%&H2&H3)]".
      iFrame. iPureIntro. destruct (decide (i = k)); subst.
      + exfalso. rewrite lookup_delete in H4. done.
      + rewrite lookup_insert_ne; done.
  Qed.

  Lemma toI_fulfill_obl γ i κ l :
    toI γ ∗ toL_thread i 1 (κ :: l)
    ⊢ |==> oblS_live κ (1/2 + 1/2/2) ∗ (oblS_done κ -∗ toI (<[i:=l]>γ) ∗ toL_thread i 1 l).
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & Ht)".
    iPoseProof (toL_thread_lookup with "[Hol Ht]") as "%"; first iFrame. destruct H3 as (l'&LUγ&Perml).
    pose proof (map_Forall2_lookup_l _ _ _ H2 _ _ LUγ) as Hlu. destruct Hlu as (W&LUΨ&Hsub).
    iPoseProof (big_sepM_delete _ _ _ _ LUΨ with "HM") as "[HP HM]".
    iDestruct "HP" as "(Hp1 & % & Hp2 & % & % & Hp3 & Hpl)".
    rewrite LUγ in H3. inv H3.
    rewrite (big_opL_permutation _ _ _ Perml). iPoseProof (big_sepL_cons with "Hpl") as "[[HL1 _] Hpl]". iFrame "HL1".
    iMod (toL_obl_free with "[Hol Ht]") as "[Hol Ht]"; first iFrame.
    iIntros "!> #Hd". iAssert (⌜ κ ∉ l ⌝)%I as "%NIN".
    { destruct (decide (κ ∈ l)); [|done]. destruct (elem_of_list_lookup_1 _ _ e) as [n LUW].
      iPoseProof (big_sepL_delete _ _ _ _ LUW with "Hpl") as "[[Hlive _] Hpl]".
      iPoseProof (oblS_live_done_false with "[Hlive Hd]") as "%F"; [by iFrame | done].
    }
    iFrame "Ht". iExists Ψ. iSplit.
    { iPureIntro. intros j. destruct (decide (i = j)).
      - subst. rewrite lookup_insert LUΨ. econstructor. etransitivity; [|eapply Hsub]. rewrite Perml. by econstructor.
      - rewrite lookup_insert_ne; done.
    }
    iFrame "Hos Hol". iApply (big_sepM_delete _ _ _ _ LUΨ). iSplitR "HM".
    - iFrame. iSplit; first by rewrite lookup_insert. iApply (big_sepL_impl with "Hp3").
      iModIntro. iIntros (k x ?) "[[% | H] He]".
      + iFrame. destruct (decide (x = κ)).
        * subst. iRight. done.
        * iLeft; iPureIntro. rewrite Perml in H4. set_solver.
      + iFrame.
    - iApply (big_sepM_impl with "HM"). iModIntro. iIntros (k x ?) "(H1&%&H2&%&%&H3&H4)". iFrame.
      iPureIntro. rewrite lookup_insert_ne; first done. intros eq. subst. rewrite lookup_delete in H3. done.
  Qed.

  Lemma toI_oblS_done_notin γ κ :
    toI γ ∗ oblS_done κ ⊢ ⌜ ∀ i L, γ !! i = Some L → κ ∉ L ⌝.
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & #Hd)". iIntros (i L LUγ).
    destruct (map_Forall2_lookup_l _ _ _ H2 _ _ LUγ) as (?&?&?).
    iPoseProof (big_sepM_delete _ _ _ _ H3 with "HM") as "[H _]".
    iDestruct "H" as "(_&%&_&%&%&Hx&HL)". destruct (decide (κ ∈ L)); [|done].
    iExFalso. rewrite LUγ in H5. inv H5. apply elem_of_list_lookup_1 in e. destruct e.
    iPoseProof (big_sepL_delete _ _ _ _ H5 with "HL") as "[[L _] _]".
    iPoseProof (oblS_live_done_false with "[L]") as "%F"; [by iFrame | done].
  Qed.

  Lemma toI_obl_reset_fuel γ i q l :
    toI γ ∗ toL_thread i q l ∗ ([∗ list] k ∈ l, (oblS_credit k (Ord.from_wf_set (WFOCM.lt_wf))))
    ⊢ (∃ f, sfS_fuel_bound i f 1) ∗ (∀ f, sfS_fuel_bound i f 1 -∗ (toI γ ∗ toL_thread i q l)).
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & Ht & HL)".
    iPoseProof (toL_thread_lookup with "[Hol Ht]") as "(%&%LUγ&%Perml)"; first iFrame.
    pose proof (map_Forall2_lookup_l _ _ _ H2 _ _ LUγ) as Hlu. destruct Hlu as (W&LUΨ&Hsub).
    iPoseProof (big_sepM_delete _ _ _ _ LUΨ with "HM") as "[HP HM]".
    iDestruct "HP" as "(Hp1 & % & Hp2 & % & % & Hp3 & Hpl)".
    rewrite LUγ in H3. inv H3. iSplitL "Hp2"; first iFrame. iIntros (?) "Hp2".
    iFrame "Ht". iExists Ψ. iSplit; first done. iFrame "Hos Hol".
    iApply (big_sepM_delete _ _ _ _ LUΨ). iFrame "HM". iFrame. iSplit; first done.
    rewrite <-(big_opL_permutation _ _ _ Perml). iCombine "HL Hpl" as "Hl". iPoseProof (big_sepL_sep with "Hl") as "Hl".
    iApply (big_sepL_impl with "Hl"). iModIntro. iIntros (j k LUk) "(Hc&Hl&(Ha & _))".
    iFrame. iPureIntro. apply Ord.lt_le, Ord.from_wf_set_upperbound.
  Qed.

  Lemma toS_assigned_obls_elem_of i K Ψ :
    K ≠ ∅ →
    (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom Ψ)))) ∗ 
    ([∗ map] j ↦ W ∈ Ψ, toS_thread j W) ∗
    ([∗ set] k ∈ K, toS_assigned i k)
    ⊢ ∃ W : list obl_id, ⌜Ψ !! i = Some W⌝ ∧ ([∗ set] k ∈ K, ⌜k ∈ W⌝).
  Proof.
    iIntros (KE) "(Hos&Hts&#HK)".
    assert (K ≢ ∅) by set_solver. apply size_non_empty_iff in H2. assert (0 < size K) by lia.
    apply size_pos_elem_of in H3. destruct H3 as [k Hk].
    iPoseProof (big_sepS_delete _ _ _ Hk with "HK") as "[Hk _]".
    iPoseProof (toS_assigned_elem_of _ _ _ with "[Hos Hk]") as "%Hkp"; first by iFrame.
    apply elem_of_gset_to_coPset, elem_of_dom in Hkp. destruct Hkp. iExists x. iSplit; first done.
    iApply big_sepS_forall. iIntros (??). iPoseProof (big_sepS_delete _ _ _ H4 with "HK") as "[Hx _]".
    iPoseProof (big_sepM_delete _ _ _ _ H3 with "Hts") as "[Ht Hts]".
    iApply (toS_thread_assigned_inv with "[Ht Hx]"); by iFrame.
  Qed.

  Lemma toI_obl_progress {OFW : OrdFromWFOCM WF} γ i (K : gset obl_id) :
    toI γ ∗ sfS_fuel_credit_forall ∗ ([∗ set] k ∈ K, toS_assigned i k)
    ⊢ |==> toI γ ∗ ([∗ set] k ∈ K, (∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblS_credit k c) ∨ oblS_done k).
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & Hcf & #HK)".
    destruct (decide (K = ∅)).
    { subst. iFrame. iModIntro. iSplit; first done. rewrite !big_sepS_empty. done. }
    iPoseProof (toS_assigned_obls_elem_of i K Ψ n with "[Hos HM]") as "(%&%LUΨ&#HKin)".
    { iFrame. iSplitL; [| done]. iApply (big_sepM_impl with "HM"). iModIntro. by iIntros (???) "[H _]". }
    iPoseProof (big_sepM_delete _ _ _ _ LUΨ with "HM") as "[(Hm1&%&Hm2&%&%&#Hm3&Hm4) HM]".
    iAssert (
        (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom Ψ)))) ∗
        (own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ))) ∗
        ([∗ map] k↦y ∈ delete i Ψ,
           toS_thread k y ∗
           ∃ f0, sfS_fuel_bound k f0 1 ∗
                 ∃ L0, ⌜γ !! k = Some L0⌝ ∗
                       ([∗ list] k0 ∈ y, (⌜k0 ∈ L0⌝ ∨ oblS_done k0) ∗ oblG_elem k0) ∗
                       ([∗ list] k0 ∈ L0, oblS_live k0 (1/2 + 1 / 2 / 2) ∗
                                          oblS_active k0 ∗ ∃ a : Ord.t,
                                              ⌜(Ord.from_wf WFOCM.lt_wf f0 <= a)%ord⌝ ∗ oblS_credit k0 a)) ∗
        |==> (toS_thread i W ∗
              ∃ f', sfS_fuel_bound i f' 1 ∗
                    ([∗ list] k ∈ W, (⌜k ∈ L⌝ ∨ oblS_done k) ∗ oblG_elem k) ∗
                    ([∗ list] k ∈ L, oblS_live k (1/2 + 1 / 2 / 2) ∗ oblS_active k ∗
                                     ∃ a : Ord.t, ⌜(Ord.from_wf WFOCM.lt_wf f' <= a)%ord⌝ ∗ oblS_credit k a) ∗
                    ([∗ set] k ∈ K, (∃ c : Ord.t, ⌜ (Ord.O < c)%ord ⌝ ∗ oblS_credit k c) ∨ oblS_done k)
      ))%I with "[-]" as "(H1&H2&H3&>(Ht&%&Hs&HW&HL&HR))".
    2:{ iModIntro. iFrame "H1 H2 HR". iSplit; first done. iApply (big_sepM_delete _ _ _ _ LUΨ with "[-]"). by iFrame. }
    iFrame "Hos Hol HM Hm1". iMod (sfS_fuel_pay_forall with "[Hcf Hm2]") as "(%f'&%Hltf&Hcf)"; first iFrame.
    iFrame "Hcf". iFrame "Hm3". iAssert ([∗ set] k ∈ K, ⌜k ∈ L⌝ ∨ oblS_done k)%I as "#HK2".
    { iApply big_sepS_forall. iIntros (x INx). iDestruct "HKin" as "%HKin".
      assert (LUW : ∃ z, W !! z = Some x).
      { apply elem_of_list_lookup_1. set_solver. }
      destruct LUW as [z LUW]. iPoseProof (big_sepL_delete _ _ _ _ LUW with "Hm3") as "[[Hx _] _]". done.
    }
    iAssert (|==> [∗ list] k ∈ L, (oblS_live k (1/2 + 1 / 2 / 2) ∗ oblS_active k ∗ ∃ a : Ord.t, ⌜(Ord.from_wf WFOCM.lt_wf f' <= a)%ord⌝ ∗ oblS_credit k a) ∗
                             (∃ c : Ord.t, ⌜ (Ord.O < c)%ord ⌝ ∗ oblS_credit k c))%I with "[Hm4]" as ">Hm4".
    { rewrite -big_sepL_bupd. iApply (big_sepL_impl with "Hm4").
      iModIntro. iIntros (???) "(Hl & Ha & % & % & Hc)".
      apply WFOCM.lt_exists_left in Hltf. destruct Hltf as (c&LTc&LEc).
      assert ((Ord.from_wf WFOCM.lt_wf f' ⊕ Ord.from_wf WFOCM.lt_wf c) <= a)%ord.
      { etransitivity; [|eauto]. rewrite <-ord_from_wfocm_hess_add. by apply ord_from_wfocm_le. }
      iMod (oblS_credit_mon_split x with "Hc") as "[Hf Hc]"; first by eapply H6.
      iModIntro. iSplitR "Hc"; first by iFrame. iFrame. iPureIntro. by apply ord_from_wfocm_unit_lt.
    }
    iPoseProof (big_sepL_sep with "Hm4") as "[Hm41 Hm42]". iFrame "Hm41". iModIntro.
    iClear "HK HKin Hm3". iStopProof. clear n H3. revert L. pattern K. revert K. apply set_ind.
    { solve_proper. }
    { iIntros. done. }
    iIntros (k K NIN IH) "% [#HK HL]". destruct (decide (k ∈ K)).
    { assert ({[k]} ∪ K = K) by set_solver. rewrite !H3. by iApply (IH L). }
    rewrite !(big_sepS_union _ {[k]} K); [|set_solver|set_solver].
    rewrite !big_sepS_singleton. iDestruct "HK" as "[[%Lk | #Hd] HK]".
    - destruct (elem_of_list_lookup_1 _ _ Lk) as [v LUL]. pose proof (delete_Permutation _ _ _ LUL).
      iPoseProof (big_opL_permutation with "HL") as "HL".
      { symmetry. apply H3. }
      rewrite big_sepL_cons. iDestruct "HL" as "[Hl HL]".
      iSplitL "Hl"; first by iLeft. iApply (IH (delete v L)). iSplitR.
      + iModIntro. iApply (big_sepS_impl with "HK"). iModIntro. iIntros (x INx) "[%INxL | Hd]"; [|by iRight].
        iLeft. iPureIntro. destruct (decide (x = k)); first set_solver.
        destruct (elem_of_list_lookup_1 _ _ INxL) as [u LUx]. destruct (decide (u = v)).
        { subst. rewrite LUL in LUx. inv LUx. }
        destruct (decide (u < v)).
        { eapply (elem_of_list_lookup_2 _ u).  rewrite lookup_delete_lt; done. }
        { destruct u; first lia. eapply (elem_of_list_lookup_2). rewrite lookup_delete_ge; first done. lia. }
      + done.
    - iSplitR; [by iRight|].
      iApply (IH L). by iFrame.
  Qed.

  Lemma toI_assigned_obl_cases γ i κ :
    toI γ ∗ toS_assigned i κ
    ⊢ (oblS_done κ ∗ oblG_elem κ) ∨ ⌜ ∃ L, γ !! i = Some L ∧ κ ∈ L ⌝.
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & #Hκ)".
    iPoseProof (toS_assigned_obls_elem_of i {[ κ ]} Ψ with "[Hos HM]") as "(%&%&%)".
    { set_solver. }
    { iFrame "Hos". iSplitL.
      - iApply (big_sepM_impl with "HM"). iModIntro. iIntros (???) "[H _]". done.
      - by rewrite big_sepS_singleton.
    }
    apply set_Forall_singleton in H4. iPoseProof (big_sepM_delete _ _ _ _ H3 with "HM") as "[Hm _]".
    iDestruct "Hm" as "(_&%&_&%&%&H1&H2)". apply elem_of_list_lookup_1 in H4. destruct H4.
    iPoseProof (big_sepL_delete _ _ _ _ H4 with "H1") as "[[[% | #Hd] He] _]".
    - iRight; iPureIntro. exists L. done.
    - iLeft. by iFrame.
  Qed.

  Lemma toI_assigned_obls_split_dom γ (D : obl_ids) :
    toI γ ∗ ([∗ set] κ ∈ D, ∃ i, toS_assigned i κ)
    ⊢ ∃ D1 D2, ⌜ D = D1 ∪ D2 ∧ D1 ## D2 ⌝ ∗
               ([∗ set] κ ∈ D1, oblS_done κ ∗ oblG_elem κ) ∗
               ([∗ set] κ ∈ D2, ⌜ ∃ i L, γ !! i = Some L ∧ κ ∈ L ⌝).
  Proof.
    pattern D. revert D. apply set_ind.
    { solve_proper. }
    { iIntros "[_ #B]". iExists ∅, ∅. iSplit; [iPureIntro; set_solver|]. rewrite !big_sepS_empty. done. }
    iIntros (κ D NINκ IH). iIntros "(HtoI & #HDκ)".
    iPoseProof (big_sepS_union with "HDκ") as "[#Hκ #HD]"; first set_solver.
    iPoseProof (IH with "[HtoI]") as "(%&%&%HDD&#HD1&#HD2)".
    { iSplitL; [iFrame|done]. }
    rewrite big_sepS_singleton. iDestruct "Hκ" as "[% Hiκ]". iClear "HDκ HD".
    iPoseProof (toI_assigned_obl_cases with "[HtoI]") as "[#Hd | %]"; first by iFrame.
    - iExists ({[κ]} ∪ D1), D2. iSplit; first (iPureIntro; set_solver).
      iSplit; [|done]. rewrite big_sepS_union; [|set_solver]. iSplit; [|done].
      rewrite big_sepS_singleton. done.
    - iExists D1, ({[κ]} ∪ D2). iSplit; first (iPureIntro; set_solver).
      iSplit; first done. rewrite big_sepS_union; [|set_solver]. iSplit; [|done].
      rewrite big_sepS_singleton. iPureIntro. exists i. done.
  Qed.

  Lemma toI_toL_thread_lookup γ i q l :
    toI γ ∗ toL_thread i q l ⊢ ∃ l', ⌜ γ !! i = Some l' ⌝ ∧ ⌜ l' ≡ₚ l ⌝.
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & Htl)".
    iApply toL_thread_lookup; iFrame.
  Qed.

  Lemma toI_unique_assign γ i L κ :
    γ !! i = Some L → κ ∈ L →
    toI γ ⊢ ⌜ ∀ i' L', γ !! i' = Some L' → κ ∈ L' → i = i' ⌝.
  Proof.
    iIntros (LU IN). rewrite /toI -!lock. iIntros "(%&%&Hos&Hol&HM)".
    iIntros (i' L' LU' IN'). destruct (decide (i' = i)); first by subst.
    iExFalso. assert (LU2 : ∃ W, Ψ !! i = Some W).
    { eapply map_Forall2_lookup_l in H2; [|eapply LU]. destruct H2 as (?&?&?). eauto. }
    assert (LU2' : ∃ W, Ψ !! i' = Some W).
    { eapply map_Forall2_lookup_l in H2; [|eapply LU']. destruct H2 as (?&?&?). eauto. }
    destruct LU2 as (W&LU2). destruct LU2' as (W'&LU2').
    iPoseProof (big_sepM_delete _ _ _ _ LU2 with "HM") as "[H HM]".
    assert (LU3 : delete i Ψ !! i' = Some W').
    { rewrite lookup_delete_ne; eauto. }
    iPoseProof (big_sepM_delete _ _ _ _ LU3 with "HM") as "[H' HM]".
    iDestruct "H" as "(_&%&_&%&%&_&HL)". iDestruct "H'" as "(_&%&_&%&%&_&HL')".
    rewrite LU in H3. inv H3. 
    apply elem_of_list_lookup_1 in IN. destruct IN as (j&IN).
    apply elem_of_list_lookup_1 in IN'. destruct IN' as (j'&IN').
    iPoseProof (big_sepL_delete _ _ _ _ IN with "HL") as "[HL _]". iDestruct "HL" as "[HL _]".
    iPoseProof (big_sepL_delete _ _ _ _ IN' with "HL'") as "[HL' _]". iDestruct "HL'" as "[HL' _]".
    iCombine "HL HL'" as "HL". iPoseProof (oblS_live_dfrac_op with "HL") as "HL".
    { replace (1 / 2 + 1 / 2 / 2 + (1 / 2 + 1 / 2 / 2))%Qp with (1 / 2 + 1 / 2 + (1 / 2 / 2 + 1 / 2 / 2))%Qp.
      2:{ rewrite !Qp.add_assoc. f_equal. rewrite -!Qp.add_assoc. f_equal. apply Qp.add_comm. }
      rewrite !Qp.div_2. reflexivity.
    }
    iPoseProof (oblS_live_valid with "HL") as "%F". by apply Qp.not_add_le_l in F.
  Qed.

  Lemma oftI_alloc_thread Ω δ γ i :
    δ !! i = None → γ !! i = None →
    oftI Ω δ γ ⊢ ∀ f, oftI Ω (<[i:=f]>δ) (<[i:=[]]>γ).
  Proof.
    rewrite /oftI. iIntros (LUδ LUγ) "[#HΩ #H]". iIntros (f). iSplit; first done.
    iApply big_sepM2_insert_2; [|done]. by rewrite big_sepL_nil.
  Qed.

  Lemma oftI_alloc_obl Ω δ γ κ i f f' l a :
    Ω !! κ = None → δ !! i = Some f → (f /≤ f') → γ !! i = Some l →
    oftI Ω δ γ ∗ toS_assigned i κ
    ⊢ oftI (<[κ:=obl_live (a, f')]>Ω) δ (<[i:=κ :: l]>γ).
  Proof.
    rewrite /oftI. iIntros (LUΩ LUδ LEf LUγ) "((#HΩ&#H)&#Ha)".
    rewrite dom_insert_L big_sepS_union; cycle 1.
    { apply not_elem_of_dom_2 in LUΩ. set_solver. }
    rewrite big_sepS_singleton. iFrame "HΩ Ha".
    rewrite !big_sepM2_forall. iDestruct "H" as "(%&%)". iSplit; iPureIntro.
    { rewrite <-(insert_id δ i f); [|auto]. intros. specialize (H2 k). destruct (decide (k = i)).
      - subst. rewrite !lookup_insert. done.
      - by rewrite !lookup_insert_ne.
    }
    simpl. intros. destruct (decide (i = x)).
    - subst. rewrite lookup_insert in H5. inv H5. rewrite lookup_cons in H6. destruct (decide (x2 = κ)).
      + subst. exists (a, f'). rewrite lookup_insert. simpl; eauto.
      + destruct k.
        { by inv H6. }
        rewrite lookup_insert_ne; [|auto]. eapply H3; eauto.
    - rewrite lookup_insert_ne in H5; [|auto]. destruct (decide (x2 = κ)).
      + subst. specialize (H3 _ _ _ H4 H5 _ _ H6). destruct H3 as (c&?&?). rewrite LUΩ in H3. inv H3.
      + rewrite lookup_insert_ne; [|auto]. eapply H3; eauto.
  Qed.

  Lemma oftI_fulfill_obl Ω δ γ κ i l l' P :
    is_Some (Ω !! κ) → γ !! i = Some l' → l' ≡ₚ (κ :: l) → (∀ j L, (<[i:=l]>γ) !! j = Some L → κ ∉ L) →
    oftI Ω δ γ ⊢ oftI (<[κ:=obl_done P]>Ω) δ (<[i:=l]>γ).
  Proof.
    rewrite /oftI. iIntros (LUΩ LUγ PERMl NIN) "(#HΩ&#H)". rewrite dom_insert_L. rewrite subseteq_union_1_L.
    2:{ apply elem_of_dom in LUΩ. set_solver. }
    iFrame "HΩ". rewrite !big_sepM2_forall. iDestruct "H" as "(%&#HL)".
    assert (LUδ : is_Some (δ !! i)).
    { specialize (H2 i). rewrite H2. done. }
    destruct LUδ as [f LUδ]. iSplit.
    { iPureIntro. rewrite <-(insert_id δ i f); [|auto]. intros. specialize (H2 k). destruct (decide (k = i)).
      - subst. rewrite !lookup_insert. done.
      - by rewrite !lookup_insert_ne.
    }
    iIntros (j f' L LUδ2 LUγ2). destruct (decide (j = i)).
    - subst. rewrite lookup_insert in LUγ2. inv LUγ2. iSpecialize ("HL" $! i f l' LUδ LUγ).
      rewrite PERMl. rewrite big_sepL_cons. iDestruct "HL" as "[H HL]". iApply (big_sepL_impl with "HL").
      iModIntro. iIntros (????). iPureIntro. destruct H4 as (C&?&?). destruct (decide (κ = x)).
      + subst. apply elem_of_list_lookup_2 in H3.
        pose proof (lookup_insert γ i L) as LI. specialize (NIN _ _ LI). set_solver.
      + rewrite lookup_insert_ne; [|auto]. eauto.
    - rewrite lookup_insert_ne in LUγ2; [|auto]. specialize (NIN j L). rewrite lookup_insert_ne in NIN; [|auto].
      specialize (NIN LUγ2). iSpecialize ("HL" $! _ _ _ LUδ2 LUγ2). iApply (big_sepL_impl with "HL").
      iModIntro. iIntros (????). destruct (decide (x = κ)).
      + subst. apply elem_of_list_lookup_2 in H3. set_solver.
      + rewrite lookup_insert_ne; [|auto]. done.
  Qed.

  Lemma oftI_schedule_1 (Ω : obl_states' OC) (γ : gmap thread_id (list obl_id)) (δ1 δ2 : gmap thread_id A) (S : thread_ids) D1 D2 :
    map_Forall2 (λ i f1 f2, if decide (i ∈ S) then True else (f2 /< f1)) δ1 δ2 →
    (∀ i, is_Some (δ1 !! i) ↔ is_Some (γ !! i)) →
    (∀ i f L, δ1 !! i = Some f → γ !! i = Some L → ∀ κ, κ ∈ L → ∃ c, Ω !! κ = Some (obl_live c) ∧ leR f c.2) →
    dom Ω = D1 ∪ D2 →
    D1 ## D2 →
    set_Forall (λ κ, ∃ P, Ω !! κ = Some (obl_done P)) D1 →
    set_Forall (λ κ, ∃ i L, γ !! i = Some L ∧ κ ∈ L) D2 →
    map_Forall (λ κ o, match o with
                       | obl_live (a, b) =>
                           (∃ i L, (γ !! i = Some L) ∧ κ ∈ L ∧
                                   if (decide (i ∈ S)) then True else ∃ b', b' /< b ∧ ∃ f, δ2 !! i = Some f ∧ f /≤ b)
                       | _ => True
                       end) Ω.
  Proof using Type*.
    intros SF DG1 DG2 HΩ HDD HD1 HD2.
    pose proof (dom_union_inv_L _ _ _ HDD HΩ). destruct H2 as (m1&m2&HΩ2&Hmm&Hm1&Hm2). subst.
    apply map_Forall_union_2.
    - intros κ o LU. assert (κ ∈ dom m1); first by apply elem_of_dom_2 in LU. specialize (HD1 _ H2). simpl in HD1.
      destruct HD1 as (P&HD1). rewrite lookup_union_l' in HD1; [|done].
      rewrite LU in HD1. inv HD1. auto.
    - intros κ o LU. assert (κ ∈ dom m2); first by apply elem_of_dom_2 in LU. specialize (HD2 _ H2). simpl in HD2.
      destruct HD2 as (i&L&LUi&INL). assert (∃ f, δ1 !! i = Some f).
      { apply DG1. done. }
      destruct H3. specialize (DG2 _ _ _ H3 LUi _ INL). destruct DG2 as ([a b]&LUm2&LE).
      rewrite lookup_union_r in LUm2.
      2:{ apply not_elem_of_dom. apply elem_of_dom_2 in LU. set_solver. }
      rewrite LU in LUm2. inv LUm2. exists i, L. split; first auto. split; first auto.
      specialize (SF i). rewrite H3 in SF. inv SF. 
      case_decide; first eauto. exists y. apply WFOCM.lt_exists_left in H6. destruct H6 as (z&?&?). split.
      + apply WFOCM.lt_exists_left. exists z. split; first auto. etransitivity; first apply H7. apply LE.
      + exists y. split; first auto. etransitivity; [|eauto]. etransitivity; [|eauto]. apply OCM.add_base_left_le.
  Qed.

  Lemma oftI_schedule_2 (Ω1 Ω2 : obl_states' OC) (δ1 δ2 : gmap thread_id A) (γ : gmap thread_id (list obl_id)) :
    dom δ1 = dom δ2 →
    (Ω1 ↪ₚ⋆ Ω2) →
    (map_Forall (λ κ o, match o with
                        | obl_live (a, b) =>
                            (∃ i L, (γ !! i = Some L) ∧ κ ∈ L ∧ (∃ f, δ2 !! i = Some f ∧ f /≤ b))
                        | _ => True end) Ω2) →
    toI γ ∗ oftI Ω1 δ1 γ ⊢ oftI Ω2 δ2 γ.
  Proof.
    rewrite /oftI. iIntros (DD HP MF) "[HtoI (#HΩ&#H)]".
    pose proof (obl_states_progress_rtc_dom Ω1 Ω2 HP). rewrite H2. iFrame "HΩ".
    iPoseProof (big_sepM2_forall with "H") as "%Hd1". destruct Hd1 as (Hdom1&Hd1).
    iApply big_sepM2_forall. iSplit.
    - iPureIntro. intros. specialize (Hdom1 k). rewrite <-Hdom1. rewrite <-!elem_of_dom. rewrite DD. done.
    - iIntros (i f L LUd2 LUg). iApply big_sepL_forall. iIntros (j κ LUL).
      assert (INL : κ ∈ L).
      { eapply elem_of_list_lookup_2; eauto. }
      iPoseProof (toI_unique_assign _ _ _ _ LUg INL with "HtoI") as "%U".
      iPureIntro.
      assert (∃ b, Ω2 !! κ = Some (obl_live b)).
      { pose proof (elem_of_dom_2 _ _ _ LUd2) as INd2. assert (i ∈ dom δ1) by (rewrite DD; auto).
        apply elem_of_dom in H3. destruct H3.
        specialize (Hd1 _ _ _ H3 LUg _ _ LUL). destruct Hd1 as (c&?&?).
        eapply (obl_states_progress_rtc_live _ _ κ HP). eauto.
      }
      destruct H3 as ([v u]&LUO2). exists (v, u). split; first auto. simpl.
      specialize (MF _ _ LUO2). destruct MF as (i'&L'&LUg'&INL'&f'&LUd2'&LE').
      specialize (U _ _ LUg' INL'). subst. rewrite LUd2' in LUd2. inv LUd2. auto.
  Qed.

End thread_obl.

(* Allocation of an initial thread obligation protocol. *)
Lemma toI_alloc `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} {ps} {Σ} `{@osatGS.osatGS SI Ord.t _ ps Σ} `{@schedfairGS.schedfairGS SI _ _ _ _ WF Σ} `{!threadoblGS Σ} : ⊢ |==> ∃ _ : threadoblGS Σ, toI ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γL) "HG";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (ThreadoblG SI _ _ γS γL).
  rewrite /toI -lock.
  iExists ∅. rewrite !fmap_empty big_opM_empty. iFrame.
  replace (⊤ ∖ gset_to_coPset (dom ∅)) with (⊤ : coPset); [iFrame|].
  { iPureIntro. apply map_Forall2_empty. }
  rewrite -leibniz_equiv_iff. intros x. split; intros IN.
  - apply elem_of_difference. split; [set_solver|].
    intros F. apply elem_of_gset_to_coPset in F. set_solver.
  - set_solver.
Qed.
