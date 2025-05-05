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
Definition toL_thread `{SI : indexT} `{!threadoblGS Σ} (i : thread_id) (l : list obl_id) : iProp Σ :=
  (∃ l', ⌜ l ≡ₚ l' ⌝ ∗ own live_name (gmap_view_frag i (DfracOwn 1) (to_agree l')))%I.
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
        (⌜ map_Forall2 (λ _ l1 l2, l1 ⊆ l2) γ Ψ ⌝) ∗
        (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom Ψ)))) ∗
        (own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ))) ∗
        ([∗ map] i ↦ W ∈ Ψ,
           toS_thread i W ∗
           ∃ (f : A), sfS_fuel_bound i f 1 ∗
                      (∃ L, ⌜ γ !! i = Some L ⌝ ∗
                            ([∗ list] k ∈ W, ⌜k ∈ L⌝ ∨ oblS_done k) ∗
                            ([∗ list] k ∈ L,
                               oblS_live k (1/2/2) ∗
                               ((oblS_idle k (1/2/2) ∗ oblS_credit k (Ord.from_wf_set (WFOCM.lt_wf)))
                                ∨ (oblS_active k ∗ ∃ a, ⌜ (Ord.from_wf (WFOCM.lt_wf) f <= a)%ord ⌝ ∗ oblS_credit k a)))
                      )
        )
    )%I.

Definition oftI `{SI : indexT} {T : Type} `{WF : WFOCM.t A leR addO ltR} `{OC : obl_class obl_ps (T * A)%type} `{!threadoblGS Σ}
  (Ω : obl_states) (δ : gmap thread_id A) (γ : gmap thread_id (list obl_id)) : iProp Σ :=
  (([∗ set] κ ∈ dom Ω, ∃ i, toS_assigned i κ) ∗
   ([∗ map] f; L ∈ δ; γ, [∗ list] k ∈ L, ⌜ ∃ c, Ω !! k = Some (obl_live c) ∧ leR f c.2 ⌝))%I.

Section thread_obligation.
  Context `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} `{OC : obl_class ps (Ord.t * A)%type}.
  Context {Σ} `{@osatGS.osatGS SI _ ord_wfocm_pack ps Σ} `{@schedfairGS.schedfairGS SI _ _ _ _ WF Σ} `{!@threadoblGS SI Σ}.

  Global Instance toS_assigned_persistent i κ : Persistent (toS_assigned i κ).
  Proof. rewrite /toS_assigned. apply _. Qed.
  Global Instance toL_term_persistent i : Persistent (toL_term i).
  Proof. rewrite /toL_term. apply _. Qed.

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

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

  Lemma toS_thread_alloc D i l :
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

  Lemma toS_obligation_alloc i l κ :
    toS_thread i l ⊢ |==> toS_thread i (κ :: l) ∗ toS_assigned i κ.
  Proof.
    rewrite /toS_thread. iIntros "(%&%&H)". iMod (own_update _ _ (reservation_map_data i (●ML (l' ++ [κ]))) with "H") as "H".
    { apply reservation_map_update. apply mono_list_update. apply prefix_app_r. done. }
    iPoseProof (toS_thread_assigned i _ κ with "[H]") as "#Hs".
    2:{ rewrite /toS_thread. iExists (l' ++ [κ]). iFrame. iPureIntro. reflexivity. }
    { set_solver. }
    iFrame. iModIntro. iSplit; [|done]. iPureIntro. rewrite H2. apply Permutation_cons_append.
  Qed.

  Lemma toL_thread_term i :
    toL_thread i [] ⊢ |==> toL_term i.
  Proof.
    rewrite /toL_thread /toL_term. iIntros "(%&%&H)". apply Permutation_nil in H2. subst.
    iApply (own_update with "H"). apply gmap_view_frag_persist.
  Qed.

  Lemma toL_thread_perm i l l' :
    Permutation l l' →
    toL_thread i l ⊣⊢ toL_thread i l'.
  Proof.
    rewrite /toL_thread. iIntros (Hp). iSplit; iIntros "(%&%&H)".
    - iExists l'0. iFrame. iPureIntro. etransitivity; done.
    - iExists l'0. iFrame. iPureIntro. etransitivity; done.
  Qed.

  Lemma toL_thread_elem_of γ i l :
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ)) ∗ toL_thread i l
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

  Lemma toL_thread_alloc γ i l :
    γ !! i = None →
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ))
    ⊢ |==> own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=l]>γ)) ∗ toL_thread i l.
  Proof.
    iIntros (LU) "H". iMod (own_update with "H") as "[H Ht]".
    { apply (gmap_view_alloc _ i (DfracOwn 1) (to_agree l)); [| done | done]. by rewrite lookup_fmap LU. }
    iModIntro. rewrite /toL_thread. iFrame. iSplit; [|done].
    by rewrite fmap_insert.
  Qed.

  Lemma toL_obligation_alloc γ i l κ :
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ)) ∗ toL_thread i l
    ⊢ |==> own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=κ :: l]>γ)) ∗ toL_thread i (κ :: l).
  Proof.
    rewrite /toL_thread. iIntros "[H (%&%&Ht)]". iCombine "H Ht" as "H".
    iMod (own_update _ _ (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=κ :: l]>γ) ⋅ gmap_view_frag i (DfracOwn 1) (to_agree (κ :: l))) with "H") as "[H Ht]".
    { rewrite fmap_insert. apply gmap_view_replace. done. }
    iFrame. iPureIntro. done.
  Qed.

  Lemma toL_obligation_free γ i κ l :
    own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ)) ∗ toL_thread i (κ :: l)
    ⊢ |==> own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=l]>γ)) ∗ toL_thread i l.
  Proof.
    rewrite /toL_thread. iIntros "[H (%&%&Ht)]". iCombine "H Ht" as "H".
    iMod (own_update _ _ (gmap_view_auth (DfracOwn 1) (to_agree <$> <[i:=l]>γ) ⋅ gmap_view_frag i (DfracOwn 1) (to_agree l)) with "H") as "[H Ht]".
    { rewrite fmap_insert. apply gmap_view_replace. done. }
    iFrame. iPureIntro. done.
  Qed.

  Lemma toI_thread_alloc γ i f :
    γ !! i = None →
    toI γ ∗ sfS_fuel_bound i f 1
    ⊢ |==> toI (<[i:=[]]>γ) ∗ toL_thread i [].
  Proof.
    iIntros (LU) "[HI Hf]". pose proof (not_elem_of_dom_2 _ _ LU) as Hn.
    rewrite /toI -!lock. iDestruct "HI" as "(%&%&Hos&Hol&HM)".
    pose proof (map_Forall2_dom_L _ _ _ H2) as Hde.
    iMod (toS_thread_alloc _ i [] with "Hos") as "[Hos Hts]".
    { intros F. apply Hn. apply elem_of_gset_to_coPset. by rewrite Hde. }
    iMod (toL_thread_alloc _ i [] with "Hol") as "[Hol Htl]".
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

  Lemma toI_obligation_alloc γ i l κ :
    toI γ ∗ toL_thread i l ∗ oblS_live κ (1/2/2) ∗ oblS_idle κ (1/2/2) ∗ oblS_credit κ (Ord.from_wf_set (WFOCM.lt_wf))
    ⊢ |==> toI (<[i:=κ :: l]>γ) ∗ toL_thread i (κ :: l) ∗ toS_assigned i κ.
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & (Htl&Hsl&Hsi&Hsc))".
    iPoseProof (toL_thread_elem_of with "[Hol Htl]") as "%"; first iFrame.
    destruct H3 as (l'&LU&HP).
    iMod (toL_obligation_alloc _ _ _ κ with "[Hol Htl]") as "(Hol&Htl)"; first iFrame.
    assert (∃ W, Ψ !! i = Some W).
    { apply map_Forall2_dom in H2. apply elem_of_dom. rewrite -H2. apply elem_of_dom. done. }
    destruct H3 as (W&LU2). iPoseProof (big_sepM_delete with "HM") as "[H HM]"; first done.
    iDestruct "H" as "(Hm1&%&Hm2&%&%&Hm3&Mm4)".
    iMod (toS_obligation_alloc _ _ κ with "Hm1") as "[Hm1 Hsa]".
    iModIntro. iSplitR "Htl Hsa"; [|iFrame].
    iExists (<[i:=κ :: W]>Ψ). replace (dom (<[i:=κ :: W]> Ψ)) with (dom Ψ).
    2:{ rewrite dom_insert_lookup_L; done. }
    iFrame. iSplit.
    { iPureIntro. apply map_Forall2_insert_2; [|done]. apply list_subseteq_skip.
      specialize (H2 i). rewrite LU2 LU in H2. inv H2.
      rewrite list_subseteq_Permutation; [apply H6 | done | done].
    }
    iApply (big_sepM_delete _ _ i (κ :: W)); [apply lookup_insert|]. rewrite H3 in LU. inv LU.
    iSplitR "HM".
    - iSplitL "Hm1"; [done|]. iExists f. iSplitL "Hm2"; [done|]. iExists (κ :: l).
      iSplit; [iPureIntro; apply lookup_insert|]. iFrame. iSplitL "Hm3".
      + rewrite big_opL_cons. iSplit; [iLeft; iPureIntro; set_solver|].
        iApply (big_sepL_impl with "Hm3"). iModIntro. iIntros (???) "[% | ?]"; [|iFrame].
        iLeft. iPureIntro. rewrite -HP. set_solver.
      + rewrite big_opL_permutation'; [|eauto]. iFrame.
    - rewrite delete_insert_delete. iApply (big_sepM_impl with "HM"). iModIntro. iIntros (???) "[Hts (%&H1&%&%&H2&H3)]".
      iFrame. iPureIntro. destruct (decide (i = k)); subst.
      + exfalso. rewrite lookup_delete in H4. done.
      + rewrite lookup_insert_ne; done.
  Qed.

  Lemma toI_obligation_fulfill γ i κ l :
    toI γ ∗ toL_thread i (κ :: l) ∗ oblS_live κ (1/2/2)
    ⊢ |==> oblS_live κ (1/2) ∗ (oblS_done κ -∗ toI (<[i:=l]>γ) ∗ toL_thread i l).
  Proof.
    rewrite /toI -!lock. iIntros "((%&%&Hos&Hol&HM) & Ht & Hl)".
    iPoseProof (toL_thread_elem_of with "[Hol Ht]") as "%"; first iFrame. destruct H3 as (l'&LUγ&Perml).
    pose proof (map_Forall2_lookup_l _ _ _ H2 _ _ LUγ) as Hlu. destruct Hlu as (W&LUΨ&Hsub).
    iPoseProof (big_sepM_delete _ _ _ _ LUΨ with "HM") as "[HP HM]".
    iDestruct "HP" as "(Hp1 & % & Hp2 & % & % & Hp3 & Hpl)".
    rewrite LUγ in H3. inv H3.
    rewrite (big_opL_permutation _ _ _ Perml). iPoseProof (big_sepL_cons with "Hpl") as "[[HL1 _] Hpl]".
    iCombine "Hl HL1" as "Hl". iPoseProof (oblS_live_div_2 with "Hl") as "Hl". iFrame "Hl".
    iMod (toL_obligation_free with "[Hol Ht]") as "[Hol Ht]"; first iFrame.
    iIntros "!> #Hd". iFrame "Ht". iExists Ψ. iSplit.
    { iPureIntro. intros j. destruct (decide (i = j)).
      - subst. rewrite lookup_insert LUΨ. econstructor. etransitivity; [|eapply Hsub]. rewrite Perml. set_solver.
      - rewrite lookup_insert_ne; done.
    }
    iFrame "Hos Hol". iApply (big_sepM_delete _ _ _ _ LUΨ). iSplitR "HM".
    - iFrame. iSplit; first by rewrite lookup_insert. iApply (big_sepL_impl with "Hp3").
      iModIntro. iIntros (k x ?) "[% | H]"; [|iRight; done]. destruct (decide (x = κ)).
      + subst. by iRight.
      + iLeft; iPureIntro. rewrite Perml in H4. set_solver.
    - iApply (big_sepM_impl with "HM"). iModIntro. iIntros (k x ?) "(H1&%&H2&%&%&H3&H4)". iFrame.
      iPureIntro. rewrite lookup_insert_ne; first done. intros eq. subst. rewrite lookup_delete in H3. done.
  Qed.

  TODO

  Lemma toI_obligation_progress γ i l :
    toI γ ∗ toL_thread i l ∗
    ⊢ |==> toI γ ∗ toL_thread i l ∗  .
  Proof.

    Definition toI `{SI : indexT} `{WF : WFOCM.t A leR addO ltR} {ps} {Σ}
  `{@osatGS.osatGS SI Ord.t _ ps Σ} `{@schedfairGS.schedfairGS SI _ _ _ _ WF Σ} `{!threadoblGS Σ}
  (γ : gmap thread_id (list obl_id))
  : iProp Σ :=
  locked
    (∃ (Ψ : gmap thread_id (list obl_id)),
        (⌜ map_Forall2 (λ _ l1 l2, l1 ⊆ l2) γ Ψ ⌝) ∗
        (own state_name (reservation_map_token (⊤ ∖ gset_to_coPset (dom Ψ)))) ∗
        (own live_name (gmap_view_auth (DfracOwn 1) (to_agree <$> γ))) ∗
        ([∗ map] i ↦ W ∈ Ψ,
           toS_thread i W ∗
           ∃ (f : A), sfS_fuel_bound i f 1 ∗
                      (∃ L, ⌜ γ !! i = Some L ⌝ ∗
                            ([∗ list] k ∈ W, ⌜k ∈ L⌝ ∨ oblS_done k) ∗
                            ([∗ list] k ∈ L,
                               oblS_live k (1/2/2) ∗
                               ((oblS_idle k (1/2/2) ∗ oblS_credit k (Ord.from_wf_set (WFOCM.lt_wf)))
                                ∨ (oblS_active k ∗ ∃ a, ⌜ (Ord.from_wf (WFOCM.lt_wf) f <= a)%ord ⌝ ∗ oblS_credit k a)))
                      )
        )
    )%I.


  Definition oftI `{SI : indexT} {T : Type} `{WF : WFOCM.t A leR addO ltR} `{OC : obl_class obl_ps (T * A)%type} `{!threadoblGS Σ}
  (Ω : obl_states) (δ : gmap thread_id A) (γ : gmap thread_id (list obl_id)) : iProp Σ :=
  (([∗ set] κ ∈ dom Ω, ∃ i, toS_assigned i κ) ∗
   ([∗ map] f; L ∈ δ; γ, [∗ list] k ∈ L, ⌜ ∃ c, Ω !! k = Some (obl_live c) ∧ leR f c.2 ⌝))%I.

End thread_obligation.

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
