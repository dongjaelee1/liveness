From iris.algebra Require Import agree gmap gmap_view reservation_map mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.algebra Require Export tree.
From liris.base_logic Require Export otree.

(* From a thread's view, its obligation has the following life cycle:
     owned -> maybe = suspended \/ returned -> owned -> ... -> resolved.
 *)

Variant tvo_sus {A : Type} `{WFA : WFOCM.pack A} : Type :=
  | tvo_sus_data (x : positive) (π : obl_id) (ψ δ α : A).
  (* | tvo_sus_data (x : positive) (π : obl_id) (ψ δ α : A). *)

Variant thread_view_obl {A : Type} `{WFA : WFOCM.pack A} : Type :=
  | tvo (l : list tvo_sus) (δ : A) (α : A).
(* | tvo_maybe (x : positive) (π : obl_id) (ψ : A) (δ0 δ1 : A) (α0 α1 : A). *)

Fixpoint tvo_interp `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS.otreeGS A Σ}
  (i : positive) (k : obl_id) (l : list tvo_sus) (δ : A) (α : A) : iProp Σ :=
  match l with
  | nil =>
      (othreadG_owns i k true (1/2) ∗ oblG_suspend k δ ∗ oblG_progress k α)
  | hd :: tl =>
      match hd with
      | tvo_sus_data x π ψ η β =>
          (oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ (⌜ WFOCM.leR δ η ∧ WFOCM.leR α β ⌝) ∗
           ((otreeG_wait k x (1/2) ∗ oblG_suspend k η ∗ oblG_progress k β)
            ∨
              (oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ tvo_interp i k tl δ α)))
      end
  end.
(* match hd with *)
(* | tvo_sus_data x π ψ η β => *)
(*    oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ (⌜ WFOCM.leR δ η ∧ WFOCM.leR α β ⌝) ∗ *)
(*    ((otreeG_wait k x (1/2) ∗ oblG_suspend k η ∗ oblG_progress k β) *)
(*     ∨ *)
(*       (oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ tvo_interp i k tl δ α)) *)
(* end *)

Definition tvos_interp `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS.otreeGS A Σ}
  (i : positive) (Δ : gmap obl_id (thread_view_obl (WFA:=WFA))) : iProp Σ :=
  ([∗ map] k ↦ v ∈ Δ,
     oblG_elem k ∗ otreeG_elem k ∗
     match v with
     | tvo l δ α => tvo_interp i k l δ α
     end)%I.

(* Definition tvos_owned *)
(*   `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ} *)
(*   `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS.otreeGS A Σ} *)
(*   (i : positive) (Δ : gmap obl_id (thread_view_obl (WFA:=WFA))) : iProp Σ := *)
(*   ([∗ map] k ↦ v ∈ Δ, *)
(*      oblG_elem k ∗ otreeG_elem k ∗ *)
(*      match v with *)
(*      | tvo_owned q δ α => *)
(*          othreadG_owns i k true q ∗ oblG_suspend k δ ∗ oblG_progress k α *)
(*      | tvo_maybe x π ψ δ0 δ1 α0 α1 => *)
(*          False *)
(*      end)%I. *)

(* Definition tvos_maybe `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ} *)
(*   `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS.otreeGS A Σ} *)
(*   (i : positive) (Δ : gmap obl_id (thread_view_obl (WFA:=WFA))) : iProp Σ := *)
(*   ([∗ map] k ↦ v ∈ Δ, *)
(*      oblG_elem k ∗ otreeG_elem k ∗ *)
(*      match v with *)
(*      | tvo_owned q δ α => *)
(*          False *)
(*      | tvo_maybe x π ψ δ0 δ1 α0 α1 => *)
(*          oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ (⌜ WFOCM.leR δ1 δ0 ∧ WFOCM.leR α1 α0 ⌝) ∗ *)
(*          ((otreeG_wait k x (1/2) ∗ oblG_suspend k δ0 ∗ oblG_progress k α0) *)
(*           ∨ *)
(*             (othreadG_owns i k true (1/2) ∗ oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ *)
(*              oblG_suspend k δ1 ∗ oblG_progress k α1)) *)
(*      end)%I. *)

(* Definition tvos_all `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ} *)
(*   `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS.otreeGS A Σ} *)
(*   (i : positive) (Δ : gmap obl_id (thread_view_obl (WFA:=WFA))) : iProp Σ := *)
(*   ([∗ map] k ↦ v ∈ Δ, *)
(*      oblG_elem k ∗ otreeG_elem k ∗ *)
(*      match v with *)
(*      | tvo_owned q δ α => *)
(*          othreadG_owns i k true q ∗ oblG_suspend k δ ∗ oblG_progress k α *)
(*      | tvo_maybe x π ψ δ0 δ1 α0 α1 => *)
(*          oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ (⌜ WFOCM.leR δ1 δ0 ∧ WFOCM.leR α1 α0 ⌝) ∗ *)
(*          ((otreeG_wait k x (1/2) ∗ oblG_suspend k δ0 ∗ oblG_progress k α0) *)
(*           ∨ *)
(*             (othreadG_owns i k true (1/2) ∗ oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ *)
(*              oblG_suspend k δ1 ∗ oblG_progress k α1)) *)
(*      end)%I. *)

(* Definition threadG_tvos `{SI : indexT} {A : Type} `{WFA : WFOCM.pack A} {ps} {Σ} *)
(*   `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS.otreeGS A Σ} *)
(*   (i : positive) (f : Qp) (Δ : gmap obl_id (thread_view_obl (WFA:=WFA))) : iProp Σ := *)
(*   locked (othreadG_obls i (dom Δ) f ∗ tvos_superposition i Δ)%I. *)

Section tvos.
  Context `{SI : indexT} `{WFA : WFOCM.pack A}.
  Context {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!othreadGS.othreadGS Σ} `{!otreeGS.otreeGS A Σ}.
  Context `{Ξl : obl_live_class A positive WFOCM.ltR} `{Ξd : obl_done_class ps}.

  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

  Fixpoint tvo_interp_temp
    (B1 B2 : obl_id → A → A → iProp Σ) (C P1 P2 : obl_id → A → A → positive → obl_id → A → A → A → iProp Σ)
    (i : positive) (k : obl_id) (l : list tvo_sus) (δ : A) (α : A) : iProp Σ :=
    match l with
    | nil =>
        ((B1 k δ α) ∗ othreadG_owns i k true (1/2) ∗ (B2 k δ α))
    | hd :: tl =>
        match hd with
        | tvo_sus_data x π ψ η β =>
            ((C k δ α x π ψ η β) ∗
             (((P1 k δ α x π ψ η β) ∗ othreadG_owns i k false (1/2))
              ∨
                ((P2 k δ α x π ψ η β) ∗ tvo_interp_temp B1 B2 C P1 P2 i k tl δ α)))
        end
    end.

  Fixpoint tvo_interp_temp_true
    (B1 B2 : obl_id → A → A → iProp Σ) (C P1 P2 : obl_id → A → A → positive → obl_id → A → A → A → iProp Σ)
    (i : positive) (k : obl_id) (l : list tvo_sus) (δ : A) (α : A) : iProp Σ :=
    match l with
    | nil =>
        ((B1 k δ α) ∗ othreadG_owns i k true (1/2) ∗ (B2 k δ α))
    | hd :: tl =>
        match hd with
        | tvo_sus_data x π ψ η β =>
            ((C k δ α x π ψ η β) ∗
             ((P2 k δ α x π ψ η β) ∗ tvo_interp_temp_true B1 B2 C P1 P2 i k tl δ α))
        end
    end.
  Fixpoint tvo_interp_temp_false
    (C P1 P2 : obl_id → A → A → positive → obl_id → A → A → A → iProp Σ)
    (i : positive) (k : obl_id) (l : list tvo_sus) (δ : A) (α : A) : iProp Σ :=
    match l with
    | nil =>
        False
    | hd :: tl =>
        match hd with
        | tvo_sus_data x π ψ η β =>
            ((C k δ α x π ψ η β) ∗
             (((P1 k δ α x π ψ η β) ∗ othreadG_owns i k false (1/2))
              ∨
                ((P2 k δ α x π ψ η β) ∗ tvo_interp_temp_false C P1 P2 i k tl δ α)))
        end
    end.

  Lemma tvo_interp_temp_true_impl B1 B2 C P1 P2 i k l δ α :
    tvo_interp_temp_true B1 B2 C P1 P2 i k l δ α ⊢ tvo_interp_temp B1 B2 C P1 P2 i k l δ α.
  Proof.
    revert δ α. induction l; simpl; intros; iIntros "H".
    { iFrame. }
    destruct a. iDestruct "H" as "(C& P2& H)". iFrame. iRight. iFrame. iApply IHl. iFrame.
  Qed.
  Lemma tvo_interp_temp_false_impl B1 B2 C P1 P2 i k l δ α :
    tvo_interp_temp_false C P1 P2 i k l δ α ⊢ tvo_interp_temp B1 B2 C P1 P2 i k l δ α.
  Proof.
    revert δ α. induction l; simpl; intros; iIntros "H".
    { done. }
    destruct a. iDestruct "H" as "(C& [H | H])"; iFrame.
    iDestruct "H" as "[P2 H]". iRight. iFrame. iApply IHl. iFrame.
  Qed.

  Lemma tvo_interp_temp_true_acc B1 B2 B2' C P1 P2 i k l δ α :
    tvo_interp_temp_true B1 B2 C P1 P2 i k l δ α
    ⊢ ((B1 k δ α) ∗ othreadG_owns i k true (1/2) ∗ (B2 k δ α)) ∗
    (((B1 k δ α) ∗ othreadG_owns i k true (1/2) ∗ (B2' k δ α)) -∗ tvo_interp_temp_true B1 B2' C P1 P2 i k l δ α).
  Proof.
    induction l; simpl; iIntros "H".
    { iFrame. auto. }
    destruct a. iDestruct "H" as "(C& P2& H)". iPoseProof (IHl with "H") as "(H& ACC)".
    iFrame "H". iIntros "H". iPoseProof ("ACC" with "H") as "H". iFrame.
  Qed.
  Lemma tvo_interp_temp_false_acc C P1 P2 i k l δ α :
    tvo_interp_temp_false C P1 P2 i k l δ α
    ⊢ othreadG_owns i k false (1/2) ∗ (othreadG_owns i k false (1/2) -∗ tvo_interp_temp_false C P1 P2 i k l δ α).
  Proof.
    induction l; simpl; iIntros "H".
    { done. }
    destruct a. iDestruct "H" as "(C& [H | H])".
    - iDestruct "H" as "(P1& H)". iFrame "H". iIntros "H". iFrame "C". iLeft. iFrame.
    - iDestruct "H" as "(P2& H)". iPoseProof (IHl with "H") as "(H& ACC)". iFrame "H". iIntros "H".
      iPoseProof ("ACC" with "H") as "H". iFrame. iRight. iFrame.
  Qed.

  Lemma oforest_aux_progress_one_thread_tvos Ω TP Φ i Ψ (γ : gmap obl_id thread_view_obl)
    (B : obl_id → A → A → iProp Σ) (Q P1 P2 : obl_id → A → A → positive → obl_id → A → A → A → iProp Σ) :
    Ψ = dom γ →
    osat Ω ∗ othread TP ∗ oforest_aux (dom Ω) Φ ∗
    (* from user *)
    othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗
    ([∗ map] k ↦ v ∈ γ,
       oblG_elem k ∗
       match v with
       | tvo l δ α => tvo_interp_temp B (λ k _ _, (∃ a, ⌜ /0 /< a ⌝ ∗ oblG_progress k a)%I) Q P1 P2 i k l δ α
       end)
    ⊢ |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | (obl_cond_owner i) ⌝) ∗
              osat Ω' ∗ othread TP ∗ oforest_aux (dom Ω') Φ ∗
              othreadG_obls i Ψ 1 ∗
              ([∗ map] k ↦ v ∈ γ,
                 oblG_elem k ∗
                 match v with
                 | tvo l δ α => tvo_interp_temp B (λ k _ _, (True)%I) Q P1 P2 i k l δ α
                 end).
  Proof.
    iIntros (Domγ) "(S& T& F& #Tei& Tbi& Tos)".
    iAssert (∃ (γ1 γ2 : gmap obl_id thread_view_obl),
                (⌜ γ = γ1 ∪ γ2 ∧ γ1 ##ₘ γ2 ⌝) ∗
                ([∗ map] ρ ↦ v ∈ γ1,
                   oblG_elem ρ ∗
                   match v with
                   | tvo l δ α => tvo_interp_temp_true B (λ k _ _, (∃ a, ⌜ /0 /< a ⌝ ∗ oblG_progress k a)%I) Q P1 P2 i ρ l δ α
                   end) ∗
                ([∗ map] ρ ↦ v ∈ γ2,
                   oblG_elem ρ ∗
                   match v with
                   | tvo l δ α => tvo_interp_temp_false Q P1 P2 i ρ l δ α
                   end)
            )%I with "[Tos]" as "TH".
    { iClear "Tei". clear Domγ. iStopProof. induction γ using map_ind.
      { iIntros "H". iExists ∅, ∅. iSplitR.
        { iPureIntro. split; auto. apply map_disjoint_empty_l. }
        iSplitR; done. }
      iIntros "H". iPoseProof (big_sepM_insert with "H") as "[[#Bei Ti] H]"; first auto.
      iPoseProof (IHγ with "H") as "(%&%&%&H1&H2)". clear IHγ. destruct H3.
      assert (γ1 !! i0 = None ∧ γ2 !! i0 = None).
      { rewrite map_eq_iff in H3. specialize (H3 i0). rewrite H2 in H3.
        symmetry in H3. apply lookup_union_None in H3. auto. }
      destruct H5. destruct x. iStopProof.
      revert δ α m H2 γ1 γ2 H3 H4 H5 H6. induction l; simpl; intros; iIntros "(#Bei& Ti& H1& H2)".
      - iExists (<[i0:=tvo [] δ α]>γ1), γ2. iSplitR.
        { iPureIntro. split_and !.
          - rewrite H3 insert_union_l. auto.
          - apply map_disjoint_insert_l. split; auto. }
        iFrame "H2". iApply big_sepM_insert; first auto. iFrame. auto.
      - destruct a. iDestruct "Ti" as "(Ci& [Ti | Ti])".
        + iExists γ1, (<[i0:=tvo (tvo_sus_data x π ψ δ0 α0 :: l) δ α]>γ2). iSplitR.
          { iPureIntro. split_and !.
            - rewrite H3 insert_union_r; auto.
            - apply map_disjoint_insert_r. split; auto. }
          iFrame "H1". iApply big_sepM_insert; first auto. iFrame "H2". iSplitR; first auto.
          simpl. iFrame "Ci". iLeft. iFrame.
        + iDestruct "Ti" as "(P2i& Ti)".
          iPoseProof (IHl _ _ m H2 γ1 γ2 with "[$Bei $Ti $H1 $H2]") as "(%&%&%& H1& H2)"; eauto.
          destruct H7. clear dependent γ1 γ2. assert (LUg : (γ0 ∪ γ3) !! i0 = Some (tvo l δ α)).
          { rewrite -H7 lookup_insert_eq. auto. }
          assert (EQm : m = delete i0 (γ0 ∪ γ3)).
          { rewrite -H7 delete_insert_id; auto. }
          apply lookup_union_Some_raw in LUg. destruct LUg as [LUgi1 | [LUgi1 LUgi2]].
          * assert (LUgi2 : γ3 !! i0 = None).
            { eapply map_disjoint_Some_l; eauto. }
            iPoseProof (big_sepM_delete _ _ _ _ LUgi1 with "H1") as "[Hi H1]".
            iFrame "H2". iExists (<[i0:=tvo (tvo_sus_data x π ψ δ0 α0 :: l) δ α]>(delete i0 γ0)).
            iSplitR.
            { iPureIntro. subst m. split.
              - rewrite delete_union (delete_id γ3); auto. rewrite insert_union_l; auto.
              - apply map_disjoint_insert_l_2; auto. apply map_disjoint_delete_l; auto. }
            iApply big_sepM_insert.
            { apply lookup_delete_eq. }
            iFrame "Bei H1". simpl. iDestruct "Hi" as "[_ Hi]". iFrame.
          * iPoseProof (big_sepM_delete _ _ _ _ LUgi2 with "H2") as "[Hi H2]".
            iFrame "H1". iExists (<[i0:=tvo (tvo_sus_data x π ψ δ0 α0 :: l) δ α]>(delete i0 γ3)).
            iSplitR.
            { iPureIntro. subst m. split.
              - rewrite delete_union (delete_id γ0); auto. rewrite insert_union_r; auto.
              - apply map_disjoint_insert_r_2; auto. apply map_disjoint_delete_r; auto. }
            iApply big_sepM_insert.
            { apply lookup_delete_eq. }
            iFrame "Bei H2". simpl. iDestruct "Hi" as "[_ Hi]". iFrame. iRight. iFrame.
    }
    iDestruct "TH" as "(%&%&%& To1& To2)". destruct H2 as (Eqγ& Disjγ).
    iAssert (∀ k, ⌜ k ∈ dom γ1 ⌝ →  ∃ d, ⌜ Ω !! k = Some (obl_live d) ⌝)%I with "[-]" as "%LUOρs".
    { iIntros (k Ink). subst Ψ. apply elem_of_dom in Ink. destruct Ink.
      iPoseProof (big_sepM_delete _ _ _ _ H2 with "To1") as "[To To1]".
      destruct x. iDestruct "To" as "(#Bek& To)".
      iPoseProof (tvo_interp_temp_true_acc _ _ (λ (k0 : obl_id) (_ _ : A), (∃ a : A, ⌜/0 /< a⌝ ∗ oblG_progress k0 a)%I) with "To") as "[Tok ACC]". iDestruct "Tok" as "(Tok1& Tok& Tok2)".
      iPoseProof (othread_live_open with "[$T $Tei $Tok]") as "(_& [Blk _]& _)".
      iPoseProof (osat_obl_is_live with "[$S $Bek $Blk]") as "A". done.
    }
    set (C:=λ (k : obl_id) (o : obl_state), ∃ ρ, is_Some (γ1 !! ρ) ∧ ∃ ρt, Φ !! ρ = Some ρt ∧ node ρt k).
    iAssert (∀ k o, ⌜ Ω !! k = Some o ⌝ → ⌜ obl_cond_owner i k o ⌝ → ⌜ C k o ⌝)%I with "[-]" as "%OCEq1".
    { subst C. simpl. iIntros (k o LUOk OC). destruct o; last done. rewrite /obl_cond_owner in OC.
      rewrite /oforest_aux. iDestruct "F" as "(% & Fetk & FM)". destruct H2 as [Dom WFΦ].
      assert (LUΦk : is_Some ((forest_fold Φ) !! k)).
      { apply elem_of_dom. rewrite Dom. apply elem_of_dom. auto. }
      destruct LUΦk as [Ck LUΦk]. pose proof WFΦ. destruct H2 as [DisjΦ TwfsΦ].
      pose proof (forest_fold_lookup_Some_exists_root _ _ _ DisjΦ LUΦk). destruct H2 as (ρ&ρt&LUΦρ&LUρtk).
      iPoseProof (big_sepM_delete _ _ _ _ LUΦρ with "FM") as "[M _]".
      iDestruct "M" as "[(%&Boρ&Toρ&M) | (_& Beρ& Bdρ& %)]"; cycle 1.
      { iExFalso. iPoseProof (osat_obl_is_done_weak with "[$S $Beρ $Bdρ]") as "(%&%)".
        subst ρt. destruct (decide (ρ = k)); cycle 1.
        { rewrite /tree_singleton lookup_singleton_ne in LUρtk; auto. }
        subst k. rewrite LUOk in H3. inv H3. }
      iPoseProof (big_sepM_delete _ _ _ _ LUρtk with "M") as "[H _]". iDestruct "H" as "(_& Bek& Blk& Tek& _& [% | H])".
      - subst k. iPoseProof (osat_lookup_owner with "[$S $Bek $Boρ]") as "[% %]".
        destruct H2. rewrite LUOk in H2. inv H2.
        iPoseProof (othread_obls_owns_elem with "[$T $Tbi $Toρ]") as "%".
        apply elem_of_dom in H2. destruct H2.
        apply lookup_union_Some in H2; last auto. destruct H2.
        + iPureIntro. exists ρ. split_and !; auto. exists ρt. split; auto. unfold node; eauto.
        + iPoseProof (big_sepM_delete _ _ _ _ H2 with "To2") as "[H To2]". iDestruct "H" as "[#Beρ H]".
          destruct x. iPoseProof (tvo_interp_temp_false_acc with "H") as "[H ACC]".
          iPoseProof (othreadG_owns_agree with "[$Toρ $H]") as "%F". inv F.
      - iDestruct "H" as "(%&%&Bok& %&Teθ& Tok& %&%& Tsk& Twk)".
        iPoseProof (osat_lookup_owner with "[$S $Bek $Bok]") as "[% %]".
        destruct H3. rewrite LUOk in H3. inv H3.
        iPoseProof (othread_obls_owns_elem with "[$T $Tbi $Toρ]") as "%".
        apply elem_of_dom in H3. destruct H3.
        apply lookup_union_Some in H3; last auto. destruct H3.
        + iPureIntro. exists ρ. split_and !; auto. exists ρt. split; auto. unfold node; eauto.
        + iPoseProof (big_sepM_delete _ _ _ _ H3 with "To2") as "[H To2]". iDestruct "H" as "[#Beρ H]".
          destruct x0. iPoseProof (tvo_interp_temp_false_acc with "H") as "[H ACC]".
          iPoseProof (othreadG_owns_agree with "[$Toρ $H]") as "%F". inv F.
    }
    iAssert (∀ k o, ⌜ Ω !! k = Some o ⌝ → ⌜ C k o ⌝ → ⌜ obl_cond_owner i k o ⌝)%I with "[-]" as "%OCEq2".
    { subst C. simpl. iIntros (k o LUOk OC). destruct OC as (ρ&?&ρt&LUΦρ&Nodek). destruct H2 as [q LUγρ].
      rewrite /oforest_aux. iDestruct "F" as "(% & Fetk & FM)". destruct H2 as [Dom WFΦ].
      iPoseProof (big_sepM_delete _ _ _ _ LUΦρ with "FM") as "[M _]".
      assert (InΨρ : ρ ∈ Ψ).
      { subst. apply elem_of_dom_2 in LUγρ. set_solver + LUγρ. }
      iClear "To2". iPoseProof (big_sepM_delete _ _ _ _ LUγρ with "To1") as "[To _]". iDestruct "To" as "(#Beρ& Toρ)".
      iDestruct "M" as "[(%&Boρ2&Toρ2&M) | (_& Beρ2& Bdρ& %)]"; cycle 1.
      { iPoseProof (othread_obls_open _ _ _ _ InΨρ with "[$T $Tei $Tbi]") as "(Tbi& Blρ& T)".
        iPoseProof (oblG_live_done_false with "[$Bdρ $Blρ]") as "%". done. }
      destruct Nodek as [Ck LUρtk]. iPoseProof (big_sepM_delete _ _ _ _ LUρtk with "M") as "[H _]".
      destruct q. iPoseProof (tvo_interp_temp_true_acc _ _ (λ (k0 : obl_id) (_ _ : A), (∃ a : A, ⌜/0 /< a⌝ ∗ oblG_progress k0 a)%I) with "Toρ") as "[Toρ ACC]".
      iDestruct "Toρ" as "(ToρR1& Toρ& ToρR2)".
      iDestruct "H" as "(_& Bek& Blk& Tek& _& [% | H])".
      - subst k.
        iPoseProof (othread_live_open with "[$T $Tei $Toρ]") as "(Toρ& (Blk2& Bok2)& T)".
        iPoseProof (oblG_owner_agree with "[$Boρ2 $Bok2]") as "%". destruct H2. subst i.
        iPoseProof (osat_lookup_owner with "[$S $Beρ $Boρ2]") as "%".
        iPureIntro. destruct H2 as (?&?&?). rewrite LUOk in H2. inv H2. done.
      - iDestruct "H" as "(%&%&Bok& %&Teθ& Tok& %&%& Tsk& Twk)".
        iPoseProof (othread_live_open with "[$T $Tei $Toρ]") as "(Toρ& (Blρ2& Boρ)& T)".
        iPoseProof (oblG_owner_agree with "[$Boρ2 $Boρ]") as "%". destruct H3. subst i.
        iPoseProof (osat_lookup_owner with "[$S $Bek $Bok]") as "%".
        iPureIntro. destruct H3 as (?&?&?). rewrite LUOk in H3. inv H3. done.
    }
    iAssert (
        |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | C ⌝) ∗
                osat Ω' ∗ othread TP ∗ oforest_aux (dom Ω') Φ ∗
                ([∗ map] ρ ↦ v ∈ γ1,
                   oblG_elem ρ ∗
                   match v with
                   | tvo l δ α =>
                       tvo_interp_temp_true B (λ (_ : obl_id) (_ _ : A), True) Q P1 P2 i ρ l δ α
                   end)
      )%I with "[- Tbi To2]" as ">H"; cycle 1.
    { iDestruct "H" as "(%&%Prog& S& T& F& To1)". iModIntro. iExists Ω'. iSplitR.
      { iPureIntro. eapply obl_states_cond_rel_iff_lookup. 1: eapply Prog. intros. split; eauto. }
      iFrame. rewrite Eqγ. iApply big_sepM_union; first auto.
      iSplitL "To1".
      - iApply (big_sepM_impl with "To1"). iIntros "!>" (???) "(#Bek& H)". destruct x.
        iPoseProof (tvo_interp_temp_true_impl with "H") as "H". iFrame. auto.
      - iApply (big_sepM_impl with "To2"). iIntros "!>" (???) "(#Bek& H)". destruct x.
        iPoseProof (tvo_interp_temp_false_impl with "H") as "H". iFrame. auto.
    }
    subst C. clear OCEq1 OCEq2. clear dependent Ψ γ γ2.
    iStopProof. revert Ω TP Φ i LUOρs. induction γ1 using map_ind.
    { iIntros (Ω TP Φ i LUOs) "(#Tei& S& T& F& Bps)".
      iModIntro. iExists Ω. iFrame. iSplitR; last done.
      iPureIntro. intro j. destruct (Ω !! j) eqn:LUOj; econstructor. split; intros; auto.
      destruct H2 as (?&?&?&?&?). destruct H2. done.
    }
    rename i into ρ. iIntros (Ω TP Φ i LUOs) "(#Tei& S& T& F& Bps)".
    iPoseProof (big_sepM_insert with "Bps") as "[Bp Bps]"; first auto.
    destruct x. iDestruct "Bp" as "(#Beρ& Toρ)".
    iPoseProof (tvo_interp_temp_true_acc _ _ (λ _ _ _, (True)%I) with "Toρ") as "[Toρ ACC]".
    iDestruct "Toρ" as "(ToρR1& Toρ& (%& %LTa& Bpρ))".
    iPoseProof (osat_elem with "[$S $Beρ]") as "%LUOρ".
    iPoseProof (oforest_aux_othreadG_owns_true_root _ _ _ _ ρ with "[$]") as "%LUΦρ".
    destruct LUΦρ as [ρt LUΦρ]. assert (∃ d, Ω !! ρ = Some (obl_live d)).
    { apply LUOs. rewrite dom_insert_L. set_solver. }
    iMod (oforest_progress_one_tree _ _ _ _ _ LTa H3 LUΦρ with "[$S $F $Bpρ]") as "(%Ω1& %Prog1& S& F)".
    assert (LUO1s : ∀ x0, x0 ∈ dom m → ∃ x, Ω1 !! x0 = Some (obl_live x)).
    { intros. assert (x0 ∈ dom (<[ρ:=tvo l δ α]> m)).
      { rewrite dom_insert_L. set_solver + H4. }
      apply LUOs in H5. destruct H5. specialize (Prog1 x0). inv Prog1.
      - destruct H8. rewrite H5 in H6. inv H6. destruct (decide (obl_cond_in_tree ρt x0 (obl_live x))).
        + apply H8 in o. destruct y; eauto. done.
        + apply H9 in n. subst y. eauto.
      - by rewrite H5 in H7. }
    iMod (IHγ1 _ _ _ _ LUO1s with "[$S $T $F $Tei $Bps]") as "(%Ω2& %Prog2& S& T& F& Tos)".
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. eapply obl_states_cond_rel_split_cond. 7: eapply Prog2. 6: eapply Prog1. all: simpl.
      1,2,3: apply _.
      - intros. rewrite /obl_cond_in_tree. split; intros.
        + destruct H4 as (?&?&?&?&?).  apply lookup_insert_is_Some in H4. destruct H4.
          * subst. left. rewrite LUΦρ in H5. inv H5. auto.
          * destruct H4. right. eauto.
        + destruct H4 as [? | (?&?&?&?&?)].
          * exists ρ. split; eauto. by rewrite lookup_insert_eq.
          * exists x. split; eauto. apply elem_of_dom. apply elem_of_dom in H4. rewrite dom_insert_L. set_solver + H4.
      - repeat intros ?. eauto. }
    rewrite (big_sepM_insert); last auto. iFrame. iSplitR; first auto.
    iApply "ACC". iFrame.
  Qed.

  Lemma oforest_progress_one_thread_tvos Ω TP i Ψ (γ : gmap obl_id thread_view_obl)
    (B : obl_id → A → A → iProp Σ) (Q P1 P2 : obl_id → A → A → positive → obl_id → A → A → A → iProp Σ) :
    Ψ = dom γ →
    osat Ω ∗ othread TP ∗ oforest (dom Ω) ∗
    (* from user *)
    othreadG_elem i ∗ othreadG_obls i Ψ 1 ∗
    ([∗ map] k ↦ v ∈ γ,
       oblG_elem k ∗
       match v with
       | tvo l δ α => tvo_interp_temp B (λ k _ _, (∃ a, ⌜ /0 /< a ⌝ ∗ oblG_progress k a)%I) Q P1 P2 i k l δ α
       end)
    ⊢ |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | (obl_cond_owner i) ⌝) ∗
              osat Ω' ∗ othread TP ∗ oforest (dom Ω') ∗
              othreadG_obls i Ψ 1 ∗
              ([∗ map] k ↦ v ∈ γ,
                 oblG_elem k ∗
                 match v with
                 | tvo l δ α => tvo_interp_temp B (λ k _ _, (True)%I) Q P1 P2 i k l δ α
                 end).
  Proof.
    iIntros (?) "(H1&H2&H3&H4&H5&H6)".
    iEval (rewrite /oforest -lock) in "H3". iDestruct "H3" as "(%&F)".
    iMod (oforest_aux_progress_one_thread_tvos with "[$]") as "H"; first auto.
    iDestruct "H" as "(%&%&S&T&F&H)". iModIntro. iFrame. rewrite /oforest -lock. by iFrame.
  Qed.

  Lemma tvos_elems Ω D i (Δ : gmap obl_id thread_view_obl) :
    osat Ω ∗ osuspend D ∗
    tvos_interp i Δ
    ⊢ [∗ map] k ↦ v ∈ Δ, (⌜ k ∈ dom Ω ∧ k ∈ D ⌝).
  Proof.
    induction Δ using map_ind; iIntros "(S& U& M)"; first done.
    rewrite /tvos_interp. rewrite !big_sepM_insert; auto.
    iDestruct "M" as "((#Bei& #Fei& Cx)& M)".
    iPoseProof (IHΔ with "[$]") as "#MIH". iFrame "MIH".
    iClear "MIH M".
    iPoseProof (osat_elem with "[$S $Bei]") as "%". iPoseProof (osuspend_elem_elem with "[$U $Fei]") as "%".
    iPureIntro. done.
  Qed.

  Local Existing Instances
    otreeGS.otree_inG otreeGS.otreeGpreS_edge otreeGS.otreeGpreS_suspend otreeGS.otreeGpreS_wait otreeGS.otreeGpreS_elem.

  Lemma tvo_interp_temp_impl i k l δ α :
    tvo_interp_temp
      (λ (k0 : obl_id) (δ1 α2 : A), oblG_suspend k0 δ1 ∗ oblG_progress k0 α2)
      (λ (_ : obl_id) (_ _ : A), True)
      (λ (k0 : obl_id) (δ1 α2 : A) (x0 : positive) (π0 : obl_id) (ψ0 η β : A), oblG_elem π0 ∗ otreeG_elem π0 ∗ otreeG_suspend k0 x0 i π0 ψ0 ∗ ⌜δ1 /≤ η ∧ α2 /≤ β⌝)
      (λ (k0 : obl_id) (_ _ : A) (x0 : positive) (π0 : obl_id) (_ η β : A), otreeG_wait k0 x0 (1 / 2) ∗ oblG_suspend k0 η ∗ oblG_progress k0 β ∗ otreeG_edge π0 k0 1)
      (λ (k0 : obl_id) (_ _ : A) (x0 : positive) (π0 : obl_id) (ψ0 _ _ : A), oblG_done π0 ∗ oblG_progress k0 ψ0 ∗ otreeG_wait_null k0 x0 ∗ otreeG_wait_null_auth k0 x0)
      i k l δ α
    ⊢ tvo_interp i k l δ α.
  Proof.
    induction l; simpl; iIntros "H".
    { iDestruct "H" as "(($& $)& $& _)". }
    destruct a. iDestruct "H" as "((#Bep& #Fep& #Fuk& %LE)& [M | M])".
    - iFrame "Bep Fep Fuk". iSplitR; first auto. iLeft. iDestruct "M" as "(($& $& $& _)& _)".
    - iFrame "Bep Fep Fuk". iSplitR; first auto. iRight. iDestruct "M" as "(($& $& $& _)& M)".
      iPoseProof (IHl with "M") as "M". iFrame.
  Qed.

  Lemma tvo_interp_acc (* Ω *) i k l δ α α0 (KSus : gmap positive (prodO (prodO positiveO obl_idO) (leibnizO A))) :
    (* oblG_elem k ∗ otreeG_elem k ∗ *)
    (* osat Ω ∗ oforest (dom Ω) ∗ *)
    tvo_interp i k l δ α
    ∗ (own otreeGS.suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> (KSus : gmap positive (positive * obl_id * leibnizO A))))) ∗
       own otreeGS.wait_name (reservation_map_data k (reservation_map_token (⊤ ∖ gset_to_coPset (dom KSus)))) ∗
       ([∗ map] x↦'(θ, π, ψ) ∈ KSus,
          ((othreadG_owns θ k false (1 / 2) ∗ otreeG_edge π k 1) ∨
             (othreadG_owns θ k true (1 / 2) ∗ otreeG_wait k x (1 / 2) ∗ oblG_done π ∗ oblG_progress k ψ)) ∨
            otreeG_wait_null_auth k x))
    ⊢ |==>
          (* osat Ω ∗ oforest (dom Ω) ∗ *)
          (
            (* oblG_elem k ∗ otreeG_elem k ∗ *)
           tvo_interp_temp
             (λ (k0 : obl_id) (δ0 α1 : A), oblG_suspend k0 δ0 ∗ oblG_progress k0 α1)
             (λ (_ : obl_id) (_ _ : A), True)
             (λ (k0 : obl_id) (δ0 α1 : A) (x : positive) (π : obl_id) (ψ η β : A), oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k0 x i π ψ ∗ ⌜δ0 /≤ η ∧ α1 /≤ β⌝)
             (λ (k0 : obl_id) (_ _ : A) (x : positive) (π : obl_id) (_ η β : A), otreeG_wait k0 x (1 / 2) ∗ oblG_suspend k0 η ∗ oblG_progress k0 β ∗ otreeG_edge π k0 1)
             (λ (k0 : obl_id) (_ _ : A) (x : positive) (π : obl_id) (ψ _ _ : A), oblG_done π ∗ oblG_progress k0 ψ ∗ otreeG_wait_null k0 x ∗ otreeG_wait_null_auth k0 x)
             i k l δ α) ∗
          ((
              (* oblG_elem k ∗ otreeG_elem k ∗ *)
            tvo_interp_temp
              (λ (k0 : obl_id) (δ0 α1 : A), oblG_suspend k0 δ0 ∗ oblG_progress k0 α1)
              (λ (_ : obl_id) (_ _ : A), True)
              (λ (k0 : obl_id) (δ0 α1 : A) (x : positive) (π : obl_id) (ψ η β : A), oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k0 x i π ψ ∗ ⌜δ0 /≤ η ∧ α1 /≤ β⌝)
              (λ (k0 : obl_id) (_ _ : A) (x : positive) (π : obl_id) (_ η β : A), otreeG_wait k0 x (1 / 2) ∗ oblG_suspend k0 η ∗ oblG_progress k0 β ∗ otreeG_edge π k0 1)
              (λ (k0 : obl_id) (_ _ : A) (x : positive) (π : obl_id) (ψ _ _ : A), oblG_done π ∗ oblG_progress k0 ψ ∗ otreeG_wait_null k0 x ∗ otreeG_wait_null_auth k0 x)
              i k l δ α0) -∗
           ((own otreeGS.suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> (KSus : gmap positive (positive * obl_id * leibnizO A))))) ∗
             own otreeGS.wait_name (reservation_map_data k (reservation_map_token (⊤ ∖ gset_to_coPset (dom KSus)))) ∗
             ([∗ map] x↦'(θ, π, ψ) ∈ KSus,
                ((othreadG_owns θ k false (1 / 2) ∗ otreeG_edge π k 1) ∨
                   (othreadG_owns θ k true (1 / 2) ∗ otreeG_wait k x (1 / 2) ∗ oblG_done π ∗ oblG_progress k ψ)) ∨
                  otreeG_wait_null_auth k x)) ∗
            (
              (* oblG_elem k ∗ otreeG_elem k ∗ *)
              tvo_interp i k l δ α0))).
  Proof.
    revert δ α α0 KSus.
    induction l; intros; iIntros "(V& (Uk1& Uk2& UkM))".
    (* induction l; intros; iIntros "(#Bek& #Fek& S& F& V& (Uk1& Uk2& UkM))". *)
    { simpl. iModIntro. iFrame. iSplitL "V".
      - iDestruct "V" as "($& $& $)".
      - iIntros "($& $& ($&$)& $& _)". }
    simpl. destruct a. iDestruct "V" as "(#Bep& #Fep& #Fuk& %LE& [V | V])".
    - destruct LE as [LEdg LEag]. iDestruct "V" as "(Fwk& Bsk& Bpk)".
      iPoseProof (otreeG_suspend_lookup with "[$Uk1 $Fuk]") as "%ElemKk".
      iPoseProof (big_sepM_delete _ _ _ _ ElemKk with "UkM") as "[[[Ukx | Ukx] | Ukx] UkM]".
      + iDestruct "Ukx" as "[Ukx1 Ukx2]".
        iModIntro. iSplitL "Fwk Bsk Bpk Ukx1 Ukx2".
        { iFrame "Bep Fep Fuk". iSplit; first done. iLeft. iFrame. }
        iIntros "((_&_&_& %LEag2)& [Mk | Mk])".
        * destruct LEag2 as [LEdg2 LEag2].
          iDestruct "Mk" as "((Fwk& Bsk& Bpk& Fgk)& Tok)". iSplitR "Fwk Bsk Bpk".
          -- iFrame. iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame. iLeft. iLeft. iFrame.
          -- iFrame "Bep Fep Fuk". iSplit; first done. iLeft. iFrame.
        * iDestruct "Mk" as "((#Bdp& Bpk& #Fwnk& Fwnak)& Tok)".
          iSplitR "Tok Bpk".
          -- iFrame. iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame "UkM". iRight. iFrame.
          -- iFrame "Bep Fep Fuk". iSplit; first done. iRight. iFrame "Bdp Bpk Fwnk".
             iApply (tvo_interp_temp_impl with "Tok").
      + iDestruct "Ukx" as "(Tok& Fwk2& #Bdp& Bpk2)".
        iMod (otreeG_wait_to_null_2 with "[$Fwk $Fwk2]") as "Fwnak".
        { apply Qp.div_2. }
        iPoseProof (otreeG_wait_null_auth_wait_null with "Fwnak") as "#Fwnk".
        iMod (oblG_suspend_mon _ _ _ LEdg with "Bsk") as "Bsk".
        iMod (oblG_progress_mon _ _ _ LEag with "Bpk") as "Bpk".
        iModIntro. iSplitL "Tok Bpk2 Bsk Bpk Fwnak".
        { iFrame "Bep Fep Fuk". iSplit; first done. iRight. iFrame. iFrame "Bdp Fwnk".

          auto. }
        iIntros "[Mk M]". iPoseProof ("ACC" with "M") as "[U M]". iFrame "M".
        iDestruct "Mk" as "(_&_&_&_&_& %LEag2& [Mk | Mk])".
        -- destruct LEag2 as [LEdg2 LEag2].
           iDestruct "Mk" as "(Fwk& Bsk& Bpk& Tok& Fgk)". iSplitR "Fwk Bsk Bpk".
           ++ iApply (big_sepM_delete _ _ _ _ ElemSk). iFrame.
              iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame. iLeft. iLeft. iFrame.
           ++ iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iLeft. iFrame.
        -- destruct LEag2 as [LEdg2 LEag2].
           iDestruct "Mk" as "(Tok& #bdp& Bpk& _& Bsk& Bpk2& Fwnka)". iSplitR "Tok Bpk Bsk Bpk2"; cycle 1.
           { iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iRight. iFrame. auto. }
           iApply (big_sepM_delete _ _ _ _ ElemSk). iFrame "Uk1 Uk2 U".
           iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame "UkM". iRight. iFrame.
        * iPoseProof (otreeG_wait_null_auth_false with "[$Fwk $Ukx]") as "%F". done.

    
otreeG_suspend_lookup
     : ∀ (k : positive) (KSus : gmap positive (prodO (prodO positiveO obl_idO) (leibnizO A))) (x θ : positive) 
         (π : obl_id) (ψ : A),
         own otreeGS.suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> KSus))) ∗
         otreeG_suspend k x θ π ψ ⊢ ⌜KSus !! x = Some (θ, π, ψ)⌝

  (* Lemma oforest_tvos_all_acc Ω D i (M1 M2 : gmap obl_id thread_view_obl) : *)
  (*   map_Forall2 (λ _ d1 d2, *)
  (*                  match d1, d2 with *)
  (*                  | tvo_owned q1 δ1 α1, tvo_owned q2 δ2 α2 => *)
  (*                      (q1 = q2) ∧ (δ1 = δ2) *)
  (*                  | tvo_maybe x1 π1 ψ1 δ01 δ11 _ _, tvo_maybe x2 π2 ψ2 δ02 δ12 _ _ => *)
  (*                      (x1 = x2) ∧ (π1 = π2) ∧ (ψ1 = ψ2) ∧ (δ01 = δ02) ∧ (δ11 = δ12) *)
  (*                  | _, _ => False *)
  (*                  end) M1 M2 → *)
  (*   D ⊆ dom Ω → *)
  (*   osat Ω ∗ osuspend D ∗ oforest (dom Ω) ∗ *)
  (*   (* from user *) *)
  (*   tvos_all i M1 *)
  (*   ⊢ |==> osat Ω ∗ oforest (dom Ω) ∗ *)
  (*       ([∗ map] k ↦ v ∈ M1, *)
  (*          oblG_elem k ∗ otreeG_elem k ∗ *)
  (*          match v with *)
  (*          | tvo_owned q δ α => *)
  (*              othreadG_owns i k true q ∗ oblG_suspend k δ ∗ oblG_progress k α *)
  (*          | tvo_maybe x π ψ δ0 δ1 α0 α1 => *)
  (*              oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ (⌜ δ1 /≤ δ0 ∧ α1 /≤ α0 ⌝) ∗ *)
  (*              ((otreeG_wait k x (1/2) ∗ oblG_suspend k δ0 ∗ oblG_progress k α0 ∗ *)
  (*                othreadG_owns i k false (1/2) ∗ otreeG_edge π k 1) *)
  (*               ∨ *)
  (*                 (othreadG_owns i k true (1/2) ∗ oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ *)
  (*                  oblG_suspend k δ1 ∗ oblG_progress k α1 ∗ *)
  (*                  otreeG_wait_null_auth k x)) *)
  (*          end) ∗ *)
  (*       (* Return leftover from extracting progress credits from above: M -> M' *) *)
  (*       (([∗ map] k ↦ v ∈ M2, *)
  (*           oblG_elem k ∗ otreeG_elem k ∗ *)
  (*           match v with *)
  (*           | tvo_owned q δ α => *)
  (*               othreadG_owns i k true q ∗ oblG_suspend k δ ∗ oblG_progress k α *)
  (*           | tvo_maybe x π ψ δ0 δ1 α0 α1 => *)
  (*               oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ (⌜ δ1 /≤ δ0 ∧ α1 /≤ α0 ⌝) ∗ *)
  (*               ((otreeG_wait k x (1/2) ∗ oblG_suspend k δ0 ∗ oblG_progress k α0 ∗ *)
  (*                 othreadG_owns i k false (1/2) ∗ otreeG_edge π k 1) *)
  (*                ∨ *)
  (*                  (othreadG_owns i k true (1/2) ∗ oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ *)
  (*                   oblG_suspend k δ1 ∗ oblG_progress k α1 ∗ *)
  (*                   otreeG_wait_null_auth k x)) *)
  (*           end) -∗ (osuspend D ∗ tvos_all i M2)). *)

  Lemma tvos_interp_acc Ω D i (M1 M2 : gmap obl_id thread_view_obl) :
    map_Forall2 (λ _ d1 d2,
                   match d1, d2 with
                   | tvo l1 δ1 α1, tvo l2 δ2 α2 =>
                       (l1 = l2) ∧ (δ1 = δ2)
                   end) M1 M2 →
    D ⊆ dom Ω →
    osat Ω ∗ osuspend D ∗ oforest (dom Ω) ∗
    (* from user *)
    tvos_interp i M1
    ⊢ |==> osat Ω ∗ oforest (dom Ω) ∗
        ([∗ map] k ↦ v ∈ M1,
           oblG_elem k ∗ otreeG_elem k ∗
           match v with
           | tvo l δ α =>
               tvo_interp_temp
                 (λ k δ α, (oblG_suspend k δ ∗ oblG_progress k α)%I)
                 (λ k _ _, (True)%I)
                 (λ k δ α x π ψ η β, (oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ (⌜ WFOCM.leR δ η ∧ WFOCM.leR α β ⌝))%I)
                 (λ k δ α x π ψ η β, (otreeG_wait k x (1/2) ∗ oblG_suspend k η ∗ oblG_progress k β ∗ otreeG_edge π k 1)%I)
                 (λ k δ α x π ψ η β, (oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ otreeG_wait_null_auth k x)%I)
                 i k l δ α
           end) ∗
        (* Return leftover from extracting progress credits from above: M -> M' *)
        (([∗ map] k ↦ v ∈ M2,
            oblG_elem k ∗ otreeG_elem k ∗
            match v with
            | tvo l δ α =>
                tvo_interp_temp
                  (λ k δ α, (oblG_suspend k δ ∗ oblG_progress k α)%I)
                  (λ k _ _, (True)%I)
                  (λ k δ α x π ψ η β, (oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ (⌜ WFOCM.leR δ η ∧ WFOCM.leR α β ⌝))%I)
                  (λ k δ α x π ψ η β, (otreeG_wait k x (1/2) ∗ oblG_suspend k η ∗ oblG_progress k β ∗ otreeG_edge π k 1)%I)
                  (λ k δ α x π ψ η β, (oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ otreeG_wait_null_auth k x)%I)
                  i k l δ α
            end) -∗ (osuspend D ∗ tvos_interp i M2)).
  Proof.
    iIntros (MF SubDF) "(S & U & F & M)".
    iPoseProof (tvos_elems with "[$S $U $M]") as "%ElemsM".
    rewrite /osuspend -lock. iDestruct "U" as "(% & %Hdom & RS & RW & RE & RM )".
    iFrame "RS RW RE".
    iAssert (
        |==> osat Ω ∗ oforest (dom Ω) ∗
          ([∗ map] k↦v ∈ M1,
             oblG_elem k ∗ otreeG_elem k ∗
             match v with
             | tvo l δ α =>
                 tvo_interp_temp
                   (λ (k0 : obl_id) (δ0 α0 : A), oblG_suspend k0 δ0 ∗ oblG_progress k0 α0)
                   (λ (_ : obl_id) (_ _ : A), True)
                   (λ (k0 : obl_id) (δ0 α0 : A) (x : positive) (π : obl_id) (ψ η β : A), oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k0 x i π ψ ∗ ⌜δ0 /≤ η ∧ α0 /≤ β⌝)
                   (λ (k0 : obl_id) (_ _ : A) (x : positive) (π : obl_id) (_ η β : A), otreeG_wait k0 x (1 / 2) ∗ oblG_suspend k0 η ∗ oblG_progress k0 β ∗ otreeG_edge π k0 1)
                   (λ (k0 : obl_id) (_ _ : A) (x : positive) (π : obl_id) (ψ _ _ : A), oblG_done π ∗ oblG_progress k0 ψ ∗ otreeG_wait_null k0 x ∗ otreeG_wait_null_auth k0 x)
                   i k l δ α
             end) ∗
          (([∗ map] k↦v ∈ M2,
              oblG_elem k ∗ otreeG_elem k ∗
              match v with
              | tvo l δ α =>
                  tvo_interp_temp
                    (λ (k0 : obl_id) (δ0 α0 : A), oblG_suspend k0 δ0 ∗ oblG_progress k0 α0)
                    (λ (_ : obl_id) (_ _ : A), True)
                    (λ (k0 : obl_id) (δ0 α0 : A) (x : positive) (π : obl_id) (ψ η β : A), oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k0 x i π ψ ∗ ⌜δ0 /≤ η ∧ α0 /≤ β⌝)
                    (λ (k0 : obl_id) (_ _ : A) (x : positive) (π : obl_id) (_ η β : A), otreeG_wait k0 x (1 / 2) ∗ oblG_suspend k0 η ∗ oblG_progress k0 β ∗ otreeG_edge π k0 1)
                    (λ (k0 : obl_id) (_ _ : A) (x : positive) (π : obl_id) (ψ _ _ : A), oblG_done π ∗ oblG_progress k0 ψ ∗ otreeG_wait_null k0 x ∗ otreeG_wait_null_auth k0 x)
                    i k l δ α
              end) -∗
           (([∗ map] k↦KSus ∈ OSus,
               own otreeGS.suspend_name (reservation_map_data k (gmap_view_auth (DfracOwn 1) (to_agree <$> (KSus : gmap positive (positive * obl_id * leibnizO A))))) ∗
               own otreeGS.wait_name (reservation_map_data k (reservation_map_token (⊤ ∖ gset_to_coPset (dom KSus)))) ∗
               ([∗ map] x↦'(θ, π, ψ) ∈ KSus,
                  ((othreadG_owns θ k false (1 / 2) ∗ otreeG_edge π k 1) ∨
                     (othreadG_owns θ k true (1 / 2) ∗ otreeG_wait k x (1 / 2) ∗ oblG_done π ∗ oblG_progress k ψ)) ∨
                    otreeG_wait_null_auth k x))) ∗
           tvos_interp i M2)
      )%I with "[-]" as "H"; cycle 1.
    { iMod "H" as "(S& F& MA& Acc)". iFrame "S F MA". iIntros "!> MA".
      iPoseProof ("Acc" with "MA") as "(H& $)".
      iExists OSus. iSplitR; first done. iApply "H". }
    iStopProof. subst D. revert M2 MF OSus ElemsM SubDF.
    induction M1 using map_ind; iIntros (M2 MF OSus ElemsM SubDF) "(S& U& F& M)".
    { apply map_Forall2_empty_inv_l in MF. subst. rewrite !big_sepM_empty. by iFrame. }
    rename i0 into k. apply map_Forall_insert in ElemsM; last auto. destruct ElemsM as [[DomOk DomSk] ElemsM].
    apply map_Forall2_insert_inv_l in MF; last auto. destruct MF as [x2 [m2 [-> [LUm2k [MFx MF]]]]].
    rewrite /tvos_interp. rewrite !big_sepM_insert; auto. iDestruct "M" as "((#Bek& #Fek& Mk)& M)".
    destruct x, x2. destruct MFx as [<- <-].
    assert (LUSk : is_Some (OSus !! k)) by (by eapply elem_of_dom). destruct LUSk as [KSusk LUSk].
    iPoseProof (big_sepM_delete _ _ _ _ LUSk with "U") as "[Uk U]".

    TODO

    destruct x, x2. 2,3: done.
    - iMod (IHM1 m2 with "[$S $U $F $M]") as "(S& F& H& ACC)". 1,2,3: auto.
      clear IHM1. iModIntro. iFrame "S F Mk H". iSplitR; first auto.
      iIntros "(Mk& M)". iPoseProof ("ACC" with "M") as "[U M]". iFrame.
    - destruct MFx as [<- [<- [<- [<- <-]]]].
      iDestruct "Mk" as "(#Bep& #Fep& #Fuk& %LEag& [Mk | Mk])".
      + destruct LEag as [LEdg LEag].
        apply elem_of_dom in DomSk. destruct DomSk as [KSusk ElemSk].
        iPoseProof (big_sepM_delete _ _ _ _ ElemSk with "U") as "[Uk U]".
        iDestruct "Uk" as "(Uk1& Uk2& UkM)". iDestruct "Mk" as "(Fwk& Bsk& Bpk)".
        iPoseProof (otreeG_suspend_lookup with "[$Uk1 $Fuk]") as "%ElemKk".
        iPoseProof (big_sepM_delete _ _ _ _ ElemKk with "UkM") as "[[[Ukx | Ukx] | Ukx] UkM]".
        * iDestruct "Ukx" as "[Ukx1 Ukx2]".
          iMod (IHM1 with "[$S $U $F $M]") as "(S& F& M& ACC)".
          { eauto. }
          { intros a b LUa. specialize (ElemsM _ _ LUa). destruct ElemsM as [A1 A2].
            assert (NEQ : a ≠ k).
            { intros <-. rewrite H1 in LUa. done. }
            split_and !; auto.
            rewrite dom_delete_L. set_solver + A2 NEQ. }
          { rewrite dom_delete_L. set_solver + SubDF. }
          clear IHM1.
          iModIntro. iFrame "S F M". iSplitL "Fwk Bsk Bpk Ukx1 Ukx2".
          { iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iLeft. iFrame. }
          iIntros "[Mk M]". iPoseProof ("ACC" with "M") as "[U M]". iFrame "M".
          iDestruct "Mk" as "(_&_&_&_&_& %LEag2& [Mk | Mk])".
          -- destruct LEag2 as [LEdg2 LEag2].
             iDestruct "Mk" as "(Fwk& Bsk& Bpk& Tok& Fgk)". iSplitR "Fwk Bsk Bpk".
             ++ iApply (big_sepM_delete _ _ _ _ ElemSk). iFrame.
                iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame. iLeft. iLeft. iFrame.
             ++ iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iLeft. iFrame.
          -- iDestruct "Mk" as "(Tok& #Bdp& Bpk& #Fwnk& Bsk& Bpk2& Fwnak)".
             iSplitR "Tok Bpk Bsk Bpk2"; cycle 1.
             { iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iRight. iFrame. auto. }
             iApply (big_sepM_delete _ _ _ _ ElemSk). iFrame "Uk1 Uk2 U".
             iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame "UkM". iRight. iFrame.
        * iDestruct "Ukx" as "(Tok& Fwk2& #Bdp& Bpk2)".
          iMod (otreeG_wait_to_null_2 with "[$Fwk $Fwk2]") as "Fwnak".
          { apply Qp.div_2. }
          iPoseProof (otreeG_wait_null_auth_wait_null with "Fwnak") as "#Fwnk".
          iMod (IHM1 with "[$S $U $F $M]") as "(S& F& M& ACC)".
          { eauto. }
          { intros a b LUa. specialize (ElemsM _ _ LUa). destruct ElemsM as [A1 A2].
            assert (NEQ : a ≠ k).
            { intros <-. rewrite H1 in LUa. done. }
            split_and !; auto.
            rewrite dom_delete_L. set_solver + A2 NEQ. }
          { rewrite dom_delete_L. set_solver + SubDF. }
          clear IHM1.
          iMod (oblG_suspend_mon _ _ _ LEdg with "Bsk") as "Bsk".
          iMod (oblG_progress_mon _ _ _ LEag with "Bpk") as "Bpk".
          iModIntro. iFrame "S F M". iSplitL "Tok Bpk2 Bsk Bpk Fwnak".
          { iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iRight. iFrame. auto. }
          iIntros "[Mk M]". iPoseProof ("ACC" with "M") as "[U M]". iFrame "M".
          iDestruct "Mk" as "(_&_&_&_&_& %LEag2& [Mk | Mk])".
          -- destruct LEag2 as [LEdg2 LEag2].
             iDestruct "Mk" as "(Fwk& Bsk& Bpk& Tok& Fgk)". iSplitR "Fwk Bsk Bpk".
             ++ iApply (big_sepM_delete _ _ _ _ ElemSk). iFrame.
                iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame. iLeft. iLeft. iFrame.
             ++ iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iLeft. iFrame.
          -- destruct LEag2 as [LEdg2 LEag2].
             iDestruct "Mk" as "(Tok& #bdp& Bpk& _& Bsk& Bpk2& Fwnka)". iSplitR "Tok Bpk Bsk Bpk2"; cycle 1.
             { iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iRight. iFrame. auto. }
             iApply (big_sepM_delete _ _ _ _ ElemSk). iFrame "Uk1 Uk2 U".
             iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame "UkM". iRight. iFrame.
        * iPoseProof (otreeG_wait_null_auth_false with "[$Fwk $Ukx]") as "%F". done.
      + iDestruct "Mk" as "(Tok& #Bdp& Bpk& #Fwnk& Bsk& Bpk2)".
        apply elem_of_dom in DomSk. destruct DomSk as [KSusk ElemSk].
        iPoseProof (big_sepM_delete _ _ _ _ ElemSk with "U") as "[Uk U]".
        iDestruct "Uk" as "(Uk1& Uk2& UkM)".
        iPoseProof (otreeG_suspend_lookup with "[$Uk1 $Fuk]") as "%ElemKk".
        iPoseProof (big_sepM_delete _ _ _ _ ElemKk with "UkM") as "[[[Ukx | Ukx] | Ukx] UkM]".
        * iExFalso. iDestruct "Ukx" as "[Tok2 _]".
          iPoseProof (othreadG_owns_agree with "[$Tok $Tok2]") as "%F". inv F.
        * iExFalso. iDestruct "Ukx" as "(_& Fwk& _)".
          iPoseProof (otreeG_wait_null_false with "[$Fwk $Fwnk]") as "%F". inv F.
        * iMod (IHM1 with "[$S $U $F $M]") as "(S& F& M& ACC)".
          { eauto. }
          { intros a b LUa. specialize (ElemsM _ _ LUa). destruct ElemsM as [A1 A2].
            assert (NEQ : a ≠ k).
            { intros <-. rewrite H1 in LUa. done. }
            split_and !; auto.
            rewrite dom_delete_L. set_solver + A2 NEQ. }
          { rewrite dom_delete_L. set_solver + SubDF. }
          clear IHM1.
          iModIntro. iFrame "S F M". iSplitL "Tok Bpk2 Bsk Bpk Ukx".
          { iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iRight. iFrame. auto. }
          iIntros "[Mk M]". iPoseProof ("ACC" with "M") as "[U M]". iFrame "M".
          iDestruct "Mk" as "(_&_&_&_&_& %LEag2& [Mk | Mk])".
          -- destruct LEag2 as [LEdg2 LEag2].
            iDestruct "Mk" as "(Fwk& Bsk& Bpk& Tok& Fgk)". iSplitR "Fwk Bsk Bpk".
             ++ iApply (big_sepM_delete _ _ _ _ ElemSk). iFrame.
                iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame. iLeft. iLeft. iFrame.
             ++ iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iLeft. iFrame.
          -- iDestruct "Mk" as "(Tok& #bdp& Bpk& _& Bsk& Bpk2& Fwnka)". iSplitR "Tok Bpk Bsk Bpk2"; cycle 1.
             { iFrame "Bek Fek Bep Fep Fuk". iSplit; first done. iRight. iFrame. auto. }
             iApply (big_sepM_delete _ _ _ _ ElemSk). iFrame "Uk1 Uk2 U".
             iApply (big_sepM_delete _ _ _ _ ElemKk). iFrame "UkM". iRight. iFrame.
  Qed.

  (* Rules for updating thread view:
     progress (spend pcred),
     suspend (owned -> maybe, spend scred),
     check (maybe -> owned with done and ψ pcred \/ maybe with α pcred reset),
     refresh pcred (spend scred) *)
  Lemma threadG_tvos_progress_one_thread Ω TP i (Δ1 Δ2 : gmap obl_id thread_view_obl) :
    osat Ω ∗ othread TP ∗ oforest (dom Ω) ∗ osuspend (dom Ω) ∗
    (* from user *)
    othreadG_elem i ∗ othreadG_obls i (dom Δ1) 1 ∗ tvos_all i Δ1 ∗
    ⌜ map_Forall2 (λ k d1 d2,
                     match d1, d2 with
                     | tvo_owned q1 δ1 α1, tvo_owned q2 δ2 α2 =>
                         (q1 = q2) ∧ (δ1 = δ2) ∧ (α2 /< α1)
                     | tvo_maybe x1 π1 ψ1 δ01 δ11 α01 α11, tvo_maybe x2 π2 ψ2 δ02 δ12 α02 α12 =>
                         (x1 = x2) ∧ (π1 = π2) ∧ (ψ1 = ψ2) ∧ (δ01 = δ02) ∧ (δ11 = δ12) ∧ (α01 = α02) ∧ (α12 /< α11)
                     | _, _ => False
                     end) Δ1 Δ2 ⌝
    ⊢ |==> ∃ Ω', (⌜ Ω ↪ₚ Ω' | (obl_cond_owner i) ⌝) ∗
              osat Ω' ∗ othread TP ∗ oforest (dom Ω') ∗ osuspend (dom Ω') ∗
              othreadG_obls i (dom Δ2) 1 ∗
              tvos_all i Δ2.
  Proof.
    iIntros "(S& T& F& U& #Tei& Tbi& Vall& %MF)".
    iMod (oforest_tvos_all_acc _ _ _ Δ1 Δ2 with "[$S $U $F $Vall]") as "(S& F& VM& AccU)".
    { eapply map_Forall2_impl; eauto. simpl; intros. destruct x1, x2; auto.
      - destruct H1 as [? [? ?]]. auto.
      - destruct H1 as [? [? [? [? [? [? ?]]]]]]. auto.
    }
    { auto. }
    iAssert (
        |==> [∗ map] k↦v ∈ Δ2,
          oblG_elem k ∗ otreeG_elem k ∗
          match v with
          | tvo_owned q δ β =>
              othreadG_owns i k true q ∗ oblG_suspend k δ ∗ oblG_progress k β ∗
              ∃ a : A, ⌜/0 /< a⌝ ∗ oblG_progress k a
          | tvo_maybe x π ψ δ0 δ1 β0 β1 =>
              oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ ⌜ δ1 /≤ δ0 ∧ β1 /≤ β0 ⌝ ∗
              ((otreeG_wait k x (1 / 2) ∗ oblG_suspend k δ0 ∗ oblG_progress k β0 ∗ othreadG_owns i k false (1 / 2) ∗ otreeG_edge π k 1)
               ∨ (othreadG_owns i k true (1 / 2) ∗ oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ 
                  oblG_suspend k δ1 ∗ oblG_progress k β1 ∗ otreeG_wait_null_auth k x ∗
                  ∃ a : A, ⌜/0 /< a⌝ ∗ oblG_progress k a
              ))
          end
      )%I with "[VM]" as ">VM".
    { iClear "Tei". iStopProof. revert Δ2 MF. induction Δ1 using map_ind; iIntros (? MF) "VM".
      { apply map_Forall2_empty_inv_l in MF. subst. iModIntro. done. }
      apply map_Forall2_insert_inv_l in MF; last auto. destruct MF as (x2& m2& EQDm2& LUm2& MFx& MF).
      subst. rewrite !big_sepM_insert; auto. iDestruct "VM" as "((#Bei& #Fei& V)& VM)".
      iMod (IHΔ1 _ MF with "VM") as "VM2". iFrame "Bei Fei VM2". clear IHΔ1 MF.
      destruct x, x2; try done.
      - destruct MFx as [? [? ?]]. subst. iDestruct "V" as "[V [S P]]".
        iMod (oblG_progress_lt _ _ _ H4 with "P") as "[P Pc]". by iFrame.
      - destruct MFx as [? [? [? [? [? [? ?]]]]]]. subst. iDestruct "V" as "($&$&$& %& [V | V])".
        + iModIntro. iSplitR.
          { iPureIntro. destruct H2. split; auto. etransitivity; last eauto. eapply WFOCM.lt_le; eauto. }
          iLeft. iFrame.
        + iDestruct "V" as "(V0& V1& V2& V3& V4& P& V5)".
          destruct H2. iMod (oblG_progress_lt _ _ _ H8 with "P") as "[P Pc]".
          iModIntro. iSplitR.
          { iPureIntro. split; auto. etransitivity; last eauto. eapply WFOCM.lt_le; eauto. }
          iRight. iFrame.
    }
    set (P:= (λ k q δ β, (oblG_suspend k δ ∗ oblG_progress k β)%I) : obl_id → Qp → A → A → iProp Σ).
    set (Q1:= (λ k x π ψ δ0 δ1 β0 β1, (otreeG_wait k x (1 / 2) ∗ oblG_suspend k δ0 ∗ oblG_progress k β0 ∗ otreeG_edge π k 1)%I) : obl_id → positive → obl_id → A → A → A → A → A → iProp Σ).
    set (Q2:= (λ k x π ψ δ0 δ1 β0 β1, (oblG_done π ∗ oblG_progress k ψ ∗ otreeG_wait_null k x ∗ oblG_suspend k δ1 ∗ oblG_progress k β1 ∗ otreeG_wait_null_auth k x)%I) : obl_id → positive → obl_id → A → A → A → A → A → iProp Σ).
    iAssert (
        ([∗ map] ρ↦v ∈ Δ2,
           oblG_elem ρ ∗
           match v with
           | tvo_owned q δ α =>
               (P ρ q δ α) ∗ othreadG_owns i ρ true q ∗ ∃ a : A, ⌜/0 /< a⌝ ∗ oblG_progress ρ a
           | tvo_maybe x π ψ δ0 δ1 α0 α1 =>
               ((Q1 ρ x π ψ δ0 δ1 α0 α1) ∗ othreadG_owns i ρ false (1 / 2))
               ∨ ((Q2 ρ x π ψ δ1 δ1 α0 α1) ∗ othreadG_owns i ρ true (1 / 2) ∗ ∃ a : A, ⌜/0 /< a⌝ ∗ oblG_progress ρ a)
           end) ∗
        ([∗ map] k↦v ∈ Δ2,
           oblG_elem k ∗ otreeG_elem k ∗
           match v with
           | tvo_owned q δ β =>
               True
           | tvo_maybe x π ψ δ0 δ1 β0 β1 =>
               oblG_elem π ∗ otreeG_elem π ∗ otreeG_suspend k x i π ψ ∗ ⌜ δ1 /≤ δ0 ∧ β1 /≤ β0 ⌝
           end)
      )%I with "[VM]" as "[VMH VMR]".
    { subst P Q1 Q2. rewrite -big_sepM_sep. iApply (big_sepM_impl with "VM"). iIntros "!>" (???) "(#Bek& #Fek& M)".
      iFrame "Bek Fek". destruct x.
      - iDestruct "M" as "($& $& P1& P2)". iSplitL "P1"; (iFrame; auto).
      - iDestruct "M" as "($& $& $& $& [M | M])".
        + iDestruct "M" as "(M1& M2& M3& M4& M5)". iLeft. iFrame.
        + iDestruct "M" as "(M1& M2& M3& M4& M5& M6& M7& M8)". iRight. iFrame.
    }
    assert (MDom : dom Δ1 = dom Δ2) by (eapply map_Forall2_dom_L; eauto).
    iMod (oforest_progress_one_thread_tvos with "[$S $T $F $Tei $Tbi $VMH]") as "(%& %Prog& S& T& F& Tbi& VMH)".
    1: auto.
    iPoseProof ("AccU" with "[VMR VMH]") as "[U VM]".
    { subst P Q1 Q2. iPoseProof (big_sepM_sep with "[$VMR $VMH]") as "M". iApply (big_sepM_impl with "M").
      iIntros "!>" (???) "[(#Bek& #Fek& M1) M2]". iFrame "Bek Fek". destruct x.
      - iDestruct "M2" as "(($& $)& $)".
      - iDestruct "M1" as "($&$&$&$)". iDestruct "M2" as "[M | M]".
        + iLeft. iDestruct "M" as "(($&$&$&$)& $)".
        + iRight. iDestruct "M" as "(($&$&$&$&$&$)& $)".
    }
    iModIntro. iExists Ω'. iSplit; first auto. rewrite MDom. assert (dom Ω = dom Ω').
    { eapply obl_states_cond_rel_dom; eauto. }
    rewrite H1. iFrame.
  Qed.

End tvos.
