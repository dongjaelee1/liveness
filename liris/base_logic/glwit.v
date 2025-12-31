From iris.algebra Require Import gmap_view reservation_map dfrac_agree mono_nat.
From iris.bi.lib Require Import cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Export wfocm.
From liris.algebra Require Import bcred.
From liris.base_logic Require Export witness glsat.

(** The ghost state for liveness obligations *)
Module glwitGS.

  Class glwitGpreS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set :=
    GlwitGpreS {
        glwitGpreS_witness : inG Σ (reservation_mapUR (reservation_mapUR bcredUR));
      }.

  Class glwitGS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set :=
    GlwitG {
        glwit_inG : glwitGpreS Σ;
        witness_name : gname;
      }.

  Definition glwitΣ `{SI : indexT} `{GL : ghost_lock_class} : gFunctors :=
    #[GFunctor (reservation_mapUR (reservation_mapUR bcredUR))
      ].

  Global Instance subG_glwitΣ `{SI : indexT} `{GL : ghost_lock_class} {Σ} : subG (glwitΣ) Σ → (glwitGpreS Σ).
  Proof. solve_inG. Qed.

End glwitGS.
Import glwitGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances glwit_inG glwitGpreS_witness.

(* Witness: manage credits for ghost lock's witness progresses *)
Definition witG_witness `{SI : indexT} `{GL : ghost_lock_class} `{!glwitGS Σ}
  (k : gl_id) (v : gl_version) (ℵ : gl_fuel) : iProp Σ :=
  own witness_name (reservation_map_data k (reservation_map_data (A:=bcredUR) (encode v) (credit_bound ℵ))).
Global Typeclasses Opaque witG_witness.
Global Instance: Params (@witG_witness) 5 := {}.

Definition witG_credit `{SI : indexT} `{GL : ghost_lock_class} `{!glwitGS Σ}
  (k : gl_id) (v : gl_version) (a : gl_fuel) : iProp Σ :=
  own witness_name (reservation_map_data k (reservation_map_data (A:=bcredUR) (encode v) (credit a))).
Global Typeclasses Opaque witG_credit.
Global Instance: Params (@witG_credit) 5 := {}.

Local Definition witG_witness_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glwitGS Σ}
  (E : coPset) : iProp Σ :=
  own witness_name (reservation_map_token (A:=reservation_mapUR bcredUR) E).
Local Definition witG_witness_token_version `{SI : indexT} `{GL : ghost_lock_class} `{!glwitGS Σ}
  (k : gl_id) (E : coPset) : iProp Σ :=
  own witness_name (reservation_map_data k (reservation_map_token (A:=bcredUR) E)).

(* Global invariant for the witness ghost state *)
Definition glwit `{SI : indexT} `{GL : ghost_lock_class} {Σ}
  `{!@glsatGS.glsatGS _ GL Σ} `{!glwitGS Σ}
  (W : witnesses) : iProp Σ :=
  locked
    (witG_witness_token_id (⊤ ∖ gset_to_coPset (dom W)) ∗
     ([∗ map] k ↦ '(v, w) ∈ W,
        witG_witness_token_version k (⊤ ∖ gset_to_coPset (set_map encode (set_seq 0 (S v) : gset gl_version))) ∗
        ([∗ set] u ∈ (set_seq 0 v : gset gl_version), glG_version_lb k u ∗ glG_unlocked k u) ∗
        glG_version_lb k v ∗
        match w with
        | wit_locked b =>
            (∃ α, (⌜ WFOCM.leR b α ⌝) ∗ witG_credit k v α)
        | wit_unlocked =>
            (glG_unlocked k v)
        end)
    )%I.

(* Global invariant that relates witnesses to obligations *)
Definition glwit_inv `{GL : ghost_lock_class}
  (η : gl_fuel → gl_fuel) (Ω : ghost_locks) (W : witnesses) : Prop :=
  map_Forall2 (λ k '(v1, g) '(v2, w),
                 (v1 = v2) ∧
                 match g, w with
                 | (gl_locked a _), (wit_locked b) => (b w≤ η a)
                 | (gl_unlocked), (wit_unlocked) => True
                 | _, _ => False
                 end
    ) Ω W.

(** Properties *)
Section glwit.
  Context `{SI : indexT} `{GL : ghost_lock_class} `{GLSAT : !glsatGS.glsatGS Σ} `{!glwitGS Σ}.

  (* witness *)
  Global Instance witG_witness_persistent k v ℵ : Persistent (witG_witness k v ℵ).
  Proof. rewrite /witG_witness. apply _. Qed.
  Global Instance witG_witness_timeless k v ℵ : Timeless (witG_witness k v ℵ).
  Proof. rewrite /witG_witness. apply _. Qed.

  Global Instance witG_credit_timeless k v a : Timeless (witG_credit k v a).
  Proof. rewrite /witG_credit. apply _. Qed.

  Local Instance witG_witness_token_id_timeless E : Timeless (witG_witness_token_id E).
  Proof. rewrite /witG_witness_token_id. apply _. Qed.
  Local Instance witG_witness_token_version_timeless k E : Timeless (witG_witness_token_version k E).
  Proof. rewrite /witG_witness_token_version. apply _. Qed.

  (* wlsat *)
  Global Instance glwit_timeless W : Timeless (glwit W).
  Proof. rewrite /glwit -lock. apply _. Qed.

  (** Witness credit rules *)
  Lemma witG_credit_eq k v a0 a1 :
    a0 w= a1 →
    witG_credit k v a0 = witG_credit k v a1.
  Proof. intros EQ. rewrite /witG_credit. by erewrite credit_eq. Qed.

  Lemma witG_credit_mon k v a0 a1 :
    a0 w≤ a1 →
    witG_credit k v a1 ⊢ |==> witG_credit k v a0.
  Proof.
    intros LE. rewrite /witG_credit. apply own_update.
    by apply reservation_map_update, reservation_map_update, credit_update.
  Qed.

  Lemma witG_credit_split k v a0 a1 :
    witG_credit k v (a0 w+ a1) ⊣⊢ witG_credit k v a0 ∗ witG_credit k v a1.
  Proof.
    rewrite /witG_credit. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite credit_split). iSplitL "H1"; iFrame.
  Qed.

  Lemma witG_credit_mon_split k v a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    witG_credit k v a2 ⊢ |==> witG_credit k v a0 ∗ witG_credit k v a1.
  Proof.
    intros LE. iIntros "H". iApply witG_credit_split. iApply witG_credit_mon; done.
  Qed.

  Lemma witG_credit_lt k v a0 a1 :
    a0 w< a1 →
    witG_credit k v a1 ⊢ |==> witG_credit k v a0 ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ witG_credit k v c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (witG_credit_mon_split _ _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.

  Lemma witG_witness_mon k v a0 a1 :
    a0 w≤ a1 →
    witG_witness k v a0 ⊢ |==> witG_witness k v a1.
  Proof.
    intros LE. rewrite /witG_witness. apply own_update.
    by apply reservation_map_update, reservation_map_update,
      cmra_update_included, credit_bound_included.
  Qed.

  Lemma witG_credit_spend_gen k v a0 a1 :
    witG_witness k v a0 ∗ witG_credit k v a1
    ⊢ |==> ∃ a2, ⌜(a1 w+ a2) w≤ a0⌝ ∗ witG_witness k v a2.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -!reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ x, ∃ a2, (x = (reservation_map_data (encode v) (credit_bound a2))) ∧ (a1 w+ a2 w≤ a0))
                (λ r, ∃ a2, (r = {[k := (reservation_map_data (encode v) (credit_bound a2))]}) ∧ (a1 w+ a2 w≤ a0))
             ).
      { eapply (reservation_map_updateP
                  (λ x, ∃ a2, (x = (credit_bound a2)) ∧ (a1 w+ a2 w≤ a0))
                  (λ r, ∃ a2, (r = (reservation_map_data (encode v) (credit_bound a2))) ∧ (a1 w+ a2 w≤ a0))
               ).
        { eapply credit_spend. }
        { intros. destruct H as (a2&A0&A1). eexists. by subst. }
      }
      { intros. destruct H as (a2&A0&A1). eexists. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplitR; done.
  Qed.
  Lemma witG_credit_spend k v a0 a1 :
    wzero w< a1 →
    witG_witness k v a0 ∗ witG_credit k v a1 ⊢ |==> ∃ a2, ⌜a2 w< a0⌝ ∗ witG_witness k v a2.
  Proof.
    iIntros (LT) "[Ow Oc]". iMod (witG_credit_spend_gen with "[$]") as "(%&%&$)".
    iPureIntro. eapply WFOCM.lt_exists_right; eauto.
  Qed.

  Lemma witG_compare k v a0 a1 :
    witG_witness k v a0 ∗ witG_credit k v a1 ⊢ ⌜ a1 w≤ a0 ⌝.
  Proof.
    rewrite -own_op -!reservation_map_data_op. iIntros "H".
    iPoseProof (own_valid with "H") as "%". do 2 apply reservation_map_data_valid in H.
    apply credit_bound_credit_valid_compare in H. done.
  Qed.

  Lemma witG_witness_id_alloc D k E :
    k ∉ D →
    witG_witness_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> witG_witness_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        witG_witness_token_version k E.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (reservation_map_token (A:=bcredUR) E) with "Htk") as "[Htk >H]"; auto.
    { apply reservation_map_token_valid. }
    rewrite /witG_witness_token_version. by iFrame.
  Qed.

  Lemma witG_witness_alloc k (D : gset gl_version) v a :
    v ∉ D →
    witG_witness_token_version k (⊤ ∖ gset_to_coPset (set_map encode D))
    ⊢ |==> witG_witness_token_version k (⊤ ∖ gset_to_coPset (set_map encode ({[v]} ∪ D))) ∗
        witG_witness k v a ∗ witG_credit k v a.
  Proof.
    iIntros (Hk) "Htk". rewrite /witG_witness_token_version.
    rewrite (reservation_map_token_difference
               (gset_to_coPset (set_map encode ({[v]} : gset nat)))
               (⊤ ∖ gset_to_coPset (set_map encode D))); cycle 1.
    { apply elem_of_subseteq. intros. rewrite elem_of_difference. split; first set_solver.
      intro F. rewrite !elem_of_gset_to_coPset in H F. apply elem_of_map_1 in H, F.
      destruct H as (?& ?& ?), F as (?& ?& ?). subst. apply encode_inj in H1. subst.
      set_solver.
    }
    iDestruct "Htk" as "[Htk H]".
    assert (⊤ ∖ gset_to_coPset (set_map encode D) ∖ gset_to_coPset (set_map encode ({[v]} : gset nat)) = ⊤ ∖ gset_to_coPset (set_map encode ({[v]} ∪ D))).
    { apply leibniz_equiv. intros x. rewrite !elem_of_difference. split; intros.
      - destruct H as ((_&?)&?). split; first set_solver.
        intros F. rewrite set_map_union_L in F. apply elem_of_gset_to_coPset, elem_of_union in F.
        destruct F; [apply H0 | apply H]; apply elem_of_gset_to_coPset; set_solver.
      - destruct H as (_&?). split; first (split; first set_solver);
          intros F; apply elem_of_gset_to_coPset in F; apply H, elem_of_gset_to_coPset; set_solver.
    }
    rewrite H. iFrame "H".
    iMod (own_update with "Htk") as "H".
    { eapply reservation_map_update. eapply (reservation_map_alloc _ (encode v) (credit_bound a ⋅ credit a)); auto.
      - apply elem_of_gset_to_coPset; set_solver.
      - apply credit_bound_credit_valid_eq.
    }
    iDestruct "H" as "[H1 H2]". rewrite /witG_witness /witG_credit. by iFrame.
  Qed.

  Lemma witG_witness_alloc_seq k s l n (ηξ : gl_witness) :
    witG_witness_token_version k (⊤ ∖ gset_to_coPset (set_map encode (set_seq s l : gset gl_version)))
    ⊢ |==> witG_witness_token_version k (⊤ ∖ gset_to_coPset (set_map encode (set_seq s (l + n) : gset gl_version))) ∗
        [∗ set] u ∈ set_seq (s + l) n, witG_witness k u (ηξ u) ∗ witG_credit k u (ηξ u).
  Proof.
    revert s l. induction n; iIntros (??) "H".
    { simpl. rewrite Nat.add_right_id big_sepS_empty. by iFrame. }
    replace (l + S n) with (S (l + n)) by lia. rewrite !set_seq_S_end_union_L.
    rewrite big_sepS_union; cycle 1.
    { apply set_seq_S_end_disjoint. }
    iMod (IHn with "H") as "[H $]". iMod (witG_witness_alloc _ _ (s + l + n) (ηξ (s + l + n)) with "H") as "(H& R)".
    { intros F. apply elem_of_set_seq in F. lia. }
    rewrite (assoc Nat.add) big_sepS_singleton. by iFrame.
  Qed.

  (** glwit rules *)
  Lemma glwit_alloc_wit_locked W k v (ηξ : gl_witness) :
    k ∉ dom W →
    glwit W ∗
    ([∗ set] u ∈ (set_seq 0 v : gset gl_version), glG_version_lb k u ∗ glG_unlocked k u) ∗
    glG_version_lb k v
    ⊢ |==> glwit (<[k:=(v, wit_locked (ηξ v))]>W) ∗
        [∗ set] u ∈ set_seq 0 (S v), witG_witness k u (ηξ u).
  Proof.
    iIntros (Nink) "(W& #Gus& #Gvl)".
    rewrite /glwit -!lock. iDestruct "W" as "(Wti& WM)".
    iMod (witG_witness_id_alloc _ _ (⊤ ∖ gset_to_coPset (set_map encode (∅ : gset gl_version))) Nink with "Wti") as "[Wti Wtvk]".
    iMod (witG_witness_alloc_seq _ 0 0 (S v) ηξ with "Wtvk") as "(Wtvk& Ws)".
    iAssert (([∗ set] u ∈ set_seq 0 (S v), witG_witness k u (ηξ u)) ∗
             ([∗ set] u ∈ set_seq 0 (S v), witG_credit k u (ηξ u)))%I
      with "[Ws]" as "[#Wws Wcs]".
    { iApply big_sepS_sep. iApply (big_sepS_impl with "Ws"). iIntros "!> % % $". }
    iModIntro. iFrame "Wws".
    rewrite dom_insert_L. iFrame "Wti".
    iApply big_sepM_insert.
    { apply not_elem_of_dom. auto. }
    iFrame. iFrame "Gus Gvl".
    rewrite set_seq_S_end_union_L. iPoseProof (big_sepS_union with "Wcs") as "[Wc Wcs]".
    { apply set_seq_S_end_disjoint. }
    rewrite big_sepS_singleton. iFrame. done.
  Qed.

  Lemma glwit_alloc_wit_unlocked W k v (ηξ : gl_witness) :
    k ∉ dom W →
    glwit W ∗
    ([∗ set] u ∈ (set_seq 0 (S v) : gset gl_version), glG_version_lb k u ∗ glG_unlocked k u)
    ⊢ |==> glwit (<[k:=(v, wit_unlocked)]>W) ∗
        [∗ set] u ∈ set_seq 0 (S v), witG_witness k u (ηξ u).
  Proof.
    iIntros (Nink) "(W& #Gus)".
    rewrite /glwit -!lock. iDestruct "W" as "(Wti& WM)".
    iMod (witG_witness_id_alloc _ _ (⊤ ∖ gset_to_coPset (set_map encode (∅ : gset gl_version))) Nink with "Wti") as "[Wti Wtvk]".
    iMod (witG_witness_alloc_seq _ 0 0 (S v) ηξ with "Wtvk") as "(Wtvk& Ws)".
    iAssert (([∗ set] u ∈ set_seq 0 (S v), witG_witness k u (ηξ u)) ∗
             ([∗ set] u ∈ set_seq 0 (S v), witG_credit k u (ηξ u)))%I
      with "[Ws]" as "[#Wws Wcs]".
    { iApply big_sepS_sep. iApply (big_sepS_impl with "Ws"). iIntros "!> % % $". }
    iModIntro. iFrame "Wws".
    rewrite dom_insert_L. iFrame "Wti".
    iApply big_sepM_insert.
    { apply not_elem_of_dom. auto. }
    iFrame. rewrite set_seq_S_end_union_L. iPoseProof (big_sepS_union with "Gus") as "[Gu Gus2]".
    { apply set_seq_S_end_disjoint. }
    rewrite big_sepS_singleton. iDestruct "Gu" as "[Gu1 Gu2]". iFrame "Gu1 Gu2 Gus2".
  Qed.

  Lemma glwit_mon W1 W2 :
    wits_mon W1 W2 →
    glwit W1 ⊢ glwit W2.
  Proof.
    iIntros (Step) "W".
    assert (Dom : dom W1 = dom W2) by (eapply map_Forall2_dom_L; eauto).
    rewrite /glwit -!lock. iDestruct "W" as "(Wti& WM)".
    rewrite -Dom. iFrame "Wti".
    iStopProof. clear Dom.
    revert W2 Step. induction W1 using map_ind; iIntros (W2 Step) "WM".
    { apply map_Forall2_empty_inv_l in Step. subst. by iFrame. }
    apply map_Forall2_insert_inv_l in Step; last auto.
    destruct Step as (w2& m2& EqW2& LUm2& Stepi& Step). subst. rewrite !big_sepM_insert; auto.
    destruct x as (v1&w1). destruct w2 as (v2&w2).
    iDestruct "WM" as "((VSa& #VS& #Gvli& Mi)& M)".
    destruct Stepi as [-> Stepi]. iFrame "VSa VS".
    iPoseProof (IHW1 _ Step with "M") as "M". clear IHW1.
    iFrame "M Gvli". destruct w1, w2; try done.
    iDestruct "Mi" as "(%&%& $)". iPureIntro. etransitivity; eauto.
  Qed.

  (* witness_step rules: progress, unlock, lock, inc/pin *)
  Lemma glwit_progress_one W k v w1 w2 :
    W !! k = Some (v, wit_locked w1) →
    witness_step (v, wit_locked w1) (v, wit_locked w2) →
    glwit W
    ⊢ |==> glwit (<[k:=(v, wit_locked w2)]>W) ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ witG_credit k v c.
  Proof.
    iIntros (Luk Prog) "W".
    rewrite /glwit -!lock. iDestruct "W" as "(Wti& WM)".
    assert (Ink : k ∈ dom W).
    { apply elem_of_dom. eauto. }
    assert (DomEq : {[k]} ∪ dom W = dom W).
    { set_solver + Ink. }
    rewrite !dom_insert_L !DomEq. iFrame "Wti".
    inv Prog. iPoseProof (big_sepM_delete _ _ _ _ Luk with "WM") as "[Mk WM]".
    iDestruct "Mk" as "(VSa& #VS& #Gvlk& %& %& Wck)".
    assert (Lt : w2 w< α).
    { eapply WFOCM.lt_le_lt; eauto. }
    apply WFOCM.lt_exists_left in Lt. destruct Lt as (?& Lt& Le).
    iMod (witG_credit_mon_split _ _ _ _ _ Le with "Wck") as "[Wck Wck0]".
    iModIntro. iFrame "Wck0". iSplitL; last done.
    rewrite -(insert_delete_eq W k). iApply big_sepM_insert.
    { apply lookup_delete_eq. }
    iFrame. auto.
  Qed.

  Lemma glwit_progress W1 W2 :
    (W1 ↓ₚ W2 | wit_cond_locked) →
    glwit W1
    ⊢ |==> glwit W2 ∗
        ([∗ map] k ↦ '(v, w) ∈ W1,
           ([∗ set] u ∈ (set_seq 0 v), glG_version_lb k u ∗ glG_unlocked k u) ∗
           glG_version_lb k v ∗
           match w with
           | wit_locked _ =>
               (∃ c, ⌜ wzero w< c ⌝ ∗ witG_credit k v c)
           | wit_unlocked =>
               (glG_unlocked k v)
           end).
  Proof.
    iIntros ([Step Keep]) "W".
    assert (Dom : dom W1 = dom W2) by (eapply wits_cond_rel_dom; eauto).
    rewrite /glwit -!lock. iDestruct "W" as "(Wti& WM)".
    rewrite -Dom. iFrame "Wti".
    iStopProof. clear Dom.
    revert W2 Step Keep. induction W1 using map_ind; iIntros (W2 Step Keep) "WM".
    { apply map_Forall2_empty_inv_l in Step. subst. iModIntro. iFrame. done. }
    apply map_Forall2_insert_inv_l in Keep; last auto.
    destruct Keep as (w2& m2& EqW2& LUm2& Keepi& Keep). subst. rewrite !big_sepM_insert; auto.
    apply map_Forall2_insert in Step; auto.
    destruct x as (v1&w1). destruct w2 as (v2&w2). iDestruct "WM" as "((VSa& #VS& #Gvli& Mi)& M)".
    destruct Keepi as [Eqvi Keepi]. subst. iFrame "VSa VS".
    destruct Step as [HC Step].
    iMod (IHW1 _ Step Keep with "M") as "[M Rs]". clear IHW1.
    iFrame "M Rs Gvli". destruct HC as [[HC Stepi] | [HC Eqi]].
    - destruct w1; last done. destruct w2; last done. inv Stepi. iDestruct "Mi" as "(%& %& Mci)".
      assert (Lt : wit0 w< α).
      { eapply WFOCM.lt_le_lt; eauto. }
      apply WFOCM.lt_exists_left in Lt. destruct Lt as (?& Lt& Le).
      iMod (witG_credit_mon_split _ _ _ _ _ Le with "Mci") as "[Mci Mci0]".
      iModIntro. iSplitL "Mci"; first by iFrame. iFrame. auto.
    - inv Eqi. destruct w2; first done. iPoseProof "Mi" as "#Mi". auto.
  Qed.

  Lemma glwit_progress_any C W1 W2 :
    (W1 ↓ₚ W2 | C) →
    glwit W1 ⊢ glwit W2.
  Proof.
    iIntros (Prog) "W".
    iApply (glwit_mon with "W").
    eapply wits_cond_progress_mon; eauto.
  Qed.

  Lemma glwit_unlock W k v a :
    W !! k = Some (v, wit_locked a) →
    glwit W ∗ glG_unlocked k v
    ⊢ glwit (<[k:=(v, wit_unlocked)]>W).
  Proof.
    iIntros (Luk) "[W #Guk]".
    rewrite /glwit -!lock. iDestruct "W" as "(Wti& WM)".
    iPoseProof (big_sepM_delete _ _ _ _ Luk with "WM") as "[Wk WM]".
    rewrite !dom_insert_L. replace ({[k]} ∪ dom W) with (dom W); cycle 1.
    { apply elem_of_dom_2 in Luk. set_solver. }
    iFrame. rewrite -(insert_delete_eq W k). iApply big_sepM_insert.
    { apply lookup_delete_eq. }
    iFrame. iDestruct "Wk" as "(VSa& VS& Gvl& _)". iFrame. auto.
  Qed.

  Lemma glwit_lock W k v1 v2 (ηξ : gl_witness) :
    v1 < v2 →
    W !! k = Some (v1, wit_unlocked) →
    glwit W ∗
    ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u) ∗
    glG_version_lb k v2
    ⊢ |==> glwit (<[k:=(v2, wit_locked (ηξ v2))]>W) ∗
        witG_witness k v2 (ηξ v2) ∗
        [∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), witG_witness k u (ηξ u).
  Proof.
    iIntros (LTv Luk) "(W& #Gus& #Gvl)".
    rewrite /glwit -!lock. iDestruct "W" as "(Wti& WM)".
    iPoseProof (big_sepM_delete _ _ _ _ Luk with "WM") as "[Mk WM]".
    iDestruct "Mk" as "(VSa& #VS& #Gvlk& #Guk)".
    iMod (witG_witness_alloc_seq _ _ _ (v2 - v1) ηξ with "VSa") as "[VSa Wks]".
    assert (∃ δ, v2 - v1 = S δ).
    { inv LTv.
      - exists O. lia.
      - exists (m - v1). lia.
    }
    destruct H as (δ& EQd).
    iEval (rewrite EQd set_seq_S_end_union_L) in "Wks".
    iPoseProof (big_sepS_union with "Wks") as "[Wk2 Wks]".
    { apply set_seq_S_end_disjoint. }
    rewrite big_sepS_singleton. iDestruct "Wk2" as "[#Wwk2 Wck2]".
    iModIntro. rewrite !dom_insert_L. replace ({[k]} ∪ dom W) with (dom W); cycle 1.
    { apply elem_of_dom_2 in Luk. set_solver. }
    iFrame "Wti".
    replace (S v1 + (v2 - v1)) with (S v2) by lia.
    replace (0 + S v1 + δ) with v2 by lia.
    iSplitR "Wks".
    - rewrite -(insert_delete_eq W k). iApply big_sepM_insert.
      { apply lookup_delete_eq. }
      iFrame.
      replace (set_seq 0 v2) with (set_seq 0 ((S v1) + (v2 - v1 - 1)) : gset gl_version); cycle 1.
      { replace ((S v1) + (v2 - v1 - 1)) with v2 by lia. done. }
      rewrite (set_seq_add_L _ (S v1)). iSplitL; last auto.
      iApply big_sepS_union.
      { apply set_seq_add_disjoint. }
      iFrame "Gus". rewrite !set_seq_S_end_union_L. rewrite !big_sepS_union.
      2: apply set_seq_S_end_disjoint.
      rewrite !big_sepS_singleton. auto.
    - iFrame "Wwk2". replace δ with (v2 - v1 - 1) by lia.
      iPoseProof (big_sepS_sep with "Wks") as "[$ _]".
  Qed.

  (** glwit_inv rules *)
  Lemma glwit_inv_empty ξ :
    glwit_inv ξ ∅ ∅.
  Proof. apply map_Forall2_empty. Qed.

  Lemma glwit_inv_dom ξ Ω W :
    glwit_inv ξ Ω W → dom Ω = dom W.
  Proof.
    intros. eapply map_Forall2_dom_L; eauto.
  Qed.

  Lemma glwit_inv_cond_step_same_gls η C Ω W1 W2 :
    glwit_inv η Ω W1 →
    (W1 ↓ₛ W2 | C) →
    glwit_inv η Ω W2 →
    wits_mon W1 W2.
  Proof.
    revert Ω W2. induction W1 using map_ind; intros.
    { apply map_Forall2_empty_inv_l in H0. subst. done. }
    rename x into w1, m into W1, W2 into W2', Ω into Ω'.
    apply map_Forall2_insert_inv_r in H0; auto. destruct H0 as (g& Ω& EQO& LUOi& HO1& MFO).
    apply map_Forall2_insert_inv_l in H1; auto. destruct H1 as (w2& W2& EQW2& LUWi2& HC& MFW).
    subst. apply map_Forall2_insert in H2; auto. destruct H2 as (How& MFW2).
    pose proof (IHW1 _ _ MFO MFW MFW2) as IH.
    apply map_Forall2_insert; auto. split; auto.
    clear MFW2 MFW MFO IHW1 IH. destruct g, w1, w2. destruct HO1, How. subst. split; auto.
    destruct HC as [[HC Step] | [HC EQ]].
    - destruct g0, w, w0; inv Step; try done. eapply WFOCM.lt_le; auto.
    - inv EQ. destruct g0, w0; try done.
  Qed.

  Lemma glwit_inv_alloc_same_gls_dom η Ω1 Ω2 W1 W2 :
    dom Ω1 = dom Ω2 →
    glwit_inv η Ω1 W1 →
    (W1 ↓ₐ W2) →
    glwit_inv η Ω2 W2 →
    False.
  Proof.
    intros. destruct H1 as (k& v& LU& [[a EQ] | EQ]); subst.
    - apply glwit_inv_dom in H0, H2. rewrite -H H0 dom_insert_L in H2.
      apply not_elem_of_dom in LU. set_solver.
    - apply glwit_inv_dom in H0, H2. rewrite -H H0 dom_insert_L in H2.
      apply not_elem_of_dom in LU. set_solver.
  Qed.

  Lemma glwit_inv_step_same_gls η Ω W1 W2 :
    glwit_inv η Ω W1 →
    (W1 ↓ W2) →
    glwit_inv η Ω W2 →
    wits_mon W1 W2.
  Proof.
    intros. inv H0.
    - eapply glwit_inv_cond_step_same_gls; eauto.
    - exfalso. eapply (glwit_inv_alloc_same_gls_dom _ Ω Ω W1 W2); eauto.
  Qed.
  Lemma glwit_inv_rc_step_same_gls η Ω W1 W2 :
    glwit_inv η Ω W1 →
    (W1 ↓∘ W2) →
    glwit_inv η Ω W2 →
    wits_mon W1 W2.
  Proof.
    intros. inv H0.
    - done.
    - eapply glwit_inv_step_same_gls; eauto.
  Qed.

  Lemma glwit_inv_alloc_same_wits_dom η Ω1 Ω2 W1 W2 :
    dom W1 = dom W2 →
    glwit_inv η Ω1 W1 →
    (Ω1 ↪ₐ Ω2) →
    glwit_inv η Ω2 W2 →
    False.
  Proof.
    intros. destruct H1 as (k& v& LU& [(a&t&EQ) | EQ]); subst.
    - apply glwit_inv_dom in H0, H2. rewrite -H -H0 dom_insert_L in H2.
      apply not_elem_of_dom in LU. set_solver.
    - apply glwit_inv_dom in H0, H2. rewrite -H -H0 dom_insert_L in H2.
      apply not_elem_of_dom in LU. set_solver.
  Qed.

  Lemma glwit_inv_progress_owner η Ω k v a t1 W1 :
    (∀ α β, α w< β → η α w< η β) →
    Ω !! k = Some (v, gl_locked a t1) →
    glwit_inv η Ω W1 →
    ∀ a' t2,
    ghost_lock_step (v, gl_locked a t1) (v, gl_locked a' t2) →
    ∀ W2,
    W1 ↓∘ W2 →
    glwit_inv η (<[k:=(v, gl_locked a' t2)]> Ω) W2 →
    wits_mon W1 W2.
  (* Below is not necessarily true - Wits can take refelexive step *)
    (* ∃ w1 w2, W1 !! k = Some (v, wit_locked w1) ∧ *)
    (*          witness_step (v, wit_locked w1) (v, wit_locked w2) ∧ *)
    (*          wits_mon (<[k:=(v, wit_locked w2)]> W1) W2. *)
  Proof.
    intros SMON LUO INV1 a' t2 GStep W2 WSStep INV2.
    inv GStep.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    destruct y as (v2& w). destruct H1. subst v2. destruct w; last done. symmetry in H0.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    destruct y as (v2, w). destruct H3. subst v2. destruct w; last done. symmetry in H2.
    eapply (glwit_inv_rc_step_same_gls _ Ω). 1: eapply INV1. 1: eauto.
    intros i. specialize (INV2 i). destruct (decide (k = i)).
    - subst. rewrite lookup_insert_eq H2 in INV2. rewrite LUO H2.
      inv INV2. destruct H5; subst. econstructor. split; eauto.
      apply SMON in LTfuel. etrans; first eauto. eapply WFOCM.lt_le; eauto.
    - rewrite lookup_insert_ne in INV2; auto.
  Qed.

  Lemma glwit_inv_unlock η Ω k v a t W1 :
    Ω !! k = Some (v, gl_locked a t) →
    glwit_inv η Ω W1 →
    ghost_lock_step (v, gl_locked a t) (v, gl_unlocked) →
    ∀ W2,
    W1 ↓∘ W2 →
    glwit_inv η (<[k:=(v, gl_unlocked)]> Ω) W2 →
    (∃ b, W1 !! k = Some (v, wit_locked b) ∧ wits_mon (<[k:=(v, wit_unlocked)]> W1) W2).
  Proof.
    intros LUO INV1 GStep W2 WSStep INV2.
    inv GStep.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    destruct y as (v2& w). destruct H1. subst v2. destruct w; last done. symmetry in H0.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    destruct y as (v2, w). destruct H3. subst v2. destruct w; first done. symmetry in H2.
    eexists. split; first eauto.
    inv WSStep.
    inv H; cycle 1.
    { eapply (glwit_inv_alloc_same_gls_dom _ Ω (<[k:=(v, gl_unlocked)]> Ω)) in H4; eauto; first done.
      rewrite dom_insert_L. apply elem_of_dom_2 in LUO. set_solver + LUO. }
    intros i. specialize (H4 i). destruct (decide (i = k)).
    { subst. rewrite H2 lookup_insert_eq. econstructor. done. }
    rewrite lookup_insert_ne; auto.
    destruct (Ω !! i) eqn:LUO2.
    - destruct g as (v0& g0).
      pose proof INV1 as I3. specialize (I3 i). rewrite LUO2 in I3. inv I3.
      destruct y as (v2& w2). destruct H6. subst v2. symmetry in H5.
      pose proof INV2 as I4. specialize (I4 i). rewrite lookup_insert_ne in I4; auto.
      rewrite LUO2 in I4. inv I4.
      destruct y as (v2, w). destruct H8. subst v2. symmetry in H7.
      rewrite H5 H7 in H4. inv H4. destruct H10 as [[HC WS] | [HC WS]]; cycle 1.
      { inv WS. econstructor. destruct w; done. }
      destruct g0, w, w2; try done; inv WS.
      econstructor. split; auto. eapply WFOCM.lt_le. auto.
    - pose proof INV1 as I3. specialize (I3 i). rewrite LUO2 in I3. inv I3.
      symmetry in H.
      pose proof INV2 as I4. specialize (I4 i). rewrite lookup_insert_ne in I4; auto.
      rewrite LUO2 in I4. inv I4.
      symmetry in H5. econstructor.
  Qed.

  Lemma glwit_inv_lock η Ω k v1 v2 a t W1 :
    Ω !! k = Some (v1, gl_unlocked) →
    glwit_inv η Ω W1 →
    ghost_lock_step (v1, gl_unlocked) (v2, gl_locked a t) →
    ∀ W2,
    W1 ↓∘ W2 →
    glwit_inv η (<[k:=(v2, gl_locked a t)]> Ω) W2 →
    (W1 !! k = Some (v1, wit_unlocked) ∧ wits_mon (<[k:=(v2, wit_locked (η a))]> W1) W2).
  Proof.
    intros LUO INV1 GStep W2 WSStep INV2.
    inv GStep.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    destruct y as (v'& w). destruct H1. subst v'. destruct w; first done. symmetry in H0.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    destruct y as (v', w). destruct H3. subst v'. destruct w; last done. symmetry in H2.
    split; first eauto.
    inv WSStep. clear H1.
    inv H; cycle 1.
    { eapply (glwit_inv_alloc_same_gls_dom _ Ω (<[k:=(v2, gl_locked a t)]> Ω)) in H1; eauto; first done.
      rewrite dom_insert_L. apply elem_of_dom_2 in LUO. set_solver + LUO. }
    intros i. specialize (H1 i). destruct (decide (i = k)).
    { subst. rewrite H2 lookup_insert_eq. econstructor. split; eauto. }
    rewrite lookup_insert_ne; auto.
    destruct (Ω !! i) eqn:LUO2.
    - destruct g as (v0& g0).
      pose proof INV1 as I3. specialize (I3 i). rewrite LUO2 in I3. inv I3.
      destruct y as (v'& w2). destruct H5. subst v'. symmetry in H4.
      pose proof INV2 as I4. specialize (I4 i). rewrite lookup_insert_ne in I4; auto.
      rewrite LUO2 in I4. inv I4.
      destruct y as (v', w). destruct H7. subst v'. symmetry in H6.
      rewrite H4 H6 in H1. inv H1. destruct H9 as [[HC WS] | [HC WS]]; cycle 1.
      { inv WS. econstructor. destruct w; done. }
      destruct g0, w, w2; try done; inv WS.
      econstructor. split; auto. eapply WFOCM.lt_le. auto.
    - pose proof INV1 as I3. specialize (I3 i). rewrite LUO2 in I3. inv I3.
      symmetry in H.
      pose proof INV2 as I4. specialize (I4 i). rewrite lookup_insert_ne in I4; auto.
      rewrite LUO2 in I4. inv I4.
      symmetry in H4. econstructor.
  Qed.

  Lemma glwit_inv_alloc_locked η Ω k W1 :
    k ∉ dom Ω →
    glwit_inv η Ω W1 →
    ∀ v a t W2,
    W1 ↓∘ W2 →
    glwit_inv η (<[k:=(v, gl_locked a t)]> Ω) W2 →
    (k ∉ dom W1 ∧ wits_mon (<[k:=(v, wit_locked (η a))]> W1) W2).
  Proof.
    intros LUO INV1 v a t W2 WSStep INV2.
    apply not_elem_of_dom in LUO.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    symmetry in H.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    destruct y as (v', w). destruct H2. subst v'. destruct w; last done. symmetry in H1.
    split.
    { apply not_elem_of_dom. auto. }
    inv WSStep. inv H0.
    { apply wits_cond_rel_dom in H3. exfalso. apply elem_of_dom_2 in H1. apply not_elem_of_dom in H.
      rewrite H3 in H. set_solver. }
    destruct H3 as (?&?&?& [(?&?) | ?]).
    - subst. destruct (decide (k = x)).
      + subst x. rewrite lookup_insert_eq in H1. inv H1. apply map_Forall2_insert; auto.
        split; auto. reflexivity.
      + rewrite lookup_insert_ne in H1; auto. rewrite H in H1. inv H1.
    - subst. destruct (decide (k = x)).
      + subst x. rewrite lookup_insert_eq in H1. inv H1.
      + rewrite lookup_insert_ne in H1; auto. rewrite H in H1. inv H1.
  Qed.

  Lemma glwit_inv_alloc_unlocked η Ω k W1 :
    k ∉ dom Ω →
    glwit_inv η Ω W1 →
    ∀ v W2,
    W1 ↓∘ W2 →
    glwit_inv η (<[k:=(v, gl_unlocked)]> Ω) W2 →
    (k ∉ dom W1 ∧ wits_mon (<[k:=(v, wit_unlocked)]> W1) W2).
  Proof.
    intros LUO INV1 v W2 WSStep INV2.
    apply not_elem_of_dom in LUO.
    pose proof INV1 as I1. specialize (I1 k). rewrite LUO in I1. inv I1.
    symmetry in H.
    pose proof INV2 as I2. specialize (I2 k). rewrite lookup_insert_eq in I2. inv I2.
    destruct y as (v', w). destruct H2. subst v'. destruct w; first done. symmetry in H1.
    split.
    { apply not_elem_of_dom. auto. }
    inv WSStep. inv H0.
    { apply wits_cond_rel_dom in H3. exfalso. apply elem_of_dom_2 in H1. apply not_elem_of_dom in H.
      rewrite H3 in H. set_solver. }
    destruct H3 as (?&?&?& [(?&?) | ?]).
    - subst. destruct (decide (k = x)).
      + subst x. rewrite lookup_insert_eq in H1. inv H1.
      + rewrite lookup_insert_ne in H1; auto. rewrite H in H1. inv H1.
    - subst. destruct (decide (k = x)).
      + subst x. rewrite lookup_insert_eq in H1. inv H1. done.
      + rewrite lookup_insert_ne in H1; auto. rewrite H in H1. inv H1.
  Qed.

End glwit.

(* Allocation of the initial witness protocol. *)
Lemma glwit_alloc `{SI : indexT} `{GL : ghost_lock_class} {Σ}
  `{!@glsatGS.glsatGS _ GL Σ} `{!glwitGS Σ} :
  ⊢ |==> ∃ _ : glwitGS Σ, glwit ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=reservation_mapUR bcredUR) ⊤)) as (γC) "HC";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (GlwitG SI GL _ _ γC).
  rewrite /glwit -lock.
  replace (⊤ ∖ gset_to_coPset (dom (∅ : witnesses))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
