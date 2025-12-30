From iris.algebra Require Import gmap_view reservation_map dfrac_agree mono_nat.
From iris.bi Require Import lib.cmra.
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
    intros. destruct H1 as (k& v& a& LU& EQ). subst.
    apply glwit_inv_dom in H0, H2. rewrite -H H0 dom_insert_L in H2.
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
    intros. destruct H1 as (k& v& a& t& LU& EQ). subst.
    apply glwit_inv_dom in H0, H2. rewrite -H -H0 dom_insert_L in H2.
    apply not_elem_of_dom in LU. set_solver.
  Qed.

  Lemma glwit_glwit η Ω k v a t1 W1 :
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

  TODO

glsat_unlock:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {glsatGS0 : glsatGS.glsatGS Σ} 
    (Ω : ghost_locks) (k : gl_id) (v : gl_version) (t : gl_owner),
    glsat Ω ∗ glG_elem k ∗ glG_locked k v (1 / 2 + 1 / 2 / 2) ∗ glG_owner k t (1 / 2 + 1 / 2 / 2)
    ⊢ |==> glsat (<[k:=(v, gl_unlocked)]> Ω) ∗ glG_unlocked k v ∗
        ⌜∀ a : gl_fuel, ghost_lock_step (v, gl_locked a t) (v, gl_unlocked)⌝
glwit_unlock:
  ∀ (W : witnesses) (k : gl_id) (v : gl_version) (a : gl_fuel),
    W !! k = Some (v, wit_locked a) → glwit W ∗ glG_unlocked k v ⊢ glwit (<[k:=(v, wit_unlocked)]> W)
glsat_lock:
  ∀ {SI : indexT} {GL : ghost_lock_class} {Σ : gFunctors} {glsatGS0 : glsatGS.glsatGS Σ} 
    (Ω : ghost_locks) (k : gl_id) (ξ : gl_witness) (v1 v2 : nat) (t : gl_owner),
    v1 < v2
    → glsat Ω ∗ glG_witfun k ξ ∗ glG_unlocked k v1 ∗ glG_version k v1 (1 / 2 + 1 / 2 / 2)
      ⊢ |==> glsat (<[k:=(v2, gl_locked (Σ[ξ] v2) t)]> Ω) ∗ glG_locked k v2 (1 / 2 + 1 / 2 / 2) ∗
          glG_version k v2 (1 / 2 + 1 / 2 / 2) ∗ glG_fuel k (Σ[ξ]{S v1, v2}) ∗
          glG_owner k t (1 / 2 + 1 / 2 / 2) ∗
          ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u) ∗
          ⌜ghost_lock_step (v1, gl_unlocked) (v2, gl_locked (Σ[ξ] v2) t)⌝
glwit_lock:
  ∀ (W : witnesses) (k : gl_id) (v1 v2 : nat) (ηξ : gl_witness),
    v1 < v2
    → W !! k = Some (v1, wit_unlocked)
      → glwit W ∗ ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u) ∗
        glG_version_lb k v2
        ⊢ |==> glwit (<[k:=(v2, wit_locked (ηξ v2))]> W) ∗ witG_witness k v2 (ηξ v2) ∗
            ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), witG_witness k u (ηξ u))

    

  Lemma glwit_glwit_inv_step_same_obl ξ Ω W1 W2 :
    glwit_inv ξ Ω W1 →
    W1 ↓ₛ W2 →
    glwit_inv ξ Ω W2 →
    glwit W1 ⊢ glwit W2.
  Proof.
    iIntros (OW1 Prog OW2) "N". inv Prog.
    - iPoseProof (glwit_wit_progress_any with "N") as "N"; eauto.
    - pose proof (glwit_inv_resolve_same _ _ _ _ _ X OW1 H0 OW2). by subst.
    - pose proof (glwit_inv_same_obl_alloc_false _ _ _ _ OW1 H0 OW2). done.
  Qed.

  Lemma glwit_glwit_inv_rc_step_same_obl ξ Ω W1 W2 :
    glwit_inv ξ Ω W1 →
    W1 ↓ₛ∘ W2 →
    glwit_inv ξ Ω W2 →
    glwit W1 ⊢ glwit W2.
  Proof.
    iIntros (OW1 Prog OW2) "N". inv Prog; first done.
    iApply (glwit_glwit_inv_step_same_obl _ Ω W1 W2 with "N"); eauto.
  Qed.

  Lemma glwit_inv_alloc ξ Ω k i a W1 W2 :
    k ∉ dom Ω →
    glwit_inv ξ Ω W1 ->
    W1 ↓ₛ∘ W2 ->
    glwit_inv ξ (<[k:=olive i a]> Ω) W2 ->
    ∃ b, b /≤ (ξ a) ∧ W2 = (<[k:=wlive b]>W1).
  Proof.
    intros Nink OW1 ProgW OW2. inv ProgW.
    { exfalso. eapply glwit_inv_same_wit_alloc_false. 1: eapply OW1. 2: eapply OW2.
      do 2 eexists. split; eauto. by apply not_elem_of_dom. }
    inv H0.
    - exfalso. apply wit_states_cond_rel_dom in H1. apply glwit_inv_dom in OW1, OW2.
      rewrite H1 in OW1. rewrite -OW1 in OW2. rewrite dom_insert_L in OW2. set_solver + Nink OW2.
    - exfalso. apply wit_states_cond_rel_dom in H1. apply glwit_inv_dom in OW1, OW2.
      rewrite H1 in OW1. rewrite -OW1 in OW2. rewrite dom_insert_L in OW2. set_solver + Nink OW2.
    - apply map_Forall2_insert_inv_l in OW2.
      2: by apply not_elem_of_dom.
      destruct OW2 as (w'& W'& EQW2& LUW2& MP& MF). subst.
      simpl in *. destruct w'; last done.
      destruct w as [b]. simpl in *.
      destruct H1 as (?& ?& ?& ?).
      assert (Dom' : dom W' = dom W1).
      { apply glwit_inv_dom in OW1, MF. by rewrite -OW1 -MF. }
      destruct (decide (k = x)).
      2:{ exfalso. apply (f_equal dom) in H1. rewrite !dom_insert_L in H1.
          apply not_elem_of_dom in LUW2, H0. rewrite Dom' in LUW2, H1. set_solver + n LUW2 H0 H1.
      }
      subst. destruct x0 as [c].
      assert (b = c).
      { rewrite map_eq_iff in H1. specialize (H1 x). rewrite !lookup_insert_eq in H1. by inv H1. }
      subst. exists c. split; auto.
  Qed.

  Lemma glwit_glwit_inv_alloc ξ Ω k i a W1 W2 :
    k ∉ dom Ω →
    glwit_inv ξ Ω W1 ->
    W1 ↓ₛ∘ W2 ->
    glwit_inv ξ (<[k:=olive i a]> Ω) W2 ->
    glwit (<[k:=wlive (ξ a)]> W1)
    ⊢ |==> glwit W2.
  Proof.
    iIntros (Nink OW1 ProgW OW2) "N".
    edestruct glwit_inv_alloc as (?& LE& Eq); eauto. subst.
    rewrite /glwit -!lock. iDestruct "N" as "[N1 NM]".
    iSplitL "N1".
    { rewrite !dom_insert_L. done. }
    assert (Dom : dom Ω = dom W1) by (by apply glwit_inv_dom in OW1).
    assert (LUWk : W1 !! k = None).
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    rewrite !(big_sepM_insert _ _ _ _ LUWk). iDestruct "NM" as "[N $]".
    simpl. iDestruct "N" as "(%&%&Nc)". iFrame.
    iPureIntro. etransitivity; eauto.
  Qed.

  Lemma glwit_inv_resolve ξ Ω k d P W1 W2 :
    glwit_inv ξ Ω W1 →
    Ω !! k = Some (obl_live d) →
    W1 ↓ₛ∘ W2 →
    glwit_inv ξ (<[k:=odone P]> Ω) W2 →
    W1 ↓ᵣ W2 | wit_cond_one k.
  Proof.
    intros OW1 LUOk ProgW OW2. pose proof OW1 as OWk1. pose proof OW2 as OWk2.
    specialize (OWk1 k). rewrite LUOk in OWk1.
    specialize (OWk2 k). rewrite lookup_insert_eq in OWk2.
    inv OWk1. inv OWk2. simpl in *. destruct y, y0; try done.
    inv ProgW.
    { exfalso. rewrite -H1 in H3. inv H3. }
    inv H0.
    - exfalso. specialize (H5 k). rewrite -H1 -H3 in H5. inv H5. destruct H7. destruct (decide (C k (inl w))).
      + apply H0 in c. done.
      + apply H5 in n. done.
    - intros ?. specialize (H5 i). destruct (decide (i = k)).
      { subst. rewrite -H1 -H3. econstructor. done. }
      specialize (OW1 i). specialize (OW2 i). rewrite lookup_insert_ne in OW2; auto.
      destruct (W1 !! i) eqn:LUWi1.
      + rewrite LUWi1 in OW1. destruct (Ω !! i) eqn:LUOi.
        * rewrite LUOi in OW1, OW2. inv OW1. inv OW2. rewrite -H6. rewrite -H6 in H5.
          inv H5. destruct H10. econstructor. destruct o, y, w0; try done; simpl in *.
          -- split; intros; first done. destruct (decide (C i (inl w0))).
             ++ by apply H0 in c.
             ++ apply H5 in n0. done.
          -- split; intros; first done. destruct (decide (C i (inr u1))).
             ++ by apply H0 in c.
             ++ apply H5 in n0. done.
        * rewrite LUOi in OW1. inv OW1.
      + rewrite LUWi1 in OW1. destruct (Ω !! i) eqn:LUOi.
        * rewrite LUOi in OW1. inv OW1.
        * rewrite LUOi in OW1, OW2. inv OW2. rewrite -H0. econstructor.
    - exfalso. destruct H5 as (?& ?& ?& ?). subst.
      assert (Dom : dom Ω = dom W1) by (apply glwit_inv_dom in OW1; auto).
      assert (LUOx : Ω !! x = None).
      { apply not_elem_of_dom. apply not_elem_of_dom in H0. rewrite Dom. auto. }
      specialize (OW2 x).
      destruct (decide (x = k)).
      { subst. rewrite H0 in H1. done. }
      rewrite lookup_insert_eq lookup_insert_ne in OW2; auto.
      rewrite LUOx in OW2. inv OW2.
  Qed.

  (* Maybe we don't need this *)
  (* Lemma glwit_glwit_inv_steps_same_obl ξ Ω W1 W2 : *)
  (*   glwit_inv ξ Ω W1 → *)
  (*   W1 ↓ₛ⋆ W2 → *)
  (*   glwit_inv ξ Ω W2 → *)
  (*   glwit W1 ⊢ glwit W2. *)
  (* Proof. *)
  (*   iIntros (OW1 Prog OW2). revert Ω OW1 OW2. *)
  (*   induction Prog; iIntros (Ω OW1 OW2) "N". *)
  (*   1: done. *)
  (*   rename x into W1, y into W2, z into W3. *)
  (*   iPoseProof (glwit_glwit_inv_step_same_obl _ _ W1 W2 with "N") as "N"; eauto. *)

  (*   pattern W2, W1. revert W1 W2 Prog. apply rtc_ind_r_weak; intros. *)
  (*   { done. } *)
  (*   rename x into W1, y into W2, z into W3, H0 into Steps, H1 into Step, H2 into IH. *)


  (* Lemma glwit_inv_credit ξ Ω1 Ω2 W1 (i : T) : *)
  (*   Proper (WFOCM.ltR ==> WFOCM.ltR) ξ → *)
  (*   glwit_inv ξ Ω1 W1 → *)
  (*   (Ω1 ↪ₚ Ω2 | obl_cond_owner i) → *)
  (*   ∃ W2, (W1 ↓ₚ W2 | λ k _, ∃ d, Ω1 !! k = Some (obl_live d) ∧ (obl_owner d = i)) ∧ *)
  (*         glwit_inv ξ Ω2 W2. *)
  (* Proof. *)
  (*   intros Hξ. revert Ω2 W1. induction Ω1 using map_ind; intros Ω2 W1 OW OP. *)
  (*   { apply map_Forall2_empty_inv_l in OP, OW. subst. exists ∅. split; apply map_Forall2_empty. } *)
  (*   rename m into Ω1, W1 into W1', Ω2 into Ω2', i0 into k, x into o. *)
  (*   apply map_Forall2_insert_inv_l in OP; last auto. destruct OP as (o2& Ω2& EqO2& LUO2& (HCO1& HCO2)& OP). *)
  (*   apply map_Forall2_insert_inv_l in OW; last auto. destruct OW as (w2& W2& EqW2& LUW2& HW2& OW). *)
  (*   pose proof (IHΩ1 _ _ OW OP) as IH. clear IHΩ1 OW OP. destruct IH as (Wi& WPi& OWi). subst. *)
  (*   assert (WDom : dom W2 = dom Wi) by (eapply wit_states_cond_rel_dom; eauto). *)
  (*   assert (LUWi : Wi !! k = None). *)
  (*   { apply not_elem_of_dom. rewrite -WDom. apply not_elem_of_dom. auto. } *)
  (*   destruct o, w2; try done. *)
  (*   - destruct o as [θ α], w as [ℵ]. simpl in *. destruct (decide (θ = i)). *)
  (*     + subst. pose proof (HCO1 eq_refl). clear HCO1 HCO2. destruct o2; last done. *)
  (*       destruct o as [θ' α']. simpl in *. destruct H1; subst. *)
  (*       exists (<[k:=wlive (ξ α')]>Wi). split. *)
  (*       * apply map_Forall2_insert; auto. simpl. split_and !; auto. *)
  (*         -- intros. destruct H1 as (?&?&?). subst. rewrite HW2. apply Hξ. auto. *)
  (*         -- intros. exfalso. apply H1; clear H1. eexists. split. *)
  (*             { apply lookup_insert_eq. } *)
  (*            done. *)
  (*         -- intros ?. specialize (WPi i). destruct (W2 !! i) eqn:LUi1. *)
  (*            ++ destruct (decide (i = k)). *)
  (*               { subst. rewrite LUW2 in LUi1; done. } *)
  (*               rewrite LUi1 in WPi. destruct (Wi !! i) eqn:LUi2. *)
  (*               ** rewrite LUi1. inv WPi. destruct H4. econstructor. split; intro. *)
  (*                  { destruct H4 as (?&?&?). rewrite lookup_insert_ne in H4; eauto. } *)
  (*                  { apply H3. intros ?. apply H4. destruct H5 as (?&?&?). rewrite lookup_insert_ne; eauto. } *)
  (*               ** inv WPi. *)
  (*            ++ rewrite LUi1 in WPi. destruct (Wi !! i) eqn:LUi2. *)
  (*               ** inv WPi. *)
  (*               ** rewrite LUi1. econstructor. *)
  (*       * apply map_Forall2_insert; auto. simpl. split_and !; auto. done. *)
  (*     + pose proof (HCO2 n). subst. clear HCO1 HCO2. *)
  (*       exists (<[k:=wlive ℵ]>Wi). split; apply map_Forall2_insert; auto. *)
  (*       simpl. split_and !; auto. *)
  (*       -- intros. exfalso. destruct H1 as (?&?&?). subst. rewrite lookup_insert_eq in H1. inv H1. *)
  (*       -- intros j. specialize (WPi j). destruct (W2 !! j) eqn:LUj1. *)
  (*          ++ destruct (decide (j = k)). *)
  (*             { subst. rewrite LUW2 in LUj1; done. } *)
  (*             rewrite LUj1 in WPi. destruct (Wi !! j) eqn:LUj2. *)
  (*             ** rewrite LUj1. inv WPi. destruct H3. econstructor. split; intro. *)
  (*                { destruct H3 as (?&?&?). rewrite lookup_insert_ne in H3; eauto. } *)
  (*                { apply H2. intros ?. apply H3. destruct H4 as (?&?&?). rewrite lookup_insert_ne; eauto. } *)
  (*             ** inv WPi. *)
  (*          ++ rewrite LUj1 in WPi. destruct (Wi !! j) eqn:LUj2. *)
  (*             ** inv WPi. *)
  (*             ** rewrite LUj1. econstructor. *)
  (*   - simpl in *. assert (inr o = o2) by (by apply HCO2). clear HCO1 HCO2. subst. *)
  (*     exists (<[k:=wdone]>Wi). split; apply map_Forall2_insert; auto. *)
  (*     simpl. split_and !; auto. *)
  (*     * intros. destruct H1 as (?&?&?). rewrite lookup_insert_eq in H1. inv H1. *)
  (*     * intros. destruct u. done. *)
  (*     * intros j. specialize (WPi j). destruct (W2 !! j) eqn:LUj1. *)
  (*       -- destruct (decide (j = k)). *)
  (*          { subst. rewrite LUW2 in LUj1; done. } *)
  (*          rewrite LUj1 in WPi. destruct (Wi !! j) eqn:LUj2. *)
  (*          ++ rewrite LUj1. inv WPi. destruct H3. econstructor. split; intro. *)
  (*             { destruct H3 as (?&?&?). rewrite lookup_insert_ne in H3; eauto. } *)
  (*             { apply H2. intros ?. apply H3. destruct H4 as (?&?&?). rewrite lookup_insert_ne; eauto. } *)
  (*          ++ inv WPi. *)
  (*       -- rewrite LUj1 in WPi. destruct (Wi !! j) eqn:LUj2. *)
  (*          ++ inv WPi. *)
  (*          ++ rewrite LUj1. econstructor. *)
  (* Qed. *)

  (* TODO : sched fair case *)

End glwit.

(* Allocation of the initial witness protocol. *)
Lemma glwit_alloc `{SI : indexT} `{WFA : WFOCM.pack A} {ps T} {Σ}
  `{!@osatGS.osatGS _ _ WFA ps T Σ} `{!glwitGpreS Σ}
  `{wit_live_class A WFOCM.ltR} :
  ⊢ |==> ∃ _ : glwitGS Σ, glwit ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=bcredUR) ⊤)) as (γC) "HC";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (GlwitG SI _ WFA _ _ γC).
  rewrite /glwit -lock.
  replace (⊤ ∖ gset_to_coPset (dom (∅ : wit_states))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
