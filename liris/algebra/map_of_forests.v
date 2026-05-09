From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From liris.algebra Require Export map_of_sets forest.

Section forest.
  Context {V : Type}.
  Context `{!EqDecision V} `{!Countable V}.
  Implicit Type t : tree V.
  Implicit Type f : forest V.
  Implicit Type v u ρ π : V.
  Implicit Type C : gset V.

  (** ** Definitions *)
  Definition forest_subseteq (f1 f2 : forest V) : Prop := f1 ⊆ f2.
  (** Only keeps trees where roots are in the set rs. *)
  Definition forest_filter_roots (f : forest V) (rs : gset V) : forest V :=
    filter (λ '(r, _), r ∈ rs) f.

  (** ** forest_subseteq lemmas *)
  Lemma forest_trees_disjoint_spec_1 f :
    forest_trees_disjoint f → ∀ r1 r2 t1 t2, r1 ≠ r2 → f !! r1 = Some t1 → f !! r2 = Some t2 → t1 ##ₘ t2.
  Proof using.
    intros. unfold forest_trees_disjoint in H0. apply elem_of_map_to_list, list_elem_of_lookup in H1, H2.
    destruct H1 as (i1& LU1), H2 as (i2& LU2). assert (Ne : i1 ≠ i2).
    { intros <-. rewrite LU1 in LU2. simplify_eq. }
    specialize (H i1 i2). apply H; auto.
    { unfold forest_to_trees. rewrite list_lookup_fmap LU1. done. }
    { unfold forest_to_trees. rewrite list_lookup_fmap LU2. done. }
  Qed.

  Lemma forest_trees_disjoint_spec_2 f :
    (∀ r1 r2 t1 t2, r1 ≠ r2 → f !! r1 = Some t1 → f !! r2 = Some t2 → t1 ##ₘ t2) → forest_trees_disjoint f.
  Proof using.
    intros. unfold forest_trees_disjoint. intros ???????.
    unfold forest_to_trees in H1, H2. apply list_lookup_fmap_Some_1 in H1, H2.
    destruct H1 as (?&?&?), H2 as (?&?&?). destruct x, x0. simplify_eq. simpl.
    assert (∃ j,  map_to_list f !! j = Some (v, g)) by eauto. apply list_elem_of_lookup in H1.
    assert (∃ j,  map_to_list f !! j = Some (v0, g0)) by eauto. apply list_elem_of_lookup in H2.
    apply elem_of_map_to_list in H1, H2. assert (v ≠ v0).
    { intros <-. rewrite H1 in H2. simplify_eq. pose proof (NoDup_map_to_list f).
      eapply (NoDup_lookup _ j1 j2) in H3; eauto. }
    eapply H; eauto.
  Qed.

  Lemma forest_trees_disjoint_spec f :
    forest_trees_disjoint f ↔ ∀ r1 r2 t1 t2, r1 ≠ r2 → f !! r1 = Some t1 → f !! r2 = Some t2 → t1 ##ₘ t2.
  Proof using. split; [apply forest_trees_disjoint_spec_1 | apply forest_trees_disjoint_spec_2]. Qed.

  Lemma forest_subseteq_wf f1 f2 :
    forest_wf f2 →
    forest_subseteq f1 f2 →
    forest_wf f1.
  Proof using.
    intros. rewrite /forest_subseteq map_subseteq_spec in H0. destruct H. split.
    - apply forest_trees_disjoint_spec. intros. rewrite forest_trees_disjoint_spec in H.
      eapply (H r1 r2 t1 t2); auto.
    - intros ???. eapply H1; eauto.
  Qed.

  (** ** forest_filter_roots lemmas *)
  Lemma forest_filter_roots_subseteq f rs :
    forest_subseteq (forest_filter_roots f rs) f.
  Proof using. apply map_filter_subseteq. Qed.

  Lemma forest_filter_roots_disjoint f rs1 rs2 :
    forest_wf f →
    rs1 ## rs2 →
    forest_disjoint (forest_filter_roots f rs1) (forest_filter_roots f rs2).
  Proof using.
    intros. apply map_disjoint_spec. intros.
    apply map_lookup_filter_Some in H1, H2. destruct H1, H2.
    set_solver.
  Qed.

End forest.

Section map_of_forests.
  Context {K V : Type}.
  Context `{!EqDecision K} `{!Countable K} `{!EqDecision V} `{!Countable V}.

  (** ** Definitions *)
  (** F is a forest, Rs is the map of roots.
      forest_to_forests transforms F into a map of forests, where the roots are given as Rs. *)
  Definition forest_to_forests (F : forest V) (Rs : gmap K (gset V)) : gmap K (forest V) :=
    (λ rs, forest_filter_roots F rs) <$> Rs.

  (** Conditions for the forest_to_forests operation to be well-formed. *)
  Definition forest_to_forests_wf (F : forest V) (Rs : gmap K (gset V)) : Prop :=
    disjoint_sets Rs ∧ (dom F = union_sets Rs) ∧ forest_wf F.

  (** ** Lemmas *)
  Lemma forest_to_forests_lookup F Rs k f :
    forest_to_forests F Rs !! k = Some f →
    ∃ rs, Rs !! k = Some rs ∧ f = forest_filter_roots F rs.
  Proof using.
    intros. apply lookup_fmap_Some in H. destruct H as (rs&?&?). eauto.
  Qed.

  Lemma forest_to_forests_disjoint_forest F Rs k1 k2 f1 f2 :
    forest_to_forests_wf F Rs →
    k1 ≠ k2 →
    forest_to_forests F Rs !! k1 = Some f1 →
    forest_to_forests F Rs !! k2 = Some f2 →
    forest_disjoint f1 f2.
  Proof using.
    intros. destruct H as (Disj& Dom& Fwf).
    apply lookup_fmap_Some in H1, H2. destruct H1 as (?&?&?), H2 as (?&?&?). simplify_eq.
    assert (x ## x0) by (eapply Disj; eauto).
    eapply forest_filter_roots_disjoint; eauto.
  Qed.

  Lemma forest_to_forests_lookup_wf F Rs k f :
    forest_to_forests_wf F Rs →
    forest_to_forests F Rs !! k = Some f →
    forest_wf f.
  Proof using.
    intros. apply forest_to_forests_lookup in H0. destruct H0 as (?&?&?).
    destruct H as (Disj& Dom& Fwf). eapply forest_subseteq_wf. 1: eapply Fwf.
    simplify_eq. apply forest_filter_roots_subseteq.
  Qed.

  (** ** Lemmas for forest_to_forests_wf F Rs. *)
  (** In this part, we state and prove lemmas about
      how forest_to_forests_wf is preserved under various operations on the forst F,
      and various operations on the root set Rs.
      For example, we can insert/delete keys of the map, and update each set in Rs.
      Forest supports many operations, as defined in forest.v,
      which also contains useful lemmas for forest_wf under forest operations.
      map_of_sets.v contains useful lemmas to work with disjoint_sets and union_sets. *)

  (** ** Basic projection / reconstruction lemmas for [forest_to_forests_wf] *)

  Lemma forest_to_forests_wf_intro F Rs :
    disjoint_sets Rs ->
    dom F = union_sets Rs ->
    forest_wf F ->
    forest_to_forests_wf F Rs.
  Proof using. intros. split; auto. Qed.

  Lemma forest_to_forests_wf_disjoint_sets F Rs :
    forest_to_forests_wf F Rs ->
    disjoint_sets Rs.
  Proof using. intros (?&?&?). done. Qed.

  Lemma forest_to_forests_wf_dom_eq F Rs :
    forest_to_forests_wf F Rs ->
    dom F = union_sets Rs.
  Proof using. intros (?&?&?). done. Qed.

  Lemma forest_to_forests_wf_forest_wf F Rs :
    forest_to_forests_wf F Rs ->
    forest_wf F.
  Proof using. intros (?&?&?). done. Qed.

  (** If only [F] changes, and its root-domain stays the same, then
      [forest_to_forests_wf] is preserved. *)
  Lemma forest_to_forests_wf_forest_eq_dom F F' Rs :
    forest_to_forests_wf F Rs ->
    dom F' = dom F ->
    forest_wf F' ->
    forest_to_forests_wf F' Rs.
  Proof using.
    intros (?&Hdom&?) HFdom Hwf'.
    split_and !; auto.
    by rewrite HFdom Hdom.
  Qed.

  (** If only [Rs] changes, and it is still a disjoint partition of the same
      root-domain, then [forest_to_forests_wf] is preserved. *)
  Lemma forest_to_forests_wf_roots_eq_union F Rs Rs' :
    forest_to_forests_wf F Rs ->
    disjoint_sets Rs' ->
    union_sets Rs' = union_sets Rs ->
    forest_to_forests_wf F Rs'.
  Proof using.
    intros (?&Hdom&Hwf) Hdisj Hu.
    split_and !; auto.
    by rewrite Hu Hdom.
  Qed.

  (** ** Lemmas for operations on the roots map [Rs] *)

  Lemma forest_to_forests_wf_roots_insert_empty F Rs k :
    forest_to_forests_wf F Rs ->
    Rs !! k = None ->
    forest_to_forests_wf F (<[k := ∅]> Rs).
  Proof using.
    intros Hwf Hk.
    eapply forest_to_forests_wf_roots_eq_union; [exact Hwf| |].
    - apply disjoint_sets_insert_2; auto.
      + set_solver.
      + by eapply forest_to_forests_wf_disjoint_sets.
    - rewrite union_sets_insert_L; auto. set_solver.
  Qed.

  Lemma forest_to_forests_wf_roots_delete_empty F Rs k :
    forest_to_forests_wf F Rs ->
    Rs !! k = Some (∅ : gset V) ->
    forest_to_forests_wf F (delete k Rs).
  Proof using.
    intros Hwf Hk.
    eapply forest_to_forests_wf_roots_eq_union; [exact Hwf| |].
    - apply disjoint_sets_delete.
      by eapply forest_to_forests_wf_disjoint_sets.
    - pose proof (union_sets_delete_L Rs k ∅ Hk). set_solver.
  Qed.

  Lemma forest_to_forests_wf_roots_rename_key F Rs k k' rs :
    forest_to_forests_wf F Rs ->
    k' ≠ k ->
    Rs !! k = Some rs ->
    Rs !! k' = None ->
    forest_to_forests_wf F (<[k' := rs]>(delete k Rs)).
  Proof using.
    intros Hwf Hne Hk Hk'.
    destruct Hwf as (Hdisj&Hdom&Hfwf).
    eapply forest_to_forests_wf_roots_eq_union.
    - split_and !; eauto.
    - apply disjoint_sets_insert_2.
      + rewrite lookup_delete_ne; [done|congruence].
      + eapply disjoint_sets_lookup_disjoint_union_sets_delete; eauto.
      + by apply disjoint_sets_delete.
    - rewrite union_sets_insert_L.
      + rewrite (union_sets_delete_L Rs k rs); auto.
      + rewrite lookup_delete_ne; [done|congruence].
  Qed.

  Lemma forest_to_forests_wf_roots_move_root F Rs k1 k2 rs1 rs2 ρ :
    forest_to_forests_wf F Rs ->
    k1 ≠ k2 ->
    Rs !! k1 = Some rs1 ->
    Rs !! k2 = Some rs2 ->
    ρ ∈ rs1 ->
    forest_to_forests_wf F (<[k2 := rs2 ∪ {[ρ]}]>(<[k1 := rs1 ∖ {[ρ]}]> Rs)).
  Proof using.
    intros Hwf Hne Hk1 Hk2 Hρ.
    destruct Hwf as (Hdisj&Hdom&Hfwf).
    set (Rs1 := <[k1 := rs1 ∖ {[ρ]}]> Rs).
    eapply forest_to_forests_wf_roots_eq_union.
    - split_and !; eauto.
    - subst Rs1.
      apply disjoint_sets_insert_union_singleton_not_in.
      + rewrite lookup_insert_ne; [exact Hk2|done].
      + eapply disjoint_sets_insert_difference; eauto.
      + rewrite union_sets_insert_difference_singleton_L; eauto. set_solver.
    - subst Rs1.
      rewrite union_sets_insert_union_L.
      2:{ rewrite lookup_insert_ne; [exact Hk2|done]. }
      rewrite union_sets_insert_difference_singleton_L; eauto.
      rewrite -union_difference_L; auto. apply union_sets_lookup_subseteq in Hk1. set_solver.
  Qed.

  Lemma forest_to_forests_wf_roots_split_key F Rs k k' rs rs1 rs2 :
    forest_to_forests_wf F Rs ->
    Rs !! k = Some rs ->
    Rs !! k' = None ->
    rs = rs1 ∪ rs2 ->
    rs1 ## rs2 ->
    forest_to_forests_wf F (<[k' := rs2]>(<[k := rs1]>(delete k Rs))).
  Proof using.
    intros Hwf Hk Hk' Hrs Hdisj12.
    destruct Hwf as (Hdisj&Hdom&Hfwf).
    assert (Hne : k' ≠ k) by congruence.
    pose proof (disjoint_sets_lookup_disjoint_union_sets_delete _ _ _ Hdisj Hk) as Hrest.
    eapply forest_to_forests_wf_roots_eq_union.
    - split_and !; eauto.
    - apply disjoint_sets_insert_2.
      + rewrite lookup_insert_ne; [|done].
        rewrite lookup_delete_ne; [done|congruence].
      + rewrite union_sets_insert_L; [|apply lookup_delete_eq].
        set_solver.
      + apply disjoint_sets_insert_2.
        * apply lookup_delete_eq.
        * set_solver.
        * by apply disjoint_sets_delete.
    - rewrite union_sets_insert_L.
      2:{
        rewrite lookup_insert_ne; [|done].
        rewrite lookup_delete_ne; [done|congruence].
      }
      rewrite union_sets_insert_L; [|apply lookup_delete_eq].
      rewrite (union_sets_delete_L Rs k rs); auto.
      set_solver.
  Qed.

  Lemma forest_to_forests_wf_roots_merge_keys F Rs k1 k2 rs1 rs2 :
    forest_to_forests_wf F Rs ->
    k1 ≠ k2 ->
    Rs !! k1 = Some rs1 ->
    Rs !! k2 = Some rs2 ->
    forest_to_forests_wf F (<[k1 := rs1 ∪ rs2]>(delete k2 Rs)).
  Proof using.
    intros Hwf Hne Hk1 Hk2.
    destruct Hwf as (Hdisj&Hdom&Hfwf).
    eapply forest_to_forests_wf_roots_eq_union.
    - split_and !; eauto.
    - apply disjoint_sets_insert_union.
      + rewrite lookup_delete_ne; [exact Hk1|congruence].
      + by apply disjoint_sets_delete.
      + rewrite elem_of_disjoint.
        intros e He1 He2.
        pose proof (disjoint_sets_lookup_disjoint_union_sets_delete _ _ _ Hdisj Hk2) as Hdisj'.
        rewrite elem_of_disjoint in Hdisj'.
        eapply (disjoint_sets_lookup_disjoint_union_sets_delete _ _ _ Hdisj Hk2); eauto.
        eapply (union_sets_mono (delete k1 (delete k2 Rs)) (delete k2 Rs)); eauto using delete_subseteq.
        apply delete_subseteq.
    - rewrite union_sets_insert_union_L.
      2:{ rewrite lookup_delete_ne; [exact Hk1|congruence]. }
      rewrite (union_sets_delete_L Rs k2 rs2); auto.
  Qed.

  (** ** Lemmas for operations on the forest [F] *)

  Lemma forest_to_forests_wf_forest_insert F Rs k rs ρ t :
    forest_to_forests_wf F Rs ->
    Rs !! k = Some rs ->
    F !! ρ = None ->
    tree_wf ρ t ->
    forest_tree_disjoint F t ->
    forest_to_forests_wf (forest_insert F ρ t) (<[k := rs ∪ {[ρ]}]> Rs).
  Proof using.
    intros (Hdisj&Hdom&Hwf) Hk Hρ Htwf Htdisj.
    split_and !; eauto.
    - apply disjoint_sets_insert_union_singleton_not_in; auto.
      apply not_elem_of_dom in Hρ.
      rewrite Hdom in Hρ. done.
    - rewrite /forest_insert dom_insert_L.
      rewrite union_sets_insert_union_L; auto.
      rewrite Hdom. set_solver.
    - by apply forest_insert_wf.
  Qed.

  Lemma forest_to_forests_wf_forest_insert_new_key F Rs k ρ t :
    forest_to_forests_wf F Rs ->
    Rs !! k = None ->
    F !! ρ = None ->
    tree_wf ρ t ->
    forest_tree_disjoint F t ->
    forest_to_forests_wf (forest_insert F ρ t) (<[k := {[ρ]}]> Rs).
  Proof using.
    intros (Hdisj&Hdom&Hwf) Hk Hρ Htwf Htdisj.
    split_and !; eauto.
    - apply disjoint_sets_insert_2; auto.
      apply not_elem_of_dom in Hρ. rewrite Hdom in Hρ. set_solver.
    - rewrite /forest_insert dom_insert_L.
      rewrite union_sets_insert_L; auto.
      rewrite Hdom. set_solver.
    - by apply forest_insert_wf.
  Qed.

  Lemma forest_to_forests_wf_forest_delete F Rs k rs ρ t :
    forest_to_forests_wf F Rs ->
    Rs !! k = Some rs ->
    F !! ρ = Some t ->
    ρ ∈ rs ->
    forest_to_forests_wf (delete ρ F) (<[k := rs ∖ {[ρ]}]> Rs).
  Proof using.
    intros (Hdisj&Hdom&Hwf) Hk Hρ Hrs.
    split_and !; eauto.
    - by eapply disjoint_sets_insert_difference.
    - rewrite dom_delete_L.
      rewrite Hdom.
      rewrite union_sets_insert_difference_singleton_L; auto.
    - by apply forest_delete_wf.
  Qed.

  Lemma forest_to_forests_wf_forest_delete_key F Rs k ρ t :
    forest_to_forests_wf F Rs ->
    Rs !! k = Some {[ρ]} ->
    F !! ρ = Some t ->
    forest_to_forests_wf (delete ρ F) (delete k Rs).
  Proof using.
    intros (Hdisj&Hdom&Hwf) Hk Hρ.
    split_and !; eauto.
    - by apply disjoint_sets_delete.
    - rewrite dom_delete_L.
      rewrite Hdom.
      rewrite (union_sets_delete_L Rs k {[ρ]}); auto.
      assert (ρ ∉ union_sets (delete k Rs)).
      { apply not_elem_of_union_sets. intros. destruct (decide (k = k0)).
        { subst. rewrite lookup_delete_eq in H. done. }
        rewrite lookup_delete_ne in H; auto. specialize (Hdisj _ _ _ _ n Hk H). set_solver. }
      set_solver.
    - by apply forest_delete_wf.
  Qed.

  Lemma forest_to_forests_wf_forest_move_tree F Rs k rs ρ ρt r rt π πC :
    forest_to_forests_wf F Rs ->
    Rs !! k = Some rs ->
    r ∈ rs ->
    ρ ≠ r ->
    F !! r = Some rt ->
    F !! ρ = Some ρt ->
    ρt !! π = Some πC ->
    forest_to_forests_wf (forest_move_tree F ρ ρt r rt π πC)
                         (<[k := rs ∖ {[r]}]> Rs).
  Proof using.
    intros (Hdisj&Hdom&Hwf) Hk Hr Hne HrF HρF Hπ.
    split_and !; eauto.
    - by eapply disjoint_sets_insert_difference.
    - rewrite /forest_move_tree /forest_insert dom_insert_L !dom_delete_L.
      rewrite Hdom.
      rewrite union_sets_insert_difference_singleton_L; auto.
      assert (ρ ∈ dom F) by (apply elem_of_dom; eauto).
      rewrite -union_difference_L; auto. set_solver.
    - by eapply forest_move_tree_wf.
  Qed.

  Lemma forest_to_forests_wf_tree_clear F Rs k rs ρ Cf :
    forest_to_forests_wf F Rs ->
    Rs !! k = Some rs ->
    ρ ∈ rs ->
    F !! ρ = Some (forest_merge ρ Cf) ->
    forest_fold Cf !! ρ = None ->
    forest_trees_disjoint Cf ->
    map_Forall (λ c ct, tree_wf c ct) Cf ->
    forest_to_forests_wf (tree_clear F ρ Cf) (<[k := rs ∪ dom Cf]> Rs).
  Proof using.
    intros (Hdisj&Hdom&Hfwf) Hk Hρrs Hρ HCfρ HCfdisj HCfwf.
    split_and !; eauto.
    - assert (dom Cf ## union_sets (delete k Rs)).
      { assert (rs ## union_sets (delete k Rs)).
        { apply disjoint_sets_lookup_disjoint_union_sets_delete; auto. }
        assert (union_sets (delete k Rs) = (dom F ∖ rs)).
        { rewrite Hdom. erewrite (union_sets_delete_L Rs k); eauto. set_solver. }
        rewrite H0. assert (dom Cf ## dom F); last set_solver.
        intros ???. apply elem_of_dom in H2. destruct H2.
        assert (map_Forall (λ (c : V) (t : tree V), c ∈ dom t) Cf).
        { eapply map_Forall_impl. 1: eapply HCfwf. intros. by eapply tree_wf_root_elem. }
        destruct (decide (ρ = x)).
        { subst x. apply not_elem_of_dom in HCfρ.
          pose proof (dom_subseteq_forest_fold_dom Cf HCfdisj H3). set_solver. }
        { destruct Hfwf. assert ((forest_merge ρ Cf) ##ₘ x0).
          { eapply (forest_trees_disjoint_lookup_disjoint F ρ x); eauto. }
          eapply H5 in H2. apply tree_wf_root_elem in H2. apply map_disjoint_dom in H6.
          assert (map_Forall (λ (c : V) (t : tree V), c ∈ dom t) Cf).
          { eapply map_Forall_impl. 1: eapply HCfwf. intros. by eapply tree_wf_root_elem. }
          pose proof (dom_subseteq_forest_merge_dom ρ Cf HCfdisj H7). set_solver. }
      }
      eapply disjoint_sets_insert_union; eauto.
    - rewrite /tree_clear forest_union_dom.
      rewrite /tree_split /forest_insert dom_insert_L dom_delete_L.
      rewrite union_sets_insert_union_L; auto.
      rewrite Hdom.
      assert (ρ ∈ union_sets Rs).
      { apply elem_of_union_sets. intros. eauto. }
      assert (ρ ∉ dom Cf).
      { apply not_elem_of_dom. apply forest_fold_not_in_forest_not_in; auto. split; auto. }
      rewrite union_assoc_L. rewrite difference_union_L. set_solver.
    - eapply tree_clear_wf; eauto.
  Qed.

  Lemma forest_to_forests_wf_forest_union F1 F2 Rs1 Rs2 :
    forest_to_forests_wf F1 Rs1 ->
    forest_to_forests_wf F2 Rs2 ->
    forest_disjoint F1 F2 ->
    Rs1 ##ₘ Rs2 ->
    map_Forall (λ _ rs, rs ## union_sets Rs2) Rs1 ->
    map_Forall (λ _ t, forest_tree_disjoint F1 t) F2 ->
    forest_to_forests_wf (forest_union F1 F2) (Rs1 ∪ Rs2).
  Proof using.
    intros (Hdisj1&Hdom1&Hwf1) (Hdisj2&Hdom2&Hwf2) HFdisj HRsdisj Hrs12 HF12.
    split_and !; eauto.
    - eapply disjoint_sets_disj_union; eauto.
    - rewrite forest_union_dom.
      rewrite union_sets_disj_union_L; auto.
      by rewrite Hdom1 Hdom2.
    - eapply forest_union_wf; eauto.
  Qed.

  Lemma forest_to_forests_wf_forest_insert_singleton F Rs k rs ρ :
    forest_to_forests_wf F Rs ->
    Rs !! k = Some rs ->
    forest_fold F !! ρ = None ->
    forest_to_forests_wf (forest_insert F ρ (tree_singleton ρ))
      (<[k := rs ∪ {[ρ]}]> Rs).
  Proof using.
    intros.
    destruct H as (?&?&?). destruct H3. assert (map_Forall (λ (c : V) (t : tree V), c ∈ dom t) F).
    { eapply map_Forall_impl. 1: eapply H4. intros. by eapply tree_wf_root_elem. }
    assert (F !! ρ = None).
    { apply not_elem_of_dom. apply not_elem_of_dom in H1. pose proof (dom_subseteq_forest_fold_dom F).
      specialize (H6 H3 H5). set_solver. }
    apply forest_to_forests_wf_forest_insert; auto.
    - split_and !; auto. split; auto.
    - apply tree_singleton_wf.
    - apply forest_tree_disjoint_tree_singleton; auto.
  Qed.

  Lemma forest_to_forests_wf_forest_insert_singleton_new_key F Rs k ρ :
    forest_to_forests_wf F Rs ->
    Rs !! k = None ->
    forest_fold F !! ρ = None ->
    forest_to_forests_wf (forest_insert F ρ (tree_singleton ρ))
                         (<[k := {[ρ]}]> Rs).
  Proof using.
    intros.
    destruct H as (?&?&?). destruct H3. assert (map_Forall (λ (c : V) (t : tree V), c ∈ dom t) F).
    { eapply map_Forall_impl. 1: eapply H4. intros. by eapply tree_wf_root_elem. }
    assert (F !! ρ = None).
    { apply not_elem_of_dom. apply not_elem_of_dom in H1. pose proof (dom_subseteq_forest_fold_dom F).
      specialize (H6 H3 H5). set_solver. }
    apply forest_to_forests_wf_forest_insert_new_key; auto.
    - split_and !; auto. split; auto.
    - apply tree_singleton_wf.
    - apply forest_tree_disjoint_tree_singleton; auto.
  Qed.

End map_of_forests.
