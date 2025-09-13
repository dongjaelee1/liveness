From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.

Notation tree V := (gmap V (gset V)).
Notation forest V := (gmap V (tree V)).

Section forest_pre.
  Context {V : Type}.
  Context `{Countable V}.
  Implicit Type t : tree V.
  Implicit Type f : forest V.
  Implicit Type v u ρ π : V.
  Implicit Type C : gset V.

  Definition forest_to_trees f : list (tree V) := (map_to_list f).*2.
  Definition forest_fold f : tree V := ⋃ (forest_to_trees f).
  Definition forest_trees_disjoint f : Prop := map_disjoint_list (forest_to_trees f).
  Definition forest_fold_alt f : tree V := map_fold (λ _ t a, t ∪ a) ∅ f.
  Definition forest_union f1 f2 : forest V := f1 ∪ f2.
  Definition forest_disjoint : relation (forest V) := λ f1 f2, f1 ##ₘ f2.
  Definition forest_tree_disjoint f t : Prop := map_Forall (λ _ m, m ##ₘ t) f.
  Definition map_fold_or m (Φ : V → tree V → Prop) : Prop := map_fold (λ i s a, (Φ i s) ∨ a) False m.
  Definition forest_node_in_tree f : V → Prop := λ v, map_fold_or f (λ _ t, (is_Some (t !! v))).
  (* Definition forest_node_in_tree f : V → Prop := λ v, map_fold (λ _ t a, (is_Some (t !! v)) ∨ a) False f. *)

  Lemma forest_fold_internal_elem_of u f :
    u ∈ dom (forest_fold f) →
    u ∉ dom f →
    ∃ ρ t, f !! ρ = Some t ∧ u ∈ dom t.
  Proof using.
    unfold forest_fold, forest_to_trees, map_to_list.
    revert u. pattern f. revert f. apply fin_maps.map_fold_ind; intros.
    { exfalso. rewrite map_fold_empty in H0. set_solver. }
    rewrite dom_insert in H4. apply not_elem_of_union in H4. destruct H4.
    rewrite H1 in H3. rewrite fmap_cons union_list_cons dom_union_L in H3. apply elem_of_union in H3. destruct H3.
    - exists i, x. split; auto. by rewrite lookup_insert_eq.
    - specialize (H2 _ H3 H5). destruct H2 as (?&?&?&?).
      assert (Hne : x0 ≠ i).
      { intros ?; subst. by rewrite H0 in H2. }
      exists x0, x1. rewrite lookup_insert_ne; auto.
  Qed.

  Lemma forest_trees_disjoint_fold f :
    forest_trees_disjoint f → forest_fold_alt f = forest_fold f.
  Proof using.
    unfold forest_trees_disjoint, forest_fold, forest_to_trees, forest_fold_alt.
    induction f using map_ind; intros.
    { rewrite map_fold_empty map_to_list_empty. done. }
    rewrite map_to_list_insert in H1; last done.
    pose proof H1 as Hdj. rewrite fmap_cons map_disjoint_list_cons in H1. destruct H1.
    pose proof H2. apply IHf in H3. clear IHf.
    rewrite map_fold_insert_L; auto.
    - pose proof (map_to_list_insert _ _ x H0).
      assert ((map_to_list (<[i:=x]> m)).*2 ≡ₚ x :: ((map_to_list m).*2)).
      { rewrite H4. rewrite fmap_cons. done. }
      rewrite (map_union_list_Permutation _ _ H5).
      + by rewrite H3 union_list_cons.
      + rewrite map_to_list_insert; auto.
    - intros. assert (z1 ##ₘ z2).
      { assert (map_Forall (λ _ m2, m2 ##ₘ x) m).
        { apply map_Forall_to_list. apply Forall_fmap in H1. eapply Forall_impl; eauto.
          intros (?&?). auto.
        }
        destruct (decide (i = j1)).
        - subst. rewrite lookup_insert_eq in H5. inv H5. rewrite lookup_insert_ne in H6; last auto.
          specialize (H7 _ _ H6). set_solver.
        - destruct (decide (i = j2)).
          + subst. rewrite lookup_insert_eq in H6. inv H6. rewrite lookup_insert_ne in H5; last auto.
            specialize (H7 _ _ H5). set_solver.
          + rewrite lookup_insert_ne in H5; auto. rewrite lookup_insert_ne in H6; auto.
            rewrite -(map_to_list_delete _ _ _ H5) in H2.
            rewrite -(lookup_delete_ne _ j1) in H6; last auto.
            rewrite -(map_to_list_delete _ _ _ H6) in H2. rewrite !fmap_cons in H2.
            apply map_disjoint_list_cons in H2. destruct H2.
            apply map_disjoint_list_cons in H8. destruct H8.
            simpl in H2, H8. apply Forall_cons in H2. destruct H2. set_solver.
      }
      rewrite !map_union_assoc. f_equal. apply map_union_comm; auto.
  Qed.

  Lemma forest_fold_insert_L f ρ t :
    forest_trees_disjoint (<[ρ:=t]>f) → f !! ρ = None →
    forest_fold (<[ρ:=t]>f) = t ∪ (forest_fold f).
  Proof using.
    unfold forest_trees_disjoint, forest_fold, forest_to_trees, map_to_list. intros.
    assert ((map_fold (λ (i : V) (x : tree V), cons (i, x)) [] (<[ρ:=t]> f)).*2 ≡ₚ
              ((ρ, t) :: (map_fold (λ (i : V) (x : tree V), cons (i, x)) [] f)).*2).
    { f_equiv. etransitivity.
      - eapply (map_fold_insert Permutation); auto.
        + intros. solve_proper.
        + intros. econstructor.
      - done.
    }
    rewrite (map_union_list_Permutation _ _ H2).
    { by rewrite fmap_cons union_list_cons. }
    eapply map_disjoint_list_Permutation.
    2:{ symmetry. eapply H2. }
    eapply map_disjoint_list_Permutation; first eapply H0. eauto.
  Qed.

  Lemma forest_fold_insert_first_key_L f i t :
    f !! i = None → map_first_key (<[i:=t]> f) i →
    forest_fold (<[i:=t]> f) = t ∪ forest_fold f.
  Proof using.
    intros. unfold forest_fold, forest_to_trees, map_to_list.
    rewrite map_fold_insert_first_key; auto.
  Qed.

  Lemma forest_trees_disjoint_insert f ρ t :
    f !! ρ = None →
    (forest_trees_disjoint (<[ρ:=t]> f) ↔
     forest_tree_disjoint f t ∧ forest_trees_disjoint f).
  Proof using.
    unfold forest_tree_disjoint, forest_trees_disjoint, forest_to_trees. split; intros.
    - rewrite map_to_list_insert in H1; last auto. rewrite fmap_cons map_disjoint_list_cons in H1.
      destruct H1. split; last auto. apply map_Forall_to_list. apply Forall_fmap in H1.
      eapply Forall_impl; eauto. intros (?&?). done.
    - rewrite map_to_list_insert; last auto. rewrite fmap_cons map_disjoint_list_cons.
      destruct H1. split; last auto. apply map_Forall_to_list in H1. apply Forall_fmap.
      eapply Forall_impl; eauto. intros (?&?). done.
  Qed.

  Lemma forest_fold_empty : forest_fold ∅ = ∅.
  Proof using. done. Qed.

  Lemma tree_disjoint_forest_fold_disjoint t f :
    forest_tree_disjoint f t → t ##ₘ forest_fold f.
  Proof using.
    unfold forest_tree_disjoint, forest_fold, forest_to_trees.
    revert t. pattern f. revert f. apply map_first_key_ind; intros.
    { rewrite map_to_list_empty. apply map_disjoint_empty_r. }
    rewrite map_to_list_insert_first_key; auto. rewrite fmap_cons union_list_cons. simpl.
    apply map_Forall_insert in H3; last auto. destruct H3. eapply H2 in H4.
    apply map_disjoint_union_r_2; eauto.
  Qed.
  Lemma forest_fold_disjoint_tree_disjoint t f :
    t ##ₘ forest_fold f → forest_tree_disjoint f t.
  Proof using.
    unfold forest_tree_disjoint, forest_fold, forest_to_trees.
    revert t. pattern f. revert f. apply map_first_key_ind; intros.
    { done. }
    rewrite map_to_list_insert_first_key in H3; auto. rewrite fmap_cons union_list_cons in H3. simpl in H3.
    apply map_Forall_insert; auto. eapply map_disjoint_union_r in H3. destruct H3. split; auto.
  Qed.

  Lemma forest_tree_disjoint_insert f ρ t s :
    f !! ρ = None →
    forest_tree_disjoint (<[ρ:=t]>f) s ↔ t ##ₘ s ∧ forest_tree_disjoint f s.
  Proof using. intros ?. unfold forest_tree_disjoint. rewrite map_Forall_insert; auto. Qed.

  Lemma forest_tree_disjoint_union_tree f s t :
    forest_tree_disjoint f s ∧ forest_tree_disjoint f t ↔
    forest_tree_disjoint f (t ∪ s).
  Proof using.
    unfold forest_tree_disjoint. split; intros.
    - destruct H0. intros ? ? ?. specialize (H0 _ _ H2). specialize (H1 _ _ H2).
      apply map_disjoint_union_r_2; auto.
    - split; intros ???.
      + specialize (H0 _ _ H1). apply map_disjoint_union_r in H0. by destruct H0.
      + specialize (H0 _ _ H1). apply map_disjoint_union_r in H0. by destruct H0.
  Qed.

  Lemma forests_disjoint_forest_fold_disjoint f g :
    map_Forall (λ _ m, forest_tree_disjoint f m) g → forest_tree_disjoint f (forest_fold g).
  Proof using.
    revert f. induction g using map_first_key_ind; intros.
    { rewrite forest_fold_empty. unfold forest_tree_disjoint. intros ? ? ?. apply map_disjoint_empty_r. }
    rewrite map_Forall_insert in H2; auto. destruct H2. rewrite forest_fold_insert_first_key_L; auto.
    specialize (IHg _ H3). apply forest_tree_disjoint_union_tree; auto.
  Qed.
  Lemma forest_fold_disjoint_forests_disjoint f g :
    forest_tree_disjoint f (forest_fold g) → map_Forall (λ _ m, forest_tree_disjoint f m) g.
  Proof using.
    revert f. induction g using map_first_key_ind; intros.
    { done. }
    rewrite forest_fold_insert_first_key_L in H2; auto. apply forest_tree_disjoint_union_tree in H2.
    destruct H2. rewrite map_Forall_insert; auto.
  Qed.

  Lemma forest_fold_subseteq f ρ t :
    forest_trees_disjoint f → f !! ρ = Some t → t ⊆ forest_fold f.
  Proof using.
    revert ρ t. induction f using map_ind; intros.
    { done. }
    rewrite forest_fold_insert_L; auto.
    apply forest_trees_disjoint_insert in H1; last auto. destruct H1.
    destruct (decide (i = ρ)).
    - subst. rewrite lookup_insert_eq in H2. inv H2. apply map_union_subseteq_l.
    - rewrite lookup_insert_ne in H2; last auto. apply map_union_subseteq_r'; last eauto.
      apply tree_disjoint_forest_fold_disjoint; auto.
  Qed.

  Lemma forest_fold_dom_forest_subseteq f :
    forest_trees_disjoint f →
    map_Forall (λ c t, c ∈ dom t) f → dom f ⊆ dom (forest_fold f).
  Proof using.
    induction f using map_ind; intros.
    { done. }
    rewrite map_Forall_insert in H2; last auto. destruct H2. intros v.
    rewrite dom_insert_L. intros Hv. rewrite forest_fold_insert_L; auto. rewrite dom_union.
    apply elem_of_union in Hv. destruct Hv.
    - apply elem_of_singleton in H4. subst. set_solver.
    - apply forest_trees_disjoint_insert in H1; last auto. destruct H1. specialize (IHf H5 H3).
      set_solver.
  Qed.

  Lemma forest_fold_lookup_Some_exists_root f v C :
    forest_trees_disjoint f →
    (forest_fold f) !! v = Some C →
    ∃ r t, f !! r = Some t ∧ t !! v = Some C.
  Proof using.
    revert v C. induction f using map_ind; intros.
    { rewrite forest_fold_empty in H1. done. }
    rewrite forest_fold_insert_L in H2; auto. rewrite forest_trees_disjoint_insert in H1; auto. destruct H1.
    apply lookup_union_Some_raw in H2. destruct H2.
    - exists i, x. rewrite lookup_insert_eq. auto.
    - destruct H2. specialize (IHf _ _ H3 H4). destruct IHf as (?&?&?&?).
      assert (i ≠ x0).
      { intros <-. by rewrite H0 in H5. }
      exists x0, x1. rewrite lookup_insert_ne; auto.
  Qed.

  Lemma forest_trees_disjoint_lookup_disjoint f r1 r2 t1 t2 :
    forest_trees_disjoint f → r1 ≠ r2 → f !! r1 = Some t1 → f !! r2 = Some t2 → t1 ##ₘ t2.
  Proof using.
    revert r1 r2 t1 t2. induction f using map_ind; intros; first done.
    apply forest_trees_disjoint_insert in H1; auto. destruct H1.
    destruct (decide (i = r1)).
    - subst. rewrite lookup_insert_eq in H3. rewrite lookup_insert_ne in H4; auto. inv H3.
      specialize (H1 _ _ H4). auto.
    - destruct (decide (i = r2)).
      + subst. rewrite lookup_insert_eq in H4. rewrite lookup_insert_ne in H3; auto. inv H4.
        specialize (H1 _ _ H3). auto.
      + rewrite lookup_insert_ne in H4; auto. rewrite lookup_insert_ne in H3; auto.
        eapply (IHf _ _ _ _ H5 H2 H3 H4).
  Qed.

  Lemma forest_fold_lookup_Some_root_unique f v r1 r2 t1 t2 :
    forest_trees_disjoint f →
    f !! r1 = Some t1 → is_Some (t1 !! v) →
    f !! r2 = Some t2 → is_Some (t2 !! v) →
    r1 = r2.
  Proof using.
    intros. destruct (decide (r1 = r2)); auto. exfalso.
    pose proof (forest_trees_disjoint_lookup_disjoint _ _ _ _ _ H0 n H1 H3). destruct H2, H4.
    rewrite (map_disjoint_Some_r _ _ _ _ H5 H4) in H2. done.
  Qed.

  Lemma forest_fold_lookup_child_tree f v C t :
    forest_trees_disjoint f →
    (forest_fold f) !! v = Some C → f !! v = Some t → v ∈ dom t →
    t !! v = Some C.
  Proof using.
    intros. pose proof (forest_fold_lookup_Some_exists_root _ _ _ H0 H1). destruct H4 as (?&?&?&?).
    apply elem_of_dom in H3. assert (is_Some (x0 !! v)) by eauto.
    pose proof (forest_fold_lookup_Some_root_unique _ _ _ _ _ _ H0 H2 H3 H4 H6). subst x.
    rewrite H2 in H4. inv H4. auto.
  Qed.

  Lemma forest_fold_empty_inv f :
    (∀ v t, f !! v = Some t → t ≠ ∅) → forest_fold f = ∅ → f = ∅.
  Proof using.
    induction f using map_first_key_ind; intros; auto.
    unfold forest_fold, forest_to_trees in H3.
    rewrite map_to_list_insert_first_key in H3; auto.
    rewrite fmap_cons union_list_cons in H3. simpl in H3.
    assert (x ≠ (∅ : tree V)).
    { eapply H2. eapply lookup_insert_eq. }
    apply leibniz_equiv_iff in H3.
    destruct (map_to_list x !! 0) eqn:Hfk.
    2:{ destruct (map_to_list x) eqn:Hml.
        - apply map_to_list_empty_iff in Hml. done.
        - done.
    }
    destruct p. assert (x !! v = Some g).
    { apply elem_of_map_to_list. eapply list_elem_of_lookup_2; eauto. }
    pose proof (lookup_union_Some_l _ (⋃ (map_to_list m).*2) _ _ H5).
    specialize (H3 v). rewrite H6 in H3. rewrite lookup_empty in H3. inv H3.
  Qed.

  Lemma forest_fold_delete_L f v t :
    forest_trees_disjoint f → f !! v = Some t →
    forest_fold f = t ∪ forest_fold (delete v f).
  Proof using.
    unfold forest_trees_disjoint, forest_fold, forest_to_trees. intros.
    erewrite (map_union_list_Permutation (map_to_list f).*2).
    2:{ symmetry. eapply fmap_Permutation. eapply (map_to_list_delete _ v t H1). }
    2: auto.
    rewrite fmap_cons union_list_cons. done.
  Qed.

  Lemma forest_trees_disjoint_delete_1 f v :
    forest_trees_disjoint f → forest_trees_disjoint (delete v f).
  Proof using.
    unfold forest_trees_disjoint, forest_to_trees. destruct (f !! v) eqn:Hv.
    - replace (map_to_list f) with (map_to_list (<[v:=g]>(delete v f))).
      2:{ rewrite insert_delete_id; auto. }
      rewrite map_to_list_insert; last by rewrite lookup_delete_eq.
      rewrite fmap_cons map_disjoint_list_cons. intros [? ?]. auto.
    - rewrite delete_id; auto.
  Qed.

  Lemma forest_trees_disjoint_delete f v t :
    f !! v = Some t →
    forest_trees_disjoint f ↔
    forest_tree_disjoint (delete v f) t ∧ forest_trees_disjoint (delete v f).
  Proof using.
    unfold forest_tree_disjoint. intros. remember (delete v f) as g.
    replace f with (<[v:=t]>(delete v f)); last by apply insert_delete_id.
    subst g. apply forest_trees_disjoint_insert. apply lookup_delete_eq.
  Qed.

  Lemma forest_tree_disjoint_union_forest_1 f1 f2 t :
    (forest_tree_disjoint f1 t ∧ forest_tree_disjoint f2 t) →
    forest_tree_disjoint (f1 ∪ f2) t.
  Proof using.
    unfold forest_tree_disjoint. intros.
    destruct H0. intros ???. apply lookup_union_Some_raw in H2. destruct H2.
    - specialize (H0 _ _ H2). done.
    - destruct H2. specialize (H1 _ _ H3). done.
  Qed.

  Lemma forest_tree_disjoint_union_forest_2 f1 f2 t :
    f1 ##ₘ f2 → forest_tree_disjoint (f1 ∪ f2) t →
    (forest_tree_disjoint f1 t ∧ forest_tree_disjoint f2 t).
  Proof using.
    unfold forest_tree_disjoint. intros. apply map_Forall_union in H1; auto.
  Qed.

  Lemma forest_trees_disjoint_union f1 f2 :
    forest_disjoint f1 f2 →
    forest_trees_disjoint f1 → forest_trees_disjoint f2 →
    map_Forall (λ _ m, forest_tree_disjoint f1 m) f2 →
    forest_trees_disjoint (forest_union f1 f2).
  Proof using.
    unfold forest_disjoint, forest_union. revert f1. induction f2 using map_first_key_ind; intros.
    { by rewrite map_union_empty. }
    apply forest_trees_disjoint_insert in H4; auto. destruct H4.
    apply map_disjoint_insert_r in H2. destruct H2.
    apply map_Forall_insert in H5; auto. destruct H5.
    specialize (IHf2 _ H7 H3 H6 H8). rewrite -insert_union_r; auto. apply forest_trees_disjoint_insert.
    - apply lookup_union_None_2; auto.
    - split; auto. apply forest_tree_disjoint_union_forest_1; auto.
  Qed.
  Lemma forest_trees_disjoint_union_inv f1 f2 :
    forest_disjoint f1 f2 →
    forest_trees_disjoint (forest_union f1 f2) →
    (forest_trees_disjoint f1 ∧
     forest_trees_disjoint f2 ∧
     map_Forall (λ _ m, forest_tree_disjoint f1 m) f2).
  Proof using.
    unfold forest_disjoint, forest_union. revert f2. induction f1 using map_first_key_ind; intros.
    { rewrite map_empty_union in H1. split_and !; try done. }
    apply map_disjoint_insert_l in H2. destruct H2.
    assert ((m ∪ f2) !! i = None).
    { apply lookup_union_None_2; auto. }
    rewrite -insert_union_l in H3. apply forest_trees_disjoint_insert in H3; auto. destruct H3.
    specialize (IHf1 _ H4 H6). destruct IHf1 as (IH1&IH2&IH3).
    split_and !; auto.
    - apply forest_trees_disjoint_insert; auto. split; auto.
      apply forest_tree_disjoint_union_forest_2 in H3; auto. by destruct H3.
    - intros ???. specialize (IH3 _ _ H7). apply forest_tree_disjoint_insert; auto.
      split; auto. symmetry. assert ((m ∪ f2) !! i0 = Some x0).
      { rewrite lookup_union_r; auto. eapply map_disjoint_Some_r; eauto. }
      eapply H3; eauto.
  Qed.

  Lemma forest_fold_union f1 f2 :
    forest_disjoint f1 f2 →
    forest_trees_disjoint (forest_union f1 f2) →
    forest_fold (forest_union f1 f2) = forest_fold f1 ∪ forest_fold f2.
  Proof using.
    unfold forest_disjoint, forest_union.
    revert f2. induction f1 using map_ind; intros.
    { rewrite forest_fold_empty !map_empty_union. done. }
    apply map_disjoint_insert_l in H1. destruct H1.
    assert ((m ∪ f2) !! i = None).
    { apply lookup_union_None_2; auto. }
    rewrite -insert_union_l in H2. apply forest_trees_disjoint_insert in H2; auto. destruct H2.
    specialize (IHf1 _ H3 H5).
    rewrite -insert_union_l. rewrite !forest_fold_insert_L; auto.
    - rewrite IHf1. by rewrite map_union_assoc.
    - apply forest_trees_disjoint_insert; auto.
      apply forest_trees_disjoint_union_inv in H5; auto. destruct H5 as (?&?&?).
      apply forest_tree_disjoint_union_forest_2 in H2; auto. destruct H2.
      split; auto.
    - apply forest_trees_disjoint_insert; auto.
  Qed.

  Lemma forest_union_dom f1 f2 :
    dom (forest_union f1 f2) = dom f1 ∪ dom f2.
  Proof using. unfold forest_union. apply dom_union_L. Qed.

  Lemma forest_fold_dom f :
    dom (forest_fold f) = map_fold (λ _ t a, (dom t) ∪ a) ∅ f.
  Proof using.
    unfold forest_fold, forest_to_trees, map_to_list. induction f using fin_maps.map_fold_ind.
    { done. }
    rewrite !H1. rewrite fmap_cons union_list_cons. rewrite dom_union_L. simpl. rewrite IHf. done.
  Qed.

  Lemma map_fold_dom_base f D :
    map_fold (λ _ t a, (dom t) ∪ a) D f = (map_fold (λ _ t a, (dom t) ∪ a) ∅ f) ∪ D.
  Proof using.
    assert (map_fold (λ (_ : V) t (a : gset V), dom t ∪ a) (∅ ∪ D) f = map_fold (λ (_ : V) t (a : gset V), dom t ∪ a) ∅ f ∪ D).
    { eapply (map_fold_comm_acc _ (λ a, a ∪ D) ∅). intros. set_solver. }
    rewrite union_empty_l_L in H0. auto.
  Qed.

  Lemma forest_fold_dom_insert f ρ t :
    f !! ρ = None →
    dom (forest_fold (<[ρ:=t]>f)) = dom t ∪ dom (forest_fold f).
  Proof using.
    intros. rewrite !forest_fold_dom map_fold_insert_L; auto.
    intros. set_solver.
  Qed.

  Lemma forest_fold_dom_delete f ρ t :
    f !! ρ = Some t →
    dom t ∪ dom (forest_fold (delete ρ f)) = dom (forest_fold f).
  Proof using.
    intros. rewrite !forest_fold_dom. rewrite (map_fold_delete_L _ _ ρ t f); eauto.
    intros. set_solver.
  Qed.

  Lemma forest_fold_dom_union f1 f2 :
    forest_disjoint f1 f2 →
    dom (forest_fold (forest_union f1 f2)) = dom (forest_fold f1) ∪ dom (forest_fold f2).
  Proof using.
    unfold forest_disjoint, forest_union. intros. rewrite !forest_fold_dom.
    rewrite map_fold_disj_union; auto. 2: set_solver. apply map_fold_dom_base.
  Qed.

  Lemma map_fold_or_insert m (Φ : V → tree V → Prop) P k t :
    (m !! k = None) →
    map_fold (λ i s a, (Φ i s) ∨ a) P (<[k:=t]>m) ↔ ((Φ k t) ∨ map_fold (λ i s a, (Φ i s) ∨ a) P m).
  Proof using.
    split; intros.
    - apply (map_fold_insert iff) in H1; auto. 1: solve_proper. 1: intuition.
    - apply (map_fold_insert iff); auto. 1: solve_proper. 1: intuition.
  Qed.

  Lemma forest_fold_node_in_tree f v :
    forest_trees_disjoint f →
    is_Some (forest_fold f !! v) ↔ forest_node_in_tree f v.
  Proof using.
    split.
    - unfold forest_node_in_tree, map_fold_or. revert v H0. induction f using map_ind; intros.
      { rewrite forest_fold_empty in H1. inv H1. }
      rewrite forest_fold_insert_L in H2; auto. apply forest_trees_disjoint_insert in H1; auto. destruct H1.
      apply map_fold_or_insert; auto. apply lookup_union_is_Some in H2. destruct H2; auto.
    - unfold forest_node_in_tree, map_fold_or. revert v H0. induction f using map_ind; intros.
      { rewrite map_fold_empty in H1. inv H1. }
      rewrite forest_fold_insert_L; auto. apply forest_trees_disjoint_insert in H1; auto. destruct H1.
      apply map_fold_or_insert in H2; auto. apply lookup_union_is_Some. destruct H2; auto.
  Qed.

  Global Instance map_fold_or_Decision f (Φ : V → tree V → Prop) : (∀ k t, Decision (Φ k t)) → Decision (map_fold_or f Φ).
  Proof using.
    intros. unfold map_fold_or. rewrite map_fold_foldr. remember (map_to_list f) as l.
    clear f Heql. induction l.
    { solve_decision. }
    rewrite foldr_cons. destruct a. simpl. apply or_dec; auto.
  Qed.

End forest_pre.

Section tree.
  Context {V : Type}.
  Context `{Countable V}.
  Implicit Type t s : tree V.
  Implicit Type f : forest V.
  Implicit Type v u ρ π : V.
  Implicit Type C : gset V.

  (** Basic definitions *)
  Definition node t v : Prop := is_Some (t !! v).
  Definition children t π C : Prop := t !! π = Some C.
  Definition child t : relation V := λ π v, ∃ C, children t π C ∧ v ∈ C.
  Definition internal t v : Prop := ∃ π, child t π v.
  Definition root t ρ : Prop := ∀ π, ¬ child t π ρ.

  Definition parent t : relation V := λ v π, ∃ C, children t π C ∧ v ∈ C.
  Definition internal_alt t v : Prop := ∃ π, parent t v π.
  Definition root_alt t ρ : Prop := ∀ π, ¬ parent t ρ π.

  Global Instance node_Decision t : ∀ v, Decision (node t v).
  Proof using.
    intros. unfold node. apply _.
  Qed.
  Global Instance children_Decision t : ∀ π C, Decision (children t π C).
  Proof using.
    intros. unfold children. apply _.
  Qed.
  Instance child_Decision_aux t π v : Decision (map_Exists (λ u C, u = π ∧ v ∈ C) t).
  Proof using. eapply map_Exists_dec. intros. solve_decision. Qed.
  Global Instance child_Decision t : ∀ π v, Decision (child t π v).
  Proof using.
    intros. unfold child, children. destruct (child_Decision_aux t π v).
    - left. destruct m as (?&?&?&?&?). subst. eauto.
    - right. intros (C&Hlu&Helem). apply n. exists π, C. auto.
  Qed.
  Global Instance internal_Decision t : ∀ v, Decision (internal t v).
  Proof using.
    intros. unfold internal, child, children. apply _.
  Qed.
  Global Instance root_Decision t : ∀ v, Decision (root t v).
  Proof using.
    intros. unfold root. destruct (internal_Decision t v).
    - right. intros F. destruct i. apply (F x). auto.
    - left. intros π Hp. apply n. exists π. auto.
  Qed.

  (** Operations *)
  Definition forest_merge ρ f : tree V := <[ρ:=dom f]>(forest_fold f).
  Definition forest_insert f ρ t : forest V := <[ρ:=t]>f.
  Definition tree_singleton ρ : tree V := {[ρ:=∅]}.
  Definition tree_insert t r (rt : tree V) π (πC : gset _) : tree V := <[π:={[r]} ∪ πC]>(rt ∪ t).

  Definition tree_split ρ (Cf : forest V) : forest V := forest_insert Cf ρ (tree_singleton ρ).
  Definition tree_clear f ρ Cf : forest V := forest_union (delete ρ f) (tree_split ρ Cf).
  Definition forest_move_tree f ρ ρt r rt π πC : forest V := forest_insert (delete ρ (delete r f)) ρ (tree_insert ρt r rt π πC).

  (** Well-formedness *)
  Inductive tree_wf : V → tree V → Prop :=
  | tree_wf_children ρ t (Cf : forest V) :
    t = forest_merge ρ Cf →
    (* root t ρ → *)
    forest_fold Cf !! ρ = None →
    forest_trees_disjoint Cf →
    map_Forall (λ c ct, tree_wf c ct) Cf →
    tree_wf ρ t.

  Definition forest_wf : forest V → Prop :=
    λ f, forest_trees_disjoint f ∧ map_Forall (λ ρ t, tree_wf ρ t) f.

  (** Properties *)
  Lemma root_not_internal t v :
    root t v ↔ ¬ internal t v.
  Proof using. rewrite /root /internal /child /children. firstorder. Qed.
  Lemma internal_not_root t v :
    internal t v ↔ ¬ root t v.
  Proof using.
    split; intros.
    - intros F. apply root_not_internal in F. done.
    - destruct (decide (internal t v)); auto. by apply root_not_internal in n.
  Qed.

  Lemma children_unique t π C1 C2 : children t π C1 → children t π C2 → C1 = C2.
  Proof using. unfold children. intros. rewrite H0 in H1. inv H1. done. Qed.

  Lemma children_child t π v C :
    children t π C → (v ∈ C ↔ child t π v).
  Proof using.
    intros. split; intros.
    - exists C. done.
    - destruct H1 as (?&?&?). pose proof (children_unique _ _ _ _ H0 H1). by subst.
  Qed.

  Lemma forest_fold_keeps_children t π C Cf r :
    children t π C → Cf !! r = Some t → forest_trees_disjoint Cf →
    children (forest_fold Cf) π C.
  Proof using.
    rewrite /children. revert t π C r. induction Cf using map_ind; intros.
    { by rewrite lookup_empty in H1. }
    rewrite forest_fold_insert_L; auto. 
    destruct (decide (r = i)).
    { subst. rewrite lookup_insert_eq in H2. inv H2. by apply lookup_union_Some_l. }
    rewrite lookup_insert_ne in H2; last auto.
    apply forest_trees_disjoint_insert in H3; last auto. destruct H3.
    pose proof (map_Forall_lookup_1 _ _ _ _ H3 H2). eapply map_disjoint_Some_l in H5; eauto.
    rewrite lookup_union_r; eauto.
  Qed.
  Lemma forest_fold_keeps_child t π v Cf r :
    child t π v → Cf !! r = Some t → forest_trees_disjoint Cf →
    child (forest_fold Cf) π v.
  Proof using.
    rewrite /child. intros. destruct H0 as (?&?&?).
    pose proof (forest_fold_keeps_children _ _ _ _ _ H0 H1 H2). eauto.
  Qed.
  Lemma forest_fold_keeps_internal t v Cf r :
    internal t v → Cf !! r = Some t → forest_trees_disjoint Cf →
    internal (forest_fold Cf) v.
  Proof using.
    rewrite /internal. intros. destruct H0 as (?&?).
    pose proof (forest_fold_keeps_child _ _ _ _ _ H0 H1 H2). eauto.
  Qed.

  Lemma forest_merge_keeps_children t π C Cf r ρ D :
    children t π C → Cf !! r = Some t → forest_trees_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    children (<[ρ:=D]>(forest_fold Cf)) π C.
  Proof using.
    intros. pose proof (forest_fold_keeps_children _ _ _ _ _ H0 H1 H2).
    unfold children in H4. unfold children. rewrite lookup_insert_ne; first eauto.
    intro F. subst. rewrite H3 in H4. done.
  Qed.
  Lemma forest_merge_keeps_child t π v Cf r ρ D :
    child t π v → Cf !! r = Some t → forest_trees_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    child (<[ρ:=D]>(forest_fold Cf)) π v.
  Proof using.
    rewrite /child. intros. destruct H0 as (?&?&?).
    pose proof (forest_merge_keeps_children _ _ _ _ _ _ D H0 H1 H2 H3). eauto.
  Qed.
  Lemma forest_merge_keeps_internal t v Cf r ρ D :
    internal t v → Cf !! r = Some t → forest_trees_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    internal (<[ρ:=D]>(forest_fold Cf)) v.
  Proof using.
    rewrite /internal. intros. destruct H0 as (?&?).
    pose proof (forest_merge_keeps_child _ _ _ _ _ _ D H0 H1 H2 H3). eauto.
  Qed.

  Lemma tree_wf_not_root_internal t ρ v :
    tree_wf ρ t → node t v → v ≠ ρ → internal t v.
  Proof using.
    intros Ht. revert v. induction Ht; intros. subst.
    assert (v ∈ dom (forest_fold Cf)).
    { apply elem_of_dom in H5. rewrite dom_insert_L in H5. apply elem_of_union in H5. destruct H5; set_solver. }
    (* FIXME: Error: Cannot infer an instance of type "tree V" for the variable t in context *)
    (* destruct (decide (v ∈ (dom Cf))). *)
    destruct (decide (v ∈ (dom Cf : gset V))).
    - pose proof e as ?. apply elem_of_dom in e. destruct e. exists ρ, (dom Cf). split; auto.
      by rewrite /children lookup_insert_eq.
    - pose proof (forest_fold_internal_elem_of _ _ H0 n). destruct H7 as (?&?&?&?).
      assert (v ≠ x).
      { intros ->. apply not_elem_of_dom in n. by rewrite n in H7. }
      apply elem_of_dom in H8. specialize (H4 _ _ H7 _ H8 H9). eapply forest_merge_keeps_internal; eauto.
  Qed.

  Lemma tree_wf_root_elem t ρ : tree_wf ρ t → ρ ∈ dom t.
  Proof using. intros. inv H0. rewrite dom_insert. set_solver. Qed.

  Lemma forest_merge_not_child_of_root ρ f v :
    node (forest_merge ρ f) v → v ∉ dom f → v ≠ ρ → ∃ c ct, f !! c = Some ct ∧ node ct v.
  Proof using.
    intros ?. apply elem_of_dom in H0. revert H0. unfold forest_merge. rewrite dom_insert.
    intros. apply elem_of_union in H0. destruct H0; first set_solver.
    pose proof (forest_fold_internal_elem_of _ _ H0 H1). destruct H3 as (?&?&?&?).
    do 2 eexists; split; eauto. by apply elem_of_dom.
  Qed.

  Lemma forest_merge_dom_forest_subseteq ρ f :
    forest_trees_disjoint f → map_Forall (λ c t, c ∈ dom t) f → dom f ⊆ dom (forest_merge ρ f).
  Proof using.
    intros. unfold forest_merge. rewrite dom_insert.
    pose proof (forest_fold_dom_forest_subseteq _ H0 H1). set_solver.
  Qed.

  Lemma forest_merge_children_of_child ρ f C v t :
    forest_trees_disjoint f → children (forest_merge ρ f) v C → v ≠ ρ → f !! v = Some t → v ∈ dom t →
    children t v C.
  Proof using.
    unfold forest_merge, children. intros. rewrite lookup_insert_ne in H1; auto.
    eapply forest_fold_lookup_child_tree; eauto.
  Qed.

  Definition descendant t : relation V := tc (child t).
  Definition lineage t : relation V := rtc (child t).

  Lemma lineage_eq_or_descendant t v u :
    lineage t v u → (v = u ∨ descendant t v u).
  Proof using.
    intros Ht. induction Ht; auto. destruct IHHt.
    - subst. right. econstructor 1; eauto.
    - right. econstructor 2; eauto.
  Qed.
  Lemma descendant_lineage t v u :
    descendant t v u → lineage t v u.
  Proof using.
    intros Ht. induction Ht.
    - econstructor 2; eauto. econstructor 1.
    - econstructor 2; eauto.
  Qed.

  Global Instance children_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) children.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. unfold children. intros. eapply lookup_weaken; eauto.
  Qed.
  Global Instance child_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) child.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. intros (?&?&?). exists x. split; auto.
    eapply children_tree_subseteq_Proper; eauto.
  Qed.
  Global Instance internal_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (→)) internal.
  Proof using.
    intros t1 t2 Hs ? v ? ?. subst. destruct H1 as (?&?).
    unfold internal. exists x. eapply child_tree_subseteq_Proper; eauto.
  Qed.
  Global Instance descendant_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) descendant.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. intro Hd. revert t2 Hs. induction Hd; intros.
    { econstructor 1. destruct H0 as (?&?&?). exists x0. split; auto. eapply children_tree_subseteq_Proper; eauto. }
    econstructor 2.
    - eapply child_tree_subseteq_Proper; eauto.
    - by eapply IHHd.
  Qed.
  Global Instance lineage_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) lineage.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. intro Hd. revert t2 Hs. induction Hd; intros.
    { econstructor 1. }
    econstructor 2.
    - eapply child_tree_subseteq_Proper; eauto.
    - by eapply IHHd.
  Qed.

  Lemma descendant_r t ρ v u : descendant t ρ v → child t v u → descendant t ρ u.
  Proof using. intros. eapply tc_r; eauto. Qed.

  Lemma lineage_r t ρ v u : lineage t ρ v → child t v u → lineage t ρ u.
  Proof using. intros. eapply rtc_r; eauto. Qed.

  Lemma forest_merge_subseteq ρ f c t :
    forest_fold f !! ρ = None → forest_trees_disjoint f → f !! c = Some t → t ⊆ forest_merge ρ f.
  Proof using.
    unfold forest_merge. etransitivity.
    2:{ eapply insert_subseteq. auto. }
    unfold forest_fold, forest_to_trees.
    eapply forest_fold_subseteq; eauto.
  Qed.

  Lemma tree_wf_node_descendant t ρ v :
    tree_wf ρ t → node t v → v ≠ ρ → descendant t ρ v.
  Proof using.
    intro Ht. revert v. induction Ht; intros. destruct (Cf !! v) eqn:Hv.
    - econstructor 1. exists (dom Cf). split.
      + subst. apply lookup_insert_eq.
      + by apply elem_of_dom.
    - assert (v ∈ dom (forest_fold Cf)).
      { subst. destruct H5. unfold forest_merge in H0.
        rewrite lookup_insert_ne in H0; last auto. by apply elem_of_dom. }
      assert (v ∉ dom Cf) by (by apply not_elem_of_dom).
      pose proof (forest_fold_internal_elem_of _ _ H7 H8). destruct H9 as (?&?&?&?).
      assert (node x0 v) by (by apply elem_of_dom).
      assert (v ≠ x).
      { intros F; subst. by rewrite Hv in H9. }
      specialize (H4 _ _ H9 _ H11 H12). eapply (tc_l _ _ x).
      { subst. exists (dom Cf). unfold children, forest_merge.
        split; last by eapply elem_of_dom. by rewrite lookup_insert_eq. }
      eapply descendant_tree_subseteq_Proper; last eapply H4; auto.
      subst. eapply forest_merge_subseteq; eauto.
  Qed.

  Lemma children_wf_subtree t s v C :
    children t v C → node s v → s ⊆ t → children s v C.
  Proof using.
    unfold children. intros. destruct H1.
    pose proof (lookup_weaken _ _ _ _ H1 H2). rewrite H3 in H0. inv H0. done.
  Qed.
  Lemma child_wf_subtree t s v u :
    child t v u → node s v → s ⊆ t → child s v u.
  Proof using.
    unfold child. intros. destruct H0 as (?&?&?).
    exists x. split; last auto. eapply children_wf_subtree; eauto.
  Qed.
  Lemma descendant_wf_subtree t s v u :
    descendant t v u → tree_wf v s → s ⊆ t → descendant s v u.
  Proof using.
    intros. revert t u H0 H2. induction H1.
    intros g u Hd Hsub. inv Hd.
    { econstructor 1. eapply child_wf_subtree; eauto. apply elem_of_dom, tree_wf_root_elem.
      econstructor; eauto.
    }
    rename y into π. econstructor 2.
    { eapply child_wf_subtree; first eapply H5; auto. by rewrite /node /forest_merge lookup_insert_eq. }
    assert (child (forest_merge ρ Cf) ρ π).
    { eapply child_wf_subtree; eauto. by rewrite /node /forest_merge lookup_insert_eq. }
    assert (is_Some (Cf !! π)).
    { destruct H0 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0. inv H0.
      apply elem_of_dom; auto. }
    destruct H7. specialize (H4 _ _ H7 _ _ H6).
    assert (x ⊆ (forest_merge ρ Cf)).
    { eapply forest_merge_subseteq; eauto. }
    eapply descendant_tree_subseteq_Proper; last eapply H4; auto.
    etransitivity; eauto.
  Qed.

  Inductive descendant_alt : tree V → relation V :=
  | descendant_alt_child t ρ v :
    child t ρ v →
    descendant_alt t ρ v
  | descendant_alt_far t ρ s π v :
    child t ρ π →
    s ⊆ t →
    tree_wf π s →
    descendant_alt s π v →
    descendant_alt t ρ v.

  Lemma descendant_descendant_alt t ρ v :
    tree_wf ρ t → descendant t ρ v → descendant_alt t ρ v.
  Proof using.
    intros. revert v H1. induction H0; intros.
    inv H5.
    { by econstructor 1. }
    rename y into π. 
    assert (is_Some (Cf !! π)).
    { destruct H6 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0. inv H0.
      apply elem_of_dom; auto. }
    destruct H0. specialize (H4 _ _ H0).
    assert (x ⊆ forest_merge ρ Cf).
    { eapply forest_merge_subseteq; eauto. }
    assert (descendant x π v).
    { eapply descendant_wf_subtree; first eapply H7; eauto. }
    specialize (H4 _ H8). econstructor 2; last eapply H4; eauto.
  Qed.

  Lemma descendant_alt_descendant t ρ v :
    tree_wf ρ t → descendant_alt t ρ v → descendant t ρ v.
  Proof using.
    intros. revert H0. induction H1; intros.
    { by econstructor 1. }
    assert (Hd : descendant s π v) by eauto. clear IHdescendant_alt.
    econstructor 2; first eauto.
    eapply descendant_tree_subseteq_Proper; last eauto; auto.
  Qed.

  Lemma node_weaken t1 t2 v :
    node t1 v → t1 ⊆ t2 → node t2 v.
  Proof using. rewrite /node. intros. eapply lookup_weaken_is_Some; eauto. Qed.

  Lemma descendant_alt_node t ρ v :
    tree_wf ρ t → descendant_alt t ρ v → node t v.
  Proof using.
    intros. eapply descendant_alt_descendant in H1; auto.
    revert v H1. induction H0; intros. induction H5.
    { subst. destruct H5 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0. inv H0.
      apply elem_of_dom. eapply elem_of_weaken; first eauto.
      eapply forest_merge_dom_forest_subseteq; eauto.
      eapply map_Forall_impl; first eapply H3. intros. by apply tree_wf_root_elem in H0. }
    rename x into ρ, y into π, z into v. clear IHtc. subst.
    assert (is_Some (Cf !! π)).
    { destruct H5 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0.
      inv H0. by apply elem_of_dom. }
    destruct H0. specialize (H4 _ _ H0).
    assert (x ⊆ forest_merge ρ Cf).
    { eapply forest_merge_subseteq; eauto. }
    assert (descendant x π v).
    { eapply descendant_wf_subtree; eauto. }
    specialize (H4 _ H8). eapply node_weaken; eauto.
  Qed.

  Lemma tree_wf_root_child_children_subseteq t ρ v C :
    tree_wf ρ t → child t ρ v → children t v C → C ⊆ dom t.
  Proof using.
    intros. inv H0. assert (v ≠ ρ).
    { intros F; subst. destruct H1 as (?&?&?). rewrite /children lookup_insert_eq in H0. inv H0.
      assert (dom Cf ⊆ dom (forest_fold Cf)).
      { eapply forest_fold_dom_forest_subseteq; eauto. eapply map_Forall_impl; eauto. intros.
        eapply tree_wf_root_elem; eauto. }
      assert (ρ ∈ dom (forest_fold Cf)) by set_solver.
      apply not_elem_of_dom in H4. done. }
    assert (is_Some (Cf !! v)).
    { destruct H1 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H1.
      inv H1. by apply elem_of_dom. }
    destruct H3. rename x into s. assert (tree_wf v s) by eauto.
    assert (v ∈ dom s).
    { apply tree_wf_root_elem; eauto. }
    pose proof (forest_merge_children_of_child _ _ _ _ _ H5 H2 H0 H3 H8).
    etransitivity; first instantiate (1:=dom s).
    - inv H7. assert (C = dom Cf0).
      { rewrite /children /forest_merge lookup_insert_eq in H9. by inv H9. }
      subst C. eapply forest_merge_dom_forest_subseteq; eauto.
      eapply map_Forall_impl; eauto. simpl; intros. apply tree_wf_root_elem; auto.
    - apply subseteq_dom. eapply forest_merge_subseteq; eauto.
  Qed.

  Lemma tree_wf_children_subseteq t ρ v C :
    tree_wf ρ t → children t v C → C ⊆ dom t.
  Proof using.
    intros. destruct (decide (v = ρ)).
    - inv H0. rewrite /children /forest_merge lookup_insert_eq in H1. inv H1.
      eapply forest_merge_dom_forest_subseteq; eauto. eapply map_Forall_impl; first eauto.
      intros. by apply tree_wf_root_elem in H0.
    - assert (node t v).
      { inv H0. rewrite /node. eauto. }
      assert (descendant_alt t ρ v).
      { apply descendant_descendant_alt; auto. eapply tree_wf_node_descendant; eauto. }
      clear n H2. generalize dependent C. revert H0. induction H3; intros.
      + eapply tree_wf_root_child_children_subseteq; eauto.
      + assert (children s v C).
        { eapply children_wf_subtree; eauto. eapply descendant_alt_node; eauto. }
        specialize (IHdescendant_alt H2 _ H6). etrans; first eauto.
        eapply subseteq_dom; eauto.
  Qed.

  Lemma tree_wf_internal_node t ρ v : tree_wf ρ t → internal t v → node t v.
  Proof using.
    intros Ht Hi.
    destruct Hi as (?&C&?&?). pose proof (tree_wf_children_subseteq _ _ _ _ Ht H0).
    apply elem_of_dom. set_solver.
  Qed.

  Lemma tree_wf_descendant_node t ρ v :
    tree_wf ρ t → descendant t ρ v → node t v.
  Proof using.
    intros. apply descendant_descendant_alt in H1; auto. revert H0. induction H1; intros.
    - inv H1. apply elem_of_dom. eapply elem_of_weaken.
      2:{ eapply forest_merge_dom_forest_subseteq; eauto. eapply map_Forall_impl; eauto.
          intros. apply tree_wf_root_elem; auto. }
      destruct H0 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0. by inv H0.
    - apply IHdescendant_alt in H2. eapply node_weaken; eauto.
  Qed.

  Lemma not_node_not_descendant t ρ v :
    tree_wf ρ t → (t !! v = None) → ¬ descendant t ρ v.
  Proof using.
    intros. intro Hd. pose proof (tree_wf_descendant_node _ _ _ H0 Hd). by rewrite /node H1 in H2.
  Qed.

  Lemma tree_wf_tree_unique t t1 t2 r :
    t1 ⊆ t → t2 ⊆ t → tree_wf r t1 → tree_wf r t2 → t1 = t2.
  Proof using.
    intros. apply map_eq. intros. destruct (t1 !! i) eqn:Ht1, (t2 !! i) eqn:Ht2; auto.
    - eapply lookup_weaken in Ht1; eauto. eapply lookup_weaken in Ht2; eauto.
      rewrite Ht1 in Ht2. inv Ht2. done.
    - destruct (decide (i = r)).
      { subst i. exfalso. apply tree_wf_root_elem, elem_of_dom in H3. by rewrite Ht2 in H3. }
      assert (node t1 i) by (unfold node; eauto).
      pose proof (tree_wf_node_descendant _ _ _ H2 H4 n).
      pose proof (not_node_not_descendant _ _ _ H3 Ht2).
      eapply descendant_tree_subseteq_Proper in H5; eauto.
      assert (¬ descendant t r i).
      { intros F. apply H6. eapply descendant_wf_subtree; eauto. }
      done.
    - destruct (decide (i = r)).
      { subst i. exfalso. apply tree_wf_root_elem, elem_of_dom in H2. by rewrite Ht1 in H2. }
      assert (node t2 i) by (unfold node; eauto).
      pose proof (tree_wf_node_descendant _ _ _ H3 H4 n).
      pose proof (not_node_not_descendant _ _ _ H2 Ht1).
      eapply descendant_tree_subseteq_Proper in H5; eauto.
      assert (¬ descendant t r i).
      { intros F. apply H6. eapply descendant_wf_subtree; eauto. }
      done.
  Qed.

  Inductive tree_wf_clo : V → tree V → Prop :=
  | tree_wf_clo_internal ρ t :
    (∀ v s, internal t v → s ⊆ t → tree_wf v s → tree_wf_clo v s) →
    tree_wf_clo ρ t.

  Lemma tree_wf_clo_subtree t ρ s r :
    tree_wf_clo ρ t → s ⊆ t → tree_wf_clo r s.
  Proof using.
    intros. revert r. generalize dependent s. induction H0; intros.
    econstructor. intros u x. intros. eapply H0; eauto.
    - eapply internal_tree_subseteq_Proper; eauto.
    - etrans; eauto.
  Qed.

  Lemma tree_wf_node_subtree t x s r v :
    tree_wf r x → tree_wf v s → node x v → x ⊆ t → s ⊆ t → s ⊆ x.
  Proof using.
    intros Ht. revert t s v. induction Ht; intros.
    assert (tree_wf ρ t) by (by econstructor). destruct (decide (v = ρ)).
    { subst v. pose proof (tree_wf_tree_unique _ _ _ _ H7 H8 H9 H5). by subst. }
    pose proof n. eapply tree_wf_not_root_internal in n; eauto.
    destruct (Cf !! v) eqn:Hv.
    - assert (tree_wf v g) by eauto. assert (g ⊆ t0).
      { etrans; last eapply H7. subst. eapply forest_merge_subseteq; eauto. }
      pose proof (tree_wf_tree_unique _ _ _ _ H8 H12 H5 H11). subst g.
      subst t. eapply forest_merge_subseteq; eauto.
    - assert (v ∉ dom Cf) by (by apply not_elem_of_dom). subst.
      pose proof (forest_merge_not_child_of_root _ _ _ H6 H11 H10). destruct H0 as (?&?&?&?).
      rename x into π, x0 into x.
      assert (x ⊆ forest_merge ρ Cf) by (by eapply forest_merge_subseteq).
      assert (x ⊆ t0).
      { etrans; last eapply H7; auto. }
      specialize (H4 _ _ H0 t0 _ _ H5 H12 H14 H8).
      etrans; first eapply H4; auto.
  Qed.

  Lemma tree_wf_root_root t ρ : tree_wf ρ t → root t ρ.
  Proof using.
    intros. destruct (decide (root t ρ)); auto.
    exfalso. inv H0.
    apply internal_not_root in n. destruct n as (?&?&?&?). rename x into v, x0 into C.
    destruct (decide (v = ρ)).
    - subst v. rewrite /children lookup_insert_eq in H0. inv H0.
      assert (dom Cf ⊆ dom (forest_fold Cf)).
      { eapply forest_fold_dom_forest_subseteq; eauto. eapply map_Forall_impl; eauto. intros.
        eapply tree_wf_root_elem; eauto. }
      assert (ρ ∈ dom (forest_fold Cf)) by set_solver.
      apply not_elem_of_dom in H2. done.
    - assert (forest_fold Cf !! v = Some C).
      { rewrite /children lookup_insert_ne in H0; auto. }
      pose proof (forest_fold_lookup_Some_exists_root _ _ _ H3 H5).
      destruct H6 as (?&?&?&?). rename x into π, x0 into s.
      assert (tree_wf π s) by (eauto).
      assert (s ⊆ forest_merge ρ Cf) by (by eapply forest_merge_subseteq).
      eapply children_wf_subtree in H0; eauto.
      2:{ by unfold node. }
      pose proof (tree_wf_children_subseteq _ _ _ _ H8 H0).
      assert (s ⊆ forest_fold Cf) by (by eapply forest_fold_subseteq).
      assert (is_Some (forest_fold Cf !! ρ)).
      { apply elem_of_dom. eapply elem_of_weaken; first eauto. etrans; eauto. by apply subseteq_dom. }
      rewrite H2 in H12. done.
  Qed.

  Lemma tree_wf_root_unique t ρ1 ρ2 : tree_wf ρ1 t → tree_wf ρ2 t → ρ1 = ρ2.
  Proof using.
    intros.
    assert (root t ρ1) as Hr1 by (by apply tree_wf_root_root).
    assert (root t ρ2) as Hr2 by (by apply tree_wf_root_root).
    pose proof H0 as Htwf. inv H0. destruct (decide (ρ1 = ρ2)); first auto. exfalso.
    pose proof (tree_wf_not_root_internal _ _ ρ1 H1).
    eapply root_not_internal in Hr1. apply Hr1. apply H0; auto.
    apply elem_of_dom, tree_wf_root_elem. auto.
  Qed.

  Lemma tree_wf_internal_not_root t ρ v : tree_wf ρ t → internal t v → v ≠ ρ.
  Proof using.
    intros. intros F; subst. apply internal_not_root in H1. apply H1.
    apply tree_wf_root_root; auto.
  Qed.

  Lemma tree_wf_root_internal_descendant t ρ v :
    tree_wf ρ t → internal t v → descendant t ρ v.
  Proof using.
    intros. eapply tree_wf_node_descendant; eauto.
    - eapply tree_wf_internal_node; eauto.
    - eapply tree_wf_internal_not_root; eauto.
  Qed.

  Lemma tree_wf_node_root_or_internal t ρ v :
    tree_wf ρ t → node t v → (root t v ∨ internal t v).
  Proof using.
    intros. apply elem_of_dom in H1. destruct (decide (v = ρ)).
    - subst. left. apply tree_wf_root_root; auto.
    - right. apply elem_of_dom in H1. eapply tree_wf_not_root_internal; eauto.
  Qed.

  Lemma tree_wf_root_node t ρ :
    tree_wf ρ t → node t ρ.
  Proof using. intros. apply elem_of_dom. by eapply tree_wf_root_elem. Qed.

  Lemma tree_wf_tree_wf_clo t ρ :
    tree_wf ρ t → tree_wf_clo ρ t.
  Proof using.
    intros. induction H0. econstructor. intros.
    destruct (Cf !! v) eqn:HV.
    - assert (tree_wf v g) by eauto. assert (g ⊆ t).
      { subst. eapply forest_merge_subseteq; eauto. }
      pose proof (tree_wf_tree_unique _ _ _ _ H6 H9 H7 H8). subst g. eauto.
    - assert (v ∉ dom Cf) by (by apply not_elem_of_dom).
      assert (v ≠ ρ).
      { eapply tree_wf_internal_not_root; eauto. econstructor; eauto. }
      assert (node t v).
      { eapply tree_wf_internal_node; eauto. econstructor; eauto. }
      subst. pose proof (forest_merge_not_child_of_root _ _ _ H10 H8 H9). destruct H0 as (?&?&?&?).
      specialize (H4 _ _ H0). eapply tree_wf_clo_subtree; first eauto.
      assert (tree_wf x x0) by eauto.
      eapply (tree_wf_node_subtree (forest_merge ρ Cf) x0 s); eauto.
      eapply forest_merge_subseteq; eauto.
  Qed.

  Lemma tree_wf_internal_ind (P : V → tree V → Prop) :
    (∀ ρ t,
       tree_wf ρ t →
       (∀ v s, internal t v → s ⊆ t → tree_wf v s → P v s) →
       P ρ t)
    → ∀ ρ (t : tree V), tree_wf ρ t → P ρ t.
  Proof using.
    intros Hind. intros. pose proof (tree_wf_tree_wf_clo _ _ H0). induction H1; eauto.
  Qed.

  Lemma tree_wf_root_node_root ρ t v :
    tree_wf ρ t → root t v → node t v → v = ρ.
  Proof using.
    intros. destruct (decide (v = ρ)); auto.
    pose proof (tree_wf_not_root_internal _ _ _ H0 H2 n). apply internal_not_root in H3. done.
  Qed.

  Lemma tree_wf_node_exists_tree ρ t v :
    tree_wf ρ t → node t v → ∃ s, s ⊆ t ∧ tree_wf v s.
  Proof using.
    intros ?. revert v. induction H0 using tree_wf_internal_ind. intros.
    destruct (tree_wf_node_root_or_internal _ _ _ H0 H2).
    { eapply tree_wf_root_node_root in H3; eauto. subst v. eauto. }
    clear H2. induction H0. destruct (Cf !! v) eqn:Hv.
    - exists g. split; eauto. subst t. eapply forest_merge_subseteq; eauto.
    - assert (tree_wf ρ t) by (by econstructor).
      assert (node t v) by (by eapply tree_wf_internal_node).
      assert (v ∉ dom Cf) by (by eapply not_elem_of_dom).
      assert (v ≠ ρ) by (by eapply tree_wf_internal_not_root).
      subst t. pose proof (forest_merge_not_child_of_root _ _ _ H8 H9 H10). destruct H0 as (?&?&?&?).
      rename x into π, x0 into ct.
      assert (ct ⊆ forest_merge ρ Cf) by (by eapply forest_merge_subseteq).
      assert (internal (forest_merge ρ Cf) π).
      { exists ρ, (dom Cf). split; [by rewrite /children /forest_merge lookup_insert_eq | by eapply elem_of_dom]. }
      assert (tree_wf π ct) by eauto.
      specialize (H1 _ _ H13 H12 H14 _ H11). destruct H1 as (?&?&?). exists x. split; auto.
      etrans; eauto.
  Qed.

  Lemma forest_fold_not_in_forest_not_in f ρ :
    forest_wf f → forest_fold f !! ρ = None → f !! ρ = None.
  Proof using.
    intros. destruct H0. destruct (f !! ρ) eqn:Hlu; auto.
    exfalso. pose proof (forest_fold_subseteq _ _ _ H0 Hlu).
    assert (ρ ∈ dom g).
    { apply tree_wf_root_elem; eauto. }
    apply subseteq_dom in H3. apply not_elem_of_dom in H1. set_solver.
  Qed.

  Lemma forest_merge_internal_forest_fold_node ρ f v :
    tree_wf ρ (forest_merge ρ f) → internal (forest_merge ρ f) v → node (forest_fold f) v.
  Proof using.
    unfold node. intros. pose proof (tree_wf_internal_node _ _ _ H0 H1).
    pose proof (tree_wf_internal_not_root _ _ _ H0 H1).
    destruct H2. rewrite /forest_merge lookup_insert_ne in H2; eauto.
  Qed.

  Lemma forest_fold_node_forest_merge_internal ρ f v :
    forest_fold f !! ρ = None →
    forest_trees_disjoint f →
    map_Forall (λ (c : V) (ct : tree V), tree_wf c ct) f →
    node (forest_fold f) v → internal (forest_merge ρ f) v.
  Proof using.
    intros. eapply tree_wf_not_root_internal; eauto.
    - by econstructor.
    - apply elem_of_dom. apply elem_of_dom in H3. rewrite /forest_merge dom_insert_L. set_solver.
    - intros F; subst. unfold node in H3. by rewrite H0 in H3.
  Qed.

  Global Instance tree_wf_child_Irreflexive t ρ : tree_wf ρ t → Irreflexive (child t).
  Proof using.
    intros ???. destruct H1 as (?&?&?). assert (node t x) by (by exists x0).
    pose proof (tree_wf_node_exists_tree _ _ _ H0 H3). destruct H4 as (?&?&?).
    assert (children x1 x x0).
    { eapply children_wf_subtree; eauto. by apply elem_of_dom, tree_wf_root_elem. }
    clear dependent t. clear ρ. rename x1 into t, x0 into C, x into ρ.
    inv H5. rewrite /children /forest_merge lookup_insert_eq in H6. inv H6.
    apply forest_fold_not_in_forest_not_in in H1; last split; auto.
    apply not_elem_of_dom in H1. done.
  Qed.

  Lemma forest_fold_children_subseteq_forest_fold f v C :
    forest_trees_disjoint f →
    map_Forall (λ c ct, tree_wf c ct) f →
    forest_fold f !! v = Some C →
    C ⊆ dom (forest_fold f).
  Proof using.
    intros. pose proof (forest_fold_lookup_Some_exists_root _ _ _ H0 H2). destruct H3 as (?&?&?&?).
    pose proof (forest_fold_subseteq _ _ _ H0 H3). assert (tree_wf x x0) by eauto.
    pose proof (tree_wf_children_subseteq _ _ _ _ H6 H4).
    apply subseteq_dom in H5. set_solver.
  Qed.

  Global Instance tree_wf_child_Asymmetric t ρ : tree_wf ρ t → Asymmetric (child t).
  Proof using.
    intros ? a b ??. destruct (decide (a = b)).
    { subst. eapply tree_wf_child_Irreflexive in H1; eauto. }
    destruct H1 as (C1&?&?). assert (node t a) by (by eexists).
    pose proof (tree_wf_node_exists_tree _ _ _ H0 H4). destruct H5 as (s1&?&?).
    assert (children s1 a C1).
    { eapply children_wf_subtree; eauto. by apply elem_of_dom, tree_wf_root_elem. }
    destruct H2 as (C2&?&?). assert (is_Some (s1 !! b)).
    { assert (C1 ⊆ dom s1).
      { eapply tree_wf_children_subseteq; eauto. }
      apply elem_of_dom. set_solver. }
    destruct H9. assert (t !! b = Some x).
    { eapply map_subseteq_spec; eauto. }
    rewrite H2 in H10. inv H10. rename x into C2.
    inv H6. rewrite /forest_merge lookup_insert_ne in H9; auto.
    pose proof (forest_fold_children_subseteq_forest_fold _ _ _ H12 H13 H9).
    apply not_elem_of_dom in H11. set_solver.
  Qed.

  Lemma descendant_start_node t v u : descendant t v u → node t v.
  Proof using.
    intros Hd; inv Hd.
    - destruct H0 as (?&?&?). exists x; auto.
    - destruct H0 as (?&?&?). exists x; auto.
  Qed.

  Definition ancestor t : relation V := tc (parent t).
  Definition lineage_up t : relation V := rtc (parent t).

  Lemma lineage_up_eq_or_ancestor t v u :
    lineage_up t v u → (v = u ∨ ancestor t v u).
  Proof using.
    intros Ht. induction Ht; auto. destruct IHHt.
    - subst. right. econstructor 1; eauto.
    - right. econstructor 2; eauto.
  Qed.
  Lemma ancestor_lineage_up t v u :
    ancestor t v u → lineage_up t v u.
  Proof using.
    intros Ht. induction Ht.
    - econstructor 2; eauto. econstructor 1.
    - econstructor 2; eauto.
  Qed.

  Lemma descendant_ancestor t v u :
    descendant t v u → ancestor t u v.
  Proof using.
    intros. apply tc_list in H0. destruct H0 as (?&?&?&?&?).
    apply tc_list. exists (reverse x). split_and !.
    - by rewrite length_reverse.
    - by rewrite head_reverse.
    - by rewrite last_reverse.
    - intros.
      pose proof H4. apply reverse_lookup_Some in H6. pose proof H5. apply reverse_lookup_Some in H7.
      destruct H6, H7. assert (length x - S i = S (length x - S (S i))) by lia.
      rewrite H10 in H6. specialize (H3 _ _ _ H7 H6). done.
  Qed.
  Lemma ancestor_descendant t v u :
    ancestor t v u → descendant t u v.
  Proof using.
    intros. apply tc_list in H0. destruct H0 as (?&?&?&?&?).
    apply tc_list. exists (reverse x). split_and !.
    - by rewrite length_reverse.
    - by rewrite head_reverse.
    - by rewrite last_reverse.
    - intros.
      pose proof H4. apply reverse_lookup_Some in H6. pose proof H5. apply reverse_lookup_Some in H7.
      destruct H6, H7. assert (length x - S i = S (length x - S (S i))) by lia.
      rewrite H10 in H6. specialize (H3 _ _ _ H7 H6). done.
  Qed.

  Lemma lineage_lineage_up t v u :
    lineage t v u → lineage_up t u v.
  Proof using.
    intros. apply lineage_eq_or_descendant in H0. destruct H0.
    - subst. done.
    - apply ancestor_lineage_up, descendant_ancestor; auto.
  Qed.
  Lemma lineage_up_lineage t v u :
    lineage_up t v u → lineage t u v.
  Proof using.
    intros. apply lineage_up_eq_or_ancestor in H0. destruct H0.
    - subst. done.
    - apply descendant_lineage, ancestor_descendant; auto.
  Qed.

  Lemma tree_wf_child_node t ρ v u :
    tree_wf ρ t → child t v u → (node t v ∧ node t u).
  Proof using.
    intros. assert (node t v).
    { destruct H1 as (?&?&?). by eexists. }
    split; auto.
    assert (descendant t v u) by (by econstructor 1).
    eapply tree_wf_descendant_node; eauto. destruct (decide (v = ρ)); first (subst; auto).
    assert (descendant t ρ v) by (eapply tree_wf_node_descendant; eauto).
    etrans; eauto.
  Qed.

  Lemma tree_wf_child_descendant_false t ρ x y :
    tree_wf ρ t → child t x y → ¬ descendant t y x.
  Proof using.
    intros. intros ?. destruct (tree_wf_child_node _ _ _ _ H0 H1).
    destruct (tree_wf_node_exists_tree _ _ _ H0 H3) as (s1&?&?).
    destruct (tree_wf_node_exists_tree _ _ _ H0 H4) as (s2&?&?).
    pose proof (descendant_wf_subtree _ _ _ _ H2 H8 H7).
    pose proof (tree_wf_descendant_node _ _ _ H8 H9).
    assert (child s1 x y).
    { eapply child_wf_subtree; eauto. by apply elem_of_dom, tree_wf_root_elem. }
    inv H6. destruct H11 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H6. inv H6.
    apply elem_of_dom in H11. destruct H11. assert (tree_wf y x0) by eauto.
    assert (x0 ⊆ t).
    { etransitivity; last eapply H5. eapply forest_merge_subseteq; eauto. }
    pose proof (tree_wf_tree_unique _ _ _ _ H7 H12 H8 H11). subst x0.
    assert (s2 ⊆ forest_fold Cf) by (eapply forest_fold_subseteq ; eauto).
    assert (x ∈ dom s2) by (eapply elem_of_dom; eauto).
    apply subseteq_dom in H16. apply not_elem_of_dom in H13. set_solver.
  Qed.

  Global Instance tree_wf_descendant_Asymmetric t ρ : tree_wf ρ t → Asymmetric (descendant t).
  Proof using.
    intros ? a b ??. revert ρ H0 H2. induction H1; intros.
    { apply (tree_wf_child_descendant_false _ _ _ _ H1 H0 H2). }
    { eapply IHtc; eauto. eapply descendant_r; eauto. }
  Qed.

  Global Instance tree_wf_descendant_Irreflexive t ρ : tree_wf ρ t → Irreflexive (descendant t).
  Proof using. intros Ht. intros ??. eapply tree_wf_descendant_Asymmetric; eauto. Qed.

  Lemma tree_wf_child_parent_unique_1 t ρ π2 v :
    π2 ≠ ρ →
    tree_wf ρ t → child t ρ v → child t π2 v → ρ = π2.
  Proof using.
    intros Hne. intros. inversion H0. subst ρ0 t0.
    assert (is_Some (Cf !! v)).
    { destruct H1 as (?&?&?). subst t. rewrite /children /forest_merge lookup_insert_eq in H1. inv H1. by apply elem_of_dom. }
    destruct H7. pose proof H2. destruct H8 as (C2&HC21&HC22).
    assert (HC23 : (forest_fold Cf) !! π2 = Some C2).
    { subst t. rewrite /children /forest_merge lookup_insert_ne in HC21; auto. }
    pose proof (forest_fold_lookup_Some_exists_root _ _ _ H5 HC23).
    destruct H8 as (c&ct&Hclu&Hctlu).
    assert (tree_wf c ct) by eauto.
    assert (node ct c) by (apply elem_of_dom, tree_wf_root_elem; auto).
    assert (ct ⊆ t) by (subst; eapply forest_merge_subseteq; eauto).
    assert (node ct π2) by (rewrite /node; eauto).
    assert (v ∈ dom ct).
    { pose proof (child_wf_subtree _ _ _ _ H2 H11 H10). destruct H12 as (?&?&?).
      pose proof (tree_wf_children_subseteq _ _ _ _ H8 H12). set_solver. }
    assert (tree_wf v x) by eauto. assert (v ∈ dom x) by (apply tree_wf_root_elem; auto).
    assert (Hcv : c ≠ v).
    { intros F; subst. destruct (decide (π2 = v)).
      { subst. eapply tree_wf_child_Irreflexive in H2; by eauto. }
      pose proof (tree_wf_node_descendant ct v π2 H8 H11 n).
      assert (descendant ct π2 v).
      { econstructor 1. eapply child_wf_subtree; first eapply H2; auto. }
      eapply (tree_wf_descendant_Asymmetric ct v); eauto. }
    assert (x ##ₘ ct).
    { eapply (forest_trees_disjoint_lookup_disjoint Cf v c); auto. }
    apply map_disjoint_dom in H15. set_solver.
  Qed.

  Lemma tree_wf_child_parent_unique t ρ π1 π2 v :
    tree_wf ρ t → child t π1 v → child t π2 v → π1 = π2.
  Proof using.
    intros. revert π1 π2 v H1 H2. induction H0; intros. assert (Htwf : tree_wf ρ t) by (by econstructor).
    destruct (decide (π1 = ρ)), (decide (π2 = ρ)); subst; auto.
    { eapply tree_wf_child_parent_unique_1; eauto. }
    { symmetry. eapply tree_wf_child_parent_unique_1; eauto. }
    pose proof H5. destruct H0 as (C1&HC11&HC12).
    assert (HC13 : (forest_fold Cf) !! π1 = Some C1).
    { rewrite /children /forest_merge lookup_insert_ne in HC11; auto. }
    pose proof (forest_fold_lookup_Some_exists_root _ _ _ H2 HC13). destruct H0 as (r1&rt1&Hr11&Hr12).
    pose proof H6. destruct H0 as (C2&HC21&HC22).
    assert (HC23 : (forest_fold Cf) !! π2 = Some C2).
    { rewrite /children /forest_merge lookup_insert_ne in HC21; auto. }
    pose proof (forest_fold_lookup_Some_exists_root _ _ _ H2 HC23). destruct H0 as (r2&rt2&Hr21&Hr22).
    destruct (decide (r1 = r2)).
    - subst r2. rewrite Hr11 in Hr21; inv Hr21.
      assert (child rt2 π1 v).
      { eapply child_wf_subtree; first eapply H5; eauto.
        - eexists; eauto.
        - eapply forest_merge_subseteq; eauto. }
      assert (child rt2 π2 v).
      { eapply child_wf_subtree; first eapply H6; eauto.
        - eexists; eauto.
        - eapply forest_merge_subseteq; eauto. }
      specialize (H4 _ _ Hr11 _ _ _ H0 H7). auto.
    - assert (Hdisj : rt1 ##ₘ rt2).
      { eapply forest_trees_disjoint_lookup_disjoint; first eapply H2; eauto. }
      assert (C1 ⊆ dom rt1).
      { eapply tree_wf_children_subseteq; eauto. }
      assert (C2 ⊆ dom rt2).
      { eapply tree_wf_children_subseteq; eauto. }
      apply map_disjoint_dom in Hdisj. set_solver + HC12 HC22 Hdisj H0 H7.
  Qed.

  Lemma tree_wf_node_lineage t ρ v :
    tree_wf ρ t → node t v → lineage t ρ v.
  Proof using.
    intros. destruct (decide (v = ρ)); first by subst.
    pose proof (tree_wf_node_descendant _ _ _ H0 H1 n). apply descendant_lineage; auto.
  Qed.

  Definition forest_node_in_tree_internal f : V → Prop := λ v, map_fold_or f (λ _ t, (internal t v)).

  Global Instance forest_node_in_tree_internal_Decision f : ∀ k, Decision (forest_node_in_tree_internal f k).
  Proof using. solve_decision. Qed.

  Lemma forest_fold_node_in_tree_root_or_internal f v :
    forest_trees_disjoint f →
    map_Forall (λ ρ t, tree_wf ρ t) f →
    node (forest_fold f) v ↔ ((v ∈ dom f) ∨ (forest_node_in_tree_internal f v)).
  Proof using.
    intros. rewrite /node forest_fold_node_in_tree; auto.
    rewrite /forest_node_in_tree /forest_node_in_tree_internal /map_fold_or.
    split; intros.
    - revert H0 H1 v H2. induction f using map_ind; intros.
      { by rewrite map_fold_empty in H2. }
      apply map_fold_or_insert in H3; auto.
      destruct H3.
      + destruct (decide (v = i)).
        * subst. left. rewrite dom_insert_L. set_solver.
        * right. apply map_fold_or_insert; auto.
          apply map_Forall_insert in H2; auto. destruct H2.
          destruct (tree_wf_node_root_or_internal _ _ _ H2 H3); auto.
          eapply tree_wf_root_node_root in H2; eauto. by subst.
      + apply forest_trees_disjoint_insert in H1; auto. destruct H1.
        apply map_Forall_insert in H2; auto. destruct H2.
        specialize (IHf H4 H5 _ H3). destruct IHf.
        * left. rewrite dom_insert_L. set_solver.
        * right. apply map_fold_or_insert; auto.
    - revert H0 H1 v H2. induction f using map_ind; intros.
      { destruct H2; done. }
      apply map_fold_or_insert; auto.
      apply forest_trees_disjoint_insert in H1; auto. destruct H1.
      apply map_Forall_insert in H2; auto. destruct H2. specialize (IHf H4 H5 v).
      destruct H3.
      + rewrite dom_insert_L in H3. apply elem_of_union in H3. destruct H3.
        * apply elem_of_singleton in H3. subst. left. apply tree_wf_root_node; auto.
        * right. apply IHf; auto.
      + apply map_fold_or_insert in H3; auto. destruct H3.
        * left. eapply tree_wf_internal_node; eauto.
        * right. apply IHf; auto.
  Qed.

  Lemma forest_merge_internal_forest_fold_node_iff ρ f v :
    tree_wf ρ (forest_merge ρ f) →
    forest_fold f !! ρ = None →
    forest_trees_disjoint f →
    map_Forall (λ ρ t, tree_wf ρ t) f →
    internal (forest_merge ρ f) v ↔ node (forest_fold f) v.
  Proof using.
    intros. split; intros.
    - eapply forest_merge_internal_forest_fold_node; eauto.
    - eapply forest_fold_node_forest_merge_internal; eauto.
  Qed.

  Lemma forest_node_in_tree_internal_insert f v k t :
    (f !! k = None) →
    forest_node_in_tree_internal (<[k:=t]>f) v ↔ ((internal t v) ∨ forest_node_in_tree_internal f v).
  Proof using.
    intros. unfold forest_node_in_tree_internal, map_fold_or. rewrite map_fold_or_insert; auto.
  Qed.

  (* Operation invariants *)
  Lemma tree_insert_wf ρ ρt r rt π πC :
    tree_wf ρ ρt → tree_wf r rt → ρt ##ₘ rt → ρt !! π = Some πC →
    tree_wf ρ (tree_insert ρt r rt π πC).
  Proof using.
    intros Ht. revert r rt π πC. induction Ht; intros.
    assert (ρ ∉ dom rt).
    { intros F. apply elem_of_dom in F. destruct F. eapply map_disjoint_Some_r in H8; eauto.
      assert (is_Some (t !! ρ)).
      { apply elem_of_dom. apply tree_wf_root_elem. by econstructor. }
      by rewrite H8 in H9. }
    assert (r ∉ dom t).
    { intros F. apply elem_of_dom in F. destruct F. eapply map_disjoint_Some_r in H9; eauto.
      assert (is_Some (rt !! r)).
      { apply elem_of_dom. apply tree_wf_root_elem. auto. }
      by rewrite H9 in H10. }
    assert (Cf !! r = None).
    { subst. assert (dom Cf ⊆ dom (forest_merge ρ Cf)).
      { eapply forest_merge_dom_forest_subseteq; eauto. eapply map_Forall_impl; eauto.
        intros. eapply tree_wf_root_elem; eauto. }
      apply not_elem_of_dom. intros F. apply H9. eapply elem_of_weaken; eauto. }
    assert (Ha0 : forest_trees_disjoint (<[r:=rt]> Cf)).
    { subst. apply forest_trees_disjoint_insert; eauto. split; auto.
      rewrite /forest_merge in H6. apply map_disjoint_insert_l in H6. destruct H6.
      apply forest_fold_disjoint_tree_disjoint; auto. }
    assert (Ha1 : (rt ∪ forest_fold Cf) !! ρ = None).
    { apply lookup_union_None_2; auto. by apply not_elem_of_dom. }
    (* Case analysis: π is root or π is internal *)
    destruct (decide (π = ρ)).
    - subst π. rewrite /tree_insert. subst.
      eapply (tree_wf_children _ _ (<[r:=rt]>Cf)); auto.
      + rewrite /forest_merge lookup_insert_eq in H7. inv H7. rewrite /forest_merge.
        rewrite forest_fold_insert_L; auto.
        rewrite -(insert_delete_eq (rt ∪ <[ρ:=dom Cf]> (forest_fold Cf)) ρ).
        replace (delete ρ (rt ∪ <[ρ:=dom Cf]> (forest_fold Cf))) with (rt ∪ forest_fold Cf).
        * rewrite dom_insert_L. done.
        * rewrite -insert_union_r; last (by eapply not_elem_of_dom).
          rewrite delete_insert_eq delete_id; auto.
      + rewrite forest_fold_insert_L; auto.
      + apply map_Forall_insert; auto.
    (* internal case: π is a child of root OR exists v, a child of root, whose tree contains π. It's update is wf by IH. *)
    - destruct (Cf !! π) eqn:Hv.
      + rename g into ct.
        assert (Hprne : π ≠ r).
        { intros F; subst. by rewrite H10 in Hv. }
        assert (ct ##ₘ rt).
        { eapply (forest_trees_disjoint_lookup_disjoint _ π r _ _ Ha0); auto.
          - rewrite lookup_insert_ne; auto.
          - rewrite lookup_insert_eq; auto. }
        assert (tree_wf π ct) by eauto.
        assert (ct !! π = Some πC).
        { subst. eapply forest_merge_children_of_child. 2: eapply H7. all: auto.
          eapply tree_wf_root_elem; eauto. }
        specialize (H4 _ _ Hv _ _ _ _ H5 H11 H13).
        assert (Hb0 : forest_trees_disjoint (<[π:=tree_insert ct r rt π πC]> (delete π Cf))).
        { rewrite /tree_insert. apply forest_trees_disjoint_insert; first by apply lookup_delete_eq.
          apply (forest_trees_disjoint_delete _ _ _ Hv) in H2. destruct H2. split; auto.
          apply forest_trees_disjoint_insert in Ha0; auto. destruct Ha0.
          apply (map_Forall_delete _ _ π) in H15. intros i x Hilu.
          specialize (H2 _ _ Hilu). specialize (H15 _ _ Hilu). simpl in H2, H15.
          apply map_disjoint_insert_r_2.
          - eapply (map_disjoint_Some_r x ct); eauto.
          - apply map_disjoint_union_r_2; auto. }
        eapply (tree_wf_children _ _ (<[π:=tree_insert ct r rt π πC]>(delete π Cf))); auto.
        * subst. rewrite /tree_insert /forest_merge. rewrite !forest_fold_insert_L; auto.
          -- rewrite dom_insert_L dom_delete_L. rewrite -(insert_union_l (rt ∪ ct) _ π).
             rewrite -(map_union_assoc rt ct). rewrite -(forest_fold_delete_L Cf π ct); auto.
             rewrite (insert_insert_ne); auto. f_equal.
             rewrite (insert_union_r rt); last by apply not_elem_of_dom. f_equal.
             replace ({[π]} ∪ dom Cf ∖ {[π]}) with (dom Cf); auto.
             assert (π ∈ dom Cf) by (by apply elem_of_dom).
             rewrite -union_difference_L; auto. set_solver.
          -- apply lookup_delete_eq.
        * unfold tree_insert. rewrite forest_fold_insert_L; auto. 2: apply lookup_delete_eq.
          apply lookup_union_None_2.
          -- rewrite lookup_insert_ne; auto. apply lookup_union_None_2; first by apply not_elem_of_dom.
             assert (ct ⊆ forest_fold Cf) by (by eapply forest_fold_subseteq).
             eapply (lookup_weaken_None _ (forest_fold Cf)); eauto.
          -- pose proof (forest_fold_delete_L _ π _ H2 Hv). rewrite H14 in H1.
             apply lookup_union_None in H1. destruct H1. auto.
        * replace Cf with (<[π:=ct]>(delete π Cf)) in H3; last by apply insert_delete_id.
          apply map_Forall_insert in H3; last by apply lookup_delete_eq. destruct H3.
          apply map_Forall_insert; first by apply lookup_delete_eq. split; auto.
      + assert (∃ c ct, Cf !! c = Some ct ∧ node ct π).
        { eapply forest_merge_not_child_of_root; eauto.
          - subst. unfold node. rewrite H7. done.
          - apply not_elem_of_dom; auto. }
        destruct H11 as (c&ct&?&?).
        assert (Hcrne : c ≠ r).
        { intros F; subst. by rewrite H10 in H11. }
        assert (ct ##ₘ rt).
        { eapply (forest_trees_disjoint_lookup_disjoint _ c r _ _ Ha0); auto.
          - rewrite lookup_insert_ne; auto.
          - rewrite lookup_insert_eq; auto. }
        assert (ct !! π = Some πC).
        { eapply children_wf_subtree; first eapply H7; auto. subst t. eapply forest_merge_subseteq; eauto. }
        specialize (H4 _ _ H11 _ _ _ _ H5 H13 H14).
        rename π into u, c into π.
        assert (Hb0 : forest_trees_disjoint (<[π:=tree_insert ct r rt u πC]> (delete π Cf))).
        { rewrite /tree_insert. apply forest_trees_disjoint_insert; first by apply lookup_delete_eq.
          apply (forest_trees_disjoint_delete _ _ _ H11) in H2. destruct H2. split; auto.
          apply forest_trees_disjoint_insert in Ha0; auto. destruct Ha0.
          apply (map_Forall_delete _ _ π) in H16. intros i x Hilu.
          specialize (H2 _ _ Hilu). specialize (H16 _ _ Hilu). simpl in H2, H16.
          apply map_disjoint_insert_r_2.
          - eapply (map_disjoint_Some_r x ct); eauto.
          - apply map_disjoint_union_r_2; auto. }
        eapply (tree_wf_children _ _ (<[π:=tree_insert ct r rt u πC]>(delete π Cf))); auto.
        * subst. rewrite /tree_insert /forest_merge. rewrite !forest_fold_insert_L; auto.
          -- rewrite dom_insert_L dom_delete_L. rewrite -(insert_union_l (rt ∪ ct) _ u).
             rewrite -(map_union_assoc rt ct). rewrite -(forest_fold_delete_L Cf π ct); auto.
             rewrite (insert_insert_ne); auto. f_equal.
             rewrite (insert_union_r rt); last by apply not_elem_of_dom. f_equal.
             replace ({[π]} ∪ dom Cf ∖ {[π]}) with (dom Cf); auto.
             assert (π ∈ dom Cf) by (by apply elem_of_dom).
             rewrite -union_difference_L; auto. set_solver.
          -- apply lookup_delete_eq.
        * unfold tree_insert. rewrite forest_fold_insert_L; auto. 2: apply lookup_delete_eq.
          apply lookup_union_None_2.
          -- rewrite lookup_insert_ne; auto. apply lookup_union_None_2; first by apply not_elem_of_dom.
             assert (ct ⊆ forest_fold Cf) by (by eapply forest_fold_subseteq).
             eapply (lookup_weaken_None _ (forest_fold Cf)); eauto.
          -- pose proof (forest_fold_delete_L _ π _ H2 H11). rewrite H15 in H1.
             apply lookup_union_None in H1. destruct H1. auto.
        * replace Cf with (<[π:=ct]>(delete π Cf)) in H3; last by apply insert_delete_id.
          apply map_Forall_insert in H3; last by apply lookup_delete_eq. destruct H3.
          apply map_Forall_insert; first by apply lookup_delete_eq. split; auto.
  Qed.

  Lemma tree_singleton_wf ρ : tree_wf ρ (tree_singleton ρ).
  Proof using. eapply (tree_wf_children _ _ ∅); try done. Qed.

  Lemma forest_insert_wf f ρ t :
    forest_wf f → tree_wf ρ t →
    f !! ρ = None →
    forest_tree_disjoint f t →
    forest_wf (forest_insert f ρ t).
  Proof using.
    intros. unfold forest_insert. destruct H0. split.
    - apply forest_trees_disjoint_insert; auto.
    - apply map_Forall_insert; auto.
  Qed.

  Lemma forest_union_wf f1 f2 :
    forest_wf f1 → forest_wf f2 →
    forest_disjoint f1 f2 →
    map_Forall (λ _ m, forest_tree_disjoint f1 m) f2 →
    forest_wf (forest_union f1 f2).
  Proof using.
    unfold forest_wf. intros. destruct H0, H1. split.
    - apply forest_trees_disjoint_union; auto.
    - apply map_Forall_union_2; auto.
  Qed.

  Lemma tree_split_wf ρ Cf :
    forest_fold Cf !! ρ = None →
    forest_trees_disjoint Cf → map_Forall (λ c ct, tree_wf c ct) Cf →
    forest_wf (tree_split ρ Cf).
  Proof using.
    intros. unfold tree_split. apply forest_insert_wf.
    - split; auto.
    - apply tree_singleton_wf.
    - assert (dom Cf ⊆ dom (forest_fold Cf)).
      { eapply forest_fold_dom_forest_subseteq; eauto. eapply map_Forall_impl; eauto.
        simpl; intros. apply tree_wf_root_elem; auto. }
      apply not_elem_of_dom in H0. apply not_elem_of_dom. set_solver.
    - intros ???. apply map_disjoint_singleton_r_2. pose proof (forest_fold_subseteq _ _ _ H1 H3).
      apply not_elem_of_dom in H0. apply not_elem_of_dom. apply subseteq_dom in H4. set_solver.
  Qed.

  Lemma forest_delete_wf f ρ : forest_wf f → forest_wf (delete ρ f).
  Proof using.
    unfold forest_wf. intros [? ?]. split.
    - by apply forest_trees_disjoint_delete_1.
    - by apply map_Forall_delete.
  Qed.

  Lemma forest_tree_disjoint_tree_singleton f ρ :
    forest_trees_disjoint f →
    map_Forall (λ c ct, c ∈ dom ct) f →
    forest_fold f !! ρ = None →
    forest_tree_disjoint f (tree_singleton ρ).
  Proof using.
    intros. assert (Ha : dom f ⊆ dom (forest_fold f)).
    { apply forest_fold_dom_forest_subseteq; auto. }
    intros ???. apply map_disjoint_singleton_r_2.
    assert (x ⊆ forest_fold f).
    { eapply forest_fold_subseteq; eauto. }
    apply not_elem_of_dom in H2. apply not_elem_of_dom.
    apply subseteq_dom in H4. set_solver.
  Qed.

  Lemma tree_clear_forest_disjoint f ρ Cf :
    forest_wf f →
    f !! ρ = Some (forest_merge ρ Cf) →
    forest_fold Cf !! ρ = None →
    forest_trees_disjoint Cf →
    map_Forall (λ (c : V) (ct : tree V), tree_wf c ct) Cf →
    forest_disjoint (delete ρ f) (tree_split ρ Cf).
  Proof using.
    intros. destruct H0. unfold forest_disjoint, tree_split, forest_insert.
    apply map_disjoint_insert_r_2; first by apply lookup_delete_eq.
    apply map_disjoint_spec. intros.
    assert (i ≠ ρ).
    { intros F; subst. by rewrite lookup_delete_eq in H6. }
    rewrite lookup_delete_ne in H6; auto.
    assert (i ∈ dom x).
    { eapply tree_wf_root_elem. eapply H5. auto. }
    assert (i ∈ dom (forest_merge ρ Cf)).
    { assert (dom Cf ⊆ dom (forest_merge ρ Cf)).
      { eapply forest_merge_dom_forest_subseteq; eauto. eapply map_Forall_impl; eauto.
        simpl; intros. apply tree_wf_root_elem; auto. }
      apply elem_of_dom_2 in H7. set_solver. }
    assert (x ##ₘ forest_merge ρ Cf).
    { eapply (forest_trees_disjoint_lookup_disjoint f); eauto. }
    apply map_disjoint_dom_1 in H11. set_solver.
  Qed.

  Lemma tree_clear_wf f ρ Cf :
    forest_wf f →
    f !! ρ = Some (forest_merge ρ Cf) →
    forest_fold Cf !! ρ = None →
    forest_trees_disjoint Cf →
    map_Forall (λ (c : V) (ct : tree V), tree_wf c ct) Cf →
    forest_wf (tree_clear f ρ Cf).
  Proof using.
    intros. unfold tree_clear. apply forest_union_wf; auto.
    - by apply forest_delete_wf.
    - apply tree_split_wf; auto.
    - apply tree_clear_forest_disjoint; auto.
    - destruct H0. apply forest_fold_disjoint_forests_disjoint. unfold tree_split, forest_insert.
      assert (Ha : dom Cf ⊆ dom (forest_fold Cf)).
      { apply forest_fold_dom_forest_subseteq; auto. eapply map_Forall_impl; first eapply H4.
        simpl; intros. apply tree_wf_root_elem; auto. }
      assert (Ha0 : Cf !! ρ = None).
      { apply not_elem_of_dom. apply not_elem_of_dom in H2. set_solver. }
      rewrite forest_fold_insert_L; auto.
      + apply forest_tree_disjoint_union_tree.
        apply (forest_trees_disjoint_delete _ _ _ H1) in H0. destruct H0.
        split.
        * unfold forest_merge in H0. rewrite insert_union_singleton_l in H0.
          apply forest_tree_disjoint_union_tree in H0. destruct H0. auto.
        * intros ???. apply map_disjoint_singleton_r_2.
          assert (x ##ₘ forest_merge ρ Cf).
          { specialize (H0 _ _ H7). auto. }
          assert (ρ ∈ dom (forest_merge ρ Cf)).
          { rewrite /forest_merge dom_insert_L. set_solver. }
          apply not_elem_of_dom. apply map_disjoint_dom in H8. set_solver.
      + apply forest_trees_disjoint_insert; auto. split; auto.
        apply forest_tree_disjoint_tree_singleton; auto.
        eapply map_Forall_impl; first eapply H4.
        simpl; intros. apply tree_wf_root_elem; auto.
  Qed.

  Lemma forest_move_tree_wf f ρ ρt r rt π πC :
    forest_wf f →
    ρ ≠ r →
    f !! r = Some rt →
    f !! ρ = Some ρt →
    ρt !! π = Some πC →
    forest_wf (forest_move_tree f ρ ρt r rt π πC).
  Proof using.
    unfold forest_move_tree. intros. apply forest_insert_wf.
    - do 2 apply forest_delete_wf. auto.
    - destruct H0.
      assert (ρt ##ₘ rt) by (by eapply forest_trees_disjoint_lookup_disjoint).
      assert (tree_wf ρ ρt) by (by eauto).
      assert (tree_wf r rt) by (by eauto).
      apply tree_insert_wf; auto.
    - apply lookup_delete_eq.
    - intros ???. unfold tree_insert.
      assert (Hne1 : i ≠ ρ) by (intros F; subst; by rewrite lookup_delete_eq in H5).
      rewrite lookup_delete_ne in H5; auto.
      assert (Hne2 : i ≠ r) by (intros F; subst; by rewrite lookup_delete_eq in H5).
      rewrite lookup_delete_ne in H5; auto. destruct H0.
      assert (Hd1 : x ##ₘ ρt).
      { eapply (forest_trees_disjoint_lookup_disjoint f i ρ); eauto. }
      apply map_disjoint_insert_r_2.
      + apply elem_of_dom_2 in H4. apply not_elem_of_dom. apply map_disjoint_dom in Hd1. set_solver.
      + apply map_disjoint_union_r_2; auto.
        eapply (forest_trees_disjoint_lookup_disjoint f i r); eauto.
  Qed.

  Lemma forest_insert_singleton_wf f ρ :
    forest_wf f → forest_fold f !! ρ = None →
    forest_wf (forest_insert f ρ (tree_singleton ρ)).
  Proof using.
    intros. pose proof (forest_fold_not_in_forest_not_in _ _ H0 H1).
    apply forest_insert_wf; auto.
    { apply tree_singleton_wf. }
    apply forest_tree_disjoint_tree_singleton; auto.
    - destruct H0; auto.
    - destruct H0. eapply map_Forall_impl; first eapply H3. simpl; intros. apply tree_wf_root_elem; auto.
  Qed.

  Lemma forest_merge_subseteq_Forall ρ f :
    forest_fold f !! ρ = None →
    forest_trees_disjoint f →
    map_Forall (λ _ t, t ⊆ forest_merge ρ f) f.
  Proof using. intros. intros ???. eapply forest_merge_subseteq; eauto. Qed.

  Lemma forest_merge_internal_Forall ρ f :
    map_Forall (λ v _, internal (forest_merge ρ f) v) f.
  Proof using.
    intros. intros ???. exists ρ, (dom f). split; last by apply elem_of_dom.
    unfold forest_merge. rewrite /children lookup_insert_eq. done.
  Qed.

  (* Domain of forest under forset_fold *)

  Lemma tree_singleton_dom ρ :
    dom (tree_singleton ρ) = {[ρ]}.
  Proof using. by rewrite /tree_singleton dom_singleton_L. Qed.

  Lemma forest_fold_insert_dom f ρ t :
    f !! ρ = None →
    dom (forest_fold (forest_insert f ρ t)) = dom t ∪ dom (forest_fold f).
  Proof using. apply forest_fold_dom_insert. Qed.

  Lemma forest_fold_tree_split_dom ρ Cf :
    Cf !! ρ = None →
    dom (forest_fold (tree_split ρ Cf)) = {[ρ]} ∪ dom (forest_fold Cf).
  Proof using. intros. rewrite /tree_split forest_fold_insert_dom; auto. by rewrite tree_singleton_dom. Qed.

  Lemma tree_clear_dom f ρ Cf :
    forest_wf f →
    f !! ρ = Some (forest_merge ρ Cf) →
    forest_fold Cf !! ρ = None →
    forest_trees_disjoint Cf →
    map_Forall (λ (c : V) (ct : tree V), tree_wf c ct) Cf →
    dom (forest_fold (tree_clear f ρ Cf)) = dom (forest_fold f).
  Proof using.
    intros. unfold tree_clear. rewrite forest_fold_dom_union.
    2: by apply tree_clear_forest_disjoint.
    rewrite forest_fold_tree_split_dom.
    2: by apply forest_fold_not_in_forest_not_in.
    rewrite -(forest_fold_dom_delete f ρ _ H1).
    rewrite (union_comm_L (dom (forest_merge ρ Cf)) (dom (forest_fold (delete ρ f)))). f_equal.
    unfold forest_merge. rewrite dom_insert_L. auto.
  Qed.

  Lemma tree_insert_dom ρt r rt π πC :
    ρt !! π = Some πC →
    dom (tree_insert ρt r rt π πC) = dom rt ∪ dom ρt.
  Proof using.
    intros. rewrite /tree_insert dom_insert_L dom_union_L.
    assert (π ∈ dom ρt) by (by apply elem_of_dom). set_solver.
  Qed.

  Lemma forest_fold_move_tree_dom f ρ ρt r rt π πC :
    ρ ≠ r →
    f !! r = Some rt →
    f !! ρ = Some ρt →
    ρt !! π = Some πC →
    dom (forest_fold (forest_move_tree f ρ ρt r rt π πC)) = dom (forest_fold f).
  Proof using.
    intros.
    unfold forest_move_tree. rewrite forest_fold_insert_dom.
    2: by rewrite lookup_delete_eq.
    rewrite -(forest_fold_dom_delete f _ _ H1).
    assert (delete r f !! ρ = Some ρt) by (by rewrite lookup_delete_ne).
    rewrite -(forest_fold_dom_delete (delete r f) _ _ H4).
    rewrite union_assoc_L. f_equal. apply tree_insert_dom; auto.
  Qed.

  Lemma forest_fold_insert_singleton_dom f ρ :
    f !! ρ = None →
    dom (forest_fold (forest_insert f ρ (tree_singleton ρ))) = {[ρ]} ∪ dom (forest_fold f).
  Proof using. intros. rewrite forest_fold_insert_dom; auto. rewrite tree_singleton_dom; auto. Qed.

  Lemma tree_insert_child ρt r rt π πC v u :
    ρt ##ₘ rt →
    ρt !! π = Some πC →
    (child ρt v u ∨ child rt v u) → child (tree_insert ρt r rt π πC) v u.
  Proof using.
    intros. rewrite /tree_insert. destruct H2 as [(?&?&?) | (?&?&?)].
    - destruct (decide (v = π)).
      + subst. exists ({[r]} ∪ πC). rewrite /children H1 in H2. inv H2. split; last set_solver.
        rewrite /children lookup_insert_eq. auto.
      + exists x. split; last auto. rewrite /children lookup_insert_ne; auto.
        apply lookup_union_Some_r; auto.
    - destruct (decide (v = π)).
      + subst. eapply map_disjoint_Some_r in H2; eauto. by rewrite H1 in H2.
      + exists x. split; last auto. rewrite /children lookup_insert_ne; auto.
        apply lookup_union_Some_l; auto.
  Qed.

  Lemma forest_merge_child_inv ρ f r rt v u :
    forest_trees_disjoint f →
    f !! r = Some rt → v ≠ ρ → v ∈ dom rt →
    child (forest_merge ρ f) v u →
    child rt v u.
  Proof using.
    intros. destruct H4 as (?&?&?). rewrite /forest_merge /children lookup_insert_ne in H4; auto.
    exists x. split; last auto. assert (rt ⊆ forest_fold f) by (eapply forest_fold_subseteq; eauto).
    apply elem_of_dom in H3. destruct H3. eapply lookup_weaken in H6; eauto. rewrite H4 in H6. inv H6. auto.
  Qed.

End tree.
