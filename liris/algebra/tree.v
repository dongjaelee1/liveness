From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
(* From liris.cgraphs Require Export cgraph. *)
(* From liris.cgraphs Require Import mapexcl. *)

Section aux.
  (* Inductive tc2 {A : Type} (R : relation A) : relation A := *)
  (* | tc2_once : ∀ x y : A, R x y → tc2 R x y *)
  (* | tc2_l : ∀ x y z : A, tc2 R x y → R y z → tc2 R x z. *)

  (* Lemma tc_tc2 A (R : relation A) : ∀ a b, tc R a b ↔ tc2 R a b. *)
  (* Proof. *)
  (*   split; intros. *)
  (*   - induction H; first by econstructor. revert x H H0. induction IHtc; intros. *)
  (*     + econstructor 2. *)

  (* Lemma tc_ind2 : *)
  (* ∀ {A : Type} (R : relation A) (P : A → A → Prop), *)
  (*   (∀ x y : A, R x y → P x y) *)
  (*   → (∀ x y z : A, tc R x y → R y z → P y z → P x z) → ∀ a a0 : A, tc R a a0 → P a a0. *)
  (* Proof. *)
  (*   intros. induction H1; eauto. eapply H0. *)
  (*   - eapply H; eauto. *)
  (*   -  *)

  (*   eauto. Qed. *)

End aux.

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
  Definition forest_disjoint f : Prop := map_disjoint_list (forest_to_trees f).
  Definition forest_fold_alt f : tree V := map_fold (λ _ t a, t ∪ a) ∅ f.

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

  Lemma forest_disjoint_fold f :
    forest_disjoint f → forest_fold_alt f = forest_fold f.
  Proof using.
    unfold forest_disjoint, forest_fold, forest_to_trees, forest_fold_alt.
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
    forest_disjoint (<[ρ:=t]>f) → f !! ρ = None →
    forest_fold (<[ρ:=t]>f) = t ∪ (forest_fold f).
  Proof using.
    unfold forest_disjoint, forest_fold, forest_to_trees, map_to_list. intros.
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

  Lemma forest_disjoint_insert f ρ t :
    f !! ρ = None → (forest_disjoint (<[ρ:=t]> f) ↔ map_Forall (λ _ m, m ##ₘ t) f ∧ forest_disjoint f).
  Proof using.
    unfold forest_disjoint, forest_to_trees. split; intros.
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
    map_Forall (λ _ (m : tree V), m ##ₘ t) f → t ##ₘ forest_fold f.
  Proof using.
    unfold forest_fold, forest_to_trees.
    revert t. pattern f. revert f. apply map_first_key_ind; intros.
    { rewrite map_to_list_empty. apply map_disjoint_empty_r. }
    rewrite map_to_list_insert_first_key; auto. rewrite fmap_cons union_list_cons. simpl.
    apply map_Forall_insert in H3; last auto. destruct H3. eapply H2 in H4.
    apply map_disjoint_union_r_2; eauto.
  Qed.

  Lemma forest_fold_subseteq f ρ t :
    forest_disjoint f → f !! ρ = Some t → t ⊆ forest_fold f.
  Proof using.
    revert ρ t. induction f using map_ind; intros.
    { done. }
    rewrite forest_fold_insert_L; auto.
    apply forest_disjoint_insert in H1; last auto. destruct H1.
    destruct (decide (i = ρ)).
    - subst. rewrite lookup_insert_eq in H2. inv H2. apply map_union_subseteq_l.
    - rewrite lookup_insert_ne in H2; last auto. apply map_union_subseteq_r'; last eauto.
      apply tree_disjoint_forest_fold_disjoint; auto.
  Qed.

  Lemma forest_fold_dom_forest_subseteq f :
    forest_disjoint f → map_Forall (λ c t, c ∈ dom t) f → dom f ⊆ dom (forest_fold f).
  Proof using.
    induction f using map_ind; intros.
    { done. }
    rewrite map_Forall_insert in H2; last auto. destruct H2. intros v.
    rewrite dom_insert_L. intros Hv. rewrite forest_fold_insert_L; auto. rewrite dom_union.
    apply elem_of_union in Hv. destruct Hv.
    - apply elem_of_singleton in H4. subst. set_solver.
    - apply forest_disjoint_insert in H1; last auto. destruct H1. specialize (IHf H5 H3).
      set_solver.
  Qed.

  Lemma forest_fold_lookup_Some_exists_root f v C :
    forest_disjoint f → (forest_fold f) !! v = Some C → ∃ r t, f !! r = Some t ∧ t !! v = Some C.
  Proof using.
    revert v C. induction f using map_ind; intros.
    { rewrite forest_fold_empty in H1. done. }
    rewrite forest_fold_insert_L in H2; auto. rewrite forest_disjoint_insert in H1; auto. destruct H1.
    apply lookup_union_Some_raw in H2. destruct H2.
    - exists i, x. rewrite lookup_insert_eq. auto.
    - destruct H2. specialize (IHf _ _ H3 H4). destruct IHf as (?&?&?&?).
      assert (i ≠ x0).
      { intros <-. by rewrite H0 in H5. }
      exists x0, x1. rewrite lookup_insert_ne; auto.
  Qed.

  Lemma forest_disjoint_lookup_disjoint f r1 r2 t1 t2 :
    forest_disjoint f → r1 ≠ r2 → f !! r1 = Some t1 → f !! r2 = Some t2 → t1 ##ₘ t2.
  Proof using.
    revert r1 r2 t1 t2. induction f using map_ind; intros; first done.
    apply forest_disjoint_insert in H1; auto. destruct H1.
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
    forest_disjoint f → f !! r1 = Some t1 → is_Some (t1 !! v) → f !! r2 = Some t2 → is_Some(t2 !! v) → r1 = r2.
  Proof using.
    intros. destruct (decide (r1 = r2)); auto. exfalso.
    pose proof (forest_disjoint_lookup_disjoint _ _ _ _ _ H0 n H1 H3). destruct H2, H4.
    rewrite (map_disjoint_Some_r _ _ _ _ H5 H4) in H2. done.
  Qed.

  Lemma forest_fold_lookup_child_tree f v C t :
    forest_disjoint f → (forest_fold f) !! v = Some C → f !! v = Some t → v ∈ dom t → t !! v = Some C.
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

  (* Instance parent_Decision_aux t v π : Decision (map_Exists (λ u C, u = π ∧ v ∈ C) t). *)
  (* Proof using. eapply map_Exists_dec. intros. solve_decision. Qed. *)
  (* Global Instance parent_Decision t : ∀ v π, Decision (parent t v π). *)
  (* Proof using. *)
  (*   intros. unfold parent, children. destruct (parent_Decision_aux t v π). *)
  (*   - left. destruct m as (?&?&?&?&?). subst. eauto. *)
  (*   - right. intros (C&Hlu&Helem). apply n. exists π, C. auto. *)
  (* Qed. *)
  (* Global Instance internal_Decision t : ∀ v, Decision (internal t v). *)
  (* Proof using. *)
  (*   intros. unfold internal, parent, children. apply _. *)
  (* Qed. *)
  (* Global Instance root_Decision t : ∀ v, Decision (root t v). *)
  (* Proof using. *)
  (*   intros. unfold root. destruct (internal_Decision t v). *)
  (*   - right. intros F. destruct i. apply (F x). auto. *)
  (*   - left. intros π Hp. apply n. exists π. auto. *)
  (* Qed. *)

  (** Operations *)
  Definition tree_singleton ρ : tree V := {[ρ:=∅]}.
  Definition forest_merge ρ f : tree V := <[ρ:=dom f]>(forest_fold f).
  Definition forest_insert f ρ t := <[ρ:=t]>f.
  Definition tree_split t ρ (Cf : forest V) : forest V := forest_insert Cf ρ (tree_singleton ρ).
  Definition tree_insert t r (rt : tree V) π (πC : gset _) : tree V := <[π:={[r]} ∪ πC]>(rt ∪ t).

  (** Well-formedness *)
  Inductive tree_wf : V → tree V → Prop :=
  | tree_wf_children ρ t (Cf : forest V) :
    t = forest_merge ρ Cf →
    root t ρ →
    forest_fold Cf !! ρ = None →
    forest_disjoint Cf →
    map_Forall (λ c ct, tree_wf c ct) Cf →
    tree_wf ρ t.

  Definition forest_wf : forest V → Prop :=
    λ f, forest_disjoint f ∧ map_Forall (λ ρ t, tree_wf ρ t) f.

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

  (* Lemma children_parent t v π C : *)
  (*   children t π C → (v ∈ C ↔ parent t v π). *)
  (* Proof using. *)
  (*   intros. split; intros. *)
  (*   - exists C. done. *)
  (*   - destruct H1 as (?&?&?). pose proof (children_unique _ _ _ _ H0 H1). by subst. *)
  (* Qed. *)

  Lemma forest_fold_keeps_children t π C Cf r :
    children t π C → Cf !! r = Some t → forest_disjoint Cf →
    children (forest_fold Cf) π C.
  Proof using.
    rewrite /children. revert t π C r. induction Cf using map_ind; intros.
    { by rewrite lookup_empty in H1. }
    rewrite forest_fold_insert_L; auto. 
    destruct (decide (r = i)).
    { subst. rewrite lookup_insert_eq in H2. inv H2. by apply lookup_union_Some_l. }
    rewrite lookup_insert_ne in H2; last auto.
    apply forest_disjoint_insert in H3; last auto. destruct H3.
    pose proof (map_Forall_lookup_1 _ _ _ _ H3 H2). eapply map_disjoint_Some_l in H5; eauto.
    rewrite lookup_union_r; eauto.
  Qed.
  Lemma forest_fold_keeps_child t π v Cf r :
    child t π v → Cf !! r = Some t → forest_disjoint Cf →
    child (forest_fold Cf) π v.
  Proof using.
    rewrite /child. intros. destruct H0 as (?&?&?).
    pose proof (forest_fold_keeps_children _ _ _ _ _ H0 H1 H2). eauto.
  Qed.
  Lemma forest_fold_keeps_internal t v Cf r :
    internal t v → Cf !! r = Some t → forest_disjoint Cf →
    internal (forest_fold Cf) v.
  Proof using.
    rewrite /internal. intros. destruct H0 as (?&?).
    pose proof (forest_fold_keeps_child _ _ _ _ _ H0 H1 H2). eauto.
  Qed.

  (* Lemma forest_fold_keeps_parent t v π Cf r : *)
  (*   parent t v π → Cf !! r = Some t → forest_disjoint Cf → *)
  (*   parent (forest_fold Cf) v π. *)
  (* Proof using. *)
  (*   rewrite /parent. intros. destruct H0 as (?&?&?). *)
  (*   pose proof (forest_fold_keeps_children _ _ _ _ _ H0 H1 H2). eauto. *)
  (* Qed. *)

  Lemma forest_merge_keeps_children t π C Cf r ρ D :
    children t π C → Cf !! r = Some t → forest_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    children (<[ρ:=D]>(forest_fold Cf)) π C.
  Proof using.
    intros. pose proof (forest_fold_keeps_children _ _ _ _ _ H0 H1 H2).
    unfold children in H4. unfold children. rewrite lookup_insert_ne; first eauto.
    intro F. subst. rewrite H3 in H4. done.
  Qed.
  Lemma forest_merge_keeps_child t π v Cf r ρ D :
    child t π v → Cf !! r = Some t → forest_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    child (<[ρ:=D]>(forest_fold Cf)) π v.
  Proof using.
    rewrite /child. intros. destruct H0 as (?&?&?).
    pose proof (forest_merge_keeps_children _ _ _ _ _ _ D H0 H1 H2 H3). eauto.
  Qed.
  Lemma forest_merge_keeps_internal t v Cf r ρ D :
    internal t v → Cf !! r = Some t → forest_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    internal (<[ρ:=D]>(forest_fold Cf)) v.
  Proof using.
    rewrite /internal. intros. destruct H0 as (?&?).
    pose proof (forest_merge_keeps_child _ _ _ _ _ _ D H0 H1 H2 H3). eauto.
  Qed.

  Lemma tree_wf_not_root_internal t ρ v :
    tree_wf ρ t → node t v → v ≠ ρ → internal t v.
    (* tree_wf ρ t → v ∈ dom t → v ≠ ρ → internal t v. *)
  Proof using.
    intros Ht. revert v. induction Ht; intros. subst.
    assert (v ∈ dom (forest_fold Cf)).
    { apply elem_of_dom in H6. rewrite dom_insert_L in H6. apply elem_of_union in H6. destruct H6; set_solver. }
    (* FIXME: Error: Cannot infer an instance of type "tree V" for the variable t in context *)
    (* destruct (decide (v ∈ (dom Cf))). *)
    destruct (decide (v ∈ (dom Cf : gset V))).
    - pose proof e as ?. apply elem_of_dom in e. destruct e. exists ρ, (dom Cf). split; auto.
      by rewrite /children lookup_insert_eq.
    - pose proof (forest_fold_internal_elem_of _ _ H0 n). destruct H8 as (?&?&?&?).
      assert (v ≠ x).
      { intros ->. apply not_elem_of_dom in n. by rewrite n in H8. }
      apply elem_of_dom in H9. specialize (H5 _ _ H8 _ H9 H10). eapply forest_merge_keeps_internal; eauto.
  Qed.

  Lemma tree_wf_root_elem t ρ : tree_wf ρ t → ρ ∈ dom t.
  Proof using. intros. inv H0. rewrite dom_insert. set_solver. Qed.

  Lemma tree_wf_root_unique t ρ1 ρ2 : tree_wf ρ1 t → tree_wf ρ2 t → ρ1 = ρ2.
  Proof using.
    intros. pose proof H0 as Htwf. inv H0. destruct (decide (ρ1 = ρ2)); first auto. exfalso.
    pose proof (tree_wf_not_root_internal _ _ ρ1 H1).
    eapply root_not_internal in H3. apply H3. apply H0; auto.
    apply elem_of_dom, tree_wf_root_elem. auto.
  Qed.

  Definition descendant t : relation V := tc (child t).

  Global Instance children_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) children.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. unfold children. intros. eapply lookup_weaken; eauto.
  Qed.
  Global Instance child_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) child.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. intros (?&?&?). exists x. split; auto.
    eapply children_tree_subseteq_Proper; eauto.
  Qed.
  Global Instance descendant_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) descendant.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. intro Hd. revert t2 Hs. induction Hd; intros.
    { econstructor 1. destruct H0 as (?&?&?). exists x0. split; auto. eapply children_tree_subseteq_Proper; eauto. }
    econstructor 2.
    - eapply child_tree_subseteq_Proper; eauto.
    - by eapply IHHd.
  Qed.
  Global Instance internal_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (→)) internal.
  Proof using.
    intros t1 t2 Hs ? v ? ?. subst. destruct H1 as (?&?).
    unfold internal. exists x. eapply child_tree_subseteq_Proper; eauto.
  Qed.

  Lemma descendant_r t ρ v u : descendant t ρ v → child t v u → descendant t ρ u.
  Proof using. intros. eapply tc_r; eauto. Qed.

  Lemma forest_merge_subseteq ρ f c t :
    forest_fold f !! ρ = None → forest_disjoint f → f !! c = Some t → t ⊆ forest_merge ρ f.
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
      { subst. destruct H6. unfold forest_merge in H0.
        rewrite lookup_insert_ne in H0; last auto. by apply elem_of_dom. }
      assert (v ∉ dom Cf) by (by apply not_elem_of_dom).
      pose proof (forest_fold_internal_elem_of _ _ H8 H9). destruct H10 as (?&?&?&?).
      assert (node x0 v) by (by apply elem_of_dom).
      assert (v ≠ x).
      { intros F; subst. by rewrite Hv in H10. }
      specialize (H5 _ _ H10 _ H12 H13). eapply (tc_l _ _ x).
      { subst. exists (dom Cf). unfold children, forest_merge.
        split; last by eapply elem_of_dom. by rewrite lookup_insert_eq. }
      eapply descendant_tree_subseteq_Proper; last eapply H5; auto.
      subst. eapply forest_merge_subseteq; eauto.
  Qed.

  Lemma children_wf_subtree t s v C :
    children t v C → is_Some(s !! v) → s ⊆ t → children s v C.
  Proof using.
    unfold children. intros. destruct H1.
    pose proof (lookup_weaken _ _ _ _ H1 H2). rewrite H3 in H0. inv H0. done.
  Qed.
  Lemma child_wf_subtree t s v u :
    child t v u → is_Some (s !! v) → s ⊆ t → child s v u.
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
    { eapply child_wf_subtree; first eapply H6; auto. by rewrite /forest_merge lookup_insert_eq. }
    assert (child (forest_merge ρ Cf) ρ π).
    { eapply child_wf_subtree; eauto. by rewrite /forest_merge lookup_insert_eq. }
    assert (is_Some (Cf !! π)).
    { destruct H0 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0. inv H0.
      apply elem_of_dom; auto. }
    destruct H8. specialize (H5 _ _ H8 _ _ H7).
    assert (x ⊆ (forest_merge ρ Cf)).
    { eapply forest_merge_subseteq; eauto. }
    eapply descendant_tree_subseteq_Proper; last eapply H5; auto.
    etransitivity; eauto.
  Qed.

  (* Global Instance parent_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) parent. *)
  (* Proof using. *)
  (*   intros t1 t2 Hs ? v ? ? u ?. subst. intros (?&?&?). exists x. split; auto. *)
  (*   eapply children_tree_subseteq_Proper; eauto. *)
  (* Qed. *)

  (* Lemma tree_wf_descendant t ρ v : *)
  (*   tree_wf ρ t → node t v → v ≠ ρ → ancestor t v ρ. *)
  (* Proof using. *)
  (*   intro Ht. revert v. induction Ht; intros. destruct (Cf !! v) eqn:Hv. *)
  (*   - econstructor 1. exists (dom Cf). split. *)
  (*     + subst. apply lookup_insert_eq. *)
  (*     + by apply elem_of_dom. *)
  (*   - assert (v ∈ dom (forest_fold Cf)). *)
  (*     { subst. destruct H6. unfold forest_merge in H0. *)
  (*       rewrite lookup_insert_ne in H0; last auto. by apply elem_of_dom. } *)
  (*     assert (v ∉ dom Cf) by (by apply not_elem_of_dom). *)
  (*     pose proof (forest_fold_internal_elem_of _ _ H8 H9). destruct H10 as (?&?&?&?). *)
  (*     assert (node x0 v) by (by apply elem_of_dom). *)
  (*     assert (v ≠ x). *)
  (*     { intros F; subst. by rewrite Hv in H10. } *)
  (*     specialize (H5 _ _ H10 _ H12 H13). eapply (ancestor_alt _ _ x). *)
  (*     { subst. exists (dom Cf). unfold children, forest_merge. *)
  (*       split; last by eapply elem_of_dom. by rewrite lookup_insert_eq. } *)
  (*     eapply ancestor_tree_subseteq_Proper; last eapply H5; auto. *)
  (*     subst. eapply forest_merge_subseteq; eauto. *)
  (* Qed. *)

  Lemma forest_merge_not_child_of_root ρ f v :
    node (forest_merge ρ f) v → v ∉ dom f → v ≠ ρ → ∃ c ct, f !! c = Some ct ∧ node ct v.
  Proof using.
    intros ?. apply elem_of_dom in H0. revert H0. unfold forest_merge. rewrite dom_insert.
    intros. apply elem_of_union in H0. destruct H0; first set_solver.
    pose proof (forest_fold_internal_elem_of _ _ H0 H1). destruct H3 as (?&?&?&?).
    do 2 eexists; split; eauto. by apply elem_of_dom.
  Qed.

  Lemma forest_merge_dom_forest_subseteq ρ f :
    forest_disjoint f → map_Forall (λ c t, c ∈ dom t) f → dom f ⊆ dom (forest_merge ρ f).
  Proof using.
    intros. unfold forest_merge. rewrite dom_insert.
    pose proof (forest_fold_dom_forest_subseteq _ H0 H1). set_solver.
  Qed.

  Lemma forest_merge_children_of_child ρ f C v t :
    forest_disjoint f → children (forest_merge ρ f) v C → v ≠ ρ → f !! v = Some t → v ∈ dom t →
    children t v C.
  Proof using.
    unfold forest_merge, children. intros. rewrite lookup_insert_ne in H1; auto.
    eapply forest_fold_lookup_child_tree; eauto.
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
    inv H6.
    { by econstructor 1. }
    rename y into π. 
    assert (is_Some (Cf !! π)).
    { destruct H7 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0. inv H0.
      apply elem_of_dom; auto. }
    destruct H0. specialize (H5 _ _ H0).
    assert (x ⊆ forest_merge ρ Cf).
    { eapply forest_merge_subseteq; eauto. }
    assert (descendant x π v).
    { eapply descendant_wf_subtree; first eapply H8; eauto. }
    specialize (H5 _ H9). econstructor 2; last eapply H5; eauto.
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
    revert v H1. induction H0; intros. induction H6.
    { subst. destruct H6 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0. inv H0.
      apply elem_of_dom. eapply elem_of_weaken; first eauto.
      eapply forest_merge_dom_forest_subseteq; eauto.
      eapply map_Forall_impl; first eapply H4. intros. by apply tree_wf_root_elem in H0. }
    rename x into ρ, y into π, z into v. clear IHtc. subst.
    assert (is_Some (Cf !! π)).
    { destruct H6 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H0.
      inv H0. by apply elem_of_dom. }
    destruct H0. specialize (H5 _ _ H0).
    assert (x ⊆ forest_merge ρ Cf).
    { eapply forest_merge_subseteq; eauto. }
    assert (descendant x π v).
    { eapply descendant_wf_subtree; eauto. }
    specialize (H5 _ H9). eapply node_weaken; eauto.
  Qed.

  Lemma tree_wf_root_child_children_subseteq t ρ v C :
    tree_wf ρ t → child t ρ v → children t v C → C ⊆ dom t.
  Proof using.
    intros. inv H0. assert (v ≠ ρ).
    { intros F; subst. eapply H4; eauto. }
    assert (is_Some (Cf !! v)).
    { destruct H1 as (?&?&?). rewrite /children /forest_merge lookup_insert_eq in H1.
      inv H1. by apply elem_of_dom. }
    destruct H3. rename x into s. assert (tree_wf v s) by eauto.
    assert (v ∈ dom s).
    { apply tree_wf_root_elem; eauto. }
    pose proof (forest_merge_children_of_child _ _ _ _ _ H6 H2 H0 H3 H9).
    etransitivity; first instantiate (1:=dom s).
    - inv H8. assert (C = dom Cf0).
      { rewrite /children /forest_merge lookup_insert_eq in H10. by inv H10. }
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

  Lemma tree_wf_internal_not_root t ρ v : tree_wf ρ t → internal t v → v ≠ ρ.
  Proof using.
    intros. intros F; subst. apply internal_not_root in H1. apply H1. inv H0; auto.
  Qed.

  Lemma tree_wf_root_internal_descendant t ρ v :
    tree_wf ρ t → internal t v → descendant t ρ v.
  Proof using.
    intros. eapply tree_wf_node_descendant; eauto.
    - eapply tree_wf_internal_node; eauto.
    - eapply tree_wf_internal_not_root; eauto.
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

  Lemma tree_wf_node_root_or_internal t ρ v :
    tree_wf ρ t → node t v → (root t v ∨ internal t v).
  Proof using.
    intros. apply elem_of_dom in H1. destruct (decide (v = ρ)).
    - subst. left. inv H0; auto.
    - right. apply elem_of_dom in H1. eapply tree_wf_not_root_internal; eauto.
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
    { subst v. pose proof (tree_wf_tree_unique _ _ _ _ H8 H9 H10 H6). by subst. }
    pose proof n. eapply tree_wf_not_root_internal in n; eauto.
    destruct (Cf !! v) eqn:Hv.
    - assert (tree_wf v g) by eauto. assert (g ⊆ t0).
      { etrans; last eapply H8. subst. eapply forest_merge_subseteq; eauto. }
      pose proof (tree_wf_tree_unique _ _ _ _ H9 H13 H6 H12). subst g.
      subst t. eapply forest_merge_subseteq; eauto.
    - assert (v ∉ dom Cf) by (by apply not_elem_of_dom). subst.
      pose proof (forest_merge_not_child_of_root _ _ _ H7 H12 H11). destruct H0 as (?&?&?&?).
      rename x into π, x0 into x.
      assert (x ⊆ forest_merge ρ Cf) by (by eapply forest_merge_subseteq).
      assert (x ⊆ t0).
      { etrans; last eapply H8; auto. }
      specialize (H5 _ _ H0 t0 _ _ H6 H13 H15 H9).
      etrans; first eapply H5; auto.
  Qed.

  Lemma tree_wf_tree_wf_clo t ρ :
    tree_wf ρ t → tree_wf_clo ρ t.
  Proof using.
    intros. induction H0. econstructor. intros.
    destruct (Cf !! v) eqn:HV.
    - assert (tree_wf v g) by eauto. assert (g ⊆ t).
      { subst. eapply forest_merge_subseteq; eauto. }
      pose proof (tree_wf_tree_unique _ _ _ _ H7 H10 H8 H9). subst g. eauto.
    - assert (v ∉ dom Cf) by (by apply not_elem_of_dom).
      assert (v ≠ ρ).
      { eapply tree_wf_internal_not_root; eauto. econstructor; eauto. }
      assert (node t v).
      { eapply tree_wf_internal_node; eauto. econstructor; eauto. }
      subst. pose proof (forest_merge_not_child_of_root _ _ _ H11 H9 H10). destruct H0 as (?&?&?&?).
      specialize (H5 _ _ H0). eapply tree_wf_clo_subtree; first eauto.
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
      subst t. pose proof (forest_merge_not_child_of_root _ _ _ H9 H10 H11). destruct H0 as (?&?&?&?).
      rename x into π, x0 into ct.
      assert (ct ⊆ forest_merge ρ Cf) by (by eapply forest_merge_subseteq).
      assert (internal (forest_merge ρ Cf) π).
      { exists ρ, (dom Cf). split; [by rewrite /children /forest_merge lookup_insert_eq | by eapply elem_of_dom]. }
      assert (tree_wf π ct) by eauto.
      specialize (H1 _ _ H14 H13 H15 _ H12). destruct H1 as (?&?&?). exists x. split; auto.
      etrans; eauto.
  Qed.
  

        destruct (tree_ eapply tree_wf_not_root_internal; eauto.
tree_wf_node_root_or_internal: ∀ t ρ v, tree_wf ρ t → node t v → root t v ∨ internal t v
        - 

      by (

      
forest_merge_not_child_of_root:
  ∀ ρ f v, node (forest_merge ρ f) v → v ∉ dom f → v ≠ ρ → ∃ (c : V) (ct : tree V), f !! c = Some ct ∧ node ct v
    

    eapply tree_wf_internal_ind; last eauto. clear ρ t H0.

  Lemma tree_insert_wf ρ t r rt π πC :
    tree_wf ρ t → tree_wf r rt → t ##ₘ rt →
    t !! π = Some πC →
    tree_wf ρ (tree_insert t r rt π πC).
  Proof.
    intros Ht. revert r rt π πC. induction Ht; intros. subst.
    (* Case analysis on where π belongs: π = ρ or π is internal *)
    

  Definition tree_insert t r rt π πC : tree V := <[π:={[r]} ∪ πC]>(<[r:=rt]>t).

  TODO

  Lemma descendants_unique g v Δ1 Δ2 :
    descendants g v Δ1 → descendants g v Δ2 → Δ1 = Δ2.
  Proof using.
    intros Hd1. revert Δ2. induction Hd1. intros ? Hd2.
    inv Hd2. replace cds0 with cds; first auto.
    apply map_eq. intros i. destruct (out_edges g v !! i) eqn:Hi.
    - assert (Hiin' : i ∈ dom (out_edges g v)) by (by apply elem_of_dom).
      assert (Hiin : i ∈ children g v) by auto. clear Hiin'.
      assert (is_Some (cds !! i)).
      { destruct (cds !! i) eqn:Hcds; auto. exfalso.
        apply not_elem_of_dom in Hcds. rewrite -H0 in Hiin.  auto. }
      assert (is_Some (cds0 !! i)).
      { destruct (cds0 !! i) eqn:Hcds0; auto. exfalso.
        apply not_elem_of_dom in Hcds0. rewrite -H4 in Hiin. auto. }
      destruct H1, H5. specialize (H2 _ _ H1). specialize (H6 _ _ H5).
      rewrite H1 H5. f_equal. eapply H3; eauto.
    - assert (Hiin' : i ∉ dom (out_edges g v)) by (by apply not_elem_of_dom).
      assert (Hiin : i ∉ children g v) by auto. clear Hiin'.
      assert (cds !! i = None).
      { destruct (cds !! i) eqn:Hcds; auto. exfalso. apply Hiin. rewrite -H0. by apply elem_of_dom. }
      assert (cds0 !! i = None).
      { destruct (cds0 !! i) eqn:Hcds; auto. exfalso. apply Hiin. rewrite -H4. by apply elem_of_dom. }
      rewrite H1 H5. auto.
  Qed.

  Lemma descendants_exists g v :
    cgraph_wf g → ∃ Δ, descendants g v Δ.
  Proof using.
    intros Ht. pattern v. revert v. eapply (cgraph_ind'' (λ _ _, True)); first eauto.
    intros v Hind _.
    assert (∃ (cds : forest V), dom (out_edges g v) = dom cds ∧ (∀ c cd, cds !! c = Some cd → descendants g c cd)); cycle 1.
    { destruct H0 as (?&?&?). eexists. econstructor; eauto. }
    remember (out_edges g v) as c.
    assert (Hind2 : ∀ y, is_Some (c !! y) → ∃ Δ, descendants g y Δ).
    { intros. eapply Hind; eauto. rewrite /edge. by subst. }
    clear Heqc Hind. revert Hind2. induction c using map_ind; intros Hind0.
    { exists ∅. split; first auto. by intros. }
    assert (∀ y : V, is_Some (m !! y) → ∃ Δ : gset V, descendants g y Δ).
    { intros. eapply Hind0. apply lookup_insert_is_Some'. by right. }
    specialize (IHc H1). clear H1. destruct IHc as (cds&?&?).
    destruct (Hind0 i); first by rewrite lookup_insert_eq.
    exists (<[i:=x0]>cds). split.
    { set_solver. }
    { intros. destruct (decide (c = i)).
      - subst. rewrite lookup_insert_eq in H4. inv H4. auto.
      - rewrite lookup_insert_ne in H4; auto.
    }
  Qed.

  Lemma child_elem_of_descendants g v π Δ :
    parent g v π → descendants g π Δ → v ∈ Δ.
  Proof using.
    intros Hp Hd. inv Hd. assert (Hin : is_Some (cds !! v)).
    { destruct (cds !! v) eqn:Hcds; auto. exfalso.
      apply not_elem_of_dom in Hcds. rewrite H0 in Hcds. set_solver. }
    clear Hp H0 H2 π g. revert v Hin. induction cds using map_ind; intros.
    { exfalso. destruct Hin. set_solver. }
    destruct Hin. destruct (decide (v = i)).
    - subst. rewrite lookup_insert_eq in H1. inv H1.
      rewrite forest_fold_insert_L; auto. set_solver.
    - rewrite lookup_insert_ne in H1; auto. rewrite forest_fold_insert_L; auto. set_solver.
  Qed.

  Lemma descendant_of_parent g v π :
    cgraph_wf g → parent g v π → descendant g π v.
  Proof using.
    intros Hcwf Hp. destruct (descendants_exists _ π Hcwf) as [Δ Hd].
    exists Δ. split; first auto. eapply child_elem_of_descendants; eauto.
  Qed.

  Lemma elem_of_descendants_internal g v Δ :
    descendants g v Δ → ∀ u, u ∈ Δ → ∃ π, parent g u π.
  Proof using.
    intros Hd. induction Hd. intros. subst.
    destruct (decide (u ∈ children g v)); eauto.
    rewrite -H0 in n. destruct (forest_fold_internal_elem_of _ _ H4 n) as (c&cd&?&?).
    eapply (H3 _ _ H1 _ H5).
  Qed.

  Lemma root_not_elem_of_descendants g v :
    root g v → ∀ u Δ, descendants g u Δ → ¬ v ∈ Δ.
  Proof using.
    intros. intro Hf. pose proof (elem_of_descendants_internal _ _ _ H1 _ Hf).
    apply internal_not_root in H2; auto.
  Qed.
  Lemma root_not_descendant g v :
    root g v → ∀ u, ¬ descendant g u v.
  Proof using.
    intros. intros (?&Hd0&Hin). eapply root_not_elem_of_descendants; eauto.
  Qed.

  Lemma descendant_descendants_subseteq g ρ v Δ1 :
    descendant g ρ v → descendants g ρ Δ1 → ∃ Δ2, descendants g v Δ2 ∧ Δ2 ⊆ Δ1.
  Proof using.
    unfold descendant. intros (Δ&Hr1&Hvr) Hr2.
    pose proof (descendants_unique _ _ _ _ Hr1 Hr2). subst. clear Hr2.
    revert v Hvr. induction Hr1; intros.
    destruct (decide (v0 ∈ children g v)).
    - rewrite -H0 in e. apply elem_of_dom in e. destruct e as (Δ2&Hv0). exists Δ2. split; first by apply H2.
      subst. eapply forest_fold_descendants_subseteq; eauto.
    - pose proof (forest_fold_internal_elem_of v0 cds). destruct H4.
      { by subst. }
      { by rewrite H0. }
      destruct H4 as (cd&?&?). specialize (H3 _ _ H4 _ H5). destruct H3 as (Δ2&?&?).
      exists Δ2. split; first auto. etransitivity; first eauto.
      subst. eapply forest_fold_descendants_subseteq; eauto.
  Qed.

  Lemma descendant_parent_descendant g ρ π v :
    descendant g ρ π → parent g v π → descendant g ρ v.
  Proof using.
    unfold descendant. intros (Δ&Hr&Hpd) Hp. exists Δ. split; first auto.
    pose proof (descendant_descendants_subseteq g ρ π Δ). destruct H0; auto.
    { exists Δ. split; auto. }
    destruct H0. assert (v ∈ x).
    { eapply child_elem_of_descendants; eauto. }
    set_solver.
  Qed.

End tree.

Notation forest V := (gmap V (gset V)).

Section forest_fold.
  Context {V : Type}.
  Context `{Countable V}.
  Implicit Type f : forest V.

  Definition forest_fold f : gset V := map_fold (λ ρ Δ s, {[ρ]} ∪ Δ ∪ s) ∅ f.

  Lemma forest_fold_internal_elem_of u f :
    u ∈ forest_fold f →
    u ∉ dom f →
    ∃ ρ Δ, f !! ρ = Some Δ ∧ u ∈ Δ.
  Proof using.
    unfold forest_fold.
    revert u. induction f using map_ind; intros.
    { exfalso. rewrite map_fold_empty in H0. set_solver. }
    rewrite map_fold_insert_L in H1; auto.
    2:{ intros. set_solver. }
    rewrite dom_insert in H2. apply not_elem_of_union in H2. destruct H2.
    apply elem_of_union in H1. destruct H1.
    - apply elem_of_union in H1. destruct H1; first set_solver.
      exists i, x. rewrite lookup_insert_eq. auto.
    - apply IHf in H1; last auto. destruct H1 as (c&cd&?&?).
      exists c, cd. rewrite lookup_insert_ne / split; auto.
      set_solver.
  Qed.

  Lemma forest_fold_descendants_subseteq f ρ Δ :
    f !! ρ = Some Δ → Δ ⊆ forest_fold f.
  Proof using.
    unfold forest_fold.
    intros. assert (f = ({[ρ := Δ]} ∪ delete ρ f)).
    { apply map_eq. intros. destruct (decide (i = ρ)).
      - subst. rewrite lookup_union_l.
        + by rewrite H0 lookup_singleton_eq.
        + by rewrite lookup_delete_eq.
      - rewrite lookup_union_r.
        + rewrite lookup_delete_ne; done.
        + by rewrite lookup_singleton_ne.
    }
    rewrite H1. rewrite map_fold_disj_union.
    - rewrite map_fold_singleton. set_solver.
    - unfold map_disjoint, map_relation. intros. destruct (decide (i = ρ)).
      + subst. rewrite lookup_singleton_eq lookup_delete_eq. done.
      + rewrite lookup_singleton_ne; auto. rewrite lookup_delete_ne; auto. destruct (f !! i); done.
    - intros. set_solver.
  Qed.

  Lemma forest_fold_insert_L f ρ Δ :
    f !! ρ = None → forest_fold (<[ρ := Δ]>f) = {[ρ]} ∪ Δ ∪ (forest_fold f).
  Proof using.
    unfold forest_fold. intros. rewrite map_fold_insert_L; auto.
    intros. set_solver.
  Qed.

End forest_fold.

Section tree.
  Context {V : Type}.
  Context `{Countable V}.
  Context `{SI : indexT} {L : ofe}.
  Implicit Type g : cgraph V L.
  Implicit Type v u π : V.

  (** Basic definitions *)
  Definition children g v : gset V := dom (out_edges g v).
  Definition parent g (v π : V) : Prop := v ∈ children g π.
  Definition root g v : Prop := ∀ u, v ∉ children g u.
  Definition internal g v : Prop := ∃ π, parent g v π.

  Inductive descendants g : V → gset V → Prop :=
  | descendants_children v Δ (cds : forest V) :
    dom cds = children g v →
    Δ = forest_fold cds →
    (∀ c cd, cds !! c = Some cd → descendants g c cd) →
    descendants g v Δ.
  Definition descendant g : relation V := λ v u, ∃ Δ, descendants g v Δ ∧ u ∈ Δ.

  (** Properties *)
  Lemma parent_edge g v π :
    parent g v π ↔ edge g π v.
  Proof using. rewrite /parent /edge /children. apply elem_of_dom. Qed.

  Instance map_Exists_out_edges_Decision v : ∀ g, Decision (map_Exists (λ u _, v ∈ dom (out_edges g u)) g).
  Proof using. intros. eapply map_Exists_dec. intros. solve_decision. Qed.
  Instance exists_out_edges_Decision g : ∀ v, Decision (∃ u, v ∈ dom (out_edges g u)).
  Proof using.
    intros. destruct (map_Exists_out_edges_Decision v g).
    - left. destruct m as (?&?&?&?). eauto.
    - right. intros [u Hu]. apply n. exists u. pose proof Hu. apply elem_of_dom in Hu. destruct Hu.
      unfold out_edges in H1. destruct (g !! u); eauto.
      set_solver + H1.
  Qed.

  Lemma root_not_internal g v :
    root g v ↔ (∀ π, ¬ parent g v π).
  Proof using.
    rewrite /root /parent /children. split; intros; auto.
  Qed.
  Lemma internal_not_root g v :
    internal g v ↔ ¬ root g v.
  Proof using.
    rewrite /root /internal /parent /children. split; intros.
    - destruct H0. eauto.
    - destruct (decide (∃ u, v ∈ dom (out_edges g u))); eauto.
      exfalso. apply H0. intros u Hu. apply n. eauto.
  Qed.

  Global Instance internal_Decision g : ∀ v, Decision (internal g v).
  Proof using.
    intros. unfold internal, parent, children. apply _.
  Qed.
  Global Instance root_Decision g : ∀ v, Decision (root g v).
  Proof using.
    intros. destruct (decide (internal g v)).
    - apply internal_not_root in i. by right.
    - left. apply root_not_internal. intros π Hp. apply n. exists π. auto.
  Qed.

  Lemma children_parent g v π :
    v ∈ children g π ↔ parent g v π.
  Proof using. done. Qed.

  Lemma descendants_unique g v Δ1 Δ2 :
    descendants g v Δ1 → descendants g v Δ2 → Δ1 = Δ2.
  Proof using.
    intros Hd1. revert Δ2. induction Hd1. intros ? Hd2.
    inv Hd2. replace cds0 with cds; first auto.
    apply map_eq. intros i. destruct (out_edges g v !! i) eqn:Hi.
    - assert (Hiin' : i ∈ dom (out_edges g v)) by (by apply elem_of_dom).
      assert (Hiin : i ∈ children g v) by auto. clear Hiin'.
      assert (is_Some (cds !! i)).
      { destruct (cds !! i) eqn:Hcds; auto. exfalso.
        apply not_elem_of_dom in Hcds. rewrite -H0 in Hiin.  auto. }
      assert (is_Some (cds0 !! i)).
      { destruct (cds0 !! i) eqn:Hcds0; auto. exfalso.
        apply not_elem_of_dom in Hcds0. rewrite -H4 in Hiin. auto. }
      destruct H1, H5. specialize (H2 _ _ H1). specialize (H6 _ _ H5).
      rewrite H1 H5. f_equal. eapply H3; eauto.
    - assert (Hiin' : i ∉ dom (out_edges g v)) by (by apply not_elem_of_dom).
      assert (Hiin : i ∉ children g v) by auto. clear Hiin'.
      assert (cds !! i = None).
      { destruct (cds !! i) eqn:Hcds; auto. exfalso. apply Hiin. rewrite -H0. by apply elem_of_dom. }
      assert (cds0 !! i = None).
      { destruct (cds0 !! i) eqn:Hcds; auto. exfalso. apply Hiin. rewrite -H4. by apply elem_of_dom. }
      rewrite H1 H5. auto.
  Qed.

  Lemma descendants_exists g v :
    cgraph_wf g → ∃ Δ, descendants g v Δ.
  Proof using.
    intros Ht. pattern v. revert v. eapply (cgraph_ind'' (λ _ _, True)); first eauto.
    intros v Hind _.
    assert (∃ (cds : forest V), dom (out_edges g v) = dom cds ∧ (∀ c cd, cds !! c = Some cd → descendants g c cd)); cycle 1.
    { destruct H0 as (?&?&?). eexists. econstructor; eauto. }
    remember (out_edges g v) as c.
    assert (Hind2 : ∀ y, is_Some (c !! y) → ∃ Δ, descendants g y Δ).
    { intros. eapply Hind; eauto. rewrite /edge. by subst. }
    clear Heqc Hind. revert Hind2. induction c using map_ind; intros Hind0.
    { exists ∅. split; first auto. by intros. }
    assert (∀ y : V, is_Some (m !! y) → ∃ Δ : gset V, descendants g y Δ).
    { intros. eapply Hind0. apply lookup_insert_is_Some'. by right. }
    specialize (IHc H1). clear H1. destruct IHc as (cds&?&?).
    destruct (Hind0 i); first by rewrite lookup_insert_eq.
    exists (<[i:=x0]>cds). split.
    { set_solver. }
    { intros. destruct (decide (c = i)).
      - subst. rewrite lookup_insert_eq in H4. inv H4. auto.
      - rewrite lookup_insert_ne in H4; auto.
    }
  Qed.

  Lemma child_elem_of_descendants g v π Δ :
    parent g v π → descendants g π Δ → v ∈ Δ.
  Proof using.
    intros Hp Hd. inv Hd. assert (Hin : is_Some (cds !! v)).
    { destruct (cds !! v) eqn:Hcds; auto. exfalso.
      apply not_elem_of_dom in Hcds. rewrite H0 in Hcds. set_solver. }
    clear Hp H0 H2 π g. revert v Hin. induction cds using map_ind; intros.
    { exfalso. destruct Hin. set_solver. }
    destruct Hin. destruct (decide (v = i)).
    - subst. rewrite lookup_insert_eq in H1. inv H1.
      rewrite forest_fold_insert_L; auto. set_solver.
    - rewrite lookup_insert_ne in H1; auto. rewrite forest_fold_insert_L; auto. set_solver.
  Qed.

  Lemma descendant_of_parent g v π :
    cgraph_wf g → parent g v π → descendant g π v.
  Proof using.
    intros Hcwf Hp. destruct (descendants_exists _ π Hcwf) as [Δ Hd].
    exists Δ. split; first auto. eapply child_elem_of_descendants; eauto.
  Qed.

  Lemma elem_of_descendants_internal g v Δ :
    descendants g v Δ → ∀ u, u ∈ Δ → ∃ π, parent g u π.
  Proof using.
    intros Hd. induction Hd. intros. subst.
    destruct (decide (u ∈ children g v)); eauto.
    rewrite -H0 in n. destruct (forest_fold_internal_elem_of _ _ H4 n) as (c&cd&?&?).
    eapply (H3 _ _ H1 _ H5).
  Qed.

  Lemma root_not_elem_of_descendants g v :
    root g v → ∀ u Δ, descendants g u Δ → ¬ v ∈ Δ.
  Proof using.
    intros. intro Hf. pose proof (elem_of_descendants_internal _ _ _ H1 _ Hf).
    apply internal_not_root in H2; auto.
  Qed.
  Lemma root_not_descendant g v :
    root g v → ∀ u, ¬ descendant g u v.
  Proof using.
    intros. intros (?&Hd0&Hin). eapply root_not_elem_of_descendants; eauto.
  Qed.

  Lemma descendant_descendants_subseteq g ρ v Δ1 :
    descendant g ρ v → descendants g ρ Δ1 → ∃ Δ2, descendants g v Δ2 ∧ Δ2 ⊆ Δ1.
  Proof using.
    unfold descendant. intros (Δ&Hr1&Hvr) Hr2.
    pose proof (descendants_unique _ _ _ _ Hr1 Hr2). subst. clear Hr2.
    revert v Hvr. induction Hr1; intros.
    destruct (decide (v0 ∈ children g v)).
    - rewrite -H0 in e. apply elem_of_dom in e. destruct e as (Δ2&Hv0). exists Δ2. split; first by apply H2.
      subst. eapply forest_fold_descendants_subseteq; eauto.
    - pose proof (forest_fold_internal_elem_of v0 cds). destruct H4.
      { by subst. }
      { by rewrite H0. }
      destruct H4 as (cd&?&?). specialize (H3 _ _ H4 _ H5). destruct H3 as (Δ2&?&?).
      exists Δ2. split; first auto. etransitivity; first eauto.
      subst. eapply forest_fold_descendants_subseteq; eauto.
  Qed.

  Lemma descendant_parent_descendant g ρ π v :
    descendant g ρ π → parent g v π → descendant g ρ v.
  Proof using.
    unfold descendant. intros (Δ&Hr&Hpd) Hp. exists Δ. split; first auto.
    pose proof (descendant_descendants_subseteq g ρ π Δ). destruct H0; auto.
    { exists Δ. split; auto. }
    destruct H0. assert (v ∈ x).
    { eapply child_elem_of_descendants; eauto. }
    set_solver.
  Qed.

End tree.

Section operations.
  Context {V : Type}.
  Context `{Countable V}.
  Context `{SI : indexT} {L : ofe}.
  Implicit Type g : cgraph V L.
  Implicit Type v u π : V.

  (** Operations *)
  (* Correct only if v is fresh *)
  Definition alloc_root g v : cgraph V L := <[v:=∅]>g.

  Lemma alloc_root_delete_edge_eq g v u :
    v ∉ dom g →
    alloc_root g v = delete_edge g v u.
  Proof using.
    intros Hf. unfold alloc_root, delete_edge.
    assert (∀ x, out_edges g v !! x = None).
    { intros. unfold out_edges. apply not_elem_of_dom in Hf. rewrite Hf. done. }
    rewrite delete_id; last eauto.
    unfold out_edges. apply not_elem_of_dom in Hf. rewrite Hf. done.
  Qed.

  Lemma alloc_root_wf g v :
    v ∉ dom g →
    cgraph_wf g → cgraph_wf (alloc_root g v).
  Proof using.
    intros Hf Hw. rewrite (alloc_root_delete_edge_eq _ _ v); last auto.
    apply delete_edge_wf. auto.
  Qed.

  (** Tree well-formedness *)
  (* Different trees (roots) are not connected (¬ uconn),
     so a root can be inserted to a different tree *)
  Definition tree_wf g : Prop := ∀ v π1 π2, parent g v π1 → parent g v π2 → π1 = π2.

End operations.

Section forest.
  Context {V : Type}.
  Context `{Countable V}.
  Context `{SI : indexT} {L : ofe}.
  Implicit Type g : cgraph V L.
  Implicit Type v u π ρ : V.
  Implicit Type f : forest V.

  Definition forest_wf g : forest V → Prop :=
    λ f, map_Forall (λ ρ Δ, root g ρ ∧ descendants g ρ Δ) f ∧ dom g = forest_fold f.

  (* Operations are valid only under certain conditions *)
  Definition make_root f ρ : forest V := <[ρ:=∅]>f.
  Definition insert_tree f r D ρ Δ : forest V := <[ρ:=Δ ∪ {[r]} ∪ D]>(delete r f).
  Definition clear_root f ρ (Ch : forest V) : forest V := (<[ρ:=∅]>f) ∪ Ch.

  Lemma empty_forest_wf : forest_wf ∅ ∅.
  Proof using. unfold forest_wf, forest_fold. rewrite map_fold_empty dom_empty_L. split; done. Qed.

  Lemma insert_tree_wf g f π r l D ρ Δ :
    forest_wf g f →
    root g r → descendants g r D →
    root g ρ → descendants g ρ Δ → (π = ρ ∨ descendant g ρ π) →
    forest_wf (insert_edge g π r l) (insert_tree f r D ρ Δ).
  Proof.
    

End forest.

(* otree:
alloc one root (alloc obl),
insert one edge (suspend one),
delete many edges (resolve obl = delete children edges),
tree_wf gives uconn that is needed for insert_edge_wf
 *)
(* insert_edge_wf: *)
(*   ∀ {V : Type} {EqDecision0 : EqDecision V} {H : Countable V} {SI : indexT} {L : ofe} (g : cgraph V L) (v1 v2 : V) (l : L), *)
(*     ¬ uconn g v1 v2 → cgraph_wf g → cgraph_wf (insert_edge g v1 v2 l) *)
(* delete_edge_wf: *)
(*   ∀ {V : Type} {EqDecision0 : EqDecision V} {H : Countable V} {SI : indexT} {L : ofe} (g : cgraph V L) (v1 v2 : V), *)
(*     cgraph_wf g → cgraph_wf (delete_edge g v1 v2) *)
