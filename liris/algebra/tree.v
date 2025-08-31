From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From liris.cgraphs Require Export cgraph.
From liris.cgraphs Require Import mapexcl.

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

End forest_pre.

Section tree.
  Context {V : Type}.
  Context `{Countable V}.
  Implicit Type t : tree V.
  Implicit Type f : forest V.
  Implicit Type v u ρ π : V.
  Implicit Type C : gset V.

  (** Basic definitions *)
  Definition children t π C : Prop := t !! π = Some C.
  Definition parent t : relation V := λ v π, ∃ C, children t π C ∧ v ∈ C.
  Definition internal t v : Prop := ∃ π, parent t v π.
  Definition root t ρ : Prop := ∀ π, ¬ parent t ρ π.

  Global Instance children_Decision t : ∀ π C, Decision (children t π C).
  Proof using.
    intros. unfold children. apply _.
  Qed.
  Instance parent_Decision_aux t v π : Decision (map_Exists (λ u C, u = π ∧ v ∈ C) t).
  Proof using. eapply map_Exists_dec. intros. solve_decision. Qed.
  Global Instance parent_Decision t : ∀ v π, Decision (parent t v π).
  Proof using.
    intros. unfold parent, children. destruct (parent_Decision_aux t v π).
    - left. destruct m as (?&?&?&?&?). subst. eauto.
    - right. intros (C&Hlu&Helem). apply n. exists π, C. auto.
  Qed.
  Global Instance internal_Decision t : ∀ v, Decision (internal t v).
  Proof using.
    intros. unfold internal, parent, children. apply _.
  Qed.
  Global Instance root_Decision t : ∀ v, Decision (root t v).
  Proof using.
    intros. unfold root. destruct (internal_Decision t v).
    - right. intros F. destruct i. apply (F x). auto.
    - left. intros π Hp. apply n. exists π. auto.
  Qed.

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
  Proof using. rewrite /root /internal /parent /children. firstorder. Qed.
  Lemma internal_not_root t v :
    internal t v ↔ ¬ root t v.
  Proof using.
    split; intros.
    - intros F. apply root_not_internal in F. done.
    - destruct (decide (internal t v)); auto. by apply root_not_internal in n.
  Qed.

  Lemma children_unique t π C1 C2 : children t π C1 → children t π C2 → C1 = C2.
  Proof using. unfold children. intros. rewrite H0 in H1. inv H1. done. Qed.

  Lemma children_parent t v π C :
    children t π C → (v ∈ C ↔ parent t v π).
  Proof using.
    intros. split; intros.
    - exists C. done.
    - destruct H1 as (?&?&?). pose proof (children_unique _ _ _ _ H0 H1). by subst.
  Qed.

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
  Lemma forest_fold_keeps_parent t v π Cf r :
    parent t v π → Cf !! r = Some t → forest_disjoint Cf →
    parent (forest_fold Cf) v π.
  Proof using.
    rewrite /parent. intros. destruct H0 as (?&?&?).
    pose proof (forest_fold_keeps_children _ _ _ _ _ H0 H1 H2). eauto.
  Qed.
  Lemma forest_fold_keeps_internal t v Cf r :
    internal t v → Cf !! r = Some t → forest_disjoint Cf →
    internal (forest_fold Cf) v.
  Proof using.
    rewrite /internal. intros. destruct H0 as (?&?).
    pose proof (forest_fold_keeps_parent _ _ _ _ _ H0 H1 H2). eauto.
  Qed.

  Lemma forest_merge_keeps_children t π C Cf r ρ D :
    children t π C → Cf !! r = Some t → forest_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    children (<[ρ:=D]>(forest_fold Cf)) π C.
  Proof using.
    intros. pose proof (forest_fold_keeps_children _ _ _ _ _ H0 H1 H2).
    unfold children in H4. unfold children. rewrite lookup_insert_ne; first eauto.
    intro F. subst. rewrite H3 in H4. done.
  Qed.
  Lemma forest_merge_keeps_parent t v π Cf r ρ D :
    parent t v π → Cf !! r = Some t → forest_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    parent (<[ρ:=D]>(forest_fold Cf)) v π.
  Proof using.
    rewrite /parent. intros. destruct H0 as (?&?&?).
    pose proof (forest_merge_keeps_children _ _ _ _ _ _ D H0 H1 H2 H3). eauto.
  Qed.
  Lemma forest_merge_keeps_internal t v Cf r ρ D :
    internal t v → Cf !! r = Some t → forest_disjoint Cf →
    (forest_fold Cf) !! ρ = None →
    internal (<[ρ:=D]>(forest_fold Cf)) v.
  Proof using.
    rewrite /internal. intros. destruct H0 as (?&?).
    pose proof (forest_merge_keeps_parent _ _ _ _ _ _ D H0 H1 H2 H3). eauto.
  Qed.

  Lemma tree_wf_not_root_internal t ρ v :
    tree_wf ρ t → v ∈ dom t → v ≠ ρ → internal t v.
  Proof using.
    intros Ht. revert v. induction Ht; intros. subst.
    assert (v ∈ dom (forest_fold Cf)).
    { rewrite dom_insert_L in H6. apply elem_of_union in H6. destruct H6; set_solver. }
    (* FIXME: Error: Cannot infer an instance of type "tree V" for the variable t in context *)
    (* destruct (decide (v ∈ (dom Cf))). *)
    destruct (decide (v ∈ (dom Cf : gset V))).
    - pose proof e as ?. apply elem_of_dom in e. destruct e. exists ρ, (dom Cf). split; auto.
      by rewrite /children lookup_insert_eq.
    - pose proof (forest_fold_internal_elem_of _ _ H0 n). destruct H8 as (?&?&?&?).
      assert (v ≠ x).
      { intros ->. apply not_elem_of_dom in n. by rewrite n in H8. }
      specialize (H5 _ _ H8 _ H9 H10). eapply forest_merge_keeps_internal; eauto.
  Qed.

  Lemma tree_wf_root_elem t ρ : tree_wf ρ t → ρ ∈ dom t.
  Proof using. intros. inv H0. rewrite dom_insert. set_solver. Qed.

  Lemma tree_wf_root_unique t ρ1 ρ2 : tree_wf ρ1 t → tree_wf ρ2 t → ρ1 = ρ2.
  Proof using.
    intros. pose proof H0 as Htwf. inv H0. destruct (decide (ρ1 = ρ2)); first auto. exfalso.
    pose proof (tree_wf_not_root_internal _ _ ρ1 H1).
    eapply root_not_internal in H3. apply H3. apply H0; auto.
    apply tree_wf_root_elem. auto.
  Qed.

  Definition ancestor t : relation V := tc (parent t).

  (* Lemma internal_ancestor t ρ v : *)
  (*   tree_wf ρ t → internal t v → ancestor t v ρ. *)
  (* Proof using. *)
  (*   revert ρ v. induction t using map_ind; intros. *)
  (*   { destruct H1 as (?&?&?&?). done. } *)
    
  (*   destruct H1 as (?&?&?&?). *)


  (*   rewrite /ancestor /internal /parent /children. *)
  (*   revert ρ v. induction t using map_ind; intros. *)
  (*   { destruct H0 as (?&?&?&?). done. } *)
  (*   destruct H1 as (?&?&?&?). *)

  Global Instance children_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) children.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. unfold children. intros. eapply lookup_weaken; eauto.
  Qed.
  Global Instance parent_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) parent.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. intros (?&?&?). exists x. split; auto.
    eapply children_tree_subseteq_Proper; eauto.
  Qed.
  Global Instance ancestor_tree_subseteq_Proper : Proper ((⊆) ==> (=) ==> (=) ==> (→)) ancestor.
  Proof using.
    intros t1 t2 Hs ? v ? ? u ?. subst. intro Ha. revert t2 Hs. induction Ha; intros.
    { econstructor 1. destruct H0 as (?&?&?). exists x0. split; auto. eapply children_tree_subseteq_Proper; eauto. }
    econstructor 2.
    - eapply parent_tree_subseteq_Proper; eauto.
    - by eapply IHHa.
  Qed.

  Lemma tree_wf_descendant t ρ v :
    tree_wf ρ t → v ∈ dom t → ancestor t v ρ.
  Proof using.
    intro Ht. revert v. induction Ht; intros. destruct (Cf !! v) eqn:Hv.
    - specialize (H5 _ _ Hv).
      admit.
    - 

  Lemma tree_wf_far_descendant t ρ C v :
    tree_wf ρ t → t !! ρ = Some C → v ∉ C →
    ∃ c, c ∈ C ∧ ancestor t v c.
  Proof using.
    intro Ht. revert C v. induction Ht; intros.

  Lemma tree_wf_root_ancestor t ρ v :
    tree_wf ρ t → internal t v → ancestor t v ρ.
  Proof using.
    intros Ht. revert v. induction Ht; intros. destruct H6 as (π&?).
    destruct (decide (π = ρ)).
    { subst. by econstructor 1. }
    


    econstructor 2; first eauto.
    eapply H5.
    

  Lemma internal_cases t ρ v :
    tree_wf ρ t → internal t v → (parent t v ρ ∨ ∃ r rt, r ≠ ρ ∧ rt ⊆ t ∧ tree_wf r rt ∧ internal rt v).
  Proof.
    

  Lemma tree_wf_internal_ind (P : V → tree V → Prop) :
    (∀ ρ t (Cf : forest V),
       t = forest_merge ρ Cf →
       root t ρ →
       forest_fold Cf !! ρ = None →
       forest_disjoint Cf →
       map_Forall (λ (c : V) (ct : tree V), tree_wf c ct) Cf →
       (∀ (v : V) (s : tree V), internal t v → s ⊆ t → root s v → P v s) →
       P ρ t)
    → ∀ ρ (t : tree V), tree_wf ρ t → P ρ t.
  Proof using.
    intros Hind ? ? Ht. induction Ht. eapply Hind; eauto.
    subst. intros.

    tree_wf_ind:
  ∀ P : V → tree V → Prop,
    (∀ ρ t (Cf : forest V),
       t = forest_merge ρ Cf
       → root t ρ
         → forest_fold Cf !! ρ = None
           → forest_disjoint Cf
             → map_Forall (λ (c : V) (ct : tree V), tree_wf c ct) Cf → (∀ (i : V) (x : tree V), Cf !! i = Some x → P i x) → P ρ t)
    → ∀ v (g : tree V), tree_wf v g → P v g

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
