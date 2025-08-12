From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From liris.cgraphs Require Export cgraph.
From liris.cgraphs Require Import mapexcl.

Section tree.
  Context {V : Type}.
  Context `{Countable V}.
  Context `{SI : indexT} {L : ofe}.
  Implicit Type t : cgraph V L.
  Implicit Type n : gmap V L.
  Implicit Type v u : V.

  Definition children t v : gmap V L := out_edges t v.
  Definition parent t (v π : V) : Prop := is_Some (children t π !! v).

  Definition root t v : Prop := in_labels t v ≡ ε.
  Definition internal t v : Prop := (∃ π, parent t v π).
  (* Definition internal t v : Prop := (∃ x, in_labels t v ≡ {[x]}). *)

  Inductive descendants t : V → (gset V) → Prop :=
  | descendants_child v Δ (cds : gmap V (gset V)) :
    dom (children t v) = dom cds →
    Δ = map_fold (λ c cd s, {[c]} ∪ cd ∪ s) ∅ cds →
    (∀ c cd, cds !! c = Some cd → descendants t c cd) →
    descendants t v Δ.
  Definition descendant t : relation V := λ v u, ∃ Δ, descendants t v Δ ∧ u ∈ Δ.

  (** Properties *)

  Lemma root_not_internal t v :
    root t v → ¬ internal t v.
  Proof using.
    rewrite /root /internal /parent /children.
    intros Hr [π [x Hi]]. eapply no_in_labels_no_out_edge in Hr. erewrite Hi in Hr. done.
  Qed.

  (* Lemma root_not_internal t v : *)
  (*   root t v ↔ ¬ internal t v. *)
  (* Proof using. *)
  (*   rewrite /root /internal /parent /children. split. *)
  (*   - intros Hr [π [x Hi]]. eapply no_in_labels_no_out_edge in Hr. erewrite Hi in Hr. done. *)
  (*   - revert v. induction t using map_ind; intros. *)
  (*     { done. } *)
  (*     destruct (decide (v = i)). *)
  (*     + subst. destruct (decide (x = ∅)). *)
  (*       * subst. rewrite in_labels_insert; auto. rewrite lookup_empty. simpl.  *)

  (*       exfalso. apply H1. exists i. rewrite out_edges_insert. *)
  (* Qed. *)

  Lemma internal_not_root t v :
    internal t v → ¬ root t v.
  Proof using.
    rewrite /root /internal /parent /children.
    intros [π [x Hi]] Hr. eapply no_in_labels_no_out_edge in Hr. erewrite Hi in Hr. done.
  Qed.

  Lemma children_parent t v π :
    is_Some (children t π !! v) ↔ parent t v π.
  Proof using. done. Qed.

  Lemma internal_parent_exists t v :
    internal t v → ∃ π, parent t v π.
  Proof using. done. Qed.
  (*   intros (?&Hl). destruct (in_labels_out_edges t v x ε); first done. *)
  (*   exists x0. rewrite /parent. by rewrite H0. *)
  (* Qed. *)

  Lemma descendants_unique t v Δ1 Δ2 :
    cgraph_wf t → descendants t v Δ1 → descendants t v Δ2 → Δ1 = Δ2.
  Proof using.
    intros Ht. revert Δ1 Δ2. pattern v. revert v. eapply (cgraph_ind'' (λ _ _, True)); first eauto.
    intros v Hind _ ? ? Hd1 Hd2.
    inv Hd1. inv Hd2. replace cds0 with cds; first auto.
    apply map_eq. intros i. destruct (out_edges t v !! i) eqn:Hi.
    - assert (Hiin : i ∈ dom (out_edges t v)) by (by apply elem_of_dom).
      assert (is_Some (cds !! i)).
      { destruct (cds !! i) eqn:Hcds; auto. exfalso.
        apply not_elem_of_dom in Hcds. rewrite H0 in Hiin. auto. }
      assert (is_Some (cds0 !! i)).
      { destruct (cds0 !! i) eqn:Hcds0; auto. exfalso.
        apply not_elem_of_dom in Hcds0. rewrite H1 in Hiin. auto. }
      destruct H3, H5. specialize (H2 _ _ H3). specialize (H4 _ _ H5).
      rewrite H3 H5. f_equal. eapply Hind; eauto. rewrite /edge. auto.
    - assert (Hiin : i ∉ dom (out_edges t v)) by (by apply not_elem_of_dom).
      assert (cds !! i = None).
      { destruct (cds !! i) eqn:Hcds; auto. exfalso. apply Hiin. rewrite H0. by apply elem_of_dom. }
      assert (cds0 !! i = None).
      { destruct (cds0 !! i) eqn:Hcds; auto. exfalso. apply Hiin. rewrite H1. by apply elem_of_dom. }
      rewrite H3 H5. auto.
  Qed.

  Lemma descendants_exists t v :
    cgraph_wf t → ∃ Δ, descendants t v Δ.
  Proof using.
    intros Ht. pattern v. revert v. eapply (cgraph_ind'' (λ _ _, True)); first eauto.
    intros v Hind _.
    assert (∃ (cds : gmap V (gset V)), dom (out_edges t v) = dom cds ∧ (∀ c cd, cds !! c = Some cd → descendants t c cd)); cycle 1.
    { destruct H0 as (?&?&?). eexists. econstructor; eauto. }
    remember (out_edges t v) as g.
    assert (Hind2 : ∀ y, is_Some (g !! y) → ∃ Δ, descendants t y Δ).
    { intros. eapply Hind; eauto. rewrite /edge. by subst. }
    clear Heqg Hind. revert Hind2. induction g using map_ind; intros Hind0.
    { exists ∅. split; first auto. by intros. }
    assert (∀ y : V, is_Some (m !! y) → ∃ Δ : gset V, descendants t y Δ).
    { intros. eapply Hind0. apply lookup_insert_is_Some'. by right. }
    specialize (IHg H1). clear H1. destruct IHg as (cds&?&?).
    destruct (Hind0 i); first by rewrite lookup_insert_eq.
    exists (<[i:=x0]>cds). split.
    { set_solver. }
    { intros. destruct (decide (c = i)).
      - subst. rewrite lookup_insert_eq in H4. inv H4. auto.
      - rewrite lookup_insert_ne in H4; auto.
    }
  Qed.

  Lemma child_elem_of_descendants t v π Δ :
    parent t v π → descendants t π Δ → v ∈ Δ.
  Proof using.
    intros [e He] Hd. inv Hd. assert (Hin : is_Some (cds !! v)).
    { destruct (cds !! v) eqn:Hcds; auto. exfalso.
      apply not_elem_of_dom in Hcds. apply elem_of_dom_2 in He. set_solver. }
    clear e He H0 H2 π t. revert v Hin. induction cds using map_ind; intros.
    { exfalso. destruct Hin. set_solver. }
    destruct Hin. destruct (decide (v = i)).
    - subst. rewrite lookup_insert_eq in H1. inv H1.
      rewrite map_fold_insert_L; auto.
      { set_solver. }
      intros. set_solver.
    - rewrite lookup_insert_ne in H1; auto. rewrite map_fold_insert_L; auto.
      { assert (is_Some (m !! v)) by auto. specialize (IHcds _ H2). set_solver. }
      intros. set_solver.
  Qed.

  Lemma descendant_of_parent t v π :
    cgraph_wf t → parent t v π → descendant t π v.
  Proof using.
    intros Hcwf [? He]. destruct (descendants_exists _ π Hcwf) as [Δ Hd]. exists Δ. split; first auto.
    eapply child_elem_of_descendants; eauto. by unfold parent.
  Qed.

  Lemma far_descendants_aux u cds :
    u ∈ map_fold (λ (c : V) (cd s : gset V), {[c]} ∪ cd ∪ s) ∅ cds →
    u ∉ dom cds →
    ∃ c cd, cds !! c = Some cd ∧ u ∈ cd.
  Proof using.
    revert u. induction cds using map_ind; intros.
    { exfalso. rewrite map_fold_empty in H0. set_solver. }
    rewrite map_fold_insert_L in H1; auto.
    2:{ intros. set_solver. }
    rewrite dom_insert in H2. apply not_elem_of_union in H2. destruct H2.
    apply elem_of_union in H1. destruct H1.
    - apply elem_of_union in H1. destruct H1; first set_solver.
      exists i, x. rewrite lookup_insert_eq. auto.
    - apply IHcds in H1; last auto. destruct H1 as (c&cd&?&?).
      exists c, cd. rewrite lookup_insert_ne / split; auto.
      set_solver.
  Qed.

  (* FIXME *)

(*   Lemma elem_of_descendants_internal t v Δ : *)
(*     descendants t v Δ → ∀ u, u ∈ Δ → internal t u. *)
(*   Proof using. *)
(*     intros Htwf Hd. induction Hd. intros. subst. rewrite /internal. *)
(*     destruct (decide (u ∈ dom (out_edges t v))). *)
(*     - apply elem_of_dom in e. destruct e. destruct (out_edges_in_labels_L t _ _ _ H1). *)
(*       destruct (Htwf u). *)
(*       + unfold root in H6. rewrite H6 in H5. exfalso. symmetry in H5. *)
(*         destruct (multiset_op_unit _ _ H5). by apply multiset_singleton_not_unit in H7. *)
(*       + destruct H6. eauto. *)
(*     - rewrite H0 in n. destruct (far_descendants_aux _ _ H4 n) as (c&cd&?&?). *)
(*       eapply (H3 _ _ H1 _ H5). *)
(*   Qed. *)

(*   Lemma root_not_elem_of_descendants t v : *)
(*     is_tree t → root t v → ∀ u Δ, descendants t u Δ → ¬ v ∈ Δ. *)
(*   Proof using. *)
(*     intros. intro Hf. pose proof (elem_of_descendants_internal _ _ _ H0 H2 _ Hf). *)
(*     apply root_not_internal in H1. auto. *)
(*   Qed. *)

(*   Lemma root_not_descendant t v : *)
(*     is_tree t → root t v → ∀ u, ¬ descendant t u v. *)
(*   Proof using. *)
(*     intros. intros (?&Hd0&Hin). eapply root_not_elem_of_descendants; eauto. *)
(*   Qed. *)

(*   (* Disjoint properties... *) *)
(*   Lemma descendants_disjoint t v1 v2 : *)
(*     cgraph_wf t → (v1 ≠ v2) → ∀ Δ1 Δ2, descendants t v1 Δ1 → descendants t v2 Δ2 → Δ1 ## Δ2. *)
(*   Proof. *)
    
(* move_edge_wf: *)
(*   ∀ {V : Type} {EqDecision0 : EqDecision V} {H : Countable V} {SI : indexT} {L : ofe} (g : cgraph V L) (v1 v2 v3 : V), *)
(*     v2 ≠ v3 → cgraph_wf g → sc (edge g) v1 v2 → cgraph_wf (move_edge g v1 v2 v3) *)
(* move_edge_wf': *)
(*   ∀ {V : Type} {EqDecision0 : EqDecision V} {H : Countable V} {SI : indexT} {L : ofe} (g : cgraph V L) (v1 v2 v3 : V), *)
(*     v2 ≠ v3 → cgraph_wf g → ¬ uconn g v1 v2 → cgraph_wf (move_edge g v1 v2 v3) *)
(* move_edge = *)
(* λ (V : Type) (EqDecision0 : EqDecision V) (H : Countable V) (SI : indexT) (L : ofe) (g : cgraph V L) (v1 v2 v3 : V), *)
(*   match out_edges g v1 !! v3 with *)
(*   | Some l => insert_edge (delete_edge g v1 v3) v2 v3 l *)
(*   | None => g *)
(*   end *)
(*      : ∀ {V : Type} {EqDecision0 : EqDecision V} {H : Countable V} {SI : indexT} {L : ofe}, cgraph V L → V → V → V → cgraph V L *)
(* cgraph_wf = *)
(* λ (V : Type) (EqDecision0 : EqDecision V) (H : Countable V) (SI : indexT) (L : ofe) (g : cgraph V L), *)
(*   no_short_loops g ∧ is_uforest (to_uforest g) *)
(*      : ∀ {V : Type} {EqDecision0 : EqDecision V} {H : Countable V} {SI : indexT} {L : ofe}, cgraph V L → Prop *)

End tree.
