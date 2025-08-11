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

  (* Definition node t v : Prop := is_Some (t !! v). *)
  Definition root t v : Prop := in_labels t v ≡ ε.
  Definition internal t v : Prop := (∃ x, in_labels t v ≡ {[x]}).
  (* Definition tree_wf t : Prop := cgraph_wf t ∧ (∀ v, node t v → (root t v ∨ internal t v)). *)

  Definition parent t (v π : V) : Prop := is_Some (out_edges t π !! v).

  Inductive descendants t : V → (gset V) → Prop :=
  | descendants_child v Δ (cds : gmap V (gset V)) :
    (* node t v → *)
    dom (out_edges t v) = dom cds →
    Δ = map_fold (λ _ cd s, cd ∪ s) ∅ cds →
    (∀ c cd, cds !! c = Some cd → descendants t c cd) →
    descendants t v Δ.
  Definition descendant t : relation V := λ v u, ∃ Δ, descendants t v Δ ∧ u ∈ Δ.

  (** Properties *)

  Lemma internal_parent_exists t v :
    internal t v → ∃ π, parent t v π.
  Proof using.
    intros (?&Hl). destruct (in_labels_out_edges t v x ε); first done.
    exists x0. rewrite /parent. by rewrite H0.
  Qed.

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

  Lemma descendant_of_parent t v π :
    parent t v π → descendant t π v.
  Proof.
    intros [? He]. 

End tree.
