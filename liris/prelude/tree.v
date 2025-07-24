From stdpp Require Export list.

(** Reference: https://github.com/DmxLarchey/Kruskal-Trees/blob/main/theories/tree/ltree.v *)

Set Implicit Arguments.

Section tree.

  Variable A : Type.

  Unset Elimination Schemes.

  Inductive tree : Type :=
  | tree_cons : A → list tree → tree.

  Set Elimination Schemes.

  Definition tree_node t : A := match t with tree_cons x l => x end.
  Definition tree_children t : list tree := match t with tree_cons x l => l end.
  Definition tree_child : relation tree := λ s t, s ∈ tree_children t.

  Lemma tree_cons_inj : Inj2 eq eq eq tree_cons.
  Proof using. repeat intro. inv H. done. Qed.

  Inductive tree_elem_of : ElemOf A tree :=
  | tree_elem_of_here (x : A) s : x ∈ tree_cons x s
  | tree_elem_of_further (x y : A) t s : x ∈ t → t ∈ s → x ∈ tree_cons y s.
  Global Existing Instance tree_elem_of.

  Inductive subtree : relation tree :=
  | subtree_here s t : tree_child s t → subtree s t
  | subtree_further s t u : tree_child t u → subtree s t → subtree s u.

  Section tree_rect.

    Lemma tree_child_wf : well_founded tree_child.
    Proof using.
      unfold well_founded. fix Hfix 1. intros x.
      constructor. intros y Hs. destruct x. unfold tree_child in Hs. simpl in Hs.
      induction l.
      - inv Hs.
      - inv Hs.
        + apply Hfix.
        + apply (IHl H1).
    Qed.

    Definition tree_rect : ∀ (P : tree → Type), (∀ t, (∀ s, tree_child s t → P s) → P t) → ∀ (t : tree), P t :=
    λ (P : tree → Type) (f : ∀ t, (∀ s, tree_child s t → P s) → P t),
      well_founded_induction_type tree_child_wf P f.
    Definition tree_ind (P : _ → Prop) := tree_rect P.
    Definition tree_rec (P : _ → Set) := tree_rect P.

  End tree_rect.

  Lemma tree_child_Irreflexive : Irreflexive tree_child.
  Proof using. intros t. induction t. intro F. specialize (H t F F). done. Qed.
  Global Existing Instance tree_child_Irreflexive.

  Lemma subtree_alt s t u : subtree t u → tree_child s t → subtree s u.
  Proof using.
    intros Hs. revert s. induction Hs; intros.
    - econstructor 2; first eauto. econstructor 1; eauto.
    - econstructor 2; first eauto. eauto.
  Qed.

  Lemma subtree_Transitive : Transitive subtree.
  Proof using.
    repeat intro. revert x H. induction H0; intros.
    - econstructor 2; eauto.
    - econstructor 2; first eauto. eauto.
  Qed.
  Global Existing Instance subtree_Transitive.

  Lemma subtree_Irreflexive : Irreflexive subtree.
  Proof using.
    intro t. induction t. intro F. inv F.
    - apply tree_child_Irreflexive in H0. auto.
    - apply (H t0 H0). etransitivity; [|eauto]. econstructor 1; eauto.
  Qed.
  Global Existing Instance subtree_Irreflexive.

  Global Instance subtree_StrictOrder : StrictOrder subtree := Build_StrictOrder _ _ _.

  Section tree_eq_dec.

    Hypothesis A_eq_dec : forall x y : A, {x = y} + {x ≠ y}.

    Theorem tree_eq_dec (t1 t2 : tree) : {t1 = t2} + {t1 ≠ t2}.
    Proof using A_eq_dec.
      revert t2; induction t1 as [ [x xs] IH]; intros [y ys].
      destruct (A_eq_dec x y) as [ <- | H1 ].
      2:{ right. contradict H1. inv H1. auto. }
      revert IH ys. induction xs; intros.
      - destruct ys; auto.
      - destruct ys; auto.
        assert (Ha : tree_child a (tree_cons x (a :: xs))).
        { econstructor. }
        assert (IHxs0 : ∀ s : tree, tree_child s (tree_cons x xs) → ∀ t2 : tree, {s = t2} + {s ≠ t2}).
        { intros. apply IH. unfold tree_child in *. simpl in *. right; auto. }
        specialize (IHxs IHxs0); clear IHxs0.
        destruct (IH _ Ha t); clear Ha.
        + subst. destruct (IHxs ys).
          * inv e. auto.
          * right. intros F. apply n. inv F.
        + right. intros F. apply n. inv F.
    Qed.

  End tree_eq_dec.

  Section tree_op.

    Definition tree_singleton (x : A) : tree := tree_cons x [].

  End tree_op.

End tree.
