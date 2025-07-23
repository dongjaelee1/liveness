From stdpp Require Export list.

(** Reference: https://github.com/DmxLarchey/Kruskal-Trees/blob/main/theories/tree/ltree.v *)

Set Implicit Arguments.

Section tree.

  Variable A : Type.

  Unset Elimination Schemes.

  Inductive tree : Type :=
  | tree_cons : A → list tree → tree.

  Set Elimination Schemes.

  Definition tree_node t := match t with tree_cons x l => x end.
  Definition tree_children t := match t with tree_cons x l => l end.
  Definition tree_child s t := s ∈ tree_children t.

  Lemma tree_cons_inj : Inj2 eq eq eq tree_cons.
  Proof using. repeat intro. inv H. done. Qed.

  Inductive tree_elem_of : ElemOf A tree :=
  | tree_elem_of_here (x : A) s : x ∈ tree_cons x s
  | tree_elem_of_further (x y : A) t s : x ∈ t → t ∈ s → x ∈ tree_cons y s.
  Global Existing Instance tree_elem_of.

  Section tree_rect.

    Lemma tree_child_wf : well_founded tree_child.
    Proof using.
      unfold well_founded. fix Hfix 1. intros x.
      constructor. intros y Hs. destruct x. unfold tree_child in Hs. simpl in Hs.
      induction l.
      - inversion Hs.
      - inversion Hs.
        + apply Hfix.
        + apply (IHl H1).
    Defined.

    Definition tree_rect : ∀ (P : tree → Type), (∀ t, (∀ s, tree_child s t → P s) → P t) → ∀ (t : tree), P t :=
    λ (P : tree → Type) (f : ∀ t, (∀ s, tree_child s t → P s) → P t),
      well_founded_induction_type tree_child_wf P f.
    Definition tree_ind (P : _ → Prop) := tree_rect P.
    Definition tree_rec (P : _ → Set) := tree_rect P.

  End tree_rect.

  Lemma tree_child_Irreflexive : Irreflexive tree_child.
  Proof using. intros t. induction t. intro F. specialize (H t F F). done. Qed.

  TODO

  Section tree_eq_dec.

    (** As an application of tree_rect, the discreteness of
        tree X follows from that of X *)

    Hypothesis eqX_dec : forall x y : X, { x = y } + { x <> y }.

    Theorem tree_eq_dec (t₁ t₂ : tree) : { t₁ = t₂ } + { t₁ <> t₂ }.
    Proof.
      revert t₂; induction t₁ as [ x ll IH ]; intros [ y mm ].
      destruct (eqX_dec x y) as [ <- | H1 ].
      2: now right; contradict H1; inversion H1.
      destruct (list_eq_dect ll mm) as [ <- | H2 ]; auto.
      now right; contradict H2; inversion H2.
    Qed.

  End tree_eq_dec.

  Section tree_recursion.

    (** A non-dependent recursor for trees, using a direct nested fixpoint,
        the nesting occurs with the external (list) map function *)

    Variable (Y : Type) (f : X -> list tree -> list Y -> Y).

    Fixpoint tree_recursion (t : tree) : Y :=
      match t with
        | ⟨x|l⟩ₗ => f x l (map tree_recursion l)
      end.

  End tree_recursion.

  Section tree_fall_exst.

    Variable (P Q : X -> list tree -> Prop).

    Definition tree_fall : tree -> Prop.
    Proof.
      induction 1 as [ x l lP ] using tree_recursion.
      exact (P x l /\ forall h, h ∈ lP -> h).
    Defined.

    Fact tree_fall_fix x l : tree_fall ⟨x|l⟩ₗ <-> P x l /\ forall t, t ∈ l -> tree_fall t.
    Proof.
      clear Q.
      simpl; apply and_equiv; try tauto; split.
      + intros H t Hl.
        apply H, in_map_iff; exists t; auto.
      + intros H h; rewrite in_map_iff.
        intros (t & <- & ?); auto.
    Qed.

    Definition tree_exst : tree -> Prop.
    Proof.
      induction 1 as [ x l lQ ] using tree_recursion.
      exact (Q x l \/ exists h, h ∈ lQ /\ h).
    Defined.

    Fact tree_exst_fix x l : tree_exst ⟨x|l⟩ₗ <-> Q x l \/ exists t, t ∈ l /\ tree_exst t.
    Proof.
      clear P.
      simpl; apply or_equiv; try tauto; split.
      + intros (? & (? & <- & ?)%in_map_iff & ?); eauto.
      + intros (t & H1 & H2).
        exists (tree_exst t); split; trivial.
        apply in_map_iff; eauto.
    Qed.

    Section tree_fall_rect.

      Variables (K : tree -> Type)
                (HK : forall x l, P x l
                               -> (forall t, t ∈ l -> tree_fall t)
                               -> (forall t, t ∈ l -> K t)
                               -> K ⟨x|l⟩ₗ).

      Theorem tree_fall_rect t : tree_fall t -> K t.
      Proof.
        induction t as [ x l IH ]; intros H.
        rewrite tree_fall_fix in H; destruct H; auto.
      Qed.

    End tree_fall_rect.

    Section tree_fall_exst.

      Hypothesis HPQ : forall x l, P x l \/ Q x l.

      Fact tree_fall_exst t : tree_fall t \/ tree_exst t.
      Proof.
        induction t as [ x l IH ].
        apply list_choice in IH as [ Hl | (t & Ht & Hl) ];
          [ destruct (HPQ x l) as [ H | H ] | ].
        1: left; apply tree_fall_fix; auto.
        all: right; apply tree_exst_fix; eauto.
      Qed.

    End tree_fall_exst.

    Section tree_fall_exst_t.

      Hypothesis HPQ : forall x l, { P x l } + { Q x l }.

      Fact tree_fall_exst_t t : { tree_fall t } + { tree_exst t }.
      Proof.
        induction t as [ x l IH ].
        apply list_choice_t in IH as [ Hl | (t & Ht & Hl) ];
          [ destruct (HPQ x l) as [ H | H ] | ].
        1: left; apply tree_fall_fix; auto.
        all: right; apply tree_exst_fix; eauto.
      Qed.

    End tree_fall_exst_t.

    Section tree_fall_exst_absurd.

      Hypothesis HPQ : forall x l, P x l -> Q x l -> False.

      Fact tree_fall_exst_absurd t : tree_fall t -> tree_exst t -> False.
      Proof.
        induction 1 as [ x l Hx Hl IHl ] using tree_fall_rect.
        intros [ | (? & ? & ?) ]%tree_exst_fix; eauto.
      Qed.

    End tree_fall_exst_absurd.

  End tree_fall_exst.

  Section tree_weight.

    Variable (w : X -> nat).

    Implicit Type l : list tree.

    Definition tree_weight : tree -> nat.
    Proof.
      apply tree_recursion.
      exact (fun x _ m => w x+list_sum (fun x => x) m).
    Defined.

    Fact tree_weight_fix x l : tree_weight ⟨x|l⟩ₗ = w x + list_sum tree_weight l.
    Proof.
      unfold tree_weight at 1; simpl; f_equal.
      clear x; induction l; simpl; auto.
    Qed.

    Fact tree_weight_0_fall t : tree_weight t = 0 -> tree_fall (fun x _ => w x = 0) t.
    Proof.
      induction t as [ x l IHl ]; rewrite tree_weight_fix, tree_fall_fix; split; tlia.
      intros t Ht.
      apply IHl; auto.
      generalize (list_sum_in tree_weight _ _ Ht); lia.
    Qed.

    Fact tree_weight_0_exst t : tree_weight t = 0 -> tree_exst (fun x _ => w x = 0) t.
    Proof. induction t; rewrite tree_weight_fix, tree_exst_fix; lia. Qed.

    Hypothesis (Hw : forall x, 0 < w x).

    Fact tree_weight_gt t : 0 < tree_weight t.
    Proof.
      destruct t as [ x l ]; rewrite tree_weight_fix.
      generalize (Hw x); lia.
    Qed.

  End tree_weight.

End tree.

Fact tree_fall_dec X (P : X -> list (tree X) -> Prop) :
        (forall x l, { P x l } + { ~ P x l })
     -> (forall t, { tree_fall P t } + { ~ tree_fall P t }).
Proof.
  intros H t.
  apply tree_fall_exst_t with (t := t) in H.
  destruct H as [ H | H ]; auto.
  right; intros H1; revert H1 H.
  apply tree_fall_exst_absurd; auto.
Qed.

Module tree_notations.

  Notation "⟨ x | l ⟩ₗ" := (tree_cons x l).

End tree_notations.

Import tree_notations.


