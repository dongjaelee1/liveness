From iris.proofmode Require Import proofmode.
From transfinite.base_logic Require Import upred.
From liris Require Import wf_structs.

Section measure_rep.
  Context `{SI: indexT} {M : ucmra}.
  Implicit Types φ : Prop.
  Implicit Types P Q : uPred M.
  Implicit Types A : Type.
  Local Arguments uPred_holds {_ _} !_ _ _ /.
  Local Hint Immediate uPred_in_entails : core.

  Import uPred_primitive.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (@uPred_entails SI M P%I Q%I) : stdpp_scope.
  Notation "(⊢)" := (@uPred_entails SI M) (only parsing) : stdpp_scope.
  Notation "P ⊣⊢ Q" := (@uPred_equiv SI M P%I Q%I) : stdpp_scope.
  Notation "(⊣⊢)" := (@uPred_equiv SI M) (only parsing) : stdpp_scope.

  Notation "'True'" := (uPred_pure True) : bi_scope.
  Notation "'False'" := (uPred_pure False) : bi_scope.
  Notation "'⌜' φ '⌝'" := (uPred_pure φ%type%stdpp) : bi_scope.
  Infix "∧" := uPred_and : bi_scope.
  Infix "∨" := uPred_or : bi_scope.
  Infix "→" := uPred_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (uPred_forall (λ x, .. (uPred_forall (λ y, P)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (uPred_exist (λ x, .. (uPred_exist (λ y, P)) ..)) : bi_scope.
  Infix "∗" := uPred_sep : bi_scope.
  Infix "-∗" := uPred_wand : bi_scope.
  Notation "□ P" := (uPred_persistently P) : bi_scope.
  Notation "■ P" := (uPred_plainly P) : bi_scope.
  Notation "x ≡ y" := (uPred_internal_eq x y) : bi_scope.
  Notation "▷ P" := (uPred_later P) : bi_scope.
  Notation "|==> P" := (uPred_bupd P) : bi_scope.

  Infix "<ₒ" := (ord_tree_lt) (at level 60).
  Notation ot := (ord_tree (index * M)%type).

  Lemma entails_measure_rep P (Q : ot → uPred M) : (P ⊢ ∃ o, Q o) → (∃ o1, (P ⊢ ∃ o0, Q o0 ∧ ⌜o0 <ₒ o1⌝)).
  Proof.
    unseal; intros HQ. inv HQ. simpl in *.
    assert (H : ∀ (nx : (index * M)%type) (SAT : (λ a, ✓{a.1} a.2 ∧ uPred_holds P a.1 a.2) nx),
              ∃ o, (λ b c, uPred_holds (Q c) b.1 b.2) nx o).
    { intros [n' x']. simpl. intros (H1&H2). apply uPred_in_entails; auto. }
    apply ord_tree_join in H. destruct H as [o H]. exists o.
    split=> n x ? //=H0. specialize (H (n, x)). simpl in H. destruct H; [auto|].
    exists x0. auto.
  Qed.

  Lemma impl_measure_rep P (Q : ot → uPred M) : (P → (∃ o, Q o)) ⊢ ∃ o1, (P → ∃ o0, Q o0 ∧ ⌜o0 <ₒ o1⌝).
  Proof.
    unseal; split=> n x ? //=H.
    assert (H' : ∀ (nx : (index * M)%type) (SAT : (λ a, x ≼ a.2 ∧ a.1 ⪯ᵢ n ∧ ✓{a.1} a.2 ∧ uPred_holds P a.1 a.2) nx),
              ∃ o, (λ b c, uPred_holds (Q c) b.1 b.2) nx o).
    { intros [n'' x'']. simpl. intros (H1&H2&H3&H4). apply H; auto. }
    apply ord_tree_join in H'. destruct H' as [o1 H']. exists o1.
    intros n' x'. specialize (H' (n', x')). simpl in H'. intros.
    destruct H'; [auto |]. exists x0. auto.
  Qed.

  Lemma wand_measure_rep P (Q : ot → uPred M) : (P -∗ (∃ o, Q o)) ⊢ ∃ o1, (P -∗ ∃ o0, Q o0 ∧ ⌜o0 <ₒ o1⌝).
  Proof.
    unseal; split=> n x ? //=H.
    assert (H' : ∀ (nx : (index * M)%type) (SAT : (λ a, a.1 ⪯ᵢ n ∧ ✓{a.1} (x ⋅ a.2) ∧ uPred_holds P a.1 a.2) nx),
              ∃ o, (λ b c, uPred_holds (Q c) b.1 (x ⋅ b.2)) nx o).
    { intros [n'' x'']. simpl. intros (H1&H2&H3). apply H; auto. }
    apply ord_tree_join in H'. destruct H' as [o1 H']. exists o1.
    intros n' x'. specialize (H' (n', x')). simpl in H'. intros.
    destruct H'; [auto |]. exists x0. auto.
  Qed.

  Lemma plainly_measure_rep (P : ot → uPred M) : ■ (∃ o, P o) ⊢ ∃ o, (■ P o).
  Proof.
    unseal; split=> n x ? //=H.
  Qed.

  Lemma persistently_measure_rep (P : ot → uPred M) : □ (∃ o, P o) ⊢ ∃ o, (□ P o).
  Proof.
    unseal; split=> n x ? //=H.
  Qed.

  Lemma later_measure_rep (P : ot → uPred M) : ▷ (∃ o, P o) ⊢ ∃ o1, ▷ (∃ o0, P o0 ∧ ⌜o0 <ₒ o1⌝).
  Proof.
    unseal; split=> n x ? //=H.
    assert (H' : ∀ (nx : (index * M)%type) (SAT : (λ a, a.1 ≺ᵢ n) nx),
              ∃ o, (λ b c, uPred_holds (P c) b.1 x) nx o).
    { intros [n'' x'']. simpl. intros H1. apply H; auto. }
    apply ord_tree_join in H'. destruct H' as [o1 H']. exists o1.
    intros n'. specialize (H' (n', x)). simpl in H'. intros.
    destruct H'; [auto |]. exists x0. auto.
  Qed.

  Lemma bupd_measure_rep (P : ot → uPred M) : (|==> (∃ o, P o)) ⊢ ∃ o1, |==> (∃ o0, P o0 ∧ ⌜o0 <ₒ o1⌝).
  Proof.
    unseal; split=> n x ? //=H.
    assert (H' : ∀ (nx : (index * M)%type) (SAT : (λ a, a.1 ⪯ᵢ n ∧ ✓{a.1} (x ⋅ a.2)) nx),
              ∃ o, (λ b c, ∃ x' : M, ✓{b.1} (x' ⋅ b.2) ∧ uPred_holds (P o) b.1 x') nx o).
    { intros [n'' x'']. simpl. intros (H1&H2). specialize (H _ _ H1 H2). destruct H as (?&?&?&?). eauto. }
    apply ord_tree_join in H'. destruct H' as [o1 H']. exists o1.
    intros k yf. specialize (H' (k, yf)). simpl in H'. intros.
    destruct H'; [auto |]. destruct H2 as ((?&?&?)&?). eauto.
  Qed.

End measure_rep.

Section logic.
  Context `{SI: indexT} {PROP : bi} {A : Type}.

  Infix "<ₒ" := (ord_tree_lt) (at level 60).
  Notation ot := (ord_tree (index * A)%type).

  Lemma mono_match_measure_rep (P : ot → PROP) o1 :
    (∀ o o', ⌜o <ₒ o'⌝ -∗ P o -∗ P o') ⊢ (∃ o0, P o0 ∧ ⌜o0 <ₒ o1⌝) -∗ P o1.
  Proof.
    iIntros "Hm (%o0&He&%Ho)". iApply "Hm".
    - iPureIntro. eauto.
    - iFrame.
  Qed.

End logic.
