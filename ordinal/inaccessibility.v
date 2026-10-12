From lantana.ordinal Require Import sflib basics.
From lantana.ordinal Require Export ordinal arithmetic.

From Coq Require Import ChoiceFacts.

Set Implicit Arguments.
Set Primitive Projections.

Section INACCESSIBLE.
  Let flip A B C (f: A -> B -> C): B -> A -> C := fun b a => f a b.

  Record inaccessible (X: Type) (base: ord.t) (next: ord.t -> ord.t) (k: ord.t): Prop :=
    mk_inaccessible
      { inaccessible_base: ord.lt base k;
        inaccessible_next: forall o (LT: ord.lt o k), ord.lt (next o) k;
        inaccessible_join: forall (os: X -> ord.t) (LT: forall a, ord.lt (os a) k),
            ord.lt (ord.join os) k;
        inaccessible_union: forall o0 o1 (LT0: ord.lt o0 k) (LT1: ord.lt o1 k),
            ord.lt (ord.union o0 o1) k;
      }.

  Lemma inaccessible_mon X0 X1 base0 base1 next0 next1 k
        (SURJ: exists (f: X1 -> X0), forall x0, exists x1, f x1 = x0)
        (BASE: ord.lt base0 k)
        (NEXT: forall o (LT: ord.lt o k), ord.le (next0 o) (next1 o))
        (INACCESSIBLE: inaccessible X1 base1 next1 k)
    :
      inaccessible X0 base0 next0 k.
  Proof.
    econs.
    { des; auto. }
    { i. eapply ord.le_lt_lt; eauto.
      eapply INACCESSIBLE.(inaccessible_next). auto. }
    { i. des. eapply (@ord.le_lt_lt (ord.join (fun (x1: X1) => os (f x1)))).
      { eapply ord.le_join. i. specialize (SURJ a0).
        des. subst. eexists. reflexivity. }
      { eapply INACCESSIBLE.(inaccessible_join). auto. }
    }
    { eapply INACCESSIBLE. }
  Qed.

  Record ginaccessible (X: Type) (base: ord.t) (next: ord.t -> ord.t) (k: ord.t): Prop :=
    mk_ginaccessible
      { ginaccessible_base: ord.lt base k;
        ginaccessible_next: forall o (LT: ord.lt o k), ord.lt (next o) k;
        ginaccessible_join: forall (P: X -> Prop) (os: sig P -> ord.t) (LT: forall a, ord.lt (os a) k),
            ord.lt (ord.join os) k;
        ginaccessible_union: forall o0 o1 (LT0: ord.lt o0 k) (LT1: ord.lt o1 k),
            ord.lt (ord.union o0 o1) k;
      }.

  Lemma ginaccessible_inaccessible X base next k
        (INACCESSIBLE: ginaccessible X base next k)
    :
      inaccessible X base next k.
  Proof.
    econs; try by apply INACCESSIBLE. i.
    hexploit INACCESSIBLE.(ginaccessible_join).
    { instantiate (1:=fun (p: sig (fun _ => True)) => os (proj1_sig p)). ss. }
    i. eapply ord.le_lt_lt; eauto.
    eapply ord.le_join. i. exists (exist _ a0 I). reflexivity.
  Qed.

  Section TREE.
    Variable X: Type.

    Inductive tree: Type :=
    | tree_O
    | tree_S (tr: tree)
    | tree_join (trs: X -> tree)
    | tree_union (tr0 tr1: tree)
    .

    Definition tree_lt (tr0 tr1: tree): Prop :=
      match tr1 with
      | tree_O => False
      | tree_S tr => tr0 = tr
      | tree_join trs => exists x, tr0 = trs x
      | tree_union trl trr => tr0 = trl \/ tr0 = trr
      end.

    Lemma tree_lt_well_founded: well_founded tree_lt.
    Proof.
      ii. induction a.
      { econs. ii. ss. }
      { econs. i. ss. subst. auto. }
      { econs. i. ss. des. subst. auto. }
      { econs. i. ss. des; subst; auto. }
    Qed.

    Lemma tree_O_O: ord.eq (ord.from_wf tree_lt_well_founded tree_O) ord.O.
    Proof.
      Local Transparent ord.from_wf ord.from_acc ord.O.
      split.
      { unfold ord.from_wf. destruct (tree_lt_well_founded tree_O).
        ss. econs. i. destruct a0. ss. }
      { eapply ord.O_bot. }
    Qed.

    Lemma tree_S_S tr:
      ord.eq (ord.from_wf tree_lt_well_founded (tree_S tr)) (ord.S (ord.from_wf tree_lt_well_founded tr)).
    Proof.
      Local Transparent ord.from_wf ord.from_acc ord.O ord.S.
      split.
      { unfold ord.from_wf at 1. destruct (tree_lt_well_founded (tree_S tr)).
        ss. econs. i. destruct a0. ss. subst. exists tt.
        ss. eapply ord.same_acc_le.
      }
      { eapply ord.S_supremum. eapply ord.lt_from_wf. ss. }
    Qed.

    Lemma tree_join_build (trs: X -> tree):
      ord.eq (ord.from_wf tree_lt_well_founded (tree_join trs)) (ord.build (fun x => ord.from_wf tree_lt_well_founded (trs x))).
    Proof.
      split.
      { unfold ord.from_wf at 1. destruct (tree_lt_well_founded (tree_join trs)).
        ss. econs. i. destruct a0. des. ss. subst. exists x0.
        ss. eapply ord.same_acc_le.
      }
      { eapply ord.build_supremum. i. eapply ord.lt_from_wf. ss. eauto. }
    Qed.

    Lemma tree_union_union_le (tr0 tr1: tree):
      ord.le (ord.from_wf tree_lt_well_founded (tree_union tr0 tr1)) (ord.S (ord.union (ord.from_wf tree_lt_well_founded tr0) (ord.from_wf tree_lt_well_founded tr1))).
    Proof.
      unfold ord.from_wf at 1. destruct (tree_lt_well_founded (tree_union tr0 tr1)).
      ss. econs. i. destruct a0. ss. exists tt. ss. des; subst.
      { transitivity (ord.from_wf tree_lt_well_founded tr0).
        { eapply ord.same_acc_le. }
        { eapply ord.union_l. }
      }
      { transitivity (ord.from_wf tree_lt_well_founded tr1).
        { eapply ord.same_acc_le. }
        { eapply ord.union_r. }
      }
    Qed.

    Lemma tree_union_union_le_rev (tr0 tr1: tree):
      ord.le (ord.union (ord.from_wf tree_lt_well_founded tr0) (ord.from_wf tree_lt_well_founded tr1)) (ord.from_wf tree_lt_well_founded (tree_union tr0 tr1)).
    Proof.
      eapply ord.union_spec.
      { eapply ord.lt_le. eapply ord.lt_from_wf. ss. auto. }
      { eapply ord.lt_le. eapply ord.lt_from_wf. ss. auto. }
    Qed.

    Definition tree_top := ord.from_wf_set tree_lt_well_founded.

    Lemma inaccessible_rec_inaccessible (base0: ord.t) (next: ord.t -> ord.t)
          (NEXTLE: forall o, ord.le o (next o))
          (NEXTMON: forall o0 o1 (LE: ord.le o0 o1), ord.le (next o0) (next o1))
          (INACCESSIBLE: inaccessible X base0 next tree_top)
          base1
          (BASE1: ord.lt base1 tree_top)
      :
        inaccessible X base0 (ord.orec base1 next) tree_top.
    Proof.
      Local Transparent ord.from_wf ord.from_acc ord.O ord.S ord.rec ord.from_wf_set.
      econs; eauto.
      { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      assert (RECS: forall tr, ord.lt (ord.orec base1 next (ord.from_wf tree_lt_well_founded tr)) tree_top).
      { induction tr.
        { eapply (@ord.eq_lt_lt _ _ base1); auto.
          transitivity (ord.orec base1 next ord.O).
          { eapply ord.eq_orec; auto. eapply tree_O_O. }
          { eapply ord.orec_O; auto. }
        }
        { eapply (@ord.eq_lt_lt _ _ (next (ord.orec base1 next (ord.from_wf tree_lt_well_founded tr)))).
          { transitivity (ord.orec base1 next (ord.S (ord.from_wf tree_lt_well_founded tr))).
            { eapply ord.eq_orec; auto. eapply tree_S_S. }
            { eapply ord.orec_S; auto. }
          }
          { eapply INACCESSIBLE. auto. }
        }
        { eapply (@ord.eq_lt_lt _ _ _).
          { etransitivity.
            { eapply ord.eq_orec; auto. eapply tree_join_build. }
            { eapply ord.orec_build. }
          }
          { eapply INACCESSIBLE; auto. eapply INACCESSIBLE. i.
            eapply INACCESSIBLE. auto. }
        }
        { eapply ord.le_lt_lt.
          { eapply ord.le_orec.
            { auto. }
            { eapply tree_union_union_le. }
          }
          eapply ord.eq_lt_lt.
          { eapply ord.orec_S; auto. }
          eapply INACCESSIBLE.
          eapply ord.eq_lt_lt.
          { eapply ord.orec_union; auto. }
          { eapply INACCESSIBLE; auto. }
        }
      }
      i. eapply ord.lt_inv in LT. des. eapply (@ord.le_lt_lt (ord.orec base1 next (ord.from_wf tree_lt_well_founded a))); auto.
      eapply ord.le_orec; auto.
    Qed.

    Lemma tree_top_O
      :
        ord.lt ord.O tree_top.
    Proof.
      econs. instantiate (1:=tree_O). eapply ord.O_bot.
    Qed.

    Lemma tree_top_S o (LT: ord.lt o tree_top)
      :
        ord.lt (ord.S o) tree_top.
    Proof.
      i. eapply ord.lt_inv in LT. des.
      econs. instantiate (1:=tree_S a).
      eapply ord.S_supremum. eapply ord.le_lt_lt; eauto.
      eapply ord.lt_from_wf. ss.
    Qed.

    Lemma tree_top_union o0 o1 (LT0: ord.lt o0 tree_top) (LT1: ord.lt o1 tree_top)
      :
        ord.lt (ord.union o0 o1) tree_top.
    Proof.
      eapply ord.lt_inv in LT0. eapply ord.lt_inv in LT1. des.
      econs. instantiate (1:=tree_union a0 a). eapply ord.union_spec.
      { etransitivity; eauto. eapply ord.lt_le. eapply ord.lt_from_wf. ss. auto. }
      { etransitivity; eauto. eapply ord.lt_le. eapply ord.lt_from_wf. ss. auto. }
    Qed.

    Hypothesis CHOICE: FunctionalChoice_on X tree.

    Lemma tree_top_join (os: X -> ord.t) (LT: forall x, ord.lt (os x) tree_top)
      :
        ord.lt (ord.join os) tree_top.
    Proof.
      i. hexploit (CHOICE (fun (x: X) (tr: tree) => ord.le (os x) (ord.from_wf tree_lt_well_founded tr))).
      { i. specialize (LT x). eapply ord.lt_inv in LT. eauto. }
      i. des.
      econs. instantiate (1:=tree_join f).
      eapply ord.join_supremum. i. etransitivity; eauto.
      eapply ord.lt_le. eapply ord.lt_from_wf. ss. eauto.
    Qed.

    Lemma tree_top_S_inaccessible
      :
        inaccessible X ord.O ord.S tree_top.
    Proof.
      econs.
      { eapply tree_top_O. }
      { eapply tree_top_S. }
      { eapply tree_top_join. }
      { eapply tree_top_union. }
    Qed.

    Lemma tree_top_add_inaccessible
          o (LT: ord.lt o tree_top)
      :
        inaccessible X ord.O (ordArith.add o) tree_top.
    Proof.
      Local Transparent ordArith.add.
      eapply inaccessible_rec_inaccessible; eauto.
      { i. eapply ord.S_le. }
      { i. apply ord.le_S. auto. }
      { eapply tree_top_S_inaccessible. }
    Qed.

    Lemma tree_top_add o0 o1 (LT0: ord.lt o0 tree_top) (LT1: ord.lt o1 tree_top)
      :
        ord.lt (ordArith.add o0 o1) tree_top.
    Proof.
      eapply tree_top_add_inaccessible; auto.
    Qed.

    Lemma tree_top_flip_add_inaccessible
          o (LT: ord.lt o tree_top)
      :
        inaccessible X ord.O (flip ordArith.add o) tree_top.
    Proof.
      hexploit tree_top_add_inaccessible; eauto. i.
      econs; auto.
      { eapply ord.le_lt_lt; eauto. eapply ord.O_bot. }
      { i. eapply (@tree_top_add_inaccessible _ LT0).(inaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma tree_top_mult_inaccessible
          o (LT: ord.lt o tree_top)
      :
        inaccessible X ord.O (ordArith.mult o) tree_top.
    Proof.
      Local Transparent ordArith.mult.
      eapply inaccessible_rec_inaccessible; eauto.
      { i. eapply ordArith.add_base_l. }
      { i. eapply ordArith.le_add_l; auto. }
      { eapply tree_top_flip_add_inaccessible. auto. }
      { eapply ord.le_lt_lt; eauto. eapply ord.O_bot. }
    Qed.

    Lemma tree_top_mult o0 o1 (LT0: ord.lt o0 tree_top) (LT1: ord.lt o1 tree_top)
      :
        ord.lt (ordArith.mult o0 o1) tree_top.
    Proof.
      eapply tree_top_mult_inaccessible; auto.
    Qed.

    Lemma tree_top_flip_mult_inaccessible
          o (LT: ord.lt o tree_top)
      :
        inaccessible X ord.O (flip ordArith.mult o) tree_top.
    Proof.
      hexploit tree_top_mult_inaccessible; eauto. i.
      econs; auto.
      { eapply ord.le_lt_lt; eauto. eapply ord.O_bot. }
      { i. eapply (@tree_top_mult_inaccessible _ LT0).(inaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma tree_top_expn_inaccessible
          o (POS: ord.lt ord.O o) (LT: ord.lt o tree_top)
      :
        inaccessible X ord.O (ordArith.expn o) tree_top.
    Proof.
      Local Transparent ordArith.expn.
      eapply inaccessible_rec_inaccessible; eauto.
      { i. unfold flip. eapply ordArith.mult_le_l. auto. }
      { i. eapply ordArith.le_mult_l. auto. }
      { eapply tree_top_flip_mult_inaccessible. auto. }
      { eapply tree_top_S. eapply tree_top_O. }
    Qed.

    Lemma tree_top_expn o0 o1 (LT0: ord.lt o0 tree_top) (LT1: ord.lt o1 tree_top)
      :
        ord.lt (ordArith.expn o0 o1) tree_top.
    Proof.
      eapply (@ord.le_lt_lt (ordArith.expn (ord.S o0) o1)).
      { eapply ordArith.le_expn_l. eapply ord.S_le. }
      { eapply tree_top_expn_inaccessible; auto.
        { eapply ord.S_pos. }
        { eapply tree_top_S. auto. }
      }
    Qed.

    Lemma tree_top_flip_expn_inaccessible
          o (LT: ord.lt o tree_top)
      :
        inaccessible X ord.O (flip ordArith.expn o) tree_top.
    Proof.
      econs.
      { eapply tree_top_O. }
      { i. eapply tree_top_expn; auto. }
      { eapply tree_top_join. }
      { eapply tree_top_union. }
    Qed.
  End TREE.

  Section GTREE.
    Variable X: Type.

    Inductive gtree: Type :=
    | gtree_O
    | gtree_S (tr: gtree)
    | gtree_join (P: X -> Prop) (trs: sig P -> gtree)
    | gtree_union (tr0 tr1: gtree)
    .

    Definition gtree_lt (tr0 tr1: gtree): Prop :=
      match tr1 with
      | gtree_O => False
      | gtree_S tr => tr0 = tr
      | gtree_join trs => exists x, tr0 = trs x
      | gtree_union trl trr => tr0 = trl \/ tr0 = trr
      end.

    Lemma gtree_lt_well_founded: well_founded gtree_lt.
    Proof.
      ii. induction a.
      { econs. ii. ss. }
      { econs. i. ss. subst. auto. }
      { econs. i. ss. des. subst. auto. }
      { econs. i. ss. des; subst; auto. }
    Qed.

    Lemma gtree_O_O: ord.eq (ord.from_wf gtree_lt_well_founded gtree_O) ord.O.
    Proof.
      Local Transparent ord.from_wf ord.from_acc ord.O ord.S ord.rec ord.from_wf_set.
      split.
      { unfold ord.from_wf. destruct (gtree_lt_well_founded gtree_O).
        ss. econs. i. destruct a0. ss. }
      { eapply ord.O_bot. }
    Qed.

    Lemma gtree_S_S tr:
      ord.eq (ord.from_wf gtree_lt_well_founded (gtree_S tr)) (ord.S (ord.from_wf gtree_lt_well_founded tr)).
    Proof.
      split.
      { unfold ord.from_wf at 1. destruct (gtree_lt_well_founded (gtree_S tr)).
        ss. econs. i. destruct a0. ss. subst. exists tt.
        ss. eapply ord.same_acc_le.
      }
      { eapply ord.S_supremum. eapply ord.lt_from_wf. ss. }
    Qed.

    Lemma gtree_join_build P (trs: sig P -> gtree):
      ord.eq (ord.from_wf gtree_lt_well_founded (gtree_join trs)) (ord.build (fun x => ord.from_wf gtree_lt_well_founded (trs x))).
    Proof.
      split.
      { unfold ord.from_wf at 1. destruct (gtree_lt_well_founded (gtree_join trs)).
        ss. econs. i. destruct a0. des. ss. subst. exists x0.
        ss. eapply ord.same_acc_le.
      }
      { eapply ord.build_supremum. i. eapply ord.lt_from_wf. ss. eauto. }
    Qed.

    Lemma gtree_union_union_le (tr0 tr1: gtree):
      ord.le (ord.from_wf gtree_lt_well_founded (gtree_union tr0 tr1)) (ord.S (ord.union (ord.from_wf gtree_lt_well_founded tr0) (ord.from_wf gtree_lt_well_founded tr1))).
    Proof.
      unfold ord.from_wf at 1. destruct (gtree_lt_well_founded (gtree_union tr0 tr1)).
      ss. econs. i. destruct a0. ss. exists tt. ss. des; subst.
      { transitivity (ord.from_wf gtree_lt_well_founded tr0).
        { eapply ord.same_acc_le. }
        { eapply ord.union_l. }
      }
      { transitivity (ord.from_wf gtree_lt_well_founded tr1).
        { eapply ord.same_acc_le. }
        { eapply ord.union_r. }
      }
    Qed.

    Lemma gtree_union_union_le_rev (tr0 tr1: gtree):
      ord.le (ord.union (ord.from_wf gtree_lt_well_founded tr0) (ord.from_wf gtree_lt_well_founded tr1)) (ord.from_wf gtree_lt_well_founded (gtree_union tr0 tr1)).
    Proof.
      eapply ord.union_spec.
      { eapply ord.lt_le. eapply ord.lt_from_wf. ss. auto. }
      { eapply ord.lt_le. eapply ord.lt_from_wf. ss. auto. }
    Qed.

    Definition gtree_top := ord.from_wf_set gtree_lt_well_founded.

    Lemma ginaccessible_rec_ginaccessible (base0: ord.t) (next: ord.t -> ord.t)
          (NEXTLE: forall o, ord.le o (next o))
          (NEXTMON: forall o0 o1 (LE: ord.le o0 o1), ord.le (next o0) (next o1))
          (INACCESSIBLE: ginaccessible X base0 next gtree_top)
          base1
          (BASE1: ord.lt base1 gtree_top)
      :
        ginaccessible X base0 (ord.orec base1 next) gtree_top.
    Proof.
      econs; eauto.
      { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      2: { eapply INACCESSIBLE. }
      assert (RECS: forall tr, ord.lt (ord.orec base1 next (ord.from_wf gtree_lt_well_founded tr)) gtree_top).
      { induction tr.
        { eapply (@ord.eq_lt_lt _ _ base1); auto.
          transitivity (ord.orec base1 next ord.O).
          { eapply ord.eq_orec; auto. eapply gtree_O_O. }
          { eapply ord.orec_O; auto. }
        }
        { eapply (@ord.eq_lt_lt _ _ (next (ord.orec base1 next (ord.from_wf gtree_lt_well_founded tr)))).
          { transitivity (ord.orec base1 next (ord.S (ord.from_wf gtree_lt_well_founded tr))).
            { eapply ord.eq_orec; auto. eapply gtree_S_S. }
            { eapply ord.orec_S; auto. }
          }
          { eapply INACCESSIBLE. auto. }
        }
        { eapply (@ord.eq_lt_lt _ _ _).
          { etransitivity.
            { eapply ord.eq_orec; auto. eapply gtree_join_build. }
            { eapply ord.orec_build. }
          }
          { eapply INACCESSIBLE; auto. eapply INACCESSIBLE. i.
            eapply INACCESSIBLE. auto. }
        }
        { eapply ord.le_lt_lt.
          { eapply ord.le_orec.
            { auto. }
            { eapply gtree_union_union_le. }
          }
          eapply ord.eq_lt_lt.
          { eapply ord.orec_S; auto. }
          eapply INACCESSIBLE.
          eapply ord.eq_lt_lt.
          { eapply ord.orec_union; auto. }
          { eapply INACCESSIBLE; auto. }
        }
      }
      i. eapply ord.lt_inv in LT. des. eapply (@ord.le_lt_lt (ord.orec base1 next (ord.from_wf gtree_lt_well_founded a))); auto.
      eapply ord.le_orec; auto.
    Qed.

    Lemma gtree_top_O
      :
        ord.lt ord.O gtree_top.
    Proof.
      econs. instantiate (1:=gtree_O). eapply ord.O_bot.
    Qed.

    Lemma gtree_top_S o (LT: ord.lt o gtree_top)
      :
        ord.lt (ord.S o) gtree_top.
    Proof.
      i. eapply ord.lt_inv in LT. des.
      econs. instantiate (1:=gtree_S a).
      eapply ord.S_supremum. eapply ord.le_lt_lt; eauto.
      eapply ord.lt_from_wf. ss.
    Qed.

    Lemma gtree_top_union o0 o1 (LT0: ord.lt o0 gtree_top) (LT1: ord.lt o1 gtree_top)
      :
        ord.lt (ord.union o0 o1) gtree_top.
    Proof.
      eapply ord.lt_inv in LT0. eapply ord.lt_inv in LT1. des.
      econs. instantiate (1:=gtree_union a0 a). eapply ord.union_spec.
      { etransitivity; eauto. eapply ord.lt_le. eapply ord.lt_from_wf. ss. auto. }
      { etransitivity; eauto. eapply ord.lt_le. eapply ord.lt_from_wf. ss. auto. }
    Qed.

    Hypothesis CHOICE: forall (P: X -> Prop), FunctionalChoice_on (sig P) gtree.

    Lemma gtree_top_join (P: X -> Prop) (os: sig P -> ord.t)
          (LT: forall x, ord.lt (os x) gtree_top)
      :
        ord.lt (ord.join os) gtree_top.
    Proof.
      i. hexploit (CHOICE (fun (x: sig P) (tr: gtree) => ord.le (os x) (ord.from_wf gtree_lt_well_founded tr))).
      { i. specialize (LT x). eapply ord.lt_inv in LT. eauto. }
      i. des.
      econs. instantiate (1:=gtree_join f).
      eapply ord.join_supremum. i. etransitivity; eauto.
      eapply ord.lt_le. eapply ord.lt_from_wf. ss. eauto.
    Qed.

    Lemma gtree_top_S_ginaccessible
      :
        ginaccessible X ord.O ord.S gtree_top.
    Proof.
      econs.
      { eapply gtree_top_O. }
      { eapply gtree_top_S. }
      { eapply gtree_top_join. }
      { eapply gtree_top_union. }
    Qed.

    Lemma gtree_top_add_ginaccessible
          o (LT: ord.lt o gtree_top)
      :
        ginaccessible X ord.O (ordArith.add o) gtree_top.
    Proof.
      Local Transparent ordArith.add.
      eapply ginaccessible_rec_ginaccessible; eauto.
      { i. eapply ord.S_le. }
      { i. apply ord.le_S. auto. }
      { eapply gtree_top_S_ginaccessible. }
    Qed.

    Lemma gtree_top_add o0 o1 (LT0: ord.lt o0 gtree_top) (LT1: ord.lt o1 gtree_top)
      :
        ord.lt (ordArith.add o0 o1) gtree_top.
    Proof.
      eapply gtree_top_add_ginaccessible; auto.
    Qed.

    Lemma gtree_top_flip_add_ginaccessible
          o (LT: ord.lt o gtree_top)
      :
        ginaccessible X ord.O (flip ordArith.add o) gtree_top.
    Proof.
      hexploit gtree_top_add_ginaccessible; eauto. i.
      econs; auto.
      { eapply ord.le_lt_lt; eauto. eapply ord.O_bot. }
      { i. eapply (@gtree_top_add_ginaccessible _ LT0).(ginaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma gtree_top_mult_ginaccessible
          o (LT: ord.lt o gtree_top)
      :
        ginaccessible X ord.O (ordArith.mult o) gtree_top.
    Proof.
      Local Transparent ordArith.mult.
      eapply ginaccessible_rec_ginaccessible; eauto.
      { i. eapply ordArith.add_base_l. }
      { i. eapply ordArith.le_add_l; auto. }
      { eapply gtree_top_flip_add_ginaccessible. auto. }
      { eapply ord.le_lt_lt; eauto. eapply ord.O_bot. }
    Qed.

    Lemma gtree_top_mult o0 o1 (LT0: ord.lt o0 gtree_top) (LT1: ord.lt o1 gtree_top)
      :
        ord.lt (ordArith.mult o0 o1) gtree_top.
    Proof.
      eapply gtree_top_mult_ginaccessible; auto.
    Qed.

    Lemma gtree_top_flip_mult_ginaccessible
          o (LT: ord.lt o gtree_top)
      :
        ginaccessible X ord.O (flip ordArith.mult o) gtree_top.
    Proof.
      hexploit gtree_top_mult_ginaccessible; eauto. i.
      econs; auto.
      { eapply ord.le_lt_lt; eauto. eapply ord.O_bot. }
      { i. eapply (@gtree_top_mult_ginaccessible _ LT0).(ginaccessible_next). auto. }
      { i. eapply H. auto. }
      { i. eapply H; auto. }
    Qed.

    Lemma gtree_top_expn_ginaccessible
          o (POS: ord.lt ord.O o) (LT: ord.lt o gtree_top)
      :
        ginaccessible X ord.O (ordArith.expn o) gtree_top.
    Proof.
      Local Transparent ordArith.expn.
      eapply ginaccessible_rec_ginaccessible; eauto.
      { i. unfold flip. eapply ordArith.mult_le_l. auto. }
      { i. eapply ordArith.le_mult_l. auto. }
      { eapply gtree_top_flip_mult_ginaccessible. auto. }
      { eapply gtree_top_S. eapply gtree_top_O. }
    Qed.

    Lemma gtree_top_expn o0 o1 (LT0: ord.lt o0 gtree_top) (LT1: ord.lt o1 gtree_top)
      :
        ord.lt (ordArith.expn o0 o1) gtree_top.
    Proof.
      eapply (@ord.le_lt_lt (ordArith.expn (ord.S o0) o1)).
      { eapply ordArith.le_expn_l. eapply ord.S_le. }
      { eapply gtree_top_expn_ginaccessible; auto.
        { eapply ord.S_pos. }
        { eapply gtree_top_S. auto. }
      }
    Qed.

    Lemma gtree_top_flip_expn_ginaccessible
          o (LT: ord.lt o gtree_top)
      :
        ginaccessible X ord.O (flip ordArith.expn o) gtree_top.
    Proof.
      econs.
      { eapply gtree_top_O. }
      { i. eapply gtree_top_expn; auto. }
      { eapply gtree_top_join. }
      { eapply gtree_top_union. }
    Qed.
  End GTREE.
End INACCESSIBLE.
