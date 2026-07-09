From lantana.ordinal Require Import sflib basics classical_ordinal cardinal inaccessibility.
From lantana.ordinal Require Export ordinal arithmetic.

From Coq Require Import ClassicalChoice.
From Coq Require Import Program.

Set Implicit Arguments.
Set Primitive Projections.

Section STRONGLYINACCESSIBLE.
  Let SmallT: Type := Type.
  Let X := @sig (@sigT SmallT (fun X => X -> X -> Prop))
                (fun PR => well_founded (projT2 PR)).
  Let Y : X -> ord.t := fun PRWF => ord.from_wf_set (proj2_sig PRWF).
  Definition kappa := ord.large.
  Local Transparent ord.large.

  Lemma kappa_complete o (LT: ord.lt o kappa):
    exists (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R),
      ord.le o (ord.from_wf_set WF).
  Proof.
    eapply ord.lt_inv in LT. des. eauto.
  Qed.

  Section UNION.
    Variable A: SmallT.
    Variable Ts: A -> SmallT.
    Variable R: forall a, Ts a -> Ts a -> Prop.
    Arguments R: clear implicits.
    Hypothesis WF: forall a, well_founded (R a).
    Arguments WF: clear implicits.
    Let _union_set: SmallT := @sigT A (fun a => option (Ts a)).

    Inductive _union_rel:
      _union_set -> _union_set -> Prop :=
    | _union_rel_top
        a x
      :
        _union_rel (existT _ a (Some x)) (existT _ a None)
    | _union_rel_normal
        a x0 x1
        (LT: R a x0 x1)
      :
        _union_rel (existT _ a (Some x0)) (existT _ a (Some x1))
    .

    Let _union_rel_well_founded:
      well_founded _union_rel.
    Proof.
      assert (forall a x, Acc _union_rel (existT _ a (Some x))).
      { intros a. eapply (well_founded_induction (WF a)); auto.
        i. econs. i. dependent destruction H0. eapply H; eauto. }
      ii. destruct a as [a [x|]]; eauto.
      econs. i. inv H0; eauto.
    Qed.

    Let _from_wf_union (a: A) (x: Ts a)
      :
        ord.eq (ord.from_wf (WF a) x)
               (ord.from_wf _union_rel_well_founded (existT _ a (Some x))).
    Proof.
      revert x. eapply (well_founded_induction (WF a)).
      i. split.
      { eapply ord.from_wf_supremum. i. specialize (H _ LT). inv H.
        eapply ord.le_lt_lt; eauto. eapply ord.lt_from_wf. econs; eauto. }
      { eapply ord.from_wf_supremum. i. dependent destruction LT.
        specialize (H _ LT). inv H.
        eapply ord.le_lt_lt; eauto. eapply ord.lt_from_wf. auto. }
    Qed.

    Let _from_wf_set_union:
      ord.eq (@ord.build A (fun a => ord.from_wf_set (WF a)))
             (ord.from_wf_set _union_rel_well_founded).
    Proof.
      Local Transparent ord.from_wf_set.
      split.
      { econs. i. exists (existT _ a0 None). eapply ord.build_supremum. i.
        eapply (@ord.le_lt_lt (ord.from_wf _union_rel_well_founded (existT _ a0 (Some a)))).
        { eapply _from_wf_union. }
        { eapply ord.lt_from_wf. econs. }
      }
      { econs. i. destruct a0 as [a0 [x|]].
        { exists a0. transitivity (ord.from_wf (WF a0) x).
          { eapply _from_wf_union. }
          { eapply ord.lt_le. eapply ord.from_wf_set_upperbound. }
        }
        { exists a0. eapply ord.from_wf_supremum. i.
          dependent destruction LT.
          eapply (@ord.le_lt_lt (ord.from_wf (WF a0) x)).
          { eapply _from_wf_union. }
          { eapply ord.from_wf_set_upperbound. }
        }
      }
    Qed.

    Lemma small_join_small:
      exists (U: SmallT) (RU: U -> U -> Prop) (WFU: well_founded RU),
        forall a, ord.lt (ord.from_wf_set (WF a)) (ord.from_wf_set WFU).
    Proof.
      exists _union_set, _union_rel, _union_rel_well_founded. i.
      eapply ord.lt_eq_lt.
      { symmetry. eapply _from_wf_set_union. }
      eapply (@ord.build_upperbound _ (fun a0 => ord.from_wf_set (WF a0)) a).
    Qed.
  End UNION.

  Lemma smaller_cardinal_small (A: Type) (B: SmallT)
        (LE: ord.le (cardinal.cardinal A) (cardinal.cardinal B))
    :
      exists (A': SmallT),
        ord.eq (cardinal.cardinal A) (cardinal.cardinal A').
  Proof.
    eapply cardinal._cardinal_le_iff in LE. inv LE.
    set (A' := @sig B (fun b => exists a, f a = b)). exists A'.
    split.
    { apply cardinal._cardinal_le_iff.
      eapply cardinal._cardinal_le_intro with (f:=fun a => exist _ (f a) (ex_intro _ a eq_refl)).
      i. inv EQ. eapply INJ; eauto.
    }
    { hexploit (choice (fun (a': A') (a: A) =>
                          f a = proj1_sig a')).
      { i. destruct x. s. eauto. }
      i. des. apply cardinal._cardinal_le_iff.
      eapply cardinal._cardinal_le_intro with (f:=f0).
      i. destruct a0, a1. des. subst.
      dup EQ. eapply f_equal with (f:=f) in EQ0.
      rewrite H in EQ0. rewrite H in EQ0. ss.
      eapply INJ in EQ0. subst. auto.
    }
  Qed.

  Lemma small_ordinal_small o (LT: ord.lt o kappa):
    exists (A: SmallT), ord.eq (cardinal.cardinal A) (cardinal.cardinal (toSet.to_total_set o)).
  Proof.
    eapply kappa_complete in LT. des.
    hexploit (@smaller_cardinal_small (toSet.to_total_set o) A).
    { etransitivity.
      2: { eapply cardinal.from_wf_set_to_total. }
      { eapply cardinal.to_total_le. eauto. }
    }
    i. des. esplits. symmetry. eapply H.
  Qed.

  Lemma sum_of_small o (LT: ord.lt o kappa):
    exists (A: SmallT) (os: A -> ord.t), ord.eq o (ord.build os).
  Proof.
    hexploit small_ordinal_small; eauto. i. des.
    hexploit cardinal.sum_of_smaller_same_cardinal; eauto.
  Qed.



  Lemma kappa_inaccessible_build (A: SmallT) (os: A -> ord.t) (LT: forall a, ord.lt (os a) kappa)
    :
      ord.lt (ord.build os) kappa.
  Proof.
    hexploit (choice (fun (a: A) (XRWF: @sig (@sigT SmallT (fun X => X -> X -> Prop)) (fun XR => well_founded (projT2 XR))) =>
                        ord.le (os a) (ord.from_wf_set (proj2_sig XRWF)))).
    { i. eapply NNPP. ii. eapply ord.lt_not_le.
      { eapply (LT x). }
      eapply ord.build_supremum. i. destruct (classicOrd.total (os x) (Y a)); auto.
      exfalso. eapply H. exists a. auto.
    }
    i. des.
    hexploit (@small_join_small A (fun a => projT1 (proj1_sig (f a))) (fun a => projT2 (proj1_sig (f a))) (fun a => proj2_sig (f a))).
    i. des. eapply (@ord.le_lt_lt (ord.from_wf_set WFU)).
    { eapply ord.build_supremum; eauto. i. eapply (@ord.le_lt_lt (ord.from_wf_set (proj2_sig (f a)))).
      { eapply H. }
      { eapply H0. }
    }
    eapply (@ord.build_upperbound X Y (exist _ (existT _ U RU) WFU)).
  Qed.

  Lemma kappa_inaccessible_is_join (A: SmallT) (os: A -> ord.t) (LT: forall a, ord.lt (os a) kappa)
        o (JOIN: ord.is_join os o)
    :
      ord.lt o kappa.
  Proof.
    eapply (@ord.le_lt_lt (ord.build os)).
    2: { eapply kappa_inaccessible_build; auto. }
    eapply ord.is_join_supremum; eauto.
    i. eapply ord.lt_le. eapply ord.build_upperbound.
  Qed.

  Lemma kappa_inaccessible_join (A: SmallT) (os: A -> ord.t) (LT: forall a, ord.lt (os a) kappa):
    ord.lt (ord.join os) kappa.
  Proof.
    eapply kappa_inaccessible_is_join; eauto. eapply ord.join_is_join.
  Qed.

  Let D: SmallT := unit.
  Let D_well_founded: @well_founded D (fun _ _ => False).
  Proof.
    ii. econs; ss.
  Qed.

  Lemma kappa_inaccesible_from_acc (A: SmallT) (R: A -> A -> Prop) a (ACC: Acc R a):
    ord.lt (ord.from_acc ACC) kappa.
  Proof.
    dup ACC. revert ACC. induction ACC0. i.
    destruct ACC. ss.
    hexploit (@kappa_inaccessible_build (sig (fun a0 => R a0 x)) (fun a0p : {a0 : A | R a0 x} => ord.from_acc (ordinal.ord.from_acc_obligation_1 (Acc_intro x a) a0p))); eauto.
    i. destruct a0. ss. eapply H0; eauto.
  Qed.

  Lemma kappa_inaccesible_from_wf (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R) a:
    ord.lt (ord.from_wf WF a) kappa.
  Proof.
    Local Transparent ord.from_wf.
    eapply kappa_inaccesible_from_acc.
  Qed.

  Lemma kappa_inaccesible_from_wf_set (A: SmallT) (R: A -> A -> Prop) (WF: well_founded R):
    ord.lt (ord.from_wf_set WF) kappa.
  Proof.
    Local Transparent ord.from_wf_set.
    eapply kappa_inaccessible_build. i. eapply kappa_inaccesible_from_wf.
  Qed.

  Lemma kappa_inaccessible_cardinal (A: SmallT):
    ord.lt (cardinal.cardinal A) kappa.
  Proof.
    hexploit (cardinal.cardinal_of_cardinal A). i. inv H.
    des. eapply ord.eq_lt_lt.
    { symmetry. eapply H2. }
    eapply (@ord.build_upperbound X Y (exist _ (existT _ A R) WF)).
  Qed.

  Lemma kappa_inaccessible_is_O o (ZERO: ord.is_O o):
    ord.lt o kappa.
  Proof.
    eapply ord.le_lt_lt.
    { eapply ZERO. }
    eapply (@ord.build_upperbound X Y (exist _ (existT _ D (fun _ _ => False)) D_well_founded)).
  Qed.

  Lemma kappa_inaccessible_O:
    ord.lt ord.O kappa.
  Proof.
    eapply kappa_inaccessible_is_O. eapply ord.O_is_O.
  Qed.

  Lemma kappa_inaccessible_is_S o s (SUCC: ord.is_S o s) (LT: ord.lt o kappa):
    ord.lt s kappa.
  Proof.
    eapply (@ord.le_lt_lt (@ord.build D (fun _ => o))).
    { eapply SUCC. eapply (ord.build_upperbound (fun _ : D => o) tt). }
    { eapply kappa_inaccessible_build; eauto. }
  Qed.

  Lemma kappa_inaccessible_S o (LT: ord.lt o kappa):
    ord.lt (ord.S o) kappa.
  Proof.
    eapply kappa_inaccessible_is_S; eauto.
    eapply ord.S_is_S.
  Qed.

  Lemma kappa_inaccessible_nat n: ord.lt (ord.from_nat n) kappa.
  Proof.
    Local Transparent ord.from_nat.
    induction n; ss.
    - eapply kappa_inaccessible_O.
    - eapply kappa_inaccessible_S. auto.
  Qed.

  Lemma kappa_inaccessible_omega: ord.lt ord.omega kappa.
  Proof.
    Local Transparent ord.omega.
    eapply kappa_inaccessible_join.
    eapply kappa_inaccessible_nat.
  Qed.

  Lemma kappa_inaccessible_power o (LT: ord.lt o kappa):
    ord.lt (cardinal.cardinal (toSet.to_total_set o -> Prop)) kappa.
  Proof.
    hexploit (kappa_complete LT); eauto. i. des.
    eapply (@ord.le_lt_lt (cardinal.cardinal (A -> Prop))).
    { apply cardinality.cardinal_le_iff.
      eapply cardinality.le_power. apply cardinality.cardinal_le_iff.
      etransitivity.
      { eapply cardinal.to_total_le. eapply H. }
      eapply cardinal.from_wf_set_to_total.
    }
    eapply kappa_inaccessible_cardinal.
  Qed.

  Lemma kappa_inaccessible_next_cardinal o (LT: ord.lt o kappa):
    ord.lt (cardinal.next_cardinal (toSet.to_total_set o)) kappa.
  Proof.
    eapply ord.le_lt_lt.
    2: { eapply kappa_inaccessible_power. eauto. }
    eapply cardinal.aleph_gen_le_beth_gen.
  Qed.

  Lemma kappa_inaccessible_union o0 o1 (LT0: ord.lt o0 kappa) (LT1: ord.lt o1 kappa):
    ord.lt (ord.union o0 o1) kappa.
  Proof.
    Local Transparent ord.union.
    eapply kappa_inaccessible_join. i. destruct a; auto.
  Qed.

  Lemma kappa_regular A
        (SIZE: ord.lt (cardinal.cardinal A) kappa)
        (os: A -> ord.t)
        (LT: forall a, ord.lt (os a) kappa)
    :
      ord.lt (ord.join os) kappa.
  Proof.
    eapply small_ordinal_small in SIZE. des.
    assert (cardinality.eq A0 A).
    { eapply cardinality.cardinal_eq_iff in SIZE.
      etransitivity; [eapply SIZE|].
      symmetry. eapply cardinality.cardinal_to_total_bij. }
    apply cardinality.eq_bij_equiv in H. inv H.
    eapply (@ord.le_lt_lt (@ord.join A0 (fun a0 => os (f a0)))).
    { eapply ord.le_join. i. exists (g a0).
      rewrite GF. reflexivity. }
    { eapply kappa_inaccessible_join. i. auto. }
  Qed.

  Lemma kappa_weakly_inaccesible
        A (SIZE: ord.lt (cardinal.cardinal A) kappa):
    inaccessible A ord.omega cardinal.aleph_gen kappa.
  Proof.
    econs.
    { eapply kappa_inaccessible_omega. }
    { eapply kappa_inaccessible_next_cardinal. }
    { eapply kappa_regular; eauto. }
    { eapply kappa_inaccessible_union. }
  Qed.

  Theorem kappa_strongly_inaccesible
          A (SIZE: ord.lt (cardinal.cardinal A) kappa):
    inaccessible A ord.omega cardinal.beth_gen kappa.
  Proof.
    econs.
    { eapply kappa_inaccessible_omega. }
    { eapply kappa_inaccessible_power. }
    { eapply kappa_regular; eauto. }
    { eapply kappa_inaccessible_union. }
  Qed.

  Lemma kappa_inaccessible_rec (base: ord.t) (next: ord.t -> ord.t)
        (BASE: ord.lt base kappa)
        (NEXT: forall o (LT: ord.lt o kappa), ord.lt (next o) kappa)
        (NEXTLE: forall o0 o1 (LE: ord.le o0 o1), ord.le (next o0) (next o1))
        o
        (LT: ord.lt o kappa):
    ord.lt (ord.orec base next o) kappa.
  Proof.
    revert o LT.
    eapply (well_founded_induction
              ord.lt_well_founded
              (fun o => forall (LT: ord.lt o kappa), ord.lt (ord.orec base next o) kappa)).
    i. dup LT. eapply sum_of_small in LT. des.
    eapply ord.le_lt_lt.
    { eapply ord.le_orec.
      { auto. }
      { eapply LT. }
    }
    Local Transparent ord.rec.
    eapply kappa_inaccessible_join. i. destruct a; auto.
    { eapply kappa_inaccessible_join. i.
      eapply NEXT. eapply H; auto.
      { eapply ord.lt_eq_lt.
        { eapply LT. }
        { eapply ord.build_upperbound. }
      }
      { etransitivity.
        { eapply ord.build_upperbound. }
        { eapply ord.eq_lt_lt; eauto. symmetry. eauto. }
      }
    }
  Qed.

  Lemma kappa_inaccessible_aleph o (LT: ord.lt o kappa):
    ord.lt (cardinal.aleph o) kappa.
  Proof.
    eapply kappa_inaccessible_rec.
    { eapply kappa_inaccessible_omega. }
    { i. eapply kappa_inaccessible_next_cardinal. auto. }
    { i. eapply cardinal.le_aleph_gen. auto. }
    { auto. }
  Qed.

  Lemma kappa_inaccessible_beth o (LT: ord.lt o kappa):
    ord.lt (cardinal.beth o) kappa.
  Proof.
    eapply kappa_inaccessible_rec.
    { eapply kappa_inaccessible_omega. }
    { i. eapply kappa_inaccessible_power. auto. }
    { i. eapply cardinal.le_beth_gen. auto. }
    { auto. }
  Qed.

  Lemma kappa_fixpoint (base: ord.t) (next: ord.t -> ord.t)
        (BASE: ord.lt base kappa)
        (NEXT: forall o (LT: ord.lt o kappa), ord.lt (next o) kappa)
        (NEXTLE: forall o0 o1 (LE: ord.le o0 o1), ord.le (next o0) (next o1))
        (EXPAND: forall o, ord.le (ord.S o) (next o)):
    ord.eq kappa (ord.orec base next kappa).
  Proof.
    split.
    - eapply ord.eq_le_le.
      { eapply ord.orec_of_S. }
      eapply ord.orec_mon.
      { eapply ord.O_bot. }
      { i. transitivity (ord.S o1); auto.
        apply ord.le_S. auto. }
    - eapply ord.orec_build_supremum.
      { eapply ord.lt_le. auto. }
      { i. eapply ord.lt_le. eapply NEXT.
        eapply kappa_inaccessible_rec; auto. }
  Qed.

  Lemma kappa_aleph_fixpoint:
    ord.eq kappa (cardinal.aleph kappa).
  Proof.
    eapply kappa_fixpoint.
    { eapply kappa_inaccessible_omega. }
    { i. eapply kappa_inaccessible_next_cardinal. auto. }
    { i. eapply cardinal.le_aleph_gen. auto. }
    { i. eapply ord.S_supremum. eapply cardinal.aleph_gen_lt. }
  Qed.

  Lemma kappa_beth_fixpoint:
    ord.eq kappa (cardinal.beth kappa).
  Proof.
    eapply kappa_fixpoint.
    { eapply kappa_inaccessible_omega. }
    { i. eapply kappa_inaccessible_power. auto. }
    { i. eapply cardinal.le_beth_gen. auto. }
    { i. eapply ord.S_supremum. eapply cardinal.beth_gen_lt. }
  Qed.

  Lemma kappa_inaccessible_add o0 o1 (LT0: ord.lt o0 kappa) (LT1: ord.lt o1 kappa):
    ord.lt (ordArith.add o0 o1) kappa.
  Proof.
    Local Transparent ordArith.add.
    eapply kappa_inaccessible_rec; auto.
    { eapply kappa_inaccessible_S. }
    { i. eapply ord.le_S. auto. }
  Qed.

  Lemma kappa_inaccessible_mult o0 o1 (LT0: ord.lt o0 kappa) (LT1: ord.lt o1 kappa):
    ord.lt (ordArith.mult o0 o1) kappa.
  Proof.
    Local Transparent ordArith.mult.
    eapply kappa_inaccessible_rec; auto.
    { eapply kappa_inaccessible_O. }
    { i. eapply kappa_inaccessible_add; auto. }
    { i. eapply ordArith.le_add_l. auto. }
  Qed.

  Lemma kappa_inaccessible_expn o0 o1 (LT0: ord.lt o0 kappa) (LT1: ord.lt o1 kappa):
    ord.lt (ordArith.expn o0 o1) kappa.
  Proof.
    Local Transparent ordArith.expn.
    eapply kappa_inaccessible_rec; auto.
    { eapply kappa_inaccessible_S.
      eapply kappa_inaccessible_O. }
    { i. eapply kappa_inaccessible_mult; auto. }
    { i. eapply ordArith.le_mult_l. auto. }
  Qed.

End STRONGLYINACCESSIBLE.

Create HintDb ord_kappa.
#[export] Hint Resolve kappa_inaccessible_build: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_join: ord_kappa.
#[export] Hint Resolve kappa_inaccesible_from_acc: ord_kappa.
#[export] Hint Resolve kappa_inaccesible_from_wf: ord_kappa.
#[export] Hint Resolve kappa_inaccesible_from_wf_set: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_O: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_S: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_nat: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_omega: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_union: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_add: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_mult: ord_kappa.
#[export] Hint Resolve kappa_inaccessible_expn: ord_kappa.
