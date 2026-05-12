From liris.ordinal Require Import sflib basics.
From liris.ordinal Require Import classical_ordinal wf_rel.
From liris.ordinal Require Export ordinal.

From Coq Require Import FunctionalExtensionality PropExtensionality.
From Coq Require Import Program. (* Axiom K *)

Set Implicit Arguments.
Set Primitive Projections.

Module toSet.
  Definition union_set (A: Type) (Ts: A -> Type): Type := @sigT A (fun a => option (Ts a)).

  Inductive union_rel (A: Type)
            (Ts: A -> Type) (R: forall a, Ts a -> Ts a -> Prop):
    union_set Ts -> union_set Ts -> Prop :=
  | union_rel_top
      a x
    :
      union_rel R (existT _ a (Some x)) (existT _ a None)
  | union_rel_normal
      a x0 x1
      (LT: R a x0 x1)
    :
      union_rel R (existT _ a (Some x0)) (existT _ a (Some x1))
  .

  (* TODO: axiom K necessary? *)
  Lemma union_rel_well_founded (A: Type) (Ts: A -> Type)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
    :
      well_founded (union_rel R).
  Proof.
    assert (forall a x, Acc (union_rel R) (existT _ a (Some x))).
    { intros a. eapply (well_founded_induction (WF a)); auto.
      i. econs. i. dependent destruction H0. eapply H; eauto. }
    ii. destruct a as [a [x|]]; eauto.
    econs. i. inv H0; eauto.
  Qed.

  Lemma from_wf_union (A: Type) (Ts: A -> Type)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
        (a: A) (x: Ts a)
    :
      ord.eq (ord.from_wf (WF a) x)
             (ord.from_wf (union_rel_well_founded R WF) (existT _ a (Some x))).
  Proof.
    revert x. eapply (well_founded_induction (WF a)).
    i. split.
    { eapply ord.from_wf_supremum. i. specialize (H _ LT). inv H.
      eapply ord.le_lt_lt; eauto. eapply ord.lt_from_wf. econs; eauto. }
    { eapply ord.from_wf_supremum. i. dependent destruction LT.
      specialize (H _ LT). inv H.
      eapply ord.le_lt_lt; eauto. eapply ord.lt_from_wf. auto. }
  Qed.

  Lemma from_wf_set_union (A: Type) (Ts: A -> Type)
        (R: forall a, Ts a -> Ts a -> Prop)
        (WF: forall a, well_founded (R a))
    :
      ord.eq (@ord.build A (fun a => ord.from_wf_set (WF a)))
             (ord.from_wf_set (union_rel_well_founded R WF)).
  Proof.
    Local Transparent ord.from_wf_set.
    split.
    { econs. i. exists (existT _ a0 None). eapply ord.build_supremum. i.
      eapply (@ord.le_lt_lt (ord.from_wf (union_rel_well_founded R WF) (existT _ a0 (Some a)))).
      { eapply from_wf_union. }
      { eapply ord.lt_from_wf. econs. }
    }
    { econs. i. destruct a0 as [a0 [x|]].
      { exists a0. transitivity (ord.from_wf (WF a0) x).
        { eapply from_wf_union. }
        { eapply ord.lt_le. eapply ord.from_wf_set_upperbound. }
      }
      { exists a0. eapply ord.from_wf_supremum. i.
        dependent destruction LT.
        eapply (@ord.le_lt_lt (ord.from_wf (WF a0) x)).
        { eapply from_wf_union. }
        { eapply ord.from_wf_set_upperbound. }
      }
    }
  Qed.

  Fixpoint toSet (o: ord.t): @sigT Type (fun A => A -> A -> Prop) :=
    match o with
    | @ord.build A os => existT
                           _
                           (union_set (fun a => projT1 (toSet (os a))))
                           (union_rel (fun a => projT2 (toSet (os a))))
    end.

  Lemma toSet_well_founded: forall o, well_founded (projT2 (toSet o)).
  Proof.
    induction o. ss. eapply union_rel_well_founded; auto.
  Defined.

  Lemma toSet_eq o:
    ord.eq o (ord.from_wf_set (toSet_well_founded o)).
  Proof.
    induction o. etransitivity.
    2: { eapply from_wf_set_union. }
    split.
    { econs. i. exists a0. eapply H. }
    { econs. i. exists a0. eapply H. }
  Qed.

  Section TOTALIFY.
    Variable A: Type.
    Variable R: A -> A -> Prop.
    Hypothesis WF: well_founded R.

    Definition equiv_class: Type :=
      @sig (A -> Prop) (fun s => (exists a, s a) /\
                                 (forall a0 a1 (IN0: s a0), s a1 <-> ord.eq (ord.from_wf WF a0) (ord.from_wf WF a1))).

    Lemma equiv_class_same_ord (s: equiv_class) (a0 a1: A)
          (IN0: proj1_sig s a0) (IN1: proj1_sig s a1)
      :
        ord.eq (ord.from_wf WF a0) (ord.from_wf WF a1).
    Proof.
      destruct s. ss. des. eapply a2; auto.
    Qed.

    Program Definition to_equiv_class (a0: A): equiv_class :=
      exist _ (fun a1 => ord.eq (ord.from_wf WF a0) (ord.from_wf WF a1)) _.
    Next Obligation.
      split.
      { exists a0. reflexivity. }
      { i. split; i.
        - transitivity (ord.from_wf WF a0); eauto. symmetry. auto.
        - transitivity (ord.from_wf WF a1); eauto.
      }
    Qed.

    Let to_equiv_class_equiv a (s: equiv_class) (IN: proj1_sig s a):
      s = to_equiv_class a.
    Proof.
      destruct s. ss. unfold to_equiv_class.
      assert (x = (fun a1 : A => ord.eq (ord.from_wf WF a) (ord.from_wf WF a1))).
      { extensionality a1. eapply propositional_extensionality. des. split.
        { i. eapply a2; eauto. }
        { i. eapply a2; eauto. }
      }
      subst. f_equal. eapply proof_irrelevance.
    Qed.

    Definition equiv_class_rel: equiv_class -> equiv_class -> Prop :=
      fun s0 s1 => exists a0 a1, (proj1_sig s0) a0 /\ (proj1_sig s1) a1 /\ ord.lt (ord.from_wf WF a0) (ord.from_wf WF a1).

    Lemma to_equiv_class_preserve a0 a1 (LT: R a0 a1):
      equiv_class_rel (to_equiv_class a0) (to_equiv_class a1).
    Proof.
      exists a0, a1. ss. splits.
      - reflexivity.
      - reflexivity.
      - eapply ord.lt_from_wf; auto.
    Qed.

    Lemma equiv_class_rel_trans s0 s1 s2
          (LT0: equiv_class_rel s0 s1) (LT1: equiv_class_rel s1 s2)
      :
        equiv_class_rel s0 s2.
    Proof.
      unfold equiv_class_rel in *. des. esplits; eauto.
      transitivity (ord.from_wf WF a3); auto.
      eapply ord.eq_lt_lt; eauto.
      eapply equiv_class_same_ord; eauto.
    Qed.

    Let _equiv_class_extensional s0 s1
          (EXT: forall s, equiv_class_rel s s0 <-> equiv_class_rel s s1)
          a
          (IN: proj1_sig s0 a)
      :
        proj1_sig s1 a.
    Proof.
      Local Transparent ord.from_wf.
      assert (exists a', proj1_sig s1 a').
      { eapply (proj2_sig s1). }
      des. eapply (proj2_sig s1); eauto.
      eapply ord.eq_ext. i. split.
      { i. unfold ord.from_wf in H0. destruct (WF a').
        eapply ord.lt_proj in H0. des. ss. destruct a1; ss.
        hexploit to_equiv_class_preserve; eauto. i.
        assert (equiv_class_rel (to_equiv_class x) s0).
        { eapply EXT. replace s1 with (to_equiv_class a'); auto.
          apply to_equiv_class_equiv in H. auto. }
        unfold equiv_class_rel in H2. des. ss.
        eapply ord.lt_eq_lt.
        { eapply (proj2_sig s0); eauto. }
        eapply ord.le_lt_lt; eauto.
        eapply ord.le_lt_lt; eauto.
        eapply ord.le_eq_le.
        { symmetry. eauto. }
        eapply ord.same_acc_le.
      }
      { i. unfold ord.from_wf in H0. destruct (WF a).
        eapply ord.lt_proj in H0. des. ss. destruct a1; ss.
        hexploit to_equiv_class_preserve; eauto. i.
        assert (equiv_class_rel (to_equiv_class x) s1).
        { eapply EXT. replace s0 with (to_equiv_class a); auto.
          apply to_equiv_class_equiv in IN. auto. }
        unfold equiv_class_rel in H2. des. ss.
        eapply ord.lt_eq_lt.
        { eapply (proj2_sig s1); eauto. }
        eapply ord.le_lt_lt; eauto.
        eapply ord.le_lt_lt; eauto.
        eapply ord.le_eq_le.
        { symmetry. eauto. }
        eapply ord.same_acc_le.
      }
    Qed.

    Lemma equiv_class_extensional s0 s1
          (EXT: forall s, equiv_class_rel s s0 <-> equiv_class_rel s s1)
      :
        s0 = s1.
    Proof.
      assert (proj1_sig s0 = proj1_sig s1).
      { extensionality a. eapply propositional_extensionality. split; i.
        - eapply _equiv_class_extensional; eauto.
        - eapply _equiv_class_extensional; eauto.
          i. symmetry. auto.
      }
      destruct s0, s1. ss. subst. f_equal. eapply proof_irrelevance.
    Qed.

    Lemma equiv_class_well_founded: well_founded equiv_class_rel.
    Proof.
      assert (forall (o: ord.t), forall (s: equiv_class) a0 (IN: proj1_sig s a0) (LT: ord.lt (ord.from_wf WF a0) o), Acc equiv_class_rel s).
      { eapply (well_founded_induction ord.lt_well_founded (fun o => forall (s: equiv_class) a0 (IN: proj1_sig s a0) (LT: ord.lt (ord.from_wf WF a0) o), Acc equiv_class_rel s)).
        i. econs. i. unfold equiv_class_rel in H0. des.
        hexploit (proj2 (proj2_sig s) a0 a2); auto. i. dup H1.
        eapply H3 in H4. clear H3. eapply (H (ord.from_wf WF a0)); eauto.
        eapply ord.lt_eq_lt; eauto.
      }
      ii. hexploit (proj2_sig a); eauto. i. des.
      hexploit (H (ord.S (ord.from_wf WF a0))); eauto. eapply ord.S_lt.
    Qed.

    Lemma to_equiv_class_eq a:
      ord.eq (ord.from_wf WF a) (ord.from_wf equiv_class_well_founded (to_equiv_class a)).
    Proof.
      assert (forall (o: ord.t), forall a (LT: ord.lt (ord.from_wf WF a) o), ord.eq (ord.from_wf WF a) (ord.from_wf equiv_class_well_founded (to_equiv_class a))).
      { eapply (well_founded_induction ord.lt_well_founded (fun o => forall a (LT: ord.lt (ord.from_wf WF a) o), ord.eq (ord.from_wf WF a) (ord.from_wf equiv_class_well_founded (to_equiv_class a)))).
        i. split.
        { eapply ord.from_wf_supremum. i. dup LT0. eapply (ord.lt_from_wf WF) in LT0; eauto.
          hexploit H; eauto. i. eapply ord.le_lt_lt; [eapply H0|].
          eapply ord.lt_from_wf. eapply to_equiv_class_preserve. auto.
        }
        { eapply ord.from_wf_supremum. i. unfold equiv_class_rel in LT0. des. ss.
          hexploit (H _ LT a2).
          { eapply ord.lt_eq_lt; eauto. } i.
          eapply ord.lt_eq_lt; eauto. eapply ord.le_lt_lt; eauto.
          etransitivity; [|eapply H0].
          eapply to_equiv_class_equiv in LT0. subst. reflexivity.
        }
      }
      eapply (H (ord.S (ord.from_wf WF a))). eapply ord.S_lt.
    Qed.

    Lemma from_wf_set_equiv_class:
      ord.eq (ord.from_wf_set WF) (ord.from_wf_set equiv_class_well_founded).
    Proof.
      split.
      { eapply ord.build_supremum. i. eapply ord.eq_lt_lt.
        { eapply to_equiv_class_eq. }
        { eapply ord.from_wf_set_upperbound. }
      }
      { eapply ord.build_supremum. i. hexploit (proj2_sig a). i. des.
        eapply to_equiv_class_equiv in H. subst.
        eapply ord.eq_lt_lt.
        { symmetry. eapply to_equiv_class_eq. }
        { eapply ord.from_wf_set_upperbound. }
      }
    Qed.

    Lemma equiv_class_total:
      forall s0 s1, equiv_class_rel s0 s1 \/ s0 = s1 \/ equiv_class_rel s1 s0.
    Proof.
      i. hexploit (proj2_sig s0). i. des. hexploit (proj2_sig s1). i. des.
      destruct (classicOrd.trichotomy (ord.from_wf WF a) (ord.from_wf WF a0)) as [|[]].
      - left. unfold equiv_class_rel. esplits; eauto.
      - right. left. assert (proj1_sig s0 = proj1_sig s1).
        { extensionality x. eapply propositional_extensionality. split; i.
          - eapply H2; eauto. transitivity (ord.from_wf WF a); eauto.
            + symmetry. auto.
            + eapply (H0 a x); auto.
          - eapply H0; eauto. transitivity (ord.from_wf WF a0); eauto.
            eapply (H2 a0 x); auto.
        }
        destruct s0, s1. ss. subst. f_equal. eapply proof_irrelevance.
      - right. right. unfold equiv_class_rel. esplits; eauto.
    Qed.
  End TOTALIFY.

  Definition to_total_set (o: ord.t): Type := equiv_class (toSet_well_founded o).
  Definition to_total_rel (o: ord.t): (to_total_set o) -> (to_total_set o) -> Prop :=
    @equiv_class_rel _ _ (toSet_well_founded o).
  Arguments to_total_rel: clear implicits.

  Lemma to_total_well_founded (o: ord.t): well_founded (to_total_rel o).
  Proof.
    eapply equiv_class_well_founded.
  Defined.
  Arguments to_total_well_founded: clear implicits.

  Lemma to_total_eq (o: ord.t):
    ord.eq o (ord.from_wf_set (@to_total_well_founded o)).
  Proof.
    etransitivity.
    - eapply toSet_eq.
    - eapply (from_wf_set_equiv_class (@toSet_well_founded o)).
  Qed.

  Lemma to_total_total (o: ord.t):
    forall (x0 x1: to_total_set o), to_total_rel o x0 x1 \/ x0 = x1 \/ to_total_rel o x1 x0.
  Proof.
    eapply equiv_class_total.
  Qed.

  Lemma to_total_exists (o: ord.t):
    exists (A: Type) (R: A -> A -> Prop) (WF: well_founded R),
      ord.eq o (ord.from_wf_set WF) /\
      (forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0).
  Proof.
    eexists _, _, (to_total_well_founded o). splits.
    { eapply to_total_eq. }
    { eapply to_total_total. }
  Qed.
End toSet.
