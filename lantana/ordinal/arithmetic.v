From lantana.ordinal Require Import sflib basics.
From lantana.ordinal Require Export ordinal.

From Coq Require Import Classes.RelationClasses Classes.Morphisms. (* TODO: Use Morphisms *)

Set Implicit Arguments.
Set Primitive Projections.

Module ordArith.
  Section arithmetic.
    Let flip A B C (f: A -> B -> C): B -> A -> C := fun b a => f a b.

    Section ADD.
      Definition add (o0: ord.t): forall (o1: ord.t), ord.t := ord.orec o0 ord.S.

      Let _S_le o: ord.le o (ord.S o).
      Proof.
        eapply ord.S_le.
      Qed.

      Let _le_S o0 o1 (LE: ord.le o0 o1): ord.le (ord.S o0) (ord.S o1).
      Proof.
        apply ord.le_S. auto.
      Qed.

      Lemma add_base_l o0 o1: ord.le o0 (add o0 o1).
      Proof.
        eapply ord.orec_le_base; auto.
      Qed.

      Lemma add_base_r o0 o1: ord.le o1 (add o0 o1).
      Proof.
        transitivity (ord.orec ord.O ord.S o1).
        { eapply ord.orec_of_S. }
        { eapply ord.orec_mon; auto. eapply ord.O_bot. }
      Qed.

      Lemma add_O_r o: ord.eq (add o ord.O) o.
      Proof.
        eapply (@ord.orec_O o ord.S); auto.
      Qed.

      Lemma add_S o0 o1: ord.eq (add o0 (ord.S o1)) (ord.S (add o0 o1)).
      Proof.
        eapply (@ord.orec_S o0 ord.S); auto.
      Qed.

      Lemma add_join o A (os: A -> ord.t):
        ord.eq (add o (ord.join os)) (ord.union o (ord.join (fun a => add o (os a)))).
      Proof.
        eapply (@ord.orec_join o ord.S); eauto.
      Qed.

      Lemma add_join_inhabited o A (os: A -> ord.t)
            (INHABITED: inhabited A):
        ord.eq (add o (ord.join os)) (ord.join (fun a => add o (os a))).
      Proof.
        eapply (@ord.orec_join_inhabited o ord.S); eauto.
      Qed.

      Lemma add_build o A (os: A -> ord.t)
        :
          ord.eq (add o (ord.build os)) (ord.union o (ord.join (fun a => ord.S (add o (os a))))).
      Proof.
        eapply ord.orec_build.
      Qed.

      Lemma add_union o0 o1 o2
        :
          ord.eq (add o0 (ord.union o1 o2)) (ord.union (add o0 o1) (add o0 o2)).
      Proof.
        eapply ord.orec_union; auto.
      Qed.

      Lemma le_add_r o0 o1 o2 (LE: ord.le o1 o2)
        :
          ord.le (add o0 o1) (add o0 o2).
      Proof.
        eapply ord.le_orec; auto.
      Qed.

      Lemma lt_add_r o0 o1 o2 (LT: ord.lt o1 o2)
        :
          ord.lt (add o0 o1) (add o0 o2).
      Proof.
        eapply ord.S_supremum in LT.
        eapply ord.lt_le_lt.
        2: { eapply le_add_r. eapply LT. }
        eapply ord.lt_eq_lt.
        { eapply add_S. }
        eapply ord.S_lt.
      Qed.

      Lemma eq_add_r o0 o1 o2 (EQ: ord.eq o1 o2)
        :
          ord.eq (add o0 o1) (add o0 o2).
      Proof.
        split.
        - eapply le_add_r; eauto. eapply EQ.
        - eapply le_add_r; eauto. eapply EQ.
      Qed.

      Lemma le_add_l o0 o1 o2 (LE: ord.le o0 o1)
        :
          ord.le (add o0 o2) (add o1 o2).
      Proof.
        eapply (@ord.orec_mon o0 ord.S o1 ord.S); auto.
      Qed.

      Lemma eq_add_l o0 o1 o2 (EQ: ord.eq o0 o1)
        :
          ord.eq (add o0 o2) (add o1 o2).
      Proof.
        split.
        - eapply le_add_l; eauto. eapply EQ.
        - eapply le_add_l; eauto. eapply EQ.
      Qed.

      Lemma add_O_l o: ord.eq (add ord.O o) o.
      Proof.
        induction o. etransitivity.
        { eapply add_build. }
        { split.
          - eapply ord.union_spec.
            + eapply ord.O_bot.
            + eapply ord.join_supremum. i. eapply ord.S_supremum.
              eapply ord.eq_lt_lt.
              * eapply H.
              * eapply ord.build_upperbound.
          - eapply ord.build_supremum. i.
            eapply (@ord.lt_le_lt (ord.join (fun a0 => ord.S (ord.orec ord.O ord.S (os a0))))).
            2: { eapply ord.union_r. }
            eapply ord.eq_lt_lt.
            { symmetry. eapply H. }
            eapply ord.lt_le_lt.
            { eapply ord.S_lt. }
            { eapply (@ord.join_upperbound _ (fun a0 => ord.S (ord.orec ord.O ord.S (os a0)))). }
        }
      Qed.

      Lemma add_assoc o0 o1 o2: ord.eq (add (add o0 o1) o2) (add o0 (add o1 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply add_build. } etransitivity.
        2: {
          eapply eq_add_r; auto.
          { symmetry. eapply add_build. }
        }
        etransitivity.
        2: { symmetry. eapply add_union; auto. }
        split.
        { eapply ord.union_spec.
          { eapply ord.union_l. }
          { eapply ord.join_supremum. i. etransitivity.
            { apply ord.le_S. eapply H. }
            etransitivity.
            2: { eapply ord.union_r. }
            etransitivity.
            2: {
              eapply le_add_r.
              eapply (@ord.join_upperbound _ (fun a0 : A => ord.S (add o1 (os a0))) a).
            }
            eapply add_S.
          }
        }
        { eapply ord.union_spec.
          { eapply ord.union_l. }
          etransitivity.
          { eapply add_join. }
          eapply ord.union_spec.
          { etransitivity.
            { eapply add_base_l. }
            { eapply ord.union_l. }
          }
          etransitivity.
          2: { eapply ord.union_r. }
          eapply ord.le_join. i. exists a0.
          etransitivity.
          { eapply add_S. }
          { apply ord.le_S. eapply H. }
        }
      Qed.

      Lemma add_lt_l o0 o1 (LT: ord.lt ord.O o1): ord.lt o0 (add o0 o1).
      Proof.
        eapply ord.S_supremum in LT. eapply (@ord.lt_le_lt (add o0 (ord.S ord.O))).
        { eapply ord.lt_eq_lt.
          { eapply add_S. }
          eapply ord.lt_le_lt.
          { eapply ord.S_lt. }
          eapply ord.le_S. eapply add_base_l.
        }
        { eapply le_add_r. auto. }
      Qed.
    End ADD.

    Section RECAPP.
      Variable D: Type.
      Variable next: D -> D.
      Variable djoin: forall (A: Type) (ds: A -> D), D.

      Variable dle: D -> D -> Prop.
      Variable wf: D -> Prop.

      Hypothesis dle_reflexive: forall d (WF: wf d), dle d d.
      Hypothesis dle_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: dle d0 d1) (LE1: dle d1 d2),
          dle d0 d2.

      Hypothesis djoin_upperbound: forall A (ds: A -> D) (a: A) (WF: forall a, wf (ds a)), dle (ds a) (djoin ds).
      Hypothesis djoin_supremum: forall A (ds: A -> D) (d: D) (WF: forall a, wf (ds a)) (WFD: wf d) (LE: forall a, dle (ds a) d), dle (djoin ds) d.
      Hypothesis djoin_wf: forall A (ds: A -> D) (WF: forall a, wf (ds a)), wf (djoin ds).

      Hypothesis next_wf: forall d (WF: wf d), wf (next d).

      Hypothesis next_le: forall d (WF: wf d), dle d (next d).
      Hypothesis next_mon: forall d0 d1 (WF0: wf d0) (WF1: wf d1) (LE: dle d0 d1), dle (next d0) (next d1).

      Let deq: D -> D -> Prop :=
        fun d0 d1 => dle d0 d1 /\ dle d1 d0.

      Let dunion (d0 d1: D): D := djoin (fun b: bool => if b then d0 else d1).

      Let dunion_l d0 d1 (WF0: wf d0) (WF1: wf d1): dle d0 (dunion d0 d1).
      Proof.
        eapply (@djoin_upperbound _ (fun b: bool => if b then d0 else d1) true). i. destruct a; auto.
      Qed.

      Let dunion_r d0 d1 (WF0: wf d0) (WF1: wf d1): dle d1 (dunion d0 d1).
      Proof.
        eapply (@djoin_upperbound _ (fun b: bool => if b then d0 else d1) false). i. destruct a; auto.
      Qed.

      Let dunion_supremum d0 d1 u (WF0: wf d0) (WF1: wf d1) (WFU: wf u) (LE0: dle d0 u) (LE1: dle d1 u):
        dle (dunion d0 d1) u.
      Proof.
        eapply djoin_supremum; auto.
        { i. destruct a; auto. }
        { i. destruct a; auto. }
      Qed.

      Let dunion_wf d0 d1 (WF0: wf d0) (WF1: wf d1): wf (dunion d0 d1).
      Proof.
        eapply djoin_wf. i. destruct a; auto.
      Qed.

      Let drec_wf base (WF: wf base) o: wf (ord.rec base next djoin o).
      Proof.
        eapply (ord.rec_wf base next djoin dle wf); auto.
      Qed.

      Let drec_rec_wf base (WF: wf base) o0 o1:
        wf (ord.rec (ord.rec base next djoin o0) next djoin o1).
      Proof.
        eapply (ord.rec_wf _ next djoin dle wf); auto.
      Qed.

      Let djoin_le A (ds0 ds1: A -> D)
          (WF0: forall a, wf (ds0 a))
          (WF1: forall a, wf (ds1 a))
          (LE: forall a, dle (ds0 a) (ds1 a))
        :
          dle (djoin ds0) (djoin ds1).
      Proof.
        eapply djoin_supremum; auto.
        i. eapply (@dle_transitive (ds1 a)); auto.
      Qed.

      Let djoin_eq A (ds0 ds1: A -> D)
          (WF0: forall a, wf (ds0 a))
          (WF1: forall a, wf (ds1 a))
          (EQ: forall a, deq (ds0 a) (ds1 a))
        :
          deq (djoin ds0) (djoin ds1).
      Proof.
        split.
        { eapply djoin_le; auto. i. eapply EQ. }
        { eapply djoin_le; auto. i. eapply EQ. }
      Qed.

      Let dunion_le dl0 dl1 dr0 dr1
          (WFL0: wf dl0) (WFL1: wf dl1) (WFR0: wf dr0) (WFR1: wf dr1)
          (LEL: dle dl0 dl1) (LER: dle dr0 dr1):
        dle (dunion dl0 dr0) (dunion dl1 dr1).
      Proof.
        eapply djoin_le.
        { i. destruct a; auto. }
        { i. destruct a; auto. }
        { i. destruct a; auto. }
      Qed.

      Let next_eq d0 d1
          (WF0: wf d0) (WF1: wf d1) (EQ: deq d0 d1)
        :
          deq (next d0) (next d1).
      Proof.
        split; eapply next_mon; auto; apply EQ.
      Qed.

      Let dunion_eq dl0 dl1 dr0 dr1
          (WFL0: wf dl0) (WFL1: wf dl1) (WFR0: wf dr0) (WFR1: wf dr1)
          (EQL: deq dl0 dl1) (EQR: deq dr0 dr1):
        deq (dunion dl0 dr0) (dunion dl1 dr1).
      Proof.
        eapply djoin_eq; auto.
        { i. destruct a; auto. }
        { i. destruct a; auto. }
        { i. destruct a; auto. }
      Qed.

      Let deq_transitive: forall d1 d0 d2 (WF0: wf d0) (WF1: wf d1) (WF2: wf d2) (LE0: deq d0 d1) (LE1: deq d1 d2),
          deq d0 d2.
      Proof.
        i. inv LE0. inv LE1. split; eauto.
      Qed.

      Let drec_red base A (os: A -> ord.t):
        ord.rec base next djoin (ord.build os) =
        dunion base (djoin (fun a => next (ord.rec base next djoin (os a)))).
      Proof.
        eapply ord.rec_red.
      Qed.

      Lemma rec_app base o0 o1 (WF: wf base):
        deq (ord.rec base next djoin (add o0 o1)) (ord.rec (ord.rec base next djoin o0) next djoin o1).
      Proof.
        Local Transparent ord.rec ord.union.
        induction o1.

        eapply (@deq_transitive (dunion (ord.rec base next djoin o0) (dunion base (djoin (fun a => next (ord.rec (ord.rec base next djoin o0) next djoin (os a))))))); auto.
        { eapply dunion_wf; auto. }
        { eapply (@deq_transitive (ord.rec base next djoin (ord.union o0 (ord.join (fun a : A => ord.S (add o0 (os a))))))); auto.
          { eapply dunion_wf; auto. }
          { eapply (@ord.eq_rec _ base next djoin dle wf); auto.
            symmetry. eapply add_build. }
          eapply (@deq_transitive (dunion (ord.rec base next djoin o0) (ord.rec base next djoin (ord.join (fun a : A => ord.S (add o0 (os a))))))); auto.
          { eapply dunion_wf; auto. }
          { eapply (ord.rec_union base next djoin dle wf); auto. }
          eapply dunion_eq; auto.
          { split; apply dle_reflexive; auto. }
          { eapply (@deq_transitive (dunion base (djoin (fun a : A => ord.rec base next djoin ((fun a0 : A => ord.S (add o0 (os a0))) a))))); auto.
            { eapply (ord.rec_join base next djoin dle wf); auto. }
            { eapply dunion_eq; auto.
              { split; auto. }
              { eapply djoin_eq; auto. i.
                eapply (@deq_transitive (next (ord.rec base next djoin (add o0 (os a))))); auto.
                eapply (ord.rec_S base next djoin dle wf); auto.
              }
            }
          }
        }

        rewrite drec_red. split.
        { eapply dunion_supremum; auto.
          eapply dunion_supremum; auto.
          eapply (@dle_transitive (ord.rec base next djoin o0)); auto.
          eapply (ord.rec_le_base base next djoin dle wf); auto.
        }
        { eapply dunion_le; auto. }
      Qed.
    End RECAPP.

    Section ORECAPP.
      Variable next: ord.t -> ord.t.
      Hypothesis next_le: forall o, ord.le o (next o).
      Hypothesis next_mon: forall o0 o1 (LE: ord.le o0 o1), ord.le (next o0) (next o1).

      Lemma orec_app base o0 o1:
        ord.eq (ord.orec base next (add o0 o1)) (ord.orec (ord.orec base next o0) next o1).
      Proof.
        eapply (rec_app next ord.join ord.le (fun _ => True)); auto.
        { i. reflexivity. }
        { i. transitivity d1; auto. }
        { i. eapply ord.join_upperbound. }
        { i. eapply ord.join_supremum. auto. }
      Qed.
    End ORECAPP.


    Section MULT.
      Definition mult (o0: ord.t): forall (o1: ord.t), ord.t := ord.orec ord.O (flip add o0).

      Lemma mult_gen_le o0 o1: ord.le o1 (flip add o0 o1).
      Proof.
        eapply add_base_l.
      Qed.
      Let _mult_gen_le := mult_gen_le.

      Lemma mult_gen_mon o o0 o1 (LE: ord.le o0 o1): ord.le (flip add o o0) (flip add o o1).
      Proof.
        eapply le_add_l. auto.
      Qed.
      Let _mult_gen_mon := mult_gen_mon.

      Lemma mult_O_r o: ord.eq (mult o ord.O) ord.O.
      Proof.
        eapply (@ord.orec_O ord.O (flip add o)); auto.
      Qed.

      Lemma mult_S o0 o1: ord.eq (mult o0 (ord.S o1)) (add (mult o0 o1) o0).
      Proof.
        eapply (@ord.orec_S ord.O (flip add o0)); auto.
      Qed.

      Lemma mult_join o A (os: A -> ord.t):
        ord.eq (mult o (ord.join os)) (ord.join (fun a => mult o (os a))).
      Proof.
        transitivity (ord.union ord.O (ord.join (fun a => mult o (os a)))).
        { eapply (@ord.orec_join ord.O (flip add _)); eauto. }
        { eapply ord.union_max. eapply ord.O_bot. }
      Qed.

      Lemma mult_build o A (os: A -> ord.t)
        :
          ord.eq (mult o (ord.build os)) (ord.join (fun a => add (mult o (os a)) o)).
      Proof.
        transitivity (ord.union ord.O (ord.join (fun a => add (mult o (os a)) o))).
        { eapply (@ord.orec_build ord.O (flip add _)); eauto. }
        { eapply ord.union_max. eapply ord.O_bot. }
      Qed.

      Lemma mult_union o0 o1 o2
        :
          ord.eq (mult o0 (ord.union o1 o2)) (ord.union (mult o0 o1) (mult o0 o2)).
      Proof.
        eapply ord.orec_union; auto.
      Qed.

      Lemma le_mult_r o0 o1 o2 (LE: ord.le o1 o2)
        :
          ord.le (mult o0 o1) (mult o0 o2).
      Proof.
        eapply ord.le_orec; auto.
      Qed.

      Lemma eq_mult_r o0 o1 o2 (EQ: ord.eq o1 o2)
        :
          ord.eq (mult o0 o1) (mult o0 o2).
      Proof.
        split.
        - eapply le_mult_r; eauto. eapply EQ.
        - eapply le_mult_r; eauto. eapply EQ.
      Qed.

      Lemma le_mult_l o0 o1 o2 (LE: ord.le o0 o1)
        :
          ord.le (mult o0 o2) (mult o1 o2).
      Proof.
        eapply (@ord.orec_mon ord.O (flip add o0) ord.O (flip add o1)); auto.
        { reflexivity. }
        { i. unfold flip. transitivity (add o4 o0).
          { eapply le_add_l; auto. }
          { eapply le_add_r; auto. }
        }
      Qed.

      Lemma eq_mult_l o0 o1 o2 (EQ: ord.eq o0 o1)
        :
          ord.eq (mult o0 o2) (mult o1 o2).
      Proof.
        split.
        - eapply le_mult_l; eauto. eapply EQ.
        - eapply le_mult_l; eauto. eapply EQ.
      Qed.

      Lemma lt_mult_r o0 o1 o2 (LT: ord.lt o1 o2) (POS: ord.lt ord.O o0)
        :
          ord.lt (mult o0 o1) (mult o0 o2).
      Proof.
        eapply ord.S_supremum in LT.
        eapply ord.lt_le_lt.
        2: { eapply le_mult_r. eapply LT. }
        eapply ord.lt_eq_lt.
        { eapply mult_S. }
        eapply add_lt_l. auto.
      Qed.

      Lemma mult_O_l o: ord.eq (mult ord.O o) ord.O.
      Proof.
        induction o. etransitivity.
        { eapply mult_build. }
        { split.
          - eapply ord.join_supremum. i.
            transitivity (mult ord.O (os a)); auto.
            { eapply add_O_r. }
            { eapply H. }
          - eapply ord.O_bot. }
      Qed.

      Lemma mult_1_r o: ord.eq (mult o (ord.S ord.O)) o.
      Proof.
        etransitivity.
        { eapply mult_S. }
        etransitivity.
        { eapply eq_add_l. eapply mult_O_r. }
        eapply add_O_l.
      Qed.

      Lemma mult_1_l o: ord.eq (mult (ord.S ord.O) o) o.
      Proof.
        transitivity (ord.orec ord.O ord.S o).
        2: { symmetry. eapply ord.orec_of_S. }
        split.
        { eapply ord.orec_mon.
          { reflexivity. }
          { i. unfold flip. etransitivity.
            { eapply add_S. }
            { apply ord.le_S. transitivity o0; auto.
              eapply add_O_r.
            }
          }
        }
        { eapply ord.orec_mon.
          { reflexivity. }
          { i. unfold flip. etransitivity.
            { apply ord.le_S. eapply LE. }
            transitivity (ord.S (add o1 ord.O)); auto.
            { apply ord.le_S. eapply add_O_r. }
            { eapply add_S. }
          }
        }
      Qed.

      Lemma mult_dist o0 o1 o2: ord.eq (mult o0 (add o1 o2)) (add (mult o0 o1) (mult o0 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply eq_mult_r. eapply add_build. }
        etransitivity.
        2: { eapply eq_add_r. symmetry. eapply mult_build. }
        etransitivity.
        { eapply mult_union. }
        etransitivity.
        { eapply ord.eq_union.
          { reflexivity. }
          { eapply mult_join. }
        }
        etransitivity.
        2: { symmetry. eapply add_join. }
        eapply ord.eq_union.
        { reflexivity. } split.
        { eapply ord.le_join. i. exists a0.
          etransitivity.
          { eapply mult_S. }
          etransitivity.
          { eapply eq_add_l. symmetry. eapply H. }
          eapply add_assoc.
        }
        { eapply ord.le_join. i. exists a0.
          etransitivity.
          { eapply add_assoc. }
          etransitivity.
          { eapply eq_add_l. eapply H. }
          eapply mult_S.
        }
      Qed.

      Lemma mult_assoc o0 o1 o2: ord.eq (mult (mult o0 o1) o2) (mult o0 (mult o1 o2)).
      Proof.
        revert o0 o1. induction o2. i. etransitivity.
        { eapply mult_build. } etransitivity.
        2: {
          eapply eq_mult_r; auto.
          { symmetry. eapply mult_build. }
        }
        etransitivity.
        2: { symmetry. eapply mult_join. }
        split.
        { eapply ord.le_join. i. exists a0.
          etransitivity.
          { eapply le_add_l. eapply H. }
          { eapply mult_dist. }
        }
        { eapply ord.le_join. i. exists a0.
          etransitivity.
          { eapply mult_dist. }
          { eapply le_add_l. eapply H. }
        }
      Qed.

      Lemma mult_le_l o0 o1 (POS: ord.lt ord.O o0): ord.le o1 (mult o1 o0).
      Proof.
        eapply ord.S_supremum in POS. etransitivity.
        2: { eapply le_mult_r in POS. eauto. }
        eapply mult_1_r.
      Qed.

      Lemma mult_lt_l o0 o1 (POS: ord.lt ord.O o1)
            (TWO: ord.lt (ord.S ord.O) o0): ord.lt o1 (mult o1 o0).
      Proof.
        eapply ord.S_supremum in TWO. eapply (@ord.lt_le_lt (mult o1 (ord.S (ord.S ord.O)))).
        { eapply ord.lt_eq_lt.
          { eapply mult_S. }
          eapply ord.lt_eq_lt.
          { eapply eq_add_l. eapply mult_S. }
          eapply ord.lt_eq_lt.
          { eapply add_assoc. }
          eapply ord.lt_le_lt.
          2: { eapply add_base_r. }
          eapply add_lt_l. apply POS.
        }
        { eapply le_mult_r. auto. }
      Qed.

    End MULT.


    Section EXPN.
      Definition expn (o0: ord.t): forall (o1: ord.t), ord.t := ord.orec (ord.S ord.O) (flip mult o0).

      Let expn_gen_mon o o0 o1 (LE: ord.le o0 o1):
        ord.le (flip mult o o0) (flip mult o o1).
      Proof.
        eapply le_mult_l. auto.
      Qed.

      Section BASE.
        Variable base: ord.t.

        Lemma expn_O o: ord.eq (expn o ord.O) (ord.S ord.O).
        Proof.
          eapply ord.orec_O; auto.
        Qed.

        Lemma expn_pos o: ord.lt ord.O (expn base o).
        Proof.
          eapply ord.lt_le_lt.
          { eapply ord.S_lt. }
          { eapply ord.orec_le_base. auto. }
        Qed.

        Section POSITIVE.
          Hypothesis POS: ord.lt ord.O base.

          Let expn_gen_le o: ord.le o (flip mult base o).
          Proof.
            eapply mult_le_l; auto.
          Qed.

          Lemma expn_S o:
            ord.eq (expn base (ord.S o)) (mult (expn base o) base).
          Proof.
            eapply ord.orec_S; auto.
          Qed.

          Lemma le_expn_r o0 o1 (LE: ord.le o0 o1):
            ord.le (expn base o0) (expn base o1).
          Proof.
            eapply ord.le_orec; auto.
          Qed.

          Lemma eq_expn_r o0 o1 (EQ: ord.eq o0 o1):
            ord.eq (expn base o0) (expn base o1).
          Proof.
            eapply ord.eq_orec; auto.
          Qed.

          Lemma expn_join A (os: A -> ord.t):
            ord.eq (expn base (ord.join os)) (ord.union (ord.S ord.O) (ord.join (fun a => expn base (os a)))).
          Proof.
            eapply ord.orec_join; auto.
          Qed.

          Lemma expn_join_inhabited A (os: A -> ord.t)
                (INHABITED: inhabited A):
            ord.eq (expn base (ord.join os)) (ord.join (fun a => expn base (os a))).
          Proof.
            eapply ord.orec_join_inhabited; auto.
          Qed.

          Lemma expn_build A (os: A -> ord.t):
            ord.eq (expn base (ord.build os)) (ord.union (ord.S ord.O) (ord.join (fun a => mult (expn base (os a)) base))).
          Proof.
            eapply ord.orec_build.
          Qed.

          Lemma expn_union o0 o1
            :
              ord.eq (expn base (ord.union o0 o1)) (ord.union (expn base o0) (expn base o1)).
          Proof.
            eapply ord.orec_union; auto.
          Qed.

          Lemma expn_1_r: ord.eq (expn base (ord.S ord.O)) base.
          Proof.
            etransitivity.
            { eapply expn_S. }
            etransitivity.
            { eapply eq_mult_l. eapply expn_O. }
            eapply mult_1_l.
          Qed.

          Lemma expn_add o0 o1:
            ord.eq (expn base (add o0 o1)) (mult (expn base o0) (expn base o1)).
          Proof.
            revert o0. induction o1. i. etransitivity.
            { eapply eq_expn_r. eapply add_build. }
            etransitivity.
            { eapply expn_union. }
            etransitivity.
            2: { eapply eq_mult_r. symmetry. eapply expn_build. }
            etransitivity.
            2: { symmetry. eapply mult_union. }
            etransitivity.
            { eapply ord.eq_union.
              { reflexivity. }
              eapply expn_join.
            }
            etransitivity.
            { eapply ord.union_assoc. }
            eapply ord.eq_union.
            { etransitivity.
              { eapply ord.union_comm. }
              { etransitivity.
                2: { symmetry. eapply mult_1_r. }
                { eapply ord.union_max. eapply ord.S_supremum. eapply expn_pos. }
              }
            }
            etransitivity.
            2: { symmetry. eapply mult_join. }
            eapply ord.eq_join. i.
            etransitivity.
            { eapply expn_S. }
            etransitivity.
            2: { eapply mult_assoc. }
            eapply eq_mult_l.
            eapply H.
          Qed.
        End POSITIVE.

        Lemma lt_expn_r (TWO: ord.lt (ord.S ord.O) base) o0 o1 (LT: ord.lt o0 o1):
          ord.lt (expn base o0) (expn base o1).
        Proof.
          assert (POS: ord.lt ord.O base).
          { eapply ord.le_lt_lt; eauto. eapply ord.S_le. }
          eapply (@ord.lt_le_lt (expn base (ord.S o0))).
          { eapply ord.lt_eq_lt.
            { eapply expn_S. auto. }
            { eapply mult_lt_l; auto. eapply expn_pos. }
          }
          { eapply le_expn_r. eapply ord.S_supremum. auto. }
        Qed.
      End BASE.

      Lemma expn_1_l o: ord.eq (expn (ord.S ord.O) o) (ord.S ord.O).
      Proof.
        induction o. etransitivity.
        { eapply expn_build. }
        etransitivity.
        { eapply ord.union_comm. }
        eapply ord.union_max. eapply ord.join_supremum.
        i. eapply ord.eq_le_le.
        { eapply mult_1_r. }
        eapply H.
      Qed.

      Lemma le_expn_l o0 o1 o2 (LE: ord.le o0 o1):
        ord.le (expn o0 o2) (expn o1 o2).
      Proof.
        eapply ord.orec_mon.
        { reflexivity. }
        { i. transitivity (mult o3 o1).
          { eapply le_mult_r. auto. }
          { eapply le_mult_l. auto. }
        }
      Qed.

      Lemma eq_expn_l o0 o1 o2 (EQ: ord.eq o0 o1):
        ord.eq (expn o0 o2) (expn o1 o2).
      Proof.
        split; eapply le_expn_l; apply EQ.
      Qed.

      Lemma expn_mult o0 (POS: ord.lt ord.O o0) o1 o2:
        ord.eq (expn o0 (mult o1 o2)) (expn (expn o0 o1) o2).
      Proof.
        induction o2.
        etransitivity.
        { eapply eq_expn_r. eapply mult_build. }
        etransitivity.
        { eapply expn_join. auto. }
        etransitivity.
        2: { symmetry. eapply expn_build. }
        eapply ord.eq_union.
        { reflexivity. }
        eapply ord.eq_join. i.
        etransitivity.
        { eapply expn_add. auto. }
        eapply eq_mult_l. auto.
      Qed.
    End EXPN.

    Section PROPER.
      Global Program Instance add_eq_proper: Proper (ord.eq ==> ord.eq ==> ord.eq) (add).
      Next Obligation.
        ii.
        etransitivity.
        - eapply eq_add_l; eauto.
        - eapply eq_add_r; eauto.
      Qed.

      Global Program Instance add_le_proper: Proper (ord.le ==> ord.le ==> ord.le) (add).
      Next Obligation.
        ii.
        etransitivity.
        - eapply le_add_l; eauto.
        - eapply le_add_r; eauto.
      Qed.

      Global Program Instance mult_eq_proper: Proper (ord.eq ==> ord.eq ==> ord.eq) (mult).
      Next Obligation.
        ii.
        etransitivity.
        - eapply eq_mult_l; eauto.
        - eapply eq_mult_r; eauto.
      Qed.

      Global Program Instance mult_le_proper: Proper (ord.le ==> ord.le ==> ord.le) (mult).
      Next Obligation.
        ii.
        etransitivity.
        - eapply le_mult_l; eauto.
        - eapply le_mult_r; eauto.
      Qed.

      Global Program Instance expn_eq_proper: Proper (ord.eq ==> ord.eq ==> ord.eq) (expn).
      Next Obligation.
        ii.
        etransitivity.
        - eapply eq_expn_l; eauto.
        - eapply eq_expn_r; eauto.
      Qed.

      Global Program Instance expn_le_proper: Proper (ord.le ==> ord.le ==> ord.le) (expn).
      Next Obligation.
        ii.
        etransitivity.
        - eapply le_expn_l; eauto.
        - eapply le_expn_r; eauto.
      Qed.
    End PROPER.

    Section FROMNAT.
      Lemma le_from_nat n0 n1 (LE: Peano.le n0 n1):
        ord.le n0 n1.
      Proof.
        induction LE.
        { reflexivity. }
        { etransitivity; eauto. ss. eapply ord.S_le. }
      Qed.

      Lemma lt_from_nat n0 n1 (LT: Peano.lt n0 n1):
        ord.lt n0 n1.
      Proof.
        eapply ord.lt_le_lt.
        2: { eapply le_from_nat. eapply LT. }
        { ss. eapply ord.S_lt. }
      Qed.

      Lemma add_from_nat n0 n1:
        ord.eq (n0 + n1) (add (ord.from_nat n0) (ord.from_nat n1)).
      Proof.
        Local Transparent ord.from_nat.
        induction n1; ss.
        { rewrite PeanoNat.Nat.add_0_r.
          symmetry. eapply add_O_r. }
        { rewrite PeanoNat.Nat.add_succ_r. ss.
          etransitivity.
          { eapply ord.eq_S. eapply IHn1. }
          symmetry. eapply add_S.
        }
      Qed.

      Lemma mult_from_nat n0 n1:
        ord.eq (ord.from_nat (n0 * n1)) (mult (ord.from_nat n0) (ord.from_nat n1)).
      Proof.
        induction n1; ss.
        { rewrite PeanoNat.Nat.mul_0_r.
          symmetry. eapply mult_O_r. }
        { rewrite PeanoNat.Nat.mul_succ_r.
          etransitivity.
          { eapply add_from_nat. }
          etransitivity.
          { eapply eq_add_l. eapply IHn1. }
          symmetry. eapply mult_S.
        }
      Qed.

      Lemma expn_from_nat n0 (POS: 0 < n0) n1:
        ord.eq (ord.from_nat (Nat.pow n0 n1)) (expn (ord.from_nat n0) (ord.from_nat n1)).
      Proof.
        induction n1; ss.
        { symmetry. eapply expn_O. }
        { etransitivity.
          { rewrite PeanoNat.Nat.mul_comm. eapply mult_from_nat. }
          etransitivity.
          { eapply eq_mult_l. eapply IHn1. }
          symmetry. eapply expn_S.
          eapply (@lt_from_nat 0 n0). auto.
        }
      Qed.
    End FROMNAT.
  End arithmetic.
End ordArith.


Global Opaque ordArith.add ordArith.mult ordArith.expn.

Module arithmeticScope.
  Infix "+" := ordArith.add : ordinal_scope.
  Infix "*" := ordArith.mult : ordinal_scope.
  Infix "^" := ordArith.expn : ordinal_scope.
End arithmeticScope.

Export arithmeticScope.
