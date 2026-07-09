From lantana.ordinal Require Import sflib basics.
From lantana.ordinal Require Export ordinal arithmetic.

From Coq Require Import Classes.RelationClasses Classes.Morphisms.

Set Implicit Arguments.
Set Primitive Projections.

Module hessenberg.
  Section ADD.
    Program Let _add: ord.t * ord.t -> ord.t :=
      Fix (double_rel_well_founded ord.lt_well_founded ord.lt_well_founded) (fun _ => ord.t)
          (fun o0o1 add =>
             match o0o1 with
             | (o0, o1) =>
                 ord.union
                   (match o1 with
                    | @ord.build X1 os1 => ord.build (fun x1 => @add (o0, os1 x1) _)
                    end)
                   (match o0 with
                    | @ord.build X0 os0 => ord.build (fun x0 => @add (os0 x0, o1) _)
                    end)
             end).
    Next Obligation.
      right. econs. reflexivity.
    Qed.
    Next Obligation.
      left. econs. reflexivity.
    Qed.

    Definition add (o0 o1: ord.t): ord.t :=
      _add (o0, o1).

    Let _add_red (o0o1: ord.t * ord.t)
      :
      ord.eq
        (_add o0o1)
        (match o0o1 with
         | (o0, o1) =>
             ord.union
               (match o1 with
                | @ord.build X1 os1 => ord.build (fun x1 => _add (o0, os1 x1))
                end)
               (match o0 with
                | @ord.build X0 os0 => ord.build (fun x0 => _add (os0 x0, o1))
                end)
         end).
    Proof.
      unfold _add. rewrite Fix_equiv; ss.
      { destruct o0o1 as [[] []]. ss. reflexivity. }
      { i. ss. destruct x as [[] []].
        eapply ord.eq_union.
        { split.
          { econs. i. exists a0. eapply H. }
          { econs. i. exists a0. eapply H. }
        }
        { split.
          { econs. i. exists a0. eapply H. }
          { econs. i. exists a0. eapply H. }
        }
      }
    Qed.

    Lemma add_red X0 (os0: X0 -> ord.t) X1 (os1: X1 -> ord.t)
      :
      ord.eq
        (add (@ord.build X0 os0) (@ord.build X1 os1))
        (ord.union
           (ord.build (fun x1 => add (@ord.build X0 os0) (os1 x1)))
           (ord.build (fun x0 => add (os0 x0) (@ord.build X1 os1)))).
    Proof.
      unfold add. apply _add_red.
    Qed.
    Global Opaque add.

    Lemma add_supremum o0 o1 o
          (LE0: forall o2 (LT: ord.lt o2 o0), ord.lt (add o2 o1) o)
          (LE1: forall o2 (LT: ord.lt o2 o1), ord.lt (add o0 o2) o)
      :
      ord.le (add o0 o1) o.
    Proof.
      destruct o0, o1. rewrite add_red.
      apply ord.union_spec.
      { eapply ord.build_supremum. i. eapply LE1. eapply ord.build_upperbound. }
      { eapply ord.build_supremum. i. eapply LE0. eapply ord.build_upperbound. }
    Qed.

    Lemma le_add_l o0 o1 o2 (LE: ord.le o0 o1)
      :
      ord.le (add o0 o2) (add o1 o2).
    Proof.
      revert o0 LE. pattern o1, o2. revert o1 o2.
      eapply (double_well_founded_induction ord.lt_well_founded ord.lt_well_founded).
      i. dup LE. inv LE. destruct b1.
      rewrite add_red. rewrite add_red.
      eapply ord.le_union.
      { econs. i. exists a0. eapply IHR; auto. econs. reflexivity. }
      { econs. i. specialize (LE1 a0). des.
        exists a1. eapply IHL; auto. econs. reflexivity. }
    Qed.

    Lemma le_add_r o0 o1 o2 (LE: ord.le o1 o2)
      :
      ord.le (add o0 o1) (add o0 o2).
    Proof.
      revert o1 LE. pattern o0. pattern o2. revert o0 o2.
      eapply (double_well_founded_induction ord.lt_well_founded ord.lt_well_founded).
      i. dup LE. inv LE. destruct a1.
      rewrite add_red. rewrite add_red.
      eapply ord.le_union.
      { econs. i. specialize (LE1 a0). des.
        exists a1. eapply IHR; auto. econs. reflexivity. }
      { econs. i. exists a0. eapply IHL; auto. econs. reflexivity. }
    Qed.

    Lemma eq_add_l o0 o1 o2 (EQ: ord.eq o0 o1)
      :
      ord.eq (add o0 o2) (add o1 o2).
    Proof.
      econs.
      { eapply le_add_l. eapply EQ. }
      { eapply le_add_l. eapply EQ. }
    Qed.

    Lemma eq_add_r o0 o1 o2 (EQ: ord.eq o1 o2)
      :
      ord.eq (add o0 o1) (add o0 o2).
    Proof.
      econs.
      { eapply le_add_r. eapply EQ. }
      { eapply le_add_r. eapply EQ. }
    Qed.

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

    Lemma lt_add_l o0 o1 o2 (LT: ord.lt o0 o1)
      :
      ord.lt (add o0 o2) (add o1 o2).
    Proof.
      inv LT. destruct o2. rewrite add_red. eapply ord.lt_le_lt.
      2:{ eapply ord.union_r. }
      { eapply ord.le_lt_lt.
        { rewrite LE. reflexivity. }
        { econs. reflexivity. }
      }
    Qed.

    Lemma lt_add_r o0 o1 o2 (LT: ord.lt o1 o2)
      :
      ord.lt (add o0 o1) (add o0 o2).
    Proof.
      inv LT. destruct o0. rewrite add_red. eapply ord.lt_le_lt.
      2:{ eapply ord.union_l. }
      { eapply ord.le_lt_lt.
        { rewrite LE. reflexivity. }
        { econs. reflexivity. }
      }
    Qed.

    Lemma add_spec o0 o1 o2
          (SUP0: forall o (LT: ord.lt o o0), ord.lt (add o o1) o2)
          (SUP1: forall o (LT: ord.lt o o1), ord.lt (add o0 o) o2)
      :
      ord.le (add o0 o1) o2.
    Proof.
      destruct o0, o1. rewrite add_red. eapply ord.union_spec.
      { eapply ord.build_supremum. i. eapply SUP1. econs. reflexivity. }
      { eapply ord.build_supremum. i. eapply SUP0. econs. reflexivity. }
    Qed.

    Lemma add_comm o0 o1
      :
      ord.eq (add o0 o1) (add o1 o0).
    Proof.
      revert o0 o1.
      cut (forall o0 o1, ord.le (add o0 o1) (add o1 o0)).
      { i. split; eauto. }
      i. pattern o0, o1. revert o0 o1.
      eapply (double_well_founded_induction ord.lt_well_founded ord.lt_well_founded).
      i. destruct a1, b1. rewrite add_red. rewrite add_red.
      rewrite ord.union_comm. eapply ord.le_union.
      { econs. i. exists a0. eapply IHL. econs. reflexivity. }
      { econs. i. exists a0. eapply IHR. econs. reflexivity. }
    Qed.

    Lemma add_assoc o0 o1 o2
      :
      ord.eq (add (add o0 o1) o2) (add o0 (add o1 o2)).
    Proof.
      revert o0 o1 o2.
      cut (forall o0 o1o2, (fun o0 o1o2 => (add (add o0 (fst o1o2)) (snd o1o2) == add o0 (add (fst o1o2) (snd o1o2)))%ordi) o0 o1o2).
      { i. eapply (H o0 (o1, o2)). }
      eapply (double_well_founded_induction ord.lt_well_founded (double_rel_well_founded ord.lt_well_founded ord.lt_well_founded)).
      intros o0 [o1 o2] IH0 IH12. ss.
      assert (IH1: forall o (LT: (o < o1)%ordi), (add (add o0 o) o2 == add o0 (add o o2))%ordi).
      { i. eapply (IH12 (o, o2)). left. auto. }
      assert (IH2: forall o (LT: (o < o2)%ordi), (add (add o0 o1) o == add o0 (add o1 o))%ordi).
      { i. eapply (IH12 (o1, o)). right. auto. }
      clear IH12. destruct o0, o1, o2.
      rewrite add_red. rewrite add_red.
      rewrite ord.union_build. rewrite ord.union_build.
      rewrite add_red. rewrite add_red.
      rewrite ord.union_build. rewrite ord.union_build. split.
      { econs.
        { i. destruct a0 as [|[]].
          { exists (inl (inl a)). ss. rewrite <- IH2.
            { rewrite add_red. rewrite ord.union_build. reflexivity. }
            { econs. reflexivity. }
          }
          { exists (inl (inr a)). ss.
            eapply IH1. econs. reflexivity. }
          { exists (inr a). ss. rewrite IH0.
            { rewrite add_red. rewrite ord.union_build. reflexivity. }
            { econs. reflexivity. }
          }
        }
      }
      { econs.
        { i. destruct a0 as [[]|].
          { exists (inl a). ss. rewrite <- IH2.
            { rewrite add_red. rewrite ord.union_build. reflexivity. }
            { econs. reflexivity. }
          }
          { exists (inr (inl a)). ss.
            eapply IH1. econs. reflexivity. }
          { exists (inr (inr a)). ss. rewrite IH0.
            { rewrite add_red. rewrite ord.union_build. reflexivity. }
            { econs. reflexivity. }
          }
        }
      }
    Qed.

    Lemma add_base_l o0 o1
      :
      ord.le o0 (add o0 o1).
    Proof.
      revert o1. pattern o0. revert o0.
      eapply (well_founded_induction ord.lt_well_founded).
      i. destruct x. eapply ord.build_supremum. i.
      eapply ord.le_lt_lt.
      { eapply H. econs. reflexivity. }
      { eapply lt_add_l. econs. reflexivity. }
    Qed.

    Lemma add_base_r o0 o1
      :
      ord.le o1 (add o0 o1).
    Proof.
      rewrite add_comm. eapply add_base_l.
    Qed.

    Lemma arith_add_larger o0 o1
      :
      ord.le (ordArith.add o0 o1) (add o0 o1).
    Proof.
      revert o0. pattern o1. revert o1.
      eapply (well_founded_induction ord.lt_well_founded).
      i. destruct x. rewrite ordArith.add_build. eapply ord.union_spec.
      { eapply add_base_l. }
      { eapply ord.join_supremum. i. eapply ord.S_supremum.
        eapply ord.le_lt_lt.
        { eapply H. econs. reflexivity. }
        { eapply lt_add_r. econs. reflexivity. }
      }
    Qed.

    Lemma add_O_r o
      :
      ord.eq (add o ord.O) o.
    Proof.
      pattern o. revert o. eapply (well_founded_induction ord.lt_well_founded).
      intros o IH. split.
      { eapply add_spec.
        { i. rewrite IH; auto. }
        { i. exfalso. eapply ord.lt_StrictOrder. eapply ord.lt_le_lt.
          { eapply LT. }
          { eapply ord.O_bot. }
        }
      }
      { eapply add_base_l. }
    Qed.

    Lemma add_O_l o
      :
      ord.eq (add ord.O o) o.
    Proof.
      rewrite add_comm. eapply add_O_r.
    Qed.

    Lemma add_S_r o0 o1
      :
      ord.eq (add o0 (ord.S o1)) (ord.S (add o0 o1)).
    Proof.
      revert o1. pattern o0. revert o0.
      eapply (well_founded_induction ord.lt_well_founded). i.
      split.
      { eapply add_spec.
        { i. rewrite H; auto. eapply ord.lt_S. eapply lt_add_l; auto. }
        { i. eapply ord.le_lt_lt; [|eapply ord.S_lt].
          eapply ord.S_supremum in LT. eapply le_add_r.
          eapply ord.le_S_rev; auto.
        }
      }
      { eapply ord.S_supremum. eapply lt_add_r. eapply ord.S_lt. }
    Qed.

    Lemma add_S_l o0 o1
      :
      ord.eq (add (ord.S o0) o1) (ord.S (add o0 o1)).
    Proof.
      rewrite add_comm. rewrite add_S_r. rewrite add_comm. reflexivity.
    Qed.

    Lemma arith_add_from_nat o (n: nat)
      :
      ord.eq (add o n) (ordArith.add o n).
    Proof.
      revert o. induction n; i.
      { rewrite ord.from_nat_O.
        rewrite add_O_r. rewrite ordArith.add_O_r. reflexivity.
      }
      { rewrite ord.from_nat_S.
        rewrite add_S_r. rewrite ordArith.add_S. rewrite IHn. reflexivity.
      }
    Qed.

    Lemma add_from_nat n0 n1:
      ord.eq (n0 + n1) (add (ord.from_nat n0) (ord.from_nat n1)).
    Proof.
      induction n1; ss.
      { rewrite PeanoNat.Nat.add_0_r.
        symmetry. eapply add_O_r. }
      { rewrite PeanoNat.Nat.add_succ_r.
        rewrite ord.from_nat_S.
        rewrite ord.from_nat_S.
        rewrite add_S_r.
        eapply ord.eq_S. auto.
      }
    Qed.

    Lemma add_lt_l o0 o1 (LT: ord.lt ord.O o1): ord.lt o0 (add o0 o1).
    Proof.
      eapply ord.lt_le_lt.
      2:{ eapply arith_add_larger. }
      eapply ordArith.add_lt_l. auto.
    Qed.

    Lemma add_lt_r o0 o1 (LT: ord.lt ord.O o0): ord.lt o1 (add o0 o1).
    Proof.
      rewrite add_comm. apply add_lt_l; auto.
    Qed.
  End ADD.
End hessenberg.

Global Opaque hessenberg.add.

(* following: *)
(* https://arxiv.org/pdf/1501.05747.pdf *)
(* (INTERMEDIATE arithmetic OPERATIONS ON ordinal NUMBERS - HARRY ALTMAN) *)
Module jacobsthal.
  Section MULT.
    Definition mult (o0: ord.t): forall (o1: ord.t), ord.t := ord.orec ord.O (hessenberg.add o0).

    Let _mult_gen_le := hessenberg.add_base_r.
    Let _mult_gen_mon := hessenberg.le_add_r.

    Lemma arith_mult_larger o0 o1
      :
      ord.le (ordArith.mult o0 o1) (mult o0 o1).
    Proof.
      Local Transparent ordArith.mult.
      eapply ord.orec_mon.
      { reflexivity. }
      { i. rewrite LE. rewrite hessenberg.add_comm.
        eapply hessenberg.arith_add_larger.
      }
    Qed.

    Lemma mult_O_r o: ord.eq (mult o ord.O) ord.O.
    Proof.
      eapply (@ord.orec_O ord.O (hessenberg.add o)); auto.
    Qed.

    Lemma mult_S o0 o1: ord.eq (mult o0 (ord.S o1)) (hessenberg.add o0 (mult o0 o1)).
    Proof.
      eapply (@ord.orec_S ord.O (hessenberg.add o0)); auto.
    Qed.

    Lemma mult_join o A (os: A -> ord.t):
      ord.eq (mult o (ord.join os)) (ord.join (fun a => mult o (os a))).
    Proof.
      transitivity (ord.union ord.O (ord.join (fun a => mult o (os a)))).
      { eapply (@ord.orec_join ord.O (hessenberg.add _)); eauto. }
      { eapply ord.union_max. eapply ord.O_bot. }
    Qed.

    Lemma mult_build o A (os: A -> ord.t)
      :
      ord.eq (mult o (ord.build os)) (ord.join (fun a => hessenberg.add o (mult o (os a)))).
    Proof.
      transitivity (ord.union ord.O (ord.join (fun a => hessenberg.add o (mult o (os a))))).
      { eapply (@ord.orec_build ord.O (hessenberg.add _)); eauto. }
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
      eapply (@ord.orec_mon ord.O (hessenberg.add o0) ord.O (hessenberg.add o1)); auto.
      { reflexivity. }
      { i. transitivity (hessenberg.add o0 o4).
        { eapply hessenberg.le_add_r; auto. }
        { eapply hessenberg.le_add_l; auto. }
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
      eapply hessenberg.add_lt_r. auto.
    Qed.

    Lemma mult_O_l o: ord.eq (mult ord.O o) ord.O.
    Proof.
      induction o. etransitivity.
      { eapply mult_build. }
      { split.
        - eapply ord.join_supremum. i.
          transitivity (mult ord.O (os a)); auto.
          { eapply hessenberg.add_O_l. }
          { eapply H. }
        - eapply ord.O_bot. }
    Qed.

    Lemma mult_1_r o: ord.eq (mult o (ord.S ord.O)) o.
    Proof.
      etransitivity.
      { eapply mult_S. }
      etransitivity.
      { eapply hessenberg.eq_add_r. eapply mult_O_r. }
      eapply hessenberg.add_O_r.
    Qed.

    Lemma mult_1_l o: ord.eq (mult (ord.S ord.O) o) o.
    Proof.
      transitivity (ord.orec ord.O ord.S o).
      2: { symmetry. eapply ord.orec_of_S. }
      split.
      { eapply ord.orec_mon.
        { reflexivity. }
        { i. etransitivity.
          { eapply hessenberg.add_S_l. }
          { apply ord.le_S. transitivity o0; auto.
            eapply hessenberg.add_O_l.
          }
        }
      }
      { eapply ord.orec_mon.
        { reflexivity. }
        { i. etransitivity.
          { apply ord.le_S. eapply LE. }
          transitivity (ord.S (hessenberg.add ord.O o1)); auto.
          { apply ord.le_S. eapply hessenberg.add_O_l. }
          { eapply hessenberg.add_S_l. }
        }
      }
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

    Lemma mult_from_nat n0 n1:
      ord.eq (n0 * n1) (mult (ord.from_nat n0) (ord.from_nat n1)).
    Proof.
      induction n1; ss.
      { rewrite PeanoNat.Nat.mul_0_r.
        symmetry. eapply mult_O_r. }
      { rewrite PeanoNat.Nat.mul_succ_r.
        rewrite ord.from_nat_S.
        rewrite mult_S.
        rewrite hessenberg.add_from_nat.
        rewrite hessenberg.add_comm. rewrite IHn1. reflexivity.
      }
    Qed.
  End MULT.

  Section EXPN.

    Let flip A B C (f: A -> B -> C): B -> A -> C := fun b a => f a b.

    Definition expn (o0: ord.t): forall (o1: ord.t), ord.t := ord.orec (ord.S ord.O) (flip mult o0).

    Let expn_gen_mon o o0 o1 (LE: ord.le o0 o1):
      ord.le (flip mult o o0) (flip mult o o1).
    Proof.
      eapply le_mult_l. auto.
    Qed.

    Lemma arith_expn_larger o0 o1
      :
      ord.le (ordArith.expn o0 o1) (expn o0 o1).
    Proof.
      Local Transparent ordArith.expn.
      eapply ord.orec_mon.
      { reflexivity. }
      { i. rewrite LE. unfold flip. apply arith_mult_larger. }
    Qed.

    Section BASE.

      Variable base: ord.t.

      Lemma expn_O: ord.eq (expn base ord.O) (ord.S ord.O).
      Proof.
        eapply (@ord.orec_O (ord.S ord.O) (flip mult base)); auto.
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
          etransitivity. apply mult_1_r. apply le_mult_r. apply ord.S_supremum; auto.
        Qed.

        Lemma expn_S o: ord.eq (expn base (ord.S o)) (mult (expn base o) base).
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

      End POSITIVE.

      Lemma lt_expn_r (TWO: ord.lt (ord.S ord.O) base) o0 o1 (LT: ord.lt o0 o1):
        ord.lt (expn base o0) (expn base o1).
      Proof.
        assert (POS: ord.lt ord.O base).
        { eapply ord.le_lt_lt; eauto. eapply ord.S_le. }
        eapply (@ord.lt_le_lt (expn base (ord.S o0))).
        { eapply ord.lt_eq_lt.
          { eapply expn_S. auto. }
          { eapply ord.le_lt_lt. 2: eapply lt_mult_r. rewrite mult_1_r. reflexivity. auto. apply expn_pos. }
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

    Lemma expn_from_nat n0 (POS: 0 < n0) n1:
      ord.eq (ord.from_nat (Nat.pow n0 n1)) (expn (ord.from_nat n0) (ord.from_nat n1)).
    Proof.
      induction n1; ss.
      { symmetry. eapply expn_O. }
      { etransitivity.
        { rewrite PeanoNat.Nat.mul_comm. eapply mult_from_nat. }
        etransitivity.
        { eapply eq_mult_l. eapply IHn1. }
        symmetry. rewrite ord.from_nat_S. eapply expn_S.
        eapply (@ordArith.lt_from_nat 0 n0). auto.
      }
    Qed.
  End EXPN.

End jacobsthal.

Global Opaque jacobsthal.mult.
Global Opaque jacobsthal.expn.

Module hessenbergScope.
  Infix "⊕" := hessenberg.add (at level 80, right associativity) : ordinal_scope.
  Infix "×" := jacobsthal.mult (at level 80, right associativity) : ordinal_scope.
  Infix "↑" := jacobsthal.expn (at level 80, right associativity) : ordinal_scope.
End hessenbergScope.

Export hessenbergScope.
