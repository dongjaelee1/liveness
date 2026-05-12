From liris.ordinal Require Import sflib basics.
From liris.ordinal Require Import classical_ordinal wf_rel well_ordering.
From liris.ordinal Require Export ordinal to_set.

From Coq Require Import Classes.RelationClasses.
From Coq Require Import ClassicalChoice FunctionalExtensionality PropExtensionality.
From Coq Require Import Program.

Set Implicit Arguments.
Set Primitive Projections.

Module cardinal.
  Section cardinalITY.
    Variant _cardinal_le (A B: Type): Prop :=
    | _cardinal_le_intro
        (f: A -> B)
        (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
    .

    Let _cardinal_eq (A B: Type): Prop := _cardinal_le A B /\ _cardinal_le B A.
    Let _cardinal_lt (A B: Type): Prop := _cardinal_le A B /\ ~ _cardinal_le B A.

    Let _cardinal_total_le: forall (A B: Type), _cardinal_le A B \/ _cardinal_le B A.
    Proof.
      i. hexploit (set_comparable A B). i. des.
      - left. econs; eauto.
      - right. econs; eauto.
    Qed.

    Lemma _cardinal_le_power A B (LE: _cardinal_le A B):
      _cardinal_le (A -> Prop) (B -> Prop).
    Proof.
      inv LE.
      eapply _cardinal_le_intro with (f := fun s y => exists x, f x = y /\ s x).
      i. extensionality x. pose proof (equal_f EQ (f x)) as EQ0.
      apply propositional_extensionality.
      transitivity (exists x0, f x0 = f x /\ a0 x0).
      { split; i; eauto.
        des. apply INJ in H. subst. auto. }
      { rewrite EQ0. split; i; eauto.
        des. apply INJ in H. subst. auto. }
    Qed.

    Section cardinal.
      Variable A: Type.

      Definition of_cardinal (c: ord.t): Prop :=
        classicOrd.is_meet (fun o =>
                              exists (R: A -> A -> Prop) (WF: well_founded R),
                                (forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0) /\
                                ord.eq (ord.from_wf_set WF) o) c.

      Lemma of_cardinal_exists: exists c, of_cardinal c.
      Proof.
        eapply classicOrd.meet_exists.
        hexploit (@well_ordering_theorem A); eauto. i. des.
        exists (ord.from_wf_set H), R, H. splits; auto. reflexivity.
      Qed.

      Lemma of_cardinal_unique c0 c1 (CARD0: of_cardinal c0) (CARD1: of_cardinal c1):
        ord.eq c0 c1.
      Proof.
        unfold of_cardinal, classicOrd.is_meet in *. des. split.
        - eapply CARD4; eauto.
        - eapply CARD2; eauto.
      Qed.

      Lemma eq_of_cardinal c0 c1 (EQ: ord.eq c0 c1) (CARD0: of_cardinal c0):
        of_cardinal c1.
      Proof.
        unfold of_cardinal, classicOrd.is_meet in *. des. split.
        - exists R, WF. splits; auto. transitivity c0; auto.
        - i. transitivity c0; auto. eapply EQ.
      Qed.

      Let X: Type :=
        @sig
          (@sigT (A -> Prop) (fun s => sig s -> sig s-> Prop))
          (fun PR =>
             well_founded (projT2 PR) /\
             (forall a0 a1, projT2 PR a0 a1 \/ a0 = a1 \/ projT2 PR a1 a0) /\
             (forall (f: A -> sig (projT1 PR)),
                 exists a0 a1, f a0 = f a1 /\ a0 <> a1)).

      Let Y (x: X): ord.t :=
        @ord.from_wf_set (sig (projT1 (proj1_sig x))) _ (proj1 (proj2_sig x)).

      Definition cardinal := @ord.build X Y.

      Lemma cardinal_lowerbound (R: A -> A -> Prop) (WF: well_founded R)
            (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0):
        ord.le cardinal (ord.from_wf_set WF).
      Proof.
        eapply ord.build_supremum. i. unfold Y.
        destruct a as [[P0 R0] [WF0 [TOTAL0 SMALL]]]; ss.
        eapply (@ord.le_lt_lt (ord.from_wf_set WF0)).
        { eapply ord.same_wf_set_le. }
        destruct (classicOrd.total (ord.from_wf_set WF) (ord.from_wf_set WF0)); auto.
        exfalso. hexploit from_wf_set_embed; eauto. intros MON. des.
        hexploit (SMALL f); eauto. i. des.
        destruct (TOTAL a0 a1) as [|[]]; ss.
        { eapply MON in H2. rewrite H0 in *.
          eapply well_founded_irreflexive in H2; eauto. }
        { eapply MON in H2. rewrite H0 in *.
          eapply well_founded_irreflexive in H2; eauto. }
      Qed.

      Lemma _cardinal_upperbound B (CARD: _cardinal_lt B A)
            (R: B -> B -> Prop) (WF: well_founded R)
        :
          ord.lt (ord.from_wf_set WF) cardinal.
      Proof.
        inv CARD.
        assert (CLT: ~ _cardinal_le A B).
        { ii. eapply H0. eauto. } inv H.
        hexploit (from_wf_set_projected_rel_sig_eq WF _ INJ). i.
        hexploit (well_founded_order_extendable (projected_rel_sig_well_founded WF f INJ)). i. des.
        hexploit (from_wf_set_le H2 (projected_rel_sig_well_founded WF f INJ) H1). i.
        eapply ord.le_lt_lt.
        { etransitivity.
          { eapply H. }
          { eapply H4. }
        }
        assert ((fun (PR:(@sigT (A -> Prop) (fun s => sig s -> sig s-> Prop))) =>
                   well_founded (projT2 PR) /\
                   (forall a0 a1, projT2 PR a0 a1 \/ a0 = a1 \/ projT2 PR a1 a0) /\
                   (forall (f: A -> sig (projT1 PR)),
                       exists a0 a1, f a0 = f a1 /\ a0 <> a1)) (existT _ _ R1)).
        { ss. splits; auto. i. eapply NNPP. ii. eapply CLT.
          hexploit (choice (fun (a: A) (b: B) => proj1_sig (f0 a) = f b)).
          { i.  hexploit (proj2_sig (f0 x)). i. des. eauto. }
          i. des. eapply _cardinal_le_intro with (f:=f1). i.
          eapply NNPP. ii. eapply f_equal with (f:=f) in EQ.
          rewrite <- H6 in EQ. rewrite <- H6 in EQ.
          eapply H5; eauto. exists a0, a1. splits; auto.
          destruct (f0 a0), (f0 a1); auto. ss. subst. f_equal. eapply proof_irrelevance.
        }
        hexploit (@ord.build_upperbound
                    X Y
                    (@exist
                       (@sigT (A -> Prop) (fun s => sig s -> sig s-> Prop))
                       (fun PR =>
                          well_founded (projT2 PR) /\
                          (forall a0 a1, projT2 PR a0 a1 \/ a0 = a1 \/ projT2 PR a1 a0) /\
                          (forall (f: A -> sig (projT1 PR)),
                              exists a0 a1, f a0 = f a1 /\ a0 <> a1))
                       (@existT (A -> Prop) (fun s => sig s -> sig s-> Prop) _ R1)
                       H5)).
        ss. unfold Y. ss. i.
        eapply ord.le_lt_lt; [|eapply H6].
        eapply ord.same_wf_set_le.
      Qed.

      Lemma _cardinal_supremum c
            (UPPER: forall (B: Type) (CARD: _cardinal_lt B A)
                           (R: B -> B -> Prop) (WF: well_founded R),
                ord.lt (ord.from_wf_set WF) c)
        :
          ord.le cardinal c.
      Proof.
        eapply ord.build_supremum. i.
        destruct a as [[P0 R0] [WF0 [TOTAL SMALL]]]; ss. unfold Y. ss.
        eapply (@ord.le_lt_lt (ord.from_wf_set WF0)).
        { eapply ord.same_wf_set_le. }
        eapply UPPER.
        assert (NLE: ~ _cardinal_le A (sig P0)).
        { ii. inv H. hexploit (SMALL f); eauto. i. des.
          eapply INJ in H. ss. }
        destruct (_cardinal_total_le A (sig P0)); ss.
      Qed.

      Lemma cardinal_of_cardinal: of_cardinal cardinal.
      Proof.
        split.
        - hexploit of_cardinal_exists. i. des.
          unfold of_cardinal, classicOrd.is_meet in H. des.
          exists R, WF. splits; auto. split.
          2: { eapply cardinal_lowerbound; auto. }
          hexploit (toSet.to_total_exists cardinal); eauto. i. des.
          hexploit (_cardinal_total_le A A0). i.
          destruct (classic (_cardinal_le A A0)).
          { transitivity (ord.from_wf_set WF0).
            2: { eapply H2. }
            transitivity c.
            { eapply H1. }
            inv H5.
            hexploit (projected_rel_rev_well_founded WF0 f); auto. i.
            hexploit (H0 (ord.from_wf_set H5)).
            { eexists _, H5. splits; auto.
              - i. destruct (H3 (f a0) (f a1)) as [|[]]; auto.
              - reflexivity. }
            i. transitivity (ord.from_wf_set H5); auto.
            eapply from_wf_set_inj; eauto.
          }
          { assert (CLT: _cardinal_lt A0 A).
            { des; ss. }
            hexploit (_cardinal_upperbound CLT WF0). i.
            exfalso. eapply ord.lt_not_le.
            { eapply H6. }
            { eapply H2. }
          }
        - i. des. eapply ord.build_supremum. i. unfold Y.
          destruct a as [[P0 R0] [WF0 [TOTAL SMALL]]]; ss.
        eapply (@ord.le_lt_lt (ord.from_wf_set WF0)).
        { eapply ord.same_wf_set_le. }
          eapply ord.lt_eq_lt.
          { symmetry. eapply IN0. }
          destruct (classicOrd.total (ord.from_wf_set WF) (ord.from_wf_set WF0)); auto.
          exfalso. hexploit from_wf_set_embed; eauto. intros MON. des.
          hexploit (SMALL f); eauto. i. des.
          destruct (IN a0 a1) as [|[]]; ss.
          { eapply MON in H2. rewrite H0 in *.
            eapply well_founded_irreflexive in H2; eauto. }
          { eapply MON in H2. rewrite H0 in *.
            eapply well_founded_irreflexive in H2; eauto. }
      Qed.
    End cardinal.

    Lemma _cardinal_le_iff A B:
      _cardinal_le A B <-> ord.le (cardinal A) (cardinal B).
    Proof.
      split. i.
      - hexploit (cardinal_of_cardinal B). i. destruct H0. des.
        transitivity (ord.from_wf_set WF); auto.
        2: { eapply H2. }
        inv H. transitivity (ord.from_wf_set (projected_rel_rev_well_founded WF f INJ)).
        { eapply cardinal_of_cardinal.
          exists (projected_rel_rev R f), (projected_rel_rev_well_founded WF f INJ). splits; auto.
          - i. destruct (H0 (f a0) (f a1)) as [|[]]; auto.
          - reflexivity.
        }
        { eapply from_wf_set_inj. instantiate (1:=f). i. apply LT. }
      - hexploit (cardinal_of_cardinal B). i. destruct H. des.
        i. eapply NNPP. ii. destruct (_cardinal_total_le A B); ss.
        hexploit (_cardinal_upperbound).
        { split; eauto. }
        instantiate (1:=WF). i. eapply ord.lt_not_le; eauto.
        transitivity (cardinal B); auto. apply H2.
    Qed.

    Lemma _cardinal_eq_iff A B:
      _cardinal_eq A B <-> ord.eq (cardinal A) (cardinal B).
    Proof.
      split. i.
      - split.
        + apply _cardinal_le_iff; auto. apply H.
        + apply _cardinal_le_iff; auto. apply H.
      - split.
        + apply _cardinal_le_iff; auto. apply H.
        + apply _cardinal_le_iff; auto. apply H.
    Qed.

    Lemma _cardinal_lt_iff A B:
      _cardinal_lt A B <-> ord.lt (cardinal A) (cardinal B).
    Proof.
      split; i.
      - inv H. apply _cardinal_le_iff in H0.
        eapply classicOrd.le_eq_or_lt in H0. des; auto.
        exfalso. eapply H1. eapply _cardinal_eq_iff; eauto.
      - split.
        + apply _cardinal_le_iff. eapply ord.lt_le; eauto.
        + ii. apply _cardinal_le_iff in H0.
          eapply ord.lt_not_le; eauto.
    Qed.

    Lemma cardinal_size_le A B (R: B -> B -> Prop) (WF: well_founded R)
          (TOTAL: forall b0 b1, R b0 b1 \/ b0 = b1 \/ R b1 b0)
          (LE: ord.le (cardinal A) (ord.from_wf_set WF)):
      ord.le (cardinal A) (cardinal B).
    Proof.
      hexploit (cardinal_of_cardinal A); auto. i. inv H. des.
      hexploit (@from_wf_set_embed _ _ _ _ WF0 WF); auto.
      { transitivity (cardinal A); auto. apply H2. }
      i. des. apply _cardinal_le_iff.
      eapply _cardinal_le_intro with (f:=f). i.
      destruct (H0 a0 a1) as [|[]]; auto.
      - eapply H in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive WF); eauto.
      - eapply H in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive WF); eauto.
    Qed.

    Lemma cardinal_size_eq A B (R: B -> B -> Prop) (WF: well_founded R)
          (TOTAL: forall b0 b1, R b0 b1 \/ b0 = b1 \/ R b1 b0)
          (EQ: ord.eq (cardinal A) (ord.from_wf_set WF)):
      ord.eq (cardinal A) (cardinal B).
    Proof.
      split; i.
      - eapply cardinal_size_le; eauto. eapply EQ.
      - transitivity (ord.from_wf_set WF).
        + eapply (cardinal_of_cardinal B). esplits; eauto. reflexivity.
        + eapply EQ.
    Qed.

    Lemma le_cardinal_le A B (RA: A -> A -> Prop) (RB: B -> B -> Prop) (WFA: well_founded RA) (WFB: well_founded RB)
          (TOTAL: forall a0 a1, RA a0 a1 \/ a0 = a1 \/ RA a1 a0)
          (LE: ord.le (ord.from_wf_set WFA) (ord.from_wf_set WFB))
      :
        ord.le (cardinal A) (cardinal B).
    Proof.
      hexploit (well_founded_order_extendable WFB); eauto. i. des.
      hexploit (@from_wf_set_embed _ _ _ _ WFA H); eauto.
      { transitivity (ord.from_wf_set WFB); auto.
        eapply from_wf_set_le; eauto. }
      i. des. apply _cardinal_le_iff.
      eapply _cardinal_le_intro with (f:=f). i.
      destruct (TOTAL a0 a1) as [|[]]; auto.
      { eapply H2 in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H); eauto. }
      { eapply H2 in H3. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H); eauto. }
    Qed.

    Lemma to_total_le o0 o1 (LE: ord.le o0 o1):
      ord.le (cardinal (toSet.to_total_set o0)) (cardinal (toSet.to_total_set o1)).
    Proof.
      eapply le_cardinal_le.
      { eapply toSet.to_total_total. }
      instantiate (1:=toSet.to_total_well_founded o1).
      instantiate (1:=toSet.to_total_well_founded o0).
      transitivity o0.
      { eapply toSet.to_total_eq. }
      transitivity o1; auto.
      { eapply toSet.to_total_eq. }
    Qed.

    Lemma to_total_cardinal_le o:
      ord.le (cardinal (toSet.to_total_set o)) o.
    Proof.
      transitivity (ord.from_wf_set (toSet.to_total_well_founded o)).
      { eapply cardinal_of_cardinal.
        exists (toSet.to_total_rel o), (toSet.to_total_well_founded o). split; auto.
        - eapply toSet.to_total_total.
        - reflexivity.
      }
      { eapply toSet.to_total_eq. }
    Qed.

    Lemma cardinal_to_total_bij1 A:
      ord.eq (cardinal A) (cardinal (toSet.to_total_set (cardinal A))).
    Proof.
      eapply cardinal_size_eq.
      { eapply toSet.to_total_total. }
      eapply toSet.to_total_eq.
    Qed.

    Lemma cardinal_to_total_bij2 A c (CARDINAL: of_cardinal A c):
      ord.eq c (cardinal (toSet.to_total_set c)).
    Proof.
      hexploit of_cardinal_unique.
      { eapply CARDINAL. }
      { eapply cardinal_of_cardinal. }
      i. transitivity (cardinal A); auto.
      transitivity (cardinal (toSet.to_total_set (cardinal A))).
      { eapply cardinal_to_total_bij1. }
      split.
      { eapply to_total_le. apply H. }
      { eapply to_total_le. apply H. }
    Qed.

    Lemma from_wf_set_to_total A (R: A -> A -> Prop) (WF: well_founded R):
      ord.le (cardinal (toSet.to_total_set (ord.from_wf_set WF))) (cardinal A).
    Proof.
      hexploit (well_founded_order_extendable WF); eauto. i. des.
      assert (ord.le (ord.from_wf_set (toSet.to_total_well_founded (ord.from_wf_set WF))) (ord.from_wf_set H)).
      { transitivity (ord.from_wf_set WF).
        { eapply toSet.to_total_eq. }
        { eapply from_wf_set_le; auto. }
      }
      dup H2. eapply from_wf_set_embed in H2; auto. des.
      hexploit (@from_wf_set_embed _ _ _ _ (toSet.to_total_well_founded (ord.from_wf_set WF)) H); auto.
      i. des. apply _cardinal_le_iff.
      eapply _cardinal_le_intro with (f:=f0).
      i. destruct (toSet.to_total_total a0 a1) as [|[]]; auto.
      { eapply H4 in H5. rewrite EQ in *. exfalso.
        eapply (well_founded_irreflexive H); eauto. }
      { eapply H4 in H5. rewrite EQ in *. exfalso.
        eapply (well_founded_irreflexive H); eauto. }
    Qed.

    Lemma total_from_wf_inj A (R: A -> A -> Prop) (WF: well_founded R)
          (TOTAL: forall a0 a1, R a0 a1 \/ a0 = a1 \/ R a1 a0)
      :
        forall a0 a1,
          a0 = a1 <-> ord.eq (ord.from_wf WF a0) (ord.from_wf WF a1).
    Proof.
      i. split.
      { i. subst. reflexivity. }
      { i. destruct (TOTAL a0 a1) as [|[]]; auto.
        { eapply (ord.lt_from_wf WF) in H0. exfalso.
          eapply ord.lt_not_le; eauto. eapply H. }
        { eapply (ord.lt_from_wf WF) in H0. exfalso.
          eapply ord.lt_not_le; eauto. eapply H. }
      }
    Qed.

    Lemma same_cardinality_bijection A B
          (cardinal: ord.eq (cardinal A) (cardinal B))
      :
        exists (f: A -> B),
          (forall a0 a1 (EQ: f a0 = f a1), a0 = a1) /\
          (forall b, exists a, f a = b).
    Proof.
      hexploit (cardinal_of_cardinal A). i. inv H. des.
      hexploit (cardinal_of_cardinal B). i. inv H. des.
      hexploit (choice (fun a b => ord.eq (ord.from_wf WF a) (ord.from_wf WF0 b))).
      { i. hexploit (@classicOrd.from_wf_set_complete _ _ WF0 (ord.from_wf WF x)).
        { eapply ord.lt_eq_lt.
          { eapply H5. }
          eapply ord.lt_eq_lt.
          { symmetry. eapply cardinal. }
          eapply ord.lt_eq_lt.
          { symmetry. eapply H2. }
          eapply ord.from_wf_set_upperbound.
        }
        i. des. eauto.
      }
      i. des. exists f. splits; auto.
      { i. eapply (total_from_wf_inj WF); eauto.
        etransitivity.
        { eapply H. }
        etransitivity.
        2: { symmetry. eapply H. }
        rewrite EQ. reflexivity.
      }
      { i. hexploit (@classicOrd.from_wf_set_complete _ _ WF (ord.from_wf WF0 b)).
        { eapply ord.lt_eq_lt.
          { eapply H2. }
          eapply ord.lt_eq_lt.
          { eapply cardinal. }
          eapply ord.lt_eq_lt.
          { symmetry. eapply H5. }
          eapply ord.from_wf_set_upperbound.
        }
        i. des. exists a. eapply (total_from_wf_inj WF0); auto.
        etransitivity.
        { symmetry. eapply H. }
        { symmetry. eapply H6. }
      }
    Qed.

    Lemma sum_of_smaller o:
      exists (os: toSet.to_total_set o -> ord.t),
        ord.eq o (ord.build os).
    Proof.
      hexploit (toSet.to_total_eq o). i.
      exists (fun x => ord.from_wf (toSet.to_total_well_founded o) x).
      eapply H.
    Qed.

    Lemma sum_of_smaller_same_cardinal o A (EQ: ord.eq (cardinal A) (cardinal (toSet.to_total_set o))):
      exists (os: A -> ord.t),
        ord.eq o (ord.build os).
    Proof.
      hexploit (sum_of_smaller o). i. des.
      eapply same_cardinality_bijection in EQ. des.
      exists (fun a => os (f a)). etransitivity.
      { eapply H. }
      split.
      { eapply ord.build_supremum. i. hexploit (EQ0 a). i. des.
        subst. eapply (ord.build_upperbound (fun a => os (f a)) a0). }
      { eapply ord.build_supremum. i.
        eapply (ord.build_upperbound os (f a)). }
    Qed.
  End cardinalITY.

  Section NEXT.
    Variable A: Type.
    Let X: Type := @sig (A -> A -> Prop) (@well_founded _).

    Let Y (x: X): ord.t := ord.from_wf_set (proj2_sig x).

    Definition next_cardinal := ord.hartogs.

    Lemma next_cardinal_upperbound B (R: B -> B -> Prop) (WF: well_founded R)
          (CARD: ord.le (cardinal B) (cardinal A))
      : ord.lt (ord.from_wf_set WF) (next_cardinal A).
    Proof.
      eapply _cardinal_le_iff in CARD. inv CARD.
      eapply (@ord.le_lt_lt (ord.from_wf_set (embed_projected_rel_well_founded WF f INJ))).
      { eapply from_wf_set_inj. instantiate (1:=f). i. econs; eauto. }
      eapply (@ord.build_upperbound X Y (exist _ _ (embed_projected_rel_well_founded WF f INJ))).
    Qed.

    Lemma next_cardinal_incr
      : ord.lt (cardinal A) (next_cardinal A).
    Proof.
      hexploit (cardinal_of_cardinal A). i. inv H. des.
      eapply ord.eq_lt_lt.
      { symmetry. eapply H2. }
      eapply next_cardinal_upperbound.
      reflexivity.
    Qed.

    Lemma next_cardinal_supremum B (CARD: ord.lt (cardinal A) (cardinal B)):
      ord.le (next_cardinal A) (cardinal B).
    Proof.
      Local Transparent ord.hartogs.
      eapply ord.build_supremum. i. destruct a as [R WF]. unfold Y. ss.
      destruct (classicOrd.total (cardinal B) (ord.from_wf_set WF)); auto.
      hexploit (cardinal_of_cardinal B); eauto. i. inv H0. des.
      hexploit (well_founded_order_extendable WF); eauto. i. des.
      hexploit (@from_wf_set_embed _ _ _ _ WF0 H3); auto.
      { transitivity (cardinal B); auto.
        { eapply H0. }
        transitivity (ord.from_wf_set WF); auto.
        eapply from_wf_set_le; auto.
      }
      i. des. exfalso.
      eapply _cardinal_lt_iff in CARD. des.
      eapply CARD0.
      eapply _cardinal_le_intro with (f:=f). i.
      destruct (H1 a0 a1) as [|[]]; auto.
      - eapply H6 in H7. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H3); eauto.
      - eapply H6 in H7. rewrite EQ in *.
        exfalso. eapply (well_founded_irreflexive H3); eauto.
    Qed.

    Lemma next_cardinal_of_cardinal:
      of_cardinal (toSet.to_total_set (next_cardinal A)) (next_cardinal A).
    Proof.
      split.
      { exists (toSet.to_total_rel (next_cardinal A)), (toSet.to_total_well_founded (next_cardinal A)).
        splits; auto.
        - eapply toSet.to_total_total.
        - symmetry. apply toSet.to_total_eq.
      }
      i. des. eapply ord.build_supremum. i. destruct a as [R0 WF0]. unfold Y. ss.
      destruct (classicOrd.total o1 (ord.from_wf_set WF0)); auto.
      assert (LE: ord.le (ord.from_wf_set WF) (ord.from_wf_set WF0)).
      { transitivity o1; auto. eapply IN0. }
      eapply le_cardinal_le in LE; auto. exfalso.
      eapply (next_cardinal_upperbound (toSet.to_total_well_founded (next_cardinal A))) in LE.
      eapply ord.lt_not_le.
      { eapply LE. }
      { eapply toSet.to_total_eq. }
    Qed.

    Lemma next_cardinal_le_power_set:
      ord.le (next_cardinal A) (cardinal (A -> Prop)).
    Proof.
      eapply next_cardinal_supremum.
      apply _cardinal_lt_iff.
      assert (LE: _cardinal_le A (A -> Prop)).
      { eapply _cardinal_le_intro with (fun a0 a1 => a0 = a1).
        i. eapply equal_f with (x:=a1) in EQ.
        rewrite EQ. auto.
      }
      { split; auto. ii. inv H.
        hexploit (choice (fun (a: A) (P1: A -> Prop) =>
                            forall P0, f P0 = a -> P0 = P1)).
        { i. destruct (classic (exists P0, f P0 = x)).
          { des. exists P0. i. rewrite <- H0 in *. eauto. }
          { exists (fun _ => True). i. exfalso. eapply H; eauto. }
        }
        i. des. hexploit (cantor_theorem f0). i. des.
        eapply (H0 (f P)). exploit H; eauto.
      }
    Qed.
  End NEXT.

  Lemma next_cardinal_le A B
        (CARDINAL: ord.le (cardinal A) (cardinal B)):
    ord.le (next_cardinal A) (next_cardinal B).
  Proof.
    assert (EQ: ord.eq (next_cardinal B) (cardinal (toSet.to_total_set (next_cardinal B)))).
    { eapply of_cardinal_unique.
      { eapply next_cardinal_of_cardinal. }
      { eapply cardinal_of_cardinal. }
    }
    transitivity (cardinal (toSet.to_total_set (next_cardinal B))).
    2: { apply EQ. }
    eapply next_cardinal_supremum.
    eapply ord.lt_le_lt.
    2: { eapply EQ. }
    eapply ord.le_lt_lt.
    { eapply CARDINAL. }
    { eapply next_cardinal_incr. }
  Qed.

  Lemma next_cardinal_eq A B
        (cardinal: ord.eq (cardinal A) (cardinal B)):
    ord.eq (next_cardinal A) (next_cardinal B).
  Proof.
    split.
    - eapply next_cardinal_le. eapply cardinal.
    - eapply next_cardinal_le. eapply cardinal.
  Qed.

  Lemma next_cardinal_lt A B
        (cardinal: ord.lt (cardinal A) (cardinal B)):
    ord.lt (next_cardinal A) (next_cardinal B).
  Proof.
    eapply next_cardinal_supremum in cardinal.
    eapply ord.le_lt_lt.
    { eapply cardinal. }
    { eapply next_cardinal_incr. }
  Qed.

  Lemma next_cardinal_le_iff A B:
    ord.le (cardinal A) (cardinal B) <-> ord.le (next_cardinal A) (next_cardinal B).
  Proof.
    split; i.
    { eapply next_cardinal_le; auto. }
    { destruct (classicOrd.total (cardinal A) (cardinal B)); auto.
      eapply next_cardinal_lt in H0. exfalso. eapply ord.lt_not_le; eauto. }
  Qed.

  Lemma next_cardinal_eq_iff A B:
    ord.eq (cardinal A) (cardinal B) <-> ord.eq (next_cardinal A) (next_cardinal B).
  Proof.
    split; i.
    { split.
      { eapply next_cardinal_le_iff. eapply H. }
      { eapply next_cardinal_le_iff. eapply H. }
    }
    { split.
      { eapply next_cardinal_le_iff. eapply H. }
      { eapply next_cardinal_le_iff. eapply H. }
    }
  Qed.

  Lemma next_cardinal_lt_iff A B:
    ord.lt (cardinal A) (cardinal B) <-> ord.lt (next_cardinal A) (next_cardinal B).
  Proof.
    destruct (classicOrd.total (cardinal B) (cardinal A)).
    { split.
      { i. exfalso. eapply ord.lt_not_le; eauto. }
      { i. eapply next_cardinal_le_iff in H.
        exfalso. eapply ord.lt_not_le; eauto. }
    }
    { split; i; auto. eapply next_cardinal_lt; auto. }
  Qed.

  Definition is_cardinal (c: ord.t): Prop :=
    of_cardinal (toSet.to_total_set c) c.

  Lemma same_cardinal_of_cardinal A B (EQ: ord.eq (cardinal A) (cardinal B))
        c (CARDINAL: of_cardinal A c):
    of_cardinal B c.
  Proof.
    eapply of_cardinal_unique in CARDINAL.
    2: { eapply cardinal_of_cardinal. }
    eapply eq_of_cardinal.
    2: { eapply cardinal_of_cardinal. }
    transitivity (cardinal A); auto. symmetry. auto.
  Qed.

  Lemma cardinal_join_upperbound X (TS: X -> Type):
    of_cardinal (toSet.to_total_set (ord.join (fun x => cardinal (TS x)))) (ord.join (fun x => cardinal (TS x))).
  Proof.
    split.
    { exists (toSet.to_total_rel (ord.join (fun x : X => cardinal (TS x)))), (toSet.to_total_well_founded _). splits.
      - eapply toSet.to_total_total.
      - symmetry. eapply toSet.to_total_eq. }
    { i. des. eapply ord.join_supremum. i. etransitivity.
      2: { eapply IN0. }
      etransitivity.
      2: { eapply cardinal_lowerbound; auto. }
      transitivity (cardinal (toSet.to_total_set (cardinal (TS a)))).
      { eapply cardinal_to_total_bij1. }
      { eapply to_total_le. eapply (ord.join_upperbound (fun x : X => cardinal (TS x))). }
    }
  Qed.

  Lemma of_cardinal_join_upperbound A (os: A -> ord.t)
        (CARD: forall a, of_cardinal (toSet.to_total_set (os a)) (os a)):
    of_cardinal (toSet.to_total_set (ord.join os)) (ord.join os).
  Proof.
    assert (ord.eq (ord.join (fun x : A => cardinal (toSet.to_total_set (os x)))) (ord.join os)).
    { split.
      { eapply ord.join_supremum. i. transitivity (os a).
        { eapply cardinal_to_total_bij2; eauto. }
        { eapply ord.join_upperbound. }
      }
      { eapply ord.join_supremum. i. transitivity (cardinal (toSet.to_total_set (os a))).
        { eapply cardinal_to_total_bij2; eauto. }
        { eapply (ord.join_upperbound (fun x : A => cardinal (toSet.to_total_set (os x)))). }
      }
    }
    hexploit (cardinal_join_upperbound (fun a => toSet.to_total_set (os a))). i.
    eapply same_cardinal_of_cardinal in H0.
    { eapply eq_of_cardinal.
      2: { eapply H0. }
      { auto. }
    }
    { split.
      - eapply to_total_le; apply H.
      - eapply to_total_le; apply H.
    }
  Qed.

  Lemma of_cardinal_size A c (cardinal: of_cardinal A c):
    of_cardinal (toSet.to_total_set c) c.
  Proof.
    eapply same_cardinal_of_cardinal; eauto.
    etransitivity.
    { eapply cardinal_to_total_bij1. }
    eapply of_cardinal_unique in cardinal.
    2: { eapply cardinal_of_cardinal. }
    split.
    { eapply to_total_le. eapply cardinal. }
    { eapply to_total_le. eapply cardinal. }
  Qed.

  Lemma of_cardinal_is_cardinal A c (cardinal: of_cardinal A c):
    is_cardinal c.
  Proof.
    eapply of_cardinal_size; eauto.
  Qed.

  Lemma eq_is_cardinal c0 c1 (EQ: ord.eq c0 c1) (CARD0: is_cardinal c0):
    is_cardinal c1.
  Proof.
    eapply of_cardinal_is_cardinal. eapply eq_of_cardinal; eauto.
  Qed.


  Section ALEPH.

    Lemma le_aleph_gen o0 o1 (LE: ord.le o0 o1):
      ord.le (next_cardinal (toSet.to_total_set o0)) (next_cardinal (toSet.to_total_set o1)).
    Proof.
      i. eapply next_cardinal_le. eapply to_total_le. apply LE.
    Qed.

    Lemma eq_aleph_gen o0 o1 (EQ: ord.eq o0 o1):
      ord.eq (next_cardinal (toSet.to_total_set o0)) (next_cardinal (toSet.to_total_set o1)).
    Proof.
      split.
      - eapply le_aleph_gen. apply EQ.
      - eapply le_aleph_gen. apply EQ.
    Qed.

    Lemma aleph_gen_lt o:
      ord.lt o (next_cardinal (toSet.to_total_set o)).
    Proof.
      eapply ord.eq_lt_lt.
      { eapply toSet.to_total_eq. }
      eapply next_cardinal_upperbound.
      reflexivity.
    Qed.

    Lemma aleph_gen_le o:
      ord.le o (next_cardinal (toSet.to_total_set o)).
    Proof.
      eapply ord.lt_le. eapply aleph_gen_lt.
    Qed.

    Definition aleph_gen (o: ord.t) := next_cardinal (toSet.to_total_set o).
    Definition aleph := ord.orec ord.omega aleph_gen.

    Lemma le_aleph o0 o1 (LE: ord.le o0 o1):
      ord.le (aleph o0) (aleph o1).
    Proof.
      eapply ord.le_orec; auto.
      eapply le_aleph_gen.
    Qed.

    Lemma lt_aleph o0 o1 (LE: ord.lt o0 o1):
      ord.lt (aleph o0) (aleph o1).
    Proof.
      eapply ord.S_supremum in LE.
      eapply ord.lt_le_lt.
      2: { eapply le_aleph; eauto. }
      eapply ord.lt_eq_lt.
      { eapply ord.orec_S.
        { eapply aleph_gen_le. }
        { eapply le_aleph_gen. }
      }
      eapply aleph_gen_lt.
    Qed.

    Lemma aleph_le_omega o:
      ord.le ord.omega (aleph o).
    Proof.
      eapply ord.orec_le_base.
      eapply le_aleph_gen.
    Qed.

    Lemma aleph_expand:
      forall o, ord.le o (aleph o).
    Proof.
      i. transitivity (ord.orec ord.O ord.S o).
      { eapply ord.orec_of_S. }
      eapply (@ord.rec_mon _ ord.le ord.join ord.O ord.S ord.omega aleph_gen).
      { eapply ord.O_bot. }
      { i. eapply ord.S_supremum. eapply ord.le_lt_lt; eauto.
        eapply aleph_gen_lt.
      }
      { eapply ord.le_PreOrder. }
      { i. eapply ord.join_upperbound. }
      { i. eapply ord.join_supremum. auto. }
    Qed.

    (* Lemma aleph_is_cardinal: *)
    (*   forall o, is_cardinal (aleph o). *)
    (* Proof. *)
    (*   eapply (rec_wf ord.le join (fun o => of_cardinal (toSet.to_total_set o) o) aleph_gen omega); eauto. *)
    (*   { i. reflexivity. } *)
    (*   { i. transitivity d1; auto. } *)
    (*   { i. eapply join_upperbound. } *)
    (*   { i. eapply join_supremum. auto. } *)
    (*   { i. eapply of_cardinal_join_upperbound. auto. } *)
    (*   { admit. } *)
    (*   { i. eapply next_cardinal_of_cardinal. } *)
    (*   { i. eapply aleph_gen_le. } *)
    (*   { i. eapply aleph_gen_eq; auto. } *)
    (* Admitted. *)
  End ALEPH.


  Section BETH.
    Definition beth_gen (o: ord.t) := cardinal (toSet.to_total_set o -> Prop).
    Definition beth := ord.orec ord.omega beth_gen.

    Lemma le_beth_gen o0 o1 (LE: ord.le o0 o1):
      ord.le (beth_gen o0) (beth_gen o1).
    Proof.
      eapply to_total_le in LE.
      apply _cardinal_le_iff in LE. apply _cardinal_le_iff.
      eapply _cardinal_le_power. auto.
    Qed.

    Lemma eq_beth_gen o0 o1 (EQ: ord.eq o0 o1):
      ord.eq (beth_gen o0) (beth_gen o1).
    Proof.
      split.
      - eapply le_beth_gen. apply EQ.
      - eapply le_beth_gen. apply EQ.
    Qed.

    Lemma beth_gen_lt o:
      ord.lt o (beth_gen o).
    Proof.
      eapply ord.eq_lt_lt.
      { eapply toSet.to_total_eq. }
      eapply ord.lt_le_lt.
      2: { eapply next_cardinal_le_power_set. }
      eapply next_cardinal_upperbound. reflexivity.
    Qed.

    Lemma beth_gen_le o:
      ord.le o (beth_gen o).
    Proof.
      eapply ord.lt_le. eapply beth_gen_lt.
    Qed.

    Lemma aleph_gen_le_beth_gen o:
      ord.le (aleph_gen o) (beth_gen o).
    Proof.
      eapply next_cardinal_le_power_set.
    Qed.

    Lemma le_beth o0 o1 (LE: ord.le o0 o1):
      ord.le (beth o0) (beth o1).
    Proof.
      eapply ord.le_orec; auto.
      eapply le_beth_gen.
    Qed.

    Lemma lt_beth o0 o1 (LE: ord.lt o0 o1):
      ord.lt (beth o0) (beth o1).
    Proof.
      eapply ord.S_supremum in LE.
      eapply ord.lt_le_lt.
      2: { eapply le_beth; eauto. }
      eapply ord.lt_eq_lt.
      { eapply ord.orec_S.
        { eapply beth_gen_le. }
        { eapply le_beth_gen. }
      }
      eapply beth_gen_lt.
    Qed.

    Lemma beth_le_omega o:
      ord.le ord.omega (beth o).
    Proof.
      eapply ord.orec_le_base.
      eapply le_beth_gen.
    Qed.

    Lemma beth_expand:
      forall o, ord.le o (beth o).
    Proof.
      i. transitivity (ord.orec ord.O ord.S o).
      { eapply ord.orec_of_S. }
      eapply (@ord.rec_mon _ ord.le ord.join ord.O ord.S ord.omega beth_gen).
      { eapply ord.O_bot. }
      { i. eapply ord.S_supremum. eapply ord.le_lt_lt; eauto.
        eapply beth_gen_lt.
      }
      { eapply ord.le_PreOrder. }
      { i. eapply ord.join_upperbound. }
      { i. eapply ord.join_supremum. auto. }
    Qed.

    Lemma aleph_le_beth o:
      ord.le (aleph o) (beth o).
    Proof.
      eapply ord.orec_mon.
      { reflexivity. }
      { i. transitivity (aleph_gen o1).
        { eapply le_aleph_gen. auto. }
        { eapply aleph_gen_le_beth_gen. }
      }
    Qed.
  End BETH.


  Section FINITE.
    Fixpoint finite (n: nat): Type :=
      match n with
      | 0 => False
      | Datatypes.S n' => option (finite n')
      end.

    Fixpoint finite_lt (n: nat): finite n -> finite n -> Prop :=
      match n with
      | 0 => fun _ _ => False
      | Datatypes.S n' =>
        fun x y => match x, y with
                   | Some x', Some y' => finite_lt n' x' y'
                   | Some x', None => True
                   | _, _ => False
                   end
      end.

    Lemma finite_total: forall n x0 x1, finite_lt n x0 x1 \/ x0 = x1 \/ finite_lt n x1 x0.
    Proof.
      induction n.
      { i. ss. }
      { i. ss. destruct x0, x1; ss; eauto.
        destruct (IHn f f0) as [|[]]; eauto. subst. auto.
      }
    Qed.

    Lemma finite_lt_acc: forall n x (ACC: Acc (finite_lt n) x), Acc (finite_lt (Datatypes.S n)) (Some x).
    Proof.
      intros n x ACC. induction ACC. econs. i. destruct y; ss.
      eapply H0. auto.
    Qed.

    Lemma finite_well_founded: forall n, well_founded (finite_lt n).
    Proof.
      induction n.
      - ii. econs. i. ss.
      - ii. econs. i. destruct a, y; ss.
        + eapply finite_lt_acc. eapply IHn.
        + eapply finite_lt_acc. eapply IHn.
    Qed.

    Lemma finite_from_acc_eq:
      forall n (x: finite n)
             (ACC0: Acc (finite_lt n) x) (ACC1: Acc (finite_lt (Datatypes.S n)) (Some x)),
        ord.eq (ord.from_acc ACC0) (ord.from_acc ACC1).
    Proof.
      Local Transparent ord.from_acc.
      intros n x ACC. dup ACC.
      induction ACC0. i. destruct ACC, ACC1. ss. split.
      { econs. i. destruct a1. exists (exist _ (Some x0) (f)). ss. eapply H0. auto. }
      { econs. i. destruct a1. destruct x0; ss. exists (exist _ f y). ss. eapply H0. auto. }
    Qed.

    Lemma finite_from_wf_eq:
      forall n (x: finite n),
        ord.eq (ord.from_wf (finite_well_founded n) x) (ord.from_wf (finite_well_founded (Datatypes.S n)) (Some x)).
    Proof.
      Local Transparent ord.from_wf.
      i. eapply finite_from_acc_eq.
    Qed.

    Lemma finite_from_wf_set_eq:
      forall n,
        ord.eq (ord.from_wf_set (finite_well_founded n)) (ord.from_wf (finite_well_founded (Datatypes.S n)) None).
    Proof.
      Local Transparent ord.from_wf_set.
      i. split.
      { eapply ord.build_supremum. i. eapply ord.le_lt_lt.
        { eapply finite_from_wf_eq. }
        { eapply ord.lt_from_wf. ss. }
      }
      { unfold ord.from_wf at 1. destruct (finite_well_founded (Datatypes.S n) None).
        ss. econs. i. destruct a0. ss. destruct x; ss.
        exists f. eapply finite_from_acc_eq.
      }
    Qed.

    Lemma finite_S:
      forall n,
        ord.eq (ord.S (ord.from_wf_set (finite_well_founded n))) (ord.from_wf_set (finite_well_founded (Datatypes.S n))).
    Proof.
      Local Transparent ord.from_wf_set ord.S.
      i. split.
      - eapply ord.S_supremum. eapply ord.le_lt_lt.
        { eapply finite_from_wf_set_eq. }
        { eapply ord.from_wf_set_upperbound. }
      - econs. i. exists tt. ss. etransitivity.
        2: { eapply finite_from_wf_set_eq. }
        destruct a0.
        { eapply ord.lt_le. eapply ord.lt_from_wf. auto. }
        { reflexivity. }
    Qed.

    Lemma finite_O:
      ord.eq (ord.from_wf_set (finite_well_founded 0)) ord.O.
    Proof.
      Local Transparent ord.from_wf_set ord.O.
      split.
      { econs. i. ss. }
      { eapply ord.O_bot. }
    Qed.

    Lemma O_cardinal:
      cardinal.of_cardinal False ord.O.
    Proof.
      split.
      { exists (fun _ _ => False).
        assert (WF: well_founded (fun _ _: False => False)).
        { ii. ss. }
        exists WF. splits; auto. split.
        { econs. i. ss. }
        { eapply ord.O_bot. }
      }
      { i. eapply ord.O_bot. }
    Qed.

    Lemma O_is_cardinal:
      cardinal.is_cardinal ord.O.
    Proof.
      eapply cardinal.of_cardinal_is_cardinal. eapply O_cardinal.
    Qed.

    Lemma finite_cardinal_O:
      cardinal.is_cardinal (ord.from_wf_set (finite_well_founded 0)).
    Proof.
      eapply cardinal.of_cardinal_is_cardinal. eapply cardinal.eq_of_cardinal.
      2: { eapply O_cardinal. }
      symmetry. eapply finite_O.
    Qed.

    (* Lemma finite_incr n: ord.lt (cardinal (finite n)) (cardinal (finite (Datatypes.S n))). *)
  End FINITE.
End cardinal.


Module cardinality.
  Variant le (A B: Type): Prop :=
  | le_intro
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. eapply le_intro with (f:=id). i. ss.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H. inv H0. eapply le_intro with (f := compose f0 f).
    i. eapply INJ. eapply INJ0. auto.
  Qed.

  Variant oto (A B: Type): Prop :=
  | oto_intro
      (f: A -> B)
      (INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1)
      (SURJ: forall b, exists a, f a = b)
  .

  Variant bij (A B: Type): Prop :=
  | bij_intro
      (f: A -> B) (g: B -> A)
      (FG: forall a, g (f a) = a)
      (GF: forall b, f (g b) = b)
  .

  Lemma bij_oto_equiv A B: bij A B <-> oto A B.
  Proof.
    split; i.
    - inv H. eapply oto_intro with (f:=f).
      + i. eapply f_equal with (f:=g) in EQ.
        repeat rewrite FG in EQ.  auto.
      + i. exists (g b). auto.
    - inv H. eapply choice in SURJ. des.
      eapply bij_intro with (f:=f) (g:=f0); auto.
  Qed.

  Global Program Instance bij_Equivalence: Equivalence bij.
  Next Obligation.
  Proof.
    ii. eapply bij_intro with (f:=id) (g:=id); auto.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H. eapply bij_intro with (f:=g) (g:=f); auto.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H. inv H0. eapply bij_intro with (f:=compose f0 f) (g:=compose g g0); auto.
    - i. unfold compose. rewrite FG0. eapply FG.
    - i. unfold compose. rewrite GF. eapply GF0.
  Qed.

  Global Program Instance oto_Equivalence: Equivalence oto.
  Next Obligation.
  Proof.
    ii. apply bij_oto_equiv. reflexivity.
  Qed.
  Next Obligation.
  Proof.
    ii. apply bij_oto_equiv. eapply bij_oto_equiv in H. symmetry. auto.
  Qed.
  Next Obligation.
  Proof.
    ii. apply bij_oto_equiv. eapply bij_oto_equiv in H. eapply bij_oto_equiv in H0.
    transitivity y; auto.
  Qed.

  Lemma oto_le A B (OTO: oto A B): le A B.
  Proof.
    inv OTO. eapply le_intro with (f:=f). auto.
  Qed.

  Lemma bij_le A B (BIJ: bij A B): le A B.
  Proof.
    apply bij_oto_equiv in BIJ. eapply oto_le; auto.
  Qed.

  Definition eq (A B: Type): Prop := le A B /\ le B A.

  Lemma eq_le A B (EQ: eq A B): le A B.
  Proof.
    eapply EQ.
  Qed.

  Global Program Instance eq_Equivalence: Equivalence eq.
  Next Obligation.
  Proof.
    ii. split; reflexivity.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct H. split; auto.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct H, H0. split; etransitivity; eauto.
  Qed.

  Global Program Instance le_eq_PartialOrder: PartialOrder eq le.
  Next Obligation.
  Proof. ss. Qed.

  Section SANDWICH.
    Variable A1 B A: Type.
    Variable sub0: A1 -> B.
    Variable sub1: B -> A.
    Variable f: A -> A1.

    Hypothesis SUB0: forall a0 a1 (EQ: sub0 a0 = sub0 a1), a0 = a1.
    Hypothesis SUB1: forall b0 b1 (EQ: sub1 b0 = sub1 b1), b0 = b1.
    Hypothesis INJ: forall a0 a1 (EQ: f a0 = f a1), a0 = a1.

    Let Fixpoint aseq (n: nat) (a: A): A :=
      match n with
      | 0 => a
      | S n' => sub1 (sub0 (f (aseq n' a)))
      end.

    Let Fixpoint bseq (n: nat) (b: B): A :=
      match n with
      | 0 => sub1 b
      | S n' => sub1 (sub0 (f (bseq n' b)))
      end.

    Let bseq_aseq n:
      forall b, exists a, bseq n b = aseq n a.
    Proof.
      induction n; ss.
      - i. eauto.
      - i. specialize (IHn b). des. exists a. rewrite IHn. auto.
    Qed.

    Let aseq_S_bseq n:
      forall a, exists b, aseq (S n) a = bseq n b.
    Proof.
      induction n; ss.
      - i. eauto.
      - i. specialize (IHn a). des. exists b. rewrite IHn. auto.
    Qed.

    Let aseq_decrease n:
      forall a0, exists a1, aseq (S n) a0 = aseq n a1.
    Proof.
      i. hexploit (aseq_S_bseq n a0). i. des.
      hexploit (bseq_aseq n b). i. des.
      exists a. rewrite H. auto.
    Qed.

    Let bseq_decrease n:
      forall b0, exists b1, bseq (S n) b0 = bseq n b1.
    Proof.
      i. hexploit (bseq_aseq (S n) b0). i. des.
      hexploit (aseq_S_bseq n a). i. des.
      exists b. rewrite H. auto.
    Qed.

    Let in_gap (n: nat) (a1: A): Prop :=
      (exists a0, aseq n a0 = a1) /\
      (forall b0, bseq n b0 <> a1).

    Let in_gap_step (n: nat) (a1: A):
      in_gap (S n) a1 <->
      (exists a0, in_gap n a0 /\ a1 = sub1 (sub0 (f a0))).
    Proof.
      unfold in_gap. split; i.
      - des. ss. exists (aseq n a0). esplits; eauto.
        ii. eapply (H0 b0). rewrite H1. auto.
      - des. subst. ss. esplits; eauto. ii.
        eapply SUB1 in H. eapply SUB0 in H.
        eapply INJ in H. eapply H1; eauto.
    Qed.

    Let in_gap_all (a1: A): Prop :=
      exists n, in_gap n a1.

    Let is_g (g: A -> B): Prop :=
      forall a,
        (forall (GAP: in_gap_all a), g a = sub0 (f a)) /\
        (forall (NGAP: ~ in_gap_all a), sub1 (g a) = a)
    .

    Let is_g_exists: exists g, is_g g.
    Proof.
      eapply (choice (fun a b =>
                        (forall (GAP: in_gap_all a), b = sub0 (f a)) /\
                        (forall (NGAP: ~ in_gap_all a), sub1 b = a))).
      intros a. destruct (classic (in_gap_all a)).
      - exists (sub0 (f a)). split; eauto. ss.
      - destruct (classic (exists b, sub1 b = a)).
        { des. exists b. splits; ss. }
        exfalso. eapply H. exists 0. econs; ss; eauto.
    Qed.

    Let g_inj (g: A -> B) (G: is_g g):
      forall a0 a1 (EQ: g a0 = g a1), a0 = a1.
    Proof.
      i. edestruct (G a0). edestruct (G a1).
      destruct (classic (in_gap_all a0)), (classic (in_gap_all a1)).
      - eapply H in H3. eapply H1 in H4.
        rewrite H3 in *. rewrite H4 in *.
        eapply SUB0 in EQ. eapply INJ in EQ; auto.
      - exfalso. dup H3. dup H4.
        eapply H in H5. eapply H2 in H6.
        inv H3. eapply H4. exists (S x).
        eapply in_gap_step. esplits; eauto.
        rewrite <- H6. rewrite <- EQ. rewrite H5. auto.
      - exfalso. dup H3. dup H4.
        eapply H0 in H5. eapply H1 in H6.
        inv H4. eapply H3. exists (S x).
        eapply in_gap_step. esplits; eauto.
        rewrite <- H6. rewrite <- EQ. rewrite H5. auto.
      - eapply H0 in H3. eapply H2 in H4.
        rewrite EQ in H3. rewrite H3 in *. auto.
    Qed.

    Let g_surj (g: A -> B) (G: is_g g):
      forall b, exists a, g a = b.
    Proof.
      i. destruct (classic (in_gap_all (sub1 b))).
      - dup H. eapply G in H0. inv H. destruct x.
        { unfold in_gap in H1. des. ss. subst. exfalso. eapply H2; eauto. }
        eapply in_gap_step in H1. des. eapply SUB1 in H2. subst.
        dup H1. destruct (G a0). exploit H.
        { exists x. auto. } i. eauto.
      - dup H. eapply G in H0. eapply SUB1 in H0. eauto.
    Qed.

    Lemma sandwich_oto: oto A B.
    Proof.
      hexploit is_g_exists. i. des.
      eapply oto_intro with (f:=g).
      - eapply g_inj. auto.
      - eapply g_surj. auto.
    Qed.

  End SANDWICH.

  Lemma eq_oto_equiv A B: eq A B <-> oto A B.
  Proof.
    split; i.
    - inv H. inv H0. inv H1.
      eapply sandwich_oto with (A1:=A) (sub0:=f) (sub1:=f0) (f:=id); auto.
    - eapply bij_oto_equiv in H. inv H. split.
      + eapply le_intro with (f:=f).
        i. eapply f_equal with (f:=g) in EQ. repeat rewrite FG in EQ. auto.
      + eapply le_intro with (f:=g).
        i. eapply f_equal with (f:=f) in EQ. repeat rewrite GF in EQ. auto.
  Qed.

  Lemma eq_bij_equiv A B: eq A B <-> bij A B.
  Proof.
    erewrite bij_oto_equiv. eapply eq_oto_equiv.
  Qed.

  Global Program Instance le_bij_PartialOrder: PartialOrder bij le.
  Next Obligation.
  Proof.
    ii. ss. rewrite <- eq_bij_equiv. split; auto.
  Qed.

  Global Program Instance le_oto_PartialOrder: PartialOrder oto le.
  Next Obligation.
  Proof.
    ii. ss. rewrite <- eq_oto_equiv. split; auto.
  Qed.

  Definition lt A B: Prop := le A B /\ ~ le B A.

  Lemma lt_le A B (LT: lt A B): le A B.
  Proof.
    eapply LT.
  Qed.

  Lemma lt_le_lt B A C (LT: lt A B) (LE: le B C): lt A C.
  Proof.
    inv LT. split.
    - transitivity B; eauto.
    - ii. inv H1. eapply H0. transitivity C; auto. econs; eauto.
  Qed.

  Lemma le_lt_lt B A C (LE: le A B) (LT: lt B C): lt A C.
  Proof.
    inv LT. split.
    - transitivity B; eauto.
    - ii. inv H1. eapply H0. transitivity A; auto. econs; eauto.
  Qed.

  #[global] Program Instance lt_StrictOrder: StrictOrder lt.
  Next Obligation.
  Proof.
    ii. inv H. eapply H1. reflexivity.
  Qed.
  Next Obligation.
  Proof.
    ii. eapply (@lt_le_lt y); eauto. eapply lt_le; eauto.
  Qed.

  Lemma lt_not_le o0 o1 (LT: lt o0 o1) (LE: le o1 o0): False.
  Proof.
    eapply lt_StrictOrder. eapply le_lt_lt; eauto.
  Qed.

  Lemma lt_eq_lt A B0 B1 (EQ: eq B0 B1):
    lt A B0 <-> lt A B1.
  Proof.
    split; i.
    - inv EQ. eapply lt_le_lt; eauto.
    - inv EQ. eapply lt_le_lt; eauto.
  Qed.

  Lemma eq_lt_lt A0 A1 B (EQ: eq A0 A1):
    lt A0 B <-> lt A1 B.
  Proof.
    split; i.
    - inv EQ. eapply le_lt_lt; eauto.
    - inv EQ. eapply le_lt_lt; eauto.
  Qed.

  Lemma le_eq_le A B0 B1 (EQ: eq B0 B1):
    le A B0 <-> le A B1.
  Proof.
    split; i.
    - inv EQ. transitivity B0; auto.
    - inv EQ. transitivity B1; auto.
  Qed.

  Lemma eq_le_le A0 A1 B (EQ: eq A0 A1):
    le A0 B <-> le A1 B.
  Proof.
    split; i.
    - inv EQ. transitivity A0; auto.
    - inv EQ. transitivity A1; auto.
  Qed.

  Lemma le_eq_or_lt A B:
    le A B <-> (lt A B \/ eq A B).
  Proof.
    split; i.
    - destruct (classic (eq A B)); auto. left. split; auto.
      ii. eapply H0. split; auto.
    - des.
      + eapply H.
      + eapply eq_le. auto.
  Qed.

  Lemma total_le A B: le A B \/ le B A.
  Proof.
    hexploit (well_ordering.set_comparable A B). i. des.
    - left. econs; eauto.
    - right. econs; eauto.
  Qed.

  Lemma total A B: le A B \/ lt B A.
  Proof.
    destruct (classic (le A B)); auto.
    destruct (total_le A B); auto.
    right. split; auto.
  Qed.

  Lemma trichotomy A B: lt A B \/ eq A B \/ lt B A.
  Proof.
    destruct (total A B); auto. apply le_eq_or_lt in H. des; auto.
  Qed.

  Section cardinal.
    Let le_iff A B: le A B <-> cardinal._cardinal_le A B.
    Proof.
      split; i.
      - inv H. econs; eauto.
      - inv H. econs; eauto.
    Qed.

    Let eq_iff A B: eq A B <-> cardinal._cardinal_le A B /\ cardinal._cardinal_le B A.
    Proof.
      split; i.
      - inv H. split; apply le_iff; auto.
      - inv H. split; apply le_iff; auto.
    Qed.

    Let lt_iff A B: lt A B <-> cardinal._cardinal_le A B /\ ~ cardinal._cardinal_le B A.
    Proof.
      split; i.
      - inv H. split.
        + apply le_iff; auto.
        + erewrite <- le_iff. auto.
      - des. split.
        + eapply le_iff; eauto.
        + erewrite le_iff; eauto.
    Qed.

    Lemma cardinal_upperbound A B (CARD: lt B A)
          (R: B -> B -> Prop) (WF: well_founded R)
      :
        ord.lt (ord.from_wf_set WF) (cardinal.cardinal A).
    Proof.
      eapply cardinal._cardinal_upperbound. apply lt_iff; auto.
    Qed.

    Lemma cardinal_supremum A c
          (UPPER: forall B (CARD: lt B A)
                         (R: B -> B -> Prop) (WF: well_founded R),
              ord.lt (ord.from_wf_set WF) c)
      :
        ord.le (cardinal.cardinal A) c.
    Proof.
      eapply cardinal._cardinal_supremum. i. eapply UPPER. des. split.
      - inv CARD. econs; eauto.
      - ii. eapply CARD0. inv H. econs; eauto.
    Qed.

    Lemma cardinal_le_iff A B:
      le A B <-> ord.le (cardinal.cardinal A) (cardinal.cardinal B).
    Proof.
      rewrite <- cardinal._cardinal_le_iff. auto.
    Qed.

    Lemma cardinal_eq_iff A B:
      eq A B <-> ord.eq (cardinal.cardinal A) (cardinal.cardinal B).
    Proof.
      rewrite <- cardinal._cardinal_eq_iff. auto.
    Qed.

    Lemma cardinal_lt_iff A B:
      lt A B <-> ord.lt (cardinal.cardinal A) (cardinal.cardinal B).
    Proof.
      rewrite <- cardinal._cardinal_lt_iff. auto.
    Qed.
  End cardinal.

  Lemma cardinal_to_total_bij A:
    eq A (toSet.to_total_set (cardinal.cardinal A)).
  Proof.
    eapply cardinal_eq_iff.
    eapply cardinal.cardinal_to_total_bij1.
  Qed.

  Lemma lt_well_founded: well_founded lt.
  Proof.
    assert (forall (o: ord.t) A (EQ: ord.eq o (cardinal.cardinal A)), Acc lt A).
    { eapply (well_founded_induction ord.lt_well_founded (fun o => forall A (EQ: ord.eq o (cardinal.cardinal A)), Acc lt A)).
      i. econs. i. apply cardinal_lt_iff in H0.
      eapply H.
      { eapply ord.lt_eq_lt.
        { eapply EQ. }
        { eapply H0. }
      }
      { reflexivity. }
    }
    ii. eapply (H (cardinal.cardinal a)). reflexivity.
  Qed.

  Definition power A := A -> Prop.
  Lemma cantor A: lt A (power A).
  Proof.
    eapply cardinal_lt_iff.
    eapply (@ord.lt_le_lt (cardinal.next_cardinal A)).
    { eapply cardinal.next_cardinal_incr. }
    { eapply cardinal.next_cardinal_le_power_set. }
  Qed.

  Lemma le_power A0 A1 (LE: le A0 A1):
    le (power A0) (power A1).
  Proof.
    inv LE.
    eapply le_intro with (f := fun s y => exists x, f x = y /\ s x).
    i. extensionality x. pose proof (equal_f EQ (f x)) as EQ0.
    apply propositional_extensionality.
    transitivity (exists x0, f x0 = f x /\ a0 x0).
    { split; i; eauto.
      des. apply INJ in H. subst. auto. }
    { rewrite EQ0. split; i; eauto.
      des. apply INJ in H. subst. auto. }
  Qed.

  Definition O := False.
  Lemma O_bot A: le O A.
  Proof.
    eapply le_intro with (f:=False_rect _).
    i. ss.
  Qed.

  Definition S A:= toSet.to_total_set (cardinal.next_cardinal A).
  Lemma S_lt A: lt A (S A).
  Proof.
    eapply cardinal_lt_iff. unfold S.
    eapply ord.lt_eq_lt.
    { symmetry. eapply cardinal.cardinal_to_total_bij2.
      eapply cardinal.next_cardinal_of_cardinal. }
    { eapply cardinal.next_cardinal_incr. }
  Qed.
  Lemma S_supremum A B (LT: lt A B): le (S A) B.
  Proof.
    apply cardinal_lt_iff in LT.
    eapply cardinal.next_cardinal_supremum in LT.
    apply cardinal_le_iff. transitivity (cardinal.next_cardinal A); auto.
    unfold S. eapply cardinal.to_total_cardinal_le.
  Qed.

  Lemma S_le_power A: le (S A) (power A).
  Proof.
    eapply S_supremum. eapply cantor.
  Qed.

  Definition join X (TS: X -> Type):=
    toSet.to_total_set (@ord.join X (fun x => cardinal.cardinal (TS x))).

  Definition continnum_hypothesis_on A: Prop := eq (S A) (power A).
End cardinality.
