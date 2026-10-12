From lantana.ordinal Require Import sflib basics.
From lantana.ordinal Require Export ordinal arithmetic hessenberg classical_ordinal.

From Coq Require Import Classes.RelationClasses Classes.Morphisms.

Set Implicit Arguments.
Set Primitive Projections.


(* TODO: find a constructive proof!! *)
Module classicJacobsthal.
  Lemma mult_dist o0 o1 o2: ord.eq (jacobsthal.mult o0 (hessenberg.add o1 o2)) (hessenberg.add (jacobsthal.mult o0 o1) (jacobsthal.mult o0 o2)).
  Proof.
    destruct (classicOrd.total o0 ord.O) as [LE|LT].
    { assert (ZERO: ord.eq o0 ord.O).
      { split; auto. apply ord.O_bot. }
      rewrite ZERO. rewrite ! jacobsthal.mult_O_l. rewrite hessenberg.add_O_l. reflexivity.
    }
    revert o1 o2.
    eapply (double_well_founded_induction ord.lt_well_founded ord.lt_well_founded).
    i. hexploit (classicOrd.limit_or_S a1). i. des.
    { hexploit ord.is_S_unique.
      { eapply H. }
      { eapply ord.S_is_S. }
      i. rewrite H0. rewrite hessenberg.add_S_l.
      rewrite jacobsthal.mult_S. rewrite jacobsthal.mult_S.
      rewrite IHL.
      { rewrite hessenberg.add_assoc. reflexivity. }
      { eapply H. }
    }
    hexploit (classicOrd.limit_or_S b1). i. des.
    { hexploit ord.is_S_unique.
      { eapply H1. }
      { eapply ord.S_is_S. }
      i. rewrite H2. rewrite hessenberg.add_S_r.
      rewrite jacobsthal.mult_S. rewrite jacobsthal.mult_S.
      rewrite IHR.
      { rewrite hessenberg.add_comm.
        rewrite hessenberg.add_assoc.
        eapply hessenberg.eq_add_r.
        eapply hessenberg.add_comm.
      }
      { eapply H1. }
    }
    hexploit ord.is_join_unique.
    { eapply H. }
    { eapply ord.join_is_join. }
    i. rewrite H3.
    hexploit ord.is_join_unique.
    { eapply H1. }
    { eapply ord.join_is_join. }
    i. rewrite H4.
    rewrite jacobsthal.mult_join. rewrite jacobsthal.mult_join.
    rewrite <- ord.build_join; auto.
    rewrite <- ord.build_join; auto.
    symmetry. rewrite <- ord.build_join.
    2:{ ii. specialize (H0 a0). des. exists a2. eapply jacobsthal.lt_mult_r; auto. }
    rewrite <- ord.build_join.
    2:{ ii. specialize (H2 a0). des. exists a2. eapply jacobsthal.lt_mult_r; auto. }
    rewrite hessenberg.add_red.
    rewrite hessenberg.add_red.
    rewrite jacobsthal.mult_union. eapply ord.eq_union.
    { rewrite jacobsthal.mult_build. rewrite ord.build_join.
      2:{ ii. specialize (H2 a0). des. exists a2. eapply hessenberg.lt_add_r. eapply jacobsthal.lt_mult_r; auto. }
      split.
      { eapply ord.le_join. i. hexploit (H2 a0); auto. i. des.
        exists a2. rewrite (ord.build_join H0); auto.
        rewrite <- H3. rewrite IHR.
        2:{ rewrite H4. rewrite <- ord.build_join; auto. eapply ord.build_upperbound. }
        eapply ord.S_supremum in H5. rewrite <- H5.
        rewrite jacobsthal.mult_S. rewrite <- hessenberg.add_assoc.
        rewrite <- hessenberg.add_assoc.
        eapply hessenberg.le_add_l.
        eapply ord.build_supremum. i.
        eapply ord.lt_le_lt.
        { apply jacobsthal.lt_mult_r; auto. eapply ord.build_upperbound. }
        { rewrite ord.build_join; auto.
          rewrite <- H3. rewrite hessenberg.add_comm.
          rewrite <- hessenberg.add_assoc. eapply hessenberg.add_base_r.
        }
      }
      { eapply ord.le_join. i. hexploit (H2 a0); auto. i. des.
        exists a2. rewrite ord.build_join; auto.
        rewrite <- H3. rewrite IHR.
        2:{ rewrite H4. rewrite <- ord.build_join; auto. eapply ord.build_upperbound. }
        eapply ord.S_supremum in H5. rewrite <- H5.
        rewrite jacobsthal.mult_S. rewrite <- hessenberg.add_assoc.
        rewrite <- hessenberg.add_assoc.
        eapply hessenberg.le_add_l.
        rewrite hessenberg.add_comm.
        eapply hessenberg.le_add_l.
        rewrite H3. rewrite jacobsthal.mult_join.
        rewrite ord.build_join; auto.
        2:{ ii. specialize (H0 a3). des. exists a4. apply jacobsthal.lt_mult_r; auto. }
        reflexivity.
      }
    }
    { rewrite jacobsthal.mult_build. rewrite ord.build_join.
      2:{ ii. specialize (H0 a0). des. exists a2. eapply hessenberg.lt_add_l. eapply jacobsthal.lt_mult_r; auto. }
      split.
      { eapply ord.le_join. i. hexploit (H0 a0); auto. i. des.
        exists a2. rewrite (ord.build_join H2); auto.
        rewrite <- H4. rewrite IHL.
        2:{ rewrite H3. rewrite <- ord.build_join; auto. eapply ord.build_upperbound. }
        eapply ord.S_supremum in H5. rewrite <- H5.
        rewrite jacobsthal.mult_S. transitivity (jacobsthal.mult o0 (os a0) ⊕ o0 ⊕ jacobsthal.mult o0 b1)%ordi.
        { eapply hessenberg.le_add_r.
          eapply ord.build_supremum. i.
          eapply ord.lt_le_lt.
          { apply jacobsthal.lt_mult_r; auto. eapply ord.build_upperbound. }
          { rewrite ord.build_join; auto.
            rewrite <- H4. eapply hessenberg.add_base_r.
          }
        }
        { etransitivity; [|eapply hessenberg.add_base_r].
          rewrite <- hessenberg.add_assoc.
          eapply hessenberg.le_add_l. rewrite hessenberg.add_comm. reflexivity.
        }
      }
      { eapply ord.le_join. i. hexploit (H0 a0); auto. i. des.
        exists a2. rewrite ord.build_join; auto.
        rewrite <- H4. rewrite IHL.
        2:{ rewrite H3. rewrite <- ord.build_join; auto. eapply ord.build_upperbound. }
        eapply ord.S_supremum in H5. rewrite <- H5.
        rewrite jacobsthal.mult_S. rewrite hessenberg.add_assoc.
        eapply hessenberg.le_add_r.
        eapply hessenberg.le_add_r.
        rewrite H4. rewrite jacobsthal.mult_join.
        rewrite ord.build_join; auto.
        2:{ ii. specialize (H2 a3). des. exists a4. apply jacobsthal.lt_mult_r; auto. }
        reflexivity.
      }
    }
  Qed.

  Lemma mult_assoc o0 o1 o2: ord.eq (jacobsthal.mult (jacobsthal.mult o0 o1) o2) (jacobsthal.mult o0 (jacobsthal.mult o1 o2)).
  Proof.
    revert o0 o1. induction o2. i. etransitivity.
    { eapply jacobsthal.mult_build. } etransitivity.
    2: {
      eapply jacobsthal.eq_mult_r; auto.
      { symmetry. eapply jacobsthal.mult_build. }
    }
    etransitivity.
    2: { symmetry. eapply jacobsthal.mult_join. }
    split.
    { eapply ord.le_join. i. exists a0.
      etransitivity.
      { eapply hessenberg.le_add_r. eapply H. }
      { eapply mult_dist. }
    }
    { eapply ord.le_join. i. exists a0.
      etransitivity.
      { eapply mult_dist. }
      { eapply hessenberg.le_add_r. eapply H. }
    }
  Qed.

  Lemma expn_add base (POS: ord.lt ord.O base) o0 o1:
    ord.eq (jacobsthal.expn base (ordArith.add o0 o1)) (jacobsthal.mult (jacobsthal.expn base o0) (jacobsthal.expn base o1)).
  Proof.
    revert o0. induction o1. i. etransitivity.
    { eapply jacobsthal.eq_expn_r. eapply ordArith.add_build. }
    etransitivity.
    { eapply jacobsthal.expn_union. auto. }
    etransitivity.
    2: { eapply jacobsthal.eq_mult_r. symmetry. eapply jacobsthal.expn_build. }
    etransitivity.
    2: { symmetry. eapply jacobsthal.mult_union. }
    etransitivity.
    { eapply ord.eq_union.
      { reflexivity. }
      eapply jacobsthal.expn_join. auto.
    }
    etransitivity.
    { eapply ord.union_assoc. }
    eapply ord.eq_union.
    { etransitivity.
      { eapply ord.union_comm. }
      { etransitivity.
        2: { symmetry. eapply jacobsthal.mult_1_r. }
        { eapply ord.union_max. eapply ord.S_supremum. eapply jacobsthal.expn_pos. }
      }
    }
    etransitivity.
    2: { symmetry. eapply jacobsthal.mult_join. }
    eapply ord.eq_join. i.
    etransitivity.
    { eapply jacobsthal.expn_S. auto. }
    etransitivity.
    2: { eapply mult_assoc. }
    eapply jacobsthal.eq_mult_l.
    eapply H.
  Qed.

  Lemma expn_mult o0 (POS: ord.lt ord.O o0) o1 o2:
    ord.eq (jacobsthal.expn o0 (ordArith.mult o1 o2)) (jacobsthal.expn (jacobsthal.expn o0 o1) o2).
  Proof.
    induction o2.
    etransitivity.
    { eapply jacobsthal.eq_expn_r. eapply ordArith.mult_build. }
    etransitivity.
    { eapply jacobsthal.expn_join. auto. }
    etransitivity.
    2: { symmetry. eapply jacobsthal.expn_build. }
    eapply ord.eq_union.
    { reflexivity. }
    eapply ord.eq_join. i.
    etransitivity.
    { eapply expn_add. auto. }
    eapply jacobsthal.eq_mult_l. auto.
  Qed.

End classicJacobsthal.
