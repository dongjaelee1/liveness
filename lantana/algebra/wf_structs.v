(** Lexicographic product of well-founded relations, where the first component is compared up to
    an equivalence [EA]. *)

From Stdlib Require Import RelationClasses.

Variant prod_eq_lt {A B} (EA RA : A -> A -> Prop) (RB : B -> B -> Prop) : A * B -> A * B -> Prop :=
  | prod_eq_lt_left a0 a1 b0 b1
      (ALT : RA a0 a1)
    :
    prod_eq_lt EA RA RB (a0, b0) (a1, b1)
  | prod_eq_lt_right a0 a1 b0 b1
      (ALE : EA a0 a1 \/ RA a0 a1) (BLT : RB b0 b1)
    :
    prod_eq_lt EA RA RB (a0, b0) (a1, b1).

Lemma prod_eq_lt_eq_lt
  A B (EA RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (EQUIV : Equivalence EA)
  (PROPER : forall a a1 a2, EA a1 a2 -> RA a a1 -> RA a a2)
  a0 a1 a2 b0 b :
  EA a1 a2 ->
  prod_eq_lt EA RA RB (a0, b0) (a1, b) ->
  prod_eq_lt EA RA RB (a0, b0) (a2, b).
Proof.
  intros. inversion H0; subst.
  - econstructor 1; eauto.
  - econstructor 2; eauto. destruct ALE; eauto. left. etransitivity; eauto.
Qed.

Lemma prod_eq_lt_eq_Acc
  A B (EA RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (EQUIV : Equivalence EA)
  (PROPER : forall a a1 a2, EA a1 a2 -> RA a a1 -> RA a a2)
  a1 a2 b :
  EA a1 a2 ->
  Acc (prod_eq_lt EA RA RB) (a1, b) ->
  Acc (prod_eq_lt EA RA RB) (a2, b).
Proof.
  intros. revert a2 H. remember (a1, b) as x. revert a1 b Heqx. induction H0; intros. subst.
  econstructor. intros. destruct y. eapply (H0 (a, b0)); eauto. 2: reflexivity.
  eapply prod_eq_lt_eq_lt; eauto. symmetry. auto.
Qed.

Lemma prod_eq_lt_well_founded
  A B (EA RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (EQUIV : Equivalence EA)
  (PROPER : forall a a1 a2, EA a1 a2 -> RA a a1 -> RA a a2)
  (WFA : well_founded RA)
  (WFB : well_founded RB)
  :
  well_founded (prod_eq_lt EA RA RB).
Proof.
  intro. destruct a as [a b]. revert b.
  induction (WFA a). rename x into a. clear H. rename H0 into IHA.
  intros b. induction (WFB b). rename x into b. clear H. rename H0 into IHB.
  econstructor. intros. inversion H; eauto. destruct ALE; subst; eauto.
  eapply prod_eq_lt_eq_Acc; eauto. symmetry. auto.
Qed.

Global Instance prod_eq_lt_Transitive {A B} {EA RA : A -> A -> Prop} {RB : B -> B -> Prop}
  (EQUIV : Equivalence EA)
  (PROPER_1 : forall a a1 a2, EA a1 a2 -> RA a a1 -> RA a a2)
  (PROPER_2 : forall a a1 a2, EA a1 a2 -> RA a1 a -> RA a2 a) :
  Transitive RA -> Transitive RB -> Transitive (prod_eq_lt EA RA RB).
Proof.
  intros. repeat intro. inversion H1; inversion H2; subst.
  - inversion H5; subst. econstructor 1. eauto.
  - inversion H5; subst. destruct ALE.
    + subst. econstructor 1. eauto.
    + econstructor 1; eauto.
  - inversion H5; subst. destruct ALE.
    + subst. econstructor 1; eauto. eapply PROPER_2; eauto. symmetry. auto.
    + econstructor 1; eauto.
  - inversion H5; subst. destruct ALE.
    + subst. destruct ALE0.
      * subst. econstructor 2; eauto. left. etransitivity; eauto.
      * econstructor 1; eauto. eapply PROPER_2; eauto. symmetry; auto.
    + destruct ALE0.
      * subst. econstructor 1; eauto.
      * econstructor 1; eauto.
Qed.
