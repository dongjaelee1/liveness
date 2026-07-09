From lantana Require Import axioms.
From Coq Require Export Relations.Relation_Operators.
From Coq Require Import RelationClasses Relations.Operators_Properties.

(* Set Implicit Arguments. *)

Lemma well_founded_irrefl A (R : A -> A -> Prop) (WF : well_founded R) : forall x, ~ R x x.
Proof. intros x HR. specialize (WF x). induction WF; eauto. Qed.

(** clos_trans *)
Lemma clos_trans_well_founded
  A (R : A -> A -> Prop) (WF : well_founded R)
  :
  well_founded (clos_trans_n1 _ R).
Proof.
  intro. pose proof (well_founded_induction WF (fun a1 => forall a0 (LT : clos_trans_n1 A R a0 a1 \/ a0 = a1), Acc (clos_trans_n1 A R) a0)).
  eapply H.
  { clear a H. intros a1 IH. intros. econstructor. intros. destruct LT.
    - inversion H0.
      + eapply IH; eauto.
      + eapply IH; eauto. left.
        eapply Operators_Properties.clos_trans_tn1. econstructor 2.
        * eapply Operators_Properties.clos_tn1_trans; eauto.
        * eapply Operators_Properties.clos_tn1_trans; eauto.
    - subst. inversion H; eauto.
  }
  { right. reflexivity. }
Qed.

Lemma clos_trans_step A (R : A -> A -> Prop) x y : clos_trans_n1 _ R x y -> exists z, R z y /\ (x = z \/ clos_trans_n1 _ R x z).
Proof. intros. destruct H; eauto. Qed.

Global Instance clos_trans_n1_trans A (R : A -> A -> Prop) : Transitive (clos_trans_n1 _ R).
Proof.
  unfold Transitive. intros.
  eapply clos_trans_tn1_iff.
  econstructor 2; eapply clos_trans_tn1_iff; eauto.
Qed.

(** ord_tree: tree with join. *)
(* Reference: Coq development of Fair Operational Semantics. *)
Inductive ord_tree (A : Type) : Type :=
| ord_tree_base
| ord_tree_cons (childs : A -> ord_tree A)
.
Arguments ord_tree_base {A}.
Arguments ord_tree_cons {A}.

Variant ord_tree_lt {A} : ord_tree A -> ord_tree A -> Prop :=
  | ord_tree_lt_intro
      childs a
    :
    ord_tree_lt (childs a) (ord_tree_cons childs)
.

Lemma ord_tree_lt_well_founded A
  :
  well_founded (@ord_tree_lt A).
Proof.
  intros a. induction a.
  { econstructor; intros. inversion H. }
  { econstructor; intros. inversion H0. eauto. }
Qed.

Lemma ord_tree_join A (P : A -> Prop) (R : A -> ord_tree A -> Prop)
  (ORD : forall a (SAT : P a), exists o, R a o)
  :
  exists o1, forall (a : A) (SAT : P a),
  exists o0, R a o0 /\ ord_tree_lt o0 o1.
Proof.
  pose proof (choice (fun a o => P a -> R a o)).
  assert (forall x : A, exists y : ord_tree A, (fun (a : A) (o : ord_tree A) => P a -> R a o) x y).
  { intros. destruct (classic (P x)).
    { specialize (ORD _ H0). destruct ORD. eauto. }
    { eexists (ord_tree_base). intros. congruence. }
  }
  specialize (H H0); clear H0. destruct H as [f H]. exists (ord_tree_cons f).
  intros. exists (f a). split; [eauto |]. econstructor; eauto.
Qed.

Definition ord_tree_lt_tc {A : Type} : ord_tree A -> ord_tree A -> Prop :=
  clos_trans_n1 _ (ord_tree_lt (A:=A)).

Lemma ord_tree_lt_tc_well_founded A :
  well_founded (@ord_tree_lt_tc A).
Proof. apply clos_trans_well_founded, ord_tree_lt_well_founded. Qed.

Lemma ord_tree_join_tc A (P : A -> Prop) (R : A -> ord_tree A -> Prop)
  (ORD : forall a (SAT : P a), exists o, R a o)
  :
  exists o1, forall (a : A) (SAT : P a),
  exists o0, R a o0 /\ ord_tree_lt_tc o0 o1.
Proof.
  pose proof (ord_tree_join _ _ _ ORD) as (?& Hj).
  exists x. intros. specialize (Hj _ SAT). destruct Hj as (?&?&?).
  exists x0. split; [auto|]. econstructor. auto.
Qed.

Global Instance ord_tree_lt_tc_transitive A : Transitive (@ord_tree_lt_tc A).
Proof. apply _. Qed.

Lemma ord_tree_base_bot {A : Type} :
  inhabited A ->
  forall (t : ord_tree A), (t = ord_tree_base) \/ ord_tree_lt_tc ord_tree_base t.
Proof.
  intros. induction t; auto.
  right. destruct H. destruct (H0 X).
  - rewrite <-H. econstructor 1. econstructor.
  - etransitivity; [eauto|]. econstructor 1. econstructor.
Qed.

(** succ *)
Variant succ_rel (n : nat) : nat -> Prop := succ_rel_intro : succ_rel n (S n).

Lemma succ_rel_well_founded : well_founded succ_rel.
Proof. intro. induction a; econstructor; intros; inversion H. auto. Qed.

Lemma succ_clos_trans : forall m n, clos_trans_n1 nat succ_rel m n <-> m < n.
Proof.
  split.
  - revert m. induction n.
    + intros. exfalso. inversion H; inversion H0.
    + intros. inversion H.
      * inversion H0. auto.
      * inversion H0. subst. econstructor. eapply IHn, H1.
  - revert m. induction n.
    + intros. inversion H.
    + intros. inversion H.
      * econstructor 1. econstructor.
      * econstructor 2. econstructor. eapply IHn. auto.
Qed.

(** double *)
Variant double_rel {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  : A * B -> A * B -> Prop :=
| double_rel_left a0 a1 b (LT : RA a0 a1) : double_rel RA RB (a0, b) (a1, b)
| double_rel_right a b0 b1 (LT : RB b0 b1) : double_rel RA RB (a, b0) (a, b1).

Lemma double_rel_well_founded {A B} {RA : A -> A -> Prop} {RB : B -> B -> Prop}
  (WFA : well_founded RA) (WFB : well_founded RB)
  :
  well_founded (double_rel RA RB).
Proof.
  cut (forall a b, Acc (double_rel RA RB) (a, b)).
  { intros H a. destruct a as [a b]. eapply H. }
  intros a0. pattern a0. revert a0.
  eapply (well_founded_induction WFA).
  intros a0 IHL. intros b0. pattern b0. revert b0.
  eapply (well_founded_induction WFB).
  intros b0 IHR. econstructor. intros [a1 b1]. intros. inversion H.
  { eapply IHL; eauto. }
  { eapply IHR; eauto. }
Qed.

Lemma double_well_founded_induction A B (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (WFA : well_founded RA) (WFB : well_founded RB)
  (P : A -> B -> Prop)
  (IND : forall a1 b1
           (IHL : forall a0 (LT : RA a0 a1), P a0 b1)
           (IHR : forall b0 (LT : RB b0 b1), P a1 b0),
     P a1 b1)
  :
  forall a b, P a b.
Proof.
  cut (forall ab, P (fst ab) (snd ab)).
  { intros. apply (H (a, b)). }
  intros ab. pattern ab. revert ab.
  eapply (well_founded_induction (double_rel_well_founded WFA WFB)).
  intros [a b] ?. simpl. eapply IND.
  { intros. eapply (H (a0, b)). econstructor 1. auto. }
  { intros. eapply (H (a, b0)). econstructor 2. auto. }
Qed.

(** option *)
Variant option_lt {A} (R : A -> A -> Prop) : option A -> option A -> Prop :=
  | optoin_lt_top a :
    option_lt R (Some a) None
  | optoin_lt_normal a0 a1 (LT : R a0 a1) :
    option_lt R (Some a0) (Some a1).

Lemma option_lt_well_founded A (R : A -> A -> Prop) (WF: well_founded R) :
  well_founded (option_lt R).
Proof.
  cut (forall a, Acc (option_lt R) (Some a)).
  { intros H a. destruct a; simpl; auto. econstructor. intros. inversion H0; eauto. }
  intros. induction (WF a). econstructor.
  intros. inversion H1. eauto.
Qed.

(** sum *)
Variant sum_lt {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A + B -> A + B -> Prop :=
  | sum_lt_left a0 a1 (LT : RA a0 a1) :
    sum_lt RA RB (inl a0) (inl a1)
  | sum_lt_right b0 b1 (LT : RB b0 b1) :
    sum_lt RA RB (inr b0) (inr b1)
  | sum_lt_cross a b :
    sum_lt RA RB (inl a) (inr b).

Lemma sum_lt_well_founded
  A B (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (WFA : well_founded RA)
  (WFB : well_founded RB)
  :
  well_founded (sum_lt RA RB).
Proof.
  assert (ACCA : forall a, Acc (sum_lt RA RB) (inl a)).
  { intros. induction (WFA a). econstructor.
    intros. inversion H1. eauto.
  }
  intro. destruct a as [a|b]; eauto.
  induction (WFB b). econstructor.
  intros. inversion H1; eauto.
Qed.

(** prod *)
Variant prod_lt {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A * B -> A * B -> Prop :=
  | prod_lt_left a0 a1 b0 b1
      (ALT : RA a0 a1)
    :
    prod_lt RA RB (a0, b0) (a1, b1)
  | prod_lt_right a0 a1 b0 b1
      (ALE : a0 = a1 \/ RA a0 a1) (BLT : RB b0 b1)
    :
    prod_lt RA RB (a0, b0) (a1, b1).

Lemma prod_lt_well_founded
  A B (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (WFA : well_founded RA)
  (WFB : well_founded RB)
  :
  well_founded (prod_lt RA RB).
Proof.
  intro. destruct a as [a b]. revert b.
  induction (WFA a). rename x into a. clear H. rename H0 into IHA.
  intros b. induction (WFB b). rename x into b. clear H. rename H0 into IHB.
  econstructor. intros. inversion H; eauto. destruct ALE; subst; eauto.
Qed.

Global Instance prod_lt_Transitive {A B} {RA : A -> A -> Prop} {RB : B -> B -> Prop} :
  Transitive RA -> Transitive RB -> Transitive (prod_lt RA RB).
Proof.
  intros. repeat intro. inversion H1; inversion H2; subst.
  - inversion H5; subst. econstructor 1. eauto.
  - inversion H5; subst. destruct ALE.
    + subst. econstructor 1. auto.
    + econstructor 1; eauto.
  - inversion H5; subst. destruct ALE.
    + subst. econstructor 1; auto.
    + econstructor 1; eauto.
  - inversion H5; subst. destruct ALE.
    + subst. destruct ALE0.
      * subst. econstructor 2; eauto.
      * econstructor 1; auto.
    + destruct ALE0.
      * subst. econstructor 1; eauto.
      * econstructor 1; eauto.
Qed.

(** prod with equivalence *)
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

(** option_bot *)
Variant option_bot_lt {A} (R : A -> A -> Prop) : option A -> option A -> Prop :=
  | optoin_bot_lt_bot a :
    option_bot_lt R None (Some a)
  | optoin_bot_lt_normal a0 a1
      (LT : R a0 a1)
    :
    option_bot_lt R (Some a0) (Some a1).

Lemma option_bot_lt_well_founded A (R : A -> A -> Prop) (WF : well_founded R) :
  well_founded (option_bot_lt R).
Proof.
  cut (forall a, Acc (option_bot_lt R) (Some a)).
  { intros H a. destruct a; auto. econstructor. intros. inversion H0. }
  intros. induction (WF a). econstructor.
  intros. inversion H1; eauto. subst.
  econstructor. intros. inversion H2.
Qed.
