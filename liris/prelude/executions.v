From stdpp Require Import base relations.
From liris Require Import axioms.

Section definitions.
  Context `(R : relation A).

  Inductive all_eventually (x : A) (P : A -> Prop) : Prop :=
  | all_eventually_done :
    (P x) -> all_eventually x P
  | all_eventually_do_step :
    (exists x', R x x') -> (forall y, R x y -> all_eventually y P) -> all_eventually x P.

  CoInductive ex_always_not (x : A) (P : A -> Prop) : Prop :=
  | ex_always_not_done :
    (forall x', ¬ R x x') -> (¬ P x) -> ex_always_not x P
  | ex_always_not_do_step y :
    (¬ P x) -> R x y -> ex_always_not y P -> ex_always_not x P.

End definitions.

Lemma nat_lt_all_eventually_zero : forall (n : nat), all_eventually (flip lt) n (fun x => x = 0).
Proof.
  intros n. assert (forall m, m <= n -> all_eventually (flip lt) m (fun x => x = 0)); [|eauto].
  induction n; simpl; intros.
  - constructor 1. lia.
  - destruct m.
    + constructor 1. auto.
    + constructor 2; simpl; [exists m; eauto|]. intros. apply IHn. lia.
Qed.

Lemma nat_gt_ex_always_not_zero : forall (n : nat), n > 0 -> ex_always_not (flip gt) n (fun x => x = 0).
Proof.
  cofix IH; intros. eapply (ex_always_not_do_step _ _ _ (S n)).
  - lia.
  - simpl. lia.
  - eauto.
Qed.

(* Section proofs. *)

(*   Lemma ex_always_not_ex_loop {A} (R : relation A) x P : *)
(*     ex_always_not R x P -> ex_loop R x. *)
(*   Proof. *)
(*     revert x. cofix IH; intros x Hex. destruct Hex. econstructor; eauto. *)
(*   Qed. *)

(* End proofs. *)

Section classical_proofs.

  (* From transfinite Iris. *)
  Lemma sn_not_ex_loop {A} (R : relation A) x :
    ¬ex_loop R x → sn R x.
  Proof.
    intros Hex. destruct (classic (sn R x)) as [|Hsn]; [done|].
    destruct Hex. revert x Hsn. cofix IH; intros x Hsn.
    destruct (classic (∃ y, R x y ∧ ¬sn R y)) as [(y&?&?)|Hnot].
    - exists y. all: auto.
    - destruct Hsn. constructor. intros y Hxy.
      destruct (classic (sn R y)). auto. naive_solver.
  Qed.

  Lemma not_all_eventually_ex_always_not {A} (R : relation A) x (P : A -> Prop) :
    ¬ all_eventually R x P -> ex_always_not R x P.
  Proof.
    intros Hsn. revert x Hsn. cofix IH; intros x Hsn.
    destruct (classic (exists y, R x y /\ ¬ all_eventually R y P)) as [(y&?&?)|Hnot].
    - econstructor 2; eauto. intro HP. destruct Hsn. constructor 1. auto.
    - destruct (classic (exists x', R x x')) as [[x' Hnext] | Hnotnext].
      + destruct Hsn. constructor 2; [eauto |]. intros y Hxy.
        destruct (classic (all_eventually R y P)). auto. naive_solver.
      + constructor 1; [naive_solver|]. intros Hp. destruct Hsn. constructor 1. auto.
  Qed.

  Lemma ex_always_not_not_all_eventually {A} (R : relation A) x (P : A -> Prop) :
    ex_always_not R x P -> ¬ all_eventually R x P.
  Proof.
    intros Hex Hsn. revert Hex. induction Hsn; intros.
    - inv Hex; auto.
    - destruct H as [x' Hxx']. inv Hex.
      + naive_solver.
      + eauto.
  Qed.

End classical_proofs.
