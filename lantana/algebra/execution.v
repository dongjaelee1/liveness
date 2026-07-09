From stdpp Require Import base relations.
From lantana.prelude Require Import axioms wf_structs.

Section classical_proofs.

  (* This Lemma is proven in transfinite Iris. *)
  Lemma not_ex_loop_sn {A} (R : relation A) x :
    (¬ ex_loop R x) → sn R x.
  Proof.
    intros Hex. destruct (classic (sn R x)) as [|Hsn]; [done|].
    destruct Hex. revert x Hsn. cofix IH; intros x Hsn.
    destruct (classic (∃ y, R x y ∧ ¬sn R y)) as [(y&?&?)|Hnot].
    - exists y. all: auto.
    - destruct Hsn. constructor. intros y Hxy.
      destruct (classic (sn R y)). auto. naive_solver.
  Qed.

  (** We show that any Acc has a measure_rep (as long as universe is consistent). *)
  Inductive Acc_ord_tree {A} (R : relation A) x (μ : ord_tree A) : Prop :=
  | Acc_ord_tree_intro μ' :
    (ord_tree_lt_tc μ' μ) →
    (∀ y, R y x → Acc_ord_tree R y μ') →
    Acc_ord_tree R x μ.
  (* Inductive Acc_ord_tree {A} (R : relation A) x (μ : ord_tree A) : Prop := *)
  (* | Acc_ord_tree_intro : *)
  (*   (∀ y, R y x → ∃ μ', (ord_tree_lt_tc μ' μ) ∧ Acc_ord_tree R y μ') → *)
  (*   Acc_ord_tree R x μ. *)

  Lemma Acc_ord_tree_mon {A} (R : relation A) x (μ1 μ2 : ord_tree A) :
    ord_tree_lt_tc μ1 μ2 →
    Acc_ord_tree R x μ1 →
    Acc_ord_tree R x μ2.
  Proof.
    intros LT AOT. inv AOT. econstructor.
    { etransitivity; [eapply H | eapply LT]. }
    auto.
  Qed.

  Lemma Acc_Acc_ord_tree {A} (R : relation A) x :
    Acc R x → ∃ μ, Acc_ord_tree R x μ.
  Proof.
    intros. induction H.
    eapply (ord_tree_join_tc) in H0.
    assert (∀ (z : A), (λ (a : A), True) z → ∃ o1, ∀ a, R a x → ∃ o0, Acc_ord_tree R a o0 ∧ ord_tree_lt_tc o0 o1).
    { intros. auto. }
    clear H0. eapply (ord_tree_join_tc) in H1. destruct H1 as (μ2& IH). specialize (IH x I).
    destruct IH as (μ1& IH& LTμ2).
    exists μ2. eapply (Acc_ord_tree_intro _ _ _ μ1).
    1: auto.
    intros y Hy. destruct (IH _ Hy) as (μ0& HA& LTμ1).
    apply (Acc_ord_tree_mon _ _ _ _ LTμ1 HA).
  Qed.

End classical_proofs.

(* Section definitions. *)
(*   Context `(R : relation A). *)

(*   Inductive all_eventually (x : A) (P : A -> Prop) : Prop := *)
(*   | all_eventually_done : *)
(*     (P x) -> all_eventually x P *)
(*   | all_eventually_do_step : *)
(*     (exists x', R x x') -> (forall y, R x y -> all_eventually y P) -> all_eventually x P. *)

(*   CoInductive ex_always_not (x : A) (P : A -> Prop) : Prop := *)
(*   | ex_always_not_done : *)
(*     (forall x', ¬ R x x') -> (¬ P x) -> ex_always_not x P *)
(*   | ex_always_not_do_step y : *)
(*     (¬ P x) -> R x y -> ex_always_not y P -> ex_always_not x P. *)

(* End definitions. *)

(* Lemma nat_lt_all_eventually_zero : forall (n : nat), all_eventually (flip lt) n (fun x => x = 0). *)
(* Proof. *)
(*   intros n. assert (forall m, m <= n -> all_eventually (flip lt) m (fun x => x = 0)); [|eauto]. *)
(*   induction n; simpl; intros. *)
(*   - constructor 1. lia. *)
(*   - destruct m. *)
(*     + constructor 1. auto. *)
(*     + constructor 2; simpl; [exists m; eauto|]. intros. apply IHn. lia. *)
(* Qed. *)

(* Lemma nat_gt_ex_always_not_zero : forall (n : nat), n > 0 -> ex_always_not (flip gt) n (fun x => x = 0). *)
(* Proof. *)
(*   cofix IH; intros. eapply (ex_always_not_do_step _ _ _ (S n)). *)
(*   - lia. *)
(*   - simpl. lia. *)
(*   - eauto. *)
(* Qed. *)

(* (* Section proofs. *) *)

(* (*   Lemma ex_always_not_ex_loop {A} (R : relation A) x P : *) *)
(* (*     ex_always_not R x P -> ex_loop R x. *) *)
(* (*   Proof. *) *)
(* (*     revert x. cofix IH; intros x Hex. destruct Hex. econstructor; eauto. *) *)
(* (*   Qed. *) *)

(* (* End proofs. *) *)

(* Section classical_proofs. *)

(*   Lemma not_all_eventually_ex_always_not {A} (R : relation A) x (P : A -> Prop) : *)
(*     ¬ all_eventually R x P -> ex_always_not R x P. *)
(*   Proof. *)
(*     intros Hsn. revert x Hsn. cofix IH; intros x Hsn. *)
(*     destruct (classic (exists y, R x y /\ ¬ all_eventually R y P)) as [(y&?&?)|Hnot]. *)
(*     - econstructor 2; eauto. intro HP. destruct Hsn. constructor 1. auto. *)
(*     - destruct (classic (exists x', R x x')) as [[x' Hnext] | Hnotnext]. *)
(*       + destruct Hsn. constructor 2; [eauto |]. intros y Hxy. *)
(*         destruct (classic (all_eventually R y P)). auto. naive_solver. *)
(*       + constructor 1; [naive_solver|]. intros Hp. destruct Hsn. constructor 1. auto. *)
(*   Qed. *)

(*   Lemma ex_always_not_not_all_eventually {A} (R : relation A) x (P : A -> Prop) : *)
(*     ex_always_not R x P -> ¬ all_eventually R x P. *)
(*   Proof. *)
(*     intros Hex Hsn. revert Hex. induction Hsn; intros. *)
(*     - inv Hex; auto. *)
(*     - destruct H as [x' Hxx']. inv Hex. *)
(*       + naive_solver. *)
(*       + eauto. *)
(*   Qed. *)

(* End classical_proofs. *)
