(** Facts about the ordinals of the [Ordinal] library ([Ord.t]) with Hessenberg addition, and the
    class [ord_mono_fun_class] of inflationary monotone functions on ordinals. *)

From stdpp Require Import base.
From Ordinal Require Export Ordinal Hessenberg ClassicalHessenberg.

Class ord_mono_fun_class := {
    η : Ord.t → Ord.t;
    η_mono : ∀ o, (o <= η o)%ord;
    #[global] η_lt_proper :: Proper (Ord.lt ==> Ord.lt) η;
    #[global] η_le_proper :: Proper (Ord.le ==> Ord.le) η;
  }.

Section ord_facts.

  Import Hessenberg.

  Lemma omega_lt_one : (Ord.S Ord.O < ω)%ord.
  Proof.
    rewrite <- Ord.from_nat_O. rewrite <- Ord.from_nat_S. apply Ord.omega_upperbound.
  Qed.

  Lemma omega_lt_zero : (Ord.O < ω)%ord.
  Proof. etransitivity; [|eapply omega_lt_one]. apply Ord.S_lt. Qed.

  Lemma ord_lt_exists_left : forall a c, (exists b, (Ord.O < b)%ord /\ ((a ⊕ b) <= c)%ord) <-> (a < c)%ord.
  Proof.
    intros a c. split; intros.
    { destruct H as (b&LT&LE). eapply Ord.lt_le_lt; [|eauto]. apply Hessenberg.add_lt_l. auto. }
    { exists Ord.one. split; [apply Ord.S_lt |].
      unfold Ord.one. rewrite Hessenberg.add_S_r. apply Ord.S_supremum.
      rewrite Hessenberg.add_O_r. auto.
    }
  Qed.

  Lemma ord_lt_one (o0 o1 : Ord.t) :
    (o0 < o1)%ord -> ((o0 ⊕ (Ord.S Ord.O)) <= o1)%ord.
  Proof.
    intros H. apply ord_lt_exists_left in H. destruct H as (b&H0&H1).
    etransitivity; [|eauto]. apply Hessenberg.le_add_r.
    apply Ord.S_supremum. auto.
  Qed.

  Lemma ord_S_add :
    forall o, (Ord.S o == ((Ord.S Ord.O) ⊕ o))%ord.
  Proof.
    intros. rewrite add_S_l, add_O_l. reflexivity.
  Qed.

End ord_facts.
