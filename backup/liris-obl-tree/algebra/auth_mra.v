From iris.algebra Require Export auth.
From iris.algebra Require Import proofmode_classes mra updates.
From iris.prelude Require Import options.

Section mra_aux.

  Context `{SI : indexT} {A} {R : relation A}.
  Implicit Types a b : A.

  (* FIXME: what's wrong here? *)
  Lemma to_mra_op_included_R `{!PreOrder R} a b :
    to_mra (R:=R) a ⋅ to_mra b ≼ to_mra a → R b a.
  Proof.
    intros Hi. apply mra_included in Hi.
    assert (H0 : to_mra (R:=R) a ⋅ to_mra b ⋅ to_mra a ≡ to_mra b ⋅ to_mra a).
    { rewrite comm assoc mra_idemp. rewrite comm. auto. }
    Set Printing All.
    replace (@ofe_equiv _ (@mraO SI A R)) with (@mra_equiv A R) in H0 by done.
    replace (@cmra_op SI (@mraR SI A R)) with (@mra_op A R) in H0 by done.
    rewrite /ucmra_car /cmra_op in Hi. simpl in Hi.
    rewrite /ucmra_op in Hi. simpl in Hi.
    Unset Printing All.
    assert (Heq : to_mra (R:=R) a ≡ to_mra b ⋅ to_mra a).
    { etransitivity; [apply Hi | apply H0]. }
    apply mra_included in Heq. apply to_mra_included in Heq. auto.
  Qed.

End mra_aux.

Definition auth_mra `{SI : indexT} {A : Type} (R : relation A) := auth (mraUR R).
Definition auth_mraR `{SI : indexT} {A : Type} (R : relation A) := authR (mraUR R).
Definition auth_mraUR `{SI : indexT} {A : Type} (R : relation A) := authUR (mraUR R).

Definition auth_mra_auth `{SI : indexT} {A : Type} (R : relation A) (dq : dfrac) (a : A) : auth_mra R :=
  ●{dq} to_mra a ⋅ ◯ to_mra a.
Definition auth_mra_know `{SI : indexT} {A : Type} (R : relation A) (a : A) : auth_mra R :=
  ◯ to_mra a.

Notation "●AM dq [ R ] a" := (auth_mra_auth R dq a)
  (at level 20, dq custom dfrac at level 1, format "●AM dq [ R ]  a").
Notation "◯AM [ R ] a" := (auth_mra_know R a)
  (at level 20, format "◯AM [ R ]  a").

Section auth_mra.
  Context `{SI : indexT} {A : Type} (R : relation A).
  Implicit Types (a : A).

  Global Instance auth_mra_know_core_id a : CoreId (◯AM[R] a).
  Proof. apply _. Qed.
  Global Instance auth_mra_auth_core_id a : CoreId (●AM□[R] a).
  Proof. apply _. Qed.

  Lemma auth_mra_auth_dfrac_op dq1 dq2 a :
    ●AM{dq1 ⋅ dq2}[R] a ≡ ●AM{dq1}[R] a ⋅ ●AM{dq2}[R] a.
  Proof.
    rewrite /auth_mra_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma auth_mra_know_op `{!Transitive R} a1 a2 :
    R a1 a2 → ◯AM[R] a2 ≡ ◯AM[R] a1 ⋅ ◯AM[R] a2.
  Proof. intros. rewrite /auth_mra_know -auth_frag_op to_mra_R_op; auto. Qed.

  Lemma auth_mra_auth_know_op `{!PreOrder R} dq a :
    ●AM{dq}[R] a ≡ ●AM{dq}[R] a ⋅ ◯AM[R] a.
  Proof.
    rewrite /auth_mra_auth /auth_mra_know.
    rewrite -!assoc -auth_frag_op to_mra_R_op; done.
  Qed.

  Global Instance auth_mra_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 → IsOp' (●AM{dq}[R] a) (●AM{dq1}[R] a) (●AM{dq2}[R] a).
  Proof. rewrite /IsOp' /IsOp=> ->. rewrite auth_mra_auth_dfrac_op //. Qed.
  Global Instance auth_mra_know_R_is_op a a1 a2 :
    IsOp (to_mra (R:=R) a) (to_mra a1) (to_mra a2) → IsOp' (◯AM[R] a) (◯AM[R] a1) (◯AM[R] a2).
  Proof. rewrite /IsOp' /IsOp /auth_mra_know=> -> //. Qed.

  (** rephrasing of [auth_mra_know_op] useful for weakening a fragment to a previous knowledge *)
  Lemma auth_mra_know_op_R_l `{!Transitive R} a a' :
    R a' a →
    ◯AM[R] a ≡ ◯AM[R] a' ⋅ ◯AM[R] a.
  Proof. intros. rewrite -auth_mra_know_op //. Qed.

  Lemma auth_mra_auth_dfrac_valid dq a : (✓ ●AM{dq}[R] a) ↔ ✓ dq.
  Proof.
    rewrite /auth_mra_auth auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma auth_mra_auth_valid a : ✓ ●AM[R] a.
  Proof. by apply auth_both_valid. Qed.

  Lemma auth_mra_auth_dfrac_op_valid
    `{Equiv A} `{!Reflexive (≡@{A})}
    `{!Reflexive R} `{!AntiSymm (≡) R} `{!Proper ((≡) ==> (≡) ==> iff) R}
    dq1 dq2 a1 a2 :
    ✓ (●AM{dq1}[R] a1 ⋅ ●AM{dq2}[R] a2) ↔ ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2.
  Proof.
    rewrite /auth_mra_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid.
      intros (H0&H1&H2). apply (inj to_mra) in H1. auto.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      by apply auth_both_dfrac_valid_discrete.
  Qed.
  Lemma auth_mra_auth_op_valid
    `{Equiv A} `{!Reflexive (≡@{A})}
    `{!Reflexive R} `{!AntiSymm (≡) R} `{!Proper ((≡) ==> (≡) ==> iff) R}
    a1 a2 :
    ✓ (●AM[R] a1 ⋅ ●AM[R] a2) ↔ False.
  Proof. rewrite auth_mra_auth_dfrac_op_valid. naive_solver. Qed.

  Lemma auth_mra_both_dfrac_valid `{!PreOrder R} dq a b :
    ✓ (●AM{dq}[R] a ⋅ ◯AM[R] b) ↔ ✓ dq ∧ R b a.
  Proof.
    rewrite /auth_mra_auth /auth_mra_know -assoc -auth_frag_op.
    rewrite auth_both_dfrac_valid_discrete. split; intros.
    - destruct H as (?&Hi&_). split; first auto.
      apply to_mra_op_included_R in Hi. auto.
    - destruct H as [Hq HR]. split; first auto. split; [|done].
      apply to_mra_R_op in HR. rewrite comm HR. done.
  Qed.
  Lemma auth_mra_both_valid `{!PreOrder R} a b :
    ✓ (●AM[R] a ⋅ ◯AM[R] b) ↔ R b a.
  Proof. rewrite auth_mra_both_dfrac_valid dfrac_valid_own. naive_solver. Qed.

  Lemma auth_mra_know_mono `{!PreOrder R} a1 a2 : R a1 a2 → ◯AM[R] a1 ≼ ◯AM[R] a2.
  Proof. intros. by apply auth_frag_mono, to_mra_included. Qed.

  Lemma auth_mra_included dq a : ◯AM[R] a ≼ ●AM{dq}[R] a.
  Proof. apply cmra_included_r. Qed.

  Lemma auth_mra_update `{!Transitive R} {a} a' :
    R a a' → ●AM[R] a ~~> ●AM[R] a'.
  Proof.
    intros. rewrite /auth_mra_auth /auth_mra_know.
    by apply auth_update, mra_local_update_grow.
  Qed.

  Lemma auth_mra_auth_persist a dq :
    ●AM{dq}[R] a ~~> ●AM□[R] a.
  Proof.
    rewrite /auth_mra_auth /auth_mra_know.
    eapply cmra_update_op_proper; last done.
    eapply auth_update_auth_persist.
  Qed.
  Lemma auth_mra_auth_unpersist a :
    ●AM□[R] a ~~>: λ k, ∃ q, k = ●AM{#q}[R] a.
  Proof. eapply auth_updateP_both_unpersist. Qed.
End auth_mra.

Global Typeclasses Opaque auth_mra_auth auth_mra_know.

(* Properties needed to use the full set of rules *)
Class auth_mra_class (A : Type) := {
    auth_mra_R : A → A → Prop;
    #[global] auth_mra_R_PreOrder :: PreOrder auth_mra_R;
    #[global] auth_mra_equiv :: Equiv A;
    #[global] auth_mra_equiv_Reflexive :: Reflexive (≡@{A});
    #[global] auth_mra_AntiSymm :: AntiSymm (≡@{A}) auth_mra_R;
    #[global] auth_mra_Proper :: Proper (((≡@{A}) ==> (≡@{A}) ==> iff)) auth_mra_R;
  }.

Class auth_mra_eq_class (A : Type) := {
    auth_mra_eq_R : A → A → Prop;
    #[global] auth_mra_eq_R_PreOrder :: PreOrder auth_mra_eq_R;
    #[global] auth_mra_eq_AntiSymm :: AntiSymm (=@{A}) auth_mra_eq_R;
    #[global] auth_mra_eq_Proper :: Proper (((=@{A}) ==> (=@{A}) ==> iff)) auth_mra_eq_R;
  }.

Global Instance auth_mra_eq_instance `{AMEC : auth_mra_eq_class A} : auth_mra_class A.
Proof. destruct AMEC. econstructor; eauto. Qed.
