From iris.proofmode Require Import base proofmode classes.
From iris.bi Require Export fixpoint.
From iris.prelude Require Import options.
From liris.base_logic Require Export gupd.
(* From transfinite.base_logic.lib Require Import ghost_map. *)

(* Defined by the programming language. *)
Class tf_atomic_class `{SI : indexT} (Σ : gFunctors) :=
  { tfa_state : Type;
    tfa_state_interp : tfa_state → iProp Σ;
  }.

(** Simple syntax for writing temporal formulae; cf., LTL, CTL*. *)
Inductive tf `{SI : indexT} `{Σ : gFunctors} `{@tf_atomic_class SI Σ} :=
| tf_emp
| tf_atomic (s : tfa_state)
| tf_pure (p : Prop)
| tf_ghost (p : iProp Σ)
| tf_and (P Q : tf)
| tf_or (P Q : tf)
| tf_impl (P Q : tf)
| tf_forall (A : Type) (P : A → tf)
| tf_exist (A : Type) (P : A → tf)
| tf_sep (P Q : tf)
| tf_wand (P Q : tf)
| tf_variant (N : namespace) (k : gl_id) (v : ghost_lock_version) (P Q R : tf).

Global Arguments tf {SI Σ _}.

(** Interpretation. *)
Fixpoint tf_interp `{SI : indexT} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ} (Φ : tf) : iProp Σ :=
  match Φ with
  | tf_emp => emp%I
  | tf_atomic s => tfa_state_interp s
  | tf_pure p => (⌜p⌝)%I
  | tf_ghost p => p
  | tf_and P Q => (tf_interp P ∧ tf_interp Q)%I
  | tf_or P Q => (tf_interp P ∨ tf_interp Q)%I
  | tf_impl P Q => (tf_interp P → tf_interp Q)%I
  | tf_forall A P => (∀ (a : A), tf_interp (P a))%I
  | tf_exist A P => (∃ (a : A), tf_interp (P a))%I
  | tf_sep P Q => (tf_interp P ∗ tf_interp Q)%I
  | tf_wand P Q => (tf_interp P -∗ tf_interp Q)%I
  | tf_variant N k v P Q R => gl_variant N k v (tf_interp P) (tf_interp Q) (tf_interp R)
  end.

Global Arguments tf_interp {SI Σ _ _}.

(** Notations *)

Declare Scope tf_scope.
Delimit Scope tf_scope with TeF.
Bind Scope tf_scope with tf.

(* Local Open Scope tf_scope. *)

Notation "'⌜' p '⌝'" := (tf_pure p) : tf_scope.
Notation "'⟨' p '⟩'" := (tf_ghost p%I) : tf_scope.
Infix "∧" := (tf_and) : tf_scope.
Infix "∨" := (tf_or) : tf_scope.
Infix "→" := (tf_impl) : tf_scope.
Notation f_forall A := (tf_forall A).
Notation "∀'" := (f_forall _) (only parsing) : tf_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%TeF)) ..)) : tf_scope.
Notation f_exist A := (tf_exist A).
Notation "∃'" := (f_exist _) (only parsing) : tf_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%TeF)) ..)) : tf_scope.
Infix "∗" := (tf_sep) : tf_scope.
Infix "-∗" := (tf_wand) : tf_scope.

(* Notation "'⟨' A '⟩'" := (Syntax.atom A) : tf_scope. *)
(* Notation "'➢' r" := (Syntax.ownM r) (at level 20) : tf_scope. *)
(* Notation "⤉ P" := (Syntax.lift P) (at level 20) : tf_scope. *)

(* Notation "'<pers>' P" := (Syntax.persistently P) : tf_scope. *)
(* Notation "'<affine>' P" := (Syntax.affinely P) : tf_scope. *)
(* Notation "□ P" := (<affine> <pers> P) : tf_scope. *)
(* Notation "■ P" := (Syntax.plainly P) : tf_scope. *)
(* Notation "|==> P" := (Syntax.upd P) : tf_scope. *)
(* Notation "¬ P" := (P → False) : tf_scope. *)
(* Notation "P ==∗ Q" := (P -∗ |==> Q) : tf_scope. *)
(* Notation "'emp'" := (Syntax.empty) : tf_scope. *)

Notation "'⟦' Φ '⟧'" := (tf_interp Φ%TeF).

Section reduction.
  Context `{SI : indexT} `{tf_atomic_class Σ} `{!gupdGS Σ}.

  Lemma tf_emp_interp :
    ⟦tf_emp⟧ = emp%I.
  Proof. done. Qed.
  Lemma tf_atomic_interp s :
    ⟦tf_atomic s⟧ = tfa_state_interp s.
  Proof. done. Qed.
  Lemma tf_pure_interp P :
    ⟦⌜P⌝⟧ = (⌜P⌝)%I.
  Proof. done. Qed.
  Lemma tf_ghost_interp P :
    ⟦⟨P⟩⟧ = (P)%I.
  Proof. done. Qed.
  Lemma tf_and_interp P Q :
    ⟦P ∧ Q⟧ = (⟦P⟧ ∧ ⟦Q⟧)%I.
  Proof. done. Qed.
  Lemma tf_or_interp P Q :
    ⟦P ∨ Q⟧ = (⟦P⟧ ∨ ⟦Q⟧)%I.
  Proof. done. Qed.
  Lemma tf_impl_interp P Q :
    ⟦P → Q⟧ = (⟦P⟧ → ⟦Q⟧)%I.
  Proof. done. Qed.
  Lemma tf_forall_interp A (P : A → tf) :
    ⟦∀ a, P a⟧ = (∀ a, ⟦P a⟧)%I.
  Proof. done. Qed.
  Lemma tf_exist_interp A (P : A → tf) :
    ⟦∃ a, P a⟧ = (∃ a, ⟦P a⟧)%I.
  Proof. done. Qed.
  Lemma tf_sep_interp P Q :
    ⟦P ∗ Q⟧ = (⟦P⟧ ∗ ⟦Q⟧)%I.
  Proof. done. Qed.
  Lemma tf_wand_interp P Q :
    ⟦P -∗ Q⟧ = (⟦P⟧ -∗ ⟦Q⟧)%I.
  Proof. done. Qed.
  Lemma tf_variant_interp N k v P Q R :
    ⟦tf_variant N k v P Q R⟧ = (gl_variant N k v ⟦P⟧ ⟦Q⟧ ⟦R⟧)%I.
  Proof. done. Qed.

End reduction.
(* Making this opaque is reasonable only if we have a better reduction tactic than simpl. *)
(* Global Opaque tf_interp. *)

Section aux.
  Context `{SI : indexT}.

  Global Instance big_opL_proper_eq {M : ofe} (o : M → M → M) `{!Monoid o} {A : Type} :
    Proper (pointwise_relation nat (pointwise_relation A eq) ==> eq ==> eq) (big_opL o).
  Proof.
    repeat intro. subst y0. revert x y H. rename x0 into l. induction l; intros f1 f2 Hf; simpl; auto.
    f_equal.
    - rewrite Hf. auto.
    - eapply IHl. repeat intro. rewrite Hf. auto.
  Qed.

End aux.

(** Ofe and Monoid structure. *)
Global Instance tf_equiv `{SI : indexT} `{tf_atomic_class Σ} `{!gupdGS Σ} : Equiv tf :=
  λ Φ1 Φ2, ⟦Φ1⟧ ≡ ⟦Φ2⟧.
Global Instance tf_equiv_Equivalence `{SI : indexT} `{tf_atomic_class Σ} `{!gupdGS Σ} : Equivalence tf_equiv.
Proof.
  unfold tf_equiv. econstructor.
  - repeat intro. done.
  - repeat intro. rewrite H0. done.
  - repeat intro. etrans; eauto.
Qed.
Canonical Structure tfO `{SI : indexT} `{tf_atomic_class Σ} `{!gupdGS Σ} : ofe :=
  (Ofe tf (discrete_ofe_mixin tf_equiv_Equivalence)).

Class tf_op_interp_comm `{SI : indexT} {Σ : gFunctors} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ}
  (tf_o : tf → tf → tf) (iProp_o : iProp Σ → iProp Σ → iProp Σ) :=
  tf_op_interp_comm_intro : ∀ (P Q : tf), ⟦tf_o P Q⟧ = (iProp_o ⟦P⟧ ⟦Q⟧)%I.

Class tf_monoid_unit_interp_eq `{SI : indexT} {Σ : gFunctors} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ}
  (tf_o : tf → tf → tf) `{!Monoid tf_o} (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o} :=
  tf_monoid_unit_interp_eq_intro : ⟦ monoid_unit ⟧ = monoid_unit.

Section instances.
  Context `{SI : indexT} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ}.

  Global Instance tf_and_interp_comm : tf_op_interp_comm tf_and bi_and.
  Proof. econstructor. Qed.
  Global Instance tf_or_interp_comm : tf_op_interp_comm tf_or bi_or.
  Proof. econstructor. Qed.
  Global Instance tf_impl_interp_comm : tf_op_interp_comm tf_impl bi_impl.
  Proof. econstructor. Qed.
  Global Instance tf_sep_interp_comm : tf_op_interp_comm tf_sep bi_sep.
  Proof. econstructor. Qed.
  Global Instance tf_wand_interp_comm : tf_op_interp_comm tf_wand bi_wand.
  Proof. econstructor. Qed.

  Program Global Instance tf_and_monoid : Monoid tf_and := Build_Monoid _ _ _ tf_emp _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H1, H2. rewrite !tf_and_interp H1 H2. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp tf_emp_interp left_id. done. Qed.

  Program Global Instance tf_or_monoid : Monoid tf_or := Build_Monoid _ _ _ (⌜ False ⌝)%TeF _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H1, H2. rewrite !tf_or_interp H1 H2. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp tf_pure_interp left_id. done. Qed.

  Program Global Instance tf_sep_monoid : Monoid tf_sep := Build_Monoid _ _ _ tf_emp _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H1, H2. rewrite !tf_sep_interp H1 H2. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp tf_emp_interp left_id. done. Qed.

  Global Instance tf_and_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_and bi_and.
  Proof. econstructor. Qed.
  Global Instance tf_or_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_or bi_or.
  Proof. econstructor. Qed.
  Global Instance tf_sep_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_sep bi_sep.
  Proof. econstructor. Qed.

End instances.

Section big_op.
  Context `{SI : indexT} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ}.

  Lemma tf_big_opL_interp
    (tf_o : tf → tf → tf) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    A (P : nat → A → tf) (l : list A) :
    ⟦[^tf_o list] n ↦ a ∈ l, P n a⟧ = ([^iProp_o list] n ↦ a ∈ l, (⟦P n a⟧))%I.
  Proof.
    cut (∀ m, ⟦[^tf_o list] n ↦ a ∈ l, P (m + n) a⟧ = ([^iProp_o list] n ↦ a ∈ l, (⟦P (m + n) a⟧))%I).
    { intros. specialize (H1 0). simpl in H1. auto. }
    induction l; intros; simpl; auto.
    rewrite (tf_op_interp_comm0). f_equal.
    erewrite (big_opL_proper_eq tf_o).
    - erewrite (IHl (S m)). apply big_opL_proper_eq; auto.
      repeat intro. replace (S m + a0) with (m + S a0) by lia. auto.
    - repeat intro. replace (S m + a0) with (m + S a0) by lia. auto.
    - auto.
  Qed.

  TODO

End big_op.

(** Defines some useful patterns which corresponds to temporal properties. *)
(* P Until Q *)
Local Definition tf_until_def `{SI : indexT} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ}
  (N : namespace) (k : gl_id) (P Q : tf) : tf :=
  (tf_variant N k 0 P Q ⌜ True ⌝)%TeF.
Local Definition tf_until_aux : seal (@tf_until_def). Proof. by eexists. Qed.
Definition tf_until := tf_until_aux.(unseal).
Local Definition tf_until_unseal :
  @tf_until = @tf_until_def := tf_until_aux.(seal_eq).
Global Arguments tf_until {SI Σ _ _}.

(* Always P *)
Local Definition tf_always_def `{SI : indexT} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ}
  (N : namespace) (P : tf) : tf :=
  (∃ k, ⟨gl_done k 0⟩ ∗ tf_until N k ⌜ False ⌝ P)%TeF.
Local Definition tf_always_aux : seal (@tf_always_def). Proof. by eexists. Qed.
Definition tf_always := tf_always_aux.(unseal).
Local Definition tf_always_unseal :
  @tf_always = @tf_always_def := tf_always_aux.(seal_eq).
Global Arguments tf_always {SI Σ _ _}.

(* Eventually P *)
Local Definition tf_eventually_def `{SI : indexT} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ}
  (N : namespace) (P : tf) : tf :=
  (∃ k, tf_until N k ⌜ True ⌝ P)%TeF.
Local Definition tf_eventually_aux : seal (@tf_eventually_def). Proof. by eexists. Qed.
Definition tf_eventually := tf_eventually_aux.(unseal).
Local Definition tf_eventually_unseal :
  @tf_eventually = @tf_eventually_def := tf_eventually_aux.(seal_eq).
Global Arguments tf_eventually {SI Σ _ _}.

(* P Weak until Q *)
Local Definition tf_weakuntil_def `{SI : indexT} `{@tf_atomic_class SI Σ} `{@gupdGS SI Σ}
  (N : namespace) (P Q : tf) : tf :=
  (∃ k v, ⟨gl_done k 0⟩ ∗ tf_variant N k v ⌜ False ⌝ P Q)%TeF.
Local Definition tf_weakuntil_aux : seal (@tf_weakuntil_def). Proof. by eexists. Qed.
Definition tf_weakuntil := tf_weakuntil_aux.(unseal).
Local Definition tf_weakuntil_unseal :
  @tf_weakuntil = @tf_weakuntil_def := tf_weakuntil_aux.(seal_eq).
Global Arguments tf_weakuntil {SI Σ _ _}.





Class testG `{SI : indexT} Σ :=
  TestG {
      #[local] test_gmG :: ghost_mapG Σ nat bool;
    }.

Definition testΣ `{SI : indexT} : gFunctors :=
  #[(ghost_mapΣ nat bool)].

Global Instance subG_testΣ `{SI : indexT} {Σ} : subG testΣ Σ → testG Σ.
Proof. solve_inG. Qed.

Section test.
  Context `{SI : indexT} `{tf_atomic_class Σ} `{!gupdGS Σ, !testG Σ}.

  Definition tf_always_test N γ n b : tf (Σ:=Σ) :=
    tf_always_def N (tf_ghost (ghost_map_elem γ n DfracDiscarded b)).

  Lemma test_forall :
    tf_interp (tf_forall (λ (P : iProp Σ), tf_ghost P)) = (∀ (P : iProp Σ), P)%I.
  Proof. simpl. auto. Qed.
  Lemma test_exist :
    tf_interp (tf_exist (λ (P : iProp Σ), tf_ghost P)) = (∃ (P : iProp Σ), P)%I.
  Proof. simpl. auto. Qed.

End test.




Local Definition tf_always_def `{SI : indexT} `{Σ : gFunctors}
  (N : namespace) (P : tf) : iProp Σ :=
  ∃ κ v, gl_done κ v ∗ gl_variant N κ v False P False.
Local Definition gl_always_aux : seal (@gl_always_def). Proof. by eexists. Qed.
Definition gl_always := gl_always_aux.(unseal).
Local Definition gl_always_unseal :
  @gl_always = @gl_always_def := gl_always_aux.(seal_eq).
Global Arguments gl_always {SI Σ _}.

Local Ltac unfold_gl_always :=
  try rewrite !gl_always_unseal /gl_always_def.

Section proof.
  Context `{SI : indexT} `{!gupdGS Σ}.

  Global Instance gl_always_persistent N P : Persistent (gl_always N P).
  Proof. unfold_gl_always. apply _. Qed.

  Lemma gl_always_alloc_0 E Θ N (P : iProp Σ) :
    (▷ P) -∗ |={E:Θ}=>g gl_always N P.
  Proof.
    unfold_gl_always.
    iIntros "HP". iMod (gl_alloc_done_0 _ _ (λ _, 0%ordi) 0%M N 0 False P False with "HP") as "(%& _& _& _& #Gd& _& #GV& _)".
    iModIntro. eauto.
  Qed.

  Lemma gl_always_acc E N P :
    ↑N ⊆ E →
    gl_always N P ={E,E ∖ ↑N}=∗ (▷ P) ∗ (▷ P ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_gl_always.
    iIntros (MASK) "(%&%& #Gd& #GV)". iMod (gl_variant_acc_done with "Gd GV") as "[H ACC]". 1: auto.
    iDestruct "H" as "[$ | H]".
    - iIntros "!> HP". iApply "ACC". iNext. iApply gl_variant_cases_unfold. iLeft; iRight. eauto.
    - iDestruct "H" as ">(_& %)". done.
  Qed.

End proof.



Local Definition heldT : Type := (bool).
Local Definition wonT : Type := (gl_id * bool).

Class ticket_lockG Σ :=
  TLockG {
      #[local] tlock_heldG :: ghost_mapG Σ Z heldT;
      #[local] tlock_wonG :: ghost_mapG Σ Z wonT;
    }.

Definition ticket_lockΣ : gFunctors :=
  #[(ghost_mapΣ Z heldT); (ghost_mapΣ Z wonT)].

Global Instance subG_ticket_lockΣ {Σ} : subG ticket_lockΣ Σ → ticket_lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !ticket_lockG Σ}.

End proof.
