From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import iprop.
From stdpp Require Import namespaces.
From liris.base_logic Require Import obligation.
From liris.program_logic Require Export weakestpre.

(** Syntax for writing temporal formulae; cf., LTL, CTL*. *)
Inductive tf `{SI : indexT} {Π : Type} `{Σ : gFunctors} :=
| tf_emp
| tf_atomic (π : Π)
| tf_pure (p : Prop)
| tf_ghost (p : iProp Σ)
| tf_and (P Q : tf)
| tf_or (P Q : tf)
(** For impl and wnad, we only allow pure Prop in the left side.
    This makes the wand just an impl, so we omit the wand. *)
| tf_impl (P : Prop) (Q : tf)
(* | tf_wand (P : Prop) (Q : tf) *)
| tf_forall (A : Type) (P : A → tf)
| tf_exist (A : Type) (P : A → tf)
| tf_sep (P Q : tf)
| tf_always (N : namespace) (P : tf)
(** P until Q, using namespace N and oid k. *)
| tf_until (N : namespace) (k : oid) (b : bool) (q : Qp) (P Q : tf)
.

Global Arguments tf : clear implicits.
Global Arguments tf {SI Π}.

(** Notations *)

Declare Scope tf_scope.
Delimit Scope tf_scope with F.
Bind Scope tf_scope with tf.

Notation "➢ π" := (tf_atomic π) (at level 50, π at level 1) : tf_scope.
Notation "'⌜' p '⌝'" := (tf_pure p) : tf_scope.
Notation "'⟨' p '⟩'" := (tf_ghost p%I) : tf_scope.
Infix "∧" := (tf_and) : tf_scope.
Infix "∨" := (tf_or) : tf_scope.
Infix "→" := (tf_impl) : tf_scope.
Notation f_forall A := (tf_forall A).
Notation "∀'" := (f_forall _) (only parsing) : tf_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%F)) ..)) : tf_scope.
Notation f_exist A := (tf_exist A).
Notation "∃'" := (f_exist _) (only parsing) : tf_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%F)) ..)) : tf_scope.
Infix "∗" := (tf_sep) : tf_scope.
(* Infix "-∗" := (tf_wand) : tf_scope. *)
(* Notation "□ P" := (tf_pers P%F) : tf_scope. *)

(** Define patterns corresponding to LTL temporal properties. *)
(* Eventually P *)
Definition tf_eventually `{SI : indexT} {Π} {Σ} N k b q (P : @tf SI Π Σ) : tf Σ :=
  (tf_until N k b q ⌜ True ⌝ P)%F.
Global Arguments tf_eventually {SI Π Σ}.

(* P Weak until Q *)
Definition tf_weakuntil `{SI : indexT} {Π} {Σ} N k b q (P Q : @tf SI Π Σ) : tf Σ :=
  (tf_until N k b q P (Q ∨ tf_always N P))%F.
(*   (tf_variant N k v ⌜ False ⌝ P (tf_until N k (v + 1) P Q))%F. *)
Global Arguments tf_weakuntil {SI Π Σ}.

(* P Release Q *)
Definition tf_release `{SI : indexT} {Π} {Σ} N k b q (P Q : @tf SI Π Σ) : tf Σ :=
  (tf_weakuntil N k b q Q (Q ∗ P))%F.
Global Arguments tf_release {SI Π Σ}.

(* P Strong release Q *)
Definition tf_strongrelease `{SI : indexT} {Π} {Σ} N k b q (P Q : @tf SI Π Σ) : tf Σ :=
  (tf_until N k b q Q (Q ∗ P))%F.
Global Arguments tf_strongrelease {SI Π Σ}.

(* FIXME: more to somewhere else. *)
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

Fixpoint tf_logic `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (Φ : @tf SI (state_pred Λ) Σ) : iProp Σ :=
  match Φ with
  | tf_emp => emp%I
  | tf_atomic π => (state_pred_interp π)%I
  | tf_pure p => (⌜p⌝)%I
  | tf_ghost p => p%I
  | tf_and P Q => (tf_logic P ∧ tf_logic Q)%I
  | tf_or P Q => (tf_logic P ∨ tf_logic Q)%I
  | tf_impl P Q => (⌜P⌝ → tf_logic Q)%I
  | tf_forall A P => (∀ (a : A), tf_logic (P a))%I
  | tf_exist A P => (∃ (a : A), tf_logic (P a))%I
  | tf_sep P Q => (tf_logic P ∗ tf_logic Q)%I
  (* | tf_wand P Q => (⌜P⌝ -∗ tf_logic Q)%I *)
  | tf_always N P => (inv N (tf_logic P))%I
  | tf_until N k b q P Q =>
      (oblP_assigned k b (q/2)%Qp ∗
       oblP_inv N k (tf_logic P)%I (tf_logic Q)%I
         (∃ n' σ' Θ' κs' i' Ω', event_obl i' (n', Ω') k obl_fulfilled ∗
                                hG_event n' (σ', Θ', κs') ∗
                                tf_intuit n' σ' Θ' κs' i' Ω' Q)%I)%I
  end
with tf_intuit `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
       n σ Θ κs i Ω (Φ : @tf SI (state_pred Λ) Σ) : iProp Σ :=
       match Φ with
       | tf_emp => emp%I
       | tf_atomic π => (event_pred n σ Θ κs π)%I
       | tf_pure p => (⌜p⌝)%I
       | tf_ghost p => True%I
       | tf_and P Q => (tf_intuit n σ Θ κs i Ω P ∧ tf_intuit n σ Θ κs i Ω Q)%I
       | tf_or P Q => (tf_intuit n σ Θ κs i Ω P ∨ tf_intuit n σ Θ κs i Ω Q)%I
       | tf_impl P Q => (⌜P⌝ → tf_intuit n σ Θ κs i Ω Q)%I
       | tf_forall A P => (∀ (a : A), tf_intuit n σ Θ κs i Ω (P a))%I
       | tf_exist A P => (∃ (a : A), tf_intuit n σ Θ κs i Ω (P a))%I
       | tf_sep P Q => (tf_intuit n σ Θ κs i Ω P ∗ tf_intuit n σ Θ κs i Ω Q)%I
       (* | tf_wand P Q => (⌜P⌝ -∗ tf_intuit n σ Θ κs i Ω Q)%I *)
       | tf_always N P => (inv N (tf_logic P))%I
       | tf_until N k b q P Q =>
           ((∃ f o, event_obl i (n, Ω) k (obl_assigned f o)) ∗
            oblP_inv N k (tf_logic P)%I (tf_logic Q)
              (∃ n' σ' Θ' κs' i' Ω', event_obl i' (n', Ω') k obl_fulfilled ∗
                                     hG_event n' (σ', Θ', κs') ∗
                                     tf_intuit n' σ' Θ' κs' i' Ω' Q)%I)
       end.

Global Arguments tf_logic {SI Λ Σ _ _}.
Global Arguments tf_intuit {SI Λ Σ _ _}.

Local Definition tf_fulfilled_def `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  k (Q : tf Σ) : iProp Σ :=
  (∃ n' σ' Θ' κs' i' Ω', event_obl i' (n', Ω') k obl_fulfilled ∗
                         hG_event n' (σ', Θ', κs') ∗
                         tf_intuit n' σ' Θ' κs' i' Ω' Q)%I.
Local Definition tf_fulfilled_aux : seal (@tf_fulfilled_def). Proof. by eexists. Qed.
Definition tf_fulfilled := tf_fulfilled_aux.(unseal).
Global Arguments tf_fulfilled {SI Λ Σ _ _}.
Local Lemma tf_fulfilled_unseal `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} :
  tf_fulfilled = @tf_fulfilled_def SI Λ Σ _ _.
Proof. rewrite -tf_fulfilled_aux.(seal_eq) //. Qed.

Section proof.
  Context `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Global Instance tf_atomic_timeless π : Timeless (state_pred_interp π) → Timeless (tf_logic (tf_atomic π)).
  Proof. intros. simpl. auto. Qed.

  Global Instance tf_intuit_persistent n σ Θ κs i Ω Φ : Persistent (tf_intuit n σ Θ κs i Ω Φ).
  Proof.
    induction Φ; simpl; apply _.
  Qed.

  Global Instance tf_fulfilled_persistent k Q : Persistent (tf_fulfilled k Q).
  Proof. rewrite tf_fulfilled_unseal /tf_fulfilled_def. apply _. Qed.

  Lemma tf_fulfilled_unfold k Q :
    tf_fulfilled k Q = (∃ n' σ' Θ' κs' i' Ω', event_obl i' (n', Ω') k obl_fulfilled ∗ hG_event n' (σ', Θ', κs') ∗ tf_intuit n' σ' Θ' κs' i' Ω' Q)%I.
  Proof. rewrite tf_fulfilled_unseal /tf_fulfilled_def. done. Qed.

  Lemma tf_logic_tf_intuit Φ h n σ Θ κs m i Ω W :
    (history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ tf_logic Φ)
    ⊢ tf_intuit n σ Θ κs i Ω Φ.
  Proof.
    revert h n σ Θ κs m i Ω W. induction Φ; iIntros (?????????) "(HI& MI& TL)"; simpl; auto.
    - rewrite /history_interp. iDestruct "HI" as "(HI1& HI2& SI)".
      iPoseProof (state_interp_wf with "[$SI $TL]") as "%".
      iApply (history_interp_event_pred_now with "[HI1 HI2 SI]"). 1: auto.
      rewrite /history_interp. iFrame.
    - iSplit.
      + iDestruct "TL" as "[TL _]". iApply IHΦ1. iFrame.
      + iDestruct "TL" as "[_ TL]". iApply IHΦ2. iFrame.
    - iDestruct "TL" as "[TL | TL]".
      + iLeft. iApply IHΦ1. iFrame.
      + iRight. iApply IHΦ2. iFrame.
    - iIntros (?). iPoseProof ("TL" with "[//]") as "TL". iApply IHΦ. iFrame.
    - iIntros (?). iPoseProof ("TL" $! a) as "TL". iApply H. iFrame.
    - iDestruct "TL" as "(%& TL)". iExists a. iApply H. iFrame.
    - iDestruct "TL" as "[TL1 TL2]".
      iPoseProof (IHΦ1 with "[$HI $MI $TL1]") as "#TI1". iPoseProof (IHΦ2 with "[$HI $MI $TL2]") as "#TI2".
      eauto.
    - iDestruct "TL" as "[OA #TL]". iFrame "TL". iDestruct "MI" as "(MI& S& MI2)".
      iEval (unfold_opreds) in "OA". iDestruct "OA" as "(#OE& OA)".
      iPoseProof (osat_lookup_assigned with "[$S $OE $OA]") as "%". destruct H as (?&?&?).
      iPoseProof (model_history_interp_event_obl_now with "MI") as "#ME". 1: eauto. eauto.
  Qed.

End proof.

(** Notations *)
Notation "'⟦' Φ '⟧ₗ'" := (tf_logic Φ%F) (format "'⟦' Φ '⟧ₗ'").

Section reduction.
  Context `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma tf_emp_logic :
    ⟦tf_emp⟧ₗ = emp%I.
  Proof. done. Qed.
  Lemma tf_atomic_logic π :
    ⟦tf_atomic π⟧ₗ = state_pred_interp π.
  Proof. done. Qed.
  Lemma tf_pure_logic P :
    ⟦⌜P⌝⟧ₗ = (⌜P⌝)%I.
  Proof. done. Qed.
  Lemma tf_ghost_logic P :
    ⟦⟨P⟩⟧ₗ = (P)%I.
  Proof. done. Qed.
  Lemma tf_and_logic P Q :
    ⟦P ∧ Q⟧ₗ = (⟦P⟧ₗ ∧ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_or_logic P Q :
    ⟦P ∨ Q⟧ₗ = (⟦P⟧ₗ ∨ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_impl_logic P Q :
    ⟦P → Q⟧ₗ = (⌜P⌝ → ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_forall_logic A (P : A → tf Σ) :
    ⟦∀ a, P a⟧ₗ = (∀ a, ⟦P a⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_exist_logic A (P : A → tf Σ) :
    ⟦∃ a, P a⟧ₗ = (∃ a, ⟦P a⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_sep_logic P Q :
    ⟦P ∗ Q⟧ₗ = (⟦P⟧ₗ ∗ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  (* Lemma tf_wand_logic P Q : *)
  (*   ⟦P -∗ Q⟧ₗ = (⟦P⟧ₗ -∗ ⟦Q⟧ₗ)%I. *)
  (* Proof. done. Qed. *)
  (* Lemma tf_pers_logic P : *)
  (*   ⟦□ P⟧ₗ = (□ ⟦P⟧ₗ)%I. *)
  (* Proof. done. Qed. *)
  Lemma tf_always_logic N P :
    ⟦tf_always N P⟧ₗ = (inv N ⟦P⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_until_logic N k b q P Q :
    ⟦tf_until N k b q P Q⟧ₗ = (oblP_assigned k b (q/2)%Qp ∗ oblP_inv N k (⟦P⟧ₗ) (⟦Q⟧ₗ) (tf_fulfilled k Q))%I.
  Proof. rewrite tf_fulfilled_unfold. done. Qed.

End reduction.

Ltac tf_red :=
  (try rewrite !tf_and_logic;
   try rewrite !tf_or_logic;
   try rewrite !tf_impl_logic;
   try rewrite !tf_forall_logic;
   try rewrite !tf_exist_logic;
   try rewrite !tf_sep_logic;
   try rewrite !tf_pure_logic;
   try rewrite !tf_ghost_logic;
   try rewrite !tf_always_logic
  ).

(* Making this opaque is reasonable only if we have a better reduction tactic than simpl. *)
Global Opaque tf_logic tf_intuit.

(** Ofe and Monoid structure. *)
Global Instance tf_equiv `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : Equiv (tf Σ) :=
  λ Φ1 Φ2, ⟦Φ1⟧ₗ ≡ ⟦Φ2⟧ₗ.
Global Instance tf_equiv_Equivalence `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : Equivalence tf_equiv.
Proof.
  unfold tf_equiv. econstructor.
  - repeat intro. done.
  - repeat intro. rewrite H. done.
  - repeat intro. etrans; eauto.
Qed.
Canonical Structure tfO `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : ofe :=
  (Ofe (tf Σ) (discrete_ofe_mixin tf_equiv_Equivalence)).

Class tf_op_interp_comm `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (tf_o : tf Σ → tf Σ → tf Σ) (iProp_o : iProp Σ → iProp Σ → iProp Σ) :=
  tf_op_interp_comm_intro : ∀ (P Q : tf Σ), ⟦tf_o P Q⟧ₗ = (iProp_o ⟦P⟧ₗ ⟦Q⟧ₗ)%I.

Class tf_monoid_unit_interp_eq `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (tf_o : tf Σ → tf Σ → tf Σ) `{!Monoid tf_o} (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o} :=
  tf_monoid_unit_interp_eq_intro : ⟦ monoid_unit ⟧ₗ = monoid_unit.

Section instances.
  Context `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Global Instance tf_and_interp_comm : tf_op_interp_comm tf_and bi_and.
  Proof. econstructor. Qed.
  Global Instance tf_or_interp_comm : tf_op_interp_comm tf_or bi_or.
  Proof. econstructor. Qed.
  Global Instance tf_sep_interp_comm : tf_op_interp_comm tf_sep bi_sep.
  Proof. econstructor. Qed.

  Program Global Instance tf_and_monoid : Monoid tf_and := Build_Monoid _ _ _ tf_emp _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_and_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_logic tf_emp_logic left_id. done. Qed.

  Program Global Instance tf_or_monoid : Monoid tf_or := Build_Monoid _ _ _ (⌜ False ⌝)%F _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_or_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_logic tf_pure_logic left_id. done. Qed.

  Program Global Instance tf_sep_monoid : Monoid tf_sep := Build_Monoid _ _ _ tf_emp _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_sep_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_logic tf_emp_logic left_id. done. Qed.

  Global Instance tf_and_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_and bi_and.
  Proof. econstructor. Qed.
  Global Instance tf_or_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_or bi_or.
  Proof. econstructor. Qed.
  Global Instance tf_sep_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_sep bi_sep.
  Proof. econstructor. Qed.

End instances.

Section big_op.
  Context `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma tf_big_opL_interp
    (tf_o : tf Σ → tf Σ → tf Σ) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    A (P : nat → A → tf Σ) (l : list A) :
    ⟦[^tf_o list] n ↦ a ∈ l, P n a⟧ₗ = ([^iProp_o list] n ↦ a ∈ l, (⟦P n a⟧ₗ))%I.
  Proof.
    cut (∀ m, ⟦[^tf_o list] n ↦ a ∈ l, P (m + n) a⟧ₗ = ([^iProp_o list] n ↦ a ∈ l, (⟦P (m + n) a⟧ₗ))%I).
    { intros. specialize (H 0). simpl in H. auto. }
    induction l; intros; simpl; auto.
    rewrite (tf_op_interp_comm0). f_equal.
    erewrite (big_opL_proper_eq tf_o).
    - erewrite (IHl (S m)). apply big_opL_proper_eq; auto.
      repeat intro. replace (S m + a0) with (m + S a0) by lia. auto.
    - repeat intro. replace (S m + a0) with (m + S a0) by lia. auto.
    - auto.
  Qed.

  Lemma tf_big_opM_interp
    (tf_o : tf Σ → tf Σ → tf Σ) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    K `{!EqDecision K} `{!Countable K} A
    (P : K → A → tf Σ) (m : gmap K A) :
    ⟦[^tf_o map] k ↦ a ∈ m, P k a⟧ₗ = ([^iProp_o map] k ↦ a ∈ m, (⟦P k a⟧ₗ))%I.
  Proof.
    rewrite !big_op.big_opM_unseal /big_op.big_opM_def.
    erewrite (big_opL_proper_eq tf_o _ (λ n x, P x.1 x.2)); last eauto.
    - erewrite (big_opL_proper_eq iProp_o _ (λ n x, ⟦P x.1 x.2⟧ₗ)); last eauto.
      + eapply tf_big_opL_interp; eauto.
      + repeat intro. unfold uncurry. destruct a0. done.
    - repeat intro. unfold uncurry. destruct a0. done.
  Qed.

  Lemma tf_big_opS_interp
    (tf_o : tf Σ → tf Σ → tf Σ) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    A `{!EqDecision A} `{!Countable A}
    (P : A → tf Σ) (s : gset A) :
    ⟦[^tf_o set] a ∈ s, P a⟧ₗ = ([^iProp_o set] a ∈ s, (⟦P a⟧ₗ))%I.
  Proof.
    rewrite !big_op.big_opS_unseal /big_op.big_opS_def.
    erewrite (big_opL_proper_eq tf_o _ (λ n x, P x)); last eauto.
    - erewrite (big_opL_proper_eq iProp_o _ (λ n x, ⟦P x⟧ₗ)); last eauto.
      + eapply tf_big_opL_interp; eauto.
      + done.
    - done.
  Qed.

End big_op.

Section proof.
  Context `{SI : indexT} `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  (** Always *)
  Global Instance tf_always_persistent N P : Persistent (⟦tf_always N P⟧ₗ).
  Proof. tf_red. apply _. Qed.

  (** For now, rewrite tf_always_logic and use rules of inv. *)

  (** Until *)
  Lemma tf_until_frac_split N k b q q1 q2 P Q :
    (q = q1 + q2)%Qp →
    ⊢ ⟦tf_until N k b q P Q⟧ₗ -∗ (⟦tf_until N k b q1 P Q⟧ₗ ∗ ⟦tf_until N k b q2 P Q⟧ₗ).
  Proof.
    iIntros (He) "U". rewrite !tf_until_logic He Qp.div_add_distr. iDestruct "U" as "([$ $]& #U)". auto.
  Qed.
  Lemma tf_until_frac_add N k b1 b2 q1 q2 q P Q P' Q' :
    (q = q1 + q2)%Qp →
    ⟦tf_until N k b1 q1 P Q⟧ₗ -∗ ⟦tf_until N k b2 q2 P' Q'⟧ₗ -∗ ⟦tf_until N k b1 q P Q⟧ₗ.
  Proof.
    intros Hq. subst q.
    rewrite !tf_until_logic Qp.div_add_distr. iIntros "[Oa1 $] [Oa2 _]".
    iPoseProof (oblP_assigned_agree with "Oa1 Oa2") as "%". subst.
    by iCombine "Oa1 Oa2" as "Oa".
  Qed.

  Global Instance tf_until_fractional N k b P Q : Fractional (λ q, ⟦tf_until N k b q P Q⟧ₗ).
  Proof.
    intros p q. rewrite !tf_until_logic. iSplit.
    - iIntros "(Oa& #OI)". iFrame "OI". rewrite !Qp.div_add_distr. iDestruct "Oa" as "[Oa Oa']". iFrame.
    - iIntros "((Oa1& #Oi)& Oa2& _)". iFrame "Oi". rewrite !Qp.div_add_distr. iCombine "Oa1 Oa2" as "$".
  Qed.
  Global Instance tf_until_as_fractional N k b q P Q : AsFractional (⟦tf_until N k b q P Q⟧ₗ) (λ q, ⟦tf_until N k b q P Q⟧ₗ) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma tf_until_alloc E i G q (b : bool) ℓ μ :
    thP_obls i G q -∗
    |={E}=>m ∃ k, ⌜k ∉ G⌝ ∗ thP_obls i ({[k]} ∪ G) q ∗
                 oblP_layer k ℓ ∗ oblP_id k ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 ∀ E' N (P Q : tf Σ), ▷ (if b then ⟦Q⟧ₗ else ⟦P⟧ₗ)
                                    ={E'}=∗ (⟦tf_until N k b 1 P Q⟧ₗ).
  Proof.
    iIntros "TG". iMod (obl_alloc_assigned with "TG") as "(%& $& $& Oa& $& $& $& $& ACC)".
    iIntros "!> %%%% H". rewrite tf_until_logic. iMod ("ACC" with "H") as "ACC". iFrame. done.
  Qed.

  Lemma tf_fulfilled_alloc E ℓ μ (Q : tf Σ) :
    ⟦Q⟧ₗ -∗
    |={E}=>m ⟦Q⟧ₗ ∗ ∃ k, oblP_fulfilled k ∗ oblP_id k ∗
                        (∀ E' N (P : tf Σ), |={E'}=> oblP_inv N k ⟦P⟧ₗ ⟦Q⟧ₗ (tf_fulfilled k Q)) ∗ 
                        oblP_layer k ℓ ∗ oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof.
    iIntros "HQ".
    unfold_sfmupd. rewrite /fmupd. iIntros (?????) "SI".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    (* FIXME: proof without unfold everything? *)
    unfold_opreds. iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI)".
    assert (NEW : ∃ k, Ω1 !! k = None).
    { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
    destruct NEW as (k& NEWk).
    assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
    iMod (osat_alloc_obl_fulfilled _ k ℓ μ with "S") as "(S& #Gwf& #Ge& #Gu& Gf& %OStep)".
    { auto. }
    iMod (owit_alloc_witness_fulfilled _ k (η (measure ℓ μ)) with "[$W $Gu]") as "(W& #Ww)".
    { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
    iPoseProof (oassigned_add_obl with "[$A $Ge Gu]") as "A".
    { iRight. iFrame "Gu". }
    set (Ω2:=(<[k:=(obl_fulfilled)]> Ω1)).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 2. eauto. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iPoseProof (history_interp_hG_event_now with "SI") as "#HE".
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. econstructor 2. econstructor 2. auto. }
    iIntros (? [WStep GWI2]) "!>".
    pose proof (owit_inv_alloc_fulfilled Ω1 k W1 NinOk1 GWI W2 WStep GWI2) as (NinWk1& WMon).
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. iFrame. }
    iPoseProof (tf_logic_tf_intuit with "[$SI $HI $S $O $A $W $HQ]") as "#HQi". 1: eauto.    
    rewrite /model_interp. iFrame "HI S O A W". iSplitR; first eauto.
    iModIntro. iMod "close" as "_". iModIntro. iFrame "SI HQ". iExists k. iFrame "Gwf Ge Ww Gf Gu".
    iIntros (E' N P).
    rewrite tf_fulfilled_unfold.
    iMod (oblG_inv_alloc_fulfilled _ N _ _ ⟦P⟧ₗ ⟦Q⟧ₗ with "[$Gu]") as "#GVar"; cycle 1.
    { iFrame "GVar". done. }
    iFrame "Eo HE HQi".
  Qed.

  (** TODO: Timeless version *)
  Lemma tf_until_to_true E N k (P Q : tf Σ) :
    ↑N ⊆ E →
    ⟦tf_until N k false 1 P Q⟧ₗ ={E,E ∖ ↑N}=∗
    ▷ (⟦P⟧ₗ ∗ ∀ E', |={E'}=>m ((▷ ⟦Q⟧ₗ) ={E ∖ ↑N,E}=∗ ⟦tf_until N k true 1 P Q⟧ₗ)).
  Proof.
    rewrite !tf_until_logic. iIntros (HM) "(Oa& #Oi)".
    iMod (obl_assigned_to_true with "Oi Oa") as "[H ACC]". 1: auto.
    iModIntro. iNext. iDestruct "H" as "[Oa $]".
    iIntros "%". iPoseProof ("ACC" with "Oa") as "ACC". iMod ("ACC" $! E') as "[Oa ACC]".
    iIntros "!> HQ". iMod ("ACC" with "HQ") as "_". iFrame. eauto.
  Qed.

  (** TODO: Timeless version *)
  Lemma tf_until_fulfill E N k (P Q : tf Σ) :
    ↑N ⊆ E →
    ⟦tf_until N k true 1 P Q⟧ₗ ={E,E ∖ ↑N}=∗
    ∀ i G q,
    (⌜k ∈ G⌝) → thP_obls i G q -∗
    ∀ E', ▷ (|={E'}=>m |={E ∖ ↑N,E}=> (⟦Q⟧ₗ ∗ thP_obls i (G ∖ {[k]}) q ∗ oblP_fulfilled k)).
  Proof.
    rewrite tf_until_logic. iIntros (HMask) "(Oa& #OI)".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: auto.
    iIntros "!> %%% %LUGk TG %". iDestruct ("H" with "Oa") as "[H ACC]".
    iNext. iDestruct "H" as "(Oa1& Oa2& HQ)". iCombine "Oa1 Oa2" as "Oa".
    unfold_sfmupd. rewrite /fmupd. iIntros (?????) "SI".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    (* FIXME: it would be better if we don't need to unfold everything and re-do the proof here... *)
    unfold_opreds. iDestruct "TG" as "(#Oe& Ox& Ob& OS)". iDestruct "OI" as "(#Ge& Gvar)". iDestruct "Oa" as "(_& Gl)".
    iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& W& %GWI)".
    iPoseProof (big_sepS_delete _ _ _ LUGk with "OS") as "[(_& Go& Oo) OS]".
    iPoseProof (osat_lookup_assigned with "[$S $Ge $Gl]") as "%LUO1l".
    iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
    destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&LUO1o).
    rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into a.
    iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%& Go1& Oo1& _) | #Gu])".
    { apply elem_of_dom. eauto. }
    2:{ iExFalso. iPoseProof (oblG_assigned_fulfilled_false with "[$Gl $Gu]") as "%". done. }
    iPoseProof (oblG_owner_agree _ i i1 with "[$Go $Go1]") as "%". destruct H as [<- _].
    iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
    iMod (othread_delete_obl_frac with "[$O $Ob $Oo]") as "(O& Ob& Go2)".
    { auto. }
    iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'".
    iCombine "Go Go'" as "Go".
    iMod (osat_fulfill with "[$S $Ge $Gl $Go]") as "(S& #Gu& %Gstep)".
    assert (LUW : ∃ b, W1 !! k = Some (witness_assigned b) ∧ (b <= η a)%ord).
    { specialize (GWI k). rewrite LUO1l in GWI. inv GWI. destruct y; try done. eauto. }
    destruct LUW as (b&LUW1& LEab).
    iPoseProof (owit_fulfill with "[$W $Gu]") as "W". 1: eauto.
    iPoseProof (oassigned_add_obl _ k with "[$A $Ge]") as "A".
    { iRight. eauto. }
    set (Ω2:=(<[k:=(obl_fulfilled)]> Ω1)).
    assert (Gstep' : obl_step (obl_assigned a i) obl_fulfilled) by (by econstructor 2).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iPoseProof (history_interp_hG_event_now with "SI") as "#HE".
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
    iIntros (? [WStep GWI2]).
    pose proof (owit_inv_fulfill _ _ _ _ _ LUO1l GWI Gstep' W2 WStep GWI2) as (?& LUW& WMon).
    rewrite LUW1 in LUW. inv LUW.
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)). 1: iFrame.
      apply elem_of_dom_2 in LUO1l. rewrite -union_difference_L; set_solver. }
    iPoseProof (tf_logic_tf_intuit with "[$SI $HI $S $O $A $W $HQ]") as "#HQi". 1: eauto.
    rewrite /model_interp. iFrame "HI S O W A".
    iApply fupd_intro. iSplitR; first eauto. iIntros "!>". iFrame "Oe Ge Gu Ox SI".
    iMod "close" as "_". iModIntro. iMod ("ACC" with "[]") as "_".
    { iNext. iRight. iRight. rewrite tf_fulfilled_unfold. iFrame "Ge Gu Eo HE HQi". }
    iModIntro. iFrame.
  Qed.

  Lemma tf_until_fulfill_full E N k (P Q : tf Σ) :
    ↑N ⊆ E →
    ⟦tf_until N k false 1 P Q⟧ₗ ={E,E ∖ ↑N}=∗
    ▷ (⟦P⟧ₗ ∗
       ∀ E', |={E'}=>m ((▷ ⟦Q⟧ₗ) ={E ∖ ↑N}=∗
                       ∀ i G q, (⌜k ∈ G⌝) → thP_obls i G q -∗
                                ∀ E'', ▷ (|={E''}=>m |={E ∖ ↑N,E}=> (⟦Q⟧ₗ ∗ thP_obls i (G ∖ {[k]}) q ∗ oblP_fulfilled k)))).
  Proof.
    iIntros (HN) "Uk". iMod (tf_until_to_true with "Uk") as "H". 1: auto.
    iModIntro. iNext. iDestruct "H" as "($& H)". iIntros (?).
    iMod ("H" $! E') as "H". iIntros "!> HQ". iMod ("H" with "HQ") as "H".
    iMod (tf_until_fulfill with "H") as "H". 1: auto.
    iIntros "!> %%% % TG". iPoseProof ("H" with "[//] TG") as "H".
    iIntros (?). iNext. iMod ("H" $! E'') as "H". iModIntro. iFrame.
  Qed.

End proof.

(* (** Random tests to check universe consistency. *) *)

(* From transfinite.stepindex Require Import ordinals. *)
(* From transfinite.base_logic Require Import satisfiable. *)
(* From liris.algebra Require Import ordinal_existential_properties. *)

(* Global Instance ordSI : indexT := ordI. *)

(* Section test. *)
(*   Context `{!temporalGS Λ Σ}. *)

(*   (* Print Universes. *) *)

(*   Lemma test (P Q : iProp Σ) : *)
(*     iProp_sat (∃ (o : ord) (X : iProp Σ), ⌜ord_lt ((tf_depth (((tf_ghost P) ∗ ∀ N, tf_always N (tf_ghost Q)) : @tf _ _ (state_pred Λ))) : ord) o⌝ ∗ X)%I → *)
(*     ∃ (o : ord), iProp_sat (∃ (X : iProp Σ), ⌜ord_lt ((tf_depth (((tf_ghost P) ∗ ∀ N, tf_always N (tf_ghost Q)) : @tf _ _ (state_pred Λ))) : ord) o⌝ ∗ X)%I. *)
(*   Proof. *)
(*     intros. apply sat_exists in H. auto. *)
(*   Qed. *)

(*   (** Fail: tf is inside tf. *) *)
(*   Fail Lemma test2 (P Q : iProp Σ) : *)
(*     iProp_sat (∃ (o : Ord.t), ⌜Ord.lt ((tf_depth ((∃ (p : tf), p ∗ ∀ N k (q : tf), tf_always N k (q)) : @tf _ Σ state_pred)) : Ord.t) o⌝)%I → *)
(*     True. *)

(*   Lemma test3 : *)
(*     tf_logic (tf_ghost (∃ (P : iProp Σ), ∀ (Q : iProp Σ), P ∗ Q)) *)
(*     ⊢ (∃ (P : iProp Σ), ∀ (Q : iProp Σ), P ∗ Q). *)
(*   Proof. simpl. done. Qed. *)

(*   Lemma test4 : *)
(*     iProp_sat (∃ (o : ord) (X : iProp Σ), *)
(*           ⌜ord_lt ((tf_depth (((tf_ghost (∃ (p : iProp Σ), p)) ∗ ∀ N, tf_ghost (∀ (q : iProp Σ), tf_logic (tf_always N (tf_ghost q)))) : @tf _ Σ (state_pred Λ))) : ord) o⌝ ∗ *)
(*           tf_logic (∃ N, tf_always N (tf_ghost X)))%I → *)
(*     ∃ (o : ord), iProp_sat (∃ (X : iProp Σ), *)
(*                        ⌜ord_lt ((tf_depth (((tf_ghost (∃ (p : iProp Σ), p)) ∗ ∀ N, tf_ghost (∀ (q : iProp Σ), tf_logic (tf_always N (tf_ghost q)))) : @tf _ Σ (state_pred Λ))) : ord) o⌝ ∗ *)
(*                        tf_logic (∃ N, tf_always N (tf_ghost X)))%I. *)
(*   Proof. *)
(*     intros. apply sat_exists in H. auto. *)
(*   Qed. *)

(*   (* Print Universes. *) *)

(*   (** Fail: iProp quantification in tf_exist, probably requiring cmra < tf. *) *)
(*   Fail Lemma test3' : *)
(*     tf_logic (∃ (P Q : iProp Σ), tf_ghost (P ∗ Q)) ⊢ True. *)

(*   (* Print Universes. *) *)
(* (* Error: Found type "iProp Σ" where "?A" was expected *) *)
(* (* (unable to find a well-typed instantiation for "?A": cannot ensure that *) *)
(* (* "Type@{max(Set+1,indexT.u0,ucmra.u0)}" is a subtype of "Type@{tf.u2}"). *) *)

(* (* Ord.TYPE.u0 < cmra.u0 *) *)
(*   (* tf.u2 <= Ord.TYPE.u0 *) *)

(*   (** Fail: Probably, tf (tf.u2) ≤ Ord.t (Ord.TYPE.u0) < iProp Σ (cmra.u0), *)
(*       and this needs cmra.u0 < tf *) *)
(*   Fail Lemma test5 (P Q : iProp Σ) : *)
(*     iProp_sat (∃ (o : ord), ⌜ord_lt ((tf_depth ((∃ (p : iProp Σ), (tf_ghost p) ∗ ∀ N k (q : iProp Σ), tf_always N k (tf_ghost q)) : @tf _ Σ state_pred)) : ord) o⌝)%I → *)
(*     True. *)

(* (* Notation OrdinalExistential := (TypeExistentialProperty Ord.t) *) *)
(* (* iProp_sat_exists_instance: *) *)
(* (*   ∀ {SI : indexT} {Σ : gFunctors} {X : Type}, *) *)
(* (*     TypeExistentialProperty X SI → SatisfiableExists X iProp_sat *) *)
(* (* sat_exists: *) *)
(* (*   ∀ {SI : indexT} {PROP : bi} {X : Type} {sat : PROP → Prop}, *) *)
(* (*     SatisfiableExists X sat → ∀ Φ : X → PROP, sat (∃ x : X, Φ x)%I → ∃ x : X, sat (Φ x) *) *)

(* End test. *)
