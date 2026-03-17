From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From liris.program_logic Require Export language weakestpre.
From liris.program_logic Require Export temporal_logic temporal_property.

From transfinite.stepindex Require Import ordinals.
(* From transfinite.base_logic Require Import satisfiable. *)
From liris.base_logic Require Import satisfiable.
From liris.algebra Require Import ordinal_existential_properties.

From liris.prelude Require Import axioms.

(** Trace properties in iProp. *)
Notation tiProp Λ Σ := (trace Λ → iProp Σ).

Definition ti_atomic `{SI : indexT} {Λ} {Σ} (π : state_pred Λ) : tiProp Λ Σ :=
  λ τ, let '((Θ, σ), _, _) := (τ.2 τ.1) in ⌜state_sat σ Θ π⌝%I.

Definition ti_pure `{SI : indexT} {Λ} {Σ} (P : Prop) : tiProp Λ Σ :=
  λ _, ⌜P⌝%I.

Definition ti_and `{SI : indexT} {Λ} {Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, (P τ) ∧ (Q τ))%I.

Definition ti_or `{SI : indexT} {Λ} {Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, (P τ) ∨ (Q τ))%I.

Definition ti_impl `{SI : indexT} {Λ} {Σ} : Prop → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, ⌜P⌝ → (Q τ))%I.

Definition ti_forall `{SI : indexT} {Λ} {Σ} : ∀ (A : Type), (A → tiProp Λ Σ) → tiProp Λ Σ :=
  λ A P, (λ τ, ∀ (a : A), (P a τ))%I.

Definition ti_exist `{SI : indexT} {Λ} {Σ} : ∀ (A : Type), (A → tiProp Λ Σ) → tiProp Λ Σ :=
  λ A P, (λ τ, ∃ (a : A), (P a τ))%I.

(** 'Always' is a co-inductive fixpoint. *)
Definition ti_always_pre `{SI : indexT} `{!lirisGS Λ Σ} E
  (ti_always : (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  λ P τ, (|={E,∅}=> ▷ |={∅,E}=> ((P τ) ∗ |={E,∅}=> ALC (|={∅,E}=> ti_always P (trace_next τ))))%I.
  (* λ P τ, (|={E,∅}=> (▷ (P τ)) ∗ ((▷ (P τ)) ={∅}=∗ ALC (|={∅,E}=> ti_always P (trace_next τ))))%I. *)

Local Instance ti_always_pre_contractive `{SI : indexT} `{!lirisGS Λ Σ} E : Contractive (ti_always_pre E).
Proof.
  rewrite /ti_always_pre. repeat intro. do 5 (f_equiv).
  f_contractive. do 2 (f_equiv).
Qed.

Local Definition ti_always_def `{SI : indexT} `{!lirisGS Λ Σ} : tiProp Λ Σ → tiProp Λ Σ :=
  fixpoint (ti_always_pre ⊤).
Local Definition ti_always_aux : seal (@ti_always_def). Proof. by eexists. Qed.
Definition ti_always := ti_always_aux.(unseal).
Global Arguments ti_always {SI Λ Σ _}.
Local Lemma ti_always_unseal `{SI : indexT} `{!lirisGS Λ Σ} : ti_always = @ti_always_def SI Λ Σ _.
Proof. rewrite -ti_always_aux.(seal_eq) //. Qed.

Lemma ti_always_unfold `{SI : indexT} `{!lirisGS Λ Σ} (P : tiProp Λ Σ) (τ : trace Λ) :
  ti_always P τ ⊣⊢ ti_always_pre ⊤ (ti_always) P τ.
Proof. rewrite ti_always_unseal. apply (fixpoint_unfold (ti_always_pre ⊤)). Qed.

(** 'Until' is an inductive fixpoint, decreasing argument of Type A. *)
Definition ti_until_pre `{SI : indexT} `{!lirisGS Λ Σ} E
  {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  (ti_until : A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  λ a P Q τ,
    ((|={E,∅}=> ▷ |={∅,E}=> (Q τ)) ∨
       (|={E,∅}=> ▷ |={∅,E}=> ((P τ) ∗ |={E,∅}=> ∃ a', (⌜ltA a' a⌝) ∗ ALC (|={∅,E}=> ti_until a' P Q (trace_next τ)))))%I.

Local Instance ti_until_pre_contractive `{SI : indexT} `{!lirisGS Λ Σ} E
  {A : Type} {ltA : A → A → Prop} {wf_ltA : well_founded ltA}
  : Contractive (ti_until_pre E wf_ltA).
Proof.
  rewrite /ti_until_pre. repeat intro. do 9 (f_equiv).
  (* FIXME: f_equiv not working. *)
  f_contractive. do 1 (f_equiv). eapply dist_ne.
  { eapply H. }
  1,2: reflexivity.
Qed.

Local Definition ti_until_def `{SI : indexT} `{!lirisGS Λ Σ}
  {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  : A → tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  fixpoint (ti_until_pre ⊤ wf_ltA).
Local Definition ti_until_aux : seal (@ti_until_def). Proof. by eexists. Qed.
Definition ti_until := ti_until_aux.(unseal).
Global Arguments ti_until {SI Λ Σ _ _ _}.
Local Lemma ti_until_unseal `{SI : indexT} `{!lirisGS Λ Σ}
  {A : Type} {ltA : A → A → Prop} {wf_ltA : well_founded ltA} :
  @ti_until SI Λ Σ _ _ _ wf_ltA = @ti_until_def SI Λ Σ _ _ _ wf_ltA.
Proof. rewrite -ti_until_aux.(seal_eq) //. Qed.

Lemma ti_until_unfold `{SI : indexT} `{!lirisGS Λ Σ}
  {A : Type} {ltA : A → A → Prop} {wf_ltA : well_founded ltA}
  (a : A) (P Q : tiProp Λ Σ) (τ : trace Λ) :
  ti_until wf_ltA a P Q τ ⊣⊢ ti_until_pre ⊤ wf_ltA (ti_until wf_ltA) a P Q τ.
Proof. rewrite ti_until_unseal. apply (fixpoint_unfold (ti_until_pre ⊤ wf_ltA)). Qed.

(** Intermediate interpretation. *)
Fixpoint ti_logic `{SI : indexT} `{!lirisGS Λ Σ}
  {A : Type} {ltA : A → A → Prop} (wf_ltA : well_founded ltA)
  (Φ : @tf SI Σ (state_pred Λ)) : tiProp Λ Σ :=
  match Φ with
  | tf_emp => ti_pure True
  | tf_atomic π => (ti_atomic π)%I
  | tf_pure p => ti_pure p
  | tf_ghost p => ti_pure True
  | tf_and P Q => (ti_and (ti_logic wf_ltA P) (ti_logic wf_ltA Q))
  | tf_or P Q => (ti_or (ti_logic wf_ltA P) (ti_logic wf_ltA Q))
  | tf_impl P Q => (ti_impl P (ti_logic wf_ltA Q))
  | tf_forall A P => (ti_forall A (λ (a : A), ti_logic wf_ltA (P a)))
  | tf_exist A P => (ti_exist A (λ (a : A), ti_logic wf_ltA (P a)))
  | tf_sep P Q => (ti_and (ti_logic wf_ltA P) (ti_logic wf_ltA Q))
  | tf_pers P => (ti_pure True)
  | tf_always N P => (ti_always (ti_logic wf_ltA P))
  | tf_until N k b q P Q =>
      (ti_exist A (λ a, ti_until wf_ltA a (ti_logic wf_ltA P) (ti_logic wf_ltA Q)))
  end.

(** FIXME: move this to a more general location. *)
Section aux.
  Context `{SI : indexT} `{!invGS Σ}.

  Import uPred.

  Lemma iProp_sat_lc_and (P Q : iProp Σ) :
    iProp_sat_lc (P ∧ Q) → (iProp_sat_lc P ∧ iProp_sat_lc Q).
  Proof.
    intros H. split; revert H; apply sat_mono.
    - iIntros "[$ _]".
    - iIntros "[_ $]".
  Qed.

  Lemma iProp_sat_lc_at_and `{!invGS Σ} E (P Q : iProp Σ) :
    iProp_sat_lc_at E (P ∧ Q) → (iProp_sat_lc_at E P ∧ iProp_sat_lc_at E Q).
  Proof.
    intros H. split; revert H; apply sat_mono.
    - iIntros "[$ _]".
    - iIntros "[_ $]".
  Qed.

  Lemma iProp_sat_lc_at_frame_and `{!invGS Σ} E (F P Q : iProp Σ) :
    iProp_sat_lc_at_frame F E (P ∧ Q) → (iProp_sat_lc_at_frame F E P ∧ iProp_sat_lc_at_frame F E Q).
  Proof.
    intros H. split; revert H; apply sat_mono.
    - iIntros "[$ _]".
    - iIntros "[_ $]".
  Qed.

End aux.

Global Instance ordSI : indexT := ordI.

(** This cast using 'change' avoids universe inconsistency. *)
Global Instance iProp_sat_lc_SatisfiableExists {Σ}: SatisfiableExists ordinal_ucmra.OrdUR (@iProp_sat _ Σ).
Proof.
  change (ordinal_ucmra.OrdUR: Type) with Ord.t. apply iProp_sat_exists_instance.
Qed.

(* Global Instance iProp_sat_lc_at_SatisfiableAtFupd {Σ} `{!invGS Σ} : SatisfiableAtFupd (iProp_sat_lc_at). *)
(* Proof. *)
(*   apply sat_at_satisfiable_at_fupd. *)
(* Qed. *)

(* Global Instance iProp_sat_lc_at_frame_SatisfiableAtFupd {Σ} `{!invGS Σ} (F : iProp Σ) : SatisfiableAtFupd (iProp_sat_lc_at_frame F). *)
(* Proof. *)
(*   apply sat_at_frame_satisfiable_at_fupd. *)
(* Qed. *)

(* Print Universes. *)

(* uPred_primitive.uPred_sat_exists.u0 = temporal_logic.ordSI.u0 *)
(* tf_depth.u2 < uPred_primitive.uPred_sat_exists.u0 *)

(* ordExistential_instance.u0 < uPred_primitive.uPred_sat_exists.u0 *)
(* uPred_primitive.uPred_sat_exists.u0 = ordExistential_instance .u1 *)
(* uPred_primitive.uPred_sat_exists.u0 = ordExistential_instance.u1 *)
(* ucmra.u0 = cmra.u0 *)
(* Ord.TYPE.u0 < cmra.u0 *)
(* obl_class.u0 <= cmra.u0 *)
(* indexT.u0 <= cmra.u0 *)
(* ofe.u0 = cmra.u0 *)
(* universes.Logic = cmra.u0 *)

(* TODO *)

(* Unable to unify "?X" with "ucmra_car ordinal_ucmra.OrdUR" *)
(* (unable to find a well-typed instantiation for "?X": cannot ensure that "Type@{ucmra.u0}" is a *)
(* subtype of "Type@{uPred_primitive.uPred_sat_exists.u0}"). *)

(* Global Instance ord_satisfiable_exists {Σ : gFunctors} : SatisfiableExists Ord.t (iProp_sat (Σ:=Σ)). *)
(* Proof. apply iProp_sat_exists_instance. Qed. *)

(* TODO *)

(* Global Instance iProp_sat_lc_satisfiable_rupd {Σ : gFunctors} `{!invGS Σ} : *)
(*   SatisfiableRUpd (iProp_sat_lc). *)
(* Proof. *)
(*   apply sat_lc_satisfiable_rupd; try apply _. *)
(*   apply iProp_sat_exists_instance. *)

(*     econstructor. intros.  apply sat_exists in H. *)

(* Unable to unify "?X" with "ucmra_car ordinal_ucmra.OrdUR" *)
(* (unable to find a well-typed instantiation for "?X": cannot ensure that "Type@{ucmra.u0}" is a *)
(* subtype of "Type@{uPred_primitive.uPred_sat_exists.u0}"). *)

(* subtype of "Type@{uPred_primitive.uPred_sat_exists .u0}"). *)


Section proof1.
  Context `{!lirisGS Λ Σ}.
  Context {A : Type} {ltA : A → A → Prop} {wf_ltA : well_founded ltA}.
  Implicit Type F : iProp Σ.

  (* Lemma test1 (Ω1 : obls) i : *)
  (*   iProp_sat (Σ:=Σ) (∃ Ω2, (⌜(Ω1 ↪ₚ Ω2 | obl_cond_owner i)⌝)) *)
  (*   → (∃ Ω2, (Ω1 ↪ₚ Ω2 | obl_cond_owner i)). *)
  (* Proof. *)
  (*   intros. apply sat_exists in H. destruct H. apply sat_elim in H. eauto. *)
  (* Qed. *)

  (* Lemma test2 : *)
  (*   iProp_sat (∃ (o : obl_fuel) k ℓ μ, oblP_fuel k ℓ μ ∗ witP_cred k o) *)
  (*   → ∃ (o : obl_fuel) k ℓ μ, iProp_sat (oblP_fuel k ℓ μ ∗ witP_cred k o). *)
  (* Proof. *)
  (*   intros. do 4 (apply sat_exists in H; destruct H). eauto. *)
  (* Qed. *)

  Lemma ti_always_trace_next F Φ τ :
    iProp_sat_lc_at_frame F ⊤ (ti_always (ti_logic wf_ltA Φ) τ) →
    iProp_sat_lc_at_frame F ⊤ (ti_always (ti_logic wf_ltA Φ) (trace_next τ)).
  Proof.
    intros. rewrite ti_always_unfold /ti_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd in H. apply sat_sep in H. destruct H.
    apply sat_fupd, sat_ALC, sat_fupd in H0. auto.
  Qed.
  Lemma ti_always_trace_later F Φ n x τf :
    n ≤ x →
    iProp_sat_lc_at_frame F ⊤ (ti_always (ti_logic wf_ltA Φ) (n, τf)) →
    iProp_sat_lc_at_frame F ⊤ (ti_always (ti_logic wf_ltA Φ) (x, τf)).
  Proof.
    intro LE. induction LE; intros; first auto.
    apply IHLE in H. apply ti_always_trace_next in H. done.
  Qed.

  Lemma ti_always_tr_always F Φ :
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_logic wf_ltA Φ τ) → tf_trace Φ τ) →
    ∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_always (ti_logic wf_ltA Φ) τ) → tr_always (tf_trace Φ) τ.
  Proof.
    intros IH τ H. unfold tr_always. destruct τ as (n&τf).
    (** Use classical logic. *)
    intro m. pattern m. revert m. apply Classical_Pred_Type.not_ex_not_all.
    intros ?. destruct H0. apply Classical_Prop.imply_to_and in H0. destruct H0.
    apply H1. clear H1.
    eapply ti_always_trace_later in H. 2: eauto.
    eapply IH. rewrite ti_always_unfold /ti_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd in H. apply sat_sep in H. destruct H. auto.
  Qed.

  Lemma ti_until_tr_until F Φ1 Φ2 :
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_logic wf_ltA Φ1 τ) → tf_trace Φ1 τ) →
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_logic wf_ltA Φ2 τ) → tf_trace Φ2 τ) →
    ∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_exist A (λ a, ti_until wf_ltA a (ti_logic wf_ltA Φ1) (ti_logic wf_ltA Φ2)) τ) →
         tr_until (tf_trace Φ1) (tf_trace Φ2) τ.
  Proof.
    intros IH1 IH2 τ H. unfold tr_until. destruct τ as (n&τf).
    unfold ti_exist in H. apply sat_exists in H. destruct H.
    revert n τf H. induction x as [a IHa] using (well_founded_ind wf_ltA). intros.
    rewrite ti_until_unfold /ti_until_pre in H. apply sat_or in H. destruct H.
    { apply sat_fupd, sat_later, sat_fupd in H. apply IH2 in H.
      exists n. split_and !; eauto. intros. lia. }
    apply sat_fupd, sat_later, sat_fupd in H. apply sat_sep in H. destruct H as [HP H].
    apply sat_fupd, sat_exists in H. destruct H as [b H].
    apply sat_sep in H. destruct H as [Hlt H]. apply sat_elim in Hlt.
    apply sat_ALC, sat_fupd in H.
    specialize (IHa _ Hlt _ _ H). simpl in IHa. destruct IHa as (m'& Hm'& Htr& Hp).
    destruct Hm'.
    { exists (S n). split_and !; eauto. intros. destruct H0. destruct H0; eauto. apply Hp. lia. }
    exists (S m). split_and !; eauto.
    { lia. }
    intros. destruct H0. destruct H0; eauto. apply Hp. lia.
  Qed.

  Lemma ti_logic_tf_trace (F : iProp Σ) (Φ : tf) (τ : trace Λ) :
    iProp_sat_lc_at_frame F ⊤ (ti_logic wf_ltA Φ τ) → tf_trace Φ τ.
  Proof.
    revert τ. induction Φ; simpl; intros.
    - done.
    - unfold ti_atomic in H. destruct τ. simpl in H.
      unfold tr_atomic. simpl. destruct (p n) as (((Θ&σ)&?)&?).
      apply sat_elim in H. auto.
    - unfold ti_pure in H. apply sat_elim in H. auto.
    - done.
    - unfold ti_and in H. apply iProp_sat_lc_at_frame_and in H. destruct H.
      apply IHΦ1 in H. apply IHΦ2 in H0. split; auto.
    - unfold ti_or in H. apply sat_or in H. destruct H.
      + apply IHΦ1 in H. left. auto.
      + apply IHΦ2 in H. right. auto.
    - unfold tr_impl. intros HP. unfold ti_impl in H. apply sat_impl in H; auto.
    - unfold tr_forall. intros. unfold ti_forall in H0. apply (sat_forall a) in H0. eauto.
    - unfold tr_exist. unfold ti_exist in H0. apply (sat_exists) in H0. destruct H0. eauto.
    - unfold ti_and in H. apply iProp_sat_lc_at_frame_and in H. destruct H.
      apply IHΦ1 in H. apply IHΦ2 in H0. split; auto.
    - done.
    - eapply ti_always_tr_always; eauto.
    - eapply ti_until_tr_until; eauto.
  Qed.

End proof1.
