From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From liris.program_logic Require Export language weakestpre.
From liris.program_logic Require Export temporal_logic temporal_property.

From transfinite.stepindex Require Import ordinals.
(* From transfinite.base_logic Require Import satisfiable. *)
From liris.base_logic Require Import satisfiable.
From liris.algebra Require Import ordinal_existential_properties.

From liris.prelude Require Import axioms.

Section fair_sched.
  Context {Λ : language}.

  Definition fscnt : Type := thread_id → nat.

  CoInductive beh_fscnt_th (τ : trace Λ) (i : thread_id) (c : nat) : Prop :=
  | beh_fscnt_th_step ρ j κs c' :
    (τ.2 τ.1) = (ρ, j, κs) →
    ((thread_na i τ) ∨ (thread_active i τ ∧ (if (decide (i = j)) then True else c' < c))) →
    beh_fscnt_th (trace_next τ) i c' →
    beh_fscnt_th τ i c.
  Definition beh_fscnt (τ : trace Λ) (γ : fscnt) : Prop :=
    ∀ (i : thread_id), beh_fscnt_th τ i (γ i).

  Lemma beh_fscnt_th_upto_le (τ : trace Λ) i (c1 c2 : nat) :
    beh_fscnt_th τ i c1 →
    c1 ≤ c2 →
    beh_fscnt_th τ i c2.
  Proof.
    intros BEH LEc. inv BEH.
    eapply (beh_fscnt_th_step _ _ _ _ _ _ c'). 1: eauto. 2: auto.
    destruct H0; auto. right. destruct H0. split; auto.
    destruct (decide (i = j)); auto. eapply Nat.lt_le_trans; eauto.
  Qed.

  (** We use choice here. *)
  Lemma fair_scheduling_fscnt (τ : trace Λ) :
    fair_scheduling τ → ∃ (γ : fscnt), beh_fscnt τ γ.
  Proof.
    intros FS. unfold beh_fscnt. apply choice. intros i. destruct τ as (n&τf).
    assert (∀ (s : nat), ((thread_na i (n, τf)) ∨ (thread_active i (n, τf) ∧ thread_turn i (s + n, τf)))
                       → beh_fscnt_th (n, τf) i s); cycle 1.
    { destruct (thread_active_or_not i (n, τf)) as [TH | TH].
      - exists 0. specialize (H 0). apply H. left. auto.
      - specialize (FS n). unshelve edestruct FS. 1: exact i. 1: lia.
        { exfalso. eapply (thread_active_and_not_false _ ((n, τf))); eauto. }
        destruct H0 as [TA TEV]. unfold tr_eventually, tr_until in TEV. destruct TEV as (m& LEm& TTurn& _).
        remember (m - n) as s. assert (m = s + n) by lia. subst m. clear Heqs LEm.
        exists s. apply H. right. auto. }
    revert n FS. cofix CIH; intros. destruct H as [TH | TH].
    - rename TH into TNA. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
      destruct (thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
      + econstructor. 1: eauto. 1: auto.
        unshelve eapply (CIH _ _ 0); auto. apply fair_scheduling_next. auto.
      + pose proof FS as FSn'. specialize (FSn' (S n)).
        unshelve edestruct FSn'. 1: exact i. 1: lia.
        { exfalso. eapply (thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
        destruct H as [TA TEV]. unfold tr_eventually, tr_until in TEV. destruct TEV as (m& LEm& TTurn& _).
        remember (m - (S n)) as s'. assert (m = s' + S n) by lia. subst m. clear Heqs' LEm.
        eapply (beh_fscnt_th_step _ _ _ _ _ _ s'). 1: eauto. 1: auto.
        eapply CIH.
        * apply fair_scheduling_next; auto.
        * right. eauto.
    - destruct TH as [TA TTurn]. destruct s.
      (* Induction on s breask Guarded check? *)
      { simpl in TTurn. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
        unfold thread_turn in TTurn. simpl in TTurn. rewrite Htrn in TTurn. subst j.
        destruct (thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
        - econstructor. 1: eauto.
          { right. split; auto. rewrite decide_True; auto. }
          unshelve eapply (CIH _ _ 0); eauto. eapply fair_scheduling_next; eauto.
        - pose proof FS as FSn'. specialize (FSn' (S n)).
          unshelve edestruct FSn'. 1: exact i. 1: lia.
          { exfalso. eapply (thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
          destruct H as [TA2 TEV2]. unfold tr_eventually, tr_until in TEV2. destruct TEV2 as (m& LEm& TTurn2& _).
          remember (m - (S n)) as s. assert (m = s + S n) by lia. subst m. clear Heqs LEm.
          eapply (beh_fscnt_th_step _ _ _ _ _ _ s). 1: eauto.
          { right. split; auto. rewrite decide_True; auto. }
          apply CIH; auto. apply fair_scheduling_next; auto. }
      { simpl in TTurn. destruct (τf n) as (((Θ& σ)& j)& κs) eqn:Htrn.
        destruct (decide (j = i)).
        - subst j. destruct (thread_active_or_not i (trace_next (n, τf))) as [Next | Next].
          + econstructor. 1: eauto.
            { right. split; auto. rewrite decide_True; auto. }
            unshelve eapply (CIH _ _ 0); eauto. eapply fair_scheduling_next; eauto.
          + pose proof FS as FSn'. specialize (FSn' (S n)).
            unshelve edestruct FSn'. 1: exact i. 1: lia.
            { exfalso. eapply (thread_active_and_not_false _ (trace_next (n, τf))); eauto. }
            destruct H as [TA2 TEV2]. unfold tr_eventually, tr_until in TEV2. destruct TEV2 as (m& LEm& TTurn2& _).
            remember (m - (S n)) as s'. assert (m = s' + S n) by lia. subst m. clear Heqs' LEm.
            eapply (beh_fscnt_th_step _ _ _ _ _ _ s'). 1: eauto.
            { right. split; auto. rewrite decide_True; auto. }
            apply CIH; auto. apply fair_scheduling_next; auto.
        - eapply (beh_fscnt_th_step _ _ _ _ _ _ s). 1: eauto.
          { right. split; auto. rewrite decide_False; auto. }
          apply CIH; auto.
          + apply fair_scheduling_next; auto.
          + simpl. destruct (thread_active_or_not i (S n, τf)) as [? | TA2]; first auto.
            right. replace (s + S n) with (S (s + n)) by lia. split; auto. }
  Qed.

  Definition fscnt_next_rel_th (τ : trace Λ) i (c1 c2 : nat) : Prop :=
    if (decide (i = trace_thread τ)) then True
    else if (decide (thread_na i τ)) then True
         else (c2 < c1).
  Definition fscnt_next_rel (τ : trace Λ) (γ1 γ2 : fscnt) : Prop :=
    ∀ i, fscnt_next_rel_th τ i (γ1 i) (γ2 i).

  (** We again use choice here. *)
  Lemma exists_fscnt_next (τ : trace Λ) (γ : fscnt) :
    beh_fscnt τ γ →
    ∃ γ', beh_fscnt (trace_next τ) γ' ∧ fscnt_next_rel τ γ γ'.
  Proof.
    intros Beh. unfold beh_fscnt, fscnt_next_rel.
    cut (∃ γ', ∀ i, (λ i c, beh_fscnt_th (trace_next τ) i c ∧ fscnt_next_rel_th τ i (γ i) c) i (γ' i)).
    { intros. destruct H. exists x. split; intros; firstorder. }
    apply choice. intros i. specialize (Beh i). inv Beh.
    exists c'. split; auto. unfold fscnt_next_rel_th.
    destruct τ as (n&τf). unfold trace_thread, trace_state. simpl in *.
    rewrite H. simpl. destruct (decide (i = j)); auto. destruct H0.
    { rewrite decide_True; auto. }
    destruct H0. rewrite decide_False; auto.
    intros F. eapply thread_active_and_not_false; eauto.
  Qed.

End fair_sched.

(** Trace properties in iProp, intermediate representation for the adequacy proof. *)
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
(* We need to use ∧ here for the proof. *)
Definition ti_always_pre `{SI : indexT} `{!lirisGS Λ Σ} E
  (ti_always : (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  λ P τ, (|={E,∅}=> ▷ |={∅,E}=> ((P τ) ∧ |={E,∅}=> ALC (|={∅,E}=> ti_always P (trace_next τ))))%I.

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
       (|={E,∅}=> ▷ |={∅,E}=> ((P τ) ∧ |={E,∅}=> ∃ a', (⌜ltA a' a⌝) ∧ ALC (|={∅,E}=> ti_until a' P Q (trace_next τ)))))%I.

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


(* Unable to unify "?X" with "ucmra_car ordinal_ucmra.OrdUR" *)
(* (unable to find a well-typed instantiation for "?X": cannot ensure that "Type@{ucmra.u0}" is a *)
(* subtype of "Type@{uPred_primitive.uPred_sat_exists.u0}"). *)

(* Global Instance ord_satisfiable_exists {Σ : gFunctors} : SatisfiableExists Ord.t (iProp_sat (Σ:=Σ)). *)
(* Proof. apply iProp_sat_exists_instance. Qed. *)


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
    apply sat_fupd, sat_later, sat_fupd in H. apply iProp_sat_lc_at_frame_and in H. destruct H.
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
    apply sat_fupd, sat_later, sat_fupd in H.
    apply iProp_sat_lc_at_frame_and in H. destruct H. auto.
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
    apply sat_fupd, sat_later, sat_fupd in H.
    apply iProp_sat_lc_at_frame_and in H. destruct H as [HP H].
    apply sat_fupd, sat_exists in H. destruct H as [b H].
    apply iProp_sat_lc_at_frame_and in H. destruct H as [Hlt H]. apply sat_elim in Hlt.
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

Section proof2.
  Local Transparent tf_intuit.
  Context `{!lirisGS Λ Σ}.

  (* Local Definition D : Type := (prod obl_fuel nat). *)
  (* Local Definition ltD : D → D → Prop := (prod_lt WFOCM.ltR lt). *)
  (* Local Definition wf_ltD : well_founded ltD := (prod_lt_well_founded _ _ _ _ WFOCM.lt_wf Nat.lt_wf_0). *)

  Definition obls_thread_active (Ω : obls) (τ : trace Λ) :=
    map_Forall (λ _ o, match o with
                       | obl_assigned _ i => thread_active i τ
                       | _ => True
                       end
      ) Ω.

  Lemma mprog_exists_step i Ω1 Ω2 W1 (τ : trace Λ) γ1 :
    i = trace_thread τ →
    obls_thread_active Ω1 τ →
    owit_inv Ω1 W1 →
    owit_inv_lb (fair_sched_fun γ1) Ω1 W1 →
    beh_fscnt τ γ1 →
    (Ω1 ↪ₚ Ω2 | obl_cond_owner i) →
    ∃ W2 γ2, (W1 ↓ₚ W2 | wit_cond_assigned) ∧ owit_inv Ω2 W2 ∧
             owit_inv_lb (fair_sched_fun γ2) Ω2 W2 ∧ beh_fscnt (trace_next τ) γ2 ∧ fscnt_next_rel τ γ1 γ2.
  Proof.
    intros EQi OTA Inv LB Beh Prog. subst i. destruct (exists_fscnt_next _ _ Beh) as (γ2&Beh2&GNext).
    cut (∃ W2, (W1 ↓ₚ W2 | wit_cond_assigned) ∧ owit_inv Ω2 W2 ∧ owit_inv_lb (fair_sched_fun γ2) Ω2 W2).
    { intros (?&?&?&?). exists x, γ2. split_and !; auto. }
    revert Ω1 Ω2 τ γ1 γ2 OTA Inv LB Beh Prog Beh2 GNext.
    induction W1 using map_ind; intros Ω1 Ω2 τ γ1 γ2 OTA Inv LB Beh Prog Beh2 GNext.
    { apply map_Forall2_empty_inv_r in Inv. subst. destruct Prog. apply map_Forall2_empty_inv_l in H0. subst.
      exists ∅. split_and !; auto.
      - split; apply map_Forall2_empty.
      - apply map_Forall2_empty.
      - apply map_Forall2_empty. }
    destruct Prog as (Step& Keep). rename i into k, x into w, m into W1, H into LUW1, Ω1 into Ω1', Ω2 into Ω2'.
    apply map_Forall2_insert_inv_r in Inv; auto. destruct Inv as (o1&Ω1&EQO1&LUO1&Invk&Inv').
    assert (Inv : owit_inv Ω1 W1) by auto. clear Inv'. subst Ω1'.
    apply map_Forall2_insert in LB; auto. destruct LB as (LBk& LB').
    assert (LB : owit_inv_lb (fair_sched_fun γ1) Ω1 W1) by auto. clear LB'.
    apply map_Forall2_insert_inv_l in Keep; auto. destruct Keep as (o2&Ω2&EQO2&LUO2&Keepk&Keep').
    assert (Keep : obls_keep Ω1 Ω2) by auto. clear Keep'. subst Ω2'.
    apply map_Forall2_insert in Step; auto. destruct Step as (Stepk&Step').
    assert (Step : Ω1 ↪ₛ Ω2 | obl_cond_owner (trace_thread τ)) by auto. clear Step'.
    apply map_Forall_insert in OTA; auto. destruct OTA as (OTAk&OTA').
    assert (OTA : obls_thread_active Ω1 τ) by auto. clear OTA'.
    unshelve epose proof (IHW1 Ω1 Ω2 τ γ1 γ2 OTA Inv LB Beh _ Beh2 GNext) as IH.
    { split; auto. }
    clear IHW1. destruct IH as (W2& ProgW& Inv2& LB2).
    destruct ProgW as [StepW KeepW]. assert (LUW2 : W2 !! k = None).
    { apply owit_inv_dom in Inv2. apply not_elem_of_dom. rewrite -Inv2. apply not_elem_of_dom. auto. }
    cut (∃ (w' : witness),
            ((wit_cond_assigned k w ∧ witness_step w w') ∨ (¬ wit_cond_assigned k w ∧ w = w')) ∧
            (witness_keep w w') ∧
            (match o2 with
             | obl_assigned a _ => match w' with
                                  | witness_assigned b => b w≤ η a
                                  | witness_fulfilled => False
                                  end
             | obl_fulfilled => match w' with
                               | witness_assigned _ => False
                               | witness_fulfilled => True
                               end
             end) ∧
            (match o2 with
             | obl_assigned a i => match w' with
                                  | witness_assigned b => (fair_sched_fun γ2 i a) w≤ b
                                  | witness_fulfilled => False
                                  end
             | obl_fulfilled => match w' with
                               | witness_assigned _ => False
                               | witness_fulfilled => True
                               end
             end)).
    { intros (w'& Hw1& Hw2& Hw3& Hw4). exists (<[k:=w']>W2). split_and !.
      - split; apply map_Forall2_insert; auto.
      - apply map_Forall2_insert; auto.
      - apply map_Forall2_insert; auto.
    }
    clear dependent W1 W2 Ω1 Ω2. destruct o1, w; try done.
    - simpl in Stepk. destruct Stepk as [Turn | NoTurn].
      + destruct Turn as [-> Stepk]. simpl in Keepk. destruct o2; last done. clear Keepk.
        inv Stepk; cycle 1. 1: inv H.
        (* FIXME: type checking fails without OC. *)
        inv H. simpl in *. exists (witness_assigned (OC:=ord_obl_class) (fair_sched_fun γ2 owner fuel0)).
        split_and !; auto.
        * left. split; auto. econstructor. econstructor. eapply (Ord.lt_le_lt); last eapply LBk.
          apply fair_sched_fun_mon_gen. auto.
        * apply fair_sched_fun_ub.
        * done.
      + destruct NoTurn as [NoTurn <-]. simpl in Keepk. clear Keepk. simpl in *.
        exists (witness_assigned (OC:=ord_obl_class) (fair_sched_fun γ2 owner fuel)).
        split_and !; auto.
        * left. split; auto. econstructor. econstructor. eapply (Ord.lt_le_lt); last eapply LBk.
          unfold fair_sched_fun. apply Hessenberg.lt_add_r. specialize (GNext owner).
          unfold fscnt_next_rel_th in GNext. rewrite decide_False in GNext; auto. rewrite decide_False in GNext; auto.
          { apply OrdArith.lt_from_nat; auto. }
          { intros F. eapply thread_active_and_not_false; eauto. }
        * apply fair_sched_fun_ub.
        * done.
    - simpl in Stepk. destruct Stepk as [Turn | NoTurn].
      + destruct Turn as [F Stepk]. done.
      + destruct NoTurn as [_ <-]. simpl in Keepk. clear Keepk. simpl in *.
        exists (witness_fulfilled). split_and !; auto.
  Qed.

  Lemma get_obls_thread_active s h n σ Θ TQ κs g v Ω W τf :
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    Θ = fst <$> TQ →
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗
    ([∗ map] i ↦ '(e, Q) ∈ TQ, match to_val e with
                               | Some v => (lift_term i Q) v
                               | None => lwp_fix s i ⊤ e (lift_term i Q)
                               end)
    ⊢ ⌜obls_thread_active Ω (n, τf)⌝.
  Proof.
    iIntros (HIST EQTQ) "(HI& MI& WPs)". iIntros (k o LUk). destruct o; last eauto.
    unfold thread_active. simpl. iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    apply HIST in Hlu. destruct Hlu as (j& Now). rewrite Now.
    iDestruct "MI" as "(MHI& S& T& A& W& %Inv)".
    iPoseProof (othread_assigned_thread_elem with "[$S $T $A]") as "%Tin". 1: eapply LUk.
    apply elem_of_dom in Tin. destruct Tin as (e&LUth).
    rewrite EQTQ lookup_fmap_Some in LUth. destruct LUth as (?& EQe& LUth).
    destruct x as (?&Q). simpl in EQe. subst e0.
    iPoseProof (big_sepM_delete _ _ _ _ LUth with "WPs") as "[WP WPs]".
    destruct (to_val e) eqn:TVe.
    - iDestruct "WP" as "(#Term& HQ)". iPoseProof (othread_assigned_term_false with "[$S $T $A]") as "%"; eauto.
      unfold_opreds. auto.
    - iPureIntro. exists e. split; auto. subst. rewrite lookup_fmap LUth. done.
  Qed.

  Lemma owit_inv_lb_step_na_turn τ Ω W γ1 γ2 :
    thread_na (trace_thread τ) τ →
    obls_thread_active Ω τ →
    owit_inv_lb (fair_sched_fun γ1) Ω W →
    fscnt_next_rel τ γ1 γ2 →
    owit_inv_lb (fair_sched_fun γ2) Ω W.
  Proof.
    intros. intro k. specialize (H0 k). specialize (H1 k). inv H1. 2: econstructor.
    symmetry in H3, H4. specialize (H0 _ H3). simpl in H0. econstructor. destruct x, y; try done.
    etrans; last eauto. apply Hessenberg.le_add_r, OrdArith.le_from_nat.
    specialize (H2 owner). unfold fscnt_next_rel_th in H2. rewrite decide_False in H2; cycle 1.
    { intros ->. eapply thread_active_and_not_false; eauto. }
    rewrite decide_False in H2; first lia. intros F. eapply thread_active_and_not_false; eauto.
  Qed.

  Lemma lwp_ti_logic s h n σ Θ (TQ : gmap thread_id ((expr Λ) * (thread_id → val Λ → iProp Σ))) κs g v1 v2 Ω1 Ω2 W τf γ Φ :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    v1 ≤ v2 →
    obls_le Ω1 Ω2 →
    (* obls_thread_active Ω2 (n, τf) → *)
    owit_inv_lb (fair_sched_fun γ) Ω2 W →
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    Θ = fst <$> TQ →
    history_interp h n σ Θ κs ∗ model_interp g v2 Ω2 W n (dom Θ) ∗
    ([∗ map] i ↦ '(e, Q) ∈ TQ, match to_val e with
                               | Some v => (lift_term i Q) v
                               | None => lwp_fix s i ⊤ e (lift_term i Q)
                               end) ∗
    tf_intuit n σ Θ κs v1 Ω1 Φ
    ⊢ ti_logic Ord.lt_well_founded Φ (n, τf).
  Proof.
    revert h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ.
    induction Φ; iIntros (h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "(HI& MI& WPs& #TF)"; simpl.
    - done.
    - unfold ti_atomic. iPoseProof (event_pred_history_interp_lookup with "[$HI $TF]") as "%". destruct H.
      simpl. apply HIST in H. destruct H. rewrite H. auto.
    - unfold ti_pure. done.
    - done.
    - unfold ti_and. iSplit.
      + iDestruct "TF" as "[TF _]". iApply (IHΦ1 with "[$HI $MI $WPs $TF]"); eauto.
      + iDestruct "TF" as "[_ TF]". iApply (IHΦ2 with "[$HI $MI $WPs $TF]"); eauto.
    - unfold ti_or. iDestruct "TF" as "[TF | TF]".
      + iLeft. iApply (IHΦ1 with "[$HI $MI $WPs $TF]"); eauto.
      + iRight. iApply (IHΦ2 with "[$HI $MI $WPs $TF]"); eauto.
    - unfold ti_impl. iIntros "HP". iPoseProof ("TF" with "HP") as "#TF'".
      iApply (IHΦ with "[$HI $MI $WPs $TF']"); eauto.
    - unfold ti_forall. iIntros (?). iSpecialize ("TF" $! a).
      iApply (H with "[$HI $MI $WPs $TF]"); eauto.
    - unfold ti_exist. iDestruct "TF" as "(%& TF)". iExists a.
      iApply (H with "[$HI $MI $WPs $TF]"); eauto.
    - unfold ti_and. iDestruct "TF" as "[TF1 TF2]". iSplit.
      + iApply (IHΦ1 with "[$HI $MI $WPs $TF1]"); eauto.
      + iApply (IHΦ2 with "[$HI $MI $WPs $TF2]"); eauto.
    - done.
    - clear dependent v1 Ω1. rename v2 into v, Ω2 into Ω.
      iRevert (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ) "TF HI MI WPs".
      iLöb as "IH". iIntros (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ) "#TF HI MI WPs".
      rewrite ti_always_unfold /ti_always_pre.
      iMod (inv_acc with "TF") as "[HP ACC]". 1: set_solver.
      iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext.
      iPoseProof (tf_logic_tf_intuit with "[$HI $MI $HP]") as "#TFP".
      iMod "close" as "_". iMod ("ACC" with "HP") as "_". iModIntro. iSplit.
      { iApply (IHΦ with "[$HI $MI $WPs $TFP]"); eauto. done. }
      (** Fetch the scheduled thread and take a step. *)
      inversion BEH. clear BEH. subst n0 τf0.
      iPoseProof (history_interp_lookup with "HI") as "%LUhn". apply HIST in LUhn. destruct LUhn as (i'&LUhn).
      rewrite H1 in LUhn. inversion LUhn. clear LUhn. subst ρ1 i' κs.
      rename κs0 into κs, H1 into TRn, H3 into TRn1, H4 into BEH.
      destruct H2 as [TStep | TDone].
      + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
        inversion TStep. clear TStep. inversion H. clear H. subst Θ0 σ ρ2. rename H1 into PStep, H0 into LUTi1.
        assert (LUTQi1 : ∃ Q, TQ !! i1 = Some (e1, Q)).
        { subst Θ. rewrite lookup_fmap_Some in LUTi1. destruct LUTi1 as (?&?&?). destruct x. subst. eauto. }
        destruct LUTQi1 as (Q& LUTQi1). iPoseProof (big_sepM_delete _ _ _ _ LUTQi1 with "WPs") as "[WP WPs]".
        pose proof (val_stuck _ _ _ _ _ _ _ _ PStep) as He1. rewrite He1.
        iPoseProof (lwp_fix_unfold_fix with "WP") as "WP". rewrite /lwp_pre He1 /lwp_step.
        iMod ("WP" $! id with "[] [//] HI") as "[%NStuck WP]".
        { iPureIntro. apply _. }
        iPoseProof ("WP" with "[//]") as "WP". rewrite /mprog.
        iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
        iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
        unshelve epose proof (mprog_exists_step i1 Ω Ω2 W (n, τf) γ _ OTA OWinv LB FS ProgO).
        { unfold trace_thread, trace_state. simpl. rewrite TRn. done. }
        destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
        iMod ("WP" $! W2 with "[]") as "[MI WP]".
        { iPureIntro. split; auto. }
        rewrite /mphys. iMod ("WP" with "MI") as "[MI WP]". iModIntro. iMod "WP". simpl.
        iMod (model_interp_mupd_steps with "WP MI") as "(WP& %g'& %v'& %Ω3& %W3& %& MI)".
        2: eapply LB2.
        { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
        destruct H as [LEO LB3]. iMod "WP" as "(HI& WP& Efs)".
        unfold trace_next in *. simpl in *. assert (TDisj : Θ ##ₘ efs).
        { eapply map_disjoint_dom_2, fork_thread_ids; eauto. }
        remember ((<[i1:=e2]> Θ) ∪ efs) as Θ2.
        replace (dom (<[i1:=e2]> Θ) ∪ dom efs) with (dom Θ2); cycle 1.
        { subst Θ2. rewrite dom_union_L. auto. }
        remember ((λ e, (e, fork_post)) <$> efs : gmap thread_id (expr Λ * (thread_id → val Λ → iProp Σ))) as TQefs.
        iAssert ([∗ map] j ↦ '(e, Q) ∈ TQefs, lwpupd j ⊤ e (match to_val e with
                                                            | Some v => lift_term j Q v
                                                            | None => lwp_fix s j ⊤ e (lift_term j Q)
                                                            end))%I with "[Efs]" as "Efs".
        { subst TQefs. iApply big_sepM_fmap. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% WP".
          destruct (to_val x) eqn:EQx.
          - rewrite lwp_fix_unfold_fix /lwp_pre EQx lwpupd_trans. iApply "WP".
          - iApply "WP". }
        iMod (all_interp_lwpupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)".
        { subst Θ2 TQefs. rewrite -map_fmap_compose. unfold compose. simpl. rewrite map_fmap_id.
          apply map_union_subseteq_r. apply map_disjoint_insert_l_2; auto. apply not_elem_of_dom.
          apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. }
        1: auto. destruct H as [LEO2 LB4]. destruct (to_val e2) eqn:He2.
        * rewrite lwp_fix_unfold_fix /lwp_pre He2.
          iMod (all_interp_lwpupd_steps with "WP HI MI") as "(WP& HI& %g3& %v3& %Ω5& %W5& %& MI)".
          { subst Θ2. rewrite lookup_union_l.
            - apply lookup_insert_eq.
            - apply not_elem_of_dom. apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. }
          1: eapply LB4. destruct H as [LEO3 LB5].
          iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                     (match to_val e with
                      | Some v => lift_term j Q v
                      | None => lwp_fix s j ⊤ e (lift_term j Q)
                      end))%I with "[WPs WP Efs]" as "WPs".
          { iApply big_sepM_union.
            { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
              apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
            iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
          iPoseProof (history_interp_wf with "HI") as "%HistWF".
          iPoseProof ("IH" with "[] [] [] [] [] TF HI MI WPs") as "H".
          1: eauto. 1: eauto. 1: eauto.
          { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
            - inv H. eapply HIST in LUh. eauto.
            - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
              inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
              destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
              rewrite H1 TRn1. eauto. }
          { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
          iModIntro. iFrame.
        * iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                     (match to_val e with
                      | Some v => lift_term j Q v
                      | None => lwp_fix s j ⊤ e (lift_term j Q)
                      end))%I with "[WPs WP Efs]" as "WPs".
          { iApply big_sepM_union.
            { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
              apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
            iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
          iPoseProof (history_interp_wf with "HI") as "%HistWF".
          iPoseProof ("IH" with "[] [] [] [] [] TF HI MI WPs") as "H".
          1: eauto. 1: eauto. 1: eauto.
          { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
            - inv H. eapply HIST in LUh. eauto.
            - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
              inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
              destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
              rewrite H1 TRn1. eauto. }
          { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
          iModIntro. iFrame.
      + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
        inversion TDone. clear TDone. inversion H. clear H. subst Θ0 σ1 ρ2.
        destruct H1 as (He1&<-&<-&->&->). destruct He1 as [v1 He1]. simpl in *.
        rewrite map_union_empty insert_id in TRn1. 2: auto.
        iPoseProof (history_interp_step with "HI") as "[SI ACC]". iMod ("ACC" with "SI") as "HI".
        pose proof (exists_fscnt_next _ _ FS). destruct H as (γ2& FS2& FSrel).
        unfold trace_next in *. simpl in *.
        assert (TNow : trace_thread (n, τf) = i1).
        { unfold trace_thread, trace_state. simpl. rewrite TRn. done. }
        assert (TNA : thread_na i1 (n, τf)).
        { unfold thread_na. simpl. rewrite TRn. right. eauto. }
        rewrite -TNow in TNA. pose proof (owit_inv_lb_step_na_turn _ _ _ _ _ TNA OTA LB FSrel) as LB2.
        iDestruct "MI" as "[MHI MI]". iMod (model_history_interp_step _ _ _ (S n) with "MHI") as "MHI".
        1: lia. 1: reflexivity.
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        iPoseProof ("IH" with "[] [] [] [] [] TF HI [$MHI $MI] WPs") as "H".
        1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H2 TRn1. eauto. }
        1: eauto.
        iApply fupd_mask_intro. 1: set_solver. iIntros "close". iModIntro. iMod "close" as "_". iModIntro. iFrame.
    -

        TODO

lwp_step =
  (s : stuckness) (i : thread_id) (E : coPset) (e1 : expr Λ) 
  (ν : expr Λ -d> thread_pool Λ -d> iPropO Σ),
  (∀ (K : expr Λ → expr Λ) (h : list
                                  (state Λ * thread_pool Λ *
                                   list (observation Λ))) 
     (n : nat) (σ1 : state Λ) (Θ : thread_pool Λ) 
     (κ κs : list (observation Λ)),
     ⌜LanguageCtx K⌝
     → ⌜Θ !! i = Some (K e1)⌝
       → history_interp h n σ1 Θ (κ ++ κs) ={E,∅}=∗
         ⌜match s with
          | NotStuck => reducible i e1 σ1 (dom Θ)
          | MaybeStuck => True
          end⌝ ∗
         ∀ (e2 : expr Λ) (σ2 : state Λ) (efs : thread_pool Λ),
           ⌜prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs⌝ -∗
           @={n,dom Θ,i}=↓ @={n,S n,dom Θ,dom (<[i:=K e2]> Θ) ∪ dom efs}=> 
           ALC
             (|=[S n,dom (<[i:=K e2]> Θ) ∪ dom efs]=>m 
              |={∅,E}=>
                history_interp (h ++ [(σ2, <[i:=K e2]> Θ ∪ efs, κs)]) 
                  (S n) σ2 (<[i:=K e2]> Θ ∪ efs) κs ∗
                ν e2 efs))%I
model_interp_mupd_steps:
    (h : list (nat * obls)) (i : nat) (Ω : obls) (W : witnesses) (n : nat) 
    (Θ : gset positive) (P : iProp Σ),
    (|=[n,Θ]=>m P) -∗
    model_interp h i Ω W n Θ ={∅}=∗
    P ∗
    ∃ (h' : list (nat * obls)) (i' : nat) (Ω' : obls) (W' : witnesses),
      model_interp (h ++ h') (i + i') Ω' W' n Θ
tf_logic_tf_intuit:
    (Φ : tf) (h : list (state Λ * thread_pool Λ * list (observation Λ))) 
    (n : nat) (σ : state Λ) (Θ : thread_pool Λ) (κs : list (observation Λ)) 
    (m : list (nat * obls)) (i : nat) (Ω : obls) (W : witnesses),
    history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ ⟦Φ⟧ₗ
    ⊢ tf_intuit n σ Θ κs i Ω Φ

  Local Opaque tf_intuit.
End proof2.
