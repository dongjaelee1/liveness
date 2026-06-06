From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From liris.program_logic Require Export language weakestpre.
From liris.program_logic Require Export temporal_logic temporal_property.

From transfinite.stepindex Require Import ordinals.
(* From transfinite.base_logic Require Import satisfiable. *)
From liris.base_logic Require Import satisfiable.
From liris.algebra Require Import ordinal_existential_properties.

From liris.prelude Require Import axioms.

(** Lift tf to tp. *)
Fixpoint tf_to_tp `{SI : indexT} {Π : Type} `{Σ : gFunctors} (Φ : @tf _ Π Σ) : @tp Π :=
  match Φ with
  | tf_emp => tp_true
  | tf_atomic π => tp_atomic π
  | tf_pure P => tp_pure P
  | tf_ghost P => tp_true
  | tf_and P Q => tp_and (tf_to_tp P) (tf_to_tp Q)
  | tf_or P Q => tp_or (tf_to_tp P) (tf_to_tp Q)
  | tf_impl P Q => tp_impl P (tf_to_tp Q)
  | tf_forall A P => tp_forall A (λ a, tf_to_tp (P a))
  | tf_exist A P => tp_exist A (λ a, tf_to_tp (P a))
  | tf_sep P Q => tp_and (tf_to_tp P) (tf_to_tp Q)
  | tf_always _ P => tp_always (tf_to_tp P)
  | tf_until _ _ _ _ P Q => tp_until (tf_to_tp P) (tf_to_tp Q)
end.

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
Definition ti_always_pre `{SI : indexT} `{!temporalGS Λ Σ} E
  (ti_always : (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  λ P1 P2 τ, (|={E,∅}=> ▷ |={∅,E}=> ((P1 τ) ∧ |={E,∅}=> (P2 τ) ∧ ALC (|={∅,E}=> ti_always P1 P2 (trace_next τ))))%I.

(** FIXME: hacky proof*)
Local Instance ti_always_pre_contractive `{SI : indexT} `{!temporalGS Λ Σ} E : Contractive (ti_always_pre E).
Proof.
  rewrite /ti_always_pre. repeat intro. do 6 (f_equiv).
  f_contractive. do 1 (f_equiv). repeat red. repeat red in H. eauto.
Qed.

Local Definition ti_always_def `{SI : indexT} `{!temporalGS Λ Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  fixpoint (ti_always_pre ⊤).
Local Definition ti_always_aux : seal (@ti_always_def). Proof. by eexists. Qed.
Definition ti_always := ti_always_aux.(unseal).
Global Arguments ti_always {SI Λ Σ _}.
Local Lemma ti_always_unseal `{SI : indexT} `{!temporalGS Λ Σ} : ti_always = @ti_always_def SI Λ Σ _.
Proof. rewrite -ti_always_aux.(seal_eq) //. Qed.

Lemma ti_always_unfold `{SI : indexT} `{!temporalGS Λ Σ} (P1 P2 : tiProp Λ Σ) (τ : trace Λ) :
  ti_always P1 P2 τ ⊣⊢ ti_always_pre ⊤ (ti_always) P1 P2 τ.
Proof. rewrite ti_always_unseal. apply (fixpoint_unfold (ti_always_pre ⊤)). Qed.

(** 'Until' is an inductive fixpoint, decreasing argument of Type A. *)
Definition ti_until_pre `{SI : indexT} `{!temporalGS Λ Σ} E
  {A : Type} (ltA : A → A → Prop)
  (ti_until : A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  λ a P Q τ,
    (|={E,∅}=> ▷ |={∅,E}=> ((Q τ) ∨ ((P τ) ∧ |={E,∅}=> ∃ a', (⌜ltA a' a⌝) ∧ ALC (|={∅,E}=> ti_until a' P Q (trace_next τ)))))%I.

Local Instance ti_until_pre_contractive `{SI : indexT} `{!temporalGS Λ Σ} E
  {A : Type} {ltA : A → A → Prop}
  : Contractive (ti_until_pre E ltA).
Proof.
  rewrite /ti_until_pre. repeat intro. do 9 (f_equiv).
  (* FIXME: f_equiv not working. *)
  f_contractive. do 1 (f_equiv). eapply dist_ne.
  { eapply H. }
  1,2: reflexivity.
Qed.

Local Definition ti_until_def `{SI : indexT} `{!temporalGS Λ Σ}
  {A : Type} (ltA : A → A → Prop)
  : A → tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  fixpoint (ti_until_pre ⊤ ltA).
Local Definition ti_until_aux : seal (@ti_until_def). Proof. by eexists. Qed.
Definition ti_until := ti_until_aux.(unseal).
Global Arguments ti_until {SI Λ Σ _ _}.
Local Lemma ti_until_unseal `{SI : indexT} `{!temporalGS Λ Σ}
  {A : Type} {ltA : A → A → Prop} :
  @ti_until SI Λ Σ _ _ ltA = @ti_until_def SI Λ Σ _ _ ltA.
Proof. rewrite -ti_until_aux.(seal_eq) //. Qed.

Lemma ti_until_unfold `{SI : indexT} `{!temporalGS Λ Σ}
  {A : Type} {ltA : A → A → Prop}
  (a : A) (P Q : tiProp Λ Σ) (τ : trace Λ) :
  ti_until ltA a P Q τ ⊣⊢ ti_until_pre ⊤ ltA (ti_until ltA) a P Q τ.
Proof. rewrite ti_until_unseal. apply (fixpoint_unfold (ti_until_pre ⊤ ltA)). Qed.

(** Intermediate interpretation. *)
Fixpoint ti_logic `{SI : indexT} `{!temporalGS Λ Σ}
  {A : Type} (ltA : A → A → Prop)
  (Φ : @tp (state_pred Λ)) : tiProp Λ Σ :=
  match Φ with
  | tp_atomic π => (ti_atomic π)%I
  | tp_pure p => ti_pure p
  | tp_and P Q => (ti_and (ti_logic ltA P) (ti_logic ltA Q))
  | tp_or P Q => (ti_or (ti_logic ltA P) (ti_logic ltA Q))
  | tp_impl P Q => (ti_impl P (ti_logic ltA Q))
  | tp_forall A P => (ti_forall A (λ (a : A), ti_logic ltA (P a)))
  | tp_exist A P => (ti_exist A (λ (a : A), ti_logic ltA (P a)))
  | tp_always P => (ti_always (ti_logic ltA P) (ti_pure True))
  | tp_until P Q =>
      (ti_exist A (λ a, ti_until ltA a (ti_logic ltA P) (ti_logic ltA Q)))
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
  Context `{!temporalGS Λ Σ}.
  Context {A : Type} {ltA : A → A → Prop}.
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

  Lemma ti_always_trace_next F P1 P2 τ :
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 τ) →
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 (trace_next τ)).
  Proof.
    intros. rewrite ti_always_unfold /ti_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd in H. apply iProp_sat_lc_at_frame_and in H. destruct H.
    apply sat_fupd in H0. apply iProp_sat_lc_at_frame_and in H0. destruct H0.
    apply sat_ALC, sat_fupd in H1. auto.
  Qed.

  Lemma ti_always_trace_later F P1 P2 n x τf :
    n ≤ x →
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 (n, τf)) →
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 (x, τf)).
  Proof.
    intro LE. induction LE; intros; first auto.
    apply IHLE in H. apply ti_always_trace_next in H. done.
  Qed.

  Lemma ti_always_tr_always F (P1 P2 : tiProp Λ Σ) (R1 R2 : trProp Λ) :
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (P1 τ) → R1 τ) →
    (∀ τ, iProp_sat_lc_at_frame F ∅ (P2 τ) → R2 τ) →
    ∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 τ) → (tr_always (R1 ∧ R2))%R τ.
  Proof.
    intros IH1 IH2 τ H. unfold tr_always. destruct τ as (n&τf).
    (** Use classical logic. *)
    intro m. pattern m. revert m. apply Classical_Pred_Type.not_ex_not_all.
    intros ?. destruct H0. apply Classical_Prop.imply_to_and in H0. destruct H0.
    apply H1. clear H1.
    eapply ti_always_trace_later in H. 2: eauto.
    split.
    - eapply IH1. rewrite ti_always_unfold /ti_always_pre in H.
      apply sat_fupd, sat_later, sat_fupd in H.
      apply iProp_sat_lc_at_frame_and in H. destruct H. auto.
    - eapply IH2. rewrite ti_always_unfold /ti_always_pre in H.
      apply sat_fupd, sat_later, sat_fupd in H.
      apply iProp_sat_lc_at_frame_and in H. destruct H.
      apply sat_fupd in H1. apply iProp_sat_lc_at_frame_and in H1. destruct H1.      
      auto.
  Qed.

  Lemma ti_until_tr_until (wf_ltA : well_founded ltA) F Φ1 Φ2 :
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_logic ltA Φ1 τ) → tp_trace Φ1 τ) →
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_logic ltA Φ2 τ) → tp_trace Φ2 τ) →
    ∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_exist A (λ a, ti_until ltA a (ti_logic ltA Φ1) (ti_logic ltA Φ2)) τ) →
         tr_until (tp_trace Φ1) (tp_trace Φ2) τ.
  Proof.
    intros IH1 IH2 τ H. unfold tr_until. destruct τ as (n&τf).
    unfold ti_exist in H. apply sat_exists in H. destruct H.
    revert n τf H. induction x as [a IHa] using (well_founded_ind wf_ltA). intros.
    rewrite ti_until_unfold /ti_until_pre in H.
    apply sat_fupd, sat_later, sat_fupd in H. apply sat_or in H. destruct H.
    { apply IH2 in H. exists n. split_and !; eauto. intros. lia. }
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

  Lemma ti_logic_tp_trace (wf_ltA : well_founded ltA) (F : iProp Σ) (Φ : tp) (τ : trace Λ) :
    iProp_sat_lc_at_frame F ⊤ (ti_logic ltA Φ τ) → tp_trace Φ τ.
  Proof.
    revert τ. induction Φ; simpl; intros.
    - unfold ti_atomic in H. destruct τ. simpl in H.
      unfold tr_atomic, ts_emb, ts_atomic. simpl. destruct (t n) as (((Θ&σ)&?)&?).
      apply sat_elim in H. auto.
    - unfold ti_pure in H. apply sat_elim in H. auto.
    - unfold ti_and in H. apply iProp_sat_lc_at_frame_and in H. destruct H.
      apply IHΦ1 in H. apply IHΦ2 in H0. split; auto.
    - unfold ti_or in H. apply sat_or in H. destruct H.
      + apply IHΦ1 in H. left. auto.
      + apply IHΦ2 in H. right. auto.
    - unfold tr_impl. intros HP. unfold ti_impl in H. apply sat_impl in H; auto.
    - unfold tr_forall. intros. unfold ti_forall in H0. apply (sat_forall a) in H0. eauto.
    - unfold tr_exist. unfold ti_exist in H0. apply (sat_exists) in H0. destruct H0. eauto.
    - cut (tr_always (tp_trace Φ ∧ tr_pure True)%R τ).
      + unfold tr_always. destruct τ. intros. eapply H0 in H1. destruct H1. auto.
      + eapply ti_always_tr_always; eauto. done.
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
                       | obl_assigned _ i => ts_emb (thread_active i) τ
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
                                  | witness_discharged => False
                                  end
             | obl_discharged => match w' with
                               | witness_assigned _ => False
                               | witness_discharged => True
                               end
             end) ∧
            (match o2 with
             | obl_assigned a i => match w' with
                                  | witness_assigned b => (fair_sched_fun γ2 i a) w≤ b
                                  | witness_discharged => False
                                  end
             | obl_discharged => match w' with
                               | witness_assigned _ => False
                               | witness_discharged => True
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
        exists (witness_discharged). split_and !; auto.
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
    apply HIST in Hlu. destruct Hlu as (j& Now). unfold ts_emb. simpl. rewrite Now.
    iDestruct "MI" as "(MHI& S& T& A& G& W& %Inv)".
    iPoseProof (othread_assigned_thread_elem with "[$S $T $A]") as "%Tin". 1: eapply LUk.
    apply elem_of_dom in Tin. destruct Tin as (e&LUth).
    rewrite EQTQ lookup_fmap_Some in LUth. destruct LUth as (?& EQe& LUth).
    destruct x as (?&Q). simpl in EQe. subst e0.
    iPoseProof (big_sepM_delete _ _ _ _ LUth with "WPs") as "[WP WPs]".
    destruct (to_val e) eqn:TVe.
    - iDestruct "WP" as "(#Term& HQ)". iPoseProof (othread_assigned_done_false with "[$S $T $A]") as "%"; eauto.
      unfold_opreds. auto.
    - iPureIntro. exists e. split; auto. subst. rewrite lookup_fmap LUth. done.
  Qed.

  Lemma owit_inv_lb_step_na_turn τ Ω W γ1 γ2 :
    ts_emb (thread_na (trace_thread τ)) τ →
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

  Lemma lwp_fix_ti_logic s h n σ Θ (TQ : gmap thread_id ((expr Λ) * (thread_id → val Λ → iProp Σ))) κs
    g v1 v2 Ω1 Ω2 W τf γ (Φ : tp) :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    v1 ≤ v2 →
    obls_le Ω1 Ω2 →
    owit_inv_lb (fair_sched_fun γ) Ω2 W →
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    Θ = fst <$> TQ →
    (∃ (Φ' : tf Σ), ⌜ tf_to_tp Φ' = Φ ⌝ ∧
    (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v2 Ω2 W n (dom Θ) ∗
    ([∗ map] i ↦ '(e, Q) ∈ TQ, match to_val e with
                               | Some v => (lift_term i Q) v
                               | None => lwp_fix s i ⊤ e (lift_term i Q)
                               end) ∗
    tf_intuit n σ Θ κs v1 Ω1 Φ')
    ⊢ ti_logic Ord.lt Φ (n, τf).
  Proof.
    iIntros (BEH FS LEv LEO LB HIST EQTQ) "(%& %& H)". subst Φ. rename Φ' into Φ.
    iStopProof. revert BEH FS LEv LEO LB HIST EQTQ.
    revert h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ.
    induction Φ; iIntros (h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ BEH FS LEv LEO LB HIST EQTQ) "([HI SIa]& MI& WPs& #TF)"; simpl.
    - done.
    - unfold ti_atomic. iPoseProof (event_pred_history_interp_lookup with "[$HI $TF]") as "%". destruct H.
      simpl. apply HIST in H. destruct H. rewrite H. auto.
    - unfold ti_pure. done.
    - done.
    - unfold ti_and. iSplit.
      + iDestruct "TF" as "[TF _]". iApply (IHΦ1 with "[$HI $SIa $MI $WPs $TF]"); eauto.
      + iDestruct "TF" as "[_ TF]". iApply (IHΦ2 with "[$HI $SIa $MI $WPs $TF]"); eauto.
    - unfold ti_or. iDestruct "TF" as "[TF | TF]".
      + iLeft. iApply (IHΦ1 with "[$HI $SIa $MI $WPs $TF]"); eauto.
      + iRight. iApply (IHΦ2 with "[$HI $SIa $MI $WPs $TF]"); eauto.
    - unfold ti_impl. iIntros "HP". iPoseProof ("TF" with "HP") as "#TF'".
      iApply (IHΦ with "[$HI $SIa $MI $WPs $TF']"); eauto.
    - unfold ti_forall. iIntros (?). iSpecialize ("TF" $! a).
      iApply (H with "[$HI $SIa $MI $WPs $TF]"); eauto.
    - unfold ti_exist. iDestruct "TF" as "(%& TF)". iExists a.
      iApply (H with "[$HI $SIa $MI $WPs $TF]"); eauto.
    - unfold ti_and. iDestruct "TF" as "[TF1 TF2]". iSplit.
      + iApply (IHΦ1 with "[$HI $SIa $MI $WPs $TF1]"); eauto.
      + iApply (IHΦ2 with "[$HI $SIa $MI $WPs $TF2]"); eauto.
    - clear dependent v1 Ω1. rename v2 into v, Ω2 into Ω.
      iRevert (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ) "TF HI SIa MI WPs".
      iLöb as "IH". iIntros (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ) "#TF HI SIa MI WPs".
      rewrite ti_always_unfold /ti_always_pre.
      iMod (inv_acc with "TF") as "[HP ACC]". 1: set_solver.
      iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext.
      iPoseProof (tf_logic_tf_intuit with "[$HI $MI $HP]") as "#TFP".
      iMod "close" as "_". iMod ("ACC" with "HP") as "_". iModIntro. iSplit.
      { iApply (IHΦ with "[$HI $SIa $MI $WPs $TFP]"); eauto. done. }
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
        iMod ("WP" $! id with "[] [//] [$HI $SIa]") as "[%NStuck WP]".
        { iPureIntro. apply _. }
        iPoseProof ("WP" with "[//]") as "WP". rewrite /mprog.
        iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
        iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
        unshelve epose proof (mprog_exists_step i1 Ω Ω2 W (n, τf) γ _ OTA OWinv LB FS ProgO).
        { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
        destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
        iMod ("WP" $! W2 with "[]") as "[MI WP]".
        { iPureIntro. split; auto. }
        rewrite /mphys. iMod ("WP" with "MI") as "[MI WP]". iModIntro. iSplit. 1: done.
        iMod "WP". simpl.
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
          iDestruct "HI" as "[HI SIa]".
          iPoseProof (history_interp_wf with "HI") as "%HistWF".
          iPoseProof ("IH" with "[] [] [] [] [] TF HI SIa MI WPs") as "H".
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
          iDestruct "HI" as "[HI SIa]".
          iPoseProof (history_interp_wf with "HI") as "%HistWF".
          iPoseProof ("IH" with "[] [] [] [] [] TF HI SIa MI WPs") as "H".
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
        { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
        assert (TNA : ts_emb (thread_na i1) (n, τf)).
        { unfold ts_emb, thread_na. simpl. rewrite TRn. right. eauto. }
        rewrite -TNow in TNA. pose proof (owit_inv_lb_step_na_turn _ _ _ _ _ TNA OTA LB FSrel) as LB2.
        iDestruct "MI" as "[MHI MI]". iMod (model_history_interp_step _ _ _ (S n) with "MHI") as "MHI".
        1: lia. 1: reflexivity.
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        iPoseProof ("IH" with "[] [] [] [] [] TF HI SIa [$MHI $MI] WPs") as "H".
        1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H2 TRn1. eauto. }
        1: eauto.
        iApply fupd_mask_intro. 1: set_solver. iIntros "close". iSplit. 1: done.
        iModIntro. iMod "close" as "_". iModIntro. iFrame.
    - rewrite /ti_exist. iDestruct "TF" as "[(%&%&#EA) #TF]".
      iPoseProof (event_obl_model_history_interp_lookup with "[MI $EA]") as "%".
      { iDestruct "MI" as "[$ _]". }
      simpl in H. destruct H as (LUMHv1& LUOk1& _). pose proof LEO as LEO2. destruct LEO2. clear H0.
      assert (is_Some (Ω2 !! k)).
      { apply elem_of_dom. apply elem_of_dom_2 in LUOk1. set_solver + LUOk1 H. }
      clear H. destruct H0 as [x LUOk2]. destruct x; cycle 1.
      { clear IHΦ1. iExists Ord.O. rewrite ti_until_unfold /ti_until_pre. iLeft.
        iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
        iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
        iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]".
        { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
          iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk2 in H. inv H. }
        { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
          iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk2 in H. inv H. }
        iDestruct "Var" as "(#Of& %&%&%&%&%&%& #EF& #HE& #TF2)".
        iPoseProof (event_obl_model_history_interp_lookup with "[MI $EF]") as "%".
        { iDestruct "MI" as "[$ _]". }
        simpl in H. destruct H as (LUMHi'& LUOk'& LEi'& LEn'& LEO').
        destruct (le_gt_dec v1 i'); cycle 1.
        { iPoseProof (event_obl_compare i' v1 with "[$EF $EA]") as "%". 1: lia.
          simpl in H. destruct H as (?&?&?). done. }
        iPoseProof (event_obl_compare v1 i' with "[$EA $EF]") as "%". 1: auto.
        simpl in H. destruct H as (LEn'2& LEO'2& _). rename l into LEv1.
        assert (n' = n) by lia. subst n'. clear LEn' LEn'2.
        iPoseProof (history_interp_hG_event_lookup with "[$HI $HE]") as "%".
        iPoseProof (history_interp_lookup with "HI") as "%". rewrite H in H0. inversion H0. clear H H0. subst σ' Θ' κs'.
        iPoseProof (IHΦ2 with "[$HI $SIa $MI $WPs $TF2]") as "HA".
        1: eapply BEH. 1: eapply FS. 1,2,3,4,5: eauto.
        iMod ("ACC" with "[]") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of EF HE TF2". }
        iModIntro. iFrame. }
      iClear "EA". clear dependent Ω1 f o v1. rename v2 into v, Ω2 into Ω, LUOk2 into LUOk.
      pose proof LB. specialize (H k). rewrite LUOk in H. inversion H. clear H. destruct y; last done. subst x.
      rename H1 into LUWk, H2 into LEwit. symmetry in LUWk.
      iExists wit. clear LUWk.
      (** Induction on wit. *)
      clear b q. iRevert (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ fuel owner LUOk LEwit) "TF HI SIa MI WPs".
      iInduction wit as [w IH] using (well_founded_ind Ord.lt_well_founded).
      iIntros (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ fuel owner LUOk LEwit) "#TF HI SIa MI WPs".
      rewrite ti_until_unfold /ti_until_pre.
      iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
      iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
      iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]"; cycle 1.
      { iPoseProof (tf_logic_tf_intuit with "[$HI $MI $HQ]") as "#TFQ". iMod ("ACC" with "[Var HQ]") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame. }
        iModIntro. iLeft. iApply (IHΦ2 with "[$HI $SIa $MI $WPs $TFQ]"); eauto. done. }
      { iDestruct "Var" as "[OF _]". iDestruct "MI" as "(MHI& S& MI)".
        iEval (unfold_opreds) in "OF". iDestruct "OF" as "(#OE& #OF)".
        iPoseProof (osat_lookup_discharged with "[$S $OE $OF]") as "%". rewrite LUOk in H. inv H. }
      iPoseProof (tf_logic_tf_intuit with "[$HI $MI $HP]") as "#TFP". iMod ("ACC" with "[Var HP]") as "_".
      { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
      iModIntro. iRight. iSplit.
      { iApply (IHΦ1 with "[$HI $SIa $MI $WPs $TFP]"); eauto. done. }
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
        iMod ("WP" $! id with "[] [//] [$HI $SIa]") as "[%NStuck WP]".
        { iPureIntro. apply _. }
        iPoseProof ("WP" with "[//]") as "WP". rewrite /mprog.
        iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
        iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
        unshelve epose proof (mprog_exists_step i1 Ω Ω2 W (n, τf) γ _ OTA OWinv LB FS ProgO).
        { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
        destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
        iMod ("WP" $! W2 with "[]") as "[MI WP]".
        { iPureIntro. split; auto. }
        assert (∃ fuel' owner', Ω2 !! k = Some (obl_assigned fuel' owner')).
        { destruct ProgO. specialize (H0 k). rewrite LUOk in H0. inv H0. destruct y; last done. eauto. }
        destruct H as (fuel2&owner2&LUOk2).
        destruct (ts_emb_thread_active_or_not owner2 (n, τf)) as [TN2 | TA2].
        { iExFalso. iDestruct "MI" as "(MHI& S& T& A& G& W& %OWInv)".
          unfold ts_emb, thread_na in TN2. simpl in TN2. rewrite TRn in TN2.
          iPoseProof (othread_assigned_thread_elem with "[$S $T $A]") as "%INk". 1: eapply LUOk2.
          destruct TN2.
          { apply not_elem_of_dom in H. done. }
          destruct H as (?&?&?). destruct H0. destruct (decide (i1 = owner2)).
          { subst i1. rewrite LUTi1 in H. inv H. }
          assert (LUTQ2 : ∃ Q2, TQ !! owner2 = Some (x, Q2)).
          { subst Θ. rewrite lookup_fmap_Some in H. destruct H as (?&?&?). destruct x1. subst. eauto. }
          destruct LUTQ2 as (Q2& LUTQ2). assert (delete i1 TQ !! owner2 = Some (x, Q2)).
          { rewrite lookup_delete_ne; auto. }
          iPoseProof (big_sepM_delete _ _ _ _ H1 with "WPs") as "[WP' WPs]". rewrite H0.
          iDestruct "WP'" as "(#Term& HQ)". iPoseProof (othread_assigned_done_false with "[$S $T $A]") as "%"; eauto.
          unfold_opreds. auto. }
        (** Resume the step. *)
        rewrite /mphys. iMod ("WP" with "MI") as "[MI WP]". iModIntro.
        (** Checkpoint Ω2 is asssigend. *)
        iPoseProof (model_history_interp_event_obl_now with "[MI]") as "#EA".
        1: eapply LUOk2.
        { iDestruct "MI" as "[$ _]". }
        assert (Drop : (fair_sched_fun γ2 owner2 fuel2 < fair_sched_fun γ owner fuel)%ord).
        { destruct ProgO as [StepO KeepO]. specialize (StepO k). rewrite LUOk LUOk2 in StepO. inv StepO. simpl in H1. destruct H1.
          - destruct H. subst i1. inv H0; inv H. apply fair_sched_fun_mon_gen; auto.
          - destruct H. inv H0. specialize (FSrel owner2). unfold fscnt_next_rel_th in FSrel.
            rewrite decide_False in FSrel; cycle 1.
            { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
            rewrite decide_False in FSrel.
            { apply Hessenberg.lt_add_r. apply OrdArith.lt_from_nat. auto. }
            intros F. eapply (thread_active_and_not_false _ _ F TA2). }
        assert (Dropw : (fair_sched_fun γ2 owner2 fuel2 < w)%ord).
        { eapply Ord.lt_le_lt; last eapply LEwit. auto. }
        iExists _. iSplit; first eauto.
        iMod "WP". simpl.
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
          iDestruct "HI" as "[HI SIa]".
          iPoseProof (history_interp_wf with "HI") as "%HistWF".
          assert (LEO5 : obls_le Ω2 Ω5).
          { etrans; first eauto. etrans; first eauto. eauto. }          
          destruct (Ω5 !! k) eqn:LUOk5; cycle 1.
          { apply elem_of_dom_2 in LUOk2. destruct LEO5. apply not_elem_of_dom in LUOk5. set_solver + LUOk2 H LUOk5. }
          destruct o.
          { iPoseProof ("IH" $! (fair_sched_fun γ2 owner2 fuel2) with "[] [] [] [] [] [] [] [] TF HI SIa MI WPs") as "H".
            1: eauto. 1: eauto. 1: eauto. 1: eauto.
            { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
              - inv H. eapply HIST in LUh. eauto.
              - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
                inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
                destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
                rewrite H1 TRn1. eauto. }
            { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
            1: eauto.
            { iPureIntro. destruct LEO5. specialize (H0 _ _ _ LUOk2 LUOk5). destruct H0.
              - destruct H0. subst. apply Hessenberg.le_add_l, Jacobsthal.le_mult_r. auto.
              - eapply Ord.lt_le, fair_sched_fun_mon_gen. auto. }
            iModIntro. iFrame. }
          { clear IHΦ1. iModIntro. rewrite ti_until_unfold /ti_until_pre. iLeft.
            iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
            iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
            iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]".
            { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
              iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk5 in H. inv H. }
            { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
              iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk5 in H. inv H. }
            iDestruct "Var" as "(#Of& %&%&%&%&%&%& #EF& #HE& #TF2)".
            iPoseProof (event_obl_model_history_interp_lookup with "[MI $EF]") as "%".
            { iDestruct "MI" as "[$ _]". }
            simpl in H. destruct H as (LUMHi'& LUOk'& LEi'& LEn'& LEO').
            destruct (le_gt_dec (S (S v)) i'); cycle 1.
            { iPoseProof (event_obl_compare i' (S (S v)) with "[$EF $EA]") as "%". 1: lia.
              simpl in H. destruct H as (?&?&?). done. }
            iPoseProof (event_obl_compare (S (S v)) i' with "[$EA $EF]") as "%". 1: auto.
            simpl in H. destruct H as (LEn'2& LEO'2& _). rename l into LEv1.
            assert (n' = S n) by lia. subst n'. clear LEn' LEn'2.
            iPoseProof (history_interp_hG_event_lookup with "[$HI $HE]") as "%".
            iPoseProof (history_interp_lookup with "HI") as "%". rewrite H in H0. inversion H0. clear H H0. subst σ' Θ' κs'.
            iPoseProof (IHΦ2 with "[$HI $SIa $MI $WPs $TF2]") as "HA".
            1: eapply BEH. 1: eapply FS2. 1,2,3,4,5: eauto.
            { intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
              - inv H. eapply HIST in LUh. eauto.
              - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
                inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
                destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
                rewrite H1 TRn1. eauto. }
            { subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
            iMod ("ACC" with "[]") as "_".
            { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of EF HE TF2". }
            iModIntro. iFrame. }
        * iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                     (match to_val e with
                      | Some v => lift_term j Q v
                      | None => lwp_fix s j ⊤ e (lift_term j Q)
                      end))%I with "[WPs WP Efs]" as "WPs".
          { iApply big_sepM_union.
            { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
              apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
            iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
          iDestruct "HI" as "[HI SIa]".
          iPoseProof (history_interp_wf with "HI") as "%HistWF".
          assert (LEO4 : obls_le Ω2 Ω4).
          { etrans; first eauto. eauto. }
          destruct (Ω4 !! k) eqn:LUOk4; cycle 1.
          { apply elem_of_dom_2 in LUOk2. destruct LEO4. apply not_elem_of_dom in LUOk4. set_solver + LUOk2 H LUOk4. }
          destruct o.
          { iPoseProof ("IH" $! (fair_sched_fun γ2 owner2 fuel2) with "[] [] [] [] [] [] [] [] TF HI SIa MI WPs") as "H".
            1: eauto. 1: eauto. 1: eauto. 1: eauto.
            { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
              - inv H. eapply HIST in LUh. eauto.
              - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
                inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
                destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
                rewrite H1 TRn1. eauto. }
            { iPureIntro. subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
            1: eauto.
            { iPureIntro. destruct LEO4. specialize (H0 _ _ _ LUOk2 LUOk4). destruct H0.
              - destruct H0. subst. apply Hessenberg.le_add_l, Jacobsthal.le_mult_r. auto.
              - eapply Ord.lt_le, fair_sched_fun_mon_gen. auto. }
            iModIntro. iFrame. }
          { clear IHΦ1. iModIntro. rewrite ti_until_unfold /ti_until_pre. iLeft.
            iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
            iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
            iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]".
            { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
              iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk4 in H. inv H. }
            { iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Var". iDestruct "Var" as "[#Oe Oa]".
              iPoseProof (osat_lookup_assigned with "[$S $Oe $Oa]") as "(%&%&%)". rewrite LUOk4 in H. inv H. }
            iDestruct "Var" as "(#Of& %&%&%&%&%&%& #EF& #HE& #TF2)".
            iPoseProof (event_obl_model_history_interp_lookup with "[MI $EF]") as "%".
            { iDestruct "MI" as "[$ _]". }
            simpl in H. destruct H as (LUMHi'& LUOk'& LEi'& LEn'& LEO').
            destruct (le_gt_dec (S (S v)) i'); cycle 1.
            { iPoseProof (event_obl_compare i' (S (S v)) with "[$EF $EA]") as "%". 1: lia.
              simpl in H. destruct H as (?&?&?). done. }
            iPoseProof (event_obl_compare (S (S v)) i' with "[$EA $EF]") as "%". 1: auto.
            simpl in H. destruct H as (LEn'2& LEO'2& _). rename l into LEv1.
            assert (n' = S n) by lia. subst n'. clear LEn' LEn'2.
            iPoseProof (history_interp_hG_event_lookup with "[$HI $HE]") as "%".
            iPoseProof (history_interp_lookup with "HI") as "%". rewrite H in H0. inversion H0. clear H H0. subst σ' Θ' κs'.
            iPoseProof (IHΦ2 with "[$HI $SIa $MI $WPs $TF2]") as "HA".
            1: eapply BEH. 1: eapply FS2. 1,2,3,4,5: eauto.
            { intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
              - inv H. eapply HIST in LUh. eauto.
              - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
                inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
                destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
                rewrite H1 TRn1. eauto. }
            { subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
            iMod ("ACC" with "[]") as "_".
            { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of EF HE TF2". }
            iModIntro. iFrame. }
      + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
        inversion TDone. clear TDone. inversion H. clear H. subst Θ0 σ1 ρ2.
        destruct H1 as (He1&<-&<-&->&->). destruct He1 as [v1 He1]. simpl in *.
        rewrite map_union_empty insert_id in TRn1. 2: auto.
        iPoseProof (history_interp_step with "HI") as "[SI ACC]". iMod ("ACC" with "SI") as "HI".
        pose proof (exists_fscnt_next _ _ FS). destruct H as (γ2& FS2& FSrel).
        unfold trace_next in *. simpl in *.
        assert (TNow : trace_thread (n, τf) = i1).
        { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
        assert (TNA : ts_emb (thread_na i1) (n, τf)).
        { unfold ts_emb, thread_na. simpl. rewrite TRn. right. eauto. }
        rewrite -TNow in TNA. pose proof (owit_inv_lb_step_na_turn _ _ _ _ _ TNA OTA LB FSrel) as LB2.
        iDestruct "MI" as "[MHI MI]". iMod (model_history_interp_step _ _ _ (S n) with "MHI") as "MHI".
        1: lia. 1: reflexivity.
        iPoseProof (history_interp_wf with "HI") as "%HistWF".
        assert (Drop : (fair_sched_fun γ2 owner fuel < fair_sched_fun γ owner fuel)%ord).
        { apply Hessenberg.lt_add_r, OrdArith.lt_from_nat.
          specialize (FSrel owner). unfold fscnt_next_rel_th in FSrel.
          specialize (OTA k _ LUOk). simpl in OTA.
          rewrite decide_False in FSrel; cycle 1.
          { intros F. subst. eapply (thread_active_and_not_false _ _ TNA OTA). }
          rewrite decide_False in FSrel; auto.
          intros F. eapply (thread_active_and_not_false _ _ F OTA). }
        assert (Dropw : (fair_sched_fun γ2 owner fuel < w)%ord).
        { eapply Ord.lt_le_lt; last eapply LEwit. auto. }
        iApply fupd_mask_intro. 1: set_solver. iIntros "close".
        iExists _. iSplit; first eauto. iModIntro. iMod "close" as "_". iModIntro.
        iPoseProof ("IH" $! (fair_sched_fun γ2 owner fuel) with "[] [] [] [] [] [] [] [] TF HI SIa [$MHI $MI] WPs") as "H".
        1: eauto. 1: eauto. 1: eauto. 1: eauto.
        { iPureIntro. intros. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
          - inv H. eapply HIST in LUh. eauto.
          - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
            inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
            destruct HistWF. rewrite length_app in H. simpl in H. assert (length h = S n) by lia.
            rewrite H2 TRn1. eauto. }
        1: eauto. 1: eauto. 1: done.
        iFrame.
  Qed.

  Lemma lwp_ti_logic s h n σ Θ (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)) κs g v Ω W τf γ (Φ : tp) :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    owit_inv_lb (fair_sched_fun γ) Ω W →
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    ((history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗
      model_interp g v Ω W n (dom Θ) ∗
      (|={⊤}=>m ∃ (Φ' : tf Σ), (⌜ tf_to_tp Φ' = Φ ⌝) ∗ ⟦Φ'⟧ₗ ∗ (⟦Φ'⟧ₗ -∗ |={⊤}=>m [∗ map] i↦e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ v, lift_term i Ψ v }}))))
      ⊢ |={⊤}=> ti_logic Ord.lt Φ (n, τf).
  Proof.
    iIntros (BEH FS LB HIST) "([HI SIa]& MI& WPs)".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "((%& %HΦ& P& WPs)& HI& %&%&%&%& %& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO1 LB1].
    iPoseProof (tf_logic_tf_intuit with "[$HI $MI $P]") as "#TF".
    iPoseProof ("WPs" with "P") as "WPs".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "(WPs& HI& %&%&%&%& %& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO2 LB2].
    iPoseProof (big_sepM2_alt with "WPs") as "[%Dom WPs]".
    remember (map_zip Θ Ψs) as TQ. assert (EQTQ : Θ = fst <$> TQ).
    { subst. rewrite fst_map_zip; auto. intro k. rewrite -!elem_of_dom Dom. auto. }
    iAssert ([∗ map] i↦'(e, Q) ∈ TQ,
               lwpupd i ⊤ e (match to_val e with
                             | Some v => (lift_term i Q) v
                             | None => lwp_fix s i ⊤ e (lift_term i Q)
                             end))%I with "[WPs]" as "WPs".
    { iApply (big_sepM_impl with "WPs"). iIntros "!> %%% H". destruct x.
      rewrite lwp_unfold_fix. iEval (rewrite lwp_fix_unfold_fix /lwp_pre) in "H".
      simpl. destruct (to_val e) eqn:He.
      - rewrite lwpupd_trans. iFrame.
      - rewrite lwp_fix_unfold_fix /lwp_pre He. iFrame. }
    iMod (all_interp_lwpupd_steps_gmap γ with "WPs [$HI $SIa] MI") as "(WPs& HI& %&%&%&%& %& MI)".
    { subst Θ. done. }
    { auto. }
    destruct H as [LEO3 LB3].
    iPoseProof (lwp_fix_ti_logic with "[$HI $MI $WPs $TF]") as "$".
    1,2: eauto. 1: lia. all: eauto. etrans; eauto.
  Qed.

  Local Opaque tf_intuit.
End proof2.

Theorem lwp_adequacy (Σ : gFunctors) (Λ : language)
  `{!mupdGpreS Σ} `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))}
  s σ Θ i κs (Φ : tp) :
  ∀ (τ : trace Λ),
  behavior τ →
  fair_scheduling τ →
  (τ.1 = 0) →
  (τ.2 0 = (Θ, σ, i, κs)) →
  (∀ `{Htemporal : !temporalGS Λ Σ},
     ∃ (c : Ord.t),
     ⊢ |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                (fork_post : thread_id → val Λ → iProp Σ)
                (* FIXME: cannot unify pos_countable for some reason *)
                (Ψs : gmap thread_id (H:=pos_countable) (thread_id → val Λ → iProp Σ)),
     let _ : lirisGS Λ Σ := LirisG Htemporal Hsic fork_post in
     state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
     (£ c -∗ ([∗ set] i ∈ dom Θ, thP_groups i ∅) -∗
      |={⊤}=>m (∃ (Φ' : tf Σ),
                  (⌜ tf_to_tp Φ' = Φ ⌝) ∗ (⟦Φ'⟧ₗ) ∗
                  (⟦Φ'⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))) →
  tp_trace Φ τ.
Proof.
  intros τ BEH FS INIT1 INIT2 Hwp.
  assert (iProp_sat
            (|==> ∃ (Hmupd : mupdGS Σ) (Hhist : histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))),
                let _ : temporalGS Λ Σ := TemporalG Hmupd Hhist in
                (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗
                wsat.wsat ∗ wsat.ownE ⊤ ∗
                |={⊤}=> ti_logic Ord.lt Φ τ)); cycle 1.
  { apply sat_bupd, sat_exists in H0. destruct H0 as (Hmupd& ?). apply sat_exists in H0. destruct H0 as (Hhist& ?).
    set (Htemp := TemporalG Hmupd Hhist : temporalGS Λ Σ).
    apply (ti_logic_tp_trace Ord.lt_well_founded emp). apply (sat_fupd ⊤).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono. 2: eapply H0. simpl. iIntros "($& $& $& $)". }
  assert (Hwp' : ⊢ ∀ Htemporal : temporalGS Λ Σ,
            ∃ (c : Ord.t),
            |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                     (fork_post : thread_id → val Λ → iProp Σ)
                     (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)),
            let _ : lirisGS Λ Σ := LirisG Htemporal Hsic fork_post in
            state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
            (£ c -∗ ([∗ set] i ∈ dom Θ, thP_groups i ∅) -∗
             |={⊤}=>m (∃ (Φ' : tf Σ), (⌜ tf_to_tp Φ' = Φ ⌝) ∗ (⟦Φ'⟧ₗ) ∗
                                     (⟦Φ'⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))).
  { iIntros (Htemp). destruct (Hwp Htemp). iExists x. iApply H0. }
  eapply sat_wand; cycle 1.
  { eapply Hwp'. }
  apply (sat_mono True); cycle 1.
  { apply iProp_sat_intro. }
  iIntros "_ H".
  iMod (model_interp_alloc 0) as "(%Hmupd& R& W& WOE& MI)".
  iMod (history_interp_init σ Θ κs) as "(%Hhist& HI)".
  iExists Hmupd, Hhist.
  set (Htemp := TemporalG Hmupd Hhist : temporalGS Λ Σ).
  iDestruct ("H" $! Htemp) as "(%& H)".
  iDestruct "R" as "(%x& R)".
  iMod (own_update _ (● x) with "R") as "[R LC]".
  { apply (auth_update_alloc x ((c : ordinal_ucmra.OrdUR) ⋅ x)).
    apply (op_local_update_discrete x ε c).
    intros ?. apply auth_valid_trivial. }
  iModIntro. iFrame "R W WOE". rewrite (right_id ε).
  iMod "H" as "(%Hsic& %fork_post& %Ψs& SI& SIa& WPs)".
  iMod ("HI" $! Hsic with "SI") as "HI". iDestruct "MI" as "(MHI& S& T& A& G& MI)".
  iMod (thP_groups_alloc_threads (dom Θ) with "[$T $G]") as "(T& G& Ths)". 1: set_solver.
  iPoseProof ("WPs" with "LC Ths") as "WPs". rewrite union_empty_l_L.
  destruct τ as [n τf]. simpl in INIT1, INIT2. subst n.
  apply fair_scheduling_fscnt in FS. destruct FS as (γ& FS).
  set (Hliris := LirisG Htemp Hsic fork_post : lirisGS Λ Σ).
  (* FIXME: just HI not working. *)
  iApply (lwp_ti_logic with "[$HI $SIa $MHI $S $T $A $G $MI $WPs]").
  1,2: eauto. 1: apply map_Forall2_empty.
  { intros. rewrite lookup_cons in H0. destruct n'; last done. inv H0. rewrite INIT2. eauto. }
Qed.

(* Print Assumptions lwp_adequacy. *)
