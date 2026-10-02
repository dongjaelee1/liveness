From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From lantana.program_logic Require Export language weakestpre.
From lantana.program_logic Require Export temporal_property.

From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.

From lantana.prelude Require Import axioms.

(** * Step-indexed trace connectives

    The in-logic readings of trace properties (temporal_tps.v) are built from these: [ti_always]
    and [ti_until] are guarded fixpoints, the until with a decreasing measure. The second half
    of the file proves the facts about one step of the running system that the guarantee rules
    and the adequacy theorem (temporal_guarantee.v) use. *)
Notation tiProp Λ Σ := (trace Λ → iProp Σ).

Definition ti_atomic `{SI : sidx} {Λ} {Σ} (π : state_pred Λ) : tiProp Λ Σ :=
  λ τ, let '((Θ, σ), _, _) := (τ.2 τ.1) in ⌜state_sat σ Θ π⌝%I.

Definition ti_pure `{SI : sidx} {Λ} {Σ} (P : Prop) : tiProp Λ Σ :=
  λ _, ⌜P⌝%I.

Definition ti_and `{SI : sidx} {Λ} {Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, (P τ) ∧ (Q τ))%I.

Definition ti_or `{SI : sidx} {Λ} {Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, (P τ) ∨ (Q τ))%I.

(** The antecedent is a trace property proper: the step-indexed reading of an implication
    assumes the antecedent at the level of traces. *)
Definition ti_impl `{SI : sidx} {Λ} {Σ} : trProp Λ → tiProp Λ Σ → tiProp Λ Σ :=
  λ P Q, (λ τ, ⌜P τ⌝ → (Q τ))%I.

Definition ti_forall `{SI : sidx} {Λ} {Σ} : ∀ (A : Type), (A → tiProp Λ Σ) → tiProp Λ Σ :=
  λ A P, (λ τ, ∀ (a : A), (P a τ))%I.

Definition ti_exist `{SI : sidx} {Λ} {Σ} : ∀ (A : Type), (A → tiProp Λ Σ) → tiProp Λ Σ :=
  λ A P, (λ τ, ∃ (a : A), (P a τ))%I.

(** 'Always' is a co-inductive fixpoint. *)
Definition ti_always_pre `{SI : sidx} `{!temporalGS Λ Σ} E
  (ti_always : (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  (** Deferred shape: the first fancy update with the later is the check at [τ] (the
      adequacy reads and certifies invariants there), the second with the credits is the
      step; both formulas at [τ] are established after the step, from the certificates. *)
  λ P1 P2 τ, (|={E,∅}=> ▷ |={∅,E}=> |={E,∅}=> ALC (|={∅,E}=>
               ((P1 τ) ∧ (P2 τ) ∧ ti_always P1 P2 (trace_next τ))))%I.

Local Instance ti_always_pre_contractive `{SI : sidx} `{!temporalGS Λ Σ} E : Contractive (ti_always_pre E).
Proof.
  rewrite /ti_always_pre. repeat intro. do 1 (f_equiv). f_contractive. do 4 f_equiv. f_equiv. f_equiv. apply H.
Qed.

Local Definition ti_always_def `{SI : sidx} `{!temporalGS Λ Σ} : tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  fixpoint (ti_always_pre ⊤).
Local Definition ti_always_aux : seal (@ti_always_def). Proof. by eexists. Qed.
Definition ti_always := ti_always_aux.(unseal).
Global Arguments ti_always {SI Λ Σ _}.
Local Lemma ti_always_unseal `{SI : sidx} `{!temporalGS Λ Σ} : ti_always = @ti_always_def SI Λ Σ _.
Proof. rewrite -ti_always_aux.(seal_eq) //. Qed.

Lemma ti_always_unfold `{SI : sidx} `{!temporalGS Λ Σ} (P1 P2 : tiProp Λ Σ) (τ : trace Λ) :
  ti_always P1 P2 τ ⊣⊢ ti_always_pre ⊤ (ti_always) P1 P2 τ.
Proof. rewrite ti_always_unseal. apply (fixpoint_unfold (ti_always_pre ⊤)). Qed.

(** 'Until' is an inductive fixpoint, decreasing argument of Type A. *)
Definition ti_until_pre `{SI : sidx} `{!temporalGS Λ Σ} E
  {A : Type} (ltA : A → A → Prop)
  (ti_until : A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ) :
  A -d> (trace Λ -d> iPropO Σ) -d> (trace Λ -d> iPropO Σ) -d> trace Λ -d> iPropO Σ :=
  (** Deferred shape, as for always: the decision about [τ] is made after the step, and
      the measure for the continuation is chosen then. *)
  λ a P Q τ,
    (|={E,∅}=> ▷ |={∅,E}=> |={E,∅}=> ALC (|={∅,E}=>
       ((Q τ) ∨ ((P τ) ∧ ∃ a', (⌜ltA a' a⌝) ∧ ti_until a' P Q (trace_next τ)))))%I.

Local Instance ti_until_pre_contractive `{SI : sidx} `{!temporalGS Λ Σ} E
  {A : Type} {ltA : A → A → Prop}
  : Contractive (ti_until_pre E ltA).
Proof.
  rewrite /ti_until_pre. repeat intro. do 1 (f_equiv). f_contractive. repeat f_equiv. apply H.
Qed.

Local Definition ti_until_def `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} (ltA : A → A → Prop)
  : A → tiProp Λ Σ → tiProp Λ Σ → tiProp Λ Σ :=
  fixpoint (ti_until_pre ⊤ ltA).
Local Definition ti_until_aux : seal (@ti_until_def). Proof. by eexists. Qed.
Definition ti_until := ti_until_aux.(unseal).
Global Arguments ti_until {SI Λ Σ _ _}.
Local Lemma ti_until_unseal `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} {ltA : A → A → Prop} :
  @ti_until SI Λ Σ _ _ ltA = @ti_until_def SI Λ Σ _ _ ltA.
Proof. rewrite -ti_until_aux.(seal_eq) //. Qed.

Lemma ti_until_unfold `{SI : sidx} `{!temporalGS Λ Σ}
  {A : Type} {ltA : A → A → Prop}
  (a : A) (P Q : tiProp Λ Σ) (τ : trace Λ) :
  ti_until ltA a P Q τ ⊣⊢ ti_until_pre ⊤ ltA (ti_until ltA) a P Q τ.
Proof. rewrite ti_until_unseal. apply (fixpoint_unfold (ti_until_pre ⊤ ltA)). Qed.

(** FIXME: move this to a more general location. *)
Section aux.
  Context `{SI : sidx} `{!invGS Σ}.

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

Global Instance ordSI : sidx := ordI.

(** This cast using 'change' avoids universe inconsistency. *)
Global Instance iProp_sat_lc_SatisfiableExists {Σ}: SatisfiableExists ordinal_ucmra.OrdUR (@iProp_sat _ Σ).
Proof.
  change (ordinal_ucmra.OrdUR: Type) with Ord.t. apply iProp_sat_exists_instance.
Qed.

Section proof1.
  Context `{!temporalGS Λ Σ}.
  Context {A : Type} {ltA : A → A → Prop}.
  Implicit Type F : iProp Σ.

  Lemma ti_always_trace_next F P1 P2 τ :
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 τ) →
    iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 (trace_next τ)).
  Proof.
    intros. rewrite ti_always_unfold /ti_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd, sat_fupd, sat_ALC, sat_fupd in H.
    apply iProp_sat_lc_at_frame_and in H. destruct H as [_ H].
    apply iProp_sat_lc_at_frame_and in H. destruct H as [_ H]. auto.
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
    (∀ τ, iProp_sat_lc_at_frame F ⊤ (P2 τ) → R2 τ) →
    ∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_always P1 P2 τ) → (tr_always (R1 ∧ R2))%R τ.
  Proof.
    intros IH1 IH2 τ H. unfold tr_always. destruct τ as (n&τf).
    (** Use classical logic. *)
    intro m. pattern m. revert m. apply Classical_Pred_Type.not_ex_not_all.
    intros ?. destruct H0. apply Classical_Prop.imply_to_and in H0. destruct H0.
    apply H1. clear H1.
    eapply ti_always_trace_later in H. 2: eauto.
    rewrite ti_always_unfold /ti_always_pre in H.
    apply sat_fupd, sat_later, sat_fupd, sat_fupd, sat_ALC, sat_fupd in H.
    apply iProp_sat_lc_at_frame_and in H. destruct H as [H1 H].
    apply iProp_sat_lc_at_frame_and in H. destruct H as [H2 _].
    split; eauto.
  Qed.

End proof1.

Section proof2.
  Context `{!lantanaGS Λ Σ}.

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

  Lemma get_obls_thread_active_gen (h : list _) n (σ : state Λ) (Θ : thread_pool Λ) (κs : list (observation Λ)) g v Ω W τf :
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    h !! n = Some (σ, Θ, κs) →
    model_interp g v Ω W n (dom Θ) ∗
    ([∗ map] i ↦ e ∈ Θ, match to_val e with
                        | Some _ => (thP_done i)
                        | None => True
                        end)
    ⊢ ⌜obls_thread_active Ω (n, τf)⌝.
  Proof.
    iIntros (HIST Hlu) "(MI& #WPs)". iIntros (k o LUk). destruct o; last eauto.
    unfold thread_active. simpl.
    apply HIST in Hlu. destruct Hlu as (j& Now). unfold ts_emb. simpl. rewrite Now.
    iDestruct "MI" as "(MHI& S& T& A& G& W& %Inv)".
    iPoseProof (othread_assigned_thread_elem with "[$S $T $A]") as "%Tin". 1: eapply LUk.
    apply elem_of_dom in Tin. destruct Tin as (e&LUth).
    iPoseProof (big_sepM_delete _ _ _ _ LUth with "WPs") as "[#WP WPs0]".
    destruct (to_val e) eqn:TVe.
    - iPoseProof (othread_assigned_done_false with "[$S $T $A]") as "%"; eauto.
      unfold_opreds. auto.
    - iPureIntro. exists e. split; auto.
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
    iIntros (HIST EQTQ) "(HI& MI& WPs)".
    iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    iApply (get_obls_thread_active_gen with "[$MI WPs]"). 1: eauto. 1: eauto.
    subst. iApply big_sepM_fmap. iApply (big_sepM_impl with "WPs").
    iIntros "!> %%% H". destruct x. simpl. destruct (to_val e); auto.
    iDestruct "H" as "[$ _]".
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

End proof2.
