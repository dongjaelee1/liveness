From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.program_logic Require Export adequacy.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.
From lantana.prelude Require Import axioms.

(** * Temporal guarantees

    Temporal formulas are ordinary iProps. What makes an iProp [P] temporal is a separate,
    persistent iProp [P ⊨ₜ G] stating that, whenever [P] holds, the rest of the execution
    satisfies the trace property [G]. Hence quantifiers are iProp's own (over any type, e.g.
    over iProp or over guaranteed iProps), temporal formulas can be stored in invariants and
    saved propositions, and program proofs never leave iProp.

    Trace properties are semantic ([tps]): a step-indexed trace predicate [tps_ti], which is
    what the program logic establishes, together with a trace property [tps_tr] that it
    soundly approximates. Adequacy concludes [tps_tr G], and hence anything it implies.

    Limitations, by design:
    - A quantifier can be trace-visible ([tps_exist]) only over types with the existential
      property of the step index (nat, Z, loc, gname, ...): over larger types (iProp, tps) no
      sound adequacy could read the witness off the trace. Over those, existentials are ghost
      ([temporal_exist_ghost]): the guarantee of the body must not depend on the witness.
    - The trace property [G] of the adequacy is fixed at the meta level; dynamically created
      names reach it through trace-visible existentials, typically under a [finally]
      allocated at time 0 (see lantana_heap_lang/examples/flag_fork.v).
    - [tguar] mentions the running system ([lwp_fix]), so this layer is specific to Lantana's
      weakest precondition and to [ordSI].
    - Recursion through trace-visible positions (e.g. an until whose right side refers to the
      formula itself) has no fixed trace property; guarded recursion is supported when the
      guarantee is fixed ([temporal_always_later], [temporal_until_later], Löb). *)

(** ** Semantic trace properties *)

(** [tps_ti] is the trace predicate that the running system establishes inside the logic
    (cf. [ti_logic]); [tps_good] says that its satisfiability implies [tps_tr]
    (cf. [ti_logic_tp_trace]). *)
Record tps {Λ : language} {Σ : gFunctors} := Tps {
  tps_ti : ∀ `{!temporalGS Λ Σ}, trace Λ → iProp Σ;
  tps_tr : trace Λ → Prop;
  tps_good : ∀ `{!temporalGS Λ Σ} (F : iProp Σ) (τ : trace Λ),
    iProp_sat_lc_at_frame F ⊤ (tps_ti τ) → tps_tr τ;
}.
Global Arguments tps Λ Σ : clear implicits.
Global Arguments Tps {Λ Σ}.
Global Arguments tps_ti {Λ Σ} _ {_}.
Global Arguments tps_tr {Λ Σ}.

Declare Scope tps_scope.
Delimit Scope tps_scope with S.
Bind Scope tps_scope with tps.

(** [G ⊑ G']: the step-indexed part of [G] implies that of [G']. *)
Definition tps_le {Λ Σ} (G G' : tps Λ Σ) : Prop :=
  ∀ (H : temporalGS Λ Σ) τ, @tps_ti _ _ G H τ ⊢ @tps_ti _ _ G' H τ.

Lemma ti_until_tr_until_gen `{!temporalGS Λ Σ} F (I1 I2 : tiProp Λ Σ) (R1 R2 : trProp Λ) :
  (∀ τ, iProp_sat_lc_at_frame F ⊤ (I1 τ) → R1 τ) →
  (∀ τ, iProp_sat_lc_at_frame F ⊤ (I2 τ) → R2 τ) →
  ∀ τ, iProp_sat_lc_at_frame F ⊤ (ti_exist Ord.t (λ a, ti_until Ord.lt a I1 I2) τ) →
       tr_until R1 R2 τ.
Proof.
  intros IH1 IH2 τ H. unfold tr_until. destruct τ as (n&τf).
  unfold ti_exist in H. apply sat_exists in H. destruct H as [x H].
  revert n τf H. induction x as [a IHa] using (well_founded_ind Ord.lt_well_founded). intros.
  rewrite ti_until_unfold /ti_until_pre in H.
  apply sat_fupd, sat_later, sat_fupd in H. apply sat_or in H. destruct H as [H|H].
  { apply IH2 in H. exists n. split_and !; eauto. intros. lia. }
  apply iProp_sat_lc_at_frame_and in H. destruct H as [HP H].
  apply sat_fupd, sat_exists in H. destruct H as [b H].
  apply iProp_sat_lc_at_frame_and in H. destruct H as [Hlt H]. apply sat_elim in Hlt.
  apply sat_ALC, sat_fupd in H.
  specialize (IHa _ Hlt _ _ H). simpl in IHa. destruct IHa as (m'& Hm'& Htr& Hp).
  destruct Hm' as [|m Hm'].
  { exists (S n). split_and !; eauto. intros l [Hl1 Hl2]. inversion Hl1; subst; eauto. apply Hp. lia. }
  exists (S m). split_and !; eauto.
  { lia. }
  intros l [Hl1 Hl2]. inversion Hl1; subst; eauto. apply Hp. lia.
Qed.

Section tps_connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : tps Λ Σ.

  Program Definition tps_pure (p : Prop) : tps Λ Σ :=
    {| tps_ti _ := ti_pure p; tps_tr := tr_pure p |}.
  Next Obligation. intros p ? F τ H. by apply sat_elim in H. Qed.

  Definition tps_true : tps Λ Σ := tps_pure True.

  Program Definition tps_atomic (π : state_pred Λ) : tps Λ Σ :=
    {| tps_ti _ := ti_atomic π; tps_tr := tr_atomic π |}.
  Next Obligation.
    intros π ? F [n τf] H. unfold ti_atomic in H. simpl in H.
    unfold tr_atomic, ts_emb, ts_atomic. simpl. destruct (τf n) as (((Θ&σ)&?)&?).
    by apply sat_elim in H.
  Qed.

  Program Definition tps_and G1 G2 : tps Λ Σ :=
    {| tps_ti _ := ti_and (tps_ti G1) (tps_ti G2); tps_tr := tr_and (tps_tr G1) (tps_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold ti_and in H. apply iProp_sat_lc_at_frame_and in H as [H1 H2].
    split; [eapply tps_good, H1|eapply tps_good, H2].
  Qed.

  Program Definition tps_or G1 G2 : tps Λ Σ :=
    {| tps_ti _ := ti_or (tps_ti G1) (tps_ti G2); tps_tr := tr_or (tps_tr G1) (tps_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold ti_or in H. apply sat_or in H as [H|H].
    - left. by eapply tps_good.
    - right. by eapply tps_good.
  Qed.

  Program Definition tps_impl (p : Prop) G : tps Λ Σ :=
    {| tps_ti _ := ti_impl p (tps_ti G); tps_tr := tr_impl p (tps_tr G) |}.
  Next Obligation.
    intros p G ? F τ H Hp. unfold ti_impl in H. eapply tps_good. eapply sat_impl; [apply H|].
    iIntros "_". by iPureIntro.
  Qed.

  (** Universal quantification over any type: [sat] commutes with [∀]. *)
  Program Definition tps_forall {X : Type} (G : X → tps Λ Σ) : tps Λ Σ :=
    {| tps_ti _ := ti_forall X (λ x, tps_ti (G x)); tps_tr := tr_forall X (λ x, tps_tr (G x)) |}.
  Next Obligation.
    intros X G ? F τ H x. unfold ti_forall in H. eapply tps_good. by apply (sat_forall x) in H.
  Qed.

  (** Existential quantification needs the existential property of the step index, so only
      types smaller than the ordinals of [ordI] qualify (nat, gnames, oids, Ord.t, ...). *)
  Program Definition tps_exist {X : Type} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) : tps Λ Σ :=
    {| tps_ti _ := ti_exist X (λ x, tps_ti (G x)); tps_tr := tr_exist X (λ x, tps_tr (G x)) |}.
  Next Obligation.
    intros X ? G ? F τ H. unfold ti_exist in H. apply sat_exists in H as [x H].
    exists x. by eapply tps_good.
  Qed.

  Program Definition tps_always G : tps Λ Σ :=
    {| tps_ti _ := ti_always (tps_ti G) (ti_pure True); tps_tr := tr_always (tps_tr G) |}.
  Next Obligation.
    intros G ? F τ H.
    cut (tr_always (tps_tr G ∧ tr_pure True)%R τ).
    { unfold tr_always. destruct τ. intros Hτ m Hm. by destruct (Hτ m Hm). }
    eapply (ti_always_tr_always F (tps_ti G) (ti_pure True) (tps_tr G) (tr_pure True));
      [intros; by eapply tps_good | intros; exact I | exact H].
  Qed.

  Program Definition tps_until G1 G2 : tps Λ Σ :=
    {| tps_ti _ := ti_exist Ord.t (λ a, ti_until Ord.lt a (tps_ti G1) (tps_ti G2));
       tps_tr := tr_until (tps_tr G1) (tps_tr G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H.
    eapply (ti_until_tr_until_gen F (tps_ti G1) (tps_ti G2) (tps_tr G1) (tps_tr G2));
      [intros; by eapply tps_good | intros; by eapply tps_good | exact H].
  Qed.

  Definition tps_finally G : tps Λ Σ := tps_until tps_true G.

  (** Syntactic trace properties are a fragment. *)
  Program Definition tps_of_tp (t : @tp (state_pred Λ)) : tps Λ Σ :=
    {| tps_ti _ := ti_logic Ord.lt t; tps_tr := tp_trace t |}.
  Next Obligation. intros t ? F τ H. by eapply (ti_logic_tp_trace Ord.lt_well_founded). Qed.

  Lemma tps_le_refl G : tps_le G G.
  Proof. intros ??. done. Qed.
  Lemma tps_le_trans G1 G2 G3 : tps_le G1 G2 → tps_le G2 G3 → tps_le G1 G3.
  Proof. intros H1 H2 ??. by rewrite H1 H2. Qed.
  Lemma tps_le_true G : tps_le G tps_true.
  Proof. intros ??. by iIntros "_". Qed.
  Lemma tps_and_elim_l G1 G2 : tps_le (tps_and G1 G2) G1.
  Proof. intros ??. rewrite /= /ti_and. by iIntros "[$ _]". Qed.
  Lemma tps_and_elim_r G1 G2 : tps_le (tps_and G1 G2) G2.
  Proof. intros ??. rewrite /= /ti_and. by iIntros "[_ $]". Qed.

  Lemma tps_always_mono G G' : tps_le G G' → tps_le (tps_always G) (tps_always G').
  Proof.
    intros Hle H τ. cbn. iIntros "H".
    iAssert (∀ τ, ti_always (tps_ti G) (ti_pure True) τ -∗ ti_always (tps_ti G') (ti_pure True) τ)%I
      with "[]" as "Hal"; last by iApply "Hal".
    iLöb as "IH". iIntros (τ') "H". rewrite !ti_always_unfold /ti_always_pre.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iSplit.
    - iDestruct "H" as "[H _]". by iApply Hle.
    - iDestruct "H" as "[_ H]". iMod "H". iModIntro. iSplit; first by iDestruct "H" as "[$ _]".
      iDestruct "H" as "[_ H]". iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
      by iApply "IH".
  Qed.

End tps_connectives.

Notation "⌜ p ⌝" := (tps_pure p) : tps_scope.
Infix "∧" := tps_and : tps_scope.
Infix "∨" := tps_or : tps_scope.
Infix "→" := tps_impl : tps_scope.
Notation "∀ x .. y , G" := (tps_forall (λ x, .. (tps_forall (λ y, G%S)) ..)) : tps_scope.
Notation "∃ x .. y , G" := (tps_exist (λ x, .. (tps_exist (λ y, G%S)) ..)) : tps_scope.

(** ** Guarantees *)

Section guarantee.
  Context `{!lantanaGS Λ Σ}.
  Implicit Types G : tps Λ Σ.
  Implicit Types P Q : iProp Σ.

  (** The running system: every thread runs its [lwp_fix]. *)
  Definition threads_run (s : stuckness)
    (TQ : gmap thread_id ((expr Λ) * (thread_id → val Λ → iProp Σ))) : iProp Σ :=
    [∗ map] i ↦ '(e, Q) ∈ TQ, match to_val e with
                              | Some v => (lift_term i Q) v
                              | None => lwp_fix s i ⊤ e (lift_term i Q)
                              end.

  (** [tguar G e]: from the event [e] (history index [n] with state [σ], pool [Θ] and
      observations [κs]; model-history index [v1] with obligations [Ω1]) on, every running
      system consistent with the history up to [e] establishes the step-indexed part of [G]
      on the trace. (This is the induction hypothesis of [lwp_fix_ti_logic].) *)
  Definition tguar G n σ Θ κs v1 Ω1 : iProp Σ :=
    □ ∀ s h TQ g v2 Ω2 W τf γ,
      ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ v1 ≤ v2 ∧ obls_le Ω1 Ω2 ∧
       owit_inv_lb (fair_sched_fun γ) Ω2 W ∧
       (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) ∧
       Θ = fst <$> TQ⌝ -∗
      (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v2 Ω2 W n (dom Θ) ∗
      threads_run s TQ -∗
      tps_ti G (n, τf).

  (** [P ⊨ₜ G]: whenever [P] holds, the rest of the execution satisfies [G]. *)
  Definition temporal P G : iProp Σ :=
    □ ∀ h n σ Θ κs m i Ω W,
      history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ P -∗ tguar G n σ Θ κs i Ω.

  Global Instance tguar_persistent G n σ Θ κs v Ω : Persistent (tguar G n σ Θ κs v Ω).
  Proof. apply _. Qed.
  Global Instance temporal_persistent P G : Persistent (temporal P G).
  Proof. apply _. Qed.

  Lemma tguar_elim G s h n σ Θ TQ κs g v1 v2 Ω1 Ω2 W τf γ :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    v1 ≤ v2 →
    obls_le Ω1 Ω2 →
    owit_inv_lb (fair_sched_fun γ) Ω2 W →
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    Θ = fst <$> TQ →
    tguar G n σ Θ κs v1 Ω1 -∗
    (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v2 Ω2 W n (dom Θ) ∗
    threads_run s TQ -∗
    tps_ti G (n, τf).
  Proof. iIntros (???????) "#HG H". iApply ("HG" with "[%] H"). split_and!; done. Qed.

  Lemma temporal_elim P G h n σ Θ κs m i Ω W :
    temporal P G -∗
    history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ P -∗ tguar G n σ Θ κs i Ω.
  Proof. iIntros "#HG H". by iApply "HG". Qed.

  Lemma tguar_mono G G' n σ Θ κs v Ω :
    tps_le G G' → tguar G n σ Θ κs v Ω ⊢ tguar G' n σ Θ κs v Ω.
  Proof.
    iIntros (Hle) "#HG !>". iIntros (?????????) "%H W". iApply Hle. by iApply ("HG" with "[//] W").
  Qed.

End guarantee.

Notation "P ⊨ₜ G" := (temporal P%I G%S) (at level 70, format "P  ⊨ₜ  G") : bi_scope.

(** Once discharged, the obligation invariant of an until keeps the guarantee of its right
    formula at the discharge event. *)
Notation until_disch k G2 :=
  (∃ n' σ' Θ' κs' i' Ω', event_obl i' (n', Ω') k obl_discharged ∗
                         hG_event n' (σ', Θ', κs') ∗ tguar G2 n' σ' Θ' κs' i' Ω')%I (only parsing).

(** [P] until [Q] using namespace [N] and obligation [k]; [G2] is the trace property that
    [Q] guarantees (it is stored at the discharge event). *)
Local Definition untilI_def `{!lantanaGS Λ Σ} N k (b : bool) (q : Qp) (P Q : iProp Σ) (G2 : tps Λ Σ) :
  iProp Σ :=
  oblP_assigned k b (q/2)%Qp ∗ oblP_inv N k P Q (until_disch k G2).
(* Sealed: the proof mode splits it by fractions, and unification (e.g. in [iFrame]) does not
   unfold it. *)
Local Definition untilI_aux : seal (@untilI_def). Proof. by eexists. Qed.
Definition untilI := untilI_aux.(unseal).
Global Arguments untilI {Λ Σ _} N k b q P Q G2.
Local Lemma untilI_unseal : @untilI = @untilI_def.
Proof. rewrite -untilI_aux.(seal_eq) //. Qed.
Lemma untilI_unfold `{!lantanaGS Λ Σ} N k b q P Q G2 :
  untilI N k b q P Q G2 = (oblP_assigned k b (q/2)%Qp ∗ oblP_inv N k P Q (until_disch k G2))%I.
Proof. by rewrite untilI_unseal. Qed.

Definition finallyI `{!lantanaGS Λ Σ} N k (b : bool) (q : Qp) (Q : iProp Σ) (G2 : tps Λ Σ) : iProp Σ :=
  untilI N k b q True Q G2.

(** ** Rules *)

Section rules.
  Context `{!lantanaGS Λ Σ}.
  Implicit Types G : tps Λ Σ.

  Lemma temporal_weaken P G G' : tps_le G G' → P ⊨ₜ G ⊢ P ⊨ₜ G'.
  Proof.
    iIntros (Hle) "#HG !>". iIntros (?????????) "H". iApply tguar_mono; first done. by iApply "HG".
  Qed.

  Lemma temporal_mono P Q G : □ (Q -∗ P) -∗ P ⊨ₜ G -∗ Q ⊨ₜ G.
  Proof.
    iIntros "#HQP #HG !>". iIntros (?????????) "(HI& MI& HQ)". iApply "HG". iFrame. by iApply "HQP".
  Qed.

  Lemma temporal_true P : ⊢ P ⊨ₜ tps_true.
  Proof. iIntros "!>" (?????????) "_ !>". iIntros (?????????) "_ _". done. Qed.

  Lemma temporal_pure (φ : Prop) : ⊢ ⌜φ⌝ ⊨ₜ tps_pure φ.
  Proof. iIntros "!>" (?????????) "(_& _& %Hφ) !>". iIntros (?????????) "_ _". done. Qed.

  Lemma temporal_atomic π : ⊢ state_pred_interp π ⊨ₜ tps_atomic π.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& _& TL)".
    rewrite /history_interp. iDestruct "HI" as "(HI1& HI2& SI)".
    iPoseProof (state_interp_wf with "[$SI $TL]") as "%".
    iPoseProof (history_interp_event_pred_now with "[HI1 HI2 SI]") as "#TF". 1: done.
    { rewrite /history_interp. iFrame. }
    iIntros "!>" (s h' TQ g v2 Ω2 W' τf γ (BEH& FS& LEv& LEO& LB& HIST& EQTQ)) "([HI' SIa]& MI& WPs)".
    simpl. unfold ti_atomic. iPoseProof (event_pred_history_interp_lookup with "[$HI' $TF]") as "%H'".
    destruct H' as [H' ?]. simpl. apply HIST in H'. destruct H' as [? H']. rewrite H'. auto.
  Qed.

  Lemma temporal_and P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∧ Q) ⊨ₜ (G1 ∧ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& HPQ)".
    iPoseProof (temporal_elim with "HG1 [$HI $MI HPQ]") as "#T1"; first by iDestruct "HPQ" as "[$ _]".
    iPoseProof (temporal_elim with "HG2 [$HI $MI HPQ]") as "#T2"; first by iDestruct "HPQ" as "[_ $]".
    iIntros "!>" (?????????) "%H W". iSplit.
    - by iApply ("T1" with "[//] W").
    - by iApply ("T2" with "[//] W").
  Qed.

  Lemma temporal_sep P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∗ Q) ⊨ₜ (G1 ∧ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& HP& HQ)".
    iPoseProof (temporal_elim with "HG1 [$HI $MI $HP]") as "#T1".
    iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#T2".
    iIntros "!>" (?????????) "%H W". iSplit.
    - by iApply ("T1" with "[//] W").
    - by iApply ("T2" with "[//] W").
  Qed.

  Lemma temporal_or P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∨ Q) ⊨ₜ (G1 ∨ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& [HP | HQ])".
    - iPoseProof (temporal_elim with "HG1 [$HI $MI $HP]") as "#T1".
      iIntros "!>" (?????????) "%H W". iLeft. by iApply ("T1" with "[//] W").
    - iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#T2".
      iIntros "!>" (?????????) "%H W". iRight. by iApply ("T2" with "[//] W").
  Qed.

  Lemma temporal_impl (φ : Prop) P G : P ⊨ₜ G -∗ (⌜φ⌝ → P) ⊨ₜ (φ → G).
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& HP)".
    destruct (Classical_Prop.classic φ) as [Hφ|Hφ].
    - iPoseProof (temporal_elim with "HG [$HI $MI HP]") as "#T"; first by iApply "HP".
      iIntros "!>" (?????????) "%H W". rewrite /= /ti_impl. iIntros (_). by iApply ("T" with "[//] W").
    - iIntros "!>" (?????????) "_ _". rewrite /= /ti_impl. by iIntros (?).
  Qed.

  (** Universal quantification over any type. *)
  Lemma temporal_forall {X : Type} (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∀ x, P x) ⊨ₜ tps_forall G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& HP)".
    iAssert (∀ x, tguar (G x) _ _ _ _ _ _)%I with "[-]" as "#T".
    { iIntros (x). iApply (temporal_elim with "HG"). iFrame. iApply "HP". }
    iIntros "!>" (?????????) "%H W". iIntros (x). by iApply ("T" $! x with "[//] W").
  Qed.

  (** Trace-visible existential quantification, over small types. *)
  Lemma temporal_exist {X : Type} `{!TypeExistentialProperty X ordI} (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∃ x, P x) ⊨ₜ tps_exist G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& [%x HP])".
    iPoseProof (temporal_elim with "HG [$HI $MI $HP]") as "#T".
    iIntros "!>" (?????????) "%H W". iExists x. by iApply ("T" with "[//] W").
  Qed.

  (** Ghost existential quantification, over any type: the witness does not show in the
      trace property. *)
  Lemma temporal_exist_ghost {X : Type} (P : X → iProp Σ) G :
    (∀ x, P x ⊨ₜ G) -∗ (∃ x, P x) ⊨ₜ G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& [%x HP])". iApply (temporal_elim with "HG"). iFrame.
  Qed.

  (** An iProp carrying its own guarantee: such pairs can be stored in invariants and
      saved propositions, and quantified over. *)
  Lemma temporal_certified G : ⊢ (∃ P, P ∗ P ⊨ₜ G) ⊨ₜ G.
  Proof.
    iIntros "!>" (?????????) "(HI& MI& (%P& HP& #HG))". iApply (temporal_elim with "HG"). iFrame.
  Qed.

  Lemma temporal_persistently P G : P ⊨ₜ G -∗ □ P ⊨ₜ G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& #HP)". iApply (temporal_elim with "HG"). iFrame "HI MI HP".
  Qed.

  (** The guarantee of the content is only needed after a step, so it may be guarded. *)
  Lemma temporal_always_later N P G : ▷ (P ⊨ₜ G) -∗ inv N P ⊨ₜ tps_always G.
  Proof.
    iIntros "#HG !>" (h0 n σ Θ κs m0 v1 Ω1 W0) "(_& _& #TF) !>".
    iIntros (s h TQ g v2 Ω2 W τf γ (BEH& FS& LEv& LEO& LB& HIST& EQTQ)) "([HI SIa]& MI& WPs)".
    clear h0 m0 W0. rewrite /threads_run. simpl.
    clear dependent v1 Ω1. rename v2 into v, Ω2 into Ω.
    iRevert (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ) "TF HI SIa MI WPs".
    iLöb as "IH". iIntros (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ) "#TF HI SIa MI WPs".
    rewrite ti_always_unfold /ti_always_pre.
    iMod (inv_acc with "TF") as "[HP ACC]". 1: set_solver.
    iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext.
    iPoseProof (temporal_elim with "HG [$HI $MI $HP]") as "#TFP".
    iMod "close" as "_". iMod ("ACC" with "HP") as "_". iModIntro. iSplit.
    { iApply (tguar_elim with "TFP [$HI $SIa $MI $WPs]"); eauto. done. }
    (** Fetch the scheduled thread and take a step. *)
    inversion BEH. clear BEH. subst n0 τf0.
    iPoseProof (history_interp_lookup with "HI") as "%LUhn". apply HIST in LUhn. destruct LUhn as (i'&LUhn).
    rewrite H1 in LUhn. inversion LUhn. clear LUhn. subst ρ1 i' κs.
    rename κs0 into κs, H1 into TRn, H3 into TRn1, H4 into BEH.
    iAssert ([∗ map] i ↦ e ∈ Θ, match to_val e with | Some _ => (thP_done i) | None => True end)%I as "#THs".
    { subst. iApply big_sepM_fmap. iApply (big_sepM_impl with "WPs").
      iIntros "!> %%% H". destruct x. simpl. destruct (to_val e); auto. iDestruct "H" as "[$ _]". }
    iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    destruct H2 as [TStep | TDone].
    + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TStep. clear TStep. inversion H. clear H. subst Θ0 σ ρ2. rename H1 into PStep, H0 into LUTi1.
      assert (LUTQi1 : ∃ Q, TQ !! i1 = Some (e1, Q)).
      { subst Θ. rewrite lookup_fmap_Some in LUTi1. destruct LUTi1 as (?&?&?). destruct x. subst. eauto. }
      destruct LUTQi1 as (Q& LUTQi1). iPoseProof (big_sepM_delete _ _ _ _ LUTQi1 with "WPs") as "[WP WPs]".
      pose proof (val_stuck _ _ _ _ _ _ _ _ PStep) as He1. rewrite He1.
      iPoseProof (lwp_fix_unfold_fix with "WP") as "WP". rewrite /lwp_pre He1 /lwp_step.
      iSpecialize ("WP" $! ctx_id). iEval (rewrite !ctx_id_apply) in "WP".
      iMod ("WP" with "[] [//] [$HI $SIa]") as "WP".
      { iPureIntro. apply _. }
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
      iMod (model_interp_gupd_steps with "WP MI") as "(WP& %g0& %v0& %Ω0 & %W0& %& MI)".
      2: eapply LB.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [OND LB0].
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv0".
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA0". 1,2: eauto.
      iDestruct "WP" as "[%NStuck WP]".
      iPoseProof ("WP" with "[//]") as "WP".
      iEval (rewrite !ctx_id_apply) in "WP". rewrite /mprog.
      iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
      unshelve epose proof (mprog_exists_step i1 Ω0 Ω2 W0 (n, τf) γ _ OTA0 OWinv0 LB0 FS ProgO).
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
        - rewrite lwp_fix_unfold_fix /lwp_pre EQx. iMod "WP".
          iApply sfmupd_lwpupd. iMod "WP". by iModIntro.
        - iApply "WP". }
      iMod (all_interp_lwpupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)".
      { subst Θ2 TQefs. rewrite -map_fmap_compose. unfold compose. simpl. rewrite map_fmap_id.
        apply map_union_subseteq_r. apply map_disjoint_insert_l_2; auto. apply not_elem_of_dom.
        apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. }
      1: auto. destruct H as [LEO2 LB4]. destruct (to_val e2) eqn:He2.
      * rewrite lwp_fix_unfold_fix /lwp_pre He2.
        iDestruct "HI" as "[HI SIa]".
        iMod (all_interp_sfgupd_steps with "WP HI MI") as "(WP& HI& %g3& %v3& %Ω5& %W5& %& MI)".
        2: eapply LB4.
        { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
        destruct H as [LEO3 LB5].
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
  Qed.

  Lemma temporal_always N P G : P ⊨ₜ G -∗ inv N P ⊨ₜ tps_always G.
  Proof. iIntros "#HG". iApply temporal_always_later. by iNext. Qed.

  Lemma temporal_until_later N k b q L1 L2 G1 G2 :
    ▷ (L1 ⊨ₜ G1) -∗ ▷ (L2 ⊨ₜ G2) -∗ untilI N k b q L1 L2 G2 ⊨ₜ tps_until G1 G2.
  Proof.
    iIntros "#HG1 #HG2 !>" (h0 n σ Θ κs m0 v1 Ω1 W0) "(HI0& MI0& HU)". rewrite !untilI_unfold. iDestruct "HU" as "[OA #TF]".
    iDestruct "MI0" as "(MI0& S& _)".
    iEval (unfold_opreds) in "OA". iDestruct "OA" as "(#OE& OA)".
    iPoseProof (osat_lookup_assigned with "[$S $OE $OA]") as "%Hk". destruct Hk as (f& o& Hk).
    iPoseProof (model_history_interp_event_obl_now with "MI0") as "#EA". 1: eauto.
    iClear "HI0 MI0 S OA OE". clear h0 m0 W0 Hk.
    iIntros "!>" (s h TQ g v2 Ω2 W τf γ (BEH& FS& LEv& LEO& LB& HIST& EQTQ)) "([HI SIa]& MI& WPs)".
    rewrite /threads_run. simpl.
    rewrite /ti_exist.
    iPoseProof (event_obl_model_history_interp_lookup with "[MI $EA]") as "%".
    { iDestruct "MI" as "[$ _]". }
    simpl in H. destruct H as (LUMHv1& LUOk1& _). pose proof LEO as LEO2. destruct LEO2. clear H0.
    assert (is_Some (Ω2 !! k)).
    { apply elem_of_dom. apply elem_of_dom_2 in LUOk1. set_solver + LUOk1 H. }
    clear H. destruct H0 as [x LUOk2]. destruct x; cycle 1.
    { iExists Ord.O. rewrite ti_until_unfold /ti_until_pre. iLeft.
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
      iPoseProof (tguar_elim with "TF2 [$HI $SIa $MI $WPs]") as "HA".
      1: eapply BEH. 1: eapply FS. 1,2,3,4,5: eauto.
      iMod ("ACC" with "[]") as "_".
      { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of EF HE TF2". }
      iModIntro. iFrame. }
    iClear "EA". clear dependent Ω1 f o v1. rename v2 into v, Ω2 into Ω, LUOk2 into LUOk.
    pose proof LB. specialize (H k). rewrite LUOk in H. inversion H. clear H. destruct y; last done. subst x.
    rename H1 into LUWk, H2 into LEwit. symmetry in LUWk.
    iExists wit. clear LUWk.
    (** Induction on wit. *)
    iRevert (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ fuel owner LUOk LEwit) "TF HI SIa MI WPs".
    iInduction wit as [w IH] using (well_founded_ind Ord.lt_well_founded).
    iIntros (γ h n σ Θ TQ κs g v Ω W BEH FS LB HIST EQTQ fuel owner LUOk LEwit) "#TF HI SIa MI WPs".
    rewrite ti_until_unfold /ti_until_pre.
    iMod (oblP_inv_acc with "TF") as "[Var ACC]". 1: set_solver.
    iApply fupd_mask_intro. 1: set_solver. iIntros "close". iNext. iMod "close" as "_".
    iDestruct "Var" as "[[Var HP] | [[Var HQ] | Var]]"; cycle 1.
    { iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#TFQ". iMod ("ACC" with "[Var HQ]") as "_".
      { iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame. }
      iModIntro. iLeft. iApply (tguar_elim with "TFQ [$HI $SIa $MI $WPs]"); eauto. done. }
    { iDestruct "Var" as "[OF _]". iDestruct "MI" as "(MHI& S& MI)".
      iEval (unfold_opreds) in "OF". iDestruct "OF" as "(#OE& #OF)".
      iPoseProof (osat_lookup_discharged with "[$S $OE $OF]") as "%". rewrite LUOk in H. inv H. }
    iPoseProof (temporal_elim with "HG1 [$HI $MI $HP]") as "#TFP". iMod ("ACC" with "[Var HP]") as "_".
    { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
    iModIntro. iRight. iSplit.
    { iApply (tguar_elim with "TFP [$HI $SIa $MI $WPs]"); eauto. done. }
    (** Fetch the scheduled thread and take a step. *)
    inversion BEH. clear BEH. subst n0 τf0.
    iPoseProof (history_interp_lookup with "HI") as "%LUhn". apply HIST in LUhn. destruct LUhn as (i'&LUhn).
    rewrite H1 in LUhn. inversion LUhn. clear LUhn. subst ρ1 i' κs.
    rename κs0 into κs, H1 into TRn, H3 into TRn1, H4 into BEH.
    iAssert ([∗ map] i ↦ e ∈ Θ, match to_val e with | Some _ => (thP_done i) | None => True end)%I as "#THs".
    { subst. iApply big_sepM_fmap. iApply (big_sepM_impl with "WPs").
      iIntros "!> %%% H". destruct x. simpl. destruct (to_val e); auto. iDestruct "H" as "[$ _]". }
    iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    destruct H2 as [TStep | TDone].
    + iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TStep. clear TStep. inversion H. clear H. subst Θ0 σ ρ2. rename H1 into PStep, H0 into LUTi1.
      assert (LUTQi1 : ∃ Q, TQ !! i1 = Some (e1, Q)).
      { subst Θ. rewrite lookup_fmap_Some in LUTi1. destruct LUTi1 as (?&?&?). destruct x. subst. eauto. }
      destruct LUTQi1 as (Q& LUTQi1). iPoseProof (big_sepM_delete _ _ _ _ LUTQi1 with "WPs") as "[WP WPs]".
      pose proof (val_stuck _ _ _ _ _ _ _ _ PStep) as He1. rewrite He1.
      iPoseProof (lwp_fix_unfold_fix with "WP") as "WP". rewrite /lwp_pre He1 /lwp_step.
      iSpecialize ("WP" $! ctx_id). iEval (rewrite !ctx_id_apply) in "WP".
      iMod ("WP" with "[] [//] [$HI $SIa]") as "WP".
      { iPureIntro. apply _. }
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
      iMod (model_interp_gupd_steps with "WP MI") as "(WP& %g0& %v0& %Ω0 & %W0& %& MI)".
      2: eapply LB.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [OND LB0].
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv0".
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA0". 1,2: eauto.
      iDestruct "WP" as "[%NStuck WP]".
      iPoseProof ("WP" with "[//]") as "WP".
      iEval (rewrite !ctx_id_apply) in "WP". rewrite /mprog.
      iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
      unshelve epose proof (mprog_exists_step i1 Ω0 Ω2 W0 (n, τf) γ _ OTA0 OWinv0 LB0 FS ProgO).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
      iMod ("WP" $! W2 with "[]") as "[MI WP]".
      { iPureIntro. split; auto. }
      assert (∃ fuel0 owner0, Ω0 !! k = Some (obl_assigned fuel0 owner0) ∧ (fuel0 w≤ fuel) ∧
                              (fair_sched_fun γ owner0 fuel0 w≤ fair_sched_fun γ owner fuel)).
      { destruct OND. assert (is_Some (Ω0 !! k)).
        { apply elem_of_dom. apply elem_of_dom_2 in LUOk. set_solver + LUOk H. }
        destruct H1. specialize (H0 _ _ _ LUOk H1). destruct x; simpl in H0; [|done]. destruct H0.
        - destruct H0. subst. exists fuel0, owner0. split_and !; eauto.
          apply Hessenberg.le_add_l. apply Jacobsthal.le_mult_r. auto.
        - exists fuel0, owner0. split_and !; eauto. 1: eapply WFOCM.lt_le; eauto.
          eapply WFOCM.lt_le, fair_sched_fun_mon; auto. }
      destruct H as (fuel0&owner0&LUOk0& LEfuel0& FSLEfuel0).
      assert (∃ fuel' owner', Ω2 !! k = Some (obl_assigned fuel' owner')).
      { destruct ProgO. specialize (H0 k). rewrite LUOk0 in H0. inv H0. destruct y; by eauto. }
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
      assert (HDrop : (fair_sched_fun γ2 owner2 fuel2 < fair_sched_fun γ owner fuel)%ord).
      { destruct ProgO as [StepO KeepO]. specialize (StepO k). rewrite LUOk0 LUOk2 in StepO.
        inv StepO. simpl in H1. destruct H1.
        - destruct H. subst i1. inv H0; inv H. apply fair_sched_fun_mon_gen; auto.
          eapply WFOCM.lt_le_lt; eauto.
        - eapply WFOCM.lt_le_lt; last eapply FSLEfuel0.
          destruct H. inv H0. specialize (FSrel owner2). unfold fscnt_next_rel_th in FSrel.
          rewrite decide_False in FSrel; cycle 1.
          { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
          rewrite decide_False in FSrel.
          { apply Hessenberg.lt_add_r. apply OrdArith.lt_from_nat. auto. }
          intros F. eapply (thread_active_and_not_false _ _ F TA2). }
      assert (HDropw : (fair_sched_fun γ2 owner2 fuel2 < w)%ord).
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
        - rewrite lwp_fix_unfold_fix /lwp_pre EQx. iMod "WP".
          iApply sfmupd_lwpupd. iMod "WP". by iModIntro.
        - iApply "WP". }
      iMod (all_interp_lwpupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)".
      { subst Θ2 TQefs. rewrite -map_fmap_compose. unfold compose. simpl. rewrite map_fmap_id.
        apply map_union_subseteq_r. apply map_disjoint_insert_l_2; auto. apply not_elem_of_dom.
        apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. }
      1: auto. destruct H as [LEO2 LB4]. destruct (to_val e2) eqn:He2.
      (* iMod (all_interp_lwpupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)". *)
      (* { subst Θ2 TQefs. rewrite -map_fmap_compose. unfold compose. simpl. rewrite map_fmap_id. *)
      (*   apply map_union_subseteq_r. apply map_disjoint_insert_l_2; auto. apply not_elem_of_dom. *)
      (*   apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. } *)
      (* 1: auto. destruct H as [LEO2 LB4]. destruct (to_val e2) eqn:He2. *)
      * rewrite lwp_fix_unfold_fix /lwp_pre He2.
        iDestruct "HI" as "[HI SIa]".
        iMod (all_interp_sfgupd_steps with "WP HI MI") as "(WP& HI& %g3& %v3& %Ω5& %W5& %& MI)".
        2: eapply LB4.
        { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
        destruct H as [LEO3 LB5].
        (* iMod (all_interp_lwpupd_steps with "WP HI MI") as "(WP& HI& %g3& %v3& %Ω5& %W5& %& MI)". *)
        (* { subst Θ2. rewrite lookup_union_l. *)
        (*   - apply lookup_insert_eq. *)
        (*   - apply not_elem_of_dom. apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. } *)
        (* 1: eapply LB4. destruct H as [LEO3 LB5]. *)
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
        assert (LEO5 : obls_le Ω2 Ω5).
        { etrans; first eauto. etrans; first eauto. apply obls_nd_obls_le; auto. }
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
        { iModIntro. rewrite ti_until_unfold /ti_until_pre. iLeft.
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
          destruct (le_gt_dec (S (S (v + v0))) i'); cycle 1.
          { iPoseProof (event_obl_compare i' (S (S (v + v0))) with "[$EF $EA]") as "%". 1: lia.
            simpl in H. destruct H as (?&?&?). done. }
          iPoseProof (event_obl_compare (S (S (v + v0))) i' with "[$EA $EF]") as "%". 1: auto.
          simpl in H. destruct H as (LEn'2& LEO'2& _). rename l into LEv1.
          assert (n' = S n) by lia. subst n'. clear LEn' LEn'2.
          iPoseProof (history_interp_hG_event_lookup with "[$HI $HE]") as "%".
          iPoseProof (history_interp_lookup with "HI") as "%". rewrite H in H0. inversion H0. clear H H0. subst σ' Θ' κs'.
          iPoseProof (tguar_elim with "TF2 [$HI $SIa $MI $WPs]") as "HA".
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
        { iModIntro. rewrite ti_until_unfold /ti_until_pre. iLeft.
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
          destruct (le_gt_dec (S (S (v + v0))) i'); cycle 1.
          { iPoseProof (event_obl_compare i' (S (S (v + v0))) with "[$EF $EA]") as "%". 1: lia.
            simpl in H. destruct H as (?&?&?). done. }
          iPoseProof (event_obl_compare (S (S (v + v0))) i' with "[$EA $EF]") as "%". 1: auto.
          simpl in H. destruct H as (LEn'2& LEO'2& _). rename l into LEv1.
          assert (n' = S n) by lia. subst n'. clear LEn' LEn'2.
          iPoseProof (history_interp_hG_event_lookup with "[$HI $HE]") as "%".
          iPoseProof (history_interp_lookup with "HI") as "%". rewrite H in H0. inversion H0. clear H H0. subst σ' Θ' κs'.
          iPoseProof (tguar_elim with "TF2 [$HI $SIa $MI $WPs]") as "HA".
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
      assert (HDrop : (fair_sched_fun γ2 owner fuel < fair_sched_fun γ owner fuel)%ord).
      { apply Hessenberg.lt_add_r, OrdArith.lt_from_nat.
        specialize (FSrel owner). unfold fscnt_next_rel_th in FSrel.
        specialize (OTA k _ LUOk). simpl in OTA.
        rewrite decide_False in FSrel; cycle 1.
        { intros F. subst. eapply (thread_active_and_not_false _ _ TNA OTA). }
        rewrite decide_False in FSrel; auto.
        intros F. eapply (thread_active_and_not_false _ _ F OTA). }
      assert (HDropw : (fair_sched_fun γ2 owner fuel < w)%ord).
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

  Lemma temporal_until N k b q L1 L2 G1 G2 :
    L1 ⊨ₜ G1 -∗ L2 ⊨ₜ G2 -∗ untilI N k b q L1 L2 G2 ⊨ₜ tps_until G1 G2.
  Proof. iIntros "#HG1 #HG2". iApply temporal_until_later; by iNext. Qed.

End rules.
Section until_rules.
  Context `{!lantanaGS Λ Σ}.

  (** Until *)
  Lemma untilI_frac_split N k b q q1 q2 P Q G2 :
    (q = q1 + q2)%Qp →
    ⊢ untilI N k b q P Q G2 -∗ (untilI N k b q1 P Q G2 ∗ untilI N k b q2 P Q G2).
  Proof.
    iIntros (He) "U". rewrite !untilI_unfold He Qp.div_add_distr. iDestruct "U" as "([$ $]& #U)". auto.
  Qed.
  Lemma untilI_frac_add N k b1 b2 q1 q2 q P Q G2 P' Q' G2' :
    (q = q1 + q2)%Qp →
    untilI N k b1 q1 P Q G2 -∗ untilI N k b2 q2 P' Q' G2' -∗ untilI N k b1 q P Q G2.
  Proof.
    intros Hq. subst q.
    rewrite !untilI_unfold Qp.div_add_distr. iIntros "[Oa1 $] [Oa2 _]".
    iPoseProof (oblP_assigned_agree with "Oa1 Oa2") as "%". subst.
    by iCombine "Oa1 Oa2" as "Oa".
  Qed.

  Global Instance untilI_fractional N k b P Q G2 : Fractional (λ q, untilI N k b q P Q G2).
  Proof.
    intros p q. rewrite !untilI_unfold. iSplit.
    - iIntros "(Oa& #OI)". iFrame "OI". rewrite !Qp.div_add_distr. iDestruct "Oa" as "[Oa Oa']". iFrame.
    - iIntros "((Oa1& #Oi)& Oa2& _)". iFrame "Oi". rewrite !Qp.div_add_distr. iCombine "Oa1 Oa2" as "$".
  Qed.
  Global Instance untilI_as_fractional N k b q P Q G2 : AsFractional (untilI N k b q P Q G2) (λ q, untilI N k b q P Q G2) q.
  Proof. split; [auto|apply _]. Qed.

  (** Update rules *)
  Lemma untilI_alloc E g K (b : bool) ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    crP_obls g ℓ1 K -∗
    |={E}=>g ∃ k, ⌜k ∉ K⌝ ∗ crP_obls g ℓ1 ({[k]} ∪ K) ∗
                 oblP_fuel k ℓ2 μ ∗ witP_layer k ℓ2 ∗
                 ∀ E' N (P Q : iProp Σ) G2, ▷ (if b then Q else P) ={E'}=∗ (untilI N k b 1 P Q G2).
  Proof.
    iIntros (Ltl) "TG". iMod (obl_alloc_assigned with "TG") as "(%& $& $& Oa& $& $& ACC)". 1: auto.
    iIntros "!> %%%%% H". rewrite !untilI_unfold. iMod ("ACC" with "H") as "ACC". iFrame. done.
  Qed.

  Lemma untilI_discharged_alloc E ℓ μ (Q : iProp Σ) G2 :
    Q ⊨ₜ G2 -∗ Q -∗
    |={E}=>g Q ∗ ∃ k, oblP_discharged k ∗
                        (∀ E' N (P : iProp Σ), |={E'}=> oblP_inv N k P Q (until_disch k G2)) ∗ 
                        oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof.
    iIntros "#HG2 HQ".
    unfold_sfgupd. rewrite /fgupd. iIntros (?????) "SI".
    (* unfold_sfmupd. rewrite /fmupd. iIntros (?????) "SI". *)
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    (* FIXME: proof without unfold everything? *)
    unfold_opreds. iApply gupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
    (* unfold_opreds. iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)". *)
    assert (NEW : ∃ k, Ω1 !! k = None).
    { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
    destruct NEW as (k& NEWk).
    assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
    iMod (osat_alloc_obl_discharged _ k (measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M) with "S") as "(S& #Gwf& #Ge& #Gu& Gf& %OStep)". 1: auto.
    iMod (owit_alloc_witness_discharged _ k (η (measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M)) with "[$W $Gu]") as "(W& #Ww)".
    { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
    iPoseProof (oassigned_add_obl with "[$A $Ge Gu]") as "A".
    { iRight. iFrame "Gu". }
    set (Ω2:=(<[k:=(obl_discharged)]> Ω1)).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 2. eauto. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iPoseProof (history_interp_hG_event_now with "SI") as "#HE".
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. econstructor 2. econstructor 2. auto. }
    iIntros (? [WStep GWI2]) "!>".
    unshelve epose proof (owit_inv_alloc_discharged Ω1 k W1 NinOk1 GWI W2 _ GWI2) as (NinWk1& WMon).
    { inv WStep; eauto. econstructor 2. apply wits_nd_step_wits_step. auto. }
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. iFrame. }
    iPoseProof (temporal_elim with "HG2 [$SI $HI $S $O $A $G $W $HQ]") as "#HQi". 1: eauto.    
    rewrite /model_interp. iFrame "HI S O A G W". iSplitR; first eauto.
    iModIntro. iMod "close" as "_". iModIntro. iFrame "SI HQ". iExists k. iFrame "Ge Ww Gf Gu".
    iIntros (E' N P).
    
    iMod (oblG_inv_alloc_discharged _ N _ _ P Q with "[$Gu]") as "#GVar"; cycle 1.
    { iFrame "GVar". done. }
    iFrame "Eo HE HQi".
  Qed.

  (** TODO: Timeless version *)
  Lemma untilI_to_true E N k (P Q : iProp Σ) G2 :
    ↑N ⊆ E →
    untilI N k false 1 P Q G2 ={E,E ∖ ↑N}=∗
    ▷ (P ∗ ∀ E', |={E'}=>g ((▷ Q) ={E ∖ ↑N,E}=∗ untilI N k true 1 P Q G2)).
  Proof.
    rewrite !untilI_unfold. iIntros (HM) "(Oa& #Oi)".
    iMod (obl_assigned_to_true with "Oi Oa") as "[H ACC]". 1: auto.
    iModIntro. iNext. iDestruct "H" as "[Oa $]".
    iIntros "%". iPoseProof ("ACC" with "Oa") as "ACC". iMod ("ACC" $! E') as "[Oa ACC]".
    iIntros "!> HQ". iMod ("ACC" with "HQ") as "_". iFrame. eauto.
  Qed.

  (** TODO: Timeless version *)
  Lemma untilI_true_to_discharge E N k (P Q : iProp Σ) G2 :
    ↑N ⊆ E →
    Q ⊨ₜ G2 -∗ untilI N k true 1 P Q G2 ={E,E ∖ ↑N}=∗
    ∀ g ℓ K,
    (⌜k ∈ K⌝) → crP_obls g ℓ K -∗
    ∀ E', ▷ (|={E'}=>m |={E ∖ ↑N,E}=> (Q ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)).
  Proof.
    rewrite !untilI_unfold. iIntros (HMask) "#HG2 (Oa& #OI)".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: auto.
    iIntros "!> %%% %LUGk TG %". iDestruct ("H" with "Oa") as "[H ACC]".
    iNext. iDestruct "H" as "(Oa1& Oa2& HQ)". iCombine "Oa1 Oa2" as "Oa".
    unfold_sfmupd. rewrite /fmupd. iIntros (?????) "SI".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    (* FIXME: it would be better if we don't need to unfold everything and re-do the proof here... *)
    unfold_opreds. iDestruct "TG" as "(%& #Oe& Gg& Gt& Gw& #Gb& OS)".
    iDestruct "OI" as "(#Ge& Gvar)". iDestruct "Oa" as "(_& Gl)".
    iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
    iPoseProof (big_sepS_delete _ _ _ LUGk with "OS") as "[(_& Go& Oo) OS]".
    iPoseProof (osat_lookup_assigned with "[$S $Ge $Gl]") as "%LUO1l".
    iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
    destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&LUO1o).
    rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into a.
    iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%& Go1& Oo1& _) | #Gu])".
    { apply elem_of_dom. eauto. }
    2:{ iExFalso. iPoseProof (oblG_assigned_discharged_false with "[$Gl $Gu]") as "%". done. }
    iPoseProof (oblG_owner_agree _ i i1 with "[$Go $Go1]") as "%". destruct H as [<- _].
    iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
    iPoseProof (othread_elem with "[$O $Oe]") as "%Ini".
    iMod (ocarrier_delete_obl with "[$O $G $Gg $Oo]") as "(O& G& Gg& Go2)". 1,2: auto.
    iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'". iCombine "Go Go'" as "Go".
    iMod (osat_discharge with "[$S $Ge $Gl $Go]") as "(S& #Gu& %Gstep)".
    assert (LUW : ∃ b, W1 !! k = Some (witness_assigned b) ∧ (b <= η a)%ord).
    { specialize (GWI k). rewrite LUO1l in GWI. inv GWI. destruct y; try done. eauto. }
    destruct LUW as (b&LUW1& LEab).
    iPoseProof (owit_discharge with "[$W $Gu]") as "W". 1: eauto.
    iPoseProof (oassigned_add_obl _ k with "[$A $Ge]") as "A".
    { iRight. eauto. }
    set (Ω2:=(<[k:=(obl_discharged)]> Ω1)).
    assert (Gstep' : obl_step (obl_assigned a i) obl_discharged) by (by econstructor 2).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iPoseProof (history_interp_hG_event_now with "SI") as "#HE".
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
    iIntros (? [WStep GWI2]).
    pose proof (owit_inv_discharge _ _ _ _ _ LUO1l GWI Gstep' W2 WStep GWI2) as (?& LUW& WMon).
    rewrite LUW1 in LUW. inv LUW.
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)). 1: iFrame.
      apply elem_of_dom_2 in LUO1l. rewrite -union_difference_L; set_solver. }
    iPoseProof (temporal_elim with "HG2 [$SI $HI $S $O $A $G $W $HQ]") as "#HQi". 1: eauto.
    rewrite /model_interp. iFrame "HI S O W A G".
    iApply fupd_intro. iSplitR; first eauto. iIntros "!>". iFrame "Oe Ge Gb Gu Gg Gt SI".
    iMod "close" as "_". iModIntro. iMod ("ACC" with "[]") as "_".
    { iNext. iRight. iRight.  iFrame "Ge Gu Eo HE HQi". }
    iModIntro. iFrame.
  Qed.

  Lemma untilI_discharge E N k (P Q : iProp Σ) G2 :
    ↑N ⊆ E →
    Q ⊨ₜ G2 -∗ untilI N k false 1 P Q G2 ={E,E ∖ ↑N}=∗
    ▷ (P ∗
       ∀ E', |={E'}=>g ((▷ Q) ={E ∖ ↑N}=∗
                       ∀ g ℓ K, (⌜k ∈ K⌝) → crP_obls g ℓ K -∗
                                ∀ E'', ▷ (|={E''}=>m |={E ∖ ↑N,E}=> (Q ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)))).
  Proof.
    iIntros (HN) "#HG2 Uk". iMod (untilI_to_true with "Uk") as "H". 1: auto.
    iModIntro. iNext. iDestruct "H" as "($& H)". iIntros (?).
    iMod ("H" $! E') as "H". iIntros "!> HQ". iMod ("H" with "HQ") as "H".
    iMod (untilI_true_to_discharge with "HG2 H") as "H". 1: auto.
    iIntros "!> %%% % TG". iPoseProof ("H" with "[//] TG") as "H".
    iIntros (?). iNext. iMod ("H" $! E'') as "H". iModIntro. iFrame.
  Qed.

  (** Access rules *)
  Lemma untilI_discharged_false N k b q P Q G2 :
    untilI N k b q P Q G2 -∗ oblP_discharged k -∗ False.
  Proof.
    rewrite !untilI_unfold. iIntros "[Oa _] #Of".
    iPoseProof (oblP_assigned_discharged_false with "Oa Of") as "%". done.
  Qed.

  Lemma untilI_acc E N k b q P Q G2 :
    ↑N ⊆ E →
    untilI N k b q P Q G2 ={E,E ∖ ↑N}=∗
    ▷ ((if b then Q else P) ∗ ((▷ if b then Q else P) ={E ∖ ↑N,E}=∗ untilI N k b q P Q G2)).
  Proof.
    rewrite !untilI_unfold. iIntros (Hmask) "(Oa& #OI)".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: set_solver.
    iPoseProof ("H" with "Oa") as "[H ACC]".
    iModIntro. iNext. iDestruct "H" as "(Oa& H)". destruct b.
    - iDestruct "H" as "(Oa2& $)". iIntros "HQ". iFrame "Oa OI". iApply "ACC".
      iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame.
    - iDestruct "H" as "(Oa2& $)". iIntros "HP". iFrame "Oa OI". iApply "ACC".
      iNext. iApply oblP_variant_unfold. iLeft. iFrame.
  Qed.

End until_rules.

Section until_derived.
  Context `{!lantanaGS Λ Σ}.

  (** Discharge a finally with its right formula at hand, using two later credits. *)
  Lemma finallyI_discharge E N k g ℓ K Q G2 :
    ↑N ⊆ E → k ∈ K →
    Q ⊨ₜ G2 -∗ £ (2 : Ord.t) -∗ crP_obls g ℓ K -∗ finallyI N k false 1 Q G2 -∗ Q -∗
    |={E}=>m Q ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof.
    iIntros (Hmask Hk) "#HG LC Cg HF HQ".
    iMod (untilI_discharge with "HG HF") as "HF"; first set_solver.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iDestruct "HF" as "[_ HF]". iMod ("HF" $! _) as "HF".
    iMod ("HF" with "[HQ]") as "HF".
    { iNext. iFrame. }
    iPoseProof ("HF" with "[//] Cg") as "HF".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("HF" $! _) as "HF". iMod "HF" as "($& $& $)". done.
  Qed.

End until_derived.

(** ** Semantic state atoms

    Any predicate on the current state can be an atom, provided some iProp ensures it
    through the state interpretation (e.g. negated points-to facts). *)
Section state_atoms.
  Context {Λ : language} {Σ : gFunctors}.

  Program Definition tps_state (φ : state Λ → thread_pool Λ → Prop) : tps Λ Σ :=
    {| tps_ti _ τ := (let '((Θ, σ), _, _) := τ.2 τ.1 in ⌜φ σ Θ⌝)%I;
       tps_tr τ := let '((Θ, σ), _, _) := τ.2 τ.1 in φ σ Θ |}.
  Next Obligation.
    intros φ ? F [n τf] H. simpl in *. destruct (τf n) as (((Θ&σ)&?)&?). by apply sat_elim in H.
  Qed.

End state_atoms.

Section state_rules.
  Context `{!lantanaGS Λ Σ}.

  Lemma temporal_state (φ : state Λ → thread_pool Λ → Prop) (P : iProp Σ) :
    (∀ σ Θ κs, state_interp σ Θ κs ∗ P ⊢ ⌜φ σ Θ⌝) → ⊢ P ⊨ₜ tps_state φ.
  Proof.
    iIntros (Hφ). iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& _& HP)".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iAssert (⌜φ σ Θ⌝)%I with "[HI HP]" as %Hs.
    { rewrite /history_interp. iDestruct "HI" as "(_& _& SI)". iApply Hφ. iFrame. }
    iIntros "!>" (s h' TQ g v2 Ω2 W' τf γ (BEH& FS& LEv& LEO& LB& HIST& EQTQ)) "([HI' SIa]& MI& WPs)".
    iPoseProof (history_interp_hG_event_lookup with "[$HI' $HE]") as "%Hh".
    apply HIST in Hh as [? Hτ]. simpl. rewrite Hτ. done.
  Qed.

End state_rules.

(** ** Adequacy, up to trace implication *)
Section adequacy.
  Context `{!lantanaGS Λ Σ}.

  Lemma lwp_ti_logic_temporal s h n σ Θ (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)) κs g v Ω W τf γ
    (G : tps Λ Σ) :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    owit_inv_lb (fair_sched_fun γ) Ω W →
    (∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → (∃ i', τf n' = ((Θ', σ'), i', κs'))) →
    ((history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗
      model_interp g v Ω W n (dom Θ) ∗
      (|={⊤}=>m ∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                  (P -∗ |={⊤}=>m [∗ map] i↦e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ v, lift_term i Ψ v }}))))
      ⊢ |={⊤}=> tps_ti G (n, τf).
  Proof.
    iIntros (BEH FS LB HIST) "([HI SIa]& MI& WPs)".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "((%P& #HG& HP& WPs)& HI& %&%&%&%& %H& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO1 LB1].
    iPoseProof (temporal_elim with "HG [$HI $MI $HP]") as "#TF".
    iPoseProof ("WPs" with "HP") as "WPs".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "(WPs& HI& %&%&%&%& %H& MI)".
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
      - iMod "H". iApply sfmupd_lwpupd. iMod "H". by iModIntro.
      - rewrite lwp_fix_unfold_fix /lwp_pre He. iFrame. }
    iMod (all_interp_lwpupd_steps_gmap γ with "WPs [$HI $SIa] MI") as "(WPs& HI& %&%&%&%& %H& MI)".
    { subst Θ. done. }
    { auto. }
    destruct H as [LEO3 LB3].
    iModIntro.
    iApply (tguar_elim with "TF [$HI $MI $WPs]").
    1,2: eauto. 1: lia. all: eauto. etrans; eauto.
  Qed.

End adequacy.

(** The program logic establishes [G]; anything implied by its trace property holds. *)
Theorem lwp_adequacy_temporal (Σ : gFunctors) (Λ : language)
  `{!mupdGpreS Σ} `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))}
  s σ Θ i κs (G : tps Λ Σ) (R : trProp Λ) :
  (∀ τ, tps_tr G τ → R τ) →
  ∀ (τ : trace Λ),
  behavior τ →
  fair_scheduling τ →
  (τ.1 = 0) →
  (τ.2 0 = (Θ, σ, i, κs)) →
  (∀ `{Htemporal : !temporalGS Λ Σ},
     ∃ (c : Ord.t),
     ⊢ |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                (fork_post : thread_id → val Λ → iProp Σ)
                (Ψs : gmap thread_id (H:=pos_countable) (thread_id → val Λ → iProp Σ)),
     let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
     state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
     (£ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
      |={⊤}=>m (∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                  (P -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))) →
  R τ.
Proof.
  intros HR τ BEH FS INIT1 INIT2 Hwp. apply HR.
  assert (iProp_sat
            (|==> ∃ (Hmupd : mupdGS Σ) (Hhist : histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))),
                let _ : temporalGS Λ Σ := TemporalG Hmupd Hhist in
                (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗
                wsat.wsat ∗ wsat.ownE ⊤ ∗
                |={⊤}=> tps_ti G τ)) as Hsat; cycle 1.
  { apply sat_bupd, sat_exists in Hsat. destruct Hsat as (Hmupd& Hsat). apply sat_exists in Hsat. destruct Hsat as (Hhist& Hsat).
    set (Htemp := TemporalG Hmupd Hhist : temporalGS Λ Σ).
    apply (tps_good G (temporalGS0:=Htemp) emp). apply (sat_fupd ⊤).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono. 2: eapply Hsat. simpl. iIntros "($& $& $& $)". }
  assert (Hwp' : ⊢ ∀ Htemporal : temporalGS Λ Σ,
            ∃ (c : Ord.t),
            |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                     (fork_post : thread_id → val Λ → iProp Σ)
                     (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)),
            let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
            state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
            (£ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
             |={⊤}=>m (∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                         (P -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))).
  { iIntros (Htemp). destruct (Hwp Htemp) as [x Hx]. iExists x. iApply Hx. }
  eapply sat_wand; cycle 1.
  { eapply Hwp'. }
  apply (sat_mono True); cycle 1.
  { apply iProp_sat_intro. }
  iIntros "_ H".
  iMod (model_interp_alloc 0) as "(%Hmupd& R& W& WOE& MI)".
  iMod (history_interp_init σ Θ κs) as "(%Hhist& HI)".
  iExists Hmupd, Hhist.
  set (Htemp := TemporalG Hmupd Hhist : temporalGS Λ Σ).
  iDestruct ("H" $! Htemp) as "(%c& H)".
  iDestruct "R" as "(%x& R)".
  iMod (own_update _ (● x) with "R") as "[R LC]".
  { apply (auth_update_alloc x ((c : ordinal_ucmra.OrdUR) ⋅ x)).
    apply (op_local_update_discrete x ε c).
    intros ?. apply auth_valid_trivial. }
  iModIntro. iFrame "R W WOE". rewrite (right_id ε).
  iMod "H" as "(%Hsic& %fork_post& %Ψs& SI& SIa& WPs)".
  iMod ("HI" $! Hsic with "SI") as "HI". iDestruct "MI" as "(MHI& S& T& A& G& MI)".
  iMod (thP_carriers_alloc_threads (dom Θ) with "[$T $G]") as "(T& G& Ths)". 1: set_solver.
  iPoseProof ("WPs" with "LC Ths") as "WPs". rewrite union_empty_l_L.
  destruct τ as [n τf]. simpl in INIT1, INIT2. subst n.
  apply fair_scheduling_fscnt in FS. destruct FS as (γ& FS).
  set (Hlantana := LantanaG Htemp Hsic fork_post : lantanaGS Λ Σ).
  iApply (lwp_ti_logic_temporal (lantanaGS0:=Hlantana) with "[$HI $SIa $MHI $S $T $A $G $MI $WPs]").
  1,2: eauto. 1: apply map_Forall2_empty.
  { intros. rewrite lookup_cons in H0. destruct n'; last done. inv H0. rewrite INIT2. eauto. }
Qed.

(** ** Inferring guarantees

    [IntoTemporal P G] computes a guarantee [G] for [P] from its shape; any iProp at all
    guarantees [tps_true], which is the fallback for leaves without an instance. For an
    existential, the strongest guarantee of the body is inferred first; if it does not
    depend on the witness the quantifier is a ghost one, otherwise it is trace-visible
    (types with the existential property). Only for other types does the search weaken
    the body until its guarantee no longer depends on the witness. *)
Class IntoTemporal `{!lantanaGS Λ Σ} (P : iProp Σ) (G : tps Λ Σ) :=
  into_temporal : ⊢ P ⊨ₜ G.
Global Arguments into_temporal {_ _ _} _ _ {_}.
Global Hint Mode IntoTemporal - - - ! - : typeclass_instances.

(** Big separating conjunctions guarantee the guarded family of their elements' guarantees. *)
Section big_op_rules.
  Context `{!lantanaGS Λ Σ}.

  Lemma temporal_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ) (G : K → A → tps Λ Σ) :
    (∀ k x, Φ k x ⊨ₜ G k x) -∗
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊨ₜ tps_forall (λ k, tps_forall (λ x, tps_impl (m !! k = Some x) (G k x))).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ k x, ⌜m !! k = Some x⌝ → Φ k x)%I with "[]").
    { iIntros "!> H" (k x Hk). by iApply (big_sepM_lookup with "H"). }
    iApply temporal_forall. iIntros (k). iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

  Lemma temporal_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → tps Λ Σ) :
    (∀ k x, Φ k x ⊨ₜ G k x) -∗
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊨ₜ tps_forall (λ k, tps_forall (λ x, tps_impl (l !! k = Some x) (G k x))).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ k x, ⌜l !! k = Some x⌝ → Φ k x)%I with "[]").
    { iIntros "!> H" (k x Hk). by iApply (big_sepL_lookup with "H"). }
    iApply temporal_forall. iIntros (k). iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

  Lemma temporal_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → tps Λ Σ) :
    (∀ x, Φ x ⊨ₜ G x) -∗
    ([∗ set] x ∈ X, Φ x) ⊨ₜ tps_forall (λ x, tps_impl (x ∈ X) (G x)).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ x, ⌜x ∈ X⌝ → Φ x)%I with "[]").
    { iIntros "!> H" (x Hx). by iApply (big_sepS_elem_of with "H"). }
    iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

End big_op_rules.

(** How an existential over a family of guarantees is guaranteed. *)
Class SimplExist `{!lantanaGS Λ Σ} {X : Type} (G : X → tps Λ Σ) (G' : tps Λ Σ) :=
  simpl_exist (P : X → iProp Σ) : (∀ x, P x ⊨ₜ G x) ⊢ (∃ x, P x) ⊨ₜ G'.
Global Hint Mode SimplExist - - - - ! - : typeclass_instances.

(** The trace property inferred for [Q], e.g. to annotate an until. *)
Definition tsem `{!lantanaGS Λ Σ} (Q : iProp Σ) {G : tps Λ Σ} `{!IntoTemporal Q G} : tps Λ Σ := G.
Global Arguments tsem {_ _ _} _ {_ _}.

(** [P] until [Q], with the trace property of [Q] inferred. *)
Notation untilT N k q P Q := (untilI N k false q P%I Q%I (tsem Q%I)).
Notation finallyT N k q Q := (finallyI N k false q Q%I (tsem Q%I)).

(** The inferred trace property of [P], computed so that it no longer mentions ghost-state
    instances: [Definition G : tps Λ Σ := ltac:(tps_of P).] in a section with the instances
    yields a [G] that can be used in an adequacy statement. *)
Ltac tps_of P := let G := eval cbv [tsem] in (tsem P%I) in exact G.

(* A family may mention its argument only through [tsem]s that compute away. *)
Global Hint Extern 0 (SimplExist _ _) => progress unfold tsem : typeclass_instances.

Section into_temporal.
  Context `{!lantanaGS Λ Σ}.
  Implicit Types G : tps Λ Σ.

  (** The fallback, used through the hint below. *)
  Lemma into_temporal_default P : IntoTemporal P tps_true.
  Proof. apply temporal_true. Qed.
  Global Instance into_temporal_pure φ : IntoTemporal (⌜φ⌝ : iProp Σ) (tps_pure φ) | 10.
  Proof. apply temporal_pure. Qed.
  Global Instance into_temporal_sep P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∗ Q) (G1 ∧ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_sep; [iApply H1|iApply H2]. Qed.
  Global Instance into_temporal_and P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∧ Q) (G1 ∧ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_and; [iApply H1|iApply H2]. Qed.
  Global Instance into_temporal_or P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∨ Q) (G1 ∨ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_or; [iApply H1|iApply H2]. Qed.
  Global Instance simpl_exist_ghost {X} G : SimplExist (λ _ : X, G) G | 0.
  Proof. intros P. iIntros "H". by iApply temporal_exist_ghost. Qed.
  Global Instance simpl_exist_visible {X} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) :
    SimplExist G (tps_exist G) | 10.
  Proof. intros P. iIntros "H". by iApply temporal_exist. Qed.
  Global Instance into_temporal_exist {X} (P : X → iProp Σ) (Gx : X → tps Λ Σ) G :
    (∀ x, IntoTemporal (P x) (Gx x)) → SimplExist Gx G → IntoTemporal (∃ x, P x) G | 10.
  Proof. intros H HS. unfold IntoTemporal in *. iApply HS. iIntros (x). iApply H. Qed.
  Global Instance into_temporal_forall {X} (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, IntoTemporal (P x) (G x)) → IntoTemporal (∀ x, P x) (tps_forall G) | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_forall. iIntros (x). iApply H. Qed.
  Global Instance into_temporal_persistently P G :
    IntoTemporal P G → IntoTemporal (□ P) G | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_persistently. iApply H. Qed.
  Global Instance into_temporal_inv N P G :
    IntoTemporal P G → IntoTemporal (inv N P) (tps_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_always. iApply H. Qed.
  Global Instance into_temporal_untilI N k b q P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (untilI N k b q P Q G2) (tps_until G1 G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_until; [iApply H1|iApply H2]. Qed.
  Global Instance into_temporal_state_pred π : IntoTemporal (state_pred_interp π) (tps_atomic π) | 10.
  Proof. apply temporal_atomic. Qed.

  Global Instance into_temporal_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ)
    (G : K → A → tps Λ Σ) :
    (∀ k x, IntoTemporal (Φ k x) (G k x)) →
    IntoTemporal ([∗ map] k ↦ x ∈ m, Φ k x)
      (tps_forall (λ k, tps_forall (λ x, tps_impl (m !! k = Some x) (G k x)))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepM. iIntros (k x). iApply HG. Qed.
  Global Instance into_temporal_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → tps Λ Σ) :
    (∀ k x, IntoTemporal (Φ k x) (G k x)) →
    IntoTemporal ([∗ list] k ↦ x ∈ l, Φ k x)
      (tps_forall (λ k, tps_forall (λ x, tps_impl (l !! k = Some x) (G k x)))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepL. iIntros (k x). iApply HG. Qed.
  Global Instance into_temporal_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → tps Λ Σ) :
    (∀ x, IntoTemporal (Φ x) (G x)) →
    IntoTemporal ([∗ set] x ∈ X, Φ x) (tps_forall (λ x, tps_impl (x ∈ X) (G x))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepS. iIntros (x). iApply HG. Qed.

  Lemma tsem_temporal (Q : iProp Σ) G `{!IntoTemporal Q G} : ⊢ Q ⊨ₜ tsem Q.
  Proof. done. Qed.

End into_temporal.

(* The fallback applies only when the formula and the ghost-state instance contain no evars:
   while a statement is elaborated they may still, and the fallback would then win over the
   precise instances (resolution is retried once the evars are solved). *)
Global Hint Extern 100 (@IntoTemporal ?Λ ?Σ ?H ?P _) =>
  assert_fails (has_evar Λ); assert_fails (has_evar Σ); assert_fails (has_evar H);
  assert_fails (has_evar P); notypeclasses refine (into_temporal_default P) : typeclass_instances.

Section until_inferred.
  Context `{!lantanaGS Λ Σ}.

  (** [finallyI_discharge] for an inferred trace property, with the obligation set split. *)
  Lemma finallyT_discharge E N k g ℓ K (Q : iProp Σ) G2 `{!IntoTemporal Q G2} :
    ↑N ⊆ E → k ∉ K →
    £ (2 : Ord.t) -∗ crP_obls g ℓ ({[k]} ∪ K) -∗ finallyI N k false 1 Q (tsem Q) -∗ Q -∗
    |={E}=>m Q ∗ crP_obls g ℓ K ∗ oblP_discharged k.
  Proof.
    iIntros (HN Hk) "LC Cg HF HQ".
    iMod (finallyI_discharge with "[] LC Cg HF HQ") as "($& Cg& $)";
      [done|set_solver|by iApply tsem_temporal|].
    assert (({[k]} ∪ K) ∖ {[k]} = K) as -> by set_solver. done.
  Qed.

End until_inferred.

(** ** The syntactic [tf] *)
Section embed.
  Context `{!lantanaGS Λ Σ}.

  Lemma tf_temporal (Φ : tf (Π:=state_pred Λ) Σ) : ⊢ ⟦Φ⟧ₗ ⊨ₜ tps_of_tp (tf_to_tp Φ).
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "H". iPoseProof (tf_logic_tf_intuit with "H") as "#TF".
    iIntros "!>" (s h' TQ g v2 Ω2 W' τf γ (BEH& FS& LEv& LEO& LB& HIST& EQTQ)) "([HI SIa]& MI& WPs)".
    rewrite /threads_run. iApply (lwp_fix_ti_logic with "[-]"); eauto. iExists Φ. iSplit; first done. iFrame "HI SIa MI WPs TF".
  Qed.

  (** Old formulas keep their trace content when mixed with new ones. *)
  Global Instance into_temporal_tf_logic (Φ : tf (Π:=state_pred Λ) Σ) :
    IntoTemporal ⟦Φ⟧ₗ (tps_of_tp (tf_to_tp Φ)) | 10.
  Proof. apply tf_temporal. Qed.

End embed.

(** The old adequacy theorem is the case of [tf] formulas. *)
Corollary lwp_adequacy_via_temporal (Σ : gFunctors) (Λ : language)
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
                (Ψs : gmap thread_id (H:=pos_countable) (thread_id → val Λ → iProp Σ)),
     let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
     state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
     (£ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
      |={⊤}=>m (∃ (Φ' : tf Σ),
                  (⌜ tf_to_tp Φ' = Φ ⌝) ∗ (⟦Φ'⟧ₗ) ∗
                  (⟦Φ'⟧ₗ -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))) →
  tp_trace Φ τ.
Proof.
  intros τ BEH FS INIT1 INIT2 Hwp.
  eapply (lwp_adequacy_temporal _ _ s σ Θ i κs (tps_of_tp Φ)); [done..|].
  intros Htemp. destruct (Hwp Htemp) as [c Hc]. exists c.
  iMod Hc as (Hsic fork_post Ψs) "(SI& SIa& H)". iModIntro. iExists Hsic, fork_post, Ψs.
  iFrame "SI SIa". iIntros "LC Ths". iMod ("H" with "LC Ths") as (Φ' <-) "[HΦ' H]".
  iModIntro. iExists ⟦Φ'⟧ₗ. iFrame. iApply tf_temporal.
Qed.

(** ** Examples *)
Section examples.
  Context `{!lantanaGS Λ Σ}.

  (** Ghost quantification over iProp, scoping over two temporal operators. *)
  Local Lemma ex_iprop N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, inv N1 Ψ ∗ finallyI N2 k false 1 Ψ tps_true) ⊨ₜ
      (tps_always tps_true ∧ tps_finally tps_true).
  Proof.
    iApply temporal_exist_ghost. iIntros (Ψ).
    iApply temporal_sep; [iApply temporal_always; iApply temporal_true|].
    iApply temporal_until; [iApply temporal_pure|iApply temporal_true].
  Qed.

  (** An invariant whose content changes over time, each content carrying its own guarantee. *)
  Local Lemma ex_dynamic_inv N G : ⊢ inv N (∃ P : iProp Σ, P ∗ P ⊨ₜ G) ⊨ₜ tps_always G.
  Proof. iApply temporal_always. iApply temporal_certified. Qed.

  (** The same guarantee, inferred. *)
  Local Lemma ex_iprop_inferred N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, inv N1 Ψ ∗ finallyT N2 k 1 Ψ) ⊨ₜ
      (tps_always tps_true ∧ tps_until (tps_pure True) tps_true).
  Proof. apply (into_temporal _ _). Qed.

  (** Trace-visible quantification over a small type is inferred when the guarantee of
      the body depends on the witness. *)
  Local Lemma ex_visible_inferred N (f : nat → Prop) :
    ⊢ (∃ n : nat, inv N ⌜f n⌝) ⊨ₜ tps_exist (λ n : nat, tps_always (tps_pure (f n))).
  Proof. apply (into_temporal _ _). Qed.

  (** The inferred trace property as a closed term. *)
  Local Definition ex_tps_of N1 N2 k : tps Λ Σ :=
    ltac:(tps_of ((∃ Ψ : iProp Σ, inv N1 Ψ ∗ finallyT N2 k 1 Ψ)%I)).
  Local Lemma ex_tps_of_eq N1 N2 k :
    ex_tps_of N1 N2 k = (tps_always tps_true ∧ tps_until (tps_pure True) tps_true)%S.
  Proof. done. Qed.

  (** Quantification over guaranteed iProps in a hypothesis, as in a higher-order spec. *)
  Local Lemma ex_higher_order N G (P : iProp Σ) : P ⊨ₜ G -∗ inv N P ⊨ₜ tps_always G.
  Proof. iApply temporal_always. Qed.

End examples.
