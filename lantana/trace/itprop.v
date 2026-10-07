From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trace_step_indexed.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.

(** * Internalized trace properties

    An [itProp] is a trace property ([trProp], its external reading) together with its
    internalization in the logic ([trIProp], its internal reading), adequate for it: if the
    internal reading is satisfiable, the external one holds. The connectives, state atoms,
    complete and instant properties, and the two entailments between properties: in the
    logic ([G ⊑ H]), for the structure of a property, and on traces ([itProp_external G ⊆ R]),
    for its meaning (see "Trace readings" below). *)

(** ** Internalized trace properties *)

(** [itProp_internal]: the step-indexed reading, which the running system establishes in the
    logic; [itProp_adeq]: its satisfiability implies the external reading [itProp_external]. *)
Record itProp {Λ : language} {Σ : gFunctors} := ItProp {
  itProp_internal : ∀ `{!temporalGS Λ Σ}, trace Λ → iProp Σ;
  itProp_external : trProp Λ;
  itProp_adeq : ∀ `{!temporalGS Λ Σ} (F : iProp Σ) (τ : trace Λ),
    iProp_sat_lc_at_frame F ⊤ (itProp_internal τ) → itProp_external τ;
}.
Global Arguments itProp Λ Σ : clear implicits.
Global Arguments ItProp {Λ Σ}.
Global Arguments itProp_internal {Λ Σ} _ {_}.
Global Arguments itProp_external {Λ Σ}.

Declare Scope itProp_scope.
Delimit Scope itProp_scope with IT.
Bind Scope itProp_scope with itProp.

(** [G ⊑ G']: the step-indexed part of [G] implies that of [G']. *)
Definition itProp_le {Λ Σ} (G G' : itProp Λ Σ) : Prop :=
  ∀ (H : temporalGS Λ Σ) τ, @itProp_internal _ _ G H τ ⊢ @itProp_internal _ _ G' H τ.

Section itProp_connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : itProp Λ Σ.

  Program Definition itProp_pure (p : Prop) : itProp Λ Σ :=
    {| itProp_internal _ := trI_pure p; itProp_external := tr_pure p |}.
  Next Obligation. intros p ? F τ H. by apply sat_elim in H. Qed.

  Definition itProp_true : itProp Λ Σ := itProp_pure True.

  Program Definition itProp_and G1 G2 : itProp Λ Σ :=
    {| itProp_internal _ := trI_and (itProp_internal G1) (itProp_internal G2); itProp_external := tr_and (itProp_external G1) (itProp_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold trI_and in H. apply iProp_sat_lc_at_frame_and in H as [H1 H2].
    split; [eapply itProp_adeq, H1|eapply itProp_adeq, H2].
  Qed.

  Program Definition itProp_or G1 G2 : itProp Λ Σ :=
    {| itProp_internal _ := trI_or (itProp_internal G1) (itProp_internal G2); itProp_external := tr_or (itProp_external G1) (itProp_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H. unfold trI_or in H. apply sat_or in H as [H|H].
    - left. by eapply itProp_adeq.
    - right. by eapply itProp_adeq.
  Qed.

  (** Implication, with any trace property as antecedent: both readings assume it at the
      level of traces. *)
  Program Definition itProp_impl (A G : itProp Λ Σ) : itProp Λ Σ :=
    {| itProp_internal _ := trI_impl (itProp_external A) (itProp_internal G); itProp_external := tr_impl (itProp_external A) (itProp_external G) |}.
  Next Obligation.
    intros A G ? F τ H HA. unfold trI_impl in H. eapply itProp_adeq. eapply sat_impl; [apply H|].
    iIntros "_". by iPureIntro.
  Qed.

  (** Over any type: [sat] commutes with [∀]. *)
  Program Definition itProp_forall {X : Type} (G : X → itProp Λ Σ) : itProp Λ Σ :=
    {| itProp_internal _ := trI_forall X (λ x, itProp_internal (G x)); itProp_external := tr_forall X (λ x, itProp_external (G x)) |}.
  Next Obligation.
    intros X G ? F τ H x. unfold trI_forall in H. eapply itProp_adeq. by apply (sat_forall x) in H.
  Qed.

  (** Existential quantification needs the existential property of the step index, so only
      types smaller than the ordinals of [ordI] qualify (nat, gnames, oids, Ord.t, ...). *)
  Program Definition itProp_exist {X : Type} `{!TypeExistentialProperty X ordI} (G : X → itProp Λ Σ) : itProp Λ Σ :=
    {| itProp_internal _ := trI_exist X (λ x, itProp_internal (G x)); itProp_external := tr_exist X (λ x, itProp_external (G x)) |}.
  Next Obligation.
    intros X ? G ? F τ H. unfold trI_exist in H. apply sat_exists in H as [x H].
    exists x. by eapply itProp_adeq.
  Qed.

  Program Definition itProp_always G : itProp Λ Σ :=
    {| itProp_internal _ := trI_always (itProp_internal G) (trI_pure True); itProp_external := tr_always (itProp_external G) |}.
  Next Obligation.
    intros G ? F τ H.
    cut (tr_always (itProp_external G ∧ tr_pure True)%R τ).
    { unfold tr_always. destruct τ. intros Hτ m Hm. by destruct (Hτ m Hm). }
    eapply (trI_always_tr_always F (itProp_internal G) (trI_pure True) (itProp_external G) (tr_pure True));
      [intros; by eapply itProp_adeq | intros; exact I | exact H].
  Qed.

  Program Definition itProp_until G1 G2 : itProp Λ Σ :=
    {| itProp_internal _ := trI_exist Ord.t (λ a, trI_until Ord.lt a (itProp_internal G1) (itProp_internal G2));
       itProp_external := tr_until (itProp_external G1) (itProp_external G2) |}.
  Next Obligation.
    intros G1 G2 ? F τ H.
    eapply (trI_until_tr_until_gen F (itProp_internal G1) (itProp_internal G2) (itProp_external G1) (itProp_external G2));
      [intros; by eapply itProp_adeq | intros; by eapply itProp_adeq | exact H].
  Qed.

  Definition itProp_finally G : itProp Λ Σ := itProp_until itProp_true G.

  Lemma itProp_le_refl G : itProp_le G G.
  Proof. intros ??. done. Qed.
  Lemma itProp_le_trans G1 G2 G3 : itProp_le G1 G2 → itProp_le G2 G3 → itProp_le G1 G3.
  Proof. intros H1 H2 ??. by rewrite H1 H2. Qed.
  Lemma itProp_always_mono_i `{!temporalGS Λ Σ} (G G' : itProp Λ Σ) :
    ▷ □ (∀ τ, itProp_internal G τ -∗ itProp_internal G' τ) -∗
    ∀ τ, itProp_internal (itProp_always G) τ -∗ itProp_internal (itProp_always G') τ.
  Proof. iIntros "#W" (τ). cbn. by iApply (trI_always_mono_i with "W"). Qed.
  Lemma itProp_until_mono_i `{!temporalGS Λ Σ} (G1 G2 G1' G2' : itProp Λ Σ) :
    ▷ □ (∀ τ, itProp_internal G1 τ -∗ itProp_internal G1' τ) -∗ ▷ □ (∀ τ, itProp_internal G2 τ -∗ itProp_internal G2' τ) -∗
    ∀ τ, itProp_internal (itProp_until G1 G2) τ -∗ itProp_internal (itProp_until G1' G2') τ.
  Proof.
    iIntros "#W1 #W2" (τ). cbn. rewrite /trI_exist. iIntros "[%a H]". iExists a.
    by iApply (trI_until_mono_i with "W1 W2").
  Qed.

End itProp_connectives.

Notation "⌜ p ⌝" := (itProp_pure p) : itProp_scope.
Infix "∧" := itProp_and : itProp_scope.
Infix "∨" := itProp_or : itProp_scope.
Infix "→" := itProp_impl : itProp_scope.
Notation "∀ x .. y , G" := (itProp_forall (λ x, .. (itProp_forall (λ y, G%IT)) ..)) : itProp_scope.
Notation "∃ x .. y , G" := (itProp_exist (λ x, .. (itProp_exist (λ y, G%IT)) ..)) : itProp_scope.
Notation "□ G" := (itProp_always G) (at level 20, right associativity) : itProp_scope.
Notation "◇ G" := (itProp_finally G) (at level 20, right associativity) : itProp_scope.
Notation "G 'Uₜ' H" := (itProp_until G H) (at level 60, right associativity) : itProp_scope.

(** In-logic entailment is the canonical order of properties. *)
Global Instance itProp_sqsubseteq {Λ Σ} : SqSubsetEq (itProp Λ Σ) := itProp_le.

(** ** Semantic state atoms

    Any predicate on the current state can be an atom, provided some iProp ensures it
    through the state interpretation (e.g. negated points-to facts). *)
Section state_atoms.
  Context {Λ : language} {Σ : gFunctors}.

  Program Definition itProp_state (φ : state Λ → thread_pool Λ → Prop) : itProp Λ Σ :=
    {| itProp_internal _ τ := (let '((Θ, σ), _, _) := τ.2 τ.1 in ⌜φ σ Θ⌝)%I;
       itProp_external := tr_state φ |}.
  Next Obligation.
    intros φ ? F [n τf] H. rewrite /tr_state /ts_emb /ts_state /trace_now. simpl in *.
    destruct (τf n) as (((Θ&σ)&?)&?). by apply sat_elim in H.
  Qed.

End state_atoms.

(** ** Complete and instant trace properties

    An implication [A → G] assumes [A] at the level of traces. In the logic it is introduced
    from [A ∧ H ⊑ G] when [A] is complete (its trace reading gives its in-logic reading), and
    eliminated when [A] is instant (the converse). Pure facts, state atoms, always and until
    are complete; the non-temporal ones are also instant. *)
Section complete.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G A : itProp Λ Σ.

  Class ItPropComplete G : Prop :=
    itProp_complete : ∀ (H : temporalGS Λ Σ) τ, itProp_external G τ → ⊢ @itProp_internal _ _ G H τ.
  Class ItPropInstant G : Prop :=
    itProp_instant : ∀ (H : temporalGS Λ Σ) τ, @itProp_internal _ _ G H τ ⊢ ⌜itProp_external G τ⌝.

  (** Completeness. *)
  Global Instance itProp_complete_pure φ : ItPropComplete (itProp_pure φ).
  Proof. intros ? τ H. rewrite /= /trI_pure. by iPureIntro. Qed.
  Global Instance itProp_complete_and G1 G2 : ItPropComplete G1 → ItPropComplete G2 → ItPropComplete (itProp_and G1 G2).
  Proof. intros H1 H2 ? τ [??]. rewrite /= /trI_and. iSplit; [by iApply H1|by iApply H2]. Qed.
  Global Instance itProp_complete_or G1 G2 : ItPropComplete G1 → ItPropComplete G2 → ItPropComplete (itProp_or G1 G2).
  Proof. intros H1 H2 ? τ [?|?]; rewrite /= /trI_or; [iLeft; by iApply H1|iRight; by iApply H2]. Qed.
  Global Instance itProp_complete_impl A G : ItPropComplete G → ItPropComplete (itProp_impl A G).
  Proof. intros HG ? τ H. rewrite /= /trI_impl. iIntros (HA). iApply HG. by apply H. Qed.
  Global Instance itProp_complete_forall {X} (G : X → itProp Λ Σ) :
    (∀ x, ItPropComplete (G x)) → ItPropComplete (itProp_forall G).
  Proof. intros HG ? τ H. rewrite /= /trI_forall. iIntros (x). iApply HG. apply H. Qed.
  Global Instance itProp_complete_exist {X} `{!TypeExistentialProperty X ordI} (G : X → itProp Λ Σ) :
    (∀ x, ItPropComplete (G x)) → ItPropComplete (itProp_exist G).
  Proof. intros HG ? τ [x H]. rewrite /= /trI_exist. iExists x. by iApply HG. Qed.

  Global Instance itProp_complete_always G : ItPropComplete G → ItPropComplete (itProp_always G).
  Proof.
    intros HG ? τ Hτ. rewrite /=.
    iAssert (□ ∀ τ, ⌜tr_always (itProp_external G) τ⌝ → trI_always (itProp_internal G) (trI_pure True) τ)%I as "#H";
      last by iApply "H".
    iLöb as "IH". iIntros "!>" ([n τf] Hal). rewrite trI_always_unfold /trI_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iApply ALC_intro. iMod "Hclose" as "_".
    iModIntro. iSplit.
    { iApply HG. apply (Hal n). lia. }
    iSplit; first by rewrite /trI_pure.
    iApply "IH". iPureIntro. intros m Hm. apply Hal. simpl in Hm. lia.
  Qed.

  Global Instance itProp_complete_until G1 G2 :
    ItPropComplete G1 → ItPropComplete G2 → ItPropComplete (itProp_until G1 G2).
  Proof.
    intros H1 H2 ? [n τf] (m & Hnm & HQ & HP). rewrite /= /trI_exist.
    (* The measure is the number of steps to the right formula. *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → itProp_external G1 (l, τf)) →
              ⊢ trI_until Ord.lt (Ord.from_nat d) (itProp_internal G1) (itProp_internal G2) (n', τf)) as Hu.
    { induction d as [|d IH]; intros n' Hd Hn' HP'; rewrite trI_until_unfold /trI_until_pre;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iNext; iMod "Hclose" as "_"; iModIntro;
        iApply fupd_mask_intro; try set_solver; iIntros "Hclose"; iApply ALC_intro; iMod "Hclose" as "_"; iModIntro.
      - assert (m = n') as -> by lia. iLeft. by iApply H2.
      - iRight. iSplit; first (iApply H1; apply HP'; lia).
        iExists (Ord.from_nat d). iSplit; first (iPureIntro; rewrite Ord.from_nat_S; apply Ord.S_lt).
        iApply (IH (S n')); [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. lia. }
    iExists (Ord.from_nat (m - n)). iApply (Hu _ n eq_refl Hnm). intros l Hl. apply HP. lia.
  Qed.

  Global Instance itProp_complete_finally G : ItPropComplete G → ItPropComplete (itProp_finally G).
  Proof. intros HG. apply itProp_complete_until; [apply itProp_complete_pure|done]. Qed.

  (** Instantness. *)
  Global Instance itProp_instant_pure φ : ItPropInstant (itProp_pure φ).
  Proof. intros ? τ. rewrite /= /trI_pure. by iIntros "%". Qed.
  Global Instance itProp_instant_and G1 G2 : ItPropInstant G1 → ItPropInstant G2 → ItPropInstant (itProp_and G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /trI_and. iIntros "H".
    iAssert ⌜itProp_external G1 τ⌝%I as %?; first by iApply H1; iDestruct "H" as "[$ _]".
    iAssert ⌜itProp_external G2 τ⌝%I as %?; first by iApply H2; iDestruct "H" as "[_ $]".
    by iPureIntro.
  Qed.
  Global Instance itProp_instant_or G1 G2 : ItPropInstant G1 → ItPropInstant G2 → ItPropInstant (itProp_or G1 G2).
  Proof.
    intros H1 H2 ? τ. rewrite /= /trI_or. iIntros "[H|H]".
    - iDestruct (H1 with "H") as %?. iPureIntro. by left.
    - iDestruct (H2 with "H") as %?. iPureIntro. by right.
  Qed.
  Global Instance itProp_instant_impl A G : ItPropInstant G → ItPropInstant (itProp_impl A G).
  Proof.
    intros HG ? τ. rewrite /= /trI_impl. iIntros "H".
    destruct (Classical_Prop.classic (itProp_external A τ)) as [HA|HA].
    - iDestruct (HG with "(H [//])") as %?. iPureIntro. by intros _.
    - iPureIntro. by intros ?.
  Qed.
  Global Instance itProp_instant_forall {X} (G : X → itProp Λ Σ) :
    (∀ x, ItPropInstant (G x)) → ItPropInstant (itProp_forall G).
  Proof.
    intros HG ? τ. rewrite /= /trI_forall /tr_forall.
    destruct (Classical_Prop.classic (∀ x, itProp_external (G x) τ)) as [Hall|Hn]; first by iIntros "_".
    apply Classical_Pred_Type.not_all_ex_not in Hn as [x Hx].
    iIntros "H". iSpecialize ("H" $! x). iDestruct (HG with "H") as %?. done.
  Qed.
  Global Instance itProp_instant_exist {X} `{!TypeExistentialProperty X ordI} (G : X → itProp Λ Σ) :
    (∀ x, ItPropInstant (G x)) → ItPropInstant (itProp_exist G).
  Proof.
    intros HG ? τ. rewrite /= /trI_exist. iIntros "[%x H]". iDestruct (HG with "H") as %?.
    iPureIntro. by exists x.
  Qed.

  Global Instance itProp_complete_state φ : ItPropComplete (itProp_state φ).
  Proof.
    intros ? [n τf]. rewrite /= /tr_state /ts_emb /ts_state /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). intros Hφ. by iPureIntro.
  Qed.
  Global Instance itProp_instant_state φ : ItPropInstant (itProp_state φ).
  Proof.
    intros ? [n τf]. rewrite /= /tr_state /ts_emb /ts_state /trace_now /=.
    destruct (τf n) as (((Θ&σ)&?)&?). by iIntros "%".
  Qed.

End complete.
Global Hint Mode ItPropComplete - - ! : typeclass_instances.
Global Hint Mode ItPropInstant - - ! : typeclass_instances.


(** ** The model

    Under the assumptions of the adequacy theorem (adequacy_temporal.v), the logic has a
    model: a property valid in the logic holds on the trace. Hence in-logic entailment is
    sound for the trace readings of complete properties, and it is not complete for them. *)
Section model.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G H : itProp Λ Σ.
  Local Notation histGpreS := (histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))).

  Lemma itProp_valid_ext `{!mupdGpreS Σ} `{!histGpreS} `{!tregGS.tregGpreS Λ Σ} G τ :
    (∀ Ht : temporalGS Λ Σ, ⊢ itProp_internal G τ) → itProp_external G τ.
  Proof.
    intros HG. destruct (τ.2 τ.1) as [[[Θ σ] i] κs].
    assert (iProp_sat (|==> ∃ (Hmupd : mupdGS Σ)
                (Hhist : histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ)))
                (Htreg : tregGS.tregGS Λ Σ),
              (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗ wsat.wsat ∗ wsat.ownE ⊤))
      as Hsat.
    { eapply sat_mono; last apply iProp_sat_intro. iIntros "_".
      iMod (model_interp_alloc 0) as "(%Hmupd& R& W& WOE& _)".
      iMod (history_interp_init (Λ:=Λ) σ Θ κs) as (Hhist) "_".
      iMod (treg_alloc (Λ:=Λ)) as (Htreg) "_".
      iModIntro. iExists Hmupd, Hhist, Htreg. iFrame. }
    apply sat_bupd, sat_exists in Hsat as [Hmupd Hsat].
    apply sat_exists in Hsat as [Hhist Hsat]. apply sat_exists in Hsat as [Htreg Hsat].
    set (Htemp := TemporalG Hmupd Hhist Htreg : temporalGS Λ Σ).
    apply (itProp_adeq G (temporalGS0:=Htemp) emp).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono; last exact Hsat. iIntros "($& $& $)". iApply (HG Htemp).
  Qed.

  (** Soundness: for a complete [G], in-logic entailment implies trace inclusion. *)
  Lemma itProp_le_sound `{!mupdGpreS Σ} `{!histGpreS} `{!tregGS.tregGpreS Λ Σ} G G' `{!ItPropComplete G} :
    G ⊑ G' → itProp_external G ⊆ itProp_external G'.
  Proof.
    intros Hle τ HG. apply itProp_valid_ext. intros Ht. rewrite -(Hle Ht τ). by apply itProp_complete.
  Qed.

  (** Incompleteness: [□ ⊥ ⊆ ⊥] holds on traces, but [□ ⊥ ⊑ ⊥] does not hold in the logic
      (the reading of [□ ⊥] starts with a later, so it is proved by Löb induction). *)
  Lemma itProp_always_elim_not_le `{!mupdGpreS Σ} `{!histGpreS} `{!tregGS.tregGpreS Λ Σ} (τ : trace Λ) :
    ¬ ((□ ⌜False⌝)%IT ⊑ (⌜False⌝ : itProp Λ Σ)%IT).
  Proof.
    intros Hle. apply (itProp_valid_ext (itProp_pure False) τ). intros Ht.
    iLöb as "IH". iPoseProof (Hle Ht τ with "[IH]") as "%HF"; last done.
    rewrite /= trI_always_unfold /trI_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "_". iNext. done.
  Qed.

End model.
