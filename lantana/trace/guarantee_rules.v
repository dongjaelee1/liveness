From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export guarantee.
From transfinite.stepindex Require Import ordinals.

(** * Rules for temporal guarantees

    The interface of [P ⊨ₜ G] (guarantee.v): monotonicity in [P] ([guar_mono]) and in
    [G] ([guar_weaken], [guar_cast]), the rules for the connectives of [P], the
    canonical property [itrProp_canon P] and its completeness, state atoms ([StateFact]),
    implications and big separating conjunctions. The rules for the temporal formulas
    [alwaysI] and [untilI] are in temporal_formula_rules.v. *)

Section rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : itrProp Λ Σ.

  Lemma guar_weaken P G G' : G ⊑ G' → P ⊨ₜ G ⊢ P ⊨ₜ G'.
  Proof.
    iIntros (Hle) "#HG !>". iIntros (?????????) "H". iApply record_mono; first done. by iApply "HG".
  Qed.

  (** A trace-level consequence [R] of [G] is guaranteed as the cast of [G] to [R]: the way
      to export what a guarantee implies. *)
  Lemma guar_cast P G R (pf : itrProp_external G ⊆ R) : P ⊨ₜ G ⊢ P ⊨ₜ itrProp_cast G R pf.
  Proof. apply guar_weaken, itrProp_cast_le. Qed.

  Lemma guar_mono P Q G : □ (Q -∗ P) -∗ P ⊨ₜ G -∗ Q ⊨ₜ G.
  Proof.
    iIntros "#HQP #HG !>". iIntros (?????????) "(HI& MI& HQ)". iApply "HG". iFrame. by iApply "HQP".
  Qed.

  Lemma guar_true P : ⊢ P ⊨ₜ itrProp_true.
  Proof.
    iIntros "!>" (?????????) "_". iApply record_intro. iIntros "!>" (????????????) "_ _ _ _". done.
  Qed.

  Lemma guar_pure (φ : Prop) : ⊢ ⌜φ⌝ ⊨ₜ itrProp_pure φ.
  Proof.
    iIntros "!>" (?????????) "(_& _& %Hφ)". iApply record_intro. iIntros "!>" (????????????) "_ _ _ _". done.
  Qed.

  Lemma guar_and P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∧ Q) ⊨ₜ (G1 ∧ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& HPQ)".
    iPoseProof (guar_elim with "HG1 [$HI $MI HPQ]") as "#T1"; first by iDestruct "HPQ" as "[$ _]".
    iPoseProof (guar_elim with "HG2 [$HI $MI HPQ]") as "#T2"; first by iDestruct "HPQ" as "[_ $]".
    iApply record_intro. iIntros "!>" (????????????) "#ST %H #B W". iSplit.
    - by iApply (record_elim with "T1 ST [//] B W").
    - by iApply (record_elim with "T2 ST [//] B W").
  Qed.

  Lemma guar_sep P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∗ Q) ⊨ₜ (G1 ∧ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& HP& HQ)".
    iPoseProof (guar_elim with "HG1 [$HI $MI $HP]") as "#T1".
    iPoseProof (guar_elim with "HG2 [$HI $MI $HQ]") as "#T2".
    iApply record_intro. iIntros "!>" (????????????) "#ST %H #B W". iSplit.
    - by iApply (record_elim with "T1 ST [//] B W").
    - by iApply (record_elim with "T2 ST [//] B W").
  Qed.

  Lemma guar_or P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∨ Q) ⊨ₜ (G1 ∨ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& [HP | HQ])".
    - iPoseProof (guar_elim with "HG1 [$HI $MI $HP]") as "#T1".
      iApply record_intro. iIntros "!>" (????????????) "#ST %H #B W". iLeft.
      by iApply (record_elim with "T1 ST [//] B W").
    - iPoseProof (guar_elim with "HG2 [$HI $MI $HQ]") as "#T2".
      iApply record_intro. iIntros "!>" (????????????) "#ST %H #B W". iRight.
      by iApply (record_elim with "T2 ST [//] B W").
  Qed.

  (** The right formula fulfils an until at once; the later of the guarantee is stripped
      by the step of the until. *)
  Lemma guar_until_now P G1 G2 : ▷ (P ⊨ₜ G2) -∗ P ⊨ₜ itrProp_until G1 G2.
  Proof.
    iIntros "#HG !>" (h n σ Θ κs m i Ω W) "(HI& MI& HP)".
    iPoseProof (guar_elim_later_guar P G2 with "HG [$HP $HI $MI]") as "#T".
    iApply record_intro. iIntros "!>" (????????????) "#ST %H #B W".
    rewrite /= /trI_exist. iExists Ord.O. rewrite trI_until_unfold /trI_until_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iApply ALC_intro. iMod "close" as "_".
    iModIntro. iLeft. by iApply (record_elim with "T ST [//] B W").
  Qed.

  (** Universal quantification over any type. *)
  Lemma guar_forall {X : Type} (P : X → iProp Σ) (G : X → itrProp Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∀ x, P x) ⊨ₜ itrProp_forall G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& HP)".
    iAssert (∀ x, record (G x) _)%I with "[-]" as "#T".
    { iIntros (x). iApply (guar_elim with "HG"). iFrame. iApply "HP". }
    iApply record_intro. iIntros "!>" (????????????) "#ST %H #B W". iIntros (x).
    by iApply (record_elim with "T ST [//] B W").
  Qed.

  Lemma guar_canon Q : ⊢ Q ⊨ₜ itrProp_canon Q.
  Proof.
    iApply (guar_mono (∀ _ : {G : itrProp Λ Σ | ⊢ Q ⊨ₜ G}, Q)%I with "[]").
    { iIntros "!> HQ" (?). done. }
    iApply guar_forall. iIntros ([G HG]). iApply HG.
  Qed.
  Lemma itrProp_canon_le Q G : (⊢ Q ⊨ₜ G) → itrProp_le (itrProp_canon Q) G.
  Proof.
    intros HG ??. rewrite /= /trI_forall. iIntros "H". iApply ("H" $! (exist (λ G, ⊢ Q ⊨ₜ G) G HG)).
  Qed.
  Lemma itrProp_canon_ext Q G τ : (⊢ Q ⊨ₜ G) → itrProp_external (itrProp_canon Q) τ → itrProp_external G τ.
  Proof. intros HG H. apply (H (exist (λ G, ⊢ Q ⊨ₜ G) G HG)). Qed.

  (** [itrProp_canon Q] is the greatest lower bound of what [Q] validly guarantees: through it,
      the rules are complete up to in-logic entailment. *)
  Lemma guar_canon_complete Q G : (⊢ Q ⊨ₜ G) ↔ itrProp_canon Q ⊑ G.
  Proof.
    split; first apply itrProp_canon_le. intros Hle.
    iApply (guar_weaken _ _ _ Hle). iApply guar_canon.
  Qed.

  (** Its trace reading: the strongest trace property [Q] validly guarantees. *)
  Definition tr_canon Q : trProp Λ := itrProp_external (itrProp_canon Q).
  Lemma tr_canon_le Q R : tr_canon Q ⊆ R ↔ ∃ G, (⊢ Q ⊨ₜ G) ∧ itrProp_external G ⊆ R.
  Proof.
    split.
    - intros HR. exists (itrProp_canon Q). split; [apply guar_canon|done].
    - intros (G & HG & HR) τ Hτ. apply HR. by eapply itrProp_canon_ext.
  Qed.

  (** Trace-visible existential quantification, over small types. *)
  Lemma guar_exist {X : Type} `{!TypeExistentialProperty X ordI} (P : X → iProp Σ) (G : X → itrProp Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∃ x, P x) ⊨ₜ itrProp_exist G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& [%x HP])".
    iPoseProof (guar_elim with "HG [$HI $MI $HP]") as "#T".
    iApply record_intro. iIntros "!>" (????????????) "#ST %H #B W". iExists x.
    by iApply (record_elim with "T ST [//] B W").
  Qed.

  (** Ghost existential quantification, over any type: the witness does not show in the
      trace property. *)
  Lemma guar_exist_ghost {X : Type} (P : X → iProp Σ) G :
    (∀ x, P x ⊨ₜ G) -∗ (∃ x, P x) ⊨ₜ G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& [%x HP])". iApply (guar_elim with "HG"). iFrame.
  Qed.

  (** An iProp carrying its own guarantee: such pairs can be stored in invariants and
      saved propositions, and quantified over. *)
  Lemma guar_packed G : ⊢ (∃ P, P ∗ P ⊨ₜ G) ⊨ₜ G.
  Proof.
    iIntros "!>" (?????????) "(HI& MI& (%P& HP& #HG))". iApply (guar_elim with "HG"). iFrame.
  Qed.

  Lemma guar_persistently P G : P ⊨ₜ G -∗ □ P ⊨ₜ G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& #HP)". iApply (guar_elim with "HG"). iFrame "HI MI HP".
  Qed.

  (** A persistent token [C] excluding [A]: a guarantee of [B] is one of [A ∨ B]. With
      [alwaysI_register_guar], this gives a stronger reading of an invariant. *)
  Lemma guar_or_excl (A B C : iProp Σ) G `{!Persistent C} :
    (C ∗ A ⊢ False) → C -∗ B ⊨ₜ G -∗ (A ∨ B) ⊨ₜ G.
  Proof.
    iIntros (Hexcl) "#HC #HB". iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& [HA|HB'])".
    - iExFalso. iApply Hexcl. iFrame "HC HA".
    - iApply (guar_elim with "HB"). iFrame.
  Qed.

End rules.

(** ** State atoms

    The atoms of temporal properties are facts about the current state: an iProp [P]
    determines [φ] when the state interpretation and [P] entail [φ] ([StateFact]), and then
    [P] guarantees [itrProp_state φ] ([guar_state_fact]). A language provides the facts of
    its assertions, e.g. [l ↦ v] for heap_lang (temporal_laws.v). *)
Section state_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Class StateFact (P : iProp Σ) (φ : state Λ → thread_pool Λ → Prop) : Prop :=
    state_fact σ Θ κs : state_interp σ Θ κs ∗ P ⊢ ⌜φ σ Θ⌝.

  Lemma guar_state (φ : state Λ → thread_pool Λ → Prop) (P : iProp Σ) :
    (∀ σ Θ κs, state_interp σ Θ κs ∗ P ⊢ ⌜φ σ Θ⌝) → ⊢ P ⊨ₜ itrProp_state φ.
  Proof.
    iIntros (Hφ). iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& _& HP)".
    iPoseProof (history_interp_hist_event_now with "HI") as "#HE".
    iAssert (⌜φ σ Θ⌝)%I with "[HI HP]" as %Hs.
    { rewrite /history_interp. iDestruct "HI" as "(_& _& SI)". iApply Hφ. iFrame. }
    iApply record_intro.
    iIntros "!>" (Sys l h' g v2 Ω2 W' τf γ σ' Θ' κs') "_ %H _ (HI'& MI& Sys)".
    destruct H as (BEH& FS& LB& HIST).
    iPoseProof (history_interp_hist_event_lookup with "[$HI' $HE]") as "%Hh".
    apply HIST in Hh as [? Hτ]. simpl. rewrite Hτ. done.
  Qed.

  Lemma guar_state_fact P φ `{!StateFact P φ} : ⊢ P ⊨ₜ itrProp_state φ.
  Proof. apply guar_state, state_fact. Qed.

End state_rules.

(** ** Implications

    The antecedent of [A → G] is read on the trace ([itrProp_impl]), so [A → G] is [¬A ∨ G]
    ([itrProp_impl_or_not]), a statement about traces: the general way to export one is the
    cast of a guarantee ([guar_cast]) after trace-level reasoning. The rules below stay
    in the logic and produce [itrProp_impl] itself: from a complete antecedent
    ([guar_impl_intro]), by weakening ([guar_impl_weaken]), and for a pure antecedent
    of an iProp implication ([guar_impl]). An iProp antecedent that the context does not
    provide cannot be used ([naive_impl_rule_unsound], guarantee_infer.v). *)
Section impl_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma guar_impl_intro P A H G `{!ItrPropComplete A} :
    (A ∧ H)%ITR ⊑ G → P ⊨ₜ H ⊢ P ⊨ₜ (A → G).
  Proof. intros HG. by apply guar_weaken, itrProp_impl_intro. Qed.

  Lemma guar_impl_weaken P A G : P ⊨ₜ G ⊢ P ⊨ₜ (A → G).
  Proof. apply guar_weaken, itrProp_impl_intro_le. Qed.

  (** A pure antecedent is decided outside the logic. *)
  Lemma guar_impl (φ : Prop) P G : P ⊨ₜ G -∗ (⌜φ⌝ → P) ⊨ₜ (⌜φ⌝ → G).
  Proof.
    iIntros "#HG". destruct (Classical_Prop.classic φ) as [Hφ|Hφ].
    - iApply guar_impl_weaken. iApply (guar_mono with "[] HG"). iIntros "!> HP". by iApply "HP".
    - iApply (guar_weaken _ itrProp_true); last iApply guar_true.
      intros ??. rewrite /= /trI_impl. by iIntros "_ %".
  Qed.

End impl_rules.

(** Big separating conjunctions guarantee the guarded family of their elements' guarantees. *)
Section big_op_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma guar_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ) (G : K → A → itrProp Λ Σ) :
    (∀ k x, Φ k x ⊨ₜ G k x) -∗
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊨ₜ itrProp_forall (λ k, itrProp_forall (λ x, itrProp_impl ⌜m !! k = Some x⌝ (G k x))).
  Proof.
    iIntros "#HG". iApply (guar_mono (∀ k x, ⌜m !! k = Some x⌝ → Φ k x)%I with "[]").
    { iIntros "!> H" (k x Hk). by iApply (big_sepM_lookup with "H"). }
    iApply guar_forall. iIntros (k). iApply guar_forall. iIntros (x). iApply guar_impl. iApply "HG".
  Qed.

  Lemma guar_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → itrProp Λ Σ) :
    (∀ k x, Φ k x ⊨ₜ G k x) -∗
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊨ₜ itrProp_forall (λ k, itrProp_forall (λ x, itrProp_impl ⌜l !! k = Some x⌝ (G k x))).
  Proof.
    iIntros "#HG". iApply (guar_mono (∀ k x, ⌜l !! k = Some x⌝ → Φ k x)%I with "[]").
    { iIntros "!> H" (k x Hk). by iApply (big_sepL_lookup with "H"). }
    iApply guar_forall. iIntros (k). iApply guar_forall. iIntros (x). iApply guar_impl. iApply "HG".
  Qed.

  Lemma guar_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → itrProp Λ Σ) :
    (∀ x, Φ x ⊨ₜ G x) -∗
    ([∗ set] x ∈ X, Φ x) ⊨ₜ itrProp_forall (λ x, itrProp_impl ⌜x ∈ X⌝ (G x)).
  Proof.
    iIntros "#HG". iApply (guar_mono (∀ x, ⌜x ∈ X⌝ → Φ x)%I with "[]").
    { iIntros "!> H" (x Hx). by iApply (big_sepS_elem_of with "H"). }
    iApply guar_forall. iIntros (x). iApply guar_impl. iApply "HG".
  Qed.

End big_op_rules.
