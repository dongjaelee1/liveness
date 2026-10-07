From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export itprop_rules.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties axioms.

(** * Least and greatest fixpoints of trace properties

    For a body [F] monotone in both readings ([ItPropMono]): [itProp_nu F], the union of the
    post-fixpoints of [F], and [itProp_mu F], the union of ordinal approximants
    [μ_α := F (∃ β < α, μ_β)]. Always and until are such fixpoints. *)

(* The proof mode must not unfold the connectives, which are records. *)
#[local] Typeclasses Opaque itProp_pure itProp_and itProp_or itProp_impl itProp_forall itProp_exist
  itProp_always itProp_until itProp_state.

(** ** Trace predicates, the in-logic step, and the next position *)
Section connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : itProp Λ Σ.

  (** Any trace predicate, read in the logic as a pure fact. *)
  Program Definition itProp_trp (R : trProp Λ) : itProp Λ Σ :=
    {| itProp_internal _ τ := ⌜R τ⌝%I; itProp_external := R |}.
  Next Obligation. intros R ? F τ H. by apply sat_elim in H. Qed.

  (** [⊳ G]: [G] after one step of the logic; at the level of traces, just [G]. *)
  Program Definition itProp_later G : itProp Λ Σ :=
    {| itProp_internal _ τ := (|={⊤,∅}=> ▷ |={∅,⊤}=> itProp_internal G τ)%I; itProp_external := itProp_external G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_later, sat_fupd in H. by eapply itProp_adeq. Qed.

  (** [○ G]: [G] at the next position. *)
  Program Definition itProp_next G : itProp Λ Σ :=
    {| itProp_internal _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> itProp_internal G (trace_next τ)))%I;
       itProp_external τ := itProp_external G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply itProp_adeq. Qed.

  (** [⊚ G]: [G] after the step taken at the current position. In the logic this is the
      step's credits and mask change; at the level of traces it is just [G]. *)
  Program Definition itProp_step G : itProp Λ Σ :=
    {| itProp_internal _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> itProp_internal G τ))%I; itProp_external := itProp_external G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply itProp_adeq. Qed.

  (** [○' G]: [G] read at the next position, with no modality; [○ G] is [⊚ ○' G]. *)
  Program Definition itProp_shift G : itProp Λ Σ :=
    {| itProp_internal _ τ := itProp_internal G (trace_next τ); itProp_external τ := itProp_external G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. by eapply itProp_adeq. Qed.

  Lemma itProp_later_mono G G' : itProp_le G G' → itProp_le (itProp_later G) (itProp_later G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    by iApply HG.
  Qed.
  Lemma itProp_next_mono G G' : itProp_le G G' → itProp_le (itProp_next G) (itProp_next G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma itProp_step_mono G G' : itProp_le G G' → itProp_le (itProp_step G) (itProp_step G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma itProp_shift_mono G G' : itProp_le G G' → itProp_le (itProp_shift G) (itProp_shift G').
  Proof. intros HG ? τ. rewrite /=. by iApply HG. Qed.

  Lemma itProp_exist_lub {X} `{!TypeExistentialProperty X ordI} (G : X → itProp Λ Σ) G' :
    (∀ x, itProp_le (G x) G') → itProp_le (itProp_exist G) G'.
  Proof. intros HG ? τ. rewrite /= /trI_exist. iIntros "[%x H]". by iApply HG. Qed.
  Lemma itProp_exist_ub {X} `{!TypeExistentialProperty X ordI} (G : X → itProp Λ Σ) x :
    itProp_le (G x) (itProp_exist G).
  Proof. intros ? τ. rewrite /= /trI_exist. iIntros "H". by iExists x. Qed.

End connectives.

Global Typeclasses Opaque itProp_trp itProp_later itProp_next.

(** ** Monotone bodies *)
Class ItPropMono {Λ Σ} (F : itProp Λ Σ → itProp Λ Σ) : Prop := {
  itProp_mono_le X Y : itProp_le X Y → itProp_le (F X) (F Y);
  itProp_mono_ext X Y : (∀ τ, itProp_external X τ → itProp_external Y τ) → ∀ τ, itProp_external (F X) τ → itProp_external (F Y) τ;
}.
Global Hint Mode ItPropMono - - ! : typeclass_instances.

Section mono_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : itProp Λ Σ → itProp Λ Σ.

  Global Instance itProp_mono_id : ItPropMono (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. split; auto. Qed.
  Global Instance itProp_mono_const G : ItPropMono (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. split; auto using itProp_le_refl. Qed.
  Global Instance itProp_mono_and F1 F2 :
    ItPropMono F1 → ItPropMono F2 → ItPropMono (λ X, itProp_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply itProp_and_mono; by apply itProp_mono_le.
    - intros X Y HXY τ [??]. split; [by apply (itProp_mono_ext (F:=F1) X Y)|by apply (itProp_mono_ext (F:=F2) X Y)].
  Qed.
  Global Instance itProp_mono_or F1 F2 :
    ItPropMono F1 → ItPropMono F2 → ItPropMono (λ X, itProp_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply itProp_or_mono; by apply itProp_mono_le.
    - intros X Y HXY τ [?|?]; [left; by apply (itProp_mono_ext (F:=F1) X Y)|right; by apply (itProp_mono_ext (F:=F2) X Y)].
  Qed.
  Global Instance itProp_mono_impl A F : ItPropMono F → ItPropMono (λ X, itProp_impl A (F X)).
  Proof.
    intros HF. split.
    - intros. apply itProp_impl_mono; [done|by apply itProp_mono_le].
    - intros X Y HXY τ H HA. apply (itProp_mono_ext (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance itProp_mono_forall {A} (F : A → itProp Λ Σ → itProp Λ Σ) :
    (∀ a, ItPropMono (F a)) → ItPropMono (λ X, itProp_forall (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply itProp_forall_mono. intros a. by apply itProp_mono_le.
    - intros X Y HXY τ H a. apply (itProp_mono_ext (F:=F a) X Y); [done|apply H].
  Qed.
  Global Instance itProp_mono_exist {A} `{!TypeExistentialProperty A ordI} (F : A → itProp Λ Σ → itProp Λ Σ) :
    (∀ a, ItPropMono (F a)) → ItPropMono (λ X, itProp_exist (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply itProp_exist_mono. intros a. by apply itProp_mono_le.
    - intros X Y HXY τ [a H]. exists a. by apply (itProp_mono_ext (F:=F a) X Y).
  Qed.
  Global Instance itProp_mono_later F : ItPropMono F → ItPropMono (λ X, itProp_later (F X)).
  Proof.
    intros HF. split.
    - intros. apply itProp_later_mono. by apply itProp_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (itProp_mono_ext (F:=F) X Y).
  Qed.
  Global Instance itProp_mono_next F : ItPropMono F → ItPropMono (λ X, itProp_next (F X)).
  Proof.
    intros HF. split.
    - intros. apply itProp_next_mono. by apply itProp_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (itProp_mono_ext (F:=F) X Y).
  Qed.
  Global Instance itProp_mono_step F : ItPropMono F → ItPropMono (λ X, itProp_step (F X)).
  Proof.
    intros HF. split.
    - intros. apply itProp_step_mono. by apply itProp_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (itProp_mono_ext (F:=F) X Y).
  Qed.
  Global Instance itProp_mono_shift F : ItPropMono F → ItPropMono (λ X, itProp_shift (F X)).
  Proof.
    intros HF. split.
    - intros. apply itProp_shift_mono. by apply itProp_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (itProp_mono_ext (F:=F) X Y).
  Qed.
  Global Instance itProp_mono_always F : ItPropMono F → ItPropMono (λ X, itProp_always (F X)).
  Proof.
    intros HF. split.
    - intros. apply itProp_always_mono. by apply itProp_mono_le.
    - intros X Y HXY [n τf] H m Hm. apply (itProp_mono_ext (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance itProp_mono_until F1 F2 :
    ItPropMono F1 → ItPropMono F2 → ItPropMono (λ X, itProp_until (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply itProp_until_mono; by apply itProp_mono_le.
    - intros X Y HXY [n τf] (m & Hm & HQ & HP). exists m. split_and!; [done| |].
      + by apply (itProp_mono_ext (F:=F2) X Y).
      + intros l Hl. apply (itProp_mono_ext (F:=F1) X Y); [done|by apply HP].
  Qed.

End mono_instances.

(** ** Continuous bodies

    [F] commutes, in the logic, with unions of increasing chains indexed by ordinals. Guarded
    bodies are not continuous: the step index ranges beyond [Ord.t], so [▷ ∃ α, X α] does
    not give [∃ α, ▷ X α]. *)
Class ItPropCont {Λ Σ} (F : itProp Λ Σ → itProp Λ Σ) : Prop :=
  itProp_cont (X : Ord.t → itProp Λ Σ) :
    (∀ α β, Ord.le α β → itProp_le (X α) (X β)) →
    itProp_le (F (itProp_exist X)) (itProp_exist (λ α, F (X α))).
Global Hint Mode ItPropCont - - ! : typeclass_instances.

Section cont_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : itProp Λ Σ → itProp Λ Σ.

  Global Instance itProp_cont_id : ItPropCont (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. intros X _. apply itProp_le_refl. Qed.
  Global Instance itProp_cont_const G : ItPropCont (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. intros X _ ? τ. rewrite /= /trI_exist. iIntros "H". by iExists Ord.O. Qed.
  Global Instance itProp_cont_and F1 F2 `{!ItPropMono F1, !ItPropMono F2} :
    ItPropCont F1 → ItPropCont F2 → ItPropCont (λ X, itProp_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2 X HX ? τ. rewrite /= /trI_and (H1 X HX _ τ) (H2 X HX _ τ) /= /trI_exist.
    rewrite bi.and_exist_r. iIntros "[%α H]". rewrite bi.and_exist_l. iDestruct "H" as (β) "H".
    iExists (Ord.union α β). iSplit.
    - iDestruct "H" as "[H _]". iApply (itProp_mono_le (X α)); [apply HX, Ord.union_l|done].
    - iDestruct "H" as "[_ H]". iApply (itProp_mono_le (X β)); [apply HX, Ord.union_r|done].
  Qed.
  Global Instance itProp_cont_or F1 F2 :
    ItPropCont F1 → ItPropCont F2 → ItPropCont (λ X, itProp_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2 X HX ? τ. rewrite /= /trI_or (H1 X HX _ τ) (H2 X HX _ τ) /= /trI_exist.
    iIntros "[[%α H]|[%α H]]"; iExists α; [by iLeft|by iRight].
  Qed.
  Global Instance itProp_cont_impl A F : ItPropCont F → ItPropCont (λ X, itProp_impl A (F X)).
  Proof.
    intros HF X HX ? τ. rewrite /= /trI_impl (HF X HX _ τ) /= /trI_exist. iIntros "H".
    destruct (classic (itProp_external A τ)) as [HA|HA].
    - iDestruct ("H" $! HA) as (α) "H". iExists α. by iIntros "_".
    - iExists Ord.O. by iIntros (?).
  Qed.
  Global Instance itProp_cont_exist {A} `{!TypeExistentialProperty A ordI} (F : A → itProp Λ Σ → itProp Λ Σ) :
    (∀ a, ItPropCont (F a)) → ItPropCont (λ X, itProp_exist (λ a, F a X)).
  Proof.
    intros HF X HX ? τ. rewrite /= /trI_exist. iIntros "[%a H]".
    rewrite (HF a X HX _ τ) /= /trI_exist. iDestruct "H" as (α) "H". iExists α, a. done.
  Qed.
  Global Instance itProp_cont_shift F : ItPropCont F → ItPropCont (λ X, itProp_shift (F X)).
  Proof. intros HF X HX ? τ. rewrite /= (HF X HX _ (trace_next τ)) /= /trI_exist. done. Qed.

End cont_instances.

(** ** Greatest fixpoints *)
Section nu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : itProp Λ Σ.

  Program Definition itProp_nu (F : itProp Λ Σ → itProp Λ Σ) `{!ItPropMono F} : itProp Λ Σ :=
    {| itProp_internal H τ := (∃ X : itProp Λ Σ, ⌜itProp_le X (F X)⌝ ∧ @itProp_internal _ _ X H τ)%I;
       itProp_external := tr_gfp (λ R, itProp_external (F (itProp_trp R))) |}.
  Next Obligation.
    intros F HF H F0 τ Hsat.
    pose (I := λ (H' : temporalGS Λ Σ) (τ' : trace Λ),
                 (∃ X : itProp Λ Σ, ⌜itProp_le X (F X)⌝ ∧ @itProp_internal _ _ X H' τ')%I).
    (* The traces at which the in-logic reading is satisfiable, for some instance. *)
    pose (S := λ τ', ∃ (H' : temporalGS Λ Σ) (F' : iProp Σ), iProp_sat_lc_at_frame F' ⊤ (I H' τ')).
    assert (HS : ∀ (H' : temporalGS Λ Σ) (F' : iProp Σ) τ',
               iProp_sat_lc_at_frame F' ⊤ (I H' τ') → S τ').
    { intros H' F' τ' Hs. by exists H', F'. }
    pose (N := ItProp I S HS).
    (* [S] is a post-fixpoint of the trace functor. *)
    exists S. split; last by exists H, F0.
    intros τ' (H' & F' & Hs).
    assert (HXN : ∀ X, itProp_le X (F X) → itProp_le X N).
    { intros X HX ? τ''. rewrite /=. iIntros "HX". iExists X. by iFrame. }
    assert (HIN : I H' τ' ⊢ @itProp_internal _ _ (F N) H' τ').
    { iIntros "[%X [%HX HXt]]". iApply (itProp_mono_le X N (HXN X HX)). by iApply HX. }
    apply (sat_mono _ _ HIN) in Hs. apply (itProp_adeq (F N)) in Hs.
    eapply (itProp_mono_ext N (itProp_trp S)); last exact Hs. done.
  Qed.

  Context (F : itProp Λ Σ → itProp Λ Σ) `{!ItPropMono F}.

  Lemma itProp_nu_coind X : itProp_le X (F X) → itProp_le X (itProp_nu F).
  Proof. intros HX ? τ. rewrite /=. iIntros "H". iExists X. by iFrame. Qed.

  Lemma itProp_nu_unfold_l : itProp_le (itProp_nu F) (F (itProp_nu F)).
  Proof.
    intros ? τ. rewrite {1}/itProp_internal /=. iIntros "[%X [%HX H]]".
    iApply (itProp_mono_le X (itProp_nu F)); first by apply itProp_nu_coind. by iApply HX.
  Qed.

  Lemma itProp_nu_unfold_r : itProp_le (F (itProp_nu F)) (itProp_nu F).
  Proof. apply itProp_nu_coind, itProp_mono_le, itProp_nu_unfold_l. Qed.

  Lemma itProp_nu_ext τ : itProp_external (itProp_nu F) τ ↔ tr_gfp (λ R, itProp_external (F (itProp_trp R))) τ.
  Proof. done. Qed.

End nu.

(** ** Least fixpoints, with ordinal approximants

    The ordinal is the measure a least fixpoint needs in a step-indexed logic: without it, a
    guarded body has a unique fixpoint, and [μ] would be [ν]. *)
Section mu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : itProp Λ Σ.
  Context (F : itProp Λ Σ → itProp Λ Σ).

  Fixpoint itProp_mu_rec (α : Ord.t) (ACC : Acc Ord.lt α) {struct ACC} : itProp Λ Σ :=
    F (itProp_exist (λ b : {β : Ord.t | Ord.lt β α},
                    itProp_mu_rec (proj1_sig b) (Acc_inv ACC (proj2_sig b)))).

  (** The approximant [μ_α]. *)
  Definition itProp_mu_approx (α : Ord.t) : itProp Λ Σ := itProp_mu_rec α (Ord.lt_well_founded α).
  Definition itProp_mu : itProp Λ Σ := itProp_exist itProp_mu_approx.

  Lemma itProp_mu_rec_irrel α A1 A2 : itProp_mu_rec α A1 = itProp_mu_rec α A2.
  Proof.
    revert A1 A2. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros [A1] [A2]. simpl. f_equal. f_equal. apply func_ext. intros [β Hβ]. by apply IH.
  Qed.

  Lemma itProp_mu_approx_unfold α :
    itProp_mu_approx α = F (itProp_exist (λ b : {β : Ord.t | Ord.lt β α}, itProp_mu_approx (proj1_sig b))).
  Proof.
    rewrite /itProp_mu_approx. generalize (Ord.lt_well_founded α) as ACC. intros [A]. simpl.
    f_equal. f_equal. apply func_ext. intros b. apply itProp_mu_rec_irrel.
  Qed.

  (** Introduction with a ranking: [H α] unfolds to [F] of smaller ranks. *)
  Lemma itProp_mu_rank `{!ItPropMono F} (H : Ord.t → itProp Λ Σ) :
    (∀ α, itProp_le (H α) (F (itProp_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    ∀ α, itProp_le (H α) (itProp_mu_approx α).
  Proof.
    intros HH α. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite itProp_mu_approx_unfold. eapply itProp_le_trans; first apply HH.
    apply itProp_mono_le, itProp_exist_mono. intros [β Hβ]. by apply IH.
  Qed.

  Lemma itProp_mu_intro `{!ItPropMono F} (H : Ord.t → itProp Λ Σ) α :
    (∀ α, itProp_le (H α) (F (itProp_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    itProp_le (H α) itProp_mu.
  Proof.
    intros HH. eapply itProp_le_trans; first by apply itProp_mu_rank. apply (itProp_exist_ub itProp_mu_approx).
  Qed.

  (** Induction: [itProp_mu F] is below every pre-fixpoint. *)
  Lemma itProp_mu_ind X `{!ItPropMono F} : itProp_le (F X) X → itProp_le itProp_mu X.
  Proof.
    intros HX. apply itProp_exist_lub. intros α.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite itProp_mu_approx_unfold. eapply itProp_le_trans; last apply HX.
    apply itProp_mono_le, itProp_exist_lub. intros [β Hβ]. by apply IH.
  Qed.

  Lemma itProp_mu_post `{!ItPropMono F} : itProp_le itProp_mu (F itProp_mu).
  Proof.
    apply itProp_exist_lub. intros α. rewrite itProp_mu_approx_unfold.
    apply itProp_mono_le, itProp_exist_lub. intros [β ?]. apply (itProp_exist_ub itProp_mu_approx).
  Qed.

  Lemma itProp_mu_approx_mono `{!ItPropMono F} α β :
    Ord.le α β → itProp_le (itProp_mu_approx α) (itProp_mu_approx β).
  Proof.
    intros Hle. rewrite !itProp_mu_approx_unfold. apply itProp_mono_le, itProp_exist_lub. intros [γ Hγ].
    apply (itProp_exist_ub (λ b : {γ | Ord.lt γ β}, itProp_mu_approx (proj1_sig b))
             (γ ↾ Ord.lt_le_lt Hγ Hle)).
  Qed.

  (** The fold, for a continuous body; with [itProp_mu_post], [itProp_mu F] is then a fixpoint.
      A guarded body has no fold ([itProp_mu_unfold_r_guarded]). *)
  Lemma itProp_mu_unfold_r `{!ItPropMono F, !ItPropCont F} : itProp_le (F itProp_mu) itProp_mu.
  Proof.
    eapply itProp_le_trans; first (apply (itProp_cont itProp_mu_approx); intros; by apply itProp_mu_approx_mono).
    apply itProp_exist_lub. intros α. eapply itProp_le_trans; last apply (itProp_exist_ub itProp_mu_approx (Ord.S α)).
    rewrite (itProp_mu_approx_unfold (Ord.S α)). apply itProp_mono_le.
    apply (itProp_exist_ub (λ b : {β | Ord.lt β (Ord.S α)}, itProp_mu_approx (proj1_sig b)) (α ↾ Ord.S_lt α)).
  Qed.

  Lemma itProp_mu_ext τ `{!ItPropMono F} : itProp_external itProp_mu τ → tr_lfp (λ R, itProp_external (F (itProp_trp R))) τ.
  Proof.
    assert (Hm : tr_mono (λ R, itProp_external (F (itProp_trp R)))).
    { intros R R' HR τ'. by apply itProp_mono_ext. }
    intros [α Hα]. revert τ Hα. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros τ Hα. rewrite itProp_mu_approx_unfold in Hα. apply tr_lfp_unfold_r; first done.
    eapply itProp_mono_ext; last exact Hα. intros τ' [[β Hβ] H']. by apply (IH β).
  Qed.

  (** The trace reading is a pre-fixpoint of the trace functor: the join of the ranks of its
      traces bounds them all. *)
  Lemma itProp_mu_ext_pre `{!ItPropMono F} τ :
    itProp_external (F (itProp_trp (itProp_external itProp_mu))) τ → itProp_external itProp_mu τ.
  Proof.
    intros Hτ.
    destruct (choice (λ (τ' : trace Λ) (α : Ord.t), itProp_external itProp_mu τ' → itProp_external (itProp_mu_approx α) τ'))
      as [f Hf].
    { intros τ'. destruct (classic (itProp_external itProp_mu τ')) as [[α Hα]|Hn]; [by exists α|by exists Ord.O]. }
    exists (Ord.S (Ord.join f)). rewrite itProp_mu_approx_unfold.
    eapply itProp_mono_ext; last exact Hτ. intros τ' Hτ'.
    exists (f τ' ↾ Ord.le_lt_lt (Ord.join_upperbound f τ') (Ord.S_lt _)). simpl. by apply Hf.
  Qed.

  Lemma itProp_mu_ext_lfp `{!ItPropMono F} τ : tr_lfp (λ R, itProp_external (F (itProp_trp R))) τ → itProp_external itProp_mu τ.
  Proof. intros H. apply H. intros τ'. apply itProp_mu_ext_pre. Qed.

  Lemma itProp_mu_ext_iff `{!ItPropMono F} τ : itProp_external itProp_mu τ ↔ tr_lfp (λ R, itProp_external (F (itProp_trp R))) τ.
  Proof. split; [by apply itProp_mu_ext|apply itProp_mu_ext_lfp]. Qed.

  (** On traces, [itProp_mu F] is a fixpoint of [F], for any monotone body. *)
  Lemma itProp_mu_ext_unfold_l `{!ItPropMono F} τ : itProp_external itProp_mu τ → itProp_external (F itProp_mu) τ.
  Proof.
    intros [α Hα]. rewrite itProp_mu_approx_unfold in Hα. eapply itProp_mono_ext; last exact Hα.
    intros τ' [b H]. by exists (proj1_sig b).
  Qed.
  Lemma itProp_mu_ext_unfold_r `{!ItPropMono F} τ : itProp_external (F itProp_mu) τ → itProp_external itProp_mu τ.
  Proof. intros H. apply itProp_mu_ext_pre. by eapply itProp_mono_ext; last exact H. Qed.

End mu.

(** ** Always and until as fixpoints *)
Section ltl.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : itProp Λ Σ.

  (** The step-indexed readings decide a position after the step taken there, so the
      bodies are [⊳ ⊚ (G ∧ ○'X)] and [⊳ ⊚ (G2 ∨ (G1 ∧ ○'X))]; on traces these read as
      [G ∧ ○X] and [G2 ∨ (G1 ∧ ○X)]. *)
  Definition F_always G : itProp Λ Σ → itProp Λ Σ := λ X, itProp_later (itProp_step (itProp_and G (itProp_shift X))).
  Definition F_until G1 G2 : itProp Λ Σ → itProp Λ Σ :=
    λ X, itProp_later (itProp_step (itProp_or G2 (itProp_and G1 (itProp_shift X)))).
  Global Instance F_always_mono G : ItPropMono (F_always G).
  Proof.
    apply (itProp_mono_later (λ X, itProp_step (itProp_and G (itProp_shift X)))),
      (itProp_mono_step (λ X, itProp_and G (itProp_shift X))), (itProp_mono_and (λ _, G) (λ X, itProp_shift X)).
    - apply itProp_mono_const.
    - apply (itProp_mono_shift (λ X, X)), itProp_mono_id.
  Qed.
  Global Instance F_until_mono G1 G2 : ItPropMono (F_until G1 G2).
  Proof.
    apply (itProp_mono_later (λ X, itProp_step (itProp_or G2 (itProp_and G1 (itProp_shift X))))),
      (itProp_mono_step (λ X, itProp_or G2 (itProp_and G1 (itProp_shift X)))),
      (itProp_mono_or (λ _, G2) (λ X, itProp_and G1 (itProp_shift X))); first apply itProp_mono_const.
    apply (itProp_mono_and (λ _, G1) (λ X, itProp_shift X)); first apply itProp_mono_const.
    apply (itProp_mono_shift (λ X, X)), itProp_mono_id.
  Qed.

  (** [□ G] is [ν X. ⊳ ⊚ (G ∧ ○'X)], in both directions. *)
  Lemma itProp_always_le_nu G : itProp_le (itProp_always G) (itProp_nu (F_always G)).
  Proof.
    apply itProp_nu_coind. intros ? τ. rewrite /F_always /= trI_always_unfold /trI_always_pre /trI_and /trI_pure.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". by iDestruct "H" as "[_ [_ $]]".
  Qed.

  Lemma itProp_nu_le_always G : itProp_le (itProp_nu (F_always G)) (itProp_always G).
  Proof.
    intros ? τ. rewrite {1}/itProp_internal /=. iIntros "[%X [%HX H]]".
    iRevert (τ) "H". iLöb as "IH". iIntros (τ) "H".
    iPoseProof (HX _ τ with "H") as "H". rewrite /F_always. iSimpl in "H".
    rewrite trI_always_unfold /trI_always_pre /trI_and /trI_pure.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". iSplit; first done.
    iDestruct "H" as "[_ H]". by iApply "IH".
  Qed.

  Lemma itProp_nu_always_ext G τ : itProp_external (itProp_nu (F_always G)) τ ↔ tr_always (itProp_external G) τ.
  Proof.
    rewrite itProp_nu_ext. destruct τ as [n τf]. split.
    - intros (R & HR & Hτ).
      assert (Hk : ∀ k, R (n + k, τf)).
      { intros k. induction k as [|k IHk]; first by rewrite Nat.add_0_r.
        destruct (HR _ IHk) as [_ Hnext]. by rewrite Nat.add_succ_r. }
      intros m Hm. replace m with (n + (m - n)) by lia. by destruct (HR _ (Hk (m - n))).
    - intros Hal. exists (tr_always (itProp_external G)). split; last done.
      intros [n' τf'] Hal'. split; first (apply Hal'; lia).
      intros m Hm. apply Hal'. simpl in Hm. lia.
  Qed.

  (** A ranked until. *)
  Program Definition itProp_until_at G1 G2 (a : Ord.t) : itProp Λ Σ :=
    {| itProp_internal _ := trI_until Ord.lt a (itProp_internal G1) (itProp_internal G2); itProp_external := itProp_external (itProp_until G1 G2) |}.
  Next Obligation.
    intros G1 G2 a ? F τ H. eapply (itProp_adeq (itProp_until G1 G2)). simpl. rewrite /trI_exist.
    eapply sat_mono; last exact H. iIntros "H". by iExists a.
  Qed.

  (** [G1 𝒰 G2] is below [μ X. ⊳(G2 ∨ (G1 ∧ ○X))]: its measure is a ranking. *)
  Lemma itProp_until_le_mu G1 G2 : itProp_le (itProp_until G1 G2) (itProp_mu (F_until G1 G2)).
  Proof.
    eapply itProp_le_trans; [|apply itProp_exist_lub; intros a; apply (itProp_mu_intro _ (itProp_until_at G1 G2))].
    - intros ? τ. rewrite /= /trI_exist. iIntros "[%a H]". by iExists a.
    - intros α ? τ. rewrite /F_until /= trI_until_unfold /trI_until_pre /trI_or /trI_and /trI_exist.
      iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
      iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
      iDestruct "H" as "[H|H]"; first by iLeft. iRight.
      iSplit; first by iDestruct "H" as "[$ _]".
      iDestruct "H" as "[_ (%a'& %Hlt& H)]". by iExists (a' ↾ Hlt).
  Qed.

  Lemma itProp_mu_until_ext G1 G2 τ :
    itProp_external (itProp_mu (F_until G1 G2)) τ → tr_until (itProp_external G1) (itProp_external G2) τ.
  Proof.
    intros H. apply itProp_mu_ext in H; last apply _. revert τ H. apply tr_lfp_ind.
    intros [n τf] [HQ|[HP (m & Hm & HQ & HPs)]].
    - exists n. split_and!; [lia|done|lia].
    - exists m. split_and!; [simpl in Hm; lia|done|].
      intros l Hl. destruct (decide (l = n)) as [->|Hne]; first done. apply HPs. simpl. lia.
  Qed.

  (** Conversely, [μ X. ⊳(G2 ∨ (G1 ∧ ○X))] is below [G1 𝒰 G2]: the approximant [μ_α] is
      the until ranked by [α]. *)
  Lemma itProp_mu_approx_le_until G1 G2 α :
    itProp_le (itProp_mu_approx (F_until G1 G2) α) (itProp_until_at G1 G2 α).
  Proof.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros ? τ. rewrite itProp_mu_approx_unfold /F_until /= trI_until_unfold /trI_until_pre /trI_or /trI_and /trI_exist.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iDestruct "H" as "[H|H]"; first by iLeft. iRight.
    iSplit; first by iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ [%b H]]". destruct b as [β Hβ]. iExists β. iSplit; first done.
    by iApply (IH β Hβ).
  Qed.

  Lemma itProp_mu_le_until G1 G2 : itProp_le (itProp_mu (F_until G1 G2)) (itProp_until G1 G2).
  Proof.
    apply itProp_exist_lub. intros α. eapply itProp_le_trans; first apply itProp_mu_approx_le_until.
    intros ? τ. rewrite /= /trI_exist. iIntros "H". by iExists α.
  Qed.

  Lemma itProp_mu_until_ext_iff G1 G2 τ :
    itProp_external (itProp_mu (F_until G1 G2)) τ ↔ tr_until (itProp_external G1) (itProp_external G2) τ.
  Proof.
    split; first apply itProp_mu_until_ext. intros Hu. apply itProp_mu_ext_lfp; first apply _.
    intros R HR. destruct τ as [n τf]. destruct Hu as (m & Hnm & HQ & HP).
    (* the until is below every pre-fixpoint, by the distance to the right formula *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → itProp_external G1 (l, τf)) → R (n', τf)) as Hd.
    { induction d as [|d IHd]; intros n' Hd Hn' HP'; apply HR; rewrite /F_until /=.
      - left. by assert (m = n') as <- by lia.
      - right. split; first (apply HP'; lia).
        apply IHd; [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. simpl in Hl. lia. }
    apply (Hd (m - n)); [done|done|]. intros l Hl. apply HP. lia.
  Qed.

  (** Beyond LTL: [G] at every even position, [ν X. ⊳ ⊚ (G ∧ ○' ○ X)] (not expressible in LTL). *)
  Definition F_even G : itProp Λ Σ → itProp Λ Σ :=
    λ X, itProp_later (itProp_step (itProp_and G (itProp_shift (itProp_next X)))).
  Global Instance F_even_mono G : ItPropMono (F_even G).
  Proof.
    apply (itProp_mono_later (λ X, itProp_step (itProp_and G (itProp_shift (itProp_next X))))),
      (itProp_mono_step (λ X, itProp_and G (itProp_shift (itProp_next X)))),
      (itProp_mono_and (λ _, G) (λ X, itProp_shift (itProp_next X))); first apply itProp_mono_const.
    apply (itProp_mono_shift (λ X, itProp_next X)), (itProp_mono_next (λ X, X)), itProp_mono_id.
  Qed.

  Lemma itProp_nu_even_ext G n τf :
    itProp_external (itProp_nu (F_even G)) (n, τf) ↔ ∀ k, itProp_external G (n + 2 * k, τf).
  Proof.
    rewrite itProp_nu_ext. split.
    - intros (R & HR & Hτ).
      assert (Hk : ∀ k, R (n + 2 * k, τf)).
      { intros k. induction k as [|k IHk]; first by rewrite Nat.add_0_r.
        destruct (HR _ IHk) as [_ Hnext]. simpl in Hnext.
        by replace (n + 2 * S k) with (S (S (n + 2 * k))) by lia. }
      intros k. by destruct (HR _ (Hk k)).
    - intros Hev. exists (λ τ, ∃ k, τ = (n + 2 * k, τf)). split; last (exists 0; f_equal; lia).
      intros τ' [k ->]. split; first apply Hev. exists (S k). rewrite /trace_next /=. f_equal. lia.
  Qed.

End ltl.

(** ** No fold for a guarded body

    A pre-fixpoint (for [⊑]) of the guarded body [X ↦ ⊳ ⊚ ○'X] is valid by Löb induction,
    hence true on every trace, while the least fixpoint of that body on traces is empty. So
    [F (μ F) ⊑ μ F] fails for it, and likewise for [G1 𝒰 G2]. *)
Section no_fold.
  Context {Λ : language} {Σ : gFunctors}.

  Lemma itProp_guarded_prefix_valid (M : itProp Λ Σ) :
    itProp_le (F_until itProp_true (itProp_pure False) M) M → ∀ (H : temporalGS Λ Σ) τ, ⊢ @itProp_internal _ _ M H τ.
  Proof.
    intros HM H. cut (⊢ ∀ τ, @itProp_internal _ _ M H τ)%I.
    { intros HM' τ. iApply HM'. }
    iLöb as "IH". iIntros (τ). iApply HM. rewrite /F_until /= /trI_or /trI_and /trI_pure.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iApply ALC_intro. iMod "Hclose" as "_".
    iModIntro. iRight. iSplit; first done. iApply "IH".
  Qed.

  (** The model: the instance is allocated as in the adequacy (adequacy_temporal.v). *)
  Lemma itProp_guarded_prefix_ext `{!mupdGpreS Σ}
      `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
      (M : itProp Λ Σ) τ :
    itProp_le (F_until itProp_true (itProp_pure False) M) M → itProp_external M τ.
  Proof.
    intros HM. destruct (τ.2 τ.1) as [[[Θ σ] i] κs].
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
    apply (itProp_adeq M (temporalGS0:=Htemp) emp).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono; last exact Hsat. iIntros "($& $& $)". iApply (itProp_guarded_prefix_valid M HM Htemp).
  Qed.

  Lemma itProp_mu_unfold_r_guarded `{!mupdGpreS Σ}
      `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
      (τ : trace Λ) :
    ¬ itProp_le (Λ:=Λ) (Σ:=Σ) (F_until itProp_true (itProp_pure False) (itProp_mu (F_until itProp_true (itProp_pure False))))
             (itProp_mu (F_until itProp_true (itProp_pure False))).
  Proof.
    intros Hfold. apply (itProp_guarded_prefix_ext _ τ), itProp_mu_until_ext in Hfold.
    destruct τ as [n τf]. by destruct Hfold as (m & _ & [] & _).
  Qed.

End no_fold.
