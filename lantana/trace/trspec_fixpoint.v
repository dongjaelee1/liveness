From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trspec_rules.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.
From lantana.prelude Require Import axioms.

(** * Least and greatest fixpoints of trace specifications

    For a body [F] monotone in both readings ([TrSpecMono]): [trSpec_nu F], the union of the
    post-fixpoints of [F], and [trSpec_mu F], the union of ordinal approximants
    [μ_α := F (∃ β < α, μ_β)]. Always and until are such fixpoints. *)

(* The proof mode must not unfold the connectives, which are records. *)
#[local] Typeclasses Opaque trSpec_pure trSpec_and trSpec_or trSpec_impl trSpec_forall trSpec_exist
  trSpec_always trSpec_until trSpec_state.

(** ** Trace predicates, the in-logic step, and the next position *)
Section connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : trSpec Λ Σ.

  (** Any trace predicate, read in the logic as a pure fact. *)
  Program Definition trSpec_trp (R : trProp Λ) : trSpec Λ Σ :=
    {| trSpec_internal _ τ := ⌜R τ⌝%I; trSpec_external := R |}.
  Next Obligation. intros R ? F τ H. by apply sat_elim in H. Qed.

  (** [⊳ G]: [G] after one step of the logic; at the level of traces, just [G]. *)
  Program Definition trSpec_later G : trSpec Λ Σ :=
    {| trSpec_internal _ τ := (|={⊤,∅}=> ▷ |={∅,⊤}=> trSpec_internal G τ)%I; trSpec_external := trSpec_external G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_later, sat_fupd in H. by eapply trSpec_adeq. Qed.

  (** [○ G]: [G] at the next position. *)
  Program Definition trSpec_next G : trSpec Λ Σ :=
    {| trSpec_internal _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> trSpec_internal G (trace_next τ)))%I;
       trSpec_external τ := trSpec_external G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply trSpec_adeq. Qed.

  (** [⊚ G]: [G] after the step taken at the current position. In the logic this is the
      step's credits and mask change; at the level of traces it is just [G]. *)
  Program Definition trSpec_step G : trSpec Λ Σ :=
    {| trSpec_internal _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> trSpec_internal G τ))%I; trSpec_external := trSpec_external G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply trSpec_adeq. Qed.

  (** [○' G]: [G] read at the next position, with no modality; [○ G] is [⊚ ○' G]. *)
  Program Definition trSpec_shift G : trSpec Λ Σ :=
    {| trSpec_internal _ τ := trSpec_internal G (trace_next τ); trSpec_external τ := trSpec_external G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. by eapply trSpec_adeq. Qed.

  Lemma trSpec_later_mono G G' : trSpec_le G G' → trSpec_le (trSpec_later G) (trSpec_later G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    by iApply HG.
  Qed.
  Lemma trSpec_next_mono G G' : trSpec_le G G' → trSpec_le (trSpec_next G) (trSpec_next G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma trSpec_step_mono G G' : trSpec_le G G' → trSpec_le (trSpec_step G) (trSpec_step G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma trSpec_shift_mono G G' : trSpec_le G G' → trSpec_le (trSpec_shift G) (trSpec_shift G').
  Proof. intros HG ? τ. rewrite /=. by iApply HG. Qed.

  Lemma trSpec_exist_lub {X} `{!TypeExistentialProperty X ordI} (G : X → trSpec Λ Σ) G' :
    (∀ x, trSpec_le (G x) G') → trSpec_le (trSpec_exist G) G'.
  Proof. intros HG ? τ. rewrite /= /trI_exist. iIntros "[%x H]". by iApply HG. Qed.
  Lemma trSpec_exist_ub {X} `{!TypeExistentialProperty X ordI} (G : X → trSpec Λ Σ) x :
    trSpec_le (G x) (trSpec_exist G).
  Proof. intros ? τ. rewrite /= /trI_exist. iIntros "H". by iExists x. Qed.

End connectives.

Global Typeclasses Opaque trSpec_trp trSpec_later trSpec_next.

(** ** Monotone bodies *)
Class TrSpecMono {Λ Σ} (F : trSpec Λ Σ → trSpec Λ Σ) : Prop := {
  trSpec_mono_le X Y : trSpec_le X Y → trSpec_le (F X) (F Y);
  trSpec_mono_ext X Y : (∀ τ, trSpec_external X τ → trSpec_external Y τ) → ∀ τ, trSpec_external (F X) τ → trSpec_external (F Y) τ;
}.
Global Hint Mode TrSpecMono - - ! : typeclass_instances.

Section mono_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : trSpec Λ Σ → trSpec Λ Σ.

  Global Instance trSpec_mono_id : TrSpecMono (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. split; auto. Qed.
  Global Instance trSpec_mono_const G : TrSpecMono (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. split; auto using trSpec_le_refl. Qed.
  Global Instance trSpec_mono_and F1 F2 :
    TrSpecMono F1 → TrSpecMono F2 → TrSpecMono (λ X, trSpec_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply trSpec_and_mono; by apply trSpec_mono_le.
    - intros X Y HXY τ [??]. split; [by apply (trSpec_mono_ext (F:=F1) X Y)|by apply (trSpec_mono_ext (F:=F2) X Y)].
  Qed.
  Global Instance trSpec_mono_or F1 F2 :
    TrSpecMono F1 → TrSpecMono F2 → TrSpecMono (λ X, trSpec_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply trSpec_or_mono; by apply trSpec_mono_le.
    - intros X Y HXY τ [?|?]; [left; by apply (trSpec_mono_ext (F:=F1) X Y)|right; by apply (trSpec_mono_ext (F:=F2) X Y)].
  Qed.
  Global Instance trSpec_mono_impl A F : TrSpecMono F → TrSpecMono (λ X, trSpec_impl A (F X)).
  Proof.
    intros HF. split.
    - intros. apply trSpec_impl_mono; [done|by apply trSpec_mono_le].
    - intros X Y HXY τ H HA. apply (trSpec_mono_ext (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance trSpec_mono_forall {A} (F : A → trSpec Λ Σ → trSpec Λ Σ) :
    (∀ a, TrSpecMono (F a)) → TrSpecMono (λ X, trSpec_forall (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply trSpec_forall_mono. intros a. by apply trSpec_mono_le.
    - intros X Y HXY τ H a. apply (trSpec_mono_ext (F:=F a) X Y); [done|apply H].
  Qed.
  Global Instance trSpec_mono_exist {A} `{!TypeExistentialProperty A ordI} (F : A → trSpec Λ Σ → trSpec Λ Σ) :
    (∀ a, TrSpecMono (F a)) → TrSpecMono (λ X, trSpec_exist (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply trSpec_exist_mono. intros a. by apply trSpec_mono_le.
    - intros X Y HXY τ [a H]. exists a. by apply (trSpec_mono_ext (F:=F a) X Y).
  Qed.
  Global Instance trSpec_mono_later F : TrSpecMono F → TrSpecMono (λ X, trSpec_later (F X)).
  Proof.
    intros HF. split.
    - intros. apply trSpec_later_mono. by apply trSpec_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (trSpec_mono_ext (F:=F) X Y).
  Qed.
  Global Instance trSpec_mono_next F : TrSpecMono F → TrSpecMono (λ X, trSpec_next (F X)).
  Proof.
    intros HF. split.
    - intros. apply trSpec_next_mono. by apply trSpec_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (trSpec_mono_ext (F:=F) X Y).
  Qed.
  Global Instance trSpec_mono_step F : TrSpecMono F → TrSpecMono (λ X, trSpec_step (F X)).
  Proof.
    intros HF. split.
    - intros. apply trSpec_step_mono. by apply trSpec_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (trSpec_mono_ext (F:=F) X Y).
  Qed.
  Global Instance trSpec_mono_shift F : TrSpecMono F → TrSpecMono (λ X, trSpec_shift (F X)).
  Proof.
    intros HF. split.
    - intros. apply trSpec_shift_mono. by apply trSpec_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (trSpec_mono_ext (F:=F) X Y).
  Qed.
  Global Instance trSpec_mono_always F : TrSpecMono F → TrSpecMono (λ X, trSpec_always (F X)).
  Proof.
    intros HF. split.
    - intros. apply trSpec_always_mono. by apply trSpec_mono_le.
    - intros X Y HXY [n τf] H m Hm. apply (trSpec_mono_ext (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance trSpec_mono_until F1 F2 :
    TrSpecMono F1 → TrSpecMono F2 → TrSpecMono (λ X, trSpec_until (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply trSpec_until_mono; by apply trSpec_mono_le.
    - intros X Y HXY [n τf] (m & Hm & HQ & HP). exists m. split_and!; [done| |].
      + by apply (trSpec_mono_ext (F:=F2) X Y).
      + intros l Hl. apply (trSpec_mono_ext (F:=F1) X Y); [done|by apply HP].
  Qed.

End mono_instances.

(** ** Continuous bodies

    [F] commutes, in the logic, with unions of increasing chains indexed by ordinals. Guarded
    bodies are not continuous: the step index ranges beyond [Ord.t], so [▷ ∃ α, X α] does
    not give [∃ α, ▷ X α]. *)
Class TrSpecCont {Λ Σ} (F : trSpec Λ Σ → trSpec Λ Σ) : Prop :=
  trSpec_cont (X : Ord.t → trSpec Λ Σ) :
    (∀ α β, Ord.le α β → trSpec_le (X α) (X β)) →
    trSpec_le (F (trSpec_exist X)) (trSpec_exist (λ α, F (X α))).
Global Hint Mode TrSpecCont - - ! : typeclass_instances.

Section cont_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : trSpec Λ Σ → trSpec Λ Σ.

  Global Instance trSpec_cont_id : TrSpecCont (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. intros X _. apply trSpec_le_refl. Qed.
  Global Instance trSpec_cont_const G : TrSpecCont (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. intros X _ ? τ. rewrite /= /trI_exist. iIntros "H". by iExists Ord.O. Qed.
  Global Instance trSpec_cont_and F1 F2 `{!TrSpecMono F1, !TrSpecMono F2} :
    TrSpecCont F1 → TrSpecCont F2 → TrSpecCont (λ X, trSpec_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2 X HX ? τ. rewrite /= /trI_and (H1 X HX _ τ) (H2 X HX _ τ) /= /trI_exist.
    rewrite bi.and_exist_r. iIntros "[%α H]". rewrite bi.and_exist_l. iDestruct "H" as (β) "H".
    iExists (Ord.union α β). iSplit.
    - iDestruct "H" as "[H _]". iApply (trSpec_mono_le (X α)); [apply HX, Ord.union_l|done].
    - iDestruct "H" as "[_ H]". iApply (trSpec_mono_le (X β)); [apply HX, Ord.union_r|done].
  Qed.
  Global Instance trSpec_cont_or F1 F2 :
    TrSpecCont F1 → TrSpecCont F2 → TrSpecCont (λ X, trSpec_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2 X HX ? τ. rewrite /= /trI_or (H1 X HX _ τ) (H2 X HX _ τ) /= /trI_exist.
    iIntros "[[%α H]|[%α H]]"; iExists α; [by iLeft|by iRight].
  Qed.
  Global Instance trSpec_cont_impl A F : TrSpecCont F → TrSpecCont (λ X, trSpec_impl A (F X)).
  Proof.
    intros HF X HX ? τ. rewrite /= /trI_impl (HF X HX _ τ) /= /trI_exist. iIntros "H".
    destruct (classic (trSpec_external A τ)) as [HA|HA].
    - iDestruct ("H" $! HA) as (α) "H". iExists α. by iIntros "_".
    - iExists Ord.O. by iIntros (?).
  Qed.
  Global Instance trSpec_cont_exist {A} `{!TypeExistentialProperty A ordI} (F : A → trSpec Λ Σ → trSpec Λ Σ) :
    (∀ a, TrSpecCont (F a)) → TrSpecCont (λ X, trSpec_exist (λ a, F a X)).
  Proof.
    intros HF X HX ? τ. rewrite /= /trI_exist. iIntros "[%a H]".
    rewrite (HF a X HX _ τ) /= /trI_exist. iDestruct "H" as (α) "H". iExists α, a. done.
  Qed.
  Global Instance trSpec_cont_shift F : TrSpecCont F → TrSpecCont (λ X, trSpec_shift (F X)).
  Proof. intros HF X HX ? τ. rewrite /= (HF X HX _ (trace_next τ)) /= /trI_exist. done. Qed.

End cont_instances.

(** ** Greatest fixpoints *)
Section nu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : trSpec Λ Σ.

  Program Definition trSpec_nu (F : trSpec Λ Σ → trSpec Λ Σ) `{!TrSpecMono F} : trSpec Λ Σ :=
    {| trSpec_internal H τ := (∃ X : trSpec Λ Σ, ⌜trSpec_le X (F X)⌝ ∧ @trSpec_internal _ _ X H τ)%I;
       trSpec_external := tr_gfp (λ R, trSpec_external (F (trSpec_trp R))) |}.
  Next Obligation.
    intros F HF H F0 τ Hsat.
    pose (I := λ (H' : temporalGS Λ Σ) (τ' : trace Λ),
                 (∃ X : trSpec Λ Σ, ⌜trSpec_le X (F X)⌝ ∧ @trSpec_internal _ _ X H' τ')%I).
    (* The traces at which the in-logic reading is satisfiable, for some instance. *)
    pose (S := λ τ', ∃ (H' : temporalGS Λ Σ) (F' : iProp Σ), iProp_sat_lc_at_frame F' ⊤ (I H' τ')).
    assert (HS : ∀ (H' : temporalGS Λ Σ) (F' : iProp Σ) τ',
               iProp_sat_lc_at_frame F' ⊤ (I H' τ') → S τ').
    { intros H' F' τ' Hs. by exists H', F'. }
    pose (N := TrSpec I S HS).
    (* [S] is a post-fixpoint of the trace functor. *)
    exists S. split; last by exists H, F0.
    intros τ' (H' & F' & Hs).
    assert (HXN : ∀ X, trSpec_le X (F X) → trSpec_le X N).
    { intros X HX ? τ''. rewrite /=. iIntros "HX". iExists X. by iFrame. }
    assert (HIN : I H' τ' ⊢ @trSpec_internal _ _ (F N) H' τ').
    { iIntros "[%X [%HX HXt]]". iApply (trSpec_mono_le X N (HXN X HX)). by iApply HX. }
    apply (sat_mono _ _ HIN) in Hs. apply (trSpec_adeq (F N)) in Hs.
    eapply (trSpec_mono_ext N (trSpec_trp S)); last exact Hs. done.
  Qed.

  Context (F : trSpec Λ Σ → trSpec Λ Σ) `{!TrSpecMono F}.

  Lemma trSpec_nu_coind X : trSpec_le X (F X) → trSpec_le X (trSpec_nu F).
  Proof. intros HX ? τ. rewrite /=. iIntros "H". iExists X. by iFrame. Qed.

  Lemma trSpec_nu_unfold_l : trSpec_le (trSpec_nu F) (F (trSpec_nu F)).
  Proof.
    intros ? τ. rewrite {1}/trSpec_internal /=. iIntros "[%X [%HX H]]".
    iApply (trSpec_mono_le X (trSpec_nu F)); first by apply trSpec_nu_coind. by iApply HX.
  Qed.

  Lemma trSpec_nu_unfold_r : trSpec_le (F (trSpec_nu F)) (trSpec_nu F).
  Proof. apply trSpec_nu_coind, trSpec_mono_le, trSpec_nu_unfold_l. Qed.

  Lemma trSpec_nu_ext τ : trSpec_external (trSpec_nu F) τ ↔ tr_gfp (λ R, trSpec_external (F (trSpec_trp R))) τ.
  Proof. done. Qed.

End nu.

(** ** Least fixpoints, with ordinal approximants

    The ordinal is the measure a least fixpoint needs in a step-indexed logic: without it, a
    guarded body has a unique fixpoint, and [μ] would be [ν]. *)
Section mu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : trSpec Λ Σ.
  Context (F : trSpec Λ Σ → trSpec Λ Σ).

  Fixpoint trSpec_mu_rec (α : Ord.t) (ACC : Acc Ord.lt α) {struct ACC} : trSpec Λ Σ :=
    F (trSpec_exist (λ b : {β : Ord.t | Ord.lt β α},
                    trSpec_mu_rec (proj1_sig b) (Acc_inv ACC (proj2_sig b)))).

  (** The approximant [μ_α]. *)
  Definition trSpec_mu_approx (α : Ord.t) : trSpec Λ Σ := trSpec_mu_rec α (Ord.lt_well_founded α).
  Definition trSpec_mu : trSpec Λ Σ := trSpec_exist trSpec_mu_approx.

  Lemma trSpec_mu_rec_irrel α A1 A2 : trSpec_mu_rec α A1 = trSpec_mu_rec α A2.
  Proof.
    revert A1 A2. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros [A1] [A2]. simpl. f_equal. f_equal. apply func_ext. intros [β Hβ]. by apply IH.
  Qed.

  Lemma trSpec_mu_approx_unfold α :
    trSpec_mu_approx α = F (trSpec_exist (λ b : {β : Ord.t | Ord.lt β α}, trSpec_mu_approx (proj1_sig b))).
  Proof.
    rewrite /trSpec_mu_approx. generalize (Ord.lt_well_founded α) as ACC. intros [A]. simpl.
    f_equal. f_equal. apply func_ext. intros b. apply trSpec_mu_rec_irrel.
  Qed.

  (** Introduction with a ranking: [H α] unfolds to [F] of smaller ranks. *)
  Lemma trSpec_mu_rank `{!TrSpecMono F} (H : Ord.t → trSpec Λ Σ) :
    (∀ α, trSpec_le (H α) (F (trSpec_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    ∀ α, trSpec_le (H α) (trSpec_mu_approx α).
  Proof.
    intros HH α. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite trSpec_mu_approx_unfold. eapply trSpec_le_trans; first apply HH.
    apply trSpec_mono_le, trSpec_exist_mono. intros [β Hβ]. by apply IH.
  Qed.

  Lemma trSpec_mu_intro `{!TrSpecMono F} (H : Ord.t → trSpec Λ Σ) α :
    (∀ α, trSpec_le (H α) (F (trSpec_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    trSpec_le (H α) trSpec_mu.
  Proof.
    intros HH. eapply trSpec_le_trans; first by apply trSpec_mu_rank. apply (trSpec_exist_ub trSpec_mu_approx).
  Qed.

  (** Induction: [trSpec_mu F] is below every pre-fixpoint. *)
  Lemma trSpec_mu_ind X `{!TrSpecMono F} : trSpec_le (F X) X → trSpec_le trSpec_mu X.
  Proof.
    intros HX. apply trSpec_exist_lub. intros α.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite trSpec_mu_approx_unfold. eapply trSpec_le_trans; last apply HX.
    apply trSpec_mono_le, trSpec_exist_lub. intros [β Hβ]. by apply IH.
  Qed.

  Lemma trSpec_mu_post `{!TrSpecMono F} : trSpec_le trSpec_mu (F trSpec_mu).
  Proof.
    apply trSpec_exist_lub. intros α. rewrite trSpec_mu_approx_unfold.
    apply trSpec_mono_le, trSpec_exist_lub. intros [β ?]. apply (trSpec_exist_ub trSpec_mu_approx).
  Qed.

  Lemma trSpec_mu_approx_mono `{!TrSpecMono F} α β :
    Ord.le α β → trSpec_le (trSpec_mu_approx α) (trSpec_mu_approx β).
  Proof.
    intros Hle. rewrite !trSpec_mu_approx_unfold. apply trSpec_mono_le, trSpec_exist_lub. intros [γ Hγ].
    apply (trSpec_exist_ub (λ b : {γ | Ord.lt γ β}, trSpec_mu_approx (proj1_sig b))
             (γ ↾ Ord.lt_le_lt Hγ Hle)).
  Qed.

  (** The fold, for a continuous body; with [trSpec_mu_post], [trSpec_mu F] is then a fixpoint.
      A guarded body has no fold ([trSpec_mu_unfold_r_guarded]). *)
  Lemma trSpec_mu_unfold_r `{!TrSpecMono F, !TrSpecCont F} : trSpec_le (F trSpec_mu) trSpec_mu.
  Proof.
    eapply trSpec_le_trans; first (apply (trSpec_cont trSpec_mu_approx); intros; by apply trSpec_mu_approx_mono).
    apply trSpec_exist_lub. intros α. eapply trSpec_le_trans; last apply (trSpec_exist_ub trSpec_mu_approx (Ord.S α)).
    rewrite (trSpec_mu_approx_unfold (Ord.S α)). apply trSpec_mono_le.
    apply (trSpec_exist_ub (λ b : {β | Ord.lt β (Ord.S α)}, trSpec_mu_approx (proj1_sig b)) (α ↾ Ord.S_lt α)).
  Qed.

  Lemma trSpec_mu_ext τ `{!TrSpecMono F} : trSpec_external trSpec_mu τ → tr_lfp (λ R, trSpec_external (F (trSpec_trp R))) τ.
  Proof.
    assert (Hm : tr_mono (λ R, trSpec_external (F (trSpec_trp R)))).
    { intros R R' HR τ'. by apply trSpec_mono_ext. }
    intros [α Hα]. revert τ Hα. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros τ Hα. rewrite trSpec_mu_approx_unfold in Hα. apply tr_lfp_unfold_r; first done.
    eapply trSpec_mono_ext; last exact Hα. intros τ' [[β Hβ] H']. by apply (IH β).
  Qed.

  (** The trace reading is a pre-fixpoint of the trace functor: the join of the ranks of its
      traces bounds them all. *)
  Lemma trSpec_mu_ext_pre `{!TrSpecMono F} τ :
    trSpec_external (F (trSpec_trp (trSpec_external trSpec_mu))) τ → trSpec_external trSpec_mu τ.
  Proof.
    intros Hτ.
    destruct (choice (λ (τ' : trace Λ) (α : Ord.t), trSpec_external trSpec_mu τ' → trSpec_external (trSpec_mu_approx α) τ'))
      as [f Hf].
    { intros τ'. destruct (classic (trSpec_external trSpec_mu τ')) as [[α Hα]|Hn]; [by exists α|by exists Ord.O]. }
    exists (Ord.S (Ord.join f)). rewrite trSpec_mu_approx_unfold.
    eapply trSpec_mono_ext; last exact Hτ. intros τ' Hτ'.
    exists (f τ' ↾ Ord.le_lt_lt (Ord.join_upperbound f τ') (Ord.S_lt _)). simpl. by apply Hf.
  Qed.

  Lemma trSpec_mu_ext_lfp `{!TrSpecMono F} τ : tr_lfp (λ R, trSpec_external (F (trSpec_trp R))) τ → trSpec_external trSpec_mu τ.
  Proof. intros H. apply H. intros τ'. apply trSpec_mu_ext_pre. Qed.

  Lemma trSpec_mu_ext_iff `{!TrSpecMono F} τ : trSpec_external trSpec_mu τ ↔ tr_lfp (λ R, trSpec_external (F (trSpec_trp R))) τ.
  Proof. split; [by apply trSpec_mu_ext|apply trSpec_mu_ext_lfp]. Qed.

  (** On traces, [trSpec_mu F] is a fixpoint of [F], for any monotone body. *)
  Lemma trSpec_mu_ext_unfold_l `{!TrSpecMono F} τ : trSpec_external trSpec_mu τ → trSpec_external (F trSpec_mu) τ.
  Proof.
    intros [α Hα]. rewrite trSpec_mu_approx_unfold in Hα. eapply trSpec_mono_ext; last exact Hα.
    intros τ' [b H]. by exists (proj1_sig b).
  Qed.
  Lemma trSpec_mu_ext_unfold_r `{!TrSpecMono F} τ : trSpec_external (F trSpec_mu) τ → trSpec_external trSpec_mu τ.
  Proof. intros H. apply trSpec_mu_ext_pre. by eapply trSpec_mono_ext; last exact H. Qed.

End mu.

(** ** Always and until as fixpoints *)
Section ltl.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : trSpec Λ Σ.

  (** The step-indexed readings decide a position after the step taken there, so the
      bodies are [⊳ ⊚ (G ∧ ○'X)] and [⊳ ⊚ (G2 ∨ (G1 ∧ ○'X))]; on traces these read as
      [G ∧ ○X] and [G2 ∨ (G1 ∧ ○X)]. *)
  Definition F_always G : trSpec Λ Σ → trSpec Λ Σ := λ X, trSpec_later (trSpec_step (trSpec_and G (trSpec_shift X))).
  Definition F_until G1 G2 : trSpec Λ Σ → trSpec Λ Σ :=
    λ X, trSpec_later (trSpec_step (trSpec_or G2 (trSpec_and G1 (trSpec_shift X)))).
  Global Instance F_always_mono G : TrSpecMono (F_always G).
  Proof.
    apply (trSpec_mono_later (λ X, trSpec_step (trSpec_and G (trSpec_shift X)))),
      (trSpec_mono_step (λ X, trSpec_and G (trSpec_shift X))), (trSpec_mono_and (λ _, G) (λ X, trSpec_shift X)).
    - apply trSpec_mono_const.
    - apply (trSpec_mono_shift (λ X, X)), trSpec_mono_id.
  Qed.
  Global Instance F_until_mono G1 G2 : TrSpecMono (F_until G1 G2).
  Proof.
    apply (trSpec_mono_later (λ X, trSpec_step (trSpec_or G2 (trSpec_and G1 (trSpec_shift X))))),
      (trSpec_mono_step (λ X, trSpec_or G2 (trSpec_and G1 (trSpec_shift X)))),
      (trSpec_mono_or (λ _, G2) (λ X, trSpec_and G1 (trSpec_shift X))); first apply trSpec_mono_const.
    apply (trSpec_mono_and (λ _, G1) (λ X, trSpec_shift X)); first apply trSpec_mono_const.
    apply (trSpec_mono_shift (λ X, X)), trSpec_mono_id.
  Qed.

  (** [□ G] is [ν X. ⊳ ⊚ (G ∧ ○'X)], in both directions. *)
  Lemma trSpec_always_le_nu G : trSpec_le (trSpec_always G) (trSpec_nu (F_always G)).
  Proof.
    apply trSpec_nu_coind. intros ? τ. rewrite /F_always /= trI_always_unfold /trI_always_pre /trI_and /trI_pure.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". by iDestruct "H" as "[_ [_ $]]".
  Qed.

  Lemma trSpec_nu_le_always G : trSpec_le (trSpec_nu (F_always G)) (trSpec_always G).
  Proof.
    intros ? τ. rewrite {1}/trSpec_internal /=. iIntros "[%X [%HX H]]".
    iRevert (τ) "H". iLöb as "IH". iIntros (τ) "H".
    iPoseProof (HX _ τ with "H") as "H". rewrite /F_always. iSimpl in "H".
    rewrite trI_always_unfold /trI_always_pre /trI_and /trI_pure.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". iSplit; first done.
    iDestruct "H" as "[_ H]". by iApply "IH".
  Qed.

  (** On traces, [ν X. G ∧ ○X] is [□ G]. *)
  Lemma trSpec_nu_always_ext G : trSpec_external (trSpec_nu (F_always G)) ⊆ (□ trSpec_external G)%R.
  Proof.
    intros [n τf]. rewrite trSpec_nu_ext. intros (R & HR & Hτ).
    assert (Hk : ∀ k, R (n + k, τf)).
    { intros k. induction k as [|k IHk]; first by rewrite Nat.add_0_r.
      destruct (HR _ IHk) as [_ Hnext]. by rewrite Nat.add_succ_r. }
    intros m Hm. replace m with (n + (m - n)) by lia. by destruct (HR _ (Hk (m - n))).
  Qed.
  Lemma trSpec_nu_always_ext' G : (□ trSpec_external G)%R ⊆ trSpec_external (trSpec_nu (F_always G)).
  Proof.
    intros [n τf] Hal. rewrite trSpec_nu_ext. exists (tr_always (trSpec_external G)). split; last done.
    intros [n' τf'] Hal'. split; first (apply Hal'; lia).
    intros m Hm. apply Hal'. simpl in Hm. lia.
  Qed.

  (** A ranked until. *)
  Program Definition trSpec_until_at G1 G2 (a : Ord.t) : trSpec Λ Σ :=
    {| trSpec_internal _ := trI_until Ord.lt a (trSpec_internal G1) (trSpec_internal G2); trSpec_external := trSpec_external (trSpec_until G1 G2) |}.
  Next Obligation.
    intros G1 G2 a ? F τ H. eapply (trSpec_adeq (trSpec_until G1 G2)). simpl. rewrite /trI_exist.
    eapply sat_mono; last exact H. iIntros "H". by iExists a.
  Qed.

  (** [G1 𝒰 G2] is below [μ X. ⊳(G2 ∨ (G1 ∧ ○X))]: its measure is a ranking. *)
  Lemma trSpec_until_le_mu G1 G2 : trSpec_le (trSpec_until G1 G2) (trSpec_mu (F_until G1 G2)).
  Proof.
    eapply trSpec_le_trans; [|apply trSpec_exist_lub; intros a; apply (trSpec_mu_intro _ (trSpec_until_at G1 G2))].
    - intros ? τ. rewrite /= /trI_exist. iIntros "[%a H]". by iExists a.
    - intros α ? τ. rewrite /F_until /= trI_until_unfold /trI_until_pre /trI_or /trI_and /trI_exist.
      iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
      iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
      iDestruct "H" as "[H|H]"; first by iLeft. iRight.
      iSplit; first by iDestruct "H" as "[$ _]".
      iDestruct "H" as "[_ (%a'& %Hlt& H)]". by iExists (a' ↾ Hlt).
  Qed.

  Lemma trSpec_mu_until_ext G1 G2 τ :
    trSpec_external (trSpec_mu (F_until G1 G2)) τ → tr_until (trSpec_external G1) (trSpec_external G2) τ.
  Proof.
    intros H. apply trSpec_mu_ext in H; last apply _. revert τ H. apply tr_lfp_ind.
    intros [n τf] [HQ|[HP (m & Hm & HQ & HPs)]].
    - exists n. split_and!; [lia|done|lia].
    - exists m. split_and!; [simpl in Hm; lia|done|].
      intros l Hl. destruct (decide (l = n)) as [->|Hne]; first done. apply HPs. simpl. lia.
  Qed.

  (** Conversely, [μ X. ⊳(G2 ∨ (G1 ∧ ○X))] is below [G1 𝒰 G2]: the approximant [μ_α] is
      the until ranked by [α]. *)
  Lemma trSpec_mu_approx_le_until G1 G2 α :
    trSpec_le (trSpec_mu_approx (F_until G1 G2) α) (trSpec_until_at G1 G2 α).
  Proof.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros ? τ. rewrite trSpec_mu_approx_unfold /F_until /= trI_until_unfold /trI_until_pre /trI_or /trI_and /trI_exist.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iDestruct "H" as "[H|H]"; first by iLeft. iRight.
    iSplit; first by iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ [%b H]]". destruct b as [β Hβ]. iExists β. iSplit; first done.
    by iApply (IH β Hβ).
  Qed.

  Lemma trSpec_mu_le_until G1 G2 : trSpec_le (trSpec_mu (F_until G1 G2)) (trSpec_until G1 G2).
  Proof.
    apply trSpec_exist_lub. intros α. eapply trSpec_le_trans; first apply trSpec_mu_approx_le_until.
    intros ? τ. rewrite /= /trI_exist. iIntros "H". by iExists α.
  Qed.

  Lemma trSpec_mu_until_ext_iff G1 G2 τ :
    trSpec_external (trSpec_mu (F_until G1 G2)) τ ↔ tr_until (trSpec_external G1) (trSpec_external G2) τ.
  Proof.
    split; first apply trSpec_mu_until_ext. intros Hu. apply trSpec_mu_ext_lfp; first apply _.
    intros R HR. destruct τ as [n τf]. destruct Hu as (m & Hnm & HQ & HP).
    (* the until is below every pre-fixpoint, by the distance to the right formula *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → trSpec_external G1 (l, τf)) → R (n', τf)) as Hd.
    { induction d as [|d IHd]; intros n' Hd Hn' HP'; apply HR; rewrite /F_until /=.
      - left. by assert (m = n') as <- by lia.
      - right. split; first (apply HP'; lia).
        apply IHd; [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. simpl in Hl. lia. }
    apply (Hd (m - n)); [done|done|]. intros l Hl. apply HP. lia.
  Qed.

  (** Beyond LTL: [G] at every even position, [ν X. ⊳ ⊚ (G ∧ ○' ○ X)] (not expressible in LTL). *)
  Definition F_even G : trSpec Λ Σ → trSpec Λ Σ :=
    λ X, trSpec_later (trSpec_step (trSpec_and G (trSpec_shift (trSpec_next X)))).
  Global Instance F_even_mono G : TrSpecMono (F_even G).
  Proof.
    apply (trSpec_mono_later (λ X, trSpec_step (trSpec_and G (trSpec_shift (trSpec_next X))))),
      (trSpec_mono_step (λ X, trSpec_and G (trSpec_shift (trSpec_next X)))),
      (trSpec_mono_and (λ _, G) (λ X, trSpec_shift (trSpec_next X))); first apply trSpec_mono_const.
    apply (trSpec_mono_shift (λ X, trSpec_next X)), (trSpec_mono_next (λ X, X)), trSpec_mono_id.
  Qed.

  Lemma trSpec_nu_even_ext G n τf :
    trSpec_external (trSpec_nu (F_even G)) (n, τf) ↔ ∀ k, trSpec_external G (n + 2 * k, τf).
  Proof.
    rewrite trSpec_nu_ext. split.
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
