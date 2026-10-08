From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export itrprop_rules.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.
From lantana.prelude Require Import axioms.

(** * Least and greatest fixpoints of internalized trace properties

    For a body [F] monotone in both readings ([ItrPropMono]): [itrProp_nu F], the union of the
    post-fixpoints of [F], and [itrProp_mu F], the union of ordinal approximants
    [μ_α := F (∃ β < α, μ_β)]. Always and until are such fixpoints. *)

(* The proof mode must not unfold the connectives, which are records. *)
#[local] Typeclasses Opaque itrProp_pure itrProp_and itrProp_or itrProp_impl itrProp_forall itrProp_exist
  itrProp_always itrProp_until itrProp_state.

(** ** Trace predicates, the in-logic step, and the next position *)
Section connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : itrProp Λ Σ.

  (** Any trace predicate, read in the logic as a pure fact. *)
  Program Definition itrProp_trp (R : trProp Λ) : itrProp Λ Σ :=
    {| itrProp_internal _ τ := ⌜R τ⌝%I; itrProp_external := R |}.
  Next Obligation. intros R ? F τ H. by apply sat_elim in H. Qed.

  (** [⊳ G]: [G] after one step of the logic; at the level of traces, just [G]. *)
  Program Definition itrProp_later G : itrProp Λ Σ :=
    {| itrProp_internal _ τ := (|={⊤,∅}=> ▷ |={∅,⊤}=> itrProp_internal G τ)%I; itrProp_external := itrProp_external G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_later, sat_fupd in H. by eapply itrProp_adeq. Qed.

  (** [○ G]: [G] at the next position. *)
  Program Definition itrProp_next G : itrProp Λ Σ :=
    {| itrProp_internal _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> itrProp_internal G (trace_next τ)))%I;
       itrProp_external τ := itrProp_external G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply itrProp_adeq. Qed.

  (** [⊚ G]: [G] after the step taken at the current position. In the logic this is the
      step's credits and mask change; at the level of traces it is just [G]. *)
  Program Definition itrProp_step G : itrProp Λ Σ :=
    {| itrProp_internal _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> itrProp_internal G τ))%I; itrProp_external := itrProp_external G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply itrProp_adeq. Qed.

  (** [○' G]: [G] read at the next position, with no modality; [○ G] is [⊚ ○' G]. *)
  Program Definition itrProp_shift G : itrProp Λ Σ :=
    {| itrProp_internal _ τ := itrProp_internal G (trace_next τ); itrProp_external τ := itrProp_external G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. by eapply itrProp_adeq. Qed.

  Lemma itrProp_later_mono G G' : itrProp_le G G' → itrProp_le (itrProp_later G) (itrProp_later G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    by iApply HG.
  Qed.
  Lemma itrProp_next_mono G G' : itrProp_le G G' → itrProp_le (itrProp_next G) (itrProp_next G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma itrProp_step_mono G G' : itrProp_le G G' → itrProp_le (itrProp_step G) (itrProp_step G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma itrProp_shift_mono G G' : itrProp_le G G' → itrProp_le (itrProp_shift G) (itrProp_shift G').
  Proof. intros HG ? τ. rewrite /=. by iApply HG. Qed.

  Lemma itrProp_exist_lub {X} `{!TypeExistentialProperty X ordI} (G : X → itrProp Λ Σ) G' :
    (∀ x, itrProp_le (G x) G') → itrProp_le (itrProp_exist G) G'.
  Proof. intros HG ? τ. rewrite /= /trI_exist. iIntros "[%x H]". by iApply HG. Qed.
  Lemma itrProp_exist_ub {X} `{!TypeExistentialProperty X ordI} (G : X → itrProp Λ Σ) x :
    itrProp_le (G x) (itrProp_exist G).
  Proof. intros ? τ. rewrite /= /trI_exist. iIntros "H". by iExists x. Qed.

End connectives.

Global Typeclasses Opaque itrProp_trp itrProp_later itrProp_next.

(** ** Monotone bodies *)
Class ItrPropMono {Λ Σ} (F : itrProp Λ Σ → itrProp Λ Σ) : Prop := {
  itrProp_mono_le X Y : itrProp_le X Y → itrProp_le (F X) (F Y);
  itrProp_mono_ext X Y : (∀ τ, itrProp_external X τ → itrProp_external Y τ) → ∀ τ, itrProp_external (F X) τ → itrProp_external (F Y) τ;
}.
Global Hint Mode ItrPropMono - - ! : typeclass_instances.

Section mono_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : itrProp Λ Σ → itrProp Λ Σ.

  Global Instance itrProp_mono_id : ItrPropMono (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. split; auto. Qed.
  Global Instance itrProp_mono_const G : ItrPropMono (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. split; auto using itrProp_le_refl. Qed.
  Global Instance itrProp_mono_and F1 F2 :
    ItrPropMono F1 → ItrPropMono F2 → ItrPropMono (λ X, itrProp_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply itrProp_and_mono; by apply itrProp_mono_le.
    - intros X Y HXY τ [??]. split; [by apply (itrProp_mono_ext (F:=F1) X Y)|by apply (itrProp_mono_ext (F:=F2) X Y)].
  Qed.
  Global Instance itrProp_mono_or F1 F2 :
    ItrPropMono F1 → ItrPropMono F2 → ItrPropMono (λ X, itrProp_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply itrProp_or_mono; by apply itrProp_mono_le.
    - intros X Y HXY τ [?|?]; [left; by apply (itrProp_mono_ext (F:=F1) X Y)|right; by apply (itrProp_mono_ext (F:=F2) X Y)].
  Qed.
  Global Instance itrProp_mono_impl A F : ItrPropMono F → ItrPropMono (λ X, itrProp_impl A (F X)).
  Proof.
    intros HF. split.
    - intros. apply itrProp_impl_mono; [done|by apply itrProp_mono_le].
    - intros X Y HXY τ H HA. apply (itrProp_mono_ext (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance itrProp_mono_forall {A} (F : A → itrProp Λ Σ → itrProp Λ Σ) :
    (∀ a, ItrPropMono (F a)) → ItrPropMono (λ X, itrProp_forall (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply itrProp_forall_mono. intros a. by apply itrProp_mono_le.
    - intros X Y HXY τ H a. apply (itrProp_mono_ext (F:=F a) X Y); [done|apply H].
  Qed.
  Global Instance itrProp_mono_exist {A} `{!TypeExistentialProperty A ordI} (F : A → itrProp Λ Σ → itrProp Λ Σ) :
    (∀ a, ItrPropMono (F a)) → ItrPropMono (λ X, itrProp_exist (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply itrProp_exist_mono. intros a. by apply itrProp_mono_le.
    - intros X Y HXY τ [a H]. exists a. by apply (itrProp_mono_ext (F:=F a) X Y).
  Qed.
  Global Instance itrProp_mono_later F : ItrPropMono F → ItrPropMono (λ X, itrProp_later (F X)).
  Proof.
    intros HF. split.
    - intros. apply itrProp_later_mono. by apply itrProp_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (itrProp_mono_ext (F:=F) X Y).
  Qed.
  Global Instance itrProp_mono_next F : ItrPropMono F → ItrPropMono (λ X, itrProp_next (F X)).
  Proof.
    intros HF. split.
    - intros. apply itrProp_next_mono. by apply itrProp_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (itrProp_mono_ext (F:=F) X Y).
  Qed.
  Global Instance itrProp_mono_step F : ItrPropMono F → ItrPropMono (λ X, itrProp_step (F X)).
  Proof.
    intros HF. split.
    - intros. apply itrProp_step_mono. by apply itrProp_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (itrProp_mono_ext (F:=F) X Y).
  Qed.
  Global Instance itrProp_mono_shift F : ItrPropMono F → ItrPropMono (λ X, itrProp_shift (F X)).
  Proof.
    intros HF. split.
    - intros. apply itrProp_shift_mono. by apply itrProp_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (itrProp_mono_ext (F:=F) X Y).
  Qed.
  Global Instance itrProp_mono_always F : ItrPropMono F → ItrPropMono (λ X, itrProp_always (F X)).
  Proof.
    intros HF. split.
    - intros. apply itrProp_always_mono. by apply itrProp_mono_le.
    - intros X Y HXY [n τf] H m Hm. apply (itrProp_mono_ext (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance itrProp_mono_until F1 F2 :
    ItrPropMono F1 → ItrPropMono F2 → ItrPropMono (λ X, itrProp_until (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply itrProp_until_mono; by apply itrProp_mono_le.
    - intros X Y HXY [n τf] (m & Hm & HQ & HP). exists m. split_and!; [done| |].
      + by apply (itrProp_mono_ext (F:=F2) X Y).
      + intros l Hl. apply (itrProp_mono_ext (F:=F1) X Y); [done|by apply HP].
  Qed.

End mono_instances.

(** ** Continuous bodies

    [F] commutes, in the logic, with unions of increasing chains indexed by ordinals. Guarded
    bodies are not continuous: the step index ranges beyond [Ord.t], so [▷ ∃ α, X α] does
    not give [∃ α, ▷ X α]. *)
Class ItrPropCont {Λ Σ} (F : itrProp Λ Σ → itrProp Λ Σ) : Prop :=
  itrProp_cont (X : Ord.t → itrProp Λ Σ) :
    (∀ α β, Ord.le α β → itrProp_le (X α) (X β)) →
    itrProp_le (F (itrProp_exist X)) (itrProp_exist (λ α, F (X α))).
Global Hint Mode ItrPropCont - - ! : typeclass_instances.

Section cont_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : itrProp Λ Σ → itrProp Λ Σ.

  Global Instance itrProp_cont_id : ItrPropCont (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. intros X _. apply itrProp_le_refl. Qed.
  Global Instance itrProp_cont_const G : ItrPropCont (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. intros X _ ? τ. rewrite /= /trI_exist. iIntros "H". by iExists Ord.O. Qed.
  Global Instance itrProp_cont_and F1 F2 `{!ItrPropMono F1, !ItrPropMono F2} :
    ItrPropCont F1 → ItrPropCont F2 → ItrPropCont (λ X, itrProp_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2 X HX ? τ. rewrite /= /trI_and (H1 X HX _ τ) (H2 X HX _ τ) /= /trI_exist.
    rewrite bi.and_exist_r. iIntros "[%α H]". rewrite bi.and_exist_l. iDestruct "H" as (β) "H".
    iExists (Ord.union α β). iSplit.
    - iDestruct "H" as "[H _]". iApply (itrProp_mono_le (X α)); [apply HX, Ord.union_l|done].
    - iDestruct "H" as "[_ H]". iApply (itrProp_mono_le (X β)); [apply HX, Ord.union_r|done].
  Qed.
  Global Instance itrProp_cont_or F1 F2 :
    ItrPropCont F1 → ItrPropCont F2 → ItrPropCont (λ X, itrProp_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2 X HX ? τ. rewrite /= /trI_or (H1 X HX _ τ) (H2 X HX _ τ) /= /trI_exist.
    iIntros "[[%α H]|[%α H]]"; iExists α; [by iLeft|by iRight].
  Qed.
  Global Instance itrProp_cont_impl A F : ItrPropCont F → ItrPropCont (λ X, itrProp_impl A (F X)).
  Proof.
    intros HF X HX ? τ. rewrite /= /trI_impl (HF X HX _ τ) /= /trI_exist. iIntros "H".
    destruct (classic (itrProp_external A τ)) as [HA|HA].
    - iDestruct ("H" $! HA) as (α) "H". iExists α. by iIntros "_".
    - iExists Ord.O. by iIntros (?).
  Qed.
  Global Instance itrProp_cont_exist {A} `{!TypeExistentialProperty A ordI} (F : A → itrProp Λ Σ → itrProp Λ Σ) :
    (∀ a, ItrPropCont (F a)) → ItrPropCont (λ X, itrProp_exist (λ a, F a X)).
  Proof.
    intros HF X HX ? τ. rewrite /= /trI_exist. iIntros "[%a H]".
    rewrite (HF a X HX _ τ) /= /trI_exist. iDestruct "H" as (α) "H". iExists α, a. done.
  Qed.
  Global Instance itrProp_cont_shift F : ItrPropCont F → ItrPropCont (λ X, itrProp_shift (F X)).
  Proof. intros HF X HX ? τ. rewrite /= (HF X HX _ (trace_next τ)) /= /trI_exist. done. Qed.

End cont_instances.

(** ** Greatest fixpoints *)
Section nu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : itrProp Λ Σ.

  Program Definition itrProp_nu (F : itrProp Λ Σ → itrProp Λ Σ) `{!ItrPropMono F} : itrProp Λ Σ :=
    {| itrProp_internal H τ := (∃ X : itrProp Λ Σ, ⌜itrProp_le X (F X)⌝ ∧ @itrProp_internal _ _ X H τ)%I;
       itrProp_external := tr_gfp (λ R, itrProp_external (F (itrProp_trp R))) |}.
  Next Obligation.
    intros F HF H F0 τ Hsat.
    pose (I := λ (H' : temporalGS Λ Σ) (τ' : trace Λ),
                 (∃ X : itrProp Λ Σ, ⌜itrProp_le X (F X)⌝ ∧ @itrProp_internal _ _ X H' τ')%I).
    (* The traces at which the in-logic reading is satisfiable, for some instance. *)
    pose (S := λ τ', ∃ (H' : temporalGS Λ Σ) (F' : iProp Σ), iProp_sat_lc_at_frame F' ⊤ (I H' τ')).
    assert (HS : ∀ (H' : temporalGS Λ Σ) (F' : iProp Σ) τ',
               iProp_sat_lc_at_frame F' ⊤ (I H' τ') → S τ').
    { intros H' F' τ' Hs. by exists H', F'. }
    pose (N := ItrProp I S HS).
    (* [S] is a post-fixpoint of the trace functor. *)
    exists S. split; last by exists H, F0.
    intros τ' (H' & F' & Hs).
    assert (HXN : ∀ X, itrProp_le X (F X) → itrProp_le X N).
    { intros X HX ? τ''. rewrite /=. iIntros "HX". iExists X. by iFrame. }
    assert (HIN : I H' τ' ⊢ @itrProp_internal _ _ (F N) H' τ').
    { iIntros "[%X [%HX HXt]]". iApply (itrProp_mono_le X N (HXN X HX)). by iApply HX. }
    apply (sat_mono _ _ HIN) in Hs. apply (itrProp_adeq (F N)) in Hs.
    eapply (itrProp_mono_ext N (itrProp_trp S)); last exact Hs. done.
  Qed.

  Context (F : itrProp Λ Σ → itrProp Λ Σ) `{!ItrPropMono F}.

  Lemma itrProp_nu_coind X : itrProp_le X (F X) → itrProp_le X (itrProp_nu F).
  Proof. intros HX ? τ. rewrite /=. iIntros "H". iExists X. by iFrame. Qed.

  Lemma itrProp_nu_unfold_l : itrProp_le (itrProp_nu F) (F (itrProp_nu F)).
  Proof.
    intros ? τ. rewrite {1}/itrProp_internal /=. iIntros "[%X [%HX H]]".
    iApply (itrProp_mono_le X (itrProp_nu F)); first by apply itrProp_nu_coind. by iApply HX.
  Qed.

  Lemma itrProp_nu_unfold_r : itrProp_le (F (itrProp_nu F)) (itrProp_nu F).
  Proof. apply itrProp_nu_coind, itrProp_mono_le, itrProp_nu_unfold_l. Qed.

  Lemma itrProp_nu_ext τ : itrProp_external (itrProp_nu F) τ ↔ tr_gfp (λ R, itrProp_external (F (itrProp_trp R))) τ.
  Proof. done. Qed.

End nu.

(** ** Least fixpoints, with ordinal approximants

    The ordinal is the measure a least fixpoint needs in a step-indexed logic: without it, a
    guarded body has a unique fixpoint, and [μ] would be [ν]. *)
Section mu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : itrProp Λ Σ.
  Context (F : itrProp Λ Σ → itrProp Λ Σ).

  Fixpoint itrProp_mu_rec (α : Ord.t) (ACC : Acc Ord.lt α) {struct ACC} : itrProp Λ Σ :=
    F (itrProp_exist (λ b : {β : Ord.t | Ord.lt β α},
                    itrProp_mu_rec (proj1_sig b) (Acc_inv ACC (proj2_sig b)))).

  (** The approximant [μ_α]. *)
  Definition itrProp_mu_approx (α : Ord.t) : itrProp Λ Σ := itrProp_mu_rec α (Ord.lt_well_founded α).
  Definition itrProp_mu : itrProp Λ Σ := itrProp_exist itrProp_mu_approx.

  Lemma itrProp_mu_rec_irrel α A1 A2 : itrProp_mu_rec α A1 = itrProp_mu_rec α A2.
  Proof.
    revert A1 A2. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros [A1] [A2]. simpl. f_equal. f_equal. apply func_ext. intros [β Hβ]. by apply IH.
  Qed.

  Lemma itrProp_mu_approx_unfold α :
    itrProp_mu_approx α = F (itrProp_exist (λ b : {β : Ord.t | Ord.lt β α}, itrProp_mu_approx (proj1_sig b))).
  Proof.
    rewrite /itrProp_mu_approx. generalize (Ord.lt_well_founded α) as ACC. intros [A]. simpl.
    f_equal. f_equal. apply func_ext. intros b. apply itrProp_mu_rec_irrel.
  Qed.

  (** Introduction with a ranking: [H α] unfolds to [F] of smaller ranks. *)
  Lemma itrProp_mu_rank `{!ItrPropMono F} (H : Ord.t → itrProp Λ Σ) :
    (∀ α, itrProp_le (H α) (F (itrProp_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    ∀ α, itrProp_le (H α) (itrProp_mu_approx α).
  Proof.
    intros HH α. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite itrProp_mu_approx_unfold. eapply itrProp_le_trans; first apply HH.
    apply itrProp_mono_le, itrProp_exist_mono. intros [β Hβ]. by apply IH.
  Qed.

  Lemma itrProp_mu_intro `{!ItrPropMono F} (H : Ord.t → itrProp Λ Σ) α :
    (∀ α, itrProp_le (H α) (F (itrProp_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    itrProp_le (H α) itrProp_mu.
  Proof.
    intros HH. eapply itrProp_le_trans; first by apply itrProp_mu_rank. apply (itrProp_exist_ub itrProp_mu_approx).
  Qed.

  (** Induction: [itrProp_mu F] is below every pre-fixpoint. *)
  Lemma itrProp_mu_ind X `{!ItrPropMono F} : itrProp_le (F X) X → itrProp_le itrProp_mu X.
  Proof.
    intros HX. apply itrProp_exist_lub. intros α.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite itrProp_mu_approx_unfold. eapply itrProp_le_trans; last apply HX.
    apply itrProp_mono_le, itrProp_exist_lub. intros [β Hβ]. by apply IH.
  Qed.

  Lemma itrProp_mu_post `{!ItrPropMono F} : itrProp_le itrProp_mu (F itrProp_mu).
  Proof.
    apply itrProp_exist_lub. intros α. rewrite itrProp_mu_approx_unfold.
    apply itrProp_mono_le, itrProp_exist_lub. intros [β ?]. apply (itrProp_exist_ub itrProp_mu_approx).
  Qed.

  Lemma itrProp_mu_approx_mono `{!ItrPropMono F} α β :
    Ord.le α β → itrProp_le (itrProp_mu_approx α) (itrProp_mu_approx β).
  Proof.
    intros Hle. rewrite !itrProp_mu_approx_unfold. apply itrProp_mono_le, itrProp_exist_lub. intros [γ Hγ].
    apply (itrProp_exist_ub (λ b : {γ | Ord.lt γ β}, itrProp_mu_approx (proj1_sig b))
             (γ ↾ Ord.lt_le_lt Hγ Hle)).
  Qed.

  (** The fold, for a continuous body; with [itrProp_mu_post], [itrProp_mu F] is then a fixpoint.
      A guarded body has no fold ([itrProp_mu_unfold_r_guarded]). *)
  Lemma itrProp_mu_unfold_r `{!ItrPropMono F, !ItrPropCont F} : itrProp_le (F itrProp_mu) itrProp_mu.
  Proof.
    eapply itrProp_le_trans; first (apply (itrProp_cont itrProp_mu_approx); intros; by apply itrProp_mu_approx_mono).
    apply itrProp_exist_lub. intros α. eapply itrProp_le_trans; last apply (itrProp_exist_ub itrProp_mu_approx (Ord.S α)).
    rewrite (itrProp_mu_approx_unfold (Ord.S α)). apply itrProp_mono_le.
    apply (itrProp_exist_ub (λ b : {β | Ord.lt β (Ord.S α)}, itrProp_mu_approx (proj1_sig b)) (α ↾ Ord.S_lt α)).
  Qed.

  Lemma itrProp_mu_ext τ `{!ItrPropMono F} : itrProp_external itrProp_mu τ → tr_lfp (λ R, itrProp_external (F (itrProp_trp R))) τ.
  Proof.
    assert (Hm : tr_mono (λ R, itrProp_external (F (itrProp_trp R)))).
    { intros R R' HR τ'. by apply itrProp_mono_ext. }
    intros [α Hα]. revert τ Hα. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros τ Hα. rewrite itrProp_mu_approx_unfold in Hα. apply tr_lfp_unfold_r; first done.
    eapply itrProp_mono_ext; last exact Hα. intros τ' [[β Hβ] H']. by apply (IH β).
  Qed.

  (** The trace reading is a pre-fixpoint of the trace functor: the join of the ranks of its
      traces bounds them all. *)
  Lemma itrProp_mu_ext_pre `{!ItrPropMono F} τ :
    itrProp_external (F (itrProp_trp (itrProp_external itrProp_mu))) τ → itrProp_external itrProp_mu τ.
  Proof.
    intros Hτ.
    destruct (choice (λ (τ' : trace Λ) (α : Ord.t), itrProp_external itrProp_mu τ' → itrProp_external (itrProp_mu_approx α) τ'))
      as [f Hf].
    { intros τ'. destruct (classic (itrProp_external itrProp_mu τ')) as [[α Hα]|Hn]; [by exists α|by exists Ord.O]. }
    exists (Ord.S (Ord.join f)). rewrite itrProp_mu_approx_unfold.
    eapply itrProp_mono_ext; last exact Hτ. intros τ' Hτ'.
    exists (f τ' ↾ Ord.le_lt_lt (Ord.join_upperbound f τ') (Ord.S_lt _)). simpl. by apply Hf.
  Qed.

  Lemma itrProp_mu_ext_lfp `{!ItrPropMono F} τ : tr_lfp (λ R, itrProp_external (F (itrProp_trp R))) τ → itrProp_external itrProp_mu τ.
  Proof. intros H. apply H. intros τ'. apply itrProp_mu_ext_pre. Qed.

  Lemma itrProp_mu_ext_iff `{!ItrPropMono F} τ : itrProp_external itrProp_mu τ ↔ tr_lfp (λ R, itrProp_external (F (itrProp_trp R))) τ.
  Proof. split; [by apply itrProp_mu_ext|apply itrProp_mu_ext_lfp]. Qed.

  (** On traces, [itrProp_mu F] is a fixpoint of [F], for any monotone body. *)
  Lemma itrProp_mu_ext_unfold_l `{!ItrPropMono F} τ : itrProp_external itrProp_mu τ → itrProp_external (F itrProp_mu) τ.
  Proof.
    intros [α Hα]. rewrite itrProp_mu_approx_unfold in Hα. eapply itrProp_mono_ext; last exact Hα.
    intros τ' [b H]. by exists (proj1_sig b).
  Qed.
  Lemma itrProp_mu_ext_unfold_r `{!ItrPropMono F} τ : itrProp_external (F itrProp_mu) τ → itrProp_external itrProp_mu τ.
  Proof. intros H. apply itrProp_mu_ext_pre. by eapply itrProp_mono_ext; last exact H. Qed.

End mu.

(** ** Always and until as fixpoints *)
Section ltl.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : itrProp Λ Σ.

  (** The step-indexed readings decide a position after the step taken there, so the
      bodies are [⊳ ⊚ (G ∧ ○'X)] and [⊳ ⊚ (G2 ∨ (G1 ∧ ○'X))]; on traces these read as
      [G ∧ ○X] and [G2 ∨ (G1 ∧ ○X)]. *)
  Definition F_always G : itrProp Λ Σ → itrProp Λ Σ := λ X, itrProp_later (itrProp_step (itrProp_and G (itrProp_shift X))).
  Definition F_until G1 G2 : itrProp Λ Σ → itrProp Λ Σ :=
    λ X, itrProp_later (itrProp_step (itrProp_or G2 (itrProp_and G1 (itrProp_shift X)))).
  Global Instance F_always_mono G : ItrPropMono (F_always G).
  Proof.
    apply (itrProp_mono_later (λ X, itrProp_step (itrProp_and G (itrProp_shift X)))),
      (itrProp_mono_step (λ X, itrProp_and G (itrProp_shift X))), (itrProp_mono_and (λ _, G) (λ X, itrProp_shift X)).
    - apply itrProp_mono_const.
    - apply (itrProp_mono_shift (λ X, X)), itrProp_mono_id.
  Qed.
  Global Instance F_until_mono G1 G2 : ItrPropMono (F_until G1 G2).
  Proof.
    apply (itrProp_mono_later (λ X, itrProp_step (itrProp_or G2 (itrProp_and G1 (itrProp_shift X))))),
      (itrProp_mono_step (λ X, itrProp_or G2 (itrProp_and G1 (itrProp_shift X)))),
      (itrProp_mono_or (λ _, G2) (λ X, itrProp_and G1 (itrProp_shift X))); first apply itrProp_mono_const.
    apply (itrProp_mono_and (λ _, G1) (λ X, itrProp_shift X)); first apply itrProp_mono_const.
    apply (itrProp_mono_shift (λ X, X)), itrProp_mono_id.
  Qed.

  (** [□ G] is [ν X. ⊳ ⊚ (G ∧ ○'X)], in both directions. *)
  Lemma itrProp_always_le_nu G : itrProp_le (itrProp_always G) (itrProp_nu (F_always G)).
  Proof.
    apply itrProp_nu_coind. intros ? τ. rewrite /F_always /= trI_always_unfold /trI_always_pre /trI_and /trI_pure.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". by iDestruct "H" as "[_ [_ $]]".
  Qed.

  Lemma itrProp_nu_le_always G : itrProp_le (itrProp_nu (F_always G)) (itrProp_always G).
  Proof.
    intros ? τ. rewrite {1}/itrProp_internal /=. iIntros "[%X [%HX H]]".
    iRevert (τ) "H". iLöb as "IH". iIntros (τ) "H".
    iPoseProof (HX _ τ with "H") as "H". rewrite /F_always. iSimpl in "H".
    rewrite trI_always_unfold /trI_always_pre /trI_and /trI_pure.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". iSplit; first done.
    iDestruct "H" as "[_ H]". by iApply "IH".
  Qed.

  (** On traces, [ν X. G ∧ ○X] is [□ G]. *)
  Lemma itrProp_nu_always_ext G : itrProp_external (itrProp_nu (F_always G)) ⊆ (□ itrProp_external G)%R.
  Proof.
    intros [n τf]. rewrite itrProp_nu_ext. intros (R & HR & Hτ).
    assert (Hk : ∀ k, R (n + k, τf)).
    { intros k. induction k as [|k IHk]; first by rewrite Nat.add_0_r.
      destruct (HR _ IHk) as [_ Hnext]. by rewrite Nat.add_succ_r. }
    intros m Hm. replace m with (n + (m - n)) by lia. by destruct (HR _ (Hk (m - n))).
  Qed.
  Lemma itrProp_nu_always_ext' G : (□ itrProp_external G)%R ⊆ itrProp_external (itrProp_nu (F_always G)).
  Proof.
    intros [n τf] Hal. rewrite itrProp_nu_ext. exists (tr_always (itrProp_external G)). split; last done.
    intros [n' τf'] Hal'. split; first (apply Hal'; lia).
    intros m Hm. apply Hal'. simpl in Hm. lia.
  Qed.

  (** A ranked until. *)
  Program Definition itrProp_until_at G1 G2 (a : Ord.t) : itrProp Λ Σ :=
    {| itrProp_internal _ := trI_until Ord.lt a (itrProp_internal G1) (itrProp_internal G2); itrProp_external := itrProp_external (itrProp_until G1 G2) |}.
  Next Obligation.
    intros G1 G2 a ? F τ H. eapply (itrProp_adeq (itrProp_until G1 G2)). simpl. rewrite /trI_exist.
    eapply sat_mono; last exact H. iIntros "H". by iExists a.
  Qed.

  (** [G1 𝒰 G2] is below [μ X. ⊳(G2 ∨ (G1 ∧ ○X))]: its measure is a ranking. *)
  Lemma itrProp_until_le_mu G1 G2 : itrProp_le (itrProp_until G1 G2) (itrProp_mu (F_until G1 G2)).
  Proof.
    eapply itrProp_le_trans; [|apply itrProp_exist_lub; intros a; apply (itrProp_mu_intro _ (itrProp_until_at G1 G2))].
    - intros ? τ. rewrite /= /trI_exist. iIntros "[%a H]". by iExists a.
    - intros α ? τ. rewrite /F_until /= trI_until_unfold /trI_until_pre /trI_or /trI_and /trI_exist.
      iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
      iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
      iDestruct "H" as "[H|H]"; first by iLeft. iRight.
      iSplit; first by iDestruct "H" as "[$ _]".
      iDestruct "H" as "[_ (%a'& %Hlt& H)]". by iExists (a' ↾ Hlt).
  Qed.

  Lemma itrProp_mu_until_ext G1 G2 τ :
    itrProp_external (itrProp_mu (F_until G1 G2)) τ → tr_until (itrProp_external G1) (itrProp_external G2) τ.
  Proof.
    intros H. apply itrProp_mu_ext in H; last apply _. revert τ H. apply tr_lfp_ind.
    intros [n τf] [HQ|[HP (m & Hm & HQ & HPs)]].
    - exists n. split_and!; [lia|done|lia].
    - exists m. split_and!; [simpl in Hm; lia|done|].
      intros l Hl. destruct (decide (l = n)) as [->|Hne]; first done. apply HPs. simpl. lia.
  Qed.

  (** Conversely, [μ X. ⊳(G2 ∨ (G1 ∧ ○X))] is below [G1 𝒰 G2]: the approximant [μ_α] is
      the until ranked by [α]. *)
  Lemma itrProp_mu_approx_le_until G1 G2 α :
    itrProp_le (itrProp_mu_approx (F_until G1 G2) α) (itrProp_until_at G1 G2 α).
  Proof.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros ? τ. rewrite itrProp_mu_approx_unfold /F_until /= trI_until_unfold /trI_until_pre /trI_or /trI_and /trI_exist.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iDestruct "H" as "[H|H]"; first by iLeft. iRight.
    iSplit; first by iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ [%b H]]". destruct b as [β Hβ]. iExists β. iSplit; first done.
    by iApply (IH β Hβ).
  Qed.

  Lemma itrProp_mu_le_until G1 G2 : itrProp_le (itrProp_mu (F_until G1 G2)) (itrProp_until G1 G2).
  Proof.
    apply itrProp_exist_lub. intros α. eapply itrProp_le_trans; first apply itrProp_mu_approx_le_until.
    intros ? τ. rewrite /= /trI_exist. iIntros "H". by iExists α.
  Qed.

  Lemma itrProp_mu_until_ext_iff G1 G2 τ :
    itrProp_external (itrProp_mu (F_until G1 G2)) τ ↔ tr_until (itrProp_external G1) (itrProp_external G2) τ.
  Proof.
    split; first apply itrProp_mu_until_ext. intros Hu. apply itrProp_mu_ext_lfp; first apply _.
    intros R HR. destruct τ as [n τf]. destruct Hu as (m & Hnm & HQ & HP).
    (* the until is below every pre-fixpoint, by the distance to the right formula *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → itrProp_external G1 (l, τf)) → R (n', τf)) as Hd.
    { induction d as [|d IHd]; intros n' Hd Hn' HP'; apply HR; rewrite /F_until /=.
      - left. by assert (m = n') as <- by lia.
      - right. split; first (apply HP'; lia).
        apply IHd; [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. simpl in Hl. lia. }
    apply (Hd (m - n)); [done|done|]. intros l Hl. apply HP. lia.
  Qed.

  (** Beyond LTL: [G] at every even position, [ν X. ⊳ ⊚ (G ∧ ○' ○ X)] (not expressible in LTL). *)
  Definition F_even G : itrProp Λ Σ → itrProp Λ Σ :=
    λ X, itrProp_later (itrProp_step (itrProp_and G (itrProp_shift (itrProp_next X)))).
  Global Instance F_even_mono G : ItrPropMono (F_even G).
  Proof.
    apply (itrProp_mono_later (λ X, itrProp_step (itrProp_and G (itrProp_shift (itrProp_next X))))),
      (itrProp_mono_step (λ X, itrProp_and G (itrProp_shift (itrProp_next X)))),
      (itrProp_mono_and (λ _, G) (λ X, itrProp_shift (itrProp_next X))); first apply itrProp_mono_const.
    apply (itrProp_mono_shift (λ X, itrProp_next X)), (itrProp_mono_next (λ X, X)), itrProp_mono_id.
  Qed.

  Lemma itrProp_nu_even_ext G n τf :
    itrProp_external (itrProp_nu (F_even G)) (n, τf) ↔ ∀ k, itrProp_external G (n + 2 * k, τf).
  Proof.
    rewrite itrProp_nu_ext. split.
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
