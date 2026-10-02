From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.program_logic Require Export temporal_guarantee.
From lantana.program_logic Require Import temporal_saved.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable later_credits.
From lantana.algebra Require Import ordinal_existential_properties.
From lantana.prelude Require Import axioms.

(** * Least and greatest fixpoints of trace properties

    The body of a fixpoint is any [F : tps Λ Σ → tps Λ Σ] that is monotone for both readings
    ([TpsMono]); no syntax is involved.

    - [tps_nu F]: the in-logic reading is the union of all post-fixpoints of [F] (for [⊑]);
      the trace reading is the greatest fixpoint of the trace functor
      [R ↦ tps_tr (F (tps_trp R))]. Soundness: the set of traces at which the in-logic
      reading is satisfiable is a post-fixpoint of the trace functor (coinduction).
    - [tps_mu F]: approximants [μ_α := F (∃ β < α, μ_β)] by well-founded recursion on
      ordinals, and [μ := ∃ α, μ_α]. Each approximant is a trace property, so soundness is
      free; the trace reading implies the least fixpoint of the trace functor. The ordinal
      is the measure that a least fixpoint needs in a step-indexed logic: without it (an
      impredicative least fixpoint for [⊑]) a guarded body has a unique fixpoint, so [μ]
      would coincide with [ν].

    The in-logic step [tps_later] and next position [tps_next] are the two halves of the
    step built into [tps_always] and [tps_until]; with them, [tps_always G] is
    [ν X. ⊳(G ∧ ○X)] and [tps_until G1 G2] is below [μ X. ⊳(G2 ∨ (G1 ∧ ○X))]. *)


(** ** Trace predicates, the in-logic step, and the next position *)
Section connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : tps Λ Σ.

  (** Any trace predicate, read in the logic as a pure fact. *)
  Program Definition tps_trp (R : trProp Λ) : tps Λ Σ :=
    {| tps_ti _ τ := ⌜R τ⌝%I; tps_tr := R |}.
  Next Obligation. intros R ? F τ H. by apply sat_elim in H. Qed.

  (** [⊳ G]: [G] after one step of the logic; at the level of traces, just [G]. *)
  Program Definition tps_later G : tps Λ Σ :=
    {| tps_ti _ τ := (|={⊤,∅}=> ▷ |={∅,⊤}=> tps_ti G τ)%I; tps_tr := tps_tr G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_later, sat_fupd in H. by eapply tps_good. Qed.

  (** [○ G]: [G] at the next position. *)
  Program Definition tps_next G : tps Λ Σ :=
    {| tps_ti _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> tps_ti G (trace_next τ)))%I;
       tps_tr τ := tps_tr G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply tps_good. Qed.

  (** [⊚ G]: [G] after the step taken at the current position. In the logic this is the
      step's credits and mask change; at the level of traces it is just [G]. *)
  Program Definition tps_step G : tps Λ Σ :=
    {| tps_ti _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> tps_ti G τ))%I; tps_tr := tps_tr G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply tps_good. Qed.

  (** [○' G]: [G] read at the next position, with no modality; [○ G] is [⊚ ○' G]. *)
  Program Definition tps_shift G : tps Λ Σ :=
    {| tps_ti _ τ := tps_ti G (trace_next τ); tps_tr τ := tps_tr G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. by eapply tps_good. Qed.

  Lemma tps_later_mono G G' : tps_le G G' → tps_le (tps_later G) (tps_later G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    by iApply HG.
  Qed.
  Lemma tps_next_mono G G' : tps_le G G' → tps_le (tps_next G) (tps_next G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma tps_step_mono G G' : tps_le G G' → tps_le (tps_step G) (tps_step G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma tps_shift_mono G G' : tps_le G G' → tps_le (tps_shift G) (tps_shift G').
  Proof. intros HG ? τ. rewrite /=. by iApply HG. Qed.

  Lemma tps_exist_lub {X} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) G' :
    (∀ x, tps_le (G x) G') → tps_le (tps_exist G) G'.
  Proof. intros HG ? τ. rewrite /= /ti_exist. iIntros "[%x H]". by iApply HG. Qed.
  Lemma tps_exist_ub {X} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) x :
    tps_le (G x) (tps_exist G).
  Proof. intros ? τ. rewrite /= /ti_exist. iIntros "H". by iExists x. Qed.

End connectives.

Global Typeclasses Opaque tps_trp tps_later tps_next.

(** ** Monotone bodies *)
Class TpsMono {Λ Σ} (F : tps Λ Σ → tps Λ Σ) : Prop := {
  tps_mono_le X Y : tps_le X Y → tps_le (F X) (F Y);
  tps_mono_tr X Y : (∀ τ, tps_tr X τ → tps_tr Y τ) → ∀ τ, tps_tr (F X) τ → tps_tr (F Y) τ;
}.
Global Hint Mode TpsMono - - ! : typeclass_instances.

Section mono_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : tps Λ Σ → tps Λ Σ.

  Global Instance tps_mono_id : TpsMono (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. split; auto. Qed.
  Global Instance tps_mono_const G : TpsMono (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. split; auto using tps_le_refl. Qed.
  Global Instance tps_mono_and F1 F2 :
    TpsMono F1 → TpsMono F2 → TpsMono (λ X, tps_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply tps_and_mono; by apply tps_mono_le.
    - intros X Y HXY τ [??]. split; [by apply (tps_mono_tr (F:=F1) X Y)|by apply (tps_mono_tr (F:=F2) X Y)].
  Qed.
  Global Instance tps_mono_or F1 F2 :
    TpsMono F1 → TpsMono F2 → TpsMono (λ X, tps_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply tps_or_mono; by apply tps_mono_le.
    - intros X Y HXY τ [?|?]; [left; by apply (tps_mono_tr (F:=F1) X Y)|right; by apply (tps_mono_tr (F:=F2) X Y)].
  Qed.
  Global Instance tps_mono_impl A F : TpsMono F → TpsMono (λ X, tps_impl A (F X)).
  Proof.
    intros HF. split.
    - intros. apply tps_impl_mono; [done|by apply tps_mono_le].
    - intros X Y HXY τ H HA. apply (tps_mono_tr (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance tps_mono_forall {A} (F : A → tps Λ Σ → tps Λ Σ) :
    (∀ a, TpsMono (F a)) → TpsMono (λ X, tps_forall (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply tps_forall_mono. intros a. by apply tps_mono_le.
    - intros X Y HXY τ H a. apply (tps_mono_tr (F:=F a) X Y); [done|apply H].
  Qed.
  Global Instance tps_mono_exist {A} `{!TypeExistentialProperty A ordI} (F : A → tps Λ Σ → tps Λ Σ) :
    (∀ a, TpsMono (F a)) → TpsMono (λ X, tps_exist (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply tps_exist_mono. intros a. by apply tps_mono_le.
    - intros X Y HXY τ [a H]. exists a. by apply (tps_mono_tr (F:=F a) X Y).
  Qed.
  Global Instance tps_mono_later F : TpsMono F → TpsMono (λ X, tps_later (F X)).
  Proof.
    intros HF. split.
    - intros. apply tps_later_mono. by apply tps_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (tps_mono_tr (F:=F) X Y).
  Qed.
  Global Instance tps_mono_next F : TpsMono F → TpsMono (λ X, tps_next (F X)).
  Proof.
    intros HF. split.
    - intros. apply tps_next_mono. by apply tps_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (tps_mono_tr (F:=F) X Y).
  Qed.
  Global Instance tps_mono_step F : TpsMono F → TpsMono (λ X, tps_step (F X)).
  Proof.
    intros HF. split.
    - intros. apply tps_step_mono. by apply tps_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (tps_mono_tr (F:=F) X Y).
  Qed.
  Global Instance tps_mono_shift F : TpsMono F → TpsMono (λ X, tps_shift (F X)).
  Proof.
    intros HF. split.
    - intros. apply tps_shift_mono. by apply tps_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (tps_mono_tr (F:=F) X Y).
  Qed.
  Global Instance tps_mono_always F : TpsMono F → TpsMono (λ X, tps_always (F X)).
  Proof.
    intros HF. split.
    - intros. apply tps_always_mono. by apply tps_mono_le.
    - intros X Y HXY [n τf] H m Hm. apply (tps_mono_tr (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance tps_mono_until F1 F2 :
    TpsMono F1 → TpsMono F2 → TpsMono (λ X, tps_until (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply tps_until_mono; by apply tps_mono_le.
    - intros X Y HXY [n τf] (m & Hm & HQ & HP). exists m. split_and!; [done| |].
      + by apply (tps_mono_tr (F:=F2) X Y).
      + intros l Hl. apply (tps_mono_tr (F:=F1) X Y); [done|by apply HP].
  Qed.

End mono_instances.

(** ** Greatest fixpoints *)
Section nu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : tps Λ Σ.

  Program Definition tps_nu (F : tps Λ Σ → tps Λ Σ) `{!TpsMono F} : tps Λ Σ :=
    {| tps_ti H τ := (∃ X : tps Λ Σ, ⌜tps_le X (F X)⌝ ∧ @tps_ti _ _ X H τ)%I;
       tps_tr := tr_gfp (λ R, tps_tr (F (tps_trp R))) |}.
  Next Obligation.
    intros F HF H F0 τ Hsat.
    pose (I := λ (H' : temporalGS Λ Σ) (τ' : trace Λ),
                 (∃ X : tps Λ Σ, ⌜tps_le X (F X)⌝ ∧ @tps_ti _ _ X H' τ')%I).
    (* The traces at which the in-logic reading is satisfiable, for some instance. *)
    pose (S := λ τ', ∃ (H' : temporalGS Λ Σ) (F' : iProp Σ), iProp_sat_lc_at_frame F' ⊤ (I H' τ')).
    assert (HS : ∀ (H' : temporalGS Λ Σ) (F' : iProp Σ) τ',
               iProp_sat_lc_at_frame F' ⊤ (I H' τ') → S τ').
    { intros H' F' τ' Hs. by exists H', F'. }
    pose (N := Tps I S HS).
    (* [S] is a post-fixpoint of the trace functor. *)
    exists S. split; last by exists H, F0.
    intros τ' (H' & F' & Hs).
    assert (HXN : ∀ X, tps_le X (F X) → tps_le X N).
    { intros X HX ? τ''. rewrite /=. iIntros "HX". iExists X. by iFrame. }
    assert (HIN : I H' τ' ⊢ @tps_ti _ _ (F N) H' τ').
    { iIntros "[%X [%HX HXt]]". iApply (tps_mono_le X N (HXN X HX)). by iApply HX. }
    apply (sat_mono _ _ HIN) in Hs. apply (tps_good (F N)) in Hs.
    eapply (tps_mono_tr N (tps_trp S)); last exact Hs. done.
  Qed.

  Context (F : tps Λ Σ → tps Λ Σ) `{!TpsMono F}.

  Lemma tps_nu_coind X : tps_le X (F X) → tps_le X (tps_nu F).
  Proof. intros HX ? τ. rewrite /=. iIntros "H". iExists X. by iFrame. Qed.

  Lemma tps_nu_unfold_l : tps_le (tps_nu F) (F (tps_nu F)).
  Proof.
    intros ? τ. rewrite {1}/tps_ti /=. iIntros "[%X [%HX H]]".
    iApply (tps_mono_le X (tps_nu F)); first by apply tps_nu_coind. by iApply HX.
  Qed.

  Lemma tps_nu_unfold_r : tps_le (F (tps_nu F)) (tps_nu F).
  Proof. apply tps_nu_coind, tps_mono_le, tps_nu_unfold_l. Qed.

  Lemma tps_nu_tr τ : tps_tr (tps_nu F) τ ↔ tr_gfp (λ R, tps_tr (F (tps_trp R))) τ.
  Proof. done. Qed.

End nu.

(** ** Least fixpoints, with ordinal approximants *)
Section mu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : tps Λ Σ.
  Context (F : tps Λ Σ → tps Λ Σ).

  Fixpoint tps_mu_rec (α : Ord.t) (ACC : Acc Ord.lt α) {struct ACC} : tps Λ Σ :=
    F (tps_exist (λ b : {β : Ord.t | Ord.lt β α},
                    tps_mu_rec (proj1_sig b) (Acc_inv ACC (proj2_sig b)))).

  (** The approximant [μ_α]. *)
  Definition tps_mu_approx (α : Ord.t) : tps Λ Σ := tps_mu_rec α (Ord.lt_well_founded α).
  Definition tps_mu : tps Λ Σ := tps_exist tps_mu_approx.

  Lemma tps_mu_rec_irrel α A1 A2 : tps_mu_rec α A1 = tps_mu_rec α A2.
  Proof.
    revert A1 A2. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros [A1] [A2]. simpl. f_equal. f_equal. apply func_ext. intros [β Hβ]. by apply IH.
  Qed.

  Lemma tps_mu_approx_unfold α :
    tps_mu_approx α = F (tps_exist (λ b : {β : Ord.t | Ord.lt β α}, tps_mu_approx (proj1_sig b))).
  Proof.
    rewrite /tps_mu_approx. generalize (Ord.lt_well_founded α) as ACC. intros [A]. simpl.
    f_equal. f_equal. apply func_ext. intros b. apply tps_mu_rec_irrel.
  Qed.

  (** Introduction with a ranking: [H α] unfolds to [F] of smaller ranks. *)
  Lemma tps_mu_rank `{!TpsMono F} (H : Ord.t → tps Λ Σ) :
    (∀ α, tps_le (H α) (F (tps_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    ∀ α, tps_le (H α) (tps_mu_approx α).
  Proof.
    intros HH α. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite tps_mu_approx_unfold. eapply tps_le_trans; first apply HH.
    apply tps_mono_le, tps_exist_mono. intros [β Hβ]. by apply IH.
  Qed.

  Lemma tps_mu_intro `{!TpsMono F} (H : Ord.t → tps Λ Σ) α :
    (∀ α, tps_le (H α) (F (tps_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    tps_le (H α) tps_mu.
  Proof.
    intros HH. eapply tps_le_trans; first by apply tps_mu_rank. apply (tps_exist_ub tps_mu_approx).
  Qed.

  (** Induction: [tps_mu F] is below every pre-fixpoint. *)
  Lemma tps_mu_ind X `{!TpsMono F} : tps_le (F X) X → tps_le tps_mu X.
  Proof.
    intros HX. apply tps_exist_lub. intros α.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite tps_mu_approx_unfold. eapply tps_le_trans; last apply HX.
    apply tps_mono_le, tps_exist_lub. intros [β Hβ]. by apply IH.
  Qed.

  Lemma tps_mu_post `{!TpsMono F} : tps_le tps_mu (F tps_mu).
  Proof.
    apply tps_exist_lub. intros α. rewrite tps_mu_approx_unfold.
    apply tps_mono_le, tps_exist_lub. intros [β ?]. apply (tps_exist_ub tps_mu_approx).
  Qed.

  (** The trace reading implies the least fixpoint of the trace functor. *)
  Lemma tps_mu_tr τ `{!TpsMono F} : tps_tr tps_mu τ → tr_lfp (λ R, tps_tr (F (tps_trp R))) τ.
  Proof.
    assert (Hm : tr_mono (λ R, tps_tr (F (tps_trp R)))).
    { intros R R' HR τ'. by apply tps_mono_tr. }
    intros [α Hα]. revert τ Hα. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros τ Hα. rewrite tps_mu_approx_unfold in Hα. apply tr_lfp_unfold_r; first done.
    eapply tps_mono_tr; last exact Hα. intros τ' [[β Hβ] H']. by apply (IH β).
  Qed.

End mu.

(** ** Guarantees *)
Section rules.
  Context `{!lantanaGS Λ Σ}.

  Lemma temporal_nu_coind (F : tps Λ Σ → tps Λ Σ) `{!TpsMono F} P H :
    tps_le H (F H) → P ⊨ₜ H ⊢ P ⊨ₜ tps_nu F.
  Proof. intros HH. by apply temporal_weaken, tps_nu_coind. Qed.

  (** A formula guarantees [ν F] if it guarantees [F] of its canonical trace property; this
      is how guarded-recursive formulas get fixpoint guarantees. *)
  Lemma temporal_nu_sem (F : tps Λ Σ → tps Λ Σ) `{!TpsMono F} P :
    (⊢ P ⊨ₜ F (tps_sem P)) → ⊢ P ⊨ₜ tps_nu F.
  Proof.
    intros HP. iApply temporal_weaken; [|iApply temporal_sem].
    apply tps_nu_coind. by apply tps_sem_le.
  Qed.

  Lemma temporal_mu_rank (F : tps Λ Σ → tps Λ Σ) `{!TpsMono F} P (H : Ord.t → tps Λ Σ) α :
    (∀ α, tps_le (H α) (F (tps_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    P ⊨ₜ H α ⊢ P ⊨ₜ tps_mu F.
  Proof. intros HH. by apply temporal_weaken, tps_mu_intro. Qed.

End rules.

(** ** Always and until as fixpoints *)
Section ltl.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : tps Λ Σ.

  (** The step-indexed readings decide a position after the step taken there, so the
      bodies are [⊳ ⊚ (G ∧ ○'X)] and [⊳ ⊚ (G2 ∨ (G1 ∧ ○'X))]; on traces these read as
      [G ∧ ○X] and [G2 ∨ (G1 ∧ ○X)]. *)
  Definition F_always G : tps Λ Σ → tps Λ Σ := λ X, tps_later (tps_step (tps_and G (tps_shift X))).
  Definition F_until G1 G2 : tps Λ Σ → tps Λ Σ :=
    λ X, tps_later (tps_step (tps_or G2 (tps_and G1 (tps_shift X)))).
  Global Instance F_always_mono G : TpsMono (F_always G).
  Proof.
    apply (tps_mono_later (λ X, tps_step (tps_and G (tps_shift X)))),
      (tps_mono_step (λ X, tps_and G (tps_shift X))), (tps_mono_and (λ _, G) (λ X, tps_shift X)).
    - apply tps_mono_const.
    - apply (tps_mono_shift (λ X, X)), tps_mono_id.
  Qed.
  Global Instance F_until_mono G1 G2 : TpsMono (F_until G1 G2).
  Proof.
    apply (tps_mono_later (λ X, tps_step (tps_or G2 (tps_and G1 (tps_shift X))))),
      (tps_mono_step (λ X, tps_or G2 (tps_and G1 (tps_shift X)))),
      (tps_mono_or (λ _, G2) (λ X, tps_and G1 (tps_shift X))); first apply tps_mono_const.
    apply (tps_mono_and (λ _, G1) (λ X, tps_shift X)); first apply tps_mono_const.
    apply (tps_mono_shift (λ X, X)), tps_mono_id.
  Qed.

  (** [□ G] is [ν X. ⊳ ⊚ (G ∧ ○'X)], in both directions. *)
  Lemma tps_always_le_nu G : tps_le (tps_always G) (tps_nu (F_always G)).
  Proof.
    apply tps_nu_coind. intros ? τ. rewrite /F_always /= ti_always_unfold /ti_always_pre /ti_and /ti_pure.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". by iDestruct "H" as "[_ [_ $]]".
  Qed.

  Lemma tps_nu_le_always G : tps_le (tps_nu (F_always G)) (tps_always G).
  Proof.
    intros ? τ. rewrite {1}/tps_ti /=. iIntros "[%X [%HX H]]".
    iRevert (τ) "H". iLöb as "IH". iIntros (τ) "H".
    iPoseProof (HX _ τ with "H") as "H". rewrite /F_always. iSimpl in "H".
    rewrite ti_always_unfold /ti_always_pre /ti_and /ti_pure.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". iSplit; first done.
    iDestruct "H" as "[_ H]". by iApply "IH".
  Qed.

  Lemma tps_nu_always_tr G τ : tps_tr (tps_nu (F_always G)) τ ↔ tr_always (tps_tr G) τ.
  Proof.
    rewrite tps_nu_tr. destruct τ as [n τf]. split.
    - intros (R & HR & Hτ).
      assert (Hk : ∀ k, R (n + k, τf)).
      { intros k. induction k as [|k IHk]; first by rewrite Nat.add_0_r.
        destruct (HR _ IHk) as [_ Hnext]. by rewrite Nat.add_succ_r. }
      intros m Hm. replace m with (n + (m - n)) by lia. by destruct (HR _ (Hk (m - n))).
    - intros Hal. exists (tr_always (tps_tr G)). split; last done.
      intros [n' τf'] Hal'. split; first (apply Hal'; lia).
      intros m Hm. apply Hal'. simpl in Hm. lia.
  Qed.

  (** A ranked until. *)
  Program Definition tps_until_at G1 G2 (a : Ord.t) : tps Λ Σ :=
    {| tps_ti _ := ti_until Ord.lt a (tps_ti G1) (tps_ti G2); tps_tr := tps_tr (tps_until G1 G2) |}.
  Next Obligation.
    intros G1 G2 a ? F τ H. eapply (tps_good (tps_until G1 G2)). simpl. rewrite /ti_exist.
    eapply sat_mono; last exact H. iIntros "H". by iExists a.
  Qed.

  (** [G1 𝒰 G2] is below [μ X. ⊳(G2 ∨ (G1 ∧ ○X))]: its measure is a ranking. *)
  Lemma tps_until_le_mu G1 G2 : tps_le (tps_until G1 G2) (tps_mu (F_until G1 G2)).
  Proof.
    eapply tps_le_trans; [|apply tps_exist_lub; intros a; apply (tps_mu_intro _ (tps_until_at G1 G2))].
    - intros ? τ. rewrite /= /ti_exist. iIntros "[%a H]". by iExists a.
    - intros α ? τ. rewrite /F_until /= ti_until_unfold /ti_until_pre /ti_or /ti_and /ti_exist.
      iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
      iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
      iDestruct "H" as "[H|H]"; first by iLeft. iRight.
      iSplit; first by iDestruct "H" as "[$ _]".
      iDestruct "H" as "[_ (%a'& %Hlt& H)]". by iExists (a' ↾ Hlt).
  Qed.

  Lemma tps_mu_until_tr G1 G2 τ :
    tps_tr (tps_mu (F_until G1 G2)) τ → tr_until (tps_tr G1) (tps_tr G2) τ.
  Proof.
    intros H. apply tps_mu_tr in H; last apply _. revert τ H. apply tr_lfp_ind.
    intros [n τf] [HQ|[HP (m & Hm & HQ & HPs)]].
    - exists n. split_and!; [lia|done|lia].
    - exists m. split_and!; [simpl in Hm; lia|done|].
      intros l Hl. destruct (decide (l = n)) as [->|Hne]; first done. apply HPs. simpl. lia.
  Qed.

  (** Beyond LTL: [G] at every even position, [ν X. ⊳ ⊚ (G ∧ ○' ○ X)] (not expressible in LTL). *)
  Definition F_even G : tps Λ Σ → tps Λ Σ :=
    λ X, tps_later (tps_step (tps_and G (tps_shift (tps_next X)))).
  Global Instance F_even_mono G : TpsMono (F_even G).
  Proof.
    apply (tps_mono_later (λ X, tps_step (tps_and G (tps_shift (tps_next X))))),
      (tps_mono_step (λ X, tps_and G (tps_shift (tps_next X)))),
      (tps_mono_and (λ _, G) (λ X, tps_shift (tps_next X))); first apply tps_mono_const.
    apply (tps_mono_shift (λ X, tps_next X)), (tps_mono_next (λ X, X)), tps_mono_id.
  Qed.

  Lemma tps_nu_even_tr G n τf :
    tps_tr (tps_nu (F_even G)) (n, τf) ↔ ∀ k, tps_tr G (n + 2 * k, τf).
  Proof.
    rewrite tps_nu_tr. split.
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

(** ** A recursive formula: the nested invariant guarantees [ν X. □(G ∧ X)] *)
Section recursion.
  Context `{!lantanaGS Λ Σ}.

  Definition F_nest (G : tps Λ Σ) : tps Λ Σ → tps Λ Σ := λ X, tps_always (tps_and G X).
  Global Instance F_nest_mono G : TpsMono (F_nest G).
  Proof.
    apply (tps_mono_always (λ X, tps_and G X)), (tps_mono_and (λ _, G) (λ X, X)).
    - apply tps_mono_const.
    - apply tps_mono_id.
  Qed.

  Lemma nest_temporal_nu N Q (G : tps Λ Σ) : (⊢ Q ⊨ₜ G) → ⊢ nest N Q ⊨ₜ tps_nu (F_nest G).
  Proof.
    intros HQ. apply temporal_nu_sem. rewrite /F_nest.
    iApply (temporal_mono (inv N (Q ∗ nest N Q)) with "[]").
    { iIntros "!> H". by iEval (rewrite nest_unfold) in "H". }
    iApply temporal_always. iApply temporal_sep; [iApply HQ|iApply temporal_sem].
  Qed.

End recursion.
