From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.trace Require Export trace_prop.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties axioms.

(** * Least and greatest fixpoints of trace properties

    For a body [F] monotone in both readings ([TpropMono]): [tprop_nu F], the union of the
    post-fixpoints of [F], and [tprop_mu F], the union of ordinal approximants
    [μ_α := F (∃ β < α, μ_β)]. Always and until are such fixpoints. *)

(* The proof mode must not unfold the connectives, which are records. *)
#[local] Typeclasses Opaque tprop_pure tprop_atomic tprop_and tprop_or tprop_impl tprop_forall tprop_exist
  tprop_always tprop_until tprop_state.

(** ** Trace predicates, the in-logic step, and the next position *)
Section connectives.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : tprop Λ Σ.

  (** Any trace predicate, read in the logic as a pure fact. *)
  Program Definition tprop_trp (R : trProp Λ) : tprop Λ Σ :=
    {| tprop_ti _ τ := ⌜R τ⌝%I; tprop_tr := R |}.
  Next Obligation. intros R ? F τ H. by apply sat_elim in H. Qed.

  (** [⊳ G]: [G] after one step of the logic; at the level of traces, just [G]. *)
  Program Definition tprop_later G : tprop Λ Σ :=
    {| tprop_ti _ τ := (|={⊤,∅}=> ▷ |={∅,⊤}=> tprop_ti G τ)%I; tprop_tr := tprop_tr G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_later, sat_fupd in H. by eapply tprop_good. Qed.

  (** [○ G]: [G] at the next position. *)
  Program Definition tprop_next G : tprop Λ Σ :=
    {| tprop_ti _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> tprop_ti G (trace_next τ)))%I;
       tprop_tr τ := tprop_tr G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply tprop_good. Qed.

  (** [⊚ G]: [G] after the step taken at the current position. In the logic this is the
      step's credits and mask change; at the level of traces it is just [G]. *)
  Program Definition tprop_step G : tprop Λ Σ :=
    {| tprop_ti _ τ := (|={⊤,∅}=> ALC (|={∅,⊤}=> tprop_ti G τ))%I; tprop_tr := tprop_tr G |}.
  Next Obligation. intros G ? F τ H. apply sat_fupd, sat_ALC, sat_fupd in H. by eapply tprop_good. Qed.

  (** [○' G]: [G] read at the next position, with no modality; [○ G] is [⊚ ○' G]. *)
  Program Definition tprop_shift G : tprop Λ Σ :=
    {| tprop_ti _ τ := tprop_ti G (trace_next τ); tprop_tr τ := tprop_tr G (trace_next τ) |}.
  Next Obligation. intros G ? F τ H. by eapply tprop_good. Qed.

  Lemma tprop_later_mono G G' : tprop_le G G' → tprop_le (tprop_later G) (tprop_later G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro.
    by iApply HG.
  Qed.
  Lemma tprop_next_mono G G' : tprop_le G G' → tprop_le (tprop_next G) (tprop_next G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma tprop_step_mono G G' : tprop_le G G' → tprop_le (tprop_step G) (tprop_step G').
  Proof.
    intros HG ? τ. rewrite /=. iIntros "H". iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro. by iApply HG.
  Qed.
  Lemma tprop_shift_mono G G' : tprop_le G G' → tprop_le (tprop_shift G) (tprop_shift G').
  Proof. intros HG ? τ. rewrite /=. by iApply HG. Qed.

  Lemma tprop_exist_lub {X} `{!TypeExistentialProperty X ordI} (G : X → tprop Λ Σ) G' :
    (∀ x, tprop_le (G x) G') → tprop_le (tprop_exist G) G'.
  Proof. intros HG ? τ. rewrite /= /ti_exist. iIntros "[%x H]". by iApply HG. Qed.
  Lemma tprop_exist_ub {X} `{!TypeExistentialProperty X ordI} (G : X → tprop Λ Σ) x :
    tprop_le (G x) (tprop_exist G).
  Proof. intros ? τ. rewrite /= /ti_exist. iIntros "H". by iExists x. Qed.

End connectives.

Global Typeclasses Opaque tprop_trp tprop_later tprop_next.

(** ** Monotone bodies *)
Class TpropMono {Λ Σ} (F : tprop Λ Σ → tprop Λ Σ) : Prop := {
  tprop_mono_le X Y : tprop_le X Y → tprop_le (F X) (F Y);
  tprop_mono_tr X Y : (∀ τ, tprop_tr X τ → tprop_tr Y τ) → ∀ τ, tprop_tr (F X) τ → tprop_tr (F Y) τ;
}.
Global Hint Mode TpropMono - - ! : typeclass_instances.

Section mono_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : tprop Λ Σ → tprop Λ Σ.

  Global Instance tprop_mono_id : TpropMono (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. split; auto. Qed.
  Global Instance tprop_mono_const G : TpropMono (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. split; auto using tprop_le_refl. Qed.
  Global Instance tprop_mono_and F1 F2 :
    TpropMono F1 → TpropMono F2 → TpropMono (λ X, tprop_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply tprop_and_mono; by apply tprop_mono_le.
    - intros X Y HXY τ [??]. split; [by apply (tprop_mono_tr (F:=F1) X Y)|by apply (tprop_mono_tr (F:=F2) X Y)].
  Qed.
  Global Instance tprop_mono_or F1 F2 :
    TpropMono F1 → TpropMono F2 → TpropMono (λ X, tprop_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply tprop_or_mono; by apply tprop_mono_le.
    - intros X Y HXY τ [?|?]; [left; by apply (tprop_mono_tr (F:=F1) X Y)|right; by apply (tprop_mono_tr (F:=F2) X Y)].
  Qed.
  Global Instance tprop_mono_impl A F : TpropMono F → TpropMono (λ X, tprop_impl A (F X)).
  Proof.
    intros HF. split.
    - intros. apply tprop_impl_mono; [done|by apply tprop_mono_le].
    - intros X Y HXY τ H HA. apply (tprop_mono_tr (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance tprop_mono_forall {A} (F : A → tprop Λ Σ → tprop Λ Σ) :
    (∀ a, TpropMono (F a)) → TpropMono (λ X, tprop_forall (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply tprop_forall_mono. intros a. by apply tprop_mono_le.
    - intros X Y HXY τ H a. apply (tprop_mono_tr (F:=F a) X Y); [done|apply H].
  Qed.
  Global Instance tprop_mono_exist {A} `{!TypeExistentialProperty A ordI} (F : A → tprop Λ Σ → tprop Λ Σ) :
    (∀ a, TpropMono (F a)) → TpropMono (λ X, tprop_exist (λ a, F a X)).
  Proof.
    intros HF. split.
    - intros. apply tprop_exist_mono. intros a. by apply tprop_mono_le.
    - intros X Y HXY τ [a H]. exists a. by apply (tprop_mono_tr (F:=F a) X Y).
  Qed.
  Global Instance tprop_mono_later F : TpropMono F → TpropMono (λ X, tprop_later (F X)).
  Proof.
    intros HF. split.
    - intros. apply tprop_later_mono. by apply tprop_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (tprop_mono_tr (F:=F) X Y).
  Qed.
  Global Instance tprop_mono_next F : TpropMono F → TpropMono (λ X, tprop_next (F X)).
  Proof.
    intros HF. split.
    - intros. apply tprop_next_mono. by apply tprop_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (tprop_mono_tr (F:=F) X Y).
  Qed.
  Global Instance tprop_mono_step F : TpropMono F → TpropMono (λ X, tprop_step (F X)).
  Proof.
    intros HF. split.
    - intros. apply tprop_step_mono. by apply tprop_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (tprop_mono_tr (F:=F) X Y).
  Qed.
  Global Instance tprop_mono_shift F : TpropMono F → TpropMono (λ X, tprop_shift (F X)).
  Proof.
    intros HF. split.
    - intros. apply tprop_shift_mono. by apply tprop_mono_le.
    - intros X Y HXY τ H. simpl in *. by apply (tprop_mono_tr (F:=F) X Y).
  Qed.
  Global Instance tprop_mono_always F : TpropMono F → TpropMono (λ X, tprop_always (F X)).
  Proof.
    intros HF. split.
    - intros. apply tprop_always_mono. by apply tprop_mono_le.
    - intros X Y HXY [n τf] H m Hm. apply (tprop_mono_tr (F:=F) X Y); [done|by apply H].
  Qed.
  Global Instance tprop_mono_until F1 F2 :
    TpropMono F1 → TpropMono F2 → TpropMono (λ X, tprop_until (F1 X) (F2 X)).
  Proof.
    intros H1 H2. split.
    - intros. apply tprop_until_mono; by apply tprop_mono_le.
    - intros X Y HXY [n τf] (m & Hm & HQ & HP). exists m. split_and!; [done| |].
      + by apply (tprop_mono_tr (F:=F2) X Y).
      + intros l Hl. apply (tprop_mono_tr (F:=F1) X Y); [done|by apply HP].
  Qed.

End mono_instances.

(** ** Continuous bodies

    [F] commutes, in the logic, with unions of increasing chains indexed by ordinals. Guarded
    bodies are not continuous: the step index ranges beyond [Ord.t], so [▷ ∃ α, X α] does
    not give [∃ α, ▷ X α]. *)
Class TpropCont {Λ Σ} (F : tprop Λ Σ → tprop Λ Σ) : Prop :=
  tprop_cont (X : Ord.t → tprop Λ Σ) :
    (∀ α β, Ord.le α β → tprop_le (X α) (X β)) →
    tprop_le (F (tprop_exist X)) (tprop_exist (λ α, F (X α))).
Global Hint Mode TpropCont - - ! : typeclass_instances.

Section cont_instances.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types F : tprop Λ Σ → tprop Λ Σ.

  Global Instance tprop_cont_id : TpropCont (Λ:=Λ) (Σ:=Σ) (λ X, X).
  Proof. intros X _. apply tprop_le_refl. Qed.
  Global Instance tprop_cont_const G : TpropCont (Λ:=Λ) (Σ:=Σ) (λ _, G).
  Proof. intros X _ ? τ. rewrite /= /ti_exist. iIntros "H". by iExists Ord.O. Qed.
  Global Instance tprop_cont_and F1 F2 `{!TpropMono F1, !TpropMono F2} :
    TpropCont F1 → TpropCont F2 → TpropCont (λ X, tprop_and (F1 X) (F2 X)).
  Proof.
    intros H1 H2 X HX ? τ. rewrite /= /ti_and (H1 X HX _ τ) (H2 X HX _ τ) /= /ti_exist.
    rewrite bi.and_exist_r. iIntros "[%α H]". rewrite bi.and_exist_l. iDestruct "H" as (β) "H".
    iExists (Ord.union α β). iSplit.
    - iDestruct "H" as "[H _]". iApply (tprop_mono_le (X α)); [apply HX, Ord.union_l|done].
    - iDestruct "H" as "[_ H]". iApply (tprop_mono_le (X β)); [apply HX, Ord.union_r|done].
  Qed.
  Global Instance tprop_cont_or F1 F2 :
    TpropCont F1 → TpropCont F2 → TpropCont (λ X, tprop_or (F1 X) (F2 X)).
  Proof.
    intros H1 H2 X HX ? τ. rewrite /= /ti_or (H1 X HX _ τ) (H2 X HX _ τ) /= /ti_exist.
    iIntros "[[%α H]|[%α H]]"; iExists α; [by iLeft|by iRight].
  Qed.
  Global Instance tprop_cont_impl A F : TpropCont F → TpropCont (λ X, tprop_impl A (F X)).
  Proof.
    intros HF X HX ? τ. rewrite /= /ti_impl (HF X HX _ τ) /= /ti_exist. iIntros "H".
    destruct (classic (tprop_tr A τ)) as [HA|HA].
    - iDestruct ("H" $! HA) as (α) "H". iExists α. by iIntros "_".
    - iExists Ord.O. by iIntros (?).
  Qed.
  Global Instance tprop_cont_exist {A} `{!TypeExistentialProperty A ordI} (F : A → tprop Λ Σ → tprop Λ Σ) :
    (∀ a, TpropCont (F a)) → TpropCont (λ X, tprop_exist (λ a, F a X)).
  Proof.
    intros HF X HX ? τ. rewrite /= /ti_exist. iIntros "[%a H]".
    rewrite (HF a X HX _ τ) /= /ti_exist. iDestruct "H" as (α) "H". iExists α, a. done.
  Qed.
  Global Instance tprop_cont_shift F : TpropCont F → TpropCont (λ X, tprop_shift (F X)).
  Proof. intros HF X HX ? τ. rewrite /= (HF X HX _ (trace_next τ)) /= /ti_exist. done. Qed.

End cont_instances.

(** ** Greatest fixpoints *)
Section nu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : tprop Λ Σ.

  Program Definition tprop_nu (F : tprop Λ Σ → tprop Λ Σ) `{!TpropMono F} : tprop Λ Σ :=
    {| tprop_ti H τ := (∃ X : tprop Λ Σ, ⌜tprop_le X (F X)⌝ ∧ @tprop_ti _ _ X H τ)%I;
       tprop_tr := tr_gfp (λ R, tprop_tr (F (tprop_trp R))) |}.
  Next Obligation.
    intros F HF H F0 τ Hsat.
    pose (I := λ (H' : temporalGS Λ Σ) (τ' : trace Λ),
                 (∃ X : tprop Λ Σ, ⌜tprop_le X (F X)⌝ ∧ @tprop_ti _ _ X H' τ')%I).
    (* The traces at which the in-logic reading is satisfiable, for some instance. *)
    pose (S := λ τ', ∃ (H' : temporalGS Λ Σ) (F' : iProp Σ), iProp_sat_lc_at_frame F' ⊤ (I H' τ')).
    assert (HS : ∀ (H' : temporalGS Λ Σ) (F' : iProp Σ) τ',
               iProp_sat_lc_at_frame F' ⊤ (I H' τ') → S τ').
    { intros H' F' τ' Hs. by exists H', F'. }
    pose (N := Tprop I S HS).
    (* [S] is a post-fixpoint of the trace functor. *)
    exists S. split; last by exists H, F0.
    intros τ' (H' & F' & Hs).
    assert (HXN : ∀ X, tprop_le X (F X) → tprop_le X N).
    { intros X HX ? τ''. rewrite /=. iIntros "HX". iExists X. by iFrame. }
    assert (HIN : I H' τ' ⊢ @tprop_ti _ _ (F N) H' τ').
    { iIntros "[%X [%HX HXt]]". iApply (tprop_mono_le X N (HXN X HX)). by iApply HX. }
    apply (sat_mono _ _ HIN) in Hs. apply (tprop_good (F N)) in Hs.
    eapply (tprop_mono_tr N (tprop_trp S)); last exact Hs. done.
  Qed.

  Context (F : tprop Λ Σ → tprop Λ Σ) `{!TpropMono F}.

  Lemma tprop_nu_coind X : tprop_le X (F X) → tprop_le X (tprop_nu F).
  Proof. intros HX ? τ. rewrite /=. iIntros "H". iExists X. by iFrame. Qed.

  Lemma tprop_nu_unfold_l : tprop_le (tprop_nu F) (F (tprop_nu F)).
  Proof.
    intros ? τ. rewrite {1}/tprop_ti /=. iIntros "[%X [%HX H]]".
    iApply (tprop_mono_le X (tprop_nu F)); first by apply tprop_nu_coind. by iApply HX.
  Qed.

  Lemma tprop_nu_unfold_r : tprop_le (F (tprop_nu F)) (tprop_nu F).
  Proof. apply tprop_nu_coind, tprop_mono_le, tprop_nu_unfold_l. Qed.

  Lemma tprop_nu_tr τ : tprop_tr (tprop_nu F) τ ↔ tr_gfp (λ R, tprop_tr (F (tprop_trp R))) τ.
  Proof. done. Qed.

End nu.

(** ** Least fixpoints, with ordinal approximants

    The ordinal is the measure a least fixpoint needs in a step-indexed logic: without it, a
    guarded body has a unique fixpoint, and [μ] would be [ν]. *)
Section mu.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G X : tprop Λ Σ.
  Context (F : tprop Λ Σ → tprop Λ Σ).

  Fixpoint tprop_mu_rec (α : Ord.t) (ACC : Acc Ord.lt α) {struct ACC} : tprop Λ Σ :=
    F (tprop_exist (λ b : {β : Ord.t | Ord.lt β α},
                    tprop_mu_rec (proj1_sig b) (Acc_inv ACC (proj2_sig b)))).

  (** The approximant [μ_α]. *)
  Definition tprop_mu_approx (α : Ord.t) : tprop Λ Σ := tprop_mu_rec α (Ord.lt_well_founded α).
  Definition tprop_mu : tprop Λ Σ := tprop_exist tprop_mu_approx.

  Lemma tprop_mu_rec_irrel α A1 A2 : tprop_mu_rec α A1 = tprop_mu_rec α A2.
  Proof.
    revert A1 A2. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros [A1] [A2]. simpl. f_equal. f_equal. apply func_ext. intros [β Hβ]. by apply IH.
  Qed.

  Lemma tprop_mu_approx_unfold α :
    tprop_mu_approx α = F (tprop_exist (λ b : {β : Ord.t | Ord.lt β α}, tprop_mu_approx (proj1_sig b))).
  Proof.
    rewrite /tprop_mu_approx. generalize (Ord.lt_well_founded α) as ACC. intros [A]. simpl.
    f_equal. f_equal. apply func_ext. intros b. apply tprop_mu_rec_irrel.
  Qed.

  (** Introduction with a ranking: [H α] unfolds to [F] of smaller ranks. *)
  Lemma tprop_mu_rank `{!TpropMono F} (H : Ord.t → tprop Λ Σ) :
    (∀ α, tprop_le (H α) (F (tprop_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    ∀ α, tprop_le (H α) (tprop_mu_approx α).
  Proof.
    intros HH α. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite tprop_mu_approx_unfold. eapply tprop_le_trans; first apply HH.
    apply tprop_mono_le, tprop_exist_mono. intros [β Hβ]. by apply IH.
  Qed.

  Lemma tprop_mu_intro `{!TpropMono F} (H : Ord.t → tprop Λ Σ) α :
    (∀ α, tprop_le (H α) (F (tprop_exist (λ b : {β : Ord.t | Ord.lt β α}, H (proj1_sig b))))) →
    tprop_le (H α) tprop_mu.
  Proof.
    intros HH. eapply tprop_le_trans; first by apply tprop_mu_rank. apply (tprop_exist_ub tprop_mu_approx).
  Qed.

  (** Induction: [tprop_mu F] is below every pre-fixpoint. *)
  Lemma tprop_mu_ind X `{!TpropMono F} : tprop_le (F X) X → tprop_le tprop_mu X.
  Proof.
    intros HX. apply tprop_exist_lub. intros α.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    rewrite tprop_mu_approx_unfold. eapply tprop_le_trans; last apply HX.
    apply tprop_mono_le, tprop_exist_lub. intros [β Hβ]. by apply IH.
  Qed.

  Lemma tprop_mu_post `{!TpropMono F} : tprop_le tprop_mu (F tprop_mu).
  Proof.
    apply tprop_exist_lub. intros α. rewrite tprop_mu_approx_unfold.
    apply tprop_mono_le, tprop_exist_lub. intros [β ?]. apply (tprop_exist_ub tprop_mu_approx).
  Qed.

  Lemma tprop_mu_approx_mono `{!TpropMono F} α β :
    Ord.le α β → tprop_le (tprop_mu_approx α) (tprop_mu_approx β).
  Proof.
    intros Hle. rewrite !tprop_mu_approx_unfold. apply tprop_mono_le, tprop_exist_lub. intros [γ Hγ].
    apply (tprop_exist_ub (λ b : {γ | Ord.lt γ β}, tprop_mu_approx (proj1_sig b))
             (γ ↾ Ord.lt_le_lt Hγ Hle)).
  Qed.

  (** The fold, for a continuous body; with [tprop_mu_post], [tprop_mu F] is then a fixpoint.
      A guarded body has no fold ([tprop_mu_unfold_r_guarded]). *)
  Lemma tprop_mu_unfold_r `{!TpropMono F, !TpropCont F} : tprop_le (F tprop_mu) tprop_mu.
  Proof.
    eapply tprop_le_trans; first (apply (tprop_cont tprop_mu_approx); intros; by apply tprop_mu_approx_mono).
    apply tprop_exist_lub. intros α. eapply tprop_le_trans; last apply (tprop_exist_ub tprop_mu_approx (Ord.S α)).
    rewrite (tprop_mu_approx_unfold (Ord.S α)). apply tprop_mono_le.
    apply (tprop_exist_ub (λ b : {β | Ord.lt β (Ord.S α)}, tprop_mu_approx (proj1_sig b)) (α ↾ Ord.S_lt α)).
  Qed.

  Lemma tprop_mu_tr τ `{!TpropMono F} : tprop_tr tprop_mu τ → tr_lfp (λ R, tprop_tr (F (tprop_trp R))) τ.
  Proof.
    assert (Hm : tr_mono (λ R, tprop_tr (F (tprop_trp R)))).
    { intros R R' HR τ'. by apply tprop_mono_tr. }
    intros [α Hα]. revert τ Hα. induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros τ Hα. rewrite tprop_mu_approx_unfold in Hα. apply tr_lfp_unfold_r; first done.
    eapply tprop_mono_tr; last exact Hα. intros τ' [[β Hβ] H']. by apply (IH β).
  Qed.

  (** The trace reading is a pre-fixpoint of the trace functor: the join of the ranks of its
      traces bounds them all. *)
  Lemma tprop_mu_tr_pre `{!TpropMono F} τ :
    tprop_tr (F (tprop_trp (tprop_tr tprop_mu))) τ → tprop_tr tprop_mu τ.
  Proof.
    intros Hτ.
    destruct (choice (λ (τ' : trace Λ) (α : Ord.t), tprop_tr tprop_mu τ' → tprop_tr (tprop_mu_approx α) τ'))
      as [f Hf].
    { intros τ'. destruct (classic (tprop_tr tprop_mu τ')) as [[α Hα]|Hn]; [by exists α|by exists Ord.O]. }
    exists (Ord.S (Ord.join f)). rewrite tprop_mu_approx_unfold.
    eapply tprop_mono_tr; last exact Hτ. intros τ' Hτ'.
    exists (f τ' ↾ Ord.le_lt_lt (Ord.join_upperbound f τ') (Ord.S_lt _)). simpl. by apply Hf.
  Qed.

  Lemma tprop_mu_tr_lfp `{!TpropMono F} τ : tr_lfp (λ R, tprop_tr (F (tprop_trp R))) τ → tprop_tr tprop_mu τ.
  Proof. intros H. apply H. intros τ'. apply tprop_mu_tr_pre. Qed.

  Lemma tprop_mu_tr_iff `{!TpropMono F} τ : tprop_tr tprop_mu τ ↔ tr_lfp (λ R, tprop_tr (F (tprop_trp R))) τ.
  Proof. split; [by apply tprop_mu_tr|apply tprop_mu_tr_lfp]. Qed.

  (** On traces, [tprop_mu F] is a fixpoint of [F], for any monotone body. *)
  Lemma tprop_mu_tr_unfold_l `{!TpropMono F} τ : tprop_tr tprop_mu τ → tprop_tr (F tprop_mu) τ.
  Proof.
    intros [α Hα]. rewrite tprop_mu_approx_unfold in Hα. eapply tprop_mono_tr; last exact Hα.
    intros τ' [b H]. by exists (proj1_sig b).
  Qed.
  Lemma tprop_mu_tr_unfold_r `{!TpropMono F} τ : tprop_tr (F tprop_mu) τ → tprop_tr tprop_mu τ.
  Proof. intros H. apply tprop_mu_tr_pre. by eapply tprop_mono_tr; last exact H. Qed.

End mu.

(** ** Always and until as fixpoints *)
Section ltl.
  Context {Λ : language} {Σ : gFunctors}.
  Implicit Types G : tprop Λ Σ.

  (** The step-indexed readings decide a position after the step taken there, so the
      bodies are [⊳ ⊚ (G ∧ ○'X)] and [⊳ ⊚ (G2 ∨ (G1 ∧ ○'X))]; on traces these read as
      [G ∧ ○X] and [G2 ∨ (G1 ∧ ○X)]. *)
  Definition F_always G : tprop Λ Σ → tprop Λ Σ := λ X, tprop_later (tprop_step (tprop_and G (tprop_shift X))).
  Definition F_until G1 G2 : tprop Λ Σ → tprop Λ Σ :=
    λ X, tprop_later (tprop_step (tprop_or G2 (tprop_and G1 (tprop_shift X)))).
  Global Instance F_always_mono G : TpropMono (F_always G).
  Proof.
    apply (tprop_mono_later (λ X, tprop_step (tprop_and G (tprop_shift X)))),
      (tprop_mono_step (λ X, tprop_and G (tprop_shift X))), (tprop_mono_and (λ _, G) (λ X, tprop_shift X)).
    - apply tprop_mono_const.
    - apply (tprop_mono_shift (λ X, X)), tprop_mono_id.
  Qed.
  Global Instance F_until_mono G1 G2 : TpropMono (F_until G1 G2).
  Proof.
    apply (tprop_mono_later (λ X, tprop_step (tprop_or G2 (tprop_and G1 (tprop_shift X))))),
      (tprop_mono_step (λ X, tprop_or G2 (tprop_and G1 (tprop_shift X)))),
      (tprop_mono_or (λ _, G2) (λ X, tprop_and G1 (tprop_shift X))); first apply tprop_mono_const.
    apply (tprop_mono_and (λ _, G1) (λ X, tprop_shift X)); first apply tprop_mono_const.
    apply (tprop_mono_shift (λ X, X)), tprop_mono_id.
  Qed.

  (** [□ G] is [ν X. ⊳ ⊚ (G ∧ ○'X)], in both directions. *)
  Lemma tprop_always_le_nu G : tprop_le (tprop_always G) (tprop_nu (F_always G)).
  Proof.
    apply tprop_nu_coind. intros ? τ. rewrite /F_always /= ti_always_unfold /ti_always_pre /ti_and /ti_pure.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". by iDestruct "H" as "[_ [_ $]]".
  Qed.

  Lemma tprop_nu_le_always G : tprop_le (tprop_nu (F_always G)) (tprop_always G).
  Proof.
    intros ? τ. rewrite {1}/tprop_ti /=. iIntros "[%X [%HX H]]".
    iRevert (τ) "H". iLöb as "IH". iIntros (τ) "H".
    iPoseProof (HX _ τ with "H") as "H". rewrite /F_always. iSimpl in "H".
    rewrite ti_always_unfold /ti_always_pre /ti_and /ti_pure.
    iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iSplit; first by iDestruct "H" as "[$ _]". iSplit; first done.
    iDestruct "H" as "[_ H]". by iApply "IH".
  Qed.

  Lemma tprop_nu_always_tr G τ : tprop_tr (tprop_nu (F_always G)) τ ↔ tr_always (tprop_tr G) τ.
  Proof.
    rewrite tprop_nu_tr. destruct τ as [n τf]. split.
    - intros (R & HR & Hτ).
      assert (Hk : ∀ k, R (n + k, τf)).
      { intros k. induction k as [|k IHk]; first by rewrite Nat.add_0_r.
        destruct (HR _ IHk) as [_ Hnext]. by rewrite Nat.add_succ_r. }
      intros m Hm. replace m with (n + (m - n)) by lia. by destruct (HR _ (Hk (m - n))).
    - intros Hal. exists (tr_always (tprop_tr G)). split; last done.
      intros [n' τf'] Hal'. split; first (apply Hal'; lia).
      intros m Hm. apply Hal'. simpl in Hm. lia.
  Qed.

  (** A ranked until. *)
  Program Definition tprop_until_at G1 G2 (a : Ord.t) : tprop Λ Σ :=
    {| tprop_ti _ := ti_until Ord.lt a (tprop_ti G1) (tprop_ti G2); tprop_tr := tprop_tr (tprop_until G1 G2) |}.
  Next Obligation.
    intros G1 G2 a ? F τ H. eapply (tprop_good (tprop_until G1 G2)). simpl. rewrite /ti_exist.
    eapply sat_mono; last exact H. iIntros "H". by iExists a.
  Qed.

  (** [G1 𝒰 G2] is below [μ X. ⊳(G2 ∨ (G1 ∧ ○X))]: its measure is a ranking. *)
  Lemma tprop_until_le_mu G1 G2 : tprop_le (tprop_until G1 G2) (tprop_mu (F_until G1 G2)).
  Proof.
    eapply tprop_le_trans; [|apply tprop_exist_lub; intros a; apply (tprop_mu_intro _ (tprop_until_at G1 G2))].
    - intros ? τ. rewrite /= /ti_exist. iIntros "[%a H]". by iExists a.
    - intros α ? τ. rewrite /F_until /= ti_until_unfold /ti_until_pre /ti_or /ti_and /ti_exist.
      iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
      iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
      iDestruct "H" as "[H|H]"; first by iLeft. iRight.
      iSplit; first by iDestruct "H" as "[$ _]".
      iDestruct "H" as "[_ (%a'& %Hlt& H)]". by iExists (a' ↾ Hlt).
  Qed.

  Lemma tprop_mu_until_tr G1 G2 τ :
    tprop_tr (tprop_mu (F_until G1 G2)) τ → tr_until (tprop_tr G1) (tprop_tr G2) τ.
  Proof.
    intros H. apply tprop_mu_tr in H; last apply _. revert τ H. apply tr_lfp_ind.
    intros [n τf] [HQ|[HP (m & Hm & HQ & HPs)]].
    - exists n. split_and!; [lia|done|lia].
    - exists m. split_and!; [simpl in Hm; lia|done|].
      intros l Hl. destruct (decide (l = n)) as [->|Hne]; first done. apply HPs. simpl. lia.
  Qed.

  (** Conversely, [μ X. ⊳(G2 ∨ (G1 ∧ ○X))] is below [G1 𝒰 G2]: the approximant [μ_α] is
      the until ranked by [α]. *)
  Lemma tprop_mu_approx_le_until G1 G2 α :
    tprop_le (tprop_mu_approx (F_until G1 G2) α) (tprop_until_at G1 G2 α).
  Proof.
    induction α as [α IH] using (well_founded_ind Ord.lt_well_founded).
    intros ? τ. rewrite tprop_mu_approx_unfold /F_until /= ti_until_unfold /ti_until_pre /ti_or /ti_and /ti_exist.
    iIntros "H". iMod "H". iModIntro. iNext. iMod "H". iModIntro. iMod "H". iModIntro.
    iApply (ALC_wand with "[] H"). iIntros "H". iMod "H". iModIntro.
    iDestruct "H" as "[H|H]"; first by iLeft. iRight.
    iSplit; first by iDestruct "H" as "[$ _]".
    iDestruct "H" as "[_ [%b H]]". destruct b as [β Hβ]. iExists β. iSplit; first done.
    by iApply (IH β Hβ).
  Qed.

  Lemma tprop_mu_le_until G1 G2 : tprop_le (tprop_mu (F_until G1 G2)) (tprop_until G1 G2).
  Proof.
    apply tprop_exist_lub. intros α. eapply tprop_le_trans; first apply tprop_mu_approx_le_until.
    intros ? τ. rewrite /= /ti_exist. iIntros "H". by iExists α.
  Qed.

  Lemma tprop_mu_until_tr_iff G1 G2 τ :
    tprop_tr (tprop_mu (F_until G1 G2)) τ ↔ tr_until (tprop_tr G1) (tprop_tr G2) τ.
  Proof.
    split; first apply tprop_mu_until_tr. intros Hu. apply tprop_mu_tr_lfp; first apply _.
    intros R HR. destruct τ as [n τf]. destruct Hu as (m & Hnm & HQ & HP).
    (* the until is below every pre-fixpoint, by the distance to the right formula *)
    assert (∀ d n', m - n' = d → n' ≤ m → (∀ l, n' ≤ l < m → tprop_tr G1 (l, τf)) → R (n', τf)) as Hd.
    { induction d as [|d IHd]; intros n' Hd Hn' HP'; apply HR; rewrite /F_until /=.
      - left. by assert (m = n') as <- by lia.
      - right. split; first (apply HP'; lia).
        apply IHd; [simpl; lia|simpl; lia|]. intros l Hl. apply HP'. simpl in Hl. lia. }
    apply (Hd (m - n)); [done|done|]. intros l Hl. apply HP. lia.
  Qed.

  (** Beyond LTL: [G] at every even position, [ν X. ⊳ ⊚ (G ∧ ○' ○ X)] (not expressible in LTL). *)
  Definition F_even G : tprop Λ Σ → tprop Λ Σ :=
    λ X, tprop_later (tprop_step (tprop_and G (tprop_shift (tprop_next X)))).
  Global Instance F_even_mono G : TpropMono (F_even G).
  Proof.
    apply (tprop_mono_later (λ X, tprop_step (tprop_and G (tprop_shift (tprop_next X))))),
      (tprop_mono_step (λ X, tprop_and G (tprop_shift (tprop_next X)))),
      (tprop_mono_and (λ _, G) (λ X, tprop_shift (tprop_next X))); first apply tprop_mono_const.
    apply (tprop_mono_shift (λ X, tprop_next X)), (tprop_mono_next (λ X, X)), tprop_mono_id.
  Qed.

  Lemma tprop_nu_even_tr G n τf :
    tprop_tr (tprop_nu (F_even G)) (n, τf) ↔ ∀ k, tprop_tr G (n + 2 * k, τf).
  Proof.
    rewrite tprop_nu_tr. split.
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

  Lemma tprop_guarded_prefix_valid (M : tprop Λ Σ) :
    tprop_le (F_until tprop_true (tprop_pure False) M) M → ∀ (H : temporalGS Λ Σ) τ, ⊢ @tprop_ti _ _ M H τ.
  Proof.
    intros HM H. cut (⊢ ∀ τ, @tprop_ti _ _ M H τ)%I.
    { intros HM' τ. iApply HM'. }
    iLöb as "IH". iIntros (τ). iApply HM. rewrite /F_until /= /ti_or /ti_and /ti_pure.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext. iMod "Hclose" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iApply ALC_intro. iMod "Hclose" as "_".
    iModIntro. iRight. iSplit; first done. iApply "IH".
  Qed.

  (** The model: the instance is allocated as in the adequacy (adequacy_temporal.v). *)
  Lemma tprop_guarded_prefix_tr `{!mupdGpreS Σ}
      `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
      (M : tprop Λ Σ) τ :
    tprop_le (F_until tprop_true (tprop_pure False) M) M → tprop_tr M τ.
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
    apply (tprop_good M (temporalGS0:=Htemp) emp).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono; last exact Hsat. iIntros "($& $& $)". iApply (tprop_guarded_prefix_valid M HM Htemp).
  Qed.

  Lemma tprop_mu_unfold_r_guarded `{!mupdGpreS Σ}
      `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
      (τ : trace Λ) :
    ¬ tprop_le (Λ:=Λ) (Σ:=Σ) (F_until tprop_true (tprop_pure False) (tprop_mu (F_until tprop_true (tprop_pure False))))
             (tprop_mu (F_until tprop_true (tprop_pure False))).
  Proof.
    intros Hfold. apply (tprop_guarded_prefix_tr _ τ), tprop_mu_until_tr in Hfold.
    destruct τ as [n τf]. by destruct Hfold as (m & _ & [] & _).
  Qed.

End no_fold.
