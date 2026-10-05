(** Languages based on evaluation contexts ([ectxLanguage]) and the [language] each gives. *)
From iris.prelude Require Export prelude.
From lantana.program_logic Require Import language.
From iris.prelude Require Import options.

(** TAKE CARE: an [ectxLanguage] canonical structure needs a matching [language] canonical
    structure, built with [LanguageOfEctx] (end of this file). *)

Section ectx_language_mixin.
  Context {expr val ectx state observation state_pred : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (base_step : thread_id → expr → state → thread_ids → list observation →
                       expr → state → gmap thread_id expr → Prop).
  Context (state_sat : state → gmap thread_id expr → state_pred → Prop).

  Record EctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_base_stuck i e1 σ1 Θ κ e2 σ2 efs :
      base_step i e1 σ1 Θ κ e2 σ2 efs → to_val e1 = None;
    mixin_fork_thread_ids i e1 σ1 Θ κ e2 σ2 efs :
      base_step i e1 σ1 Θ κ e2 σ2 efs → Θ ## dom efs;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);

    (** A base redex in [fill K' e1'], with [e1'] not a value, lies inside [e1']. Hence
        there is at most one base redex ([base_redex_unique]). *)
    mixin_step_by_val i K' K_redex e1' e1_redex σ1 Θ κ e2 σ2 efs :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      base_step i e1_redex σ1 Θ κ e2 σ2 efs →
      ∃ K'', K_redex = comp_ectx K' K'';

    (** Wrapping a non-value in a context adds no base redex positions. *)
    mixin_base_ctx_step_val i K e σ1 Θ κ e2 σ2 efs :
      base_step i (fill K e) σ1 Θ κ e2 σ2 efs → is_Some (to_val e) ∨ K = empty_ectx;
  }.
End ectx_language_mixin.

Structure ectxLanguage := EctxLanguage {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;
  observation : Type;
  state_pred : Type;

  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  base_step : thread_id → expr → state → thread_ids → list observation →
              expr → state → gmap thread_id expr → Prop;
  state_sat : state → gmap thread_id expr → state_pred → Prop;

  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill base_step
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments EctxLanguage {_ _ _ _ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments empty_ectx {_}.
Global Arguments comp_ectx {_} _ _.
Global Arguments fill {_} _ _.
Global Arguments base_step {_} _ _ _ _ _ _ _ _.
Global Arguments state_sat {_} _ _ _.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  Lemma val_base_stuck i e1 σ1 Θ κ e2 σ2 efs : base_step i e1 σ1 Θ κ e2 σ2 efs → to_val e1 = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fork_thread_ids i e1 σ1 Θ κ e2 σ2 efs : base_step i e1 σ1 Θ κ e2 σ2 efs → Θ ## dom efs.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val i K' K_redex e1' e1_redex σ1 Θ κ e2 σ2 efs :
    fill K' e1' = fill K_redex e1_redex →
    to_val e1' = None →
    base_step i e1_redex σ1 Θ κ e2 σ2 efs →
    ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply ectx_language_mixin. Qed.
  Lemma base_ctx_step_val i K e σ1 Θ κ e2 σ2 efs :
    base_step i (fill K e) σ1 Θ κ e2 σ2 efs → is_Some (to_val e) ∨ K = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.

  Definition base_reducible i (e : expr Λ) (σ : state Λ) Θ :=
    ∃ κ e' σ' efs, base_step i e σ Θ κ e' σ' efs.
  Definition base_reducible_no_obs i (e : expr Λ) (σ : state Λ) Θ :=
    ∃ e' σ' efs, base_step i e σ Θ [] e' σ' efs.
  Definition base_irreducible i (e : expr Λ) (σ : state Λ) Θ :=
    ∀ κ e' σ' efs, ¬base_step i e σ Θ κ e' σ' efs.
  Definition base_stuck i (e : expr Λ) (σ : state Λ) Θ :=
    to_val e = None ∧ base_irreducible i e σ Θ.

  (* All non-value redexes are at the root. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step i (e1 : expr Λ) (σ1 : state Λ) (Θ : thread_ids) (κ : list (observation Λ))
      (e2 : expr Λ) (σ2 : state Λ) (efs : gmap thread_id (expr Λ)) : Prop :=
    Ectx_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      base_step i e1' σ1 Θ κ e2' σ2 efs → prim_step i e1 σ1 Θ κ e2 σ2 efs.

  Lemma Ectx_step' i K e1 σ1 Θ κ e2 σ2 efs :
    base_step i e1 σ1 Θ κ e2 σ2 efs → prim_step i (fill K e1) σ1 Θ κ (fill K e2) σ2 efs.
  Proof. econstructor; eauto. Qed.

  Definition ectx_lang_mixin : LanguageMixin of_val to_val prim_step.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros ???????? [??? -> -> ?%val_base_stuck].
      apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
    - intros. inv H. eapply ectx_language_mixin; eauto.
  Qed.

  Definition ectx_lang_ctx_mixin :
    LanguageCtxMixin (@fill Λ) (@empty_ectx Λ) (@comp_ectx Λ).
  Proof.
    split.
    - apply fill_empty.
    - intros. symmetry. apply fill_comp.
  Qed.

  Canonical Structure ectx_lang : language :=
    Language (state_sat:=state_sat) ectx_lang_mixin ectx_lang_ctx_mixin.

  Definition base_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ i σ Θ κ e' σ' efs,
      base_step i e σ Θ κ e' σ' efs →
      if a is WeaklyAtomic then irreducible i e' σ' (Θ ∪ dom efs) else is_Some (to_val e').

  (** * Some lemmas about this language *)
  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma base_reducible_no_obs_reducible i e σ Θ :
    base_reducible_no_obs i e σ Θ → base_reducible i e σ Θ.
  Proof. intros (?&?&?&?). eexists. eauto. Qed.
  Lemma not_base_reducible i e σ Θ : ¬base_reducible i e σ Θ ↔ base_irreducible i e σ Θ.
  Proof. unfold base_reducible, base_irreducible. naive_solver. Qed.

  (** The decomposition into base redex and context is unique; no law equates
      [comp_ectx K' empty_ectx] with [K']. *)
  Lemma base_redex_unique K K' i e e' σ Θ :
    fill K e = fill K' e' →
    base_reducible i e σ Θ →
    base_reducible i e' σ Θ →
    K = comp_ectx K' empty_ectx ∧ e = e'.
  Proof.
    intros Heq (κ & e2 & σ2 & efs & Hred) (κ' & e2' & σ2' & efs' & Hred').
    edestruct (step_by_val i K' K e' e) as [K'' HK];
      [by eauto using val_base_stuck..|].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (base_ctx_step_val _ _ _ _ _ _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
    { by eapply val_base_stuck. }
    subst K''. rewrite fill_empty. done.
  Qed.

  Lemma base_prim_step i e1 σ1 Θ κ e2 σ2 efs :
    base_step i e1 σ1 Θ κ e2 σ2 efs → prim_step i e1 σ1 Θ κ e2 σ2 efs.
  Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma base_step_not_stuck i e σ Θ κ e' σ' efs : base_step i e σ Θ κ e' σ' efs → not_stuck i e σ Θ.
  Proof. rewrite /not_stuck /reducible /=. eauto 10 using base_prim_step. Qed.

  Lemma fill_prim_step i K e1 σ1 Θ κ e2 σ2 efs :
    prim_step i e1 σ1 Θ κ e2 σ2 efs → prim_step i (fill K e1) σ1 Θ κ (fill K e2) σ2 efs.
  Proof.
    destruct 1 as [K' e1' e2' -> ->].
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible i K e σ Θ : reducible i e σ Θ → reducible i (fill K e) σ Θ.
  Proof.
    intros (κ&e'&σ'&efs&?). exists κ, (fill K e'), σ', efs.
    by apply fill_prim_step.
  Qed.
  Lemma fill_reducible_no_obs i K e σ Θ : reducible_no_obs i e σ Θ → reducible_no_obs i (fill K e) σ Θ.
  Proof.
    intros (e'&σ'&efs&?). exists (fill K e'), σ', efs.
    by apply fill_prim_step.
  Qed.
  Lemma base_prim_reducible i e σ Θ : base_reducible i e σ Θ → reducible i e σ Θ.
  Proof. intros (κ&e'&σ'&efs&?). eexists κ, e', σ', efs. by apply base_prim_step. Qed.
  Lemma base_prim_fill_reducible i e K σ Θ :
    base_reducible i e σ Θ → reducible i (fill K e) σ Θ.
  Proof. intro. by apply fill_reducible, base_prim_reducible. Qed.
  Lemma base_prim_reducible_no_obs i e σ Θ : base_reducible_no_obs i e σ Θ → reducible_no_obs i e σ Θ.
  Proof. intros (e'&σ'&efs&?). eexists e', σ', efs. by apply base_prim_step. Qed.
  Lemma base_prim_irreducible i e σ Θ : irreducible i e σ Θ → base_irreducible i e σ Θ.
  Proof.
    rewrite -not_reducible -not_base_reducible. eauto using base_prim_reducible.
  Qed.
  Lemma base_prim_fill_reducible_no_obs i e K σ Θ :
    base_reducible_no_obs i e σ Θ → reducible_no_obs i (fill K e) σ Θ.
  Proof. intro. by apply fill_reducible_no_obs, base_prim_reducible_no_obs. Qed.

  Lemma prim_base_reducible i e σ Θ :
    reducible i e σ Θ → sub_redexes_are_values e → base_reducible i e σ Θ.
  Proof.
    intros (κ&e'&σ'&efs&[K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_base_stuck.
    rewrite fill_empty /base_reducible; eauto.
  Qed.
  Lemma prim_base_irreducible i e σ Θ :
    base_irreducible i e σ Θ → sub_redexes_are_values e → irreducible i e σ Θ.
  Proof.
    rewrite -not_reducible -not_base_reducible. eauto using prim_base_reducible.
  Qed.

  Lemma base_stuck_stuck i e σ Θ :
    base_stuck i e σ Θ → sub_redexes_are_values e → stuck i e σ Θ.
  Proof.
    intros [] ?. split; first done.
    by apply prim_base_irreducible.
  Qed.

  Lemma ectx_language_atomic a e :
    base_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill i σ Θ κ e' σ' efs [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using val_base_stuck.
    rewrite fill_empty. eapply Hatomic_step. by rewrite fill_empty.
  Qed.

  Lemma base_reducible_prim_step_ctx i K e1 σ1 Θ κ e2 σ2 efs :
    base_reducible i e1 σ1 Θ →
    prim_step i (fill K e1) σ1 Θ κ e2 σ2 efs →
    ∃ e2', e2 = fill K e2' ∧ base_step i e1 σ1 Θ κ e2' σ2 efs.
  Proof.
    intros (κ'&e2''&σ2''&efs''&HhstepK) [K' e1' e2' HKe1 -> Hstep].
    edestruct (step_by_val i K) as [K'' ?];
      eauto using val_base_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply base_ctx_step_val in HhstepK as [[v ?]|?]; simplify_eq.
    { apply val_base_stuck in Hstep; simplify_eq. }
    by rewrite !fill_empty.
  Qed.

  Lemma base_reducible_prim_step i e1 σ1 Θ κ e2 σ2 efs :
    base_reducible i e1 σ1 Θ →
    prim_step i e1 σ1 Θ κ e2 σ2 efs →
    base_step i e1 σ1 Θ κ e2 σ2 efs.
  Proof.
    intros.
    edestruct (base_reducible_prim_step_ctx i empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.

  Global Instance ectx_lang_ctx K : @LanguageCtx ectx_lang K.
  Proof.
    split; simpl.
    - eauto using fill_not_val.
    - intros ???????? [K' e1' e2' Heq1 Heq2 Hstep].
      by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
    - intros i e1 σ1 Θ κ e2 σ2 efs Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val i K K'' e1 e1'' σ1 Θ κ e2'' σ2 efs) as [K' ->]; eauto.
      rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      econstructor; eauto.
  Qed.

  Record pure_base_step (e1 e2 : expr Λ) := {
    pure_base_step_safe i σ1 Θ : base_reducible_no_obs i e1 σ1 Θ;
    pure_base_step_det i σ1 Θ κ e2' σ2 efs :
      base_step i e1 σ1 Θ κ e2' σ2 efs → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = ∅
  }.

  Lemma pure_base_step_pure_step e1 e2 : pure_base_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros i σ1 Θ. destruct (Hp1 i σ1 Θ) as (e2' & σ2 & efs & ?).
      eexists e2', σ2, efs. by apply base_prim_step.
    - intros i σ1 κ Θ e2' σ2 efs ?%base_reducible_prim_step; eauto using base_reducible_no_obs_reducible.
  Qed.

  (** Not an instance: HeapLang's [wp_pure] handles evaluation contexts itself. *)
  Lemma pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill K e1) (fill K e2).
  Proof. apply: (pure_exec_ctx K). Qed.
End ectx_language.

Global Arguments ectx_lang : clear implicits.
Global Arguments Ectx_step {Λ i e1 σ1 Θ κ e2 σ2 efs}.
Coercion ectx_lang : ectxLanguage >-> language.

(* The [let '...] match makes the fields of the [language] record the fields of [Λ], not
   projections of it, as canonical structure search needs. *)
Definition LanguageOfEctx (Λ : ectxLanguage) : language :=
  let '@EctxLanguage E V C St K Π of_val to_val empty comp fill base sat mix := Λ in
  @Language E V St K Π C of_val to_val _ sat fill empty comp
    (@ectx_lang_mixin (@EctxLanguage E V C St K Π of_val to_val empty comp fill base sat mix))
    (@ectx_lang_ctx_mixin (@EctxLanguage E V C St K Π of_val to_val empty comp fill base sat mix)).

Global Arguments LanguageOfEctx : simpl never.
