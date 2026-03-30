From stdpp Require Export gmap.
From iris.algebra Require Export ofe.
From liris.bi Require Export weakestpre.
From iris.prelude Require Import options.
From liris Require Export wfocm.
From liris.prelude Require Export ordinal_facts.

Definition thread_id := positive.
Global Instance thread_id_inhabited : Inhabited thread_id := Pos.inhabited.
Canonical Structure thread_idO `{SI : indexT} := leibnizO thread_id.

Notation thread_ids := (gset thread_id).

Section language_mixin.
  Context {expr val state observation state_pred : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  (** We annotate the reduction relation with observations [κ], which we will
     use in the definition of weakest preconditions to predict future
     observations and assert correctness of the predictions. *)
  (** thread_ids is a state that tracks occupied thread_ids,
     and gmap thread_id expr are forked threads. *)
  Context (prim_step : thread_id → expr → state → thread_ids → list observation →
                       expr → state → gmap thread_id expr → Prop).
  Context (state_sat : state → gmap thread_id expr → state_pred → Prop).

  Record LanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck i e σ Θ κ e' σ' efs : prim_step i e σ Θ κ e' σ' efs → to_val e = None;
    mixin_fork_thread_ids i e σ Θ κ e' σ' efs :
      prim_step i e σ Θ κ e' σ' efs → (Θ ## (dom efs))
  }.
End language_mixin.

Structure language :=
  Language {
      expr : Type;
      val : Type;
      state : Type;
      observation : Type;
      state_pred : Type;
      of_val : val → expr;
      to_val : expr → option val;
      prim_step : thread_id → expr → state → thread_ids → list observation →
                  expr → state → gmap thread_id expr → Prop;
      state_sat : state → gmap thread_id expr → state_pred → Prop;
      language_mixin : LanguageMixin of_val to_val prim_step
    }.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments Language {_ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments prim_step {_} _ _ _ _ _ _ _ _.
Global Arguments state_sat {_} _ _ _.

Canonical Structure stateO `{SI : indexT} Λ := leibnizO (state Λ).
Canonical Structure valO `{SI : indexT} Λ := leibnizO (val Λ).
Canonical Structure exprO `{SI : indexT} Λ := leibnizO (expr Λ).

Definition ctx (Λ : language) := expr Λ → expr Λ.

Class LanguageCtx {Λ : language} (K : ctx Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_step i e1 σ1 Θ1 κ e2 σ2 efs :
    prim_step i e1 σ1 Θ1 κ e2 σ2 efs →
    prim_step i (K e1) σ1 Θ1 κ (K e2) σ2 efs;
  fill_step_inv i e1' σ1 Θ1 κ e2 σ2 efs :
    to_val e1' = None → prim_step i (K e1') σ1 Θ1 κ e2 σ2 efs →
    ∃ e2', e2 = K e2' ∧ prim_step i e1' σ1 Θ1 κ e2' σ2 efs
}.

Global Instance language_ctx_id Λ : LanguageCtx (@id (expr Λ)).
Proof. constructor; naive_solver. Qed.

Global Instance language_ctx_compose Λ (K1 K2 : ctx Λ) :
  LanguageCtx K1 → LanguageCtx K2 → LanguageCtx (K2 ∘ K1).
Proof.
  intros. constructor.
  - simpl. intros. do 2 apply fill_not_val. auto.
  - simpl. intros. apply (fill_step _ (K1 e1)). apply fill_step. auto.
  - simpl. intros. apply fill_step_inv in H2.
    2:{ apply fill_not_val. auto. }
    destruct H2 as (?&?&?). apply (fill_step_inv) in H3.
    2:{ auto. }
    subst. destruct H3 as (?&?&?). subst. eexists. split; eauto.
Qed.

Notation thread_pool Λ := (gmap thread_id (expr Λ)).

Definition cfg (Λ : language) :=
  (thread_pool Λ * state Λ)%type.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  if s is MaybeStuck then StronglyAtomic else WeaklyAtomic.

Section language.
  Context {Λ : language}.
  Implicit Types i : thread_id.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck i e σ Θ κ e' σ' efs : prim_step i e σ Θ κ e' σ' efs → to_val e = None.
  Proof. apply language_mixin. Qed.
  Lemma fork_thread_ids i e σ Θ κ e' σ' efs : prim_step i e σ Θ κ e' σ' efs → (Θ ## (dom efs)).
  Proof. apply language_mixin. Qed.

  Definition reducible i (e : expr Λ) (σ : state Λ) Θ :=
    ∃ κ e' σ' efs, prim_step i e σ Θ κ e' σ' efs.
  (* Total WP only permits reductions without observations *)
  Definition reducible_no_obs i (e : expr Λ) (σ : state Λ) Θ :=
    ∃ e' σ' efs, prim_step i e σ Θ [] e' σ' efs.
  Definition irreducible i (e : expr Λ) (σ : state Λ) Θ :=
    ∀ κ e' σ' efs, ¬prim_step i e σ Θ κ e' σ' efs.
  Definition stuck i (e : expr Λ) (σ : state Λ) Θ :=
    to_val e = None ∧ irreducible i e σ Θ.
  Definition not_stuck i (e : expr Λ) (σ : state Λ) Θ :=
    is_Some (to_val e) ∨ reducible i e σ Θ.

  (* [Atomic WeaklyAtomic]: This (weak) form of atomicity is enough to open
     invariants when WP ensures safety, i.e., programs never can get stuck.  We
     have an example in lambdaRust of an expression that is atomic in this
     sense, but not in the stronger sense defined below, and we have to be able
     to open invariants around that expression.  See `CasStuckS` in
     [lambdaRust](https://gitlab.mpi-sws.org/FP/LambdaRust-coq/blob/master/theories/lang/lang.v).

     [Atomic StronglyAtomic]: To open invariants with a WP that does not ensure
     safety, we need a stronger form of atomicity.  With the above definition,
     in case `e` reduces to a stuck non-value, there is no proof that the
     invariants have been established again. *)
  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic i σ Θ e' κ σ' efs :
      prim_step i e σ Θ κ e' σ' efs →
      if a is WeaklyAtomic then irreducible i e' σ' (Θ ∪ (dom efs)) else is_Some (to_val e').

  (** An atomic thread step.
   We formalize an execution of a program as the infinite sequence of program states,
   where the last state for a terminating program is repeated infinitely.
   Note that if a thread spawns, it never deallocates. *)
  Inductive thread_step (i : thread_id) (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : Prop :=
  | thread_step_atomic e1 σ1 e2 σ2 efs Θ :
    ρ1 = (Θ, σ1) →
    Θ !! i = Some e1 →
    (* atomic execution *)
    prim_step i e1 σ1 (dom Θ) κ e2 σ2 efs →
    ρ2 = (<[i:=e2]>Θ ∪ efs, σ2) →
    (* ((is_Some (to_val e1) ∧ e1 = e2 ∧ σ1 = σ2 ∧ efs = ∅) *)
    (*  ∨ prim_step e1 σ1 (dom ths) κ e2 σ2 efs) → *)
    thread_step i ρ1 κ ρ2.
  Local Hint Constructors thread_step : core.

  Definition erased_thread_step i (ρ1 ρ2 : cfg Λ) := ∃ κ, thread_step i ρ1 κ ρ2.

  (** TODO: Probably need to define trace and a Coinductive behavior for adequacy *)
  Definition step (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : Prop :=
    ∃ i, thread_step i ρ1 κ ρ2.
  Local Hint Unfold step : core.

  Inductive nsteps : nat → cfg Λ → list (observation Λ) → cfg Λ → Prop :=
    | nsteps_refl ρ :
       nsteps 0 ρ [] ρ
    | nsteps_l n ρ1 ρ2 ρ3 κ κs :
       step ρ1 κ ρ2 →
       nsteps n ρ2 κs ρ3 →
       nsteps (S n) ρ1 (κ ++ κs) ρ3.
  Local Hint Constructors nsteps : core.

  Definition erased_step (ρ1 ρ2 : cfg Λ) := ∃ κ, step ρ1 κ ρ2.

  (** [rtc erased_step] and [nsteps] encode the same thing, just packaged
      in a different way. *)
  Lemma erased_steps_nsteps ρ1 ρ2 :
    rtc erased_step ρ1 ρ2 ↔ ∃ n κs, nsteps n ρ1 κs ρ2.
  Proof.
    split.
    - induction 1; firstorder eauto. eexists. eexists. econstructor 2; eauto.
    - intros (n & κs & Hsteps). unfold erased_step.
      induction Hsteps; eauto using rtc_refl, rtc_l.
  Qed.
  (** TODO: and above definitions are maybe not needed *)

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.

  Lemma not_reducible i e σ Θ : ¬reducible i e σ Θ ↔ irreducible i e σ Θ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val i e σ Θ : reducible i e σ Θ → to_val e = None.
  Proof. intros (?&?&?&?&?); eauto using val_stuck. Qed.
  Lemma reducible_no_obs_reducible i e σ Θ : reducible_no_obs i e σ Θ → reducible i e σ Θ.
  Proof. intros (?&?&?&?); eexists; eauto. Qed.
  Lemma val_irreducible i e σ Θ : is_Some (to_val e) → irreducible i e σ Θ.
  Proof. intros [??] ???? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
  Lemma not_not_stuck i e σ Θ : ¬not_stuck i e σ Θ ↔ stuck i e σ Θ.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof. unfold Atomic. destruct a; eauto using val_irreducible. Qed.

  Lemma reducible_fill `{!@LanguageCtx Λ K} i e σ Θ :
    reducible i e σ Θ → reducible i (K e) σ Θ.
  Proof. unfold reducible in *. naive_solver eauto using fill_step. Qed.
  Lemma reducible_fill_inv `{!@LanguageCtx Λ K} i e σ Θ :
    to_val e = None → reducible i (K e) σ Θ → reducible i e σ Θ.
  Proof.
    intros ? (e'&σ'&k&efs&Hstep); unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma reducible_no_obs_fill `{!@LanguageCtx Λ K} i e σ Θ :
    reducible_no_obs i e σ Θ → reducible_no_obs i (K e) σ Θ.
  Proof. unfold reducible_no_obs in *. naive_solver eauto using fill_step. Qed.
  Lemma reducible_no_obs_fill_inv `{!@LanguageCtx Λ K} i e σ Θ :
    to_val e = None → reducible_no_obs i (K e) σ Θ → reducible_no_obs i e σ Θ.
  Proof.
    intros ? (e'&σ'&efs&Hstep); unfold reducible_no_obs.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma irreducible_fill `{!@LanguageCtx Λ K} i e σ Θ :
    to_val e = None → irreducible i e σ Θ → irreducible i (K e) σ Θ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
  Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} i e σ Θ :
    irreducible i (K e) σ Θ → irreducible i e σ Θ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} i e σ Θ :
    not_stuck i (K e) σ Θ → not_stuck i e σ Θ.
  Proof.
    rewrite /not_stuck -!not_eq_None_Some. intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill `{!@LanguageCtx Λ K} i e σ Θ :
    stuck i e σ Θ → stuck i (K e) σ Θ.
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  (** Generalized pure_step that can condition on the state *)
  Record pure_step (e1 e2 : expr Λ) := {
    pure_step_safe i σ1 Θ : reducible_no_obs i e1 σ1 Θ;
    pure_step_det i σ1 κ Θ e2' σ2 efs :
      prim_step i e1 σ1 Θ κ e2' σ2 efs → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = ∅
  }.

  Notation pure_steps_tp := (map_Forall2 (λ _, rtc (pure_step))).

  (* TODO: Exclude the case of [n=0], either here, or in [wp_pure] to avoid it
  succeeding when it did not actually do anything. *)
  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps (pure_step) n e1 e2.

  Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    pure_step e1 e2 →
    pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible_no_obs in *. naive_solver eauto using fill_step.
    - intros i σ1 κ Θ e2' σ2 efs Hpstep.
      destruct (fill_step_inv i e1 σ1 Θ κ e2' σ2 efs) as (e2'' & -> & ?); [|exact Hpstep|].
      + destruct (Hred i σ1 Θ) as (? & ? & ? & ?); eauto using val_stuck.
      + edestruct (Hstep i σ1 κ Θ e2'' σ2 efs) as (? & -> & -> & ->); auto.
  Qed.

  Lemma pure_step_nsteps_ctx K `{!@LanguageCtx Λ K} n e1 e2 :
    relations.nsteps (pure_step) n e1 e2 →
    relations.nsteps (pure_step) n (K e1) (K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.

  Lemma rtc_pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    rtc (pure_step) e1 e2 → rtc (pure_step) (K e1) (K e2).
  Proof. eauto using rtc_congruence, pure_step_ctx. Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx K `{!@LanguageCtx Λ K} φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (K e1) (K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

  (* This is a family of frequent assumptions for PureExec *)
  Class IntoVal (e : expr Λ) (v : val Λ) :=
    into_val : of_val v = e.

  Class AsVal (e : expr Λ) := as_val : ∃ v, of_val v = e.
  (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more
  efficiently since no witness has to be computed. *)
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /=; eauto.
  Qed.

  Lemma as_val_is_Some e :
    (∃ v, of_val v = e) → is_Some (to_val e).
  Proof. intros [v <-]. rewrite to_of_val. eauto. Qed.

  Lemma prim_step_not_stuck i e σ Θ κ e' σ' efs :
    prim_step i e σ Θ κ e' σ' efs → not_stuck i e σ Θ.
  Proof. rewrite /not_stuck /reducible. eauto 10. Qed.

  Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e :
    rtc (pure_step) (of_val v) e → to_val e = Some v.
  Proof.
    intros ?; rewrite <- to_of_val.
    f_equal; symmetry; eapply rtc_nf; first done.
    intros [e' [Hstep _]].
    destruct (Hstep inhabitant inhabitant ∅) as (?&?&?&Hval%val_stuck); auto.
    by rewrite to_of_val in Hval.
  Qed.

  (** Let thread pools [t1] and [t3] be such that each thread in [t1] makes
   (zero or more) pure steps to the corresponding thread in [t3]. Furthermore,
   let [t2] be a thread pool such that [t1] under state [σ1] makes a (single)
   step to thread pool [t2] and state [σ2]. In this situation, either the step
   from [t1] to [t2] corresponds to one of the pure steps between [t1] and [t3],
   or, there is an [i] such that [i]th thread does not participate in the
   pure steps between [t1] and [t3] and [t2] corresponds to taking a step in
   the [i]th thread starting from [t1]. *)
  Lemma erased_thread_step_pure_step_tp i t1 σ1 t2 σ2 t3 :
    erased_thread_step i (t1, σ1) (t2, σ2) →
    pure_steps_tp t1 t3 →
    (σ1 = σ2 ∧ pure_steps_tp t2 t3) ∨
    (∃ i e efs e' κ,
      t1 !! i = Some e ∧ t3 !! i = Some e ∧
      t2 = <[i:=e']>t1 ∪ efs ∧
      prim_step i e σ1 (dom t1) κ e' σ2 efs).
  Proof.
    intros [κ [e σ e' σ' efs ths t11 Hi t12 Hstep]] Hps; simplify_eq/=.
    assert (Hths : ∃ ths', ths = <[i:=e]>ths' ∧ ths' !! i = None).
    { exists (delete i ths). split; [rewrite insert_delete_id | apply lookup_delete_eq]; auto. }
    destruct Hths as (ths'&EQths&Hths'). subst ths. clear Hi.
    apply map_Forall2_insert_inv_l in Hps as (e'' & t31 & -> & Ht31 & Hsteps & Hps); [| done].
    destruct Hsteps as [e|e1 e2 e3 Hpstep Hprs].
    - right. exists i, e, efs, e', κ. split_and!. 1,2: by apply lookup_insert_eq. all: done.
    - edestruct Hpstep as (?&?&?&?); try done. destruct H1. simplify_eq.
      left. split; first done. rewrite insert_insert_eq right_id_L.
      by eapply map_Forall2_insert.
  Qed.

  (* Lemma erased_step_pure_step_tp t1 σ1 t2 σ2 t3 : *)
  (*   erased_step (t1, σ1) (t2, σ2) → *)
  (*   pure_steps_tp t1 t3 → *)
  (*   (σ1 = σ2 ∧ pure_steps_tp t2 t3) ∨ *)
  (*   (∃ i e efs e' κ, *)
  (*     t1 !! i = Some e ∧ t3 !! i = Some e ∧ *)
  (*     t2 = <[i:=e']>t1 ∪ efs ∧ *)
  (*     prim_step i e σ1 (dom t1) κ e' σ2 efs). *)
  (* Proof. *)
  (*   intros [κ [i [e σ e' σ' efs ths t11 t12 Hi Hstep]]] Hps; simplify_eq/=. *)
  (*   assert (Hths : ∃ ths', ths = <[i:=e]>ths' ∧ ths' !! i = None). *)
  (*   { exists (delete i ths). split; [rewrite insert_delete_id | apply lookup_delete_eq]; auto. } *)
  (*   destruct Hths as (ths'&EQths&Hths'). subst ths. clear Hi. *)
  (*   apply map_Forall2_insert_inv_l in Hps as (e'' & t31 & -> & Ht31 & Hsteps & Hps); [| done]. *)
  (*   destruct Hsteps as [e|e1 e2 e3 Hpstep Hprs]. *)
  (*   - right. exists i, e, efs, e', κ. split_and!. 1,2: by apply lookup_insert_eq. all: done. *)
  (*   - edestruct Hpstep as (?&?&?&?); first done. destruct H1. simplify_eq. *)
  (*     left. split; first done. rewrite insert_insert_eq right_id_L. *)
  (*     by eapply map_Forall2_insert. *)
  (* Qed. *)

End language.

Global Hint Mode PureExec + - - ! - : typeclass_instances.
Global Arguments thread_step_atomic {Λ i ρ1 κ ρ2}.
Notation pure_steps_tp := (map_Forall2 (λ _, rtc (pure_step))).

(** Trace and behavior. *)
Definition trace (Λ : language) : Type :=
  nat * (nat → (cfg Λ * thread_id * list (observation Λ))).

Definition trace_next {Λ} : trace Λ → trace Λ := λ τ, (S τ.1, τ.2).
Definition trace_state {Λ} : trace Λ → (cfg Λ * thread_id * list (observation Λ)) := λ τ, (τ.2 τ.1).
Definition trace_thread {Λ} : trace Λ → (thread_id) := λ τ, (trace_state τ).1.2.

Inductive thread_done {Λ : language} (i : thread_id) (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : Prop :=
| thread_done_intro e1 σ1 e2 σ2 efs Θ :
  ρ1 = (Θ, σ1) →
  Θ !! i = Some e1 →
  (is_Some (to_val e1) ∧ e1 = e2 ∧ σ1 = σ2 ∧ efs = ∅ ∧ κ = []) →
  ρ2 = (<[i:=e2]>Θ ∪ efs, σ2) →
  thread_done i ρ1 κ ρ2.

CoInductive behavior {Λ : language} : trace Λ → Prop :=
| behavior_step n τf ρ1 ρ2 i1 i2 κ κs :
  τf n = (ρ1, i1, (κ ++ κs)) →
  (thread_step i1 ρ1 κ ρ2 ∨ thread_done i1 ρ1 κ ρ2) →
  τf (S n) = (ρ2, i2, κs) →
  behavior (S n, τf) →
  behavior (n, τf).

Definition behavior_cfg {Λ : language} (ρ : cfg Λ) (τ : trace Λ) : Prop :=
  ∃ i κs, (τ.2 0) = (ρ, i, κs) ∧ behavior τ.
Definition behavior_tp {Λ : language} (Θ : thread_pool Λ) (τ : trace Λ) : Prop :=
  ∃ σ, behavior_cfg (Θ, σ) τ.

(** We fix a (somewhat general) fair scheduler, only for convenience. *)
Definition fair_sched_ub : Ord.t → Ord.t := (λ a, ((ω × a) ⊕ ω)%ord).

Lemma fair_sched_ub_mono : ∀ o, (o <= fair_sched_ub o)%ord.
Proof.
  intros. etrans. 2: apply Hessenberg.add_base_l. etrans.
  { apply (Jacobsthal.mult_1_l o). }
  apply Jacobsthal.mult_le_proper; last done.
  apply Ord.lt_le, omega_lt_one.
Qed.

Global Instance fair_sched_ub_lt_proper : Proper (Ord.lt ==> Ord.lt) fair_sched_ub.
Proof.
  repeat intro. apply Hessenberg.lt_add_l.
  apply Jacobsthal.lt_mult_r; auto. apply omega_lt_zero.
Qed.

Global Instance fair_sched_ub_le_proper : Proper (Ord.le ==> Ord.le) fair_sched_ub.
Proof.
  repeat intro. apply Hessenberg.le_add_l.
  apply Jacobsthal.le_mult_r; auto.
Qed.

Global Instance fair_sched_ub_ord_mono_fun_class : ord_mono_fun_class :=
  Build_ord_mono_fun_class fair_sched_ub fair_sched_ub_mono _ _.

Definition fair_sched_fun (γ : thread_id → nat) : thread_id → Ord.t → Ord.t :=
  (λ i a, ((ω × a) ⊕ Ord.from_nat (γ i))%ord).

Lemma fair_sched_fun_mon_gen (γ1 γ2 : thread_id → nat) :
  (∀ a b i j, (a < b)%ord → (fair_sched_fun γ1 i a < fair_sched_fun γ2 j b)%ord).
Proof.
  intros. unfold fair_sched_fun. apply ord_lt_exists_left in H. destruct H as (u& GTu& LEu).
  unshelve eapply Ord.lt_le_lt. 1: exact ((ω × (a ⊕ u)) ⊕ γ2 j)%ord.
  2:{ apply Hessenberg.le_add_l. apply Jacobsthal.le_mult_r. auto. }
  rewrite ClassicJacobsthal.mult_dist Hessenberg.add_assoc.
  apply Hessenberg.lt_add_r. unshelve eapply Ord.lt_le_lt. 1: exact ((ω × Ord.one) ⊕ (γ2 j))%ord.
  { rewrite Jacobsthal.mult_1_r. eapply Ord.lt_le_lt, Hessenberg.add_base_l. apply Ord.omega_upperbound. }
  apply Hessenberg.le_add_l, Jacobsthal.le_mult_r. apply Ord.S_supremum. auto.
Qed.

Lemma fair_sched_fun_mon (γ : thread_id → nat) :
  (∀ a b i j, (a < b)%ord → (fair_sched_fun γ i a < fair_sched_fun γ j b)%ord).
Proof.
  intros. eapply fair_sched_fun_mon_gen; eauto.
Qed.

Lemma fair_sched_fun_ub (γ : thread_id → nat) :
  (∀ i a, (fair_sched_fun γ i a <= fair_sched_ub a)%ord).
Proof.
  intros. unfold fair_sched_fun, fair_sched_ub. apply Hessenberg.le_add_r.
  apply Ord.lt_le, Ord.omega_upperbound.
Qed.
