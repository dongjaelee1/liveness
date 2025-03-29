From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.

Definition thread_id := positive.
Canonical Structure thread_idO `{SI : indexT} := leibnizO thread_id.

Notation thread_ids := (gset thread_id).

Section language_mixin.
  Context {expr val state observation fuel : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (fuelR : fuel → fuel → Prop).
  (** We annotate the reduction relation with observations [κ], which we will
     use in the definition of weakest preconditions to predict future
     observations and assert correctness of the predictions. *)
  (** thread_ids is a state that tracks occupied thread_ids,
     and gmap thread_id expr are forked threads. *)
  Context (prim_step : expr → state → thread_ids → list observation →
                       expr → state → gmap thread_id expr → Prop).

  Record LanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e σ τ κ e' σ' efs : prim_step e σ τ κ e' σ' efs → to_val e = None;
    mixin_fuelR_wf : well_founded fuelR;
    mixin_fork_thread_ids e σ τ κ e' σ' efs :
      prim_step e σ τ κ e' σ' efs → (τ ## (dom efs))
  }.
End language_mixin.

Structure language :=
  Language {
      expr : Type;
      val : Type;
      state : Type;
      observation : Type;
      fuel : Type;
      of_val : val → expr;
      to_val : expr → option val;
      fuelR : fuel → fuel → Prop;
      prim_step : expr → state → thread_ids → list observation →
                  expr → state → gmap thread_id expr → Prop;
      language_mixin : LanguageMixin of_val to_val fuelR prim_step
    }.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments Language {_ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments fuelR {_} _ _.
Global Arguments prim_step {_} _ _ _ _ _ _ _.

Canonical Structure fuelO `{SI : indexT} Λ := leibnizO (fuel Λ).
Canonical Structure stateO `{SI : indexT} Λ := leibnizO (state Λ).
Canonical Structure valO `{SI : indexT} Λ := leibnizO (val Λ).
Canonical Structure exprO `{SI : indexT} Λ := leibnizO (expr Λ).

Notation sched_fuels := (λ Λ, gmap thread_id (option (fuel Λ))).
Notation thread_pool := (λ Λ, gmap thread_id (expr Λ)).

(** Thread pool with fuels to model scheduler fairness.
    If a thread is done (is a val), fuel = None. *)
Definition cfg (Λ : language) :=
  (thread_pool Λ * sched_fuels Λ * state Λ)%type.
  (* (gmap thread_id (expr Λ) * gmap thread_id (option (fuel Λ)) * state Λ)%type. *)

Class LanguageCtx {Λ : language} (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_step e1 σ1 τ1 κ e2 σ2 efs :
    prim_step e1 σ1 τ1 κ e2 σ2 efs →
    prim_step (K e1) σ1 τ1 κ (K e2) σ2 efs;
  fill_step_inv e1' σ1 τ1 κ e2 σ2 efs :
    to_val e1' = None → prim_step (K e1') σ1 τ1 κ e2 σ2 efs →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 τ1 κ e2' σ2 efs
}.

Global Instance language_ctx_id Λ : LanguageCtx (@id (expr Λ)).
Proof. constructor; naive_solver. Qed.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  if s is MaybeStuck then StronglyAtomic else WeaklyAtomic.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck e σ τ κ e' σ' efs : prim_step e σ τ κ e' σ' efs → to_val e = None.
  Proof. apply language_mixin. Qed.
  Lemma fuelR_wf : well_founded (@fuelR Λ).
  Proof. apply language_mixin. Qed.
  Lemma fork_thread_ids e σ τ κ e' σ' efs : prim_step e σ τ κ e' σ' efs → (τ ## (dom efs)).
  Proof. apply language_mixin. Qed.

  Definition reducible (e : expr Λ) (σ : state Λ) τ :=
    ∃ κ e' σ' efs, prim_step e σ τ κ e' σ' efs.
  (* Total WP only permits reductions without observations *)
  Definition reducible_no_obs (e : expr Λ) (σ : state Λ) τ :=
    ∃ e' σ' efs, prim_step e σ τ [] e' σ' efs.
  Definition irreducible (e : expr Λ) (σ : state Λ) τ :=
    ∀ κ e' σ' efs, ¬prim_step e σ τ κ e' σ' efs.
  Definition stuck (e : expr Λ) (σ : state Λ) τ :=
    to_val e = None ∧ irreducible e σ τ.
  Definition not_stuck (e : expr Λ) (σ : state Λ) τ :=
    is_Some (to_val e) ∨ reducible e σ τ.

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
    atomic σ τ e' κ σ' efs :
      prim_step e σ τ κ e' σ' efs →
      if a is WeaklyAtomic then irreducible e' σ' (τ ∪ (dom efs)) else is_Some (to_val e').

  Definition thread_pool_inv (ths : thread_pool Λ) (ϕ : sched_fuels Λ) : Prop :=
    map_Forall2 (λ _ e f, (is_Some (to_val e) ∧ f = None) ∨ (to_val e = None ∧ is_Some f)) ths ϕ.

  Definition fuels_fair_update (S : thread_ids) (ϕ1 ϕ2 : sched_fuels Λ) : Prop :=
    map_Forall2 (λ i u1 u2,
                   match u1, u2 with
                   | None, None => True
                   | Some f1, Some f2 => if decide (i ∈ S) then True else (fuelR f2 f1)
                   | _, _ => False
                   end) ϕ1 ϕ2.

  Definition fuels_thread_yield (i : thread_id) (e : expr Λ) (ϕ : sched_fuels Λ) : sched_fuels Λ :=
    match to_val e with
    | Some v => <[i:=None]>ϕ
    | None => ϕ
    end.

  Definition fuels_fair_add (efs : thread_pool Λ) (ϕ1 ϕ2 : sched_fuels Λ) : Prop :=
    ∃ (ϕ' : sched_fuels Λ), (thread_pool_inv efs ϕ') ∧ (ϕ2 = ϕ1 ∪ ϕ').

  (** An atomic thread step under scheduler fairness governed by fuel. *)
  Inductive step (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : Prop :=
  | step_atomic e1 σ1 e2 σ2 ths i efs ϕ0 ϕ1 ϕ2 ϕ3 :
    ρ1 = (ths, ϕ0, σ1) →
    ths !! i = Some e1 →
    (* fair scheduling. *)
    fuels_fair_update {[i]} ϕ0 ϕ1 →
    prim_step e1 σ1 (dom ths) κ e2 σ2 efs →
    ϕ2 = fuels_thread_yield i e2 ϕ1 →
    fuels_fair_add efs ϕ2 ϕ3 →
    ρ2 = (<[i:=e2]>ths ∪ efs, ϕ3, σ2) →
    step ρ1 κ ρ2.
  Local Hint Constructors step : core.

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
    - induction 1; firstorder eauto. (* FIXME: [naive_solver eauto] should be able to handle this *)
    - intros (n & κs & Hsteps). unfold erased_step.
      induction Hsteps; eauto using rtc_refl, rtc_l.
  Qed.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.

  Lemma not_reducible e σ τ : ¬reducible e σ τ ↔ irreducible e σ τ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val e σ τ : reducible e σ τ → to_val e = None.
  Proof. intros (?&?&?&?&?); eauto using val_stuck. Qed.
  Lemma reducible_no_obs_reducible e σ τ : reducible_no_obs e σ τ → reducible e σ τ.
  Proof. intros (?&?&?&?); eexists; eauto. Qed.
  Lemma val_irreducible e σ τ : is_Some (to_val e) → irreducible e σ τ.
  Proof. intros [??] ???? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
  Lemma not_not_stuck e σ τ : ¬not_stuck e σ τ ↔ stuck e σ τ.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof. unfold Atomic. destruct a; eauto using val_irreducible. Qed.

  Lemma reducible_fill `{!@LanguageCtx Λ K} e σ τ :
    reducible e σ τ → reducible (K e) σ τ.
  Proof. unfold reducible in *. naive_solver eauto using fill_step. Qed.
  Lemma reducible_fill_inv `{!@LanguageCtx Λ K} e σ τ :
    to_val e = None → reducible (K e) σ τ → reducible e σ τ.
  Proof.
    intros ? (e'&σ'&k&efs&Hstep); unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma reducible_no_obs_fill `{!@LanguageCtx Λ K} e σ τ :
    reducible_no_obs e σ τ → reducible_no_obs (K e) σ τ.
  Proof. unfold reducible_no_obs in *. naive_solver eauto using fill_step. Qed.
  Lemma reducible_no_obs_fill_inv `{!@LanguageCtx Λ K} e σ τ :
    to_val e = None → reducible_no_obs (K e) σ τ → reducible_no_obs e σ τ.
  Proof.
    intros ? (e'&σ'&efs&Hstep); unfold reducible_no_obs.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma irreducible_fill `{!@LanguageCtx Λ K} e σ τ :
    to_val e = None → irreducible e σ τ → irreducible (K e) σ τ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. Qed.
  Lemma irreducible_fill_inv `{!@LanguageCtx Λ K} e σ τ :
    irreducible (K e) σ τ → irreducible e σ τ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K `{!@LanguageCtx Λ K} e σ τ :
    not_stuck (K e) σ τ → not_stuck e σ τ.
  Proof.
    rewrite /not_stuck -!not_eq_None_Some. intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill `{!@LanguageCtx Λ K} e σ τ :
    stuck e σ τ → stuck (K e) σ τ.
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  (** Properties about step. *)
  Lemma thread_pool_inv_dom ths ϕ :
    thread_pool_inv ths ϕ → dom ths = dom ϕ.
  Proof. by eapply map_Forall2_dom_L. Qed.

  Lemma fuels_fair_update_dom S ϕ0 ϕ1 :
    fuels_fair_update S ϕ0 ϕ1 → dom ϕ0 = dom ϕ1.
  Proof. by eapply map_Forall2_dom_L. Qed.

  Lemma fuels_fair_update_thread_pool_inv ths ϕ0 S ϕ1 :
    thread_pool_inv ths ϕ0 →
    fuels_fair_update S ϕ0 ϕ1 →
    thread_pool_inv ths ϕ1.
  Proof.
    revert ϕ0 ϕ1. pattern ths. revert ths. eapply map_ind; intros.
    { apply map_Forall2_empty_inv_l in H; subst. apply map_Forall2_empty_inv_l in H0; subst.
      apply map_Forall2_empty.
    }
    eapply map_Forall2_insert_inv_l in H1; [|done]. destruct H1 as (?&?&?&?&?&?). subst.
    eapply map_Forall2_insert_inv_l in H2; [|done]. destruct H2 as (?&?&?&?&?&?). subst.
    apply map_Forall2_insert; auto.
    split; [| by eapply H0].
    destruct x0, x2; simpl in H6; try done.
    destruct H4.
    - by destruct H1.
    - right. by destruct H1.
  Qed.

  Lemma fuels_thread_yield_thread_pool_inv ths e1 ϕ i e2 :
    ths !! i = Some e1 →
    to_val e1 = None →
    thread_pool_inv ths ϕ →
    thread_pool_inv (<[i:=e2]>ths) (fuels_thread_yield i e2 ϕ).
  Proof.
    intros Hs Hv Hi. rewrite <- (insert_delete ths i e1) in Hi; [|done].
    apply map_Forall2_insert_inv_l in Hi; [|by eapply lookup_delete].
    destruct Hi as (?&?&?&?&?&?). subst.
    rewrite <- (insert_delete ths i e1); [|done]. rewrite (insert_insert (delete i ths)).
    rewrite /fuels_thread_yield. destruct (to_val e2) eqn:He.
    - rewrite insert_insert. apply map_Forall2_insert; try done.
      + apply lookup_delete.
      + split; [left; done | done].
    - apply map_Forall2_insert; try done.
      + apply lookup_delete.
      + split; [right | done]. rewrite Hv in H1. destruct H1 as [(?&?) | (?&?)]; [| done].
        by destruct H.
  Qed.

  Lemma disjoint_union_thread_pool_inv ths ϕ efs ϕ' :
    (dom ths ## dom efs) →
    thread_pool_inv ths ϕ →
    thread_pool_inv efs ϕ' →
    thread_pool_inv (ths ∪ efs) (ϕ ∪ ϕ').
  Proof.
    revert ϕ. pattern ths. revert ths. eapply map_ind; intros.
    { apply map_Forall2_empty_inv_l in H0; subst. rewrite !left_id_L. auto. }
    eapply map_Forall2_insert_inv_l in H2; [|done]. destruct H2 as (?&?&?&?&?&?). subst.
    assert (Hefs : efs !! i = None).
    { apply map_disjoint_dom in H1. eapply map_disjoint_Some_l; [done | apply lookup_insert]. }
    rewrite -!insert_union_l. apply map_Forall2_insert.
    { rewrite lookup_union_l; auto. }
    { rewrite lookup_union_l; [auto |]. apply not_elem_of_dom_1. apply not_elem_of_dom_2 in Hefs.
      replace (dom ϕ') with (dom efs); [auto|].
      by eapply map_Forall2_dom_L.
    }
    split; [done|].
    apply H0; try done. set_solver.
  Qed.

  Lemma fuels_fair_add_thread_pool_inv ths ϕ1 efs ϕ2 :
    (dom ths ## dom efs) →
    thread_pool_inv ths ϕ1 →
    fuels_fair_add efs ϕ1 ϕ2 →
    thread_pool_inv (ths ∪ efs) ϕ2.
  Proof.
    intros. destruct H1 as (ϕ'&?&?). subst. by apply disjoint_union_thread_pool_inv.
  Qed.

  Lemma step_thread_pool_inv ρ1 κ ρ2 :
    thread_pool_inv ρ1.1.1 ρ1.1.2 →
    step ρ1 κ ρ2 →
    thread_pool_inv ρ2.1.1 ρ2.1.2.
  Proof.
    intros Hi Hs. inv Hs. simpl in *.
    assert (Hd : dom ths ## dom efs).
    { by eapply fork_thread_ids. }
    eapply fuels_fair_add_thread_pool_inv; [| | done].
    { rewrite dom_insert_lookup; done. }
    eapply fuels_thread_yield_thread_pool_inv; [done | by eapply val_stuck |].
    eapply fuels_fair_update_thread_pool_inv; done.
  Qed.

  Record pure_step (e1 e2 : expr Λ) := {
    pure_step_safe σ1 τ : reducible_no_obs e1 σ1 τ;
    pure_step_det σ1 κ τ e2' σ2 efs :
      prim_step e1 σ1 τ κ e2' σ2 efs → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = ∅
  }.

  Notation pure_steps_tp := (map_Forall2 (λ _, rtc pure_step)).

  (* TODO: Exclude the case of [n=0], either here, or in [wp_pure] to avoid it
  succeeding when it did not actually do anything. *)
  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps pure_step n e1 e2.

  Lemma pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    pure_step e1 e2 →
    pure_step (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible_no_obs in *. naive_solver eauto using fill_step.
    - intros σ1 κ τ e2' σ2 efs Hpstep.
      destruct (fill_step_inv e1 σ1 τ κ e2' σ2 efs) as (e2'' & -> & ?); [|exact Hpstep|].
      + destruct (Hred σ1 τ) as (? & ? & ? & ?); eauto using val_stuck.
      + edestruct (Hstep σ1 κ τ e2'' σ2 efs) as (? & -> & -> & ->); auto.
  Qed.

  Lemma pure_step_nsteps_ctx K `{!@LanguageCtx Λ K} n e1 e2 :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (K e1) (K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.

  Lemma rtc_pure_step_ctx K `{!@LanguageCtx Λ K} e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2).
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

  Lemma prim_step_not_stuck e σ τ κ e' σ' efs :
    prim_step e σ τ κ e' σ' efs → not_stuck e σ τ.
  Proof. rewrite /not_stuck /reducible. eauto 10. Qed.

  Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e :
    rtc pure_step (of_val v) e → to_val e = Some v.
  Proof.
    intros ?; rewrite <- to_of_val.
    f_equal; symmetry; eapply rtc_nf; first done.
    intros [e' [Hstep _]].
    destruct (Hstep inhabitant ∅) as (?&?&?&Hval%val_stuck).
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
  Lemma erased_step_pure_step_tp t1 ϕ1 σ1 t2 ϕ2 σ2 t3 :
    erased_step (t1, ϕ1, σ1) (t2, ϕ2, σ2) →
    pure_steps_tp t1 t3 →
    (σ1 = σ2 ∧ pure_steps_tp t2 t3) ∨
    (∃ i e efs e' κ,
      t1 !! i = Some e ∧ t3 !! i = Some e ∧
      t2 = <[i:=e']>t1 ∪ efs ∧
      prim_step e σ1 (dom t1) κ e' σ2 efs).
  Proof.
    intros [κ [e σ e' σ' ths i efs ϕ10 ϕ11 ϕ12 ϕ13 t11 Hi Hf0 Hstep Hf' Hf1 t12]] Hps; simplify_eq/=.
    assert (Hths : ∃ ths', ths = <[i:=e]>ths' ∧ ths' !! i = None).
    { exists (delete i ths). split; [by rewrite insert_delete | by apply lookup_delete]. }
    destruct Hths as (ths'&EQths&Hths'). subst ths. clear Hi.
    apply map_Forall2_insert_inv_l in Hps as (e'' & t31 & -> & Ht31 & Hsteps & Hps); [| done].
    destruct Hsteps as [e|e1 e2 e3 Hpstep Hprs].
    - right. exists i, e, efs, e', κ. split_and!. 1,2: by apply lookup_insert. all: done.
    - edestruct Hpstep as (?&?&?&?); first done. destruct H1. simplify_eq.
      left. split; first done. rewrite insert_insert right_id_L.
      by eapply map_Forall2_insert.
  Qed.

End language.

Global Hint Mode PureExec + - - ! - : typeclass_instances.

Global Arguments step_atomic {Λ ρ1 κ ρ2}.

Notation pure_steps_tp := (map_Forall2 (λ _, rtc pure_step)).
