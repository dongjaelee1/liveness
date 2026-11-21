(** Correspondences between the paper's presentation and the definitions of this development.

    The paper states three things differently from Rocq, and this file proves that the
    two agree:
    - [omega_lt_large]: the paper's grammar of measures has ω, where [measure] has [ms_large]
      (written [ℵ]), which is interpreted as [Ord.large]. They are different ordinals, with
      ω below ℵ.
    - [thread_done_iff]: THREAD-DONE (Figure 6) leaves the thread pool and the state unchanged,
      where [thread_done_intro] has the shape of [thread_step_atomic], with side conditions.
    - [behavior_iff]: the paper's [Behavior] quantifies over all later positions of the trace,
      where [behavior] is coinductive.

    None of the three lemmas assumes an axiom ([examples/assumptions.v] prints this). *)
From lantana.algebra Require Import measure layer.
From lantana.program_logic Require Import language.
From iris.prelude Require Import options.

(** ω is below ℵ ([ms_large], interpreted as [Ord.large] by [measure_rep_large]): ω is the
    ordinal of (nat, <), and [Ord.large] is above the ordinal of every well-founded relation on
    a small type. *)
Lemma omega_lt_large : (Ord.omega < Ord.large)%ord.
Proof.
  eapply Ord.le_lt_lt; [apply Ord.omega_from_peano_lt_set|].
  apply Ord.large_lt_from_wf_set.
Qed.

Section equivalences.
  Context {Λ : language}.

  (** THREAD-DONE as in the paper: a scheduled value leaves the thread pool and the state
      unchanged. *)
  Lemma thread_done_iff i (ρ1 ρ2 : cfg Λ) κ :
    thread_done i ρ1 κ ρ2 ↔
    ∃ v, ρ1.1 !! i = Some (of_val v) ∧ κ = [] ∧ ρ2 = ρ1.
  Proof.
    split.
    - intros [e1 σ1 e2 σ2 efs Θ -> Hi ([v Hv] & <- & <- & -> & ->) ->].
      apply of_to_val in Hv. subst e1.
      exists v. split; [done|]. split; [done|].
      rewrite insert_id // map_union_empty //.
    - intros (v & Hi & -> & ->). destruct ρ1 as [Θ σ].
      eapply (thread_done_intro _ _ _ _ (of_val v) σ (of_val v) σ ∅ Θ); [done|done| |].
      + split; [rewrite to_of_val; eauto|done].
      + rewrite insert_id // map_union_empty //.
  Qed.

  (** One transition of Figure 6. Trace states also carry Iris's observations, which the
      paper omits; a transition consumes the observations of its step, as in [behavior]. *)
  Definition trans (s1 s2 : trace_state Λ) : Prop :=
    ∃ ρ1 i1 κ κs ρ2 i2,
      s1 = (ρ1, i1, κ ++ κs) ∧ s2 = (ρ2, i2, κs) ∧
      (thread_step i1 ρ1 κ ρ2 ∨ thread_done i1 ρ1 κ ρ2 ∨ thread_stuck i1 ρ1 κ ρ2).

  Lemma behavior_later k n (ζ : nat → trace_state Λ) :
    behavior (n, ζ) → behavior (k + n, ζ).
  Proof.
    induction k as [|k IH]; [done|]. intros Hb.
    specialize (IH Hb). inversion IH; subst. done.
  Qed.

  (** [Behavior] as in the paper: every transition from the current time on is a step. *)
  Lemma behavior_iff n (ζ : nat → trace_state Λ) :
    behavior (n, ζ) ↔ ∀ m, n ≤ m → trans (ζ m) (ζ (S m)).
  Proof.
    split.
    - intros Hb m Hm. assert (m = (m - n) + n) as -> by lia.
      apply (behavior_later (m - n)) in Hb. inversion Hb; subst.
      do 6 eexists. eauto.
    - revert n. cofix CIH. intros n H.
      destruct (H n (le_n n)) as (ρ1 & i1 & κ & κs & ρ2 & i2 & H1 & H2 & Hs).
      eapply behavior_step; [exact H1|exact Hs|exact H2|].
      apply CIH. intros m Hm. apply H. lia.
  Qed.
End equivalences.
