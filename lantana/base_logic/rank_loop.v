From iris.proofmode Require Import proofmode.
From lantana.base_logic Require Export opreds depth.
From iris.prelude Require Import options.

(** * Rank loops: stackable well-founded components with a computed charge

  A blocking loop is justified by a finite family of well-founded relations,
  ordered: every iteration makes progress on one component and may reset the
  components below it. [lex_fuels] (lex_fuels.v) packages the two-component
  case, an embedded variant over a witness. This file packages the general
  case as a structure [rank_loop] that can be stacked:

  - [wit_rank_loop] is the base: waiting on one obligation by witness
    induction;
  - [embed_rank_loop wf R] adds an outer component, a value of a
    well-founded type, above the loop [R].

  Every rank loop knows its own charge [rl_budget]: [ℵ] per embedded
  component (above every rank of a small well-founded type) and [▽] for the
  witness (above every witness bound at a lower layer). With depth fuel the
  charge is paid by one unit one depth up ([rank_loop_run_d]), so a proof
  that stacks three components never writes an ordinal at all.

  The induction principle [rl_ind] offers the loop body one hypothesis: for
  any state [s'] reachable by a step from the current state [s], the step
  resource [rl_step s s'] buys the per-iteration budget [m] and the goal at
  [s']. For the witness the step resource is a witness credit; for an
  embedded component it is either a step of the inner loop with the variant
  unchanged, or a strict decrease of the variant with the inner loop
  restarted at any state. *)

Section rank_loop.
  Context `{SI : sidx} `{!mupdGS Σ} `{OMC : !ord_mono_fun_class}.
  (** The carriers of the looping thread, their layer, and the budget of
      one iteration of the body. *)
  Context (G : gset ocid) (l : ord.t) (m : measure).

  Local Notation fuels μ := ([∗ set] g ∈ G, crP_fuel g l μ)%I.

  Record rank_loop := RankLoop {
    rl_state : Type;
    (** what it takes to start the loop at a state, besides fuel *)
    rl_init : rl_state → iProp Σ;
    (** the fuel (on [G] at layer [l]) it takes to start *)
    rl_budget : measure;
    (** the running structure *)
    rl_fuels : rl_state → iProp Σ;
    (** the resource certifying progress from one state to the next *)
    rl_step : rl_state → rl_state → iProp Σ;
    rl_start : ∀ s, rl_init s -∗ fuels rl_budget ==∗ rl_fuels s;
    rl_ind : ∀ (P : rl_state → iProp Σ) s,
      □ (∀ s, (∀ s', rl_step s s' ==∗ fuels m ∗ P s') ==∗ P s) ∗ rl_fuels s ⊢ |==> P s;
  }.

  (** Running a rank loop from its initial resources and charge. *)
  Lemma rank_loop_run (R : rank_loop) (P : rl_state R → iProp Σ) s :
    □ (∀ s, (∀ s', rl_step R s s' ==∗ fuels m ∗ P s') ==∗ P s) ∗
    rl_init R s ∗ fuels (rl_budget R)
    ⊢ |==> P s.
  Proof.
    iIntros "(#H& I& F)". iMod (rl_start R s with "I F") as "RF".
    iApply (rl_ind R with "[$RF]"). done.
  Qed.

  (** With depth fuel: one unit one depth up pays the whole charge. *)
  Lemma rank_loop_run_d (R : rank_loop) (P : rl_state R → iProp Σ) s (n : nat) :
    □ (∀ s, (∀ s', rl_step R s s' ==∗ fuels m ∗ P s') ==∗ P s) ∗
    rl_init R s ∗ ([∗ set] g ∈ G, crP_dfuel g l (S n) 1)
    ⊢ |==> P s.
  Proof.
    iIntros "(#H& I& F)". iMod (crP_dfuel_to_fuel_set _ _ _ (rl_budget R) with "F") as "F".
    iApply rank_loop_run. iFrame "H I F".
  Qed.

  (** ** The base: one obligation, by witness induction. *)
  Program Definition wit_rank_loop : rank_loop := {|
    rl_state := oid * ord.t;
    rl_init := λ '(k, ℓ), (⌜(ℓ < l)%ordi⌝ ∗ witP_layer k ℓ)%I;
    rl_budget := (m × ▽)%M;
    rl_fuels := λ '(k, ℓ), (witP_layer k ℓ ∗ ∃ α, wit_fuels k ℓ α (gset_to_gmap (l, m) G))%I;
    rl_step := λ '(k, ℓ) '(k', ℓ'), (⌜k' = k ∧ ℓ' = ℓ⌝ ∗ witP_cred k Ord.one)%I;
  |}.
  Next Obligation.
    intros [k ℓ]. iIntros "[%LT #Wl] F".
    iPoseProof (wit_fuels_init with "Wl") as "(%α& W0)".
    iMod (wit_fuels_add_map with "W0 F") as "W". 1: done. rewrite map_union_empty.
    iModIntro. iFrame "Wl". eauto.
  Qed.
  Next Obligation.
    intros P [k ℓ]. iIntros "[#H (#Wl& %α& W)]".
    iApply (wit_fuels_ind with "[$W]").
    iIntros "!> IHw". iApply ("H" $! (k, ℓ)).
    iIntros ([k' ℓ']) "[[-> ->] Wc]".
    iMod ("IHw" with "Wc") as "[Fs HP]".
    iEval (rewrite big_sepM_gset_to_gmap) in "Fs". by iFrame.
  Qed.

  (** ** Embedding: a well-founded variant above a rank loop. *)
  Program Definition embed_rank_loop {A : Type} {ltA : A → A → Prop}
    (wf_ltA : well_founded ltA) (R : rank_loop) : rank_loop := {|
    rl_state := A * rl_state R;
    rl_init := λ '(a, s), rl_init R s;
    rl_budget := (((m ⊕ rl_budget R) × ℵ) ⊕ rl_budget R)%M;
    rl_fuels := λ '(a, s),
      (embed_fuels wf_ltA a (gset_to_gmap (l, (m ⊕ rl_budget R)%M) G) ∗ rl_fuels R s)%I;
    rl_step := λ '(a, s) '(a', s'),
      ((⌜a' = a⌝ ∗ rl_step R s s') ∨ (⌜ltA a' a⌝ ∗ rl_init R s'))%I;
  |}.
  Next Obligation.
    intros A ltA wf R [a s]. iIntros "I F".
    iPoseProof (crP_fuel_add_set with "F") as "[Fe Fr]".
    iPoseProof (embed_fuels_init wf a) as "E0".
    iMod (embed_fuels_add_map with "E0 Fe") as "E". rewrite map_union_empty.
    iMod (rl_start R s with "I Fr") as "RF". iModIntro. iFrame.
  Qed.
  Next Obligation.
    intros A ltA wf R P [a s]. iIntros "[#H RF]". iRevert (s) "RF".
    iInduction a as [a IHa] using (well_founded_ind wf).
    iIntros (s) "[E F]".
    iAssert (|==> (embed_fuels wf a (gset_to_gmap (l, (m ⊕ rl_budget R)%M) G) -∗ |==> P (a, s)))%I
      with "[F]" as ">HP"; last by iApply ("HP" with "E").
    iApply (rl_ind R (λ s, embed_fuels wf a (gset_to_gmap (l, (m ⊕ rl_budget R)%M) G) -∗ |==> P (a, s))%I
             with "[$F]").
    iIntros "!> %s0 IHw !> E". iApply ("H" $! (a, s0)).
    iIntros ([a' s']) "[[-> S] | [%Lt I]]".
    - iMod ("IHw" with "S") as "[Fs HP]". iFrame "Fs". by iApply ("HP" with "E").
    - iMod (embed_fuels_decr _ _ a' with "E") as "[E Fs]". 1: done.
      iEval (rewrite big_sepM_gset_to_gmap) in "Fs".
      iPoseProof (crP_fuel_add_set with "Fs") as "[Fm Fb]".
      iMod (rl_start R s' with "I Fb") as "F'".
      iMod ("IHa" with "[//] [$E $F']") as "$". done.
  Qed.

  (** [lex_fuels] of lex_fuels.v is the two-component instance; a third
      component is one more embedding, with its charge computed. *)
  Definition lex_rank_loop {A} {ltA : A → A → Prop} (wf : well_founded ltA) : rank_loop :=
    embed_rank_loop wf wit_rank_loop.
  Definition lex3_rank_loop {A B} {ltA : A → A → Prop} {ltB : B → B → Prop}
    (wfA : well_founded ltA) (wfB : well_founded ltB) : rank_loop :=
    embed_rank_loop wfA (embed_rank_loop wfB wit_rank_loop).

  Lemma lex3_rank_loop_budget {A B} {ltA : A → A → Prop} {ltB : B → B → Prop}
    (wfA : well_founded ltA) (wfB : well_founded ltB) :
    rl_budget (lex3_rank_loop wfA wfB)
    = (((m ⊕ (((m ⊕ (m × ▽)) × ℵ) ⊕ (m × ▽))) × ℵ) ⊕ (((m ⊕ (m × ▽)) × ℵ) ⊕ (m × ▽)))%M.
  Proof. done. Qed.

End rank_loop.
