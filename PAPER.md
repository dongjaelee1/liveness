# From the paper to Rocq

This document relates *Decoupling Liveness Obligations from Threads in the Lantana Concurrent
Separation Logic* (POPL 2027) to the current development. The artifact evaluated with the paper
is the tag `popl27-ae-v1` (branch `popl27/artifact`). The development has evolved since then;
the tables below give the current Rocq name of each item of the paper. For building and for the
layout of the development, see [README.md](README.md).

1. [Results](#1-results)
2. [Differences from the paper](#2-differences-from-the-paper)
3. [Predicates](#3-predicates-fig-1-35)
4. [Rules](#4-rules-figs-36-5)
5. [Traces, temporal properties and adequacy](#5-traces-temporal-properties-and-adequacy-6-fig-7)
6. [Case studies](#6-case-studies-27)
7. [Checking the results](#7-checking-the-results)

## 1. Results

| Result | Paper | Rocq |
|---|---|---|
| The logic: Lantana's predicates and the rules the paper displays, as lemmas about the weakest precondition `lWP` and the model update `\|={E}=>m`; the carrier rules become rules of the obligation forest | §1–§5, Figs. 1, 3–6 | `lantana/`, `lantana_heap_lang/` |
| Adequacy: `lwp_adequacy_temporal` (Theorem 1), and Iris-style safety `lwp_adequacy_safety_iris` | §6 | `lantana/trace/adequacy_temporal.v`, `lantana/trace/adequacy_safety.v` |
| The case studies, with end-to-end liveness and safety theorems for the client programs | §2, §4.3, §5, §7 | `lantana_heap_lang/examples/` |
| A pure-step rule that burns no fuel is unsound: `no_lc_absurd` | end of §6.2 | `lantana_heap_lang/examples/paradox.v` |
| Nothing is admitted, and the results assume only axioms of Rocq's standard library | — | [§7](#7-checking-the-results) |

## 2. Differences from the paper

### The weakest precondition replaces the fuel-burning triple

The paper presents Lantana through the *fuel-burning triple* `{P}^G e {Q}^G'`. The development
is stated in terms of the thread-local weakest precondition `lwp` (notation
`lWP e @ s; i; E {{ Φ }}` from `lantana/program_logic/lwp_notation.v`, defined in
`lantana/program_logic/weakestpre.v`). A triple of the paper corresponds to a texan-style `lwp`
triple in which the superscripts become ordinary assertions `thP_kids i G`, the obligations
directly below thread `i`:

```
l{{{ thread_expr i C e ∗ thP_kids i G ∗ P }}} e @ i; E
l{{{ v, RET v; thread_expr i C (of_val v) ∗ thP_kids i G' ∗ Q v }}}
```

Rules that the paper states for the triple therefore appear either as `lwp_*` lemmas, or as
entailments and model updates `|={E}=>m` on the underlying predicates, usable at any point of an
`lwp` proof (`sfmupd_lwp`, `lwp_sfmupd`). The case-study specifications are texan-style `lwp`
triples with explicit `thP_kids`/`parP_kids`/`oblP_fuel` assertions.

### Obligations form a forest, and there are no carriers

The parent of an obligation is a thread or another obligation (`PThread i` / `PObl k`,
`base_logic/parent.v`), and `parP_kids p K` says that the children of `p` are `K`. A step of
thread `i` burns one unit of fuel of each child of `i`; the model keeps the fuel of every
obligation above the fuel of its parent, so the obligations further below make progress too. An
obligation changes its parent by burning one unit of its own fuel (`obl_move`), so obligation fuel
`oblP_fuel` is the only kind of fuel. The predicates, the model update `|={E}=>m` and their rules
are the class `oblf.obl_forest_interface` (`program_logic/obl_forest.v`, derived rules in
`program_logic/obl_forest_rules.v`); `lwp` and everything built on it use only the class. Its one
instance `obl_forest_lantana` (`program_logic/obl_forest_instance.v`) is the model `omodel` of
`base_logic/opreds.v`.

### Temporal formulas are iProps

There is no syntax of temporal formulas: `alwaysI`, `untilI` and `finallyI` are ordinary
`iProp`s, and a persistent *guarantee* `P ⊨ₜ G` (`guar P G`) states that whenever `P` holds, the
rest of the execution satisfies the trace specification `G` (`trSpec`). Guarantees are inferred
by `IntoGuar` instances, and adequacy concludes the trace reading `trSpec_external G`
(`trace/guarantee.v`; inference in `trace/guarantee_infer.v`).

### Two entailments of trace specifications

A `trSpec` has an in-logic reading, which the run establishes, and a trace reading, which
adequacy concludes. In-logic entailment `G ⊑ H` (`trSpec_le`, rules in `trace/trspec_rules.v`)
transports guarantees (`guar_weaken`) and is what the connectives are monotone in, but it is too
weak for temporal reasoning (`trSpec_always_elim_not_le`). Trace entailment
`trSpec_external G ⊆ R` is LTL on traces (rules in `trace/trace_prop_rules.v`), and the cast
`trSpec_cast G R pf` transports it along a guarantee (`guar_cast`). `IntoTrace P R` infers the
trace property that `P` guarantees (`trace/guarantee_infer.v`).

## 3. Predicates (Fig. 1, §3–§5)

| Paper | Rocq | File (under `lantana/`) |
|---|---|---|
| `{P}^G_i e {Q}^G'_E` (fuel-burning triple) | a texan `lwp` triple `l{{{ thread_expr i C e ∗ thP_kids i G ∗ P }}} e @ i; E l{{{ v, RET v; … ∗ thP_kids i G' ∗ Q v }}}` (persistent, as the `□`-specifications of §3.4) | `program_logic/lwp_notation.v`, `program_logic/weakestpre.v` |
| carrier superscripts / `carriers_i G` (Thm 1) | no carriers: `thP_kids i G`, the children of thread `i` in the obligation forest; every initial thread starts with `thP_kids i ∅` | `program_logic/obl_forest.v` |
| `Fuel^ℓ_G μ` | no carrier fuel: `oblP_fuel k ℓ μ` of each child `k` of the thread; a set is `[∗ set] k ∈ G, oblP_fuel k ℓ μ` (cf. `oblP_fuels`) | `program_logic/obl_forest.v` |
| `obls^ℓ_g K` | replaced by `parP_kids p K` (children `K` of a thread, `thP_kids i K`, or of an obligation, `oblP_kids k K`); below an obligation the layer bound is its witness layer (`parP_below` / `parP_le`) | `program_logic/obl_forest.v` |
| `Φ until^k_q Ψ` | `untilI N k q P Q` (an `iProp`; `N` is the namespace of the obligation invariant `oblP_inv` of `k`; variant `untilI_guar` with given readings, e.g. for recursion, `renew` in `trace/guarantee_rec.v`); guarantee `guar_untilI`. A discharged until is the done until `untilI_done k Q` (`untilI_discharge_done`, or `untilI_done_init` for an until fulfilled at its allocation); guarantee `guar_untilI_done` | `trace/temporal_formula.v`, `trace/temporal_formula_rules.v` |
| `finally^k Φ` | `finallyI N k q Q` (`untilI N k q True Q`) | `trace/temporal_formula.v` |
| `obl∎ k` (discharged) | `oblP_discharged k` | `program_logic/obl_forest.v` |
| `tr$^ℓ_k m` (transfer credit) | `oblP_fuel k ℓ m` (the obligation's own fuel, now the only kind of fuel) | `program_logic/obl_forest.v` |
| `wit^ℓ k` (witness) | `witP_layer k ℓ` | `program_logic/obl_forest.v` |
| `wit€ k` (witness credit, §4.1) | `witP_cred k a` (`a` an ordinal amount; a step gives `witP_cred k Ord.one`, notation `witP_cred1 k`) | `program_logic/obl_forest.v` |
| `∎ i` (thread finished, Thm 1) | `thP_done i` | `program_logic/obl_forest.v` |
| `always I` | `alwaysI N I` (a registered invariant; variants `alwaysI_as`, `alwaysI_guar`); guarantee `guar_alwaysI` | `trace/temporal_formula.v`, `trace/temporal_formula_rules.v`, `base_logic/invariants.v` |
| `£ α` (transfinite later credits) | later-credit predicate `£ α` and `tlc_*` lemmas | `base_logic/later_credits.v` |
| `Measure` (with extension measure `∇`, §3.2) | inductive `measure`; `∇` is the constructor `ms_extend`; interpretation into ordinals via `measure_rep_rec` | `algebra/measure.v` |
| layers `ℓ` (ordinals) | `layer`, a notation for `ord.t` from the copy of the Ordinal library in `ordinal/` (two copies of the library sidestep a universe inconsistency); its order is the instance `layer_layer_class` of `layer_class` | `algebra/measure.v`, `algebra/layer.v` |

## 4. Rules (Figs. 3–6, §5)

| Paper rule | Rocq | File (under `lantana/` or `lantana_heap_lang/`) |
|---|---|---|
| STEP-PURE, STEP-PURE-LC, STEP-PURE-WIT | `lwp_pure_step` (the `o : Ord.t` argument grants the `£ α` later credits of STEP-PURE-LC, and parameter `R` is the set of obligations whose status is reported as `witP_cred r Ord.one ∨ oblP_discharged r`) | `program_logic/lifting.v`, heap-lang instance in `lantana_heap_lang/primitive_laws.v` |
| STEP-REF / STEP-STORE / STEP-LOAD | `lwp_alloc` / `lwp_store` / `lwp_load` (each takes the children `G` of the thread, `thP_kids i G`, and burns one unit of fuel of each, at any layer) | `lantana_heap_lang/primitive_laws.v` |
| FORK* | `lwp_fork` (with the lower-level `lwp_fork_step`; the children `K ⊆ G` given to the new thread move with one unit of fuel each) | `lantana_heap_lang/primitive_laws.v` |
| EXIT | the value case of `lwp` (`lwp_value`); `thread_terminate` turns `thP_kids i ∅` into `thP_done i`, which forked threads owe in their postcondition (`lift_term`) | `program_logic/weakestpre.v`, `program_logic/obl_forest.v` |
| FINALLY-EXIT* | `thread_expr_terminate_finally` | `lantana_heap_lang/temporal_laws.v` |
| FINALLY-ALLOC* | `untilI_alloc` with left formula `True` (`finallyI`) | `trace/temporal_formula_rules.v` |
| BIND | `lwp_bind` | `program_logic/weakestpre.v` |
| FRAME, UPD-ELIM | `lwp_strong_mono`, `fupd_lwp` / `lwp_fupd` / `sfmupd_lwp` / `lwp_sfmupd` | `program_logic/weakestpre.v` |
| CARRIER-ALLOC | no carriers: `obl_new` creates an obligation below a parent (a thread or an obligation), and an obligation can itself be a parent | `program_logic/obl_forest.v` |
| CARRIER-DELETE | no carriers: a childless obligation is discharged by `obl_discharge_leaf`; its children can first move up to its parent for free (`obl_move_up`; both: `obl_discharge_lift_kids`) | `program_logic/obl_forest.v`, `program_logic/obl_forest_rules.v` |
| FUELS-ADD / FUELS-UNION / FUELS-EMPTY | `oblP_fuel_add*`, `oblP_fuels_add_obls` / `oblP_fuels_remove_obls`; FUELS-EMPTY is the empty big-op | `program_logic/obl_forest.v`, `program_logic/obl_forest_rules.v` |
| FUELS-LAYER | `oblP_fuel_extend` (and `oblP_fuel_extend_set`) | `program_logic/obl_forest.v`, `program_logic/obl_forest_rules.v` |
| ALWAYS-ALLOC / ALWAYS-ACC | `alwaysI_alloc` / `alwaysI_acc` (`iInv` also opens `alwaysI`); guarantee `guar_alwaysI` | `trace/temporal_formula.v`, `trace/temporal_formula_rules.v`, `base_logic/invariants.v` |
| LÖB | Löb induction of Transfinite Iris (`iLöb`) | (Transfinite Iris) |
| LC-SPEND | `tlc_later`, `tlc_later_strong` | `base_logic/later_credits.v` |
| UNTIL-ALLOC | `untilI_alloc` (or `obl_new`, then `untilI_init`) | `trace/temporal_formula_rules.v` |
| UNTIL-ACC | `untilI_acc` | `trace/temporal_formula_rules.v` |
| UNTIL-DISCHARGE | `untilI_discharge`, `finallyI_discharge` (`untilI_discharge_done` gives the done until) | `trace/temporal_formula_rules.v` |
| UNTIL-DONE-FALSE | `untilI_discharged_false` | `trace/temporal_formula_rules.v` |
| UNTIL-SPLIT | `untilI_frac_split`, `untilI_frac_add` | `trace/temporal_formula_rules.v` |
| WIT-IND | `wit_layer_ind` | `program_logic/obl_forest_rules.v` |
| OBLS-OFFLOAD | `obl_move` (an obligation moves with its subtree to another parent, burning one unit of its own fuel at a layer above the new parent's witness layer, `parP_below`), set versions `obl_move_set_gen` / `obl_move_thread_set` / `obl_move_obl_set` | `program_logic/obl_forest.v`, `program_logic/obl_forest_rules.v` |

## 5. Traces, temporal properties and adequacy (§6, Fig. 7)

| Paper | Rocq | File (under `lantana/`) |
|---|---|---|
| `Cfg`, `TPool`, THREAD-STEP/THREAD-DONE, `Trace`, `Behavior` | `cfg`, `thread_pool`, `thread_step` / `thread_done`, `trace`, `behavior_cfg` / `behavior_tp`; the observations `κ : list (observation Λ)` are carried but never used. Additionally `thread_stuck`: a stuck scheduled thread stutters, so stuck executions are behaviors too | `program_logic/language.v` |
| temporal properties `Φ, Ψ` and `⟦·⟧_t` | trace specifications `trSpec`, trace reading `trSpec_external` (and step-indexed reading `trSpec_internal`); `Always` = `trSpec_always`, `Until` = `trSpec_until`, `Finally` = `trSpec_finally`; meta-level trace predicates `tr_always` / `tr_until` / `tr_eventually` | `trace/trspec.v`, `trace/trace_prop.v` (rules: `trace/trspec_rules.v`, `trace/trace_prop_rules.v`) |
| `Fair` (fair scheduling) | `fair_scheduling` | `trace/fair_scheduling.v` |
| logical assertions `φ` and `⟦·⟧_l` | no syntax: temporal formulas are `iProp`s; guarantee `P ⊨ₜ G` (`guar P G`), inferred by `IntoGuar` | `trace/guarantee.v`, `trace/guarantee_infer.v` |
| `lift` | `trSpec_canon P`, the canonical trace specification guaranteed by `P` (`guar_canon`); `trSpec_inferred P`, the one inferred by `IntoGuar` | `trace/guarantee.v`, `trace/guarantee_infer.v` |
| `Label s e`, `ChooseNat`, atomic property `label_i "s" v` | `Label`, `ChooseNat` (`lantana_heap_lang/lang.v`); atomic properties are state predicates `pointsto_sat` / `thread_expr_sat` (`lantana_heap_lang/lang.v`), read as `trSpec_state`; the assertions `l ↦ v` / `thread_expr i C e` (`exits v @ i`) determine them through the state interpretation (`StateFact` instances, `lantana_heap_lang/temporal_laws.v`), so they guarantee them (`guar_state_fact`, `trace/guarantee_rules.v`) | — |
| `lwp` | `lwp`, notation `lWP e @ s; i; E {{ Φ }}` | `program_logic/weakestpre.v`, `program_logic/lwp_notation.v` |
| obligation state `Ω`, witness state `W` | `obls` (`gmap oid obl`), `witnesses` (`gmap oid witness`); the forest is kept by `oforest` | `base_logic/obligation.v`, `base_logic/witness.v`, `base_logic/oforest.v` |
| model interpretation `M` | `model_interp` (including the forest invariant `oforest` and the model history `model_history_interp`) | `base_logic/mupd.v`, `base_logic/model_history.v` |
| model update modality | `mupd` / `fmupd`; the `lwp`-facing form is the class field `sfmupd` (`\|={E}=>m`), defined at the instance from `fmupd`, and the step modalities are `mprog` / `mphys` | `base_logic/mupd.v`, `program_logic/obl_forest.v`, `program_logic/obl_forest_instance.v`, `base_logic/model_physical_updates.v` |
| fair-scheduler invariant `H` | `owit_inv` | `base_logic/owit.v` |
| state interpretation `S` | `state_interp` (heap-lang instance) and `history_interp` (its wrapper for the adequacy proof) | `lantana_heap_lang/primitive_laws.v`, `program_logic/history_interp.v` |
| Theorem 1 (Adequacy) | `lwp_adequacy_temporal`: from a guarantee `P ⊨ₜ G` of the initial resources, any trace predicate implied by `trSpec_external G` holds on every fair behavior; the weakest preconditions are `NotStuck`, which refutes the stuck behaviors. Iris-style safety `lwp_adequacy_safety_iris`: on the same fair behaviors, the scheduled thread is never stuck, and whenever the chosen thread is a value, its postcondition holds | `trace/adequacy_temporal.v`, `trace/adequacy_safety.v` |

In the development, a guarantee turns its formula into a *record* (`record G n`) of what the
formula holds at position `n`, and before every step the proof of Theorem 1 *certifies* every
registered temporal formula (`reg_check`); the records and certificates are then read off the
run. `lantana/trace/README.md` lists the files.

## 6. Case studies (§2–§7)

All in `lantana_heap_lang/examples/`.

| Paper | Rocq | File |
|---|---|---|
| Flag module: `init`/`set`/`wait`; `isFlag`; `FlagObl`; SPEC-INIT/SPEC-SET/SPEC-WAIT | `init`/`set`/`wait`; `is_flag` (guarantee `guar_is_flag`, trace specification `flag_trSpec`); `flag_tk`; `Flag_init_spec` / `Flag_set_spec` / `Flag_wait_spec` | `flag.v` |
| `main` (§2) and its trace property | `main`, `FlagFork_main_spec`, end-to-end `main_adequacy` | `flag_fork.v` |
| `nest` / `nondet` (§4.3); SPEC-NEST/SPEC-NONDET | `nest` / `nondet`; `Nondet_nest_spec` / `Nondet_nondet_spec` | `nondet.v` |
| Handoff: `send`/`receive`; `HandoffBuf`; `isHandoff`; `TaskSpec`; SPEC-SEND/SPEC-RECEIVE | `send`/`receive`; `handoff_inv`; `is_handoff`; `is_task`; `Handoff_send_spec` / `Handoff_receive_spec` | `handoff.v` |
| `handoffMain` (§5.2); SPEC-HANDOFF-MAIN | `main`, `main_spec`, `handoff_client_adequacy` | `handoff_client.v` |
| Ticket lock (§7.1): `TLInv`; `TLObl`; SPEC-ACQUIRE/SPEC-RELEASE | `is_fair_lock`; `lock_token`; `TicketLock_init_spec` / `TicketLock_acquire_spec` / `TicketLock_release_spec` (more general than the paper's specifications) | `ticket_lock.v` |
| Queue (§7.2): `QInv` (`QData`/`QState`/`QObls`/`QPrimary`); SPEC-ENQUEUE/SPEC-DEQUEUE | `is_queue` (with `queue_worker` for the primary); `Queue_init_spec` / `Queue_enqueue_spec` / `Queue_dequeue_spec` | `queue.v` |
| Task queue (§7.3): `TQInv`; SPEC-PUT-TASK/SPEC-WORKER | `is_task_queue`; `TaskQueue_init_spec` / `TaskQueue_put_task_spec` / `TaskQueue_run_task_spec` / `TaskQueue_worker_spec` | `task_queue.v` |
| Reentrant client `decr` / `clientMain` (§7.3); SPEC-DECR/SPEC-DECR-CLIENTMAIN | `decr_reentrant` / `main`; `decr_reentrant_spec` / `main_spec`; `task_queue_client_adequacy` | `task_queue_client.v` |

### End-to-end theorems

Each client program has three, over all fair behaviors from its initial configuration:

- `*_adequacy` instantiates Theorem 1 (`lwp_adequacy_temporal`) and gives a trace property of the
  program (`main_adequacy`, `flag_client_adequacy`, `handoff_client_adequacy`,
  `task_queue_client_adequacy`, and for the examples beyond the paper `ticket_lock_client_adequacy`
  and `cert_discharge_adequacy`). `flag_client.v` proves a property about a memory location,
  beyond termination.
- `*_safety_adequacy` instantiates `lwp_adequacy_safety_iris`: the scheduled thread is never
  stuck, and a returned thread has its return value.
- `*_liveness_safety` states both.

### Unsound rules

`paradox.v` proves the unsoundness counterexample remarked at the end of §6.2 (`no_lc_absurd`):
a HeapLang rule for one pure step without fuel would be unsound.

### Beyond the paper

- `nonstrict_move.v` shows that moving an obligation below an obligation of the same layer would
  be unsound (`nonstrict_move_absurd`).
- `ticket_lock2.v` / `ticket_lock2_client.v` give a starvation-free ticket lock
  (`fair_lock_starvation_free`, `ticket_lock_client_adequacy`).
- `cert_discharge.v` tests a discharge in the pre-step model update with nested temporal formulas
  (`cert_discharge_adequacy`).
- `flag_stable.v` (with `flag_stable_client.v`, `handoff_flag_stable_client.v`,
  `task_queue_flag_stable_client.v`) is a flag whose set value lives in a nested `alwaysI`, so it
  stays set (`flag_trSpec_stays`).
- `ticket_lock_mono.v` exports that `next` never decreases, so a lock that cannot be deleted is
  starvation free (`alive_fair_lock_starvation_free`).

## 7. Checking the results

Building the development (`make`, see [README.md](README.md#building)) checks every proof. To
read a statement, open the files in an editor with Rocq support at the root of the repository,
or, after `make`:

```
rocq top -Q ordinal lantana.ordinal -Q lantana lantana -Q lantana_heap_lang lantana.heap_lang
Require Import lantana.trace.adequacy_temporal.
Check lwp_adequacy_temporal.
```

Nothing is admitted. The adequacy theorems, the end-to-end theorems of the clients,
`no_lc_absurd` and `nonstrict_move_absurd` depend only on seven axioms of Rocq's standard
library; [README.md](README.md#axioms-and-admits) lists them and shows how to check them with
`Print Assumptions`.
