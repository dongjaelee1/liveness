### Installation

The development depends on the following opam packages:

* Rocq 9.0 -- 9.3 (`rocq-core`, `rocq-stdlib`)
* std++ `dev.2026-09-17.0.d510b616` (`rocq-stdpp`)
* Iris (`rocq-iris`, `rocq-iris-heap-lang`) from the branch
  [`dongjae/transfinite-base`](https://gitlab.mpi-sws.org/dongjae/iris/-/tree/dongjae/transfinite-base),
  which is upstream Iris master (commit `8e490959`) plus the commits of the Iris branch
  `robbert/transfinite` that change the BI laws to support transfinite step-indexing
* [Transfinite Iris](https://github.com/dongjaelee1/transfinite-iris) (`rocq-iris-transfinite`)
* The Ordinal library `coq-ordinal.0.5.6`

1. Set up a new opam switch and switch to it:
  ```
  opam update
  opam switch create lantana 5.2.1
  eval $(opam env)
  ```

2. Run the configure script:
  ```
  ./configure
  ```
  This adds the `coq-released` and `iris-dev` opam repositories, pins Iris and
  Transfinite Iris to the commits listed at the top of `configure`, and installs
  all of the packages above. Set `NJOBS` to control build parallelism (default 8),
  e.g. `NJOBS=4 ./configure`. To use another commit of Transfinite Iris, set
  `TRANSFINITE_REPO`/`TRANSFINITE_REF`; the Iris commit in `configure` must match the
  one that Transfinite Iris's opam file pins in its `pin-depends`.

3. Run `make -jN` to build the full development, where `N` is the number of
   threads to use for the build process.

## Acknowledgements

The `lantana/ordinal/` directory is a copy of the Ordinal library, available at
https://github.com/snu-sf/Ordinal.

(Transfinite Iris) The mechanization of set-theoretic ordinals and the underlying ZF model construction 
has been based on Coq code by Dominik Kirst and Gert Smolka, available at: 

* "Large Model Constructions for Second-Order ZF in Dependent Type Theory"
  by Dominik Kirst and Gert Smolka, CPP 2018
  See https://www.ps.uni-saarland.de/Publications/details/KirstSmolka:2017:Large-Model.html.
* "Formalised Set Theory: Well-Orderings and the Axiom of Choice", Dominik Kirst. 
  See https://www.ps.uni-saarland.de/~kirst/bachelor.php 

## Structure of the development

Each directory imports only from the directories listed before it:

| Directory | Contents |
| --- | --- |
| `lantana/ordinal/` | a copy of the Ordinal library (see Acknowledgements) |
| `lantana/algebra/` | Rocq-level mathematics: ordinals and well-founded structures, ordered commutative monoids, measures and layers, and the cameras used by the logic |
| `lantana/base_logic/` | the `iProp`-level model of Lantana: transfinite later credits, fancy updates and invariants, and the obligation model (obligations and witnesses, their ghost state, the obligation forest, model updates `mupd`, and the predicates of §3–§5 in `base_logic/opreds.v`) |
| `lantana/program_logic/` | languages and the thread-local weakest precondition `lwp`: its definition, lifting lemmas, the model update `sfmupd` usable inside `lwp` proofs, and the obligation-forest interface |
| `lantana/trace/` | traces and temporal properties, temporal guarantees `P ⊨ₜ G` (always, until, finally), and the adequacy theorems |
| `lantana_heap_lang/` | HeapLang for Lantana, its proof mode, and the case studies in `examples/` |

## Correspondence between the paper and the Rocq development

**The most important difference:** the paper presents Lantana through the
*fuel-burning triple* `{P}^G e {Q}^G'`, but the Rocq development is mostly
stated in terms of the thread-local weakest precondition `lwp` (notation
`lWP e @ s; i; E {{ Φ }}` from `lantana/program_logic/lwp_notation.v`, defined in
`lantana/program_logic/weakestpre.v`).
The triple is a thin wrapper defined on top of `lwp` in
`lantana/trace/fuel_burning_triple.v`:

```
fuel_burning_triple s i E G G' P e Q :=
  ∀ Φ, (thP_kids i G ∗ P) -∗ (∀ v, thP_kids i G' ∗ Q v -∗ Φ v) -∗
       lWP e @ s; i; E {{ Φ }}
```

That is, the paper's carrier-set superscripts `G`/`G'` become ordinary
assertions `thP_kids i G` (the obligations directly below thread `i`, see below)
threaded through the pre/postcondition. Rules
that the paper states for the triple therefore appear in the development
either as `lwp_*` lemmas, as entailments between the underlying predicates or model
updates `|={E}=>m` on them (usable at any point of an `lwp` proof, see `sfmupd_lwp` /
`lwp_sfmupd`), or — for a few key rules — as
packaged `fuel_burning_triple_*` lemmas. Likewise, the case-study
specifications are stated as `lwp` (texan-style `l{{{ ... }}}`) triples with
explicit `thP_kids`/`parP_kids`/`oblP_fuel` assertions rather than
carrier-set superscripts.

**Further differences.** The development has evolved since the paper:

* *No carriers; obligations form a forest.* The parent of an obligation is a thread or
  another obligation (`PThread i` / `PObl k`, `base_logic/parent.v`), and `parP_kids p K`
  says that the children of `p` are `K`. A step of thread `i` burns one unit of fuel of each
  child of `i`; the model keeps the fuel of every obligation above the fuel of its parent, so
  the obligations further below make progress too. An obligation changes its parent by
  burning one unit of its own fuel (`obl_move`), so obligation fuel `oblP_fuel` is the only
  kind of fuel. The rules are model updates in `base_logic/opreds.v` and, with the program
  state, `|={E}=>m` updates in `program_logic/sfmupd.v`; `program_logic/obl_forest.v` states
  them as an abstract interface `oblf.obl_forest_interface` (instance `obl_forest_lantana`
  in `program_logic/obl_forest_instance.v`).
* *Temporal formulas are iProps.* There is no syntax of temporal formulas: `alwaysI`,
  `untilI` and `finallyI` are ordinary `iProp`s, and a persistent *guarantee* `P ⊨ₜ G` states
  that whenever `P` holds, the rest of the execution satisfies the semantic trace property
  `G` (`tps`). Guarantees are inferred by `IntoTemporal` instances, and adequacy concludes the
  trace reading `tps_tr G` (`trace/temporal_guarantee.v`).

Naming conventions: `oblP_*` are obligation predicates, `witP_*` witness predicates,
`thP_*` per-thread predicates, `parP_*` predicates on parents (`thP_kids i K` and
`oblP_kids k K` are `parP_kids` at a thread and at an obligation), `alwaysI`/`untilI`/`finallyI`
temporal formulas (iProps), `tps_*` semantic trace properties, and `tr_*` meta-level trace
predicates.

### Predicates (Fig. 1, §3–§5)

| Paper | Rocq | File (under `lantana/`) |
|---|---|---|
| `{P}^G_i e {Q}^G'_E` (fuel-burning triple) | `fuel_burning_triple` (and `fuel_burning_triple_persistent` for the `□`-specification format of §3.4) | `trace/fuel_burning_triple.v` |
| carrier superscripts / `carriers_i G` (Thm 1) | no carriers: `thP_kids i G`, the children of thread `i` in the obligation forest; every initial thread starts with `thP_kids i ∅` | `base_logic/opreds.v` |
| `Fuel^ℓ_G μ` | no carrier fuel: `oblP_fuel k ℓ μ` of each child `k` of the thread; a set is `[∗ set] k ∈ G, oblP_fuel k ℓ μ` (cf. `oblP_fuels`) | `base_logic/opreds.v` |
| `obls^ℓ_g K` | replaced by `parP_kids p K` (children `K` of a thread, `thP_kids i K`, or of an obligation, `oblP_kids k K`); below an obligation the layer bound is its witness layer (`parP_below` / `parP_le`) | `base_logic/opreds.v` |
| `Φ until^k_q Ψ` | `untilI N k q P Q` (an `iProp`; `N` is the namespace of the obligation invariant `oblP_inv` of `k`; variant `untilI_guar` with given readings, e.g. for recursion, `renew` in `trace/temporal_fixpoint.v`); guarantee `temporal_until` | `trace/temporal_guarantee.v` |
| `finally^k Φ` | `finallyI N k q Q` (`untilI N k q True Q`) | `trace/temporal_guarantee.v` |
| `obl∎ k` (discharged) | `oblP_discharged k` | `base_logic/opreds.v` |
| `tr$^ℓ_k m` (transfer credit) | `oblP_fuel k ℓ m` (the obligation's own fuel, now the only kind of fuel) | `base_logic/opreds.v` |
| `wit^ℓ k` (witness) | `witP_layer k ℓ` | `base_logic/opreds.v` |
| `wit€ k` (witness credit, §4.1) | `witP_cred k a` (`a` an ordinal amount; a step gives `witP_cred k Ord.one`) | `base_logic/opreds.v` |
| `∎ i` (thread finished, Thm 1) | `thP_done i` | `base_logic/opreds.v` |
| `always I` | `alwaysI N I` (a registered invariant; variants `alwaysI_as`, `alwaysI_guar`); guarantee `temporal_always` | `trace/temporal_guarantee.v`, `base_logic/invariants.v` |
| `£ α` (transfinite later credits) | later-credit predicate `£ α` and `tlc_*` lemmas | `base_logic/later_credits.v` |
| `Measure` (with extension measure `∇`, §3.2) | inductive `measure`; `∇` is the constructor `ms_extend`; interpretation into ordinals via `measure_rep_rec` | `algebra/measure.v` |
| layers `ℓ` (ordinals) | `layer_class` (instance `layer_layer_class`), over `ord.t` from the Ordinal library (we use two Ordinal libraries to sidestep universe inconsistency) | `algebra/measure.v`, `algebra/layer.v` |

### Rules (Figs. 3–6, §5)

| Paper rule | Rocq | File (under `lantana/` or `lantana_heap_lang/`) |
|---|---|---|
| STEP-PURE, STEP-PURE-LC, STEP-PURE-WIT | `lwp_pure_step` (the `o : Ord.t` argument grants the `£ α` later credits of STEP-PURE-LC, and parameter `R` is the set of obligations whose status is reported as `witP_cred r Ord.one ∨ oblP_discharged r`) | `program_logic/lifting.v`, heap-lang instance in `lantana_heap_lang/primitive_laws.v` |
| STEP-REF / STEP-STORE / STEP-LOAD | `lwp_alloc` / `lwp_store` / `lwp_load` (each takes the children `G` of the thread, `thP_kids i G`, and burns one unit of fuel of each, at any layer) | `lantana_heap_lang/primitive_laws.v` |
| FORK* | `lwp_fork` (with the lower-level `lwp_fork_step`; the children `K ⊆ G` given to the new thread move with one unit of fuel each) | `lantana_heap_lang/primitive_laws.v` |
| EXIT | the value case of `lwp` (`lwp_value`); `thread_terminate` turns `thP_kids i ∅` into `thP_done i`, which forked threads owe in their postcondition (`lift_term`) | `program_logic/weakestpre.v`, `program_logic/sfmupd.v` |
| FINALLY-EXIT* | `thread_expr_terminate_finally` | `lantana_heap_lang/temporal_laws.v` |
| FINALLY-ALLOC* | `untilI_alloc` with left formula `True` (`finallyI`) | `trace/temporal_guarantee.v` |
| BIND | `lwp_bind` | `program_logic/weakestpre.v` |
| FRAME, UPD-ELIM | `lwp_strong_mono`, `fupd_lwp` / `lwp_fupd` / `sfmupd_lwp` / `lwp_sfmupd` | `program_logic/weakestpre.v` |
| CARRIER-ALLOC | no carriers: `obl_new` creates an obligation below a parent (a thread or an obligation), and an obligation can itself be a parent | `program_logic/sfmupd.v` |
| CARRIER-DELETE | no carriers: a childless obligation is discharged by `obl_discharge_leaf`; its children can first move up to its parent for free (`obl_move_up`; both: `obl_discharge_lift_kids`) | `program_logic/sfmupd.v` |
| FUELS-ADD / FUELS-UNION / FUELS-EMPTY | `oblP_fuel_add*`, `oblP_fuels_add_obls` / `oblP_fuels_remove_obls`; FUELS-EMPTY is the empty big-op | `base_logic/opreds.v` |
| FUELS-LAYER | `oblP_fuel_extend` (and `oblP_fuel_extend_set`) | `base_logic/opreds.v` |
| ALWAYS-ALLOC / ALWAYS-ACC | `alwaysI_alloc` / `alwaysI_acc` (`iInv` also opens `alwaysI`); guarantee `temporal_always` | `trace/temporal_guarantee.v`, `base_logic/invariants.v` |
| LÖB | Löb induction of Transfinite Iris (`iLöb`) | (Transfinite Iris) |
| LC-SPEND | `tlc_later`, `tlc_later_strong` | `base_logic/later_credits.v` |
| UNTIL-ALLOC | `untilI_alloc`; triple-level `fuel_burning_triple_until_alloc` | `trace/temporal_guarantee.v`, `trace/fuel_burning_triple.v` |
| UNTIL-ACC | `untilI_acc` | `trace/temporal_guarantee.v` |
| UNTIL-DISCHARGE | `untilI_discharge`; triple-level `fuel_burning_triple_until_discharge` | `trace/temporal_guarantee.v`, `trace/fuel_burning_triple.v` |
| UNTIL-DONE-FALSE | `untilI_discharged_false` | `trace/temporal_guarantee.v` |
| UNTIL-SPLIT | `untilI_frac_split`, `untilI_frac_add` | `trace/temporal_guarantee.v` |
| WIT-IND | `fuel_burning_triple_wit_ind`; underlying `wit_layer_ind` | `trace/fuel_burning_triple.v`, `base_logic/opreds.v` |
| OBLS-OFFLOAD | `obl_move` (an obligation moves with its subtree to another parent, burning one unit of its own fuel at a layer above the new parent's witness layer, `parP_below`), set versions `obl_move_set_gen` / `obl_move_thread_set` / `obl_move_obl_set` | `program_logic/sfmupd.v` |

### Traces, temporal properties, and adequacy (§6, Fig. 7)

| Paper | Rocq | File (under `lantana/`) |
|---|---|---|
| `Cfg`, `TPool`, THREAD-STEP/THREAD-DONE, `Trace`, `Behavior` | `cfg`, `thread_pool`, `thread_step` / `thread_done`, `trace`, `behavior_cfg` / `behavior_tp` (please ignore `κ : list (observation Λ)`, which is never used) | `program_logic/language.v` |
| temporal properties `Φ, Ψ` and `⟦·⟧_t` | semantic trace properties `tps`, trace reading `tps_tr` (and step-indexed reading `tps_ti`); `Always` = `tps_always`, `Until` = `tps_until`, `Finally` = `tps_finally`; meta-level trace predicates `tr_always` / `tr_until` / `tr_eventually` | `trace/temporal_tps.v`, `trace/temporal_property.v` |
| `Fair` (fair scheduling) | `fair_scheduling` | `trace/temporal_property.v` |
| logical assertions `φ` and `⟦·⟧_l` | no syntax: temporal formulas are `iProp`s; guarantee `P ⊨ₜ G` (`temporal P G`), inferred by `IntoTemporal` | `trace/temporal_guarantee.v` |
| `lift` | `tps_sem P`, the canonical trace property guaranteed by `P` (`temporal_sem`); `tsem P`, the one inferred by `IntoTemporal` | `trace/temporal_guarantee.v` |
| `Label s e`, `ChooseNat`, atomic property `label_i "s" v` | `Label`, `ChooseNat` (`lantana_heap_lang/lang.v`); atomic properties are state predicates `pred_pointsto` / `pred_expr` (`lantana_heap_lang/lang.v`), owned as `l ↦ v` / `thread_expr i C e` (`exits v @ i`, `lantana_heap_lang/primitive_laws.v`), guaranteeing `tps_atomic` (`lantana_heap_lang/temporal_laws.v`) | — |
| `lwp` | `lwp`, notation `lWP e @ s; i; E {{ Φ }}` | `program_logic/weakestpre.v`, `program_logic/lwp_notation.v` |
| obligation state `Ω`, witness state `W` | `obls` (`gmap oid obl`), `witnesses` (`gmap oid witness`); the forest is kept by `oforest` | `base_logic/obligation.v`, `base_logic/witness.v`, `base_logic/oforest.v` |
| model interpretation `M` | `model_interp` (including the forest invariant `oforest` and the model history `model_history_interp`) | `base_logic/mupd.v`, `base_logic/model_history.v` |
| model update modality | `mupd` / `fmupd`; the `lwp`-facing form is `sfmupd`, and the step modalities are `mprog` / `mphys` | `base_logic/mupd.v`, `program_logic/sfmupd.v`, `base_logic/model_physical_updates.v` |
| fair-scheduler invariant `H` | `owit_inv` | `base_logic/owit.v` |
| state interpretation `S` | `state_interp` (heap-lang instance) and `history_interp` (wrapper for adequacy proof) | `lantana_heap_lang/primitive_laws.v`, `program_logic/history_interp.v` |
| **Theorem 1 (Adequacy)** | `lwp_adequacy_temporal` (from a guarantee `P ⊨ₜ G` of the initial resources, any trace predicate implied by `tps_tr G`); Iris-style safety variant `lwp_adequacy_safety_iris` | `trace/guarantee_adequacy.v`, `trace/adequacy_iris.v` |

### Case studies (§2 to §7)

All in `lantana_heap_lang/examples/`.

| Paper | Rocq | File |
|---|---|---|
| Flag module: `init`/`set`/`wait`; `isFlag`; `FlagObl`; SPEC-INIT/SPEC-SET/SPEC-WAIT | `init`/`set`/`wait`; `is_flag` (guarantee `is_flag_temporal`, trace property `flag_tps`); `flag_tk`; `Flag_init_spec` / `Flag_set_spec` / `Flag_wait_spec` | `flag.v` |
| `main` (§2) and its trace property | `main`, `FlagFork_main_spec`, end-to-end `main_adequacy` | `flag_fork.v` |
| `nest` / `nondet` (§4.3); SPEC-NEST/SPEC-NONDET | `nest` / `nondet`; `Nondet_nest_spec` / `Nondet_nondet_spec` | `nondet.v` |
| Handoff: `send`/`receive`; `HandoffBuf`; `isHandoff`; `TaskSpec`; SPEC-SEND/SPEC-RECEIVE | `send`/`receive`; `handoff_inv`; `is_handoff`; `is_task`; `Handoff_send_spec` / `Handoff_receive_spec` | `handoff.v` |
| `handoffMain` (§5.2); SPEC-HANDOFF-MAIN | `main`, `main_spec`, `handoff_client_adequacy` | `handoff_client.v` |
| Ticket lock (§7.1): `TLInv`; `TLObl`; SPEC-ACQUIRE/SPEC-RELEASE | `is_fair_lock`; `lock_token`; `TicketLock_init_spec` / `TicketLock_acquire_spec` / `TicketLock_release_spec` (the specifications in Rocq are more generalized than ones in the paper) | `ticket_lock.v` |
| Queue (§7.2): `QInv` (`QData`/`QState`/`QObls`/`QPrimary`); SPEC-ENQUEUE/SPEC-DEQUEUE | `is_queue` (with `queue_worker` for the primary); `Queue_init_spec` / `Queue_enqueue_spec` / `Queue_dequeue_spec` | `queue.v` |
| Task queue (§7.3): `TQInv`; SPEC-PUT-TASK/SPEC-WORKER | `is_task_queue`; `TaskQueue_init_spec` / `TaskQueue_put_task_spec` / `TaskQueue_run_task_spec` / `TaskQueue_worker_spec` | `task_queue.v` |
| Reentrant client `decr` / `clientMain` (§7.3); SPEC-DECR/SPEC-DECR-CLIENTMAIN | `decr_reentrant` / `main`; `decr_reentrant_spec` / `main_spec`; `task_queue_client_adequacy` | `task_queue_client.v` |

The per-example `*_adequacy` theorems (`flag_client_adequacy`, `main_adequacy`,
`handoff_client_adequacy`, `task_queue_client_adequacy`) are end-to-end
instantiations of Theorem 1 (`lwp_adequacy_temporal`), deriving the trace-level temporal
property of the respective client program.
`flag_client.v` uses adequacy to prove a property about a memory location, beyond termination.
`paradox.v` proves the unsoundness counterexample remarked at the end of §6.2
(`no_lc_absurd`). Beyond the paper: `nonstrict_move.v` shows that moving an obligation below
an obligation of the same layer would be unsound (`nonstrict_move_absurd`);
`ticket_lock2.v` / `ticket_lock2_client.v` give a starvation-free ticket lock
(`fair_lock_starvation_free`, `ticket_lock_client_adequacy`); `cert_discharge.v` tests a
discharge in the pre-step model update with nested temporal formulas
(`cert_discharge_adequacy`).
