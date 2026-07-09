### Installation

The development depends on std++ (version `dev.2025-07-31.0.8c814126`, i.e.,
upstream commit `8c814126`), parametric Iris, and transfinite Iris, whose
sources are bundled in this repository as `stdpp.zip`,
`iris-parametric-index.zip`, and `transfinite-parametric-index.zip`, so no
access to their upstream repositories is needed.

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
  This installs Coq 9.0.0 and the Ordinal library via opam, and then unpacks
  the bundled zip files into `vendor/` and builds and installs std++,
  parametric Iris, and transfinite Iris from them. Set `NJOBS` to control
  build parallelism (default 8), e.g. `NJOBS=4 ./configure`.

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

## Correspondence between the paper and the Rocq development

**The most important difference:** the paper presents Lantana through the
*fuel-burning triple* `{P}^G_i e {Q}^G'`, but the Rocq development is mostly
stated in terms of the thread-local weakest precondition `lwp` (notation
`lWP e @ s; i; E {{ Φ }}`, defined in `lantana/program_logic/weakestpre.v`).
The triple is a thin wrapper defined on top of `lwp` in
`lantana/program_logic/fuel_burning_triple.v`:

```
fuel_burning_triple s i E G G' P e Q :=
  ∀ Φ, (thP_carriers i G ∗ P) -∗ (∀ v, thP_carriers i G' ∗ Q v -∗ Φ v) -∗
       lWP e @ s; i; E {{ Φ }}
```

That is, the paper's carrier-set superscripts `G`/`G'` become ordinary
assertions `thP_carriers i G` threaded through the pre/postcondition. Rules
that the paper states for the triple therefore appear in the development
either as `lwp_*` lemmas, as entailments between the underlying predicates
(usable at any point of an `lwp` proof), or — for a few key rules — as
packaged `fuel_burning_triple_*` lemmas. Likewise, the case-study
specifications are stated as `lwp` (texan-style `l{{{ ... }}}`) triples with
explicit `thP_carriers`/`crP_fuel`/`crP_obls` assertions rather than
carrier-set superscripts.

Naming conventions: `crP_*` are carrier predicates, `oblP_*` obligation
predicates, `witP_*` witness predicates, `thP_*` per-thread predicates,
`tf_*` the syntax of separation-logic temporal formulas (interpreted into
`iProp` by `⟦·⟧ₗ`), and `tp`/`tr_*` meta-level temporal trace properties.

### Predicates (Fig. 1, §3–§5)

| Paper | Rocq | File (under `lantana/`) |
|---|---|---|
| `{P}^G_i e {Q}^G'_E` (fuel-burning triple) | `fuel_burning_triple` (and `fuel_burning_triple_persistent` for the `□`-specification format of §3.4) | `program_logic/fuel_burning_triple.v` |
| carrier superscripts / `carriers_i G` (Thm 1) | `thP_carriers i G` | `base_logic/opreds.v` |
| `Fuel^ℓ_G μ` | `crP_fuel g ℓ μ` for one carrier; a set is `[∗ set] g ∈ G, crP_fuel g ℓ μ` (cf. `crP_fuels`) | `base_logic/opreds.v` |
| `obls^ℓ_g K` | `crP_obls g ℓ K` | `base_logic/opreds.v` |
| `Φ until^k_q Ψ` | `tf_until N k b q P Q`, notation `untilP N k q P Q` (`N` is the invariant namespace; the flag `b` records whether the until is in the "accessed" state of UNTIL-ACC) | `program_logic/temporal_logic.v` |
| `finally^k Φ` | `tf_finally`, notation `finallyP N k q Q` | `program_logic/temporal_logic.v` |
| `obl∎ k` (discharged) | `oblP_discharged k` | `base_logic/opreds.v` |
| `tr$^ℓ_k m` (transfer credit) | `oblP_fuel k ℓ m` (the obligation's own fuel) | `base_logic/opreds.v` |
| `wit^ℓ k` (witness) | `witP_layer k ℓ` | `base_logic/opreds.v` |
| `wit€ k` (witness credit, §4.1) | `witP_cred k μ` | `base_logic/opreds.v` |
| `∎ i` (thread finished, Thm 1) | `thP_done i` | `base_logic/opreds.v` |
| `always I` | `tf_always` (with the invariant machinery of `base_logic/invariants.v`) | `program_logic/temporal_logic.v` |
| `£ α` (transfinite later credits) | later-credit predicate and `tlc_*` lemmas | `base_logic/later_credits.v` |
| `Measure` (with extension measure `∇`, §3.2) | inductive `measure`; `∇` is the constructor `ms_extend`; interpretation into ordinals via `measure_rep_rec` | `algebra/measure.v` |
| layers `ℓ` (ordinals) | `layer_class`, over `Ord.t` from the Ordinal library | `algebra/layer.v` |

### Rules (Figs. 3–6, §5)

| Paper rule | Rocq | File (under `lantana/` or `lantana_heap_lang/`) |
|---|---|---|
| STEP-PURE, STEP-PURE-LC | `lwp_pure_step` (the `o : Ord.t` argument grants the `£ α` later credits of STEP-PURE-LC) | `program_logic/lifting.v`, heap-lang instance in `lantana_heap_lang/primitive_laws.v` |
| STEP-PURE-WIT | `lwp_pure_step_alt` (parameter `R` is the set of obligations whose status is reported as `witP_cred r 1 ∨ oblP_discharged r`) | `program_logic/lifting.v` |
| STEP-REF / STEP-STORE / STEP-LOAD | `lwp_alloc` / `lwp_store` / `lwp_load` (each takes the carrier set `G` and burns one unit of layer-0 fuel) | `lantana_heap_lang/primitive_laws.v` |
| FORK* | `lwp_fork` (with the lower-level `lwp_fork_step`) | `lantana_heap_lang/primitive_laws.v` |
| EXIT | the value case of `lwp` (see `lwp_value_*` lemmas; the empty carrier set yields `thP_done i`) | `program_logic/weakestpre.v` |
| FINALLY-EXIT* | `lwp_exit` | `lantana_heap_lang/primitive_laws.v` |
| FINALLY-ALLOC* | `tf_until_alloc` instantiated with `finallyP` | `program_logic/temporal_logic.v` |
| BIND | `lwp_bind` | `program_logic/weakestpre.v` |
| FRAME, UPD-ELIM | `lwp_strong_mono`, `fupd_lwp` / `lwp_fupd` / `sfgupd_elim_lwp` | `program_logic/weakestpre.v` |
| CARRIER-ALLOC | `fuel_burning_triple_carrier_alloc`; underlying `carrier_alloc_gupd` | `program_logic/fuel_burning_triple.v`, `base_logic/opreds.v` |
| CARRIER-DELETE | `carrier_delete_gupd` | `base_logic/opreds.v` |
| FUELS-ADD / FUELS-UNION / FUELS-EMPTY | `crP_fuel_add*`, `crP_fuels_add_carriers` / `crP_fuels_remove_carriers`; FUELS-EMPTY is the empty big-op | `base_logic/opreds.v` |
| FUELS-LAYER | `crP_fuel_layer_mon` (and `crP_fuel_layer_eq`); obligation-fuel analogue `oblP_fuel_layer_mon` | `base_logic/opreds.v` |
| ALWAYS-ALLOC / ALWAYS-ACC | `tf_always_logic` together with the invariant allocation/access lemmas | `program_logic/temporal_logic.v`, `base_logic/invariants.v` |
| LÖB | Löb induction of Transfinite Iris (`iLöb`) | (Transfinite Iris) |
| LC-SPEND | `tlc_later`, `tlc_later_strong` | `base_logic/later_credits.v` |
| UNTIL-ALLOC | `tf_until_alloc`; triple-level `fuel_burning_triple_until_alloc` | `program_logic/temporal_logic.v`, `program_logic/fuel_burning_triple.v` |
| UNTIL-ACC | `tf_until_acc`, `tf_until_to_true` | `program_logic/temporal_logic.v` |
| UNTIL-DISCHARGE | `tf_until_discharge`, `tf_until_true_to_discharge`; triple-level `fuel_burning_triple_until_discharge` | `program_logic/temporal_logic.v`, `program_logic/fuel_burning_triple.v` |
| UNTIL-DONE-FALSE | `tf_until_discharged_false` | `program_logic/temporal_logic.v` |
| UNTIL-SPLIT | `tf_until_frac_split`, `tf_until_frac_add` | `program_logic/temporal_logic.v` |
| WIT-IND | `fuel_burning_triple_wit_ind` | `program_logic/fuel_burning_triple.v` |
| OBLS-OFFLOAD | `obl_offload_gupd`, `obl_offload_set_gupd` | `base_logic/opreds.v` |

### Traces, temporal properties, and adequacy (§6, Fig. 7)

| Paper | Rocq | File (under `lantana/`) |
|---|---|---|
| `Cfg`, `TPool`, THREAD-STEP/THREAD-DONE, `Trace`, `Behavior` | `cfg`, `thread_pool`, `thread_step`, `trace`, `behavior_cfg` / `behavior_tp` | `program_logic/language.v` |
| temporal properties `Φ, Ψ` and `⟦·⟧_t` | syntax `tp`, interpretation `tp_trace`; `Always` = `tr_always`, `Until` = `tr_until`, `Finally` = `tr_eventually` | `program_logic/temporal_property.v` |
| `Fair` (fair scheduling) | `fair_scheduling` | `program_logic/temporal_property.v` |
| logical assertions `φ` and `⟦·⟧_l` | syntax `tf`, interpretation `⟦·⟧ₗ` | `program_logic/temporal_logic.v` |
| `lift` | `tf_to_tp` | `program_logic/adequacy.v` |
| `Label s e`, `ChooseNat`, atomic property `label_i "s" v` | `Label`, `ChooseNat` (`lantana_heap_lang/lang.v`); `label` predicate (`lantana_heap_lang/primitive_laws.v`) | — |
| `lwp` | `lwp`, notation `lWP e @ s; i; E {{ Φ }}` | `program_logic/weakestpre.v` |
| obligation state `Ω`, witness state `W` | `obls` (`gmap oid obl`), witness maps in `owit` | `base_logic/obligation.v`, `base_logic/owit.v` |
| model interpretation `M` | `model_history_interp` | `base_logic/model_interp.v` |
| model update modality | `mupd` / `fmupd`; the `lwp`-facing forms are `sfmupd` (`|={E}=>m`) and `sfgupd` (`|={E}=>g`) | `base_logic/mupd.v`, `program_logic/sfmupd.v`, `program_logic/sfgupd.v` |
| fair-scheduler invariant `H` | `owit_inv` | `base_logic/owit.v` |
| state interpretation `S` | `state_interp` (heap-lang instance) | `lantana_heap_lang/primitive_laws.v` |
| **Theorem 1 (Adequacy)** | `lwp_adequacy`; Iris-style safety variant `lwp_adequacy_safety_iris` | `program_logic/adequacy.v`, `program_logic/adequacy_iris.v` |

### Case studies (§2, §7)

All in `lantana_heap_lang/examples/`.

| Paper | Rocq | File |
|---|---|---|
| Flag module: `init`/`set`/`wait`; `isFlag`; `FlagObl`; SPEC-INIT/SPEC-SET/SPEC-WAIT | `init`/`set`/`wait`; `is_flag` (syntactic form `is_flag_tf`); `flag_tk`; `Flag_init_spec` / `Flag_set_spec` / `Flag_wait_spec` | `flag.v` |
| `main` (§2) and its trace property | `main`, `FlagFork_main_spec`, end-to-end `main_adequacy` | `flag_fork.v` |
| `nest` / `nondet` (§4.3); SPEC-NEST/SPEC-NONDET | `nest` / `nondet`; `Nondet_nest_spec` / `Nondet_nondet_spec` | `nondet.v` |
| Handoff: `send`/`receive`; `HandoffBuf`; `isHandoff`; `TaskSpec`; SPEC-SEND/SPEC-RECEIVE | `send`/`receive`; `handoff_inv`; `is_handoff`; `is_task`; `Handoff_send_spec` / `Handoff_receive_spec` | `handoff.v` |
| `handoffMain` (§5.2); SPEC-HANDOFF-MAIN | `main`, `main_spec`, `handoff_client_adequacy` | `handoff_client.v` |
| Ticket lock (§7.1): `TLInv`; `TLObl`; SPEC-ACQUIRE/SPEC-RELEASE | `is_fair_lock`; `lock_token`; `TicketLock_init_spec` / `TicketLock_acquire_spec` / `TicketLock_release_spec` (a self-contained variant lives in `ticket_lock2.v`) | `ticket_lock.v` |
| Queue (§7.2): `QInv` (`QData`/`QState`/`QObls`/`QPrimary`); SPEC-ENQUEUE/SPEC-DEQUEUE | `is_queue` (with `queue_worker` for the primary); `Queue_init_spec` / `Queue_enqueue_spec` / `Queue_dequeue_spec` | `queue.v` |
| Task queue (§7.3): `TQInv`; SPEC-PUT-TASK/SPEC-WORKER | `is_task_queue`; `TaskQueue_init_spec` / `TaskQueue_put_task_spec` / `TaskQueue_run_task_spec` / `TaskQueue_worker_spec` | `task_queue.v` |
| Reentrant client `decr` / `clientMain` (§7.3); SPEC-DECR/SPEC-DECR-CLIENTMAIN | `decr_reentrant` / `main`; `decr_reentrant_spec` / `main_spec`; `task_queue_client_adequacy` | `task_queue_client.v` |

The per-example `*_adequacy` theorems (`flag_client_adequacy`, `main_adequacy`,
`handoff_client_adequacy`, `task_queue_client_adequacy`) are end-to-end
instantiations of Theorem 1, deriving the trace-level temporal property of the
respective client program. The files `flag_client.v`, `paradox.v`, and
`extended_int.v` are auxiliary developments not presented in the paper.
