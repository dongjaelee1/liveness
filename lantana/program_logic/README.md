# `lantana/program_logic/`

The program logic: the language interface with thread ids, traces, fair scheduling and temporal properties of executions, the thread-local weakest precondition `lwp` with its updates and logical temporal formulas, and the adequacy theorems that turn `lwp` proofs into properties of all fair executions. It builds on Iris and Transfinite Iris, and several files are adapted from Iris's `iris/program_logic/` (see Notes).

Builds on `lantana/algebra/`, `lantana/base_logic/`, `lantana/bi/`, `lantana/prelude/`. Used by `lantana_heap_lang/`, `lantana_heap_lang/examples/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `language.v` | — | The `language` interface, whose steps `prim_step` have a thread id, the set of ids in use, and forked threads. Thread pools and configurations (`cfg`), thread steps (`thread_step`, `thread_done`, `thread_stuck`), traces, and the coinductive `behavior` (the paper's `Behavior`; `thread_stuck` lets a scheduled stuck thread stutter), plus the ordinal bounds `fair_sched_fun` and `fair_sched_ub` used by the adequacy proofs. |
| `ectx_language.v` | `language.v` | Languages defined by evaluation contexts and base steps (`ectxLanguage`), and their `language` instance. |
| `ectxi_language.v` | `ectx_language.v`, `language.v` | Languages defined by evaluation-context items (`ectxiLanguage`), and their `ectxLanguage` instance. HeapLang is defined this way. |
| `history_interp.v` | `language.v` | Ghost state for the execution history (`history_interp`, `event_pred`), and the class `state_interp_class` of state interpretations that a language instance provides (the paper's `S`). |
| `model_physical_updates.v` | — | The two updates of a step: the progress update `mprog` (the scheduled thread's obligations progress and witnesses decrease), and the physical update `mphys` (move to the next configuration, with empty carrier sets for forked threads). |
| `sfgupd.v` | `history_interp.v` | Ghost updates `\|={E1,E2}=>g` of the obligation model, which discharge nothing, framed with the history interpretation. Rules for thread termination, carriers, and allocating and offloading obligations (`thread_terminate`, `carrier_alloc`, `obl_offload_set`, …). |
| `sfmupd.v` | `sfgupd.v` | Model updates `\|={E1,E2}=>m`, which can also discharge obligations, framed with the history interpretation. |
| `temporal_property.v` | `language.v` | Temporal properties of traces: syntax `tp` and interpretation `tp_trace` (the paper's `⟦·⟧_t`), fair scheduling `fair_scheduling` (the paper's `Fair`) with fair-scheduling counters, and Iris-style safety `safety_iris`. |
| `weakestpre.v` | `language.v`, `model_physical_updates.v`, `sfmupd.v` | The thread-local weakest precondition `lwp` (the paper's `lwp`), the least fixpoint of `lwp_pre`, which is built from the step `lwp_step`, together with the update `lwpupd`, structural rules such as `lwp_bind` and `lwp_strong_mono`, and proof mode instances. |
| `atomic.v` | `weakestpre.v` | Logically atomic triples for `lwp` (`atomic_lwp`) and their notation. |
| `lifting.v` | `weakestpre.v` | Lifting lemmas that prove `lwp` from the operational semantics, for general, atomic and pure steps (`lwp_lift_step`, `lwp_pure_step`). |
| `ectx_lifting.v` | `ectx_language.v`, `lifting.v` | The lifting lemmas for base steps of evaluation-context languages. |
| `temporal_logic.v` | `weakestpre.v` | Logical temporal formulas `tf` and their interpretation `⟦·⟧ₗ` in `iProp` (the paper's `⟦·⟧_l`): `always` is an invariant and `until` an obligation with an invariant. Notations `alwaysP`, `untilP`, `finallyP`, and rules to allocate, access and discharge them (`tf_until_alloc`, `tf_until_discharge`). |
| `adequacy.v` | `language.v`, `temporal_logic.v`, `temporal_property.v`, `weakestpre.v` | `tf_to_tp` (the paper's `lift`) and the adequacy theorem `lwp_adequacy` for `NotStuck` weakest preconditions: every fair behavior satisfies the lifted formula. |
| `adequacy_iris.v` | `adequacy.v`, `language.v`, `temporal_logic.v`, `temporal_property.v`, `weakestpre.v` | Iris-style safety `lwp_adequacy_safety_iris` for the same fair behaviors: the scheduled thread is never stuck, and whenever a chosen thread `j` is a value `v`, its postcondition `Φ j v` holds. |

## Notes

- `language.v`, `ectx_language.v`, `ectxi_language.v`, `lifting.v`, `ectx_lifting.v` and `atomic.v`, and the structure of `weakestpre.v`, are adapted from Iris's `iris/program_logic/`.
- Steps and traces carry observations `κ : list (observation Λ)`, as in Iris, where they serve prophecy variables. HeapLang has no prophecy variables, and its `observation` is the empty type.
