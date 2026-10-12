# `lantana/program_logic/`

The program logic. It has three parts. First, languages with thread ids and forking, their traces
and behaviors, the history of configurations, and the ghost state of the temporal layer. Second,
the obligation-forest interface, the core of the logic: a class whose fields are the obligation
predicates, the model update `|={E1,E2}=>m P` and their rules, with derived rules and its one
instance. Third, the thread-local liveness weakest precondition `lWP e @ s; i; E {{ Φ }}`, a least
fixpoint, with its lifting lemmas and logically atomic triples. Everything above the instance
file uses only the interface.

Builds on `lantana/prelude/`, `lantana/algebra/`, `lantana/base_logic/`. Used by `lantana/trace/`,
`lantana_heap_lang/`, `lantana_heap_lang/examples/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `lwp_notation.v` | — | The class `Lwp` and the notations `lWP e @ s; i; E {{ Φ }}` and texan triples `l{{{ P }}} e @ i; E l{{{ v, RET v; Q }}}`, with a thread id `i`; without `s`, `NotStuck`. |
| `language.v` | `lwp_notation.v` | Languages with thread ids and forking (`language`; a step knows the stepping thread and the ids in use), contexts, pure steps, atomicity; configurations, `thread_step`, `thread_done`, `thread_stuck` (a stuck scheduled thread stutters), traces and the coinductive `behavior`; the ordinal bound `fair_sched_ub` of the fair scheduler. |
| `history_interp.v` | `language.v` | The history of configurations as ghost state (`hG_history_auth`, `hG_event`), the state interpretation class `state_interp_class` of a language, and the history interpretation `history_interp` built from both. |
| `temporal_registry.v` | `history_interp.v` | The temporal registry: an append-only list of the trace-visible structures (`alwaysI`, `untilI`), each tagged with its registration position, and a marker per check of the adequacy proof (ghost state `tregGS`). |
| `temporal_class.v` | `temporal_registry.v` | The ghost state of the temporal layer (`temporalGS`: the obligation model, the history and the registry), and `TemporalInterp`, the interpretation of the temporal layer, which the program logic threads without knowing its content; `lantana/trace/temporal_formula.v` fixes it to the registry. |
| `obl_forest.v` | `temporal_class.v` | The obligation-forest interface `oblf.obl_forest_interface`: the obligation predicates (`oblP_*`, `witP_*`, `thP_*`, `parP_kids p K`: the children of the parent `p` are `K`), the model update `\|={E1,E2}=>m P` and the rules of both. Every live obligation is a child of one parent, a thread or an obligation. |
| `obl_forest_rules.v` | `obl_forest.v` | Derived rules of the interface: the usual rules of the model update and its proof-mode instances from the three core rules of the class; the rules of obligation invariants, witnesses (`wit_layer_ind`), parents, fuel and credits (`oblP_fuels*`); set versions of moves; model updates and physical steps in their usual shapes. |
| `obl_forest_instance.v` | `obl_forest_rules.v` | The instance `obl_forest_lantana` of the interface over the obligation model `omodel` (`base_logic/opreds.v`): the only file that names the implementation. Also the bridges from the projections to the model, and the facts about the model that the trace layer and the adequacy proofs read. |
| `weakestpre.v` | `language.v`, `lwp_notation.v`, `obl_forest_instance.v` | `lantanaGS` (the temporal ghost state, the state interpretation, the postcondition of forked threads), one step `lwp_step` of the program logic (a model update before the step, the progress and physical updates of the step, a model update after it), and `lWP` as its least fixpoint, with structural rules (`lwp_bind`, `lwp_strong_mono`, `sfmupd_lwp`, …) and proof-mode instances. |
| `lifting.v` | `weakestpre.v` | Lifting lemmas: the rules of the operational semantics as rules of `lWP` (`lwp_lift_step`, `lwp_lift_atomic_step`, `lwp_pure_step`, …). Only `lwp_step_step` and `lwp_lift_step` see the history and the model updates around a step. |
| `ectx_language.v` | `language.v` | Languages based on evaluation contexts (`ectxLanguage`), and the `language` each gives (`LanguageOfEctx`). |
| `ectx_lifting.v` | `ectx_language.v`, `lifting.v` | Lifting lemmas of `lWP` for ectx-based languages, stated with base steps (`lwp_lift_base_step`, …). |
| `ectxi_language.v` | `language.v`, `ectx_language.v` | Languages based on evaluation-context items (`ectxiLanguage`), as instances of `ectxLanguage` (`EctxLanguageOfEctxi`). |
| `atomic.v` | `weakestpre.v` | Logically atomic triples for `lWP`: `<<{ ∀∀ x, α }>> e @ i; E <<{ ∃∃ y, β \| z, RET v; POST }>>`, with the inner mask empty. |

## Notes

- The language interface, the lifting lemmas, logically atomic triples and the notations are
  adapted from Iris, and the structure of `weakestpre.v` follows Iris's weakest precondition, as
  the headers say. Unlike Iris's, `lWP` is a least fixpoint, and each step of a thread burns fuel
  of the obligations below it.
- `lantana/trace/` reads this directory through `language.v` (`trace_prop.v`),
  `temporal_class.v` (`triprop.v`), `obl_forest_instance.v` (`temporal_formula.v`) and
  `weakestpre.v` (`adequacy_step.v`). HeapLang builds on `ectxi_language.v`, `ectx_lifting.v`
  and `atomic.v`.
- The adequacy theorems of `lWP` are in `lantana/trace/` (`adequacy_temporal.v`,
  `adequacy_safety.v`), since they conclude temporal properties.
