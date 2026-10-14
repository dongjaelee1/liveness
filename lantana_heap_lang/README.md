# `lantana_heap_lang/`

HeapLang for Lantana: Iris's HeapLang where a step knows the id of the stepping thread and the ids
in use, forked threads get fresh ids, and there are nondeterministic `ChooseNat` and labels
`Label t e`. On top of the language: its instance of the program logic (the ghost state
`heapGS`, the points-to and thread-expression assertions, and the primitive `lWP` laws), the
proof mode, and the state atoms of temporal properties with the facts that guarantee them. The
case studies are in [`examples/`](examples/README.md).

Builds on `lantana/algebra/`, `lantana/base_logic/`, `lantana/program_logic/`, `lantana/trace/`.
Used by `lantana_heap_lang/examples/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `locations.v` | — | Heap locations: integers with offsets (`l +ₗ off`), an order, and fresh locations. |
| `lang.v` | `locations.v` | The language: expressions and values (with prophecy variables `NewProph`/`Resolve`, `Label t e` and `ChooseNat`), evaluation contexts, the base step `base_step i e σ Θ κ e' σ' efs` of thread `i` with thread ids `Θ` in use (forked threads get fresh ids), and the state predicates `pointsto_sat` / `thread_expr_sat` that the atoms of temporal properties observe. As in Iris, evaluation is right-to-left and freed locations are never reused. |
| `tactics.v` | `lang.v` | Tactics on the operational semantics: `reshape_expr`, `inv_base_step`, and the `base_step` hint database. |
| `notation.v` | `lang.v` | Notations and coercions for writing programs (`λ:`, `let:`, `#v`, `Skip`, `CAS`, …). |
| `class_instances.v` | `lang.v`, `tactics.v`, `notation.v` | The `IntoVal`, `AsVal`, `Atomic` and `PureExec` instances. |
| `pretty.v` | `lang.v` | Pretty printing of values. Not imported by any file. |
| `metatheory.v` | `lang.v` | Metatheory (closedness, parallel substitution), not needed for verifying programs. Not imported by any file. |
| `primitive_laws.v` | `class_instances.v`, `tactics.v`, `notation.v` | The instance of the program logic: the ghost state `heapGS` and `heapGS_lantanaGS`, the assertions `l ↦{dq} v` and `thread_expr i C e` (thread `i` runs `e` in the context `C`), the state interpretation, and the primitive laws proved from the lifting lemmas (`lwp_alloc`, `lwp_load`, `lwp_store`, `lwp_free`, `lwp_xchg`, `lwp_cmpxchg_suc`/`_fail`, `lwp_faa`, `lwp_fork`, `lwp_choosenat`, `lwp_new_proph`, `lwp_pure_step`). Each step rule takes the children `thP_kids i G` of the thread and fuel for each. |
| `derived_laws.v` | `primitive_laws.v`, `notation.v` | The `array` connective `l ↦∗ vs` (`pointsto` for a list of values) and the `lWP` rules for arrays, derived without the lifting lemmas. |
| `proofmode.v` | `tactics.v`, `derived_laws.v`, `notation.v` | Proof-mode tactics for `lWP`: focusing the thread-expression token in the hypothesis `"TE"`, pure steps (`lwp_pure` and the tactics built on it), binding (`lwp_bind`), and values (`lwp_finish`). |
| `temporal_laws.v` | `primitive_laws.v` | Temporal guarantees for HeapLang: the trace atoms `l ↦ v` and `exits v @ i` (state predicates of `lang.v`, read as `trSpec_state`), the `StateFact` instances by which `l ↦{dq} v`, `thread_expr i C e` and `freed l q` determine them (so they guarantee them), trace-level atom rules (`tr_pointsto_agree`, `tr_pointsto_frac`, `tr_pointsto_freed`), and `thread_expr_terminate_finally` for discharging a `finallyI` on termination. |

## Notes

- Every file except `temporal_laws.v` is adapted from the file of the same name in Iris's
  HeapLang (`iris.heap_lang`), as its header says.
- `primitive_laws.v` imports the trace layer (`triprop`, `adequacy_step`, `guarantee_infer`,
  `adequacy_temporal`), so the examples get the adequacy theorem with HeapLang;
  `lantana/trace/adequacy_safety.v` is imported by each client that proves safety.
- The proof mode supports pure steps and bind; heap operations are proved by applying the rules
  of `primitive_laws.v` (e.g. `lwp_load`) to the thread-expression token.
