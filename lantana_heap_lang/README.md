# `lantana_heap_lang/`

HeapLang, Iris's example language, adapted to Lantana: its semantics with thread ids and
nondeterministic `ChooseNat` (and without Iris's prophecy variables), its program logic (the
primitive `lWP` rules and the paper's fuel-burning triple), and proof-mode tactics. Adapted from
Iris's `heap_lang`; builds on Iris, Transfinite Iris and stdpp.

Builds on `lantana/algebra/`, `lantana/base_logic/`, `lantana/program_logic/`. Used by `lantana_heap_lang/examples/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `locations.v` | — | Heap locations `loc`, with the offset `l +ₗ off`, their order, and `Loc.fresh` for allocation. |
| `lang.v` | `locations.v` | The syntax and semantics of HeapLang: expressions, values, evaluation contexts, and `base_step`, which takes the stepping thread's id and gives forked threads fresh ids. There are no prophecy variables, so `observation` is the empty type. Also the atomic state predicates `state_pred` (points-to and thread expression) of the temporal logic, and the canonical `heap_lang` language. |
| `notation.v` | `lang.v` | Coercions and notations for writing HeapLang programs (`λ:`, `let:`, `match:`, `#v`, `ref`, ...). |
| `tactics.v` | `lang.v` | The tactics `reshape_expr`, which splits an expression into an evaluation context and a subexpression, and `inv_base_step`, which inverts base steps. |
| `class_instances.v` | `lang.v`, `notation.v`, `tactics.v` | `Atomic` and `PureExec` instances for HeapLang expressions. |
| `primitive_laws.v` | `class_instances.v`, `notation.v`, `tactics.v` | The state interpretation and `heapGS`; the points-to `l ↦ v`, the thread-expression token `thread_expr i C e`, and the atom `exits v@i` (thread `i` has finished with value `v`). The primitive `lWP` rules for pure steps, `Fork`, `ChooseNat` and the heap operations, which consume carrier fuel, and the exit rules `thread_expr_exit` and `thread_expr_terminate`. |
| `derived_laws.v` | `notation.v`, `primitive_laws.v`, `tactics.v` | The array connective `l ↦∗ vs` and the heap rules for arrays and offsets. |
| `proofmode.v` | `derived_laws.v`, `notation.v`, `tactics.v` | Proof-mode tactics for `lWP`: `lwp_pure` and its variants (`lwp_rec`, `lwp_let`, ...), `lwp_bind`, `lwp_finish`, and `thread_expr_focus`, which keeps the token on the current expression. |
| `triple.v` | `lang.v`, `notation.v`, `proofmode.v` | The paper's fuel-burning triple `fbtriple` (notation `fb{{ P }}^G e @ i; C; E fb{{ v, Q }}^G'`) and its general form `fbtriple_gen`, with proofs of the paper's triple rules (structural, carrier and obligation, step, fork and exit rules) and the logic-level rules under the paper's names. |

Subdirectory: `examples/` has the case studies and other examples.

## Notes

`locations.v` is Iris's file, and `notation.v` is Iris's file with the imports changed.
`lang.v`, `tactics.v` and `class_instances.v` are Iris's files extended with
thread ids and `ChooseNat` (and, in `lang.v`, the state predicates). `primitive_laws.v`,
`derived_laws.v` and `proofmode.v` follow Iris's files but are stated for Lantana's `lWP`.
`triple.v` is new. Iris's prophecy variables (`NewProph`, `Resolve`, the `proph` ghost state)
are removed from all of these files.
