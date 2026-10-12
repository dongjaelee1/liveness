# `lantana/base_logic/`

The `iProp`-level model of Lantana. The first part is the logical infrastructure: relational
updates and transfinite later credits `£ α`, fancy updates and invariants built on them, and
generic ghost state (invariant locations, the thread map). The second part is the model of
obligations: obligations and witnesses with their steps, their ghost state, the obligation forest
(every live obligation has a parent, a thread or another obligation), the model history, and the
model update `mupd`/`fmupd`, which takes rounds of the model while keeping `model_interp`. The
last file, `opreds.v`, implements the user-facing predicates of the obligation-forest interface
(`lantana/program_logic/obl_forest.v`) as the module `omodel`.

Builds on `lantana/prelude/`, `lantana/algebra/`. Used by `lantana/program_logic/`,
`lantana/trace/`, `lantana_heap_lang/`, `lantana_heap_lang/examples/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `relational_updates.v` | — | Relational updates `\|==>r P`: the later-elimination update of *Later Credits* (Spies et al. 2022), generalized from natural numbers to any type with a well-founded relation, and their elimination in adequacy proofs. |
| `later_credits.v` | `relational_updates.v` | Transfinite later credits `£ α`: a generic theory of credits for relational updates, the allocation modality `ALC`, and the instantiation with the ordinals `Ord.t` (`tlcGS`, the `tlc_*` lemmas). |
| `fancy_updates.v` | `later_credits.v` | Fancy updates `\|={E1,E2}=> P` on top of the relational update of transfinite later credits instead of the basic update (`invGS`), and the rules for spending credits at fancy updates. |
| `satisfiable.v` | `fancy_updates.v` | Satisfiability with invariant masks (`SatisfiableAt`) for these fancy updates, used by the adequacy proofs in `lantana/trace/`. |
| `invariants.v` | `fancy_updates.v` | Invariants `inv N P` for these fancy updates, with rules for allocating, opening, splitting and changing them. |
| `gen_inv_heap.v` | `invariants.v` | Invariant locations: locations with an invariant on their value that are never deallocated (`inv_pointsto`, `inv_pointsto_own`). Used by HeapLang. |
| `thread_map.v` | — | The thread map: ghost state for a map from thread ids to values, with an authoritative part `thread_map_interp Θ R` and per-thread fragments `thread p b v q`. Used by HeapLang for the thread-expression token. |
| `obligation.v` | — | Obligations: an obligation is assigned (with fuel and an owner thread) or discharged. The steps of one obligation and the relations on obligation maps `obls` used by the model: allocation `↪ₐ`, conditional steps `↪ₛ`, progress `↪ₚ` and the order `obls_le`. |
| `witness.v` | `obligation.v` | Witnesses: a witness of an obligation is assigned (with a bound) or discharged; the steps of a witness and the conditional relations on witness maps. |
| `osat.v` | `obligation.v` | The ghost state of obligations: the invariant `osat Ω` ties the obligation map `Ω` to per-obligation ghost state (a fuel bound, the state, fuel credits, the owner), with rules for progress, owner change and discharge. |
| `owit.v` | `witness.v`, `osat.v` | The ghost state of witnesses: `owit W` holds a credit for every assigned witness, and `owit_inv Ω W` relates witnesses to obligations; rules for witness credits and witness steps. |
| `othread.v` | `osat.v` | The ghost state of threads: `othread TP` tracks whether each thread runs or has terminated and which obligations it owns; `oassigned` relates every obligation to its owner thread. |
| `parent.v` | `obligation.v` | Parents in an obligation forest: a thread (`PThread i`) or an obligation (`PObl k`). Shared by the interface (`program_logic/obl_forest.v`) and the model (`oforest.v`). |
| `model_rel.v` | `owit.v` | The round relations of the model. A round may change several obligations at once, so rounds use pointwise relations: `obls_ndf` (every obligation stays or makes progress, new ones may be added), `obls_lef` (also discharges), and `wits_ndf` / `wits_lef`; `obls_lef` implies the order `obls_le` seen by adequacy. |
| `oforest.v` | `osat.v`, `othread.v`, `parent.v`, `model_rel.v` | The ghost state of obligation forests: the invariant `oforest Ω Θ`, part of `model_interp`, gives every live obligation a parent and keeps the children of each parent in a ghost map. A node below an obligation `c` stores a piece of its fuel above the fuel of `c`, so children burn fuel with their parent without user resources. |
| `model_history.v` | `obligation.v` | The model history: a monotonically growing list of events `(n, Ω)` (a physical step index and the obligations), with the authoritative part `model_history_interp` and the record `event_obl`. |
| `mupd.v` | `owit.v`, `othread.v`, `oforest.v`, `model_rel.v`, `model_history.v`, `invariants.v` | `model_interp`, the ghost state of the obligation model, and the model update `\|=[n,Θ]=>m P`, a least fixpoint of rounds that may change obligations (`obls_lef`) and witnesses (`wits_lef`) while keeping `model_interp`; `fmupd` wraps it in fancy updates. |
| `oinv.v` | `osat.v`, `invariants.v` | Invariants of obligations: `oblG_inv N k q P Q R` holds `P` or `Q` while the obligation `k` is assigned (depending on its flag) and `R` once it is discharged. |
| `model_physical_updates.v` | `mupd.v` | The model rounds taken at a physical step: `mprog` for the step of a thread (progress of its obligations, credits for witnesses) and `mphys` for the change of the physical state and the thread pool (forked threads). |
| `opreds.v` | `oinv.v`, `mupd.v`, `model_physical_updates.v` | The module `omodel`: the obligation predicates as ghost state (`oblP_*`, `witP_*`, `thP_*`, `parP_kids`), their rules, the model updates of the forest (`*_mupd`) and the physical steps. It implements the obligation-forest interface and is used only by `program_logic/obl_forest_instance.v`. |

## Notes

- `fancy_updates.v`, `satisfiable.v`, `invariants.v` and `gen_inv_heap.v` are adapted from
  Transfinite Iris, and `relational_updates.v` and `later_credits.v` from the artifact of
  *Later Credits*, as their headers say.
- Outside this directory, the program logic uses the model only through
  `program_logic/obl_forest_instance.v` (which imports `opreds.v`) and the step modalities of
  `model_physical_updates.v`; `lantana/trace/` uses `satisfiable.v`, and HeapLang and the
  examples use `invariants.v`, `later_credits.v`, `gen_inv_heap.v` and `thread_map.v`.
- In `opreds.v`, the assignment of a live obligation `k` is split four ways: a quarter in
  `osat`, a half for the user (`oblP_assigned k 1`), and an eighth each in the children
  predicate of `k` and in that of its parent. Hence a children predicate excludes
  `oblP_discharged` for `k` and for each of its children, without the forest invariant.
