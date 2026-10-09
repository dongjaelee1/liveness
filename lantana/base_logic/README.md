# `lantana/base_logic/`

The base logic of Lantana: ghost state for obligations, threads, carriers and witnesses, the model interpretation and the model and ghost update modalities over it, and the predicates (`oblP_*`, `witP_*`, `crP_*`, `thP_*`) that proofs use. It also provides transfinite later credits, fancy updates and invariants, built on Iris and Transfinite Iris.

Builds on `lantana/algebra/`. Used by `lantana/program_logic/`, `lantana_heap_lang/`, `lantana_heap_lang/examples/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `obligation.v` | — | Obligations (assigned, with fuel and an owner thread, or discharged) and obligation states `obls` (the paper's `Ω`). Their step relations: steps `↪`, non-discharging steps `↪ₙ`, conditional steps and strict progress, and the orders `obls_le` and `obls_nd`. |
| `model_interp.v` | `obligation.v` | Ghost state for the model history, a monotone list of events `(n, Ω)`: `model_history_interp` and the persistent event facts `mhG_event` and `event_obl`. |
| `osat.v` | `obligation.v` | Ghost state for each obligation (bound, state, fuel and fuel supply, owner) and the invariant `osat Ω` that ties it to the obligation state, with rules to allocate, progress and discharge obligations. Fixes obligation fuel to ordinals (`ord_obl_class`). |
| `othread.v` | `osat.v` | Ghost state for threads and the obligations they own, executing or terminated, with the invariants `othread` and `oassigned` that relate obligations to threads. |
| `ocarrier.v` | `osat.v`, `othread.v` | Ghost state for carriers: the carriers of each thread, the obligations each carrier carries, and carrier fuel bounded by `ocarrierG_bound`. The invariant `ocarrier` comes with rules to allocate and delete carriers and to move obligations between carriers and threads. |
| `relational_updates.v` | — | The relational update `rupd`, a later elimination update parametric in a well-founded relation, with proof mode instances and support for adequacy proofs (`sat_lc`). |
| `later_credits.v` | `relational_updates.v` | Later credits on top of relational updates, with the allocation modality `ALC` and credit induction, instantiated with ordinals: the paper's transfinite later credits `£ α` (`tlc_*` lemmas). |
| `fancy_updates.v` | `later_credits.v` | Fancy updates (`invGS`) built on relational updates with transfinite later credits, and lemmas that spend a credit to remove a later (`lc_fupd_elim_later_ord`, `lc_fupd_add_later`). |
| `invariants.v` | `fancy_updates.v` | Semantic invariants `inv N P` with allocation and access rules. |
| `gen_inv_heap.v` | `invariants.v` | Invariant locations (`inv_pointsto`, `inv_pointsto_own`): heap locations whose value always satisfies a fixed invariant. HeapLang's `heap_stateGS` includes this ghost state, but the invariant `inv_heap_inv` is not part of HeapLang's state interpretation. |
| `oinv.v` | `invariants.v`, `osat.v` | `oblG_inv`: an invariant attached to an obligation that holds `P`, `Q` or `R` depending on the obligation's state, with access and allocation rules. |
| `satisfiable.v` | `fancy_updates.v` | Satisfiability with invariant masks (`sat_at`) for these fancy updates, used by the adequacy proofs. |
| `thread_map.v` | — | A ghost map from thread ids to values (`thread_map_interp`, `thread`). HeapLang uses it for the expression of each thread. |
| `witness.v` | `obligation.v` | Witnesses, which mirror obligations (assigned, with a measure, or discharged), witness states `witnesses` (the paper's `W`), and their step relations, analogous to those of `obligation.v`. |
| `owit.v` | `osat.v`, `witness.v` | Ghost state for witness credits and bounds with the invariant `owit W`, and the relation `owit_inv Ω W` between obligations and witnesses (the paper's fair-scheduler invariant `H`). |
| `mupd.v` | `invariants.v`, `model_interp.v`, `ocarrier.v`, `owit.v` | The model interpretation `model_interp` (the paper's `M`), which combines the ghost state above, and the model update modality `mupd`, with its masked form `fmupd`. |
| `gupd.v` | `mupd.v` | The ghost update modality `gupd`: a model update whose steps discharge nothing, with its masked form `fgupd`. `gupd_mupd` turns it into a model update. |
| `opreds.v` | `gupd.v`, `oinv.v` | The predicates used in proofs and their rules: obligations (`oblP_discharged`, `oblP_fuel`), witnesses (`witP_layer`, `witP_cred`), carriers (`crP_fuel`, `crP_obls`) and threads (`thP_carriers`, `thP_done`). Also update rules for thread termination, carriers, and allocating, discharging and offloading obligations, and witness induction (`wit_layer_ind`). |

## Notes

`relational_updates.v` and `later_credits.v` come from the artifact of *Later Credits: Resourceful Reasoning for the Later Modality* (Spies et al., 2022). `fancy_updates.v`, `invariants.v`, `gen_inv_heap.v` and `satisfiable.v` are adapted from the files of the same names in Transfinite Iris's `base_logic/lib/`.
