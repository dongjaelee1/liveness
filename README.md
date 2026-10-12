# Lantana in Rocq

The Rocq development of *Decoupling Liveness Obligations from Thread-Local Carriers in the Lantana
Concurrent Separation Logic* (POPL 2027). It mechanizes Lantana on top of Transfinite Iris: the
logic and its fuel-burning triple, the adequacy theorem, and the case studies.

Rule names and notation follow the revised paper. Section and figure numbers refer to the
submitted version.

1. [Claims](#1-claims)
2. [Getting started](#2-getting-started)
3. [Evaluating the claims](#3-evaluating-the-claims)
4. [The development](#4-the-development)

## 1. Claims

| Claim | Paper | Rocq |
|---|---|---|
| 1. The logic: Lantana's predicates and the fuel-burning triple, with every rule the paper displays proved as a lemma | §1–§5, Figs. 1, 3–5 | `lantana/`, `lantana_heap_lang/triple.v` |
| 2. Adequacy: `lwp_adequacy` (Theorem 1), and Iris-style safety `lwp_adequacy_safety_iris` | §6 | `lantana/program_logic/adequacy.v`, `adequacy_iris.v` |
| 3. The case studies, with end-to-end theorems for the client programs | §2, §4.3, §5, §7 | `lantana_heap_lang/examples/` |
| 4. A pure-step rule that burns no fuel is unsound: `no_lc_absurd` | end of §6.2 | `lantana_heap_lang/examples/paradox.v` |
| 5. Nothing is admitted, and the results assume only seven standard axioms, among them Hilbert's epsilon | §6.2 | `lantana_heap_lang/examples/assumptions.v` |

Building the development (§3.1) checks claims 1–4, and §3.3 gives the Rocq name of each item of
the paper. §3.2 checks claim 5.

## 2. Getting started

### Requirements

- opam 2.1 or later, on Linux or macOS (on Windows, use WSL), with network access.
  We tested with opam 2.1.5, OCaml 5.2.1 and Rocq 9.0.0 on Linux (x86-64).
- 8 GB of memory. With `-j6`, the build used at most 3.6 GB.
- Time, on an Intel Xeon Gold 6354 (3.0 GHz): `./configure` takes about 5 minutes plus the time
  opam takes to build Rocq, and `make -j6` about 10 minutes.

### Installation

1. Create an opam switch:
   ```
   opam update
   opam switch create lantana 5.2.1
   eval $(opam env)
   ```
2. Install the dependencies:
   ```
   ./configure
   ```
   This installs Rocq 9.0.0 and the Ordinal library 0.5.6 with opam. It then builds and installs
   std++, parametric Iris and Transfinite Iris from the bundled `stdpp.zip`,
   `iris-parametric-index.zip` and `transfinite-parametric-index.zip`, so their upstream
   repositories are not needed. `NJOBS=4 ./configure` sets the number of jobs (default 8).
3. Build the development:
   ```
   make -j4
   ```

### Check

The build must end without errors. Its last file, `assumptions.v`, prints the axioms of the main
results (§3.2).

## 3. Evaluating the claims

### 3.1 Building

`make` checks every proof. To rebuild from scratch, run `make clean` first.

To read a statement, open the files in an editor with Rocq support, at the root of this directory
(for instance VS Code with coq-lsp). Or, after `make`:
```
coqtop -Q ordinal lantana.ordinal -Q lantana lantana -Q lantana_heap_lang lantana.heap_lang
Require Import lantana.program_logic.adequacy.
Check lwp_adequacy.
```

### 3.2 Axioms and admits

`make` prints the output of `lantana_heap_lang/examples/assumptions.v`. The adequacy theorems, the
twelve client theorems and `no_lc_absurd` assume these seven axioms of Rocq's standard library:

- `Classical_Prop.classic`
- `Epsilon.epsilon_statement`
- `FunctionalExtensionality.functional_extensionality_dep`
- `ProofIrrelevance.proof_irrelevance`
- `PropExtensionality.propositional_extensionality`
- `ClassicalUniqueChoice.dependent_unique_choice`
- `RelationalChoice.relational_choice`

The rules of `triple.v` and the case-study specifications assume the first five. An admitted proof
would appear in this output.

`grep -rnwE 'admit|Admitted' lantana lantana_heap_lang` finds only the word "admit" in a comment
(`lantana/base_logic/later_credits.v`). On `ordinal/`, the copy of the Ordinal library, it finds
only commented-out code and an unused tactic.

### 3.3 From the paper to Rocq

Paths are under `lantana/`, unless they start with `lantana_heap_lang/`.

#### The fuel-burning triple

The paper's triple `{P}^G_i e {v. Q v}^G'_E` is `fbtriple` (`lantana_heap_lang/triple.v`), defined
from the weakest precondition `lWP` (`program_logic/weakestpre.v`):

```
fbtriple_gen s i C E G P e Q :=
  ∀ Φ, thread_expr i C e ∗ thP_carriers i G ∗ P -∗
       (∀ v, thread_expr i C (of_val v) ∗ Q v -∗ Φ v) -∗
       lWP e @ s; i; E {{ Φ }}
fbtriple s i C E G G' P e Q := fbtriple_gen s i C E G P e (λ v, thP_carriers i G' ∗ Q v)
```

- Notation: `fb{{ P }}^G e @ i; C; E fb{{ v, Q }}^G'`, or with `@ s; i; C; E` for a stuckness `s`
  other than `NotStuck`.
- It makes explicit what the paper leaves implicit: the mask `E`, and the context `C` around `e`
  in thread `i`'s expression. The triple carries the thread token `thread_expr i C e` and the
  carriers `thP_carriers i G`, so neither appears in `P` or `Q`.
- `fbtriple_gen` (no final superscript) lets the postcondition state the final carriers, when
  they depend on its variables (e.g. SPEC-ACQUIRE).
- A triple is not persistent; a specification is `□ ∃ μ, ∀ …, fb{{ P }}^G e @ i; C; ⊤ fb{{ v, Q }}^G'`.
- The case studies prove texan-style `*_spec` lemmas and restate them in this form as `*_fbspec`.

Name prefixes: `crP_` carriers, `oblP_` obligations, `witP_` witnesses, `thP_` threads, `tf_`
logical temporal formulas, `tp`/`tr_` trace properties.

#### Predicates (Fig. 1, §2–§6)

| Paper | Rocq | File |
|---|---|---|
| carriers `G`, `carriers_i G` | `thP_carriers i G` | `base_logic/opreds.v` |
| `thread_i e`, `exit_i v` | `thread_expr i [] e`, `exits v@i` | `lantana_heap_lang/primitive_laws.v` |
| `Fuel^ℓ_G μ` | `fuels G ℓ μ`; for one carrier, `crP_fuel g ℓ μ` | `lantana_heap_lang/triple.v`, `base_logic/opreds.v` |
| `obls^ℓ_g K` | `crP_obls g ℓ K` | `base_logic/opreds.v` |
| `obl_■ k` | `oblP_discharged k` | `base_logic/opreds.v` |
| `tr$^ℓ_k m` | `oblP_fuel k ℓ m` | `base_logic/opreds.v` |
| `wit^ℓ k`, `wit€ k` | `witP_layer k ℓ`, `witP_cred k a` | `base_logic/opreds.v` |
| `■ i` | `thP_done i` | `base_logic/opreds.v` |
| `Φ until^k_q Ψ` | `untilP N k q Φ Ψ` | `program_logic/temporal_logic.v` |
| `finally^k Φ` | `finallyP N k q Φ` | `program_logic/temporal_logic.v` |
| `always I` | `alwaysP N I` | `program_logic/temporal_logic.v` |
| `£ α` | later credits, `tlc_*` lemmas | `base_logic/later_credits.v` |
| `Measure` | `measure` | `algebra/measure.v` |
| layers `ℓ` | `ord.t` | `algebra/layer.v` |

Notes:
- `N` is an invariant namespace, which the paper omits.
- In `measure`, `▽` is `ms_extend`, and `+`, `×`, `μ1^μ2` are `⊕`, `×`, `↑`. There is no `ω`:
  `ms_embed` embeds any well-founded relation (`ms_nat n` is `n`), and `ms_large` is a large
  ordinal `ℵ`.
- Layers are ordinals of the copy of the Ordinal library in `ordinal/`. Measures are interpreted
  at internal layers `ord.t × nat`, where the paper's `ℓ` is `(ℓ, 0)`.

#### Rules (§2, Figs. 3–5, §5)

All in `lantana_heap_lang/triple.v`.

| Paper rule | Rocq |
|---|---|
| STEP-PURE, STEP-PURE-LC, STEP-PURE-WIT | `fbtriple_step_pure`, `fbtriple_step_pure_lc`, `fbtriple_step_pure_wit1` |
| STEP-REF, STEP-STORE, STEP-LOAD | `fbtriple_step_ref`, `fbtriple_step_store`, `fbtriple_step_load` |
| FORK\* | `fbtriple_fork1` |
| EXIT | `fbtriple_exit`, and `fbtriple_top_lwp` for Theorem 1 |
| FINALLY-EXIT\*, FINALLY-ALLOC\* | `fbtriple_finally_exit`, `fbtriple_finally_alloc` |
| BIND, FRAME | `fbtriple_bind`, `fbtriple_frame` |
| UPD-ELIM | `fbtriple_upd_elim` (fancy update), `fbtriple_gupd_elim` (ghost update) |
| CARRIER-ALLOC, CARRIER-DELETE | `fbtriple_carrier_alloc`, `fbtriple_carrier_delete` |
| OBLS-OFFLOAD | `fbtriple_obls_offload` |
| ALWAYS-ALLOC, ALWAYS-ACC | `fbtriple_always_alloc`, `fbtriple_always_acc` |
| UNTIL-ALLOC, UNTIL-ACC, UNTIL-DISCHARGE | `fbtriple_until_alloc`, `fbtriple_until_acc`, `fbtriple_until_discharge` |
| WIT-IND | `fbtriple_wit_ind` |
| FUELS-ADD, FUELS-UNION, FUELS-MONO, FUELS-LAYER | `fuels_add`, `fuels_union`, `fuels_mono`, `fuels_layer` |
| UNTIL-DONE-FALSE, UNTIL-SPLIT | `until_done_false`, `until_split` |
| LÖB, LC-SPEND | `lob`, `lc_spend` |

Notes:
- The Rocq rules state the later credits and masks that the paper elides; for example, UNTIL-ACC
  takes `£ 1` and UNTIL-DISCHARGE `£ 2`. `fuels_mono` is an update. In WIT-IND, the induction
  hypothesis's `⇛` is `={E}=∗`, used once.
- More general versions: `fbtriple_step_pure_wit` (a set of obligations), `fbtriple_fork` (moves a
  set of obligations to the child), `fbtriple_pure_step` (a pure step to any expression, such as a
  β-step), and `fbtriple_gen_bind`, `fbtriple_gen_frame` for the general form.
- Rules the paper does not display: `fbtriple_wand_pre` (`(R -∗ {P} e {Q}) ⊢ {P ∗ R} e {Q}`),
  `fuels_weaken` and `fuels_empty`, and `fuels_layer_eq` (layers compared as ordinals). The proof
  of `main` uses `fbtriple_wand_pre` and `fuels_layer_eq`.

#### Traces and adequacy (§6, Fig. 6)

| Paper | Rocq | File |
|---|---|---|
| `Cfg`, `TPool`, `Trace`, `Behavior` | `trace_state`, `thread_pool`, `trace`, `behavior` | `program_logic/language.v` |
| THREAD-STEP, THREAD-DONE, THREAD-STUCK | `thread_step`, `thread_done`, `thread_stuck` | `program_logic/language.v` |
| temporal properties, `⟦·⟧_t`: Always, Until, Finally | `tp`, `tp_trace`: `tr_always`, `tr_until`, `tr_eventually` | `program_logic/temporal_property.v` |
| `Fair`: inactive, active, turn | `fair_scheduling`: `thread_na`, `thread_active`, `thread_turn` | `program_logic/temporal_property.v` |
| logical assertions, `⟦·⟧_l` | `tf`, `⟦·⟧ₗ` | `program_logic/temporal_logic.v` |
| `lift` | `tf_to_tp` | `program_logic/adequacy.v` |
| `x ↦ v`, `thread_i e`, `exit_i v` | `pred_pointsto`, `pred_expr i [] e`, `exits v@i` | `lantana_heap_lang/lang.v`, `lantana_heap_lang/primitive_laws.v` |
| `lwp` | `lwp`, notation `lWP e @ s; i; E {{ Φ }}` | `program_logic/weakestpre.v` |
| `Ω`, `W` | `obls`, `witnesses` | `base_logic/obligation.v`, `base_logic/witness.v` |
| `M`, model update | `model_interp`, `mupd` | `base_logic/mupd.v` |
| `H` | `owit_inv` | `base_logic/owit.v` |
| `S` | `state_interp` | `lantana_heap_lang/primitive_laws.v` |
| **Theorem 1** | `lwp_adequacy` | `program_logic/adequacy.v` |
| Iris-style safety | `lwp_adequacy_safety_iris` | `program_logic/adequacy_iris.v` |

Notes:
- `lwp_adequacy` is Theorem 1 in general form: it starts a thread pool `Θ`, grants initial later
  credits `£ c`, and its weakest preconditions are `NotStuck`.
- In THREAD-STUCK, a stuck scheduled thread stutters, so stuck executions are behaviors too.
- `lwp_adequacy_safety_iris` holds for the same fair behaviors: the scheduled thread is never
  stuck, and whenever a thread is a value, its postcondition holds.

#### Case studies (§2–§7)

All in `lantana_heap_lang/examples/`.

| Paper | Rocq | File |
|---|---|---|
| Flag: `isFlag`, `FlagObl`, SPEC-INIT, SPEC-SET, SPEC-WAIT | `is_flag`, `flag_tk`, `Flag_init_fbspec`, `Flag_set_fbspec`, `Flag_wait_fbspec` | `flag.v` |
| `main` (§2) | `FlagFork_main_fbspec`, `main_adequacy` | `flag_fork.v` |
| SPEC-NEST, SPEC-NONDET (§4.3) | `Nondet_nest_fbspec`, `Nondet_nondet_fbspec` | `nondet.v` |
| Handoff (§5): `HandoffBuf`, `HInv`, `TaskSpec`, SPEC-SEND, SPEC-RECEIVE | `handoff_inv`, `is_handoff`, `is_task`, `Handoff_send_fbspec`, `Handoff_receive_fbspec` | `handoff.v` |
| SPEC-HANDOFF-MAIN (§5.2) | `main_fbspec`, `handoff_client_adequacy` | `handoff_client.v` |
| Ticket lock (§7.1): `TLInv`, `TLObl`, SPEC-ACQUIRE, SPEC-RELEASE | `lock_token`, `TicketLock_acquire_fbspec`, `TicketLock_release_fbspec` | `ticket_lock.v` |
| Queue (§7.2): `QInv`, SPEC-ENQUEUE, SPEC-DEQUEUE | `is_queue`, `Queue_enqueue_fbspec`, `Queue_dequeue_fbspec` | `queue.v` |
| Task queue (§7.3): `TQInv`, SPEC-PUT-TASK, SPEC-WORKER | `is_task_queue`, `TaskQueue_put_task_fbspec`, `TaskQueue_worker_fbspec` | `task_queue.v` |
| Reentrant client (§7.3): SPEC-DECR, SPEC-DECR-CLIENTMAIN | `decr_reentrant_fbspec`, `main_fbspec`, `task_queue_client_adequacy` | `task_queue_client.v` |
| The paradox (end of §6.2) | `no_lc_absurd` | `paradox.v` |

Notes:
- `is_flag x k ℓ` takes its arguments in another order than `isFlag`.
- `TLInv` is `is_fair_lock tl γ R ∗ γ ↪LOCK_AL□ ∗ γ ↪LOCK_CF□ ℓ`, which is persistent.
- `is_queue` is built from `queue_inv` (`QObls`), `queue_lock` (`QState`), `queue_contents`
  (`QData`) and `qG_queue` (`QList`); `queue_worker` is `QPrimary`. `Queue_dequeue_fbspec` also
  covers the worker and the empty queue; the paper shows the other case.
- SPEC-ACQUIRE, SPEC-DEQUEUE and `TaskQueue_run_task_fbspec` use the general form. The ticket lock,
  the queue and the task queue also have `init` specifications, and the ticket lock a `delete` one.
- Each client has three end-to-end theorems: `*_adequacy` (Theorem 1), `*_safety_adequacy`
  (safety) and `*_liveness_safety` (both). The clients are `main` in `flag_fork.v`,
  `handoff_client.v`, `task_queue_client.v`, and `flag_client.v`, which proves a property of a
  memory location.
- `no_lc_absurd` derives `False` from a fuel-free pure-step rule (`lantanaGS_no_lc`), through
  `loop_paradox` and a concrete fair run `loop_run` of two looping threads.

## 4. The development

### Structure

In dependency order; each directory has a README that describes its files.

- [`ordinal/`](ordinal/README.md): a copy of the Ordinal library, used for layers.
- [`lantana/prelude/`](lantana/prelude/README.md): classical axioms, ordinal facts, well-founded relations.
- [`lantana/algebra/`](lantana/algebra/README.md): resource algebras, measures and layers.
- [`lantana/base_logic/`](lantana/base_logic/README.md): ghost state for obligations, threads,
  carriers and witnesses; the model and ghost updates; transfinite later credits.
- [`lantana/bi/`](lantana/bi/README.md): the interface and notation of `lWP`.
- [`lantana/program_logic/`](lantana/program_logic/README.md): languages, traces and fair
  scheduling, `lwp`, temporal formulas, and the adequacy theorems.
- [`lantana_heap_lang/`](lantana_heap_lang/README.md): HeapLang, its `lWP` rules, and the
  fuel-burning triple.
- [`lantana_heap_lang/examples/`](lantana_heap_lang/examples/README.md): the case studies.

The logical paths are `lantana.ordinal`, `lantana` and `lantana.heap_lang`.

### What is new

`lantana/` and `lantana_heap_lang/` are new. Some files are adapted from earlier work, as their
headers say:
- HeapLang (apart from `triple.v` and the examples) from Iris's HeapLang, with thread ids and
  `ChooseNat`, and without prophecy variables;
- the language interface, lifting lemmas and atomic triples (`lantana/program_logic/`) and the
  weakest-precondition interface (`lantana/bi/`) from Iris;
- fancy updates, invariants and satisfiability (`lantana/base_logic/`) from Transfinite Iris, and
  the relational updates and later credits from the artifact of *Later Credits* (Spies et al.,
  2022);
- `ord_tree` (`lantana/prelude/wf_structs.v`) from the Coq development of Fair Operational
  Semantics.

`ordinal/` is a copy of the Ordinal library, and the zip files are std++, parametric Iris and
Transfinite Iris.

### Reusing Lantana

To verify a new program, start from the case studies: `flag.v` proves a module's specifications,
and `flag_fork.v` proves a client with the triple rules and applies the adequacy theorem to it.
To use Lantana from another project, run `make install`, or add the three `-Q` options of the
`coqtop` command above, with paths to this directory, to that project's `_CoqProject`.

### Acknowledgements

The `ordinal/` directory is a copy of the Ordinal library, available at
https://github.com/snu-sf/Ordinal.

(Transfinite Iris) The mechanization of set-theoretic ordinals and the underlying ZF model
construction has been based on Coq code by Dominik Kirst and Gert Smolka, available at:

* "Large Model Constructions for Second-Order ZF in Dependent Type Theory"
  by Dominik Kirst and Gert Smolka, CPP 2018
  See https://www.ps.uni-saarland.de/Publications/details/KirstSmolka:2017:Large-Model.html.
* "Formalised Set Theory: Well-Orderings and the Axiom of Choice", Dominik Kirst.
  See https://www.ps.uni-saarland.de/~kirst/bachelor.php

### License

BSD-3-Clause (`LICENSE`); the copy of the Ordinal library is under the MIT license
(`ordinal/LICENSE`).
