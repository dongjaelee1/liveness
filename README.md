# Lantana in Rocq

Lantana is a concurrent separation logic for proving liveness properties of concurrent programs
under fair scheduling. This repository is its Rocq development, built on Iris and Transfinite
Iris: the logic, its adequacy theorems, an instance for HeapLang, and case studies. The logic is
described in *Decoupling Liveness Obligations from Threads in the Lantana Concurrent Separation
Logic* (POPL 2027); [PAPER.md](PAPER.md) gives the Rocq name of each item of the paper and the
differences between the paper and the current development.

1. [The logic](#the-logic)
2. [Proving a liveness property](#proving-a-liveness-property)
3. [Building](#building)
4. [Axioms and admits](#axioms-and-admits)
5. [Structure](#structure)
6. [Naming conventions](#naming-conventions)
7. [Credits and license](#credits-and-license)

## The logic

A liveness obligation is a resource that must eventually be discharged. Obligations form a
forest: every live obligation has a parent, which is a thread or another obligation. Each step of
a thread burns a unit of fuel of every obligation in its tree (the model keeps the fuel of each
obligation above that of its parent), and fuel is an ordinal measure, so on a fair behavior no
obligation stays assigned forever. Temporal formulas are tied to obligations: `untilI N k q P Q`
says that `P` holds until `Q`, and `Q` comes because `k` must be discharged.

| Concept | Rocq | File |
|---|---|---|
| Thread-local weakest precondition, a least fixpoint; one step is a model update, the physical step with its progress update, and a model update | `lWP e @ s; i; E {{ Φ }}` (`lwp`), texan triples `l{{{ P }}} e @ i; E l{{{ v, RET v; Q }}}`, one step `lwp_step` | `lantana/program_logic/weakestpre.v`, `lwp_notation.v` |
| The obligation predicates and their rules, as an interface that the program logic uses | the class `oblf.obl_forest_interface`: obligations `oblP_*`, witnesses `witP_*`, threads `thP_*`, the children `parP_kids p K` of a parent `p` | `lantana/program_logic/obl_forest.v`, `obl_forest_rules.v` |
| The model update, which changes obligations and witnesses | `\|={E1,E2}=>m P` (a field of the class) | `lantana/program_logic/obl_forest.v` |
| The model of the interface, its only instance | `obl_forest_lantana`, over `omodel` | `lantana/program_logic/obl_forest_instance.v`, `lantana/base_logic/opreds.v` |
| Trace properties, with LTL on traces | `trProp`, `□` `◇` `○` `Uₜ`, entailment `R ⊆ S` | `lantana/trace/trace_prop.v` |
| Trace specifications: a trace property with an internal, step-indexed reading adequate for it | `trSpec` (`trSpec_external`, `trSpec_internal`), entailment `G ⊑ H` | `lantana/trace/trspec.v` |
| Guarantees: whenever `P` holds, the rest of the execution satisfies `G` | `P ⊨ₜ G` (`guar P G`), inferred by `IntoGuar` | `lantana/trace/guarantee.v`, `guarantee_infer.v` |
| Temporal formulas, which are `iProp`s with guarantees | `alwaysI N P`, `untilI N k q P Q`, `finallyI N k q Q` | `lantana/trace/temporal_formula.v`, `temporal_formula_rules.v` |
| Adequacy | `lwp_adequacy_temporal`, `lwp_adequacy_safety_iris` | `lantana/trace/adequacy_temporal.v`, `adequacy_safety.v` |
| HeapLang: the language, its `lWP` laws, and points-to and thread termination as trace atoms | `lwp_load`, `lwp_store`, `lwp_fork`, …; `l ↦ v`, `exits v @ i` | `lantana_heap_lang/primitive_laws.v`, `temporal_laws.v` |

`lwp_adequacy_temporal` states: if the initial resources hold some `P` with `P ⊨ₜ G`, and the
initial threads satisfy their `lWP`s, then every fair behavior from the initial configuration
satisfies `trSpec_external G`, and hence every trace property `R` that it implies. Its proof is
described file by file in [`lantana/trace/README.md`](lantana/trace/README.md).

## Proving a liveness property

`lantana_heap_lang/examples/flag_fork.v` follows these steps for the program `main` of the
paper's §2, which forks a thread that sets a flag and waits for the flag.

1. Specify each module with texan `lWP` triples. Their pre- and postconditions hold the
   thread-expression token `thread_expr i C e`, the children `thP_kids i G` of the thread and
   fuel `oblP_fuel g ℓ μ` for each child `g` (`Flag_init_spec`, `Flag_set_spec` and
   `Flag_wait_spec` in `flag.v`).
2. In the proofs, create obligations (`obl_new`) and temporal formulas (`alwaysI_alloc`,
   `untilI_alloc`) inside model updates `|={E}=>m`, and discharge an until once its right
   formula holds (`untilI_discharge`, `finallyI_discharge`).
3. Give the initial resources an `iProp` `P` with a guarantee `P ⊨ₜ G`, usually inferred with
   `into_guar` (`guar_Φ_P` in `flag_fork.v`).
4. Show that `trSpec_external G` implies the trace property of interest (`G_main_impl`), and
   apply `lwp_adequacy_temporal` (`main_adequacy`). `lwp_adequacy_safety_iris` gives safety in
   the same way (`main_safety_adequacy`).

## Building

The development depends on the following opam packages:

* Rocq 9.0 to 9.3 (`rocq-core`, `rocq-stdlib`)
* std++ `dev.2026-09-17.0.d510b616` (`rocq-stdpp`)
* Iris (`rocq-iris`, `rocq-iris-heap-lang`) from the branch
  [`dongjae/transfinite-base`](https://gitlab.mpi-sws.org/dongjae/iris/-/tree/dongjae/transfinite-base),
  which is upstream Iris master (commit `8e490959`) plus the commits of the Iris branch
  `robbert/transfinite` that change the BI laws to support transfinite step-indexing
* [Transfinite Iris](https://github.com/dongjaelee1/transfinite-iris) (`rocq-iris-transfinite`)
* The Ordinal library `coq-ordinal.0.5.6`

To install them and build:

1. Create an opam switch and switch to it:
   ```
   opam update
   opam switch create lantana 5.2.1
   eval $(opam env)
   ```
2. Run `./configure`. It adds the `coq-released` and `iris-dev` opam repositories, pins Iris and
   Transfinite Iris to the commits listed at the top of `configure`, and installs all of the
   packages above. `NJOBS` sets the build parallelism of the packages (default 8), for example
   `NJOBS=4 ./configure`. To use another commit of Transfinite Iris, set `TRANSFINITE_REPO` and
   `TRANSFINITE_REF`; the Iris commit in `configure` must match the one that the opam file of
   Transfinite Iris pins in its `pin-depends`.
3. Run `make -jN`, where `N` is the number of parallel jobs. `make clean` removes the build
   outputs.

On an Intel Xeon Gold 6354 (3.0 GHz), `make -j3` builds the 118 files from scratch in about
6.5 minutes.

To work on the files, open the repository root in an editor with Rocq support (for instance VS
Code with VsRocq or coq-lsp). The logical paths are `lantana.ordinal` (`ordinal/`), `lantana`
(`lantana/`) and `lantana.heap_lang` (`lantana_heap_lang/`).

## Axioms and admits

The adequacy theorems (`lwp_adequacy_temporal`, `lwp_adequacy_safety_iris`), the end-to-end
theorems of the clients (`*_liveness_safety`, which contain `*_adequacy` and
`*_safety_adequacy`), `no_lc_absurd` and `nonstrict_move_absurd` depend on these seven axioms of
Rocq's standard library:

- `Classical_Prop.classic`
- `Epsilon.epsilon_statement`
- `FunctionalExtensionality.functional_extensionality_dep`
- `ProofIrrelevance.proof_irrelevance`
- `PropExtensionality.propositional_extensionality`
- `ClassicalUniqueChoice.dependent_unique_choice`
- `RelationalChoice.relational_choice`

The case-study specifications (for instance `Flag_set_spec`, `TicketLock_acquire_spec`,
`TaskQueue_worker_spec`) depend on the first five. To check one result, after `make`:
```
rocq top -Q ordinal lantana.ordinal -Q lantana lantana -Q lantana_heap_lang lantana.heap_lang
Require Import lantana.heap_lang.examples.flag_fork.
Print Assumptions main_liveness_safety.
```

`grep -rnwE 'admit|Admitted' lantana lantana_heap_lang` finds nothing. In `ordinal/`, the copy of
the Ordinal library, it finds only commented-out code and an unused tactic (`eadmit` in
`sflib.v`).

## Structure

In dependency order: each directory imports only from the directories listed before it, and has
a README that describes its files.

- [`ordinal/`](ordinal/README.md): a copy of the Ordinal library, used for layers.
- [`lantana/prelude/`](lantana/prelude/README.md): classical axioms, facts about both copies of the
  ordinals, well-founded structures.
- [`lantana/algebra/`](lantana/algebra/README.md): ordered commutative monoids, measures and
  layers, and the cameras of the logic.
- [`lantana/base_logic/`](lantana/base_logic/README.md): the `iProp`-level model: transfinite later
  credits, fancy updates and invariants, and the obligation model (obligations and witnesses,
  their ghost state, the obligation forest, model updates `mupd`, and `omodel`, the model of the
  predicates).
- [`lantana/program_logic/`](lantana/program_logic/README.md): languages with thread ids, traces
  and behaviors, the ghost state of the temporal layer, the obligation-forest interface (the
  predicates, the model update `|={E}=>m` and their rules), and the weakest precondition `lWP`
  with its lifting lemmas.
- [`lantana/trace/`](lantana/trace/README.md): trace properties, trace specifications `trSpec`,
  guarantees `P ⊨ₜ G`, the temporal formulas always, until and finally, and the adequacy
  theorems; the README has a dependency map.
- [`lantana_heap_lang/`](lantana_heap_lang/README.md): HeapLang for Lantana, its `lWP` rules and
  proof mode, and the state atoms of temporal properties.
- [`lantana_heap_lang/examples/`](lantana_heap_lang/examples/README.md): the case studies, with
  end-to-end liveness and safety theorems for the client programs.

## Naming conventions

- `oblP_*` are obligation predicates, `witP_*` witness predicates, `thP_*` per-thread
  predicates, and `parP_*` predicates on parents (`thP_kids i K` and `oblP_kids k K` are
  `parP_kids` at a thread and at an obligation).
- `alwaysI`, `untilI` and `finallyI` are temporal formulas (`iProp`s); a suffix `_guar` marks the
  variant with an explicit guarantee, as in `alwaysI_guar N P G`.
- `guar_*` are rules of guarantees `P ⊨ₜ G`, and `guar_X` is the guarantee of `X` (for example
  `guar_alwaysI`, `guar_is_flag`); `into_guar_*` are `IntoGuar` instances.
- `trSpec_*` are trace specifications, `trI_*` internal readings (`trIProp`), and `tr_*`
  meta-level trace properties (`trProp`).
- `reg_*` are the temporal registry, and `record`, `cert` and `bundle` the records,
  certificates and bundles of the adequacy proof.

## Credits and license

`lantana/` and `lantana_heap_lang/` are new. Some files are adapted from earlier work, as their
headers say:

- HeapLang (apart from `temporal_laws.v` and the examples) from Iris's HeapLang, with thread ids,
  fresh ids for forked threads, `ChooseNat` and `Label`;
- the language interface, the lifting lemmas, logically atomic triples and the `lWP` notations
  (`lantana/program_logic/`) from Iris, and `weakestpre.v` follows the structure of Iris's
  weakest precondition;
- fancy updates, invariants, satisfiability and invariant locations (`lantana/base_logic/`) from
  Transfinite Iris, and the relational updates and later credits from the artifact of
  *Later Credits* (Spies et al., 2022);
- ordered commutative monoids and the bank and bounded-credit cameras (`lantana/algebra/`) from
  the Lilo and FOS developments.

The `ordinal/` directory is a copy of the Ordinal library, available at
https://github.com/snu-sf/Ordinal (MIT license, `ordinal/LICENSE`).

The mechanization of set-theoretic ordinals and of the underlying ZF model in Transfinite Iris is
based on Coq code by Dominik Kirst and Gert Smolka:

* "Large Model Constructions for Second-Order ZF in Dependent Type Theory", Dominik Kirst and
  Gert Smolka, CPP 2018,
  https://www.ps.uni-saarland.de/Publications/details/KirstSmolka:2017:Large-Model.html
* "Formalised Set Theory: Well-Orderings and the Axiom of Choice", Dominik Kirst,
  https://www.ps.uni-saarland.de/~kirst/bachelor.php

The development is under the BSD-3-Clause license (`LICENSE`); the copy of the Ordinal library is
under the MIT license (`ordinal/LICENSE`).
