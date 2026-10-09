## Installation

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

## Structure

The directories, in dependency order. Each has a README that describes its files and the
dependencies between them.

- [`lantana/prelude/`](lantana/prelude/README.md): classical axioms, ordinal facts, well-founded relations.
- [`lantana/ordinal/`](lantana/ordinal/README.md): a copy of the Ordinal library, used for layers.
- [`lantana/algebra/`](lantana/algebra/README.md): resource algebras, measures and layers.
- [`lantana/base_logic/`](lantana/base_logic/README.md): ghost state for obligations, threads,
  carriers and witnesses; the model and ghost updates; transfinite later credits.
- [`lantana/bi/`](lantana/bi/README.md): the interface and notation of `lWP`.
- [`lantana/program_logic/`](lantana/program_logic/README.md): languages, traces and fair
  scheduling, `lwp`, temporal formulas, and the adequacy theorems.
- [`lantana_heap_lang/`](lantana_heap_lang/README.md): HeapLang, its `lWP` rules, and the
  fuel-burning triple (`triple.v`).
- [`lantana_heap_lang/examples/`](lantana_heap_lang/examples/README.md): the case studies.

## Axioms

`lantana_heap_lang/examples/assumptions.v` prints the axioms of the main results when it is built
(`make` shows the output). The adequacy theorems (`lwp_adequacy`, `lwp_adequacy_safety_iris`), the
twelve client theorems and `no_lc_absurd` assume these seven axioms of Rocq's standard library:
`Classical_Prop.classic`, `Epsilon.epsilon_statement`,
`FunctionalExtensionality.functional_extensionality_dep`, `ProofIrrelevance.proof_irrelevance`,
`PropExtensionality.propositional_extensionality`, `ClassicalUniqueChoice.dependent_unique_choice`
and `RelationalChoice.relational_choice`. The rules of `triple.v` and the case-study
specifications assume the first five.

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

Section and figure numbers refer to the submitted version of the paper.

### The fuel-burning triple

The paper presents Lantana through the *fuel-burning triple*
`{P}^G_i e {v. Q v}^G'_E`. In Rocq it is `fbtriple`, defined in
`lantana_heap_lang/triple.v` on top of the thread-local weakest precondition
`lwp` (notation `lWP e @ s; i; E {{ Φ }}`, `lantana/program_logic/weakestpre.v`):

```
fbtriple_gen s i C E G P e Q :=
  ∀ Φ, thread_expr i C e ∗ thP_carriers i G ∗ P -∗
       (∀ v, thread_expr i C (of_val v) ∗ Q v -∗ Φ v) -∗
       lWP e @ s; i; E {{ Φ }}
fbtriple s i C E G G' P e Q := fbtriple_gen s i C E G P e (λ v, thP_carriers i G' ∗ Q v)
```

with the notation `⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q ⦄^G'`, written
`⦃ P ⦄^G e @ i; C; E ⦃ v, Q ⦄^G'` when `s` is `NotStuck`. The Rocq triple makes
explicit what the paper leaves implicit:
- the stuckness `s` and the invariant mask `E`;
- the evaluation context `C` around `e` in thread `i`'s expression. The triple
  carries the thread-expression token `thread_expr i C e` (thread `i`'s
  expression is exactly `C[e]`) and the carrier assertion `thP_carriers i G`,
  which is the paper's carrier-set superscript. Neither appears in `P` or `Q`.
  A top-level triple has `C = []`, and its token for a value `v` is `exits v@i`.

`fbtriple_gen`, written `⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q ⦄` (no final
superscript), is the general form, whose postcondition states the final carriers
itself. A specification needs it when the final carrier set depends on variables
of the postcondition: SPEC-ACQUIRE's new carrier `g_u`, for example. The paper
writes such a set in the superscript.

As in the paper, a triple is not persistent. A *specification* is a persistent
triple, `□ ∃ μ, ∀ …, ⦃ P ⦄^G e @ i; C; E ⦃ v, Q ⦄^G'`. `spec_persistent_intro`
shows that the `□` can be introduced in front of any closed statement.
`fbtriple_texan` shows that a persistent triple `□ fbtriple …` is the
texan-style `lwp` triple `l{{{ … }}} e @ s; i; E l{{{ … }}}` with the token and
the carriers spelled out.

The case studies prove their specifications in this texan form, with explicit
`thread_expr`, `thP_carriers`, `crP_fuel`, and `crP_obls` assertions. They
restate each one in the paper's format as a corollary named `*_fbspec` (see
"Case studies" below). The closed specifications (`main`, and the flag client's
`writer` and `reader`) are proved in the paper's format directly, ending with no
carriers. Their texan form, in which the thread has terminated, follows from
that (`fbtriple_top_texan`, or the same argument inline), and is the form the
adequacy proofs use.

Every rule the paper displays for the triple is proved in `triple.v` as an
`fbtriple_*` lemma, and the paper's logic-level rules are restated there under
the paper's names (tables below). The Rocq statements contain the later
modalities, masks, and later credits that the paper elides. Three rules differ
from the submitted paper's displays:
- CARRIER-ALLOC and CARRIER-DELETE: the post-carriers are the same set `G'` in
  the premise and the conclusion. The paper's displays have different
  post-carriers there (`{g} ∪ G` and `G` for CARRIER-ALLOC, `G ∖ {g}` and `G`
  for CARRIER-DELETE).
- FINALLY-EXIT*: there is no `Return` (HeapLang has no `Label`; see
  "Termination" below). The thread's last step (a pure step to the value `v` at
  the empty context) discharges the exit obligation, whose `finally` predicate
  is `exits v@i`.

WIT-IND is as displayed, provided the `⇛` in its induction hypothesis is read
as the fancy wand `wcred k -∗ |⇛ …` (`={E}=∗` in Rocq). Its premise is
persistent, since every iteration uses it. Its induction hypothesis is used
once: it carries the remaining witness budget. The submitted paper says that
`⇛` is Iris's view shift (§3.1), which is persistent; read that way, the
displayed hypothesis is stronger than the one Rocq proves.

STEP-PURE and STEP-PURE-LC are as displayed: they step only to a value. §2
also applies STEP-PURE to steps into non-values, such as the β-step of
`main ()` (§2.1). Rocq takes those with `fbtriple_pure_step`, which the paper
does not display. The proof of `main` from the triple rules alone
(`FlagFork_main_fbspec`) also uses two other undisplayed rules,
`fbtriple_wand_pre` and `fuels_layer_eq` (see the rules table).

Naming conventions: `crP_*` are carrier predicates, `oblP_*` obligation
predicates, `witP_*` witness predicates, `thP_*` per-thread predicates,
`tf_*` the syntax of separation-logic temporal formulas (interpreted into
`iProp` by `⟦·⟧ₗ`), and `tp`/`tr_*` meta-level temporal trace properties.

### Predicates (Fig. 1, §2–§6)

Files are under `lantana/` unless they start with `lantana_heap_lang/`.

| Paper | Rocq | File |
|---|---|---|
| `{P}^G_i e {v. Q v}^G'_E` (fuel-burning triple) | `fbtriple`, notation `⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q ⦄^G'`; the general form `fbtriple_gen`, notation `⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q ⦄`, whose `Q` states the final carriers | `lantana_heap_lang/triple.v` |
| specification `∃ μ. {P}^G e {v. Q}^G'` (`□` and the `∀` omitted) | `□ ∃ μ, ∀ …, ⦃ P ⦄^G e @ i; C; ⊤ ⦃ v, Q ⦄^G'`; `spec_persistent_intro`; `fbtriple_texan`. The `□` is in front: the unfolded form in §3.3, `∃ μ. ∀ …. isFlag x ℓ k ∗ k ∈ K ⇒ □ {…}`, puts it after the quantifiers and the persistent assumptions, which Rocq puts in the precondition | `lantana_heap_lang/triple.v` |
| carrier superscripts / `carriers_i G` (Thm 1) | `thP_carriers i G` | `base_logic/opreds.v` |
| `exit v` (termination with value `v`; established by `Return v`, i.e. `Label "exit" v`) | `exits v@i` (`thread_expr i [] v`): thread `i`'s whole expression is `v`. It is an instance of the thread-expression token `thread_expr i C e`, which the submitted paper does not have (see "Termination" below) | `lantana_heap_lang/primitive_laws.v` |
| `Fuel^ℓ_G μ` | `fuels G ℓ μ := [∗ set] g ∈ G, crP_fuel g ℓ μ`; one carrier: `crP_fuel g ℓ μ` | `lantana_heap_lang/triple.v`, `base_logic/opreds.v` |
| `obls^ℓ_g K` | `crP_obls g ℓ K` | `base_logic/opreds.v` |
| `Φ until^k_q Ψ` | `tf_until N k b q P Q`, notation `untilP N k q P Q` (`N` is the invariant namespace; the flag `b` is needed for the adequacy proof, and our examples fix it to `false`) | `program_logic/temporal_logic.v` |
| `finally^k Φ` | `tf_finally`, notation `finallyP N k q Q` | `program_logic/temporal_logic.v` |
| `obl_■ k` (discharged) | `oblP_discharged k` | `base_logic/opreds.v` |
| `tr$^ℓ_k m` (transfer credit) | `oblP_fuel k ℓ m` (the obligation's own fuel) | `base_logic/opreds.v` |
| `wit^ℓ k` (witness) | `witP_layer k ℓ` | `base_logic/opreds.v` |
| `wit€ k` (witness credit, §4.1) | `witP_cred k a`, where the amount `a` is an ordinal | `base_logic/opreds.v` |
| `■ i` (thread finished, Thm 1) | `thP_done i` | `base_logic/opreds.v` |
| `always I` | `tf_always`, notation `alwaysP N I` (with the invariant machinery of `base_logic/invariants.v`) | `program_logic/temporal_logic.v` |
| `£ α` (transfinite later credits) | later-credit predicate and `tlc_*` lemmas | `base_logic/later_credits.v` |
| `Measure` (§3.1; the extension measure `▽`, §4.1) | inductive `measure`; `▽` is the constructor `ms_extend`, and `+`, `×`, `μ1^μ2` are `⊕`, `×`, `↑`; interpretation into ordinals via `measure_rep_rec`. There is no `ω` constructor: `ms_embed` embeds an element of any well-founded relation (`ms_nat n`, a coercion, gives `n`), and `ms_large` (`ℵ`) is a large ordinal, not in the paper's grammar | `algebra/measure.v` |
| layers `ℓ` (ordinals) | `ℓ : ord.t`, from the copy of the Ordinal library in `lantana/ordinal/` (a second copy sidesteps a universe inconsistency). Measures are interpreted at internal layers `layer := ord.t × nat`, an instance of `layer_class`; a layer `ℓ` is `(ℓ, 0)` | `algebra/layer.v`, `algebra/measure.v` |

Termination differs from the submitted paper:
- The paper states termination with the ghost construct `Label`: `Return v` is
  `Label "exit" v`, `exit v` says that some thread is evaluating `Return v`,
  and the trace atom is `label_i s v` (§6.1). The Rocq HeapLang has no
  `Label`. Termination is `exits v@i`, the exclusive thread-expression token
  `thread_expr i C e` (thread `i`'s expression is `C[e]`) at the empty context:
  it holds only when thread `i`'s whole expression is `v`.
- The closed programs end with a plain value (`…; wait x; 42`) instead of
  `Return 42`, and their specifications use `finally (exits v@i)` instead of
  `finally [exit v]`.
- The triple carries the token, so no rule or specification mentions it. The
  clients' adequacy proofs get each thread's initial token from
  `thread_map_init` (`base_logic/thread_map.v`).

### Rules (§2, Figs. 3–5, §5)

The triple-level lemmas are in `lantana_heap_lang/triple.v`; the last column
names the underlying lemmas.

| Paper rule | Rocq (`triple.v`) | Underlying |
|---|---|---|
| STEP-PURE, STEP-PURE-LC, STEP-PURE-WIT | `fbtriple_step_pure`, `fbtriple_step_pure_lc`, `fbtriple_step_pure_wit1` (one obligation `k`, as displayed) and `fbtriple_step_pure_wit` (a set `R` of obligations, each reported as `witP_cred r 1 ∨ oblP_discharged r`). These step to a value; `fbtriple_pure_step` (not displayed in the paper) takes a pure step to any expression, such as a function call's β-step | `lwp_pure_step` (`program_logic/lifting.v`, HeapLang instance in `lantana_heap_lang/primitive_laws.v`) |
| STEP-REF / STEP-STORE / STEP-LOAD | `fbtriple_step_ref` / `fbtriple_step_store` / `fbtriple_step_load` | `lwp_alloc` / `lwp_store` / `lwp_load` (`lantana_heap_lang/primitive_laws.v`) |
| FORK* | `fbtriple_fork1` (as displayed) and `fbtriple_fork` (moves a set `K ⊆ K1` of obligations to the child); the child's premise is a top-level triple for every thread `j` and carrier `g2`, ending with no carriers | `lwp_fork_step` (`lantana_heap_lang/primitive_laws.v`) |
| EXIT | `fbtriple_exit`; `fbtriple_top_lwp` turns a top-level triple from and to the empty carrier set into the `lwp` that Theorem 1 consumes | value case of `lwp`; `thread_terminate` (`program_logic/sfgupd.v`) |
| FINALLY-EXIT* | `fbtriple_finally_exit` (the thread's last pure step discharges `finally (exits v@i)`; see above) | `tf_until_discharge`, `carrier_delete`; the case studies use the same reasoning packaged as `thread_expr_exit` (`lantana_heap_lang/primitive_laws.v`) |
| FINALLY-ALLOC* | `fbtriple_finally_alloc` | `tf_until_alloc` (`program_logic/temporal_logic.v`) |
| BIND | `fbtriple_bind` (the premise is at context `K ++ C`); for the general form, `fbtriple_gen_bind`, whose first postcondition names the intermediate carriers | `lwp_bind` (`program_logic/weakestpre.v`) |
| FRAME | `fbtriple_frame`; `fbtriple_gen_frame` for the general form | `lwp_strong_mono` |
| (not displayed) moving precondition resources into the context | `fbtriple_wand_pre`, `fbtriple_gen_wand_pre`: `(R -∗ {P} e {Q}) ⊢ {P ∗ R} e {Q}`, which holds because triples are not persistent | |
| UPD-ELIM | `fbtriple_upd_elim` (fancy update), `fbtriple_gupd_elim` (ghost update) | `fupd_lwp`, `sfgupd_elim_lwp` (`program_logic/weakestpre.v`) |
| CARRIER-ALLOC | `fbtriple_carrier_alloc` (same post-carriers in premise and conclusion) | `carrier_alloc` (`program_logic/sfgupd.v`) |
| CARRIER-DELETE | `fbtriple_carrier_delete` (same post-carriers in premise and conclusion) | `carrier_delete` (`program_logic/sfgupd.v`) |
| OBLS-OFFLOAD | `fbtriple_obls_offload` | `obl_offload_set` (`program_logic/sfgupd.v`) |
| ALWAYS-ALLOC / ALWAYS-ACC | `fbtriple_always_alloc` / `fbtriple_always_acc` | `tf_always_logic` (`program_logic/temporal_logic.v`) and the invariant rules of `base_logic/invariants.v` |
| UNTIL-ALLOC | `fbtriple_until_alloc` | `tf_until_alloc` |
| UNTIL-ACC | `fbtriple_until_acc` (the access takes a later, paid with `£ 1`) | `tf_until_acc` |
| UNTIL-DISCHARGE | `fbtriple_until_discharge` (paid with `£ 2`) | `tf_until_discharge` |
| WIT-IND | `fbtriple_wit_ind` (as displayed, with the induction hypothesis's `⇛` read as the one-shot fancy wand: see above) | `wit_layer_ind` (`base_logic/opreds.v`) |
| FUELS-ADD / FUELS-UNION / FUELS-EMPTY / FUELS-LAYER | `fuels_add` / `fuels_union` / `fuels_empty` (generalized by `fuels_weaken`) / `fuels_layer` | `crP_fuel_add_set` / big-op union / empty big-op / `crP_fuel_extend_set` (`base_logic/opreds.v`) |
| (not displayed) FUELS-MONO: fuel can be lowered to a smaller measure | `fuels_mono` (an update; the measures are compared by their interpretations at layer `ℓ`) | `crP_fuel_mon_set` (`base_logic/opreds.v`) |
| (not displayed) layers compared as ordinals | `fuels_layer_eq` (`ℓ1 == ℓ2`, e.g. `0 ⊕ 1` and `1`) | `crP_fuel_layer_eq_set` |
| UNTIL-DONE-FALSE / UNTIL-SPLIT | `until_done_false` / `until_split` | `tf_until_discharged_false` / `tf_until_fractional` (also `tf_until_frac_split`, `tf_until_frac_add`) |
| LÖB / LC-SPEND | `lob` / `lc_spend` | Löb induction of Transfinite Iris (`iLöb`) / `lc_fupd_elim_later_ord` (`base_logic/fancy_updates.v`); see also `tlc_later` (`base_logic/later_credits.v`) |
| persistence facts | `always_persistent`, `persistently_persistent`, `persistent_dup`, `wit_layer_persistent`, `obl_done_persistent` | |

The step rules of `primitive_laws.v` accept one unit of fuel at any layer; the
triple-level step rules state the paper's layer-0 form.

### Traces, temporal properties, and adequacy (§6, Fig. 6)

| Paper | Rocq | File (under `lantana/` unless it starts with `lantana_heap_lang/`) |
|---|---|---|
| `Cfg`, `TPool`, THREAD-STEP/THREAD-DONE, `Trace`, `Behavior` | `trace_state` (a `cfg`, i.e. a `thread_pool` and a state, with the scheduled thread), `thread_step`, `thread_done`, `trace`, `behavior` (the observations `κ : list (observation Λ)` only serve HeapLang's prophecy variables, which no example uses). Unlike Fig. 6, a behavior also lets a scheduled stuck thread stutter (`thread_stuck`), so executions that get stuck are behaviors too | `program_logic/language.v` |
| temporal properties `Φ, Ψ` and `⟦·⟧_t` | syntax `tp`, interpretation `tp_trace`; `Always` = `tr_always`, `Until` = `tr_until`, `Finally` = `tr_eventually` | `program_logic/temporal_property.v` |
| `Fair` (fair scheduling) | `fair_scheduling`; `inactive`, `active`, `turn` are `thread_na`, `thread_active`, `thread_turn` | `program_logic/temporal_property.v` |
| logical assertions `φ` and `⟦·⟧_l` | syntax `tf`, interpretation `⟦·⟧ₗ` | `program_logic/temporal_logic.v` |
| `lift` | `tf_to_tp` | `program_logic/adequacy.v` |
| `ChooseNat` | `ChooseNat` | `lantana_heap_lang/lang.v` |
| atomic properties `x ↦ v` and `label_i s v`, with `exit v := ∃ i. label_i "exit" v` | `l ↦ v` (`pred_pointsto`) and `pred_expr i C e` (thread `i`'s expression is `C[e]`), in scope `tp_scope`; there is no label atom, and termination is `exits v@i` (`pred_expr i [] v`). `exits_finally_iff`: `Finally [exits v@i]` holds iff thread `i`'s whole expression eventually is `v` | `lantana_heap_lang/lang.v`, `lantana_heap_lang/primitive_laws.v` |
| `lwp` | `lwp`, notation `lWP e @ s; i; E {{ Φ }}` | `program_logic/weakestpre.v` |
| obligation state `Ω`, witness state `W` | `obls` (`gmap oid obl`), `witnesses` (`gmap oid witness`) | `base_logic/obligation.v`, `base_logic/witness.v` |
| model interpretation `M` | `model_interp` | `base_logic/mupd.v` |
| model update modality | `mupd` / `fmupd`; the `lwp`-facing forms are `sfmupd`, `sfgupd`, and `lwpupd` | `base_logic/mupd.v`, `program_logic/sfmupd.v`, `program_logic/sfgupd.v`, `program_logic/weakestpre.v` |
| fair-scheduler invariant `H` | `owit_inv` | `base_logic/owit.v` |
| state interpretation `S` | `state_interp` (heap-lang instance) and `history_interp` (wrapper for adequacy proof) | `lantana_heap_lang/primitive_laws.v`, `program_logic/history_interp.v` |
| **Theorem 1 (Adequacy)** | `lwp_adequacy`. Unlike the displayed theorem, its premise also grants initial later credits `£ c` (the proof picks `c`), and the weakest preconditions must be `NotStuck`: the paper's `lwp` has no stuckness parameter, and its step case requires `reducible`. A stuck scheduled thread contradicts that reducibility. It starts a whole thread pool `Θ` (with postconditions `Ψs`, each `lwp` under `lwpupd`), and `ψ v ∗ ■ i` is `lift_term i Ψ` | `program_logic/adequacy.v` |
| Iris-style safety (cf. Iris's `adequate`; not in the submitted paper) | `lwp_adequacy_safety_iris`: in every fair behavior the scheduled thread is never stuck, so no stuck transition happens, and whenever thread `j` is a value `v`, its postcondition holds (`safety_iris`). It assumes the same behaviors as `lwp_adequacy` | `program_logic/adequacy_iris.v`, `program_logic/language.v`, `program_logic/temporal_property.v` |

### Case studies (§2 to §7)

All in `lantana_heap_lang/examples/`.

| Paper | Rocq | File |
|---|---|---|
| Flag module: `init`/`set`/`wait`; `isFlag`; `FlagObl`; SPEC-INIT/SPEC-SET/SPEC-WAIT | `init`/`set`/`wait`; `is_flag x k ℓ` (arguments in another order; syntactic form `is_flag_tf`); `flag_tk`; `Flag_init_fbspec` / `Flag_set_fbspec` / `Flag_wait_fbspec` (from `Flag_*_spec`). In `Flag_set_fbspec`, the carrier's layer `ℓg` (`crP_obls g ℓg K`) is independent of the flag's layer `ℓ`, while SPEC-SET uses `ℓ` for both: TaskSpec quantifies over the carrier's layer, so `decr` (§7.3) calls `set` at any carrier layer | `flag.v` |
| `main` (§2) and its trace property | `main`; `FlagFork_main_fbspec`, proved with the rules of `triple.v` and the flag specifications only, following §2's walkthrough and §2.2's budgets (see below; texan form `FlagFork_main_spec`); end-to-end `main_adequacy` | `flag_fork.v` |
| `nest` / `nondet` (§4.3); SPEC-NEST/SPEC-NONDET | `nest` / `nondet`; `Nondet_nest_fbspec` / `Nondet_nondet_fbspec` (from `Nondet_*_spec`). `Nondet_nondet_fbspec` ends with the carriers `G`, which SPEC-NONDET's empty post superscript leaves out | `nondet.v` |
| Handoff: `send`/`receive`; `HandoffBuf`; `polling`; `HInv`; `TaskSpec`; SPEC-SEND/SPEC-RECEIVE | `send`/`receive`; `handoff_inv`; `ghost_var (handoff_γd γ)`; `is_handoff`; `is_task` (in the paper's format: `is_task_fbtriple`, whose triple is persistent, `□`, unlike TaskSpec's); `Handoff_send_fbspec` / `Handoff_receive_fbspec` (from `Handoff_*_spec`) | `handoff.v` |
| `handoffMain` (§5.2); SPEC-HANDOFF-MAIN | `main`, `main_fbspec` (texan form `main_spec`), `handoff_client_adequacy` | `handoff_client.v` |
| Ticket lock (§7.1): `TLInv`; `TLObl`; SPEC-ACQUIRE/SPEC-RELEASE | `TLInv` is `is_fair_lock tl γ R ∗ γ ↪LOCK_AL□ ∗ γ ↪LOCK_CF□ ℓ`, which is persistent: the specifications take the alive and configuration tokens at any fraction, and `lock_alive_persist` / `lock_config_persist` make them persistent (as `queue.v` does); `lock_token`; `TicketLock_init_fbspec` / `TicketLock_acquire_fbspec` (general form) / `TicketLock_release_fbspec` / `TicketLock_delete_fbspec` (from `TicketLock_*_spec`; the specifications in Rocq are more generalized than ones in the paper) | `ticket_lock.v` |
| Queue (§7.2): `QInv` (`QData`/`QState`/`QObls`/`QPrimary`); SPEC-ENQUEUE/SPEC-DEQUEUE | `is_queue`, built from `queue_inv` (`QObls`), `queue_lock` (`QState`), `queue_contents` (`QData`) and `qG_queue` (`QList`); `queue_worker` is `QPrimary`; `Queue_init_fbspec` / `Queue_enqueue_fbspec` / `Queue_dequeue_fbspec` (general form; the paper shows the non-worker, non-empty case) (from `Queue_*_spec`) | `queue.v` |
| Task queue (§7.3): `TQInv`; SPEC-PUT-TASK/SPEC-WORKER | `is_task_queue`; `TaskQueue_init_fbspec` / `TaskQueue_put_task_fbspec` / `TaskQueue_run_task_fbspec` (general form) / `TaskQueue_worker_fbspec` (from `TaskQueue_*_spec`) | `task_queue.v` |
| Reentrant client `decr` / `clientMain` (§7.3); SPEC-DECR/SPEC-DECR-CLIENTMAIN | `decr_reentrant` / `main`; `decr_reentrant_fbspec` (from `decr_reentrant_spec`) / `main_fbspec` (texan form `main_spec`); `task_queue_client_adequacy` | `task_queue_client.v` |

Two proofs differ from the submitted paper's text:
- §2.5's budgets for `main` differ from §2.2's, and `FlagFork_main_fbspec`
  follows §2.2: `g_e`'s layer-1 budget is `1 ⊕ (μ_wait ⊕ 1)`, whose first unit
  becomes the layer-0 fuel `1 ⊕ μ0` with `μ0 = μ_init ⊕ 5`, and `g_f` gets `μ0`.
  §2.5 instead gives `g_e` the budget `100 + μ_init + μ_wait` and uses `μ_set`
  for `g_f`. In the proof, `μ_set` is the budget of the child's carrier at
  FORK*, as in §2.3.
- §7.1 says that the waiter in `acquire` reasons by witness induction on the
  current owner's obligation `κ` alone. `TicketLock_acquire_spec` uses two
  nested inductions: an outer one on the number of threads ahead of the waiter
  (`embed_fuels`), and, for each owner, an inner one on the witness budget of
  its unlock obligation (`wit_fuels`). Each release creates a new owner
  obligation, so one `κ` is not enough.

The per-example `*_adequacy` theorems (`flag_client_adequacy`, `main_adequacy`,
`handoff_client_adequacy`, `task_queue_client_adequacy`) are end-to-end
instantiations of Theorem 1, deriving the trace-level temporal property of the
respective client program. The `*_safety_adequacy` theorems
(`flag_client_safety_adequacy`, `main_safety_adequacy`,
`handoff_client_safety_adequacy`, `task_queue_client_safety_adequacy`)
instantiate `lwp_adequacy_safety_iris` for the same programs: in every fair behavior,
the scheduled thread is never stuck, and each thread that terminates returns the
value its specification promises. Since both theorems assume the same behaviors, the
`*_liveness_safety` corollaries (`main_liveness_safety`, `handoff_client_liveness_safety`,
`task_queue_client_liveness_safety`, `flag_client_liveness_safety`) state both at once.
`flag_client.v` uses adequacy to prove a property about a memory location, beyond termination;
its threads' closed specifications are `writer_fbspec` and `reader_fbspec`.
`paradox.v` proves the unsoundness counterexample remarked at the end of §6.2: `no_lc_absurd`
derives `False` from a fuel-free pure-step rule (the class `lantanaGS_no_lc`, one pure step
without fuel, for HeapLang instances), through `loop_paradox` and the concrete fair run `loop_run`
of two looping threads.
