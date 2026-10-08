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
  the premise and the conclusion.
- FINALLY-EXIT*: there is no `Return`. The thread's last step (a pure step to
  the value `v` at the empty context) discharges the exit obligation, whose
  `finally` predicate is `exits v@i`.

WIT-IND is as displayed. Its premise is persistent, since every iteration uses
it. Its induction hypothesis is an ordinary, non-persistent triple: it can be
used once, because it carries the remaining witness budget.

Naming conventions: `crP_*` are carrier predicates, `oblP_*` obligation
predicates, `witP_*` witness predicates, `thP_*` per-thread predicates,
`tf_*` the syntax of separation-logic temporal formulas (interpreted into
`iProp` by `⟦·⟧ₗ`), and `tp`/`tr_*` meta-level temporal trace properties.

### Predicates (Fig. 1, §3–§5)

Files are under `lantana/` unless they start with `lantana_heap_lang/`.

| Paper | Rocq | File |
|---|---|---|
| `{P}^G_i e {v. Q v}^G'_E` (fuel-burning triple) | `fbtriple`, notation `⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q ⦄^G'`; the general form `fbtriple_gen`, notation `⦃ P ⦄^G e @ s; i; C; E ⦃ v, Q ⦄`, whose `Q` states the final carriers | `lantana_heap_lang/triple.v` |
| specification `∃ μ. {P}^G e {v. Q}^G'` (`□` and the `∀` omitted) | `□ ∃ μ, ∀ …, ⦃ P ⦄^G e @ i; C; ⊤ ⦃ v, Q ⦄^G'`; `spec_persistent_intro`; `fbtriple_texan` | `lantana_heap_lang/triple.v` |
| carrier superscripts / `carriers_i G` (Thm 1) | `thP_carriers i G` | `base_logic/opreds.v` |
| thread `i`'s expression; termination with value `v` | `thread_expr i C e`; `exits v@i` (`thread_expr i [] v`) | `lantana_heap_lang/primitive_laws.v` |
| `Fuel^ℓ_G μ` | `fuels G ℓ μ := [∗ set] g ∈ G, crP_fuel g ℓ μ`; one carrier: `crP_fuel g ℓ μ` | `lantana_heap_lang/triple.v`, `base_logic/opreds.v` |
| `obls^ℓ_g K` | `crP_obls g ℓ K` | `base_logic/opreds.v` |
| `Φ until^k_q Ψ` | `tf_until N k b q P Q`, notation `untilP N k q P Q` (`N` is the invariant namespace; the flag `b` is needed for the adequacy proof, and our examples fix it to `false`) | `program_logic/temporal_logic.v` |
| `finally^k Φ` | `tf_finally`, notation `finallyP N k q Q` | `program_logic/temporal_logic.v` |
| `obl∎ k` (discharged) | `oblP_discharged k` | `base_logic/opreds.v` |
| `tr$^ℓ_k m` (transfer credit) | `oblP_fuel k ℓ m` (the obligation's own fuel) | `base_logic/opreds.v` |
| `wit^ℓ k` (witness) | `witP_layer k ℓ` | `base_logic/opreds.v` |
| `wit€ k` (witness credit, §4.1) | `witP_cred k a`, where the amount `a` is an ordinal | `base_logic/opreds.v` |
| `∎ i` (thread finished, Thm 1) | `thP_done i` | `base_logic/opreds.v` |
| `always I` | `tf_always`, notation `alwaysP N I` (with the invariant machinery of `base_logic/invariants.v`) | `program_logic/temporal_logic.v` |
| `£ α` (transfinite later credits) | later-credit predicate and `tlc_*` lemmas | `base_logic/later_credits.v` |
| `Measure` (with extension measure `∇`, §3.2) | inductive `measure`; `∇` is the constructor `ms_extend`; interpretation into ordinals via `measure_rep_rec` | `algebra/measure.v` |
| layers `ℓ` (ordinals) | `ℓ : ord.t`, from the copy of the Ordinal library in `lantana/ordinal/` (a second copy sidesteps a universe inconsistency). Measures are interpreted at internal layers `layer := ord.t × nat`, an instance of `layer_class`; a layer `ℓ` is `(ℓ, 0)` | `algebra/layer.v`, `algebra/measure.v` |

### Rules (Figs. 3–6, §5)

The triple-level lemmas are in `lantana_heap_lang/triple.v`; the last column
names the underlying lemmas.

| Paper rule | Rocq (`triple.v`) | Underlying |
|---|---|---|
| STEP-PURE, STEP-PURE-LC, STEP-PURE-WIT | `fbtriple_step_pure`, `fbtriple_step_pure_lc`, `fbtriple_step_pure_wit1` (one obligation `k`, as displayed) and `fbtriple_step_pure_wit` (a set `R` of obligations, each reported as `witP_cred r 1 ∨ oblP_discharged r`) | `lwp_pure_step` (`program_logic/lifting.v`, HeapLang instance in `lantana_heap_lang/primitive_laws.v`) |
| STEP-REF / STEP-STORE / STEP-LOAD | `fbtriple_step_ref` / `fbtriple_step_store` / `fbtriple_step_load` | `lwp_alloc` / `lwp_store` / `lwp_load` (`lantana_heap_lang/primitive_laws.v`) |
| FORK* | `fbtriple_fork1` (as displayed) and `fbtriple_fork` (moves a set `K ⊆ K1` of obligations to the child); the child's premise is a top-level triple for every thread `j` and carrier `g2`, ending with no carriers | `lwp_fork_step` (`lantana_heap_lang/primitive_laws.v`) |
| EXIT | `fbtriple_exit`; `fbtriple_top_lwp` turns a top-level triple ending with no carriers into the `lwp` that Theorem 1 consumes | value case of `lwp`; `thread_terminate` (`program_logic/sfgupd.v`) |
| FINALLY-EXIT* | `fbtriple_finally_exit` (the thread's last pure step discharges `finally (exits v@i)`; see above) | `tf_until_discharge`, `carrier_delete`; the case studies use the same reasoning packaged as `thread_expr_exit` (`lantana_heap_lang/primitive_laws.v`) |
| FINALLY-ALLOC* | `fbtriple_finally_alloc` | `tf_until_alloc` (`program_logic/temporal_logic.v`) |
| BIND | `fbtriple_bind` (the premise is at context `K ++ C`) | `lwp_bind` (`program_logic/weakestpre.v`) |
| FRAME | `fbtriple_frame` | `lwp_strong_mono` |
| UPD-ELIM | `fbtriple_upd_elim` (fancy update), `fbtriple_gupd_elim` (ghost update) | `fupd_lwp`, `sfgupd_elim_lwp` (`program_logic/weakestpre.v`) |
| CARRIER-ALLOC | `fbtriple_carrier_alloc` (same post-carriers in premise and conclusion) | `carrier_alloc` (`program_logic/sfgupd.v`) |
| CARRIER-DELETE | `fbtriple_carrier_delete` (same post-carriers in premise and conclusion) | `carrier_delete` (`program_logic/sfgupd.v`) |
| OBLS-OFFLOAD | `fbtriple_obls_offload` | `obl_offload_set` (`program_logic/sfgupd.v`) |
| ALWAYS-ALLOC / ALWAYS-ACC | `fbtriple_always_alloc` / `fbtriple_always_acc` | `tf_always_logic` (`program_logic/temporal_logic.v`) and the invariant rules of `base_logic/invariants.v` |
| UNTIL-ALLOC | `fbtriple_until_alloc` | `tf_until_alloc` |
| UNTIL-ACC | `fbtriple_until_acc` (the access takes a later, paid with `£ 1`) | `tf_until_acc` |
| UNTIL-DISCHARGE | `fbtriple_until_discharge` (paid with `£ 2`) | `tf_until_discharge` |
| WIT-IND | `fbtriple_wit_ind` (as displayed: a persistent premise, and a non-persistent triple as the induction hypothesis) | `wit_layer_ind` (`base_logic/opreds.v`) |
| FUELS-ADD / FUELS-UNION / FUELS-EMPTY / FUELS-LAYER | `fuels_add` / `fuels_union` / `fuels_empty` (generalized by `fuels_weaken`) / `fuels_layer` | `crP_fuel_add_set` / big-op union / empty big-op / `crP_fuel_extend_set` (`base_logic/opreds.v`) |
| FUELS-MONO (fuel can be lowered to a smaller measure) | `fuels_mono` | `crP_fuel_mon_set` (`base_logic/opreds.v`) |
| UNTIL-DONE-FALSE / UNTIL-SPLIT | `until_done_false` / `until_split` | `tf_until_discharged_false` / `tf_until_fractional` (also `tf_until_frac_split`, `tf_until_frac_add`) |
| LÖB / LC-SPEND | `lob` / `lc_spend` | Löb induction of Transfinite Iris (`iLöb`) / `lc_fupd_elim_later_ord` (`base_logic/fancy_updates.v`); see also `tlc_later` (`base_logic/later_credits.v`) |
| persistence facts | `always_persistent`, `persistently_persistent`, `persistent_dup`, `wit_layer_persistent`, `obl_done_persistent` | |

The step rules of `primitive_laws.v` accept one unit of fuel at any layer; the
triple-level step rules state the paper's layer-0 form.

### Traces, temporal properties, and adequacy (§6, Fig. 7)

| Paper | Rocq | File (under `lantana/`) |
|---|---|---|
| `Cfg`, `TPool`, THREAD-STEP/THREAD-DONE, `Trace`, `Behavior` | `cfg`, `thread_pool`, `thread_step`, `thread_done`, `trace`, `behavior` (please ignore `κ : list (observation Λ)`, which is never used) | `program_logic/language.v` |
| temporal properties `Φ, Ψ` and `⟦·⟧_t` | syntax `tp`, interpretation `tp_trace`; `Always` = `tr_always`, `Until` = `tr_until`, `Finally` = `tr_eventually` | `program_logic/temporal_property.v` |
| `Fair` (fair scheduling) | `fair_scheduling` | `program_logic/temporal_property.v` |
| logical assertions `φ` and `⟦·⟧_l` | syntax `tf`, interpretation `⟦·⟧ₗ` | `program_logic/temporal_logic.v` |
| `lift` | `tf_to_tp` | `program_logic/adequacy.v` |
| `ChooseNat` | `ChooseNat` | `lantana_heap_lang/lang.v` |
| atomic properties `x ↦ v` and thread `i`'s expression | `l ↦ v` and `exits v@i` in scope `tp_scope` (`pred_pointsto`, `pred_expr`); `exits_finally_iff`: `Finally [exits v@i]` holds iff thread `i`'s whole expression eventually is `v` | `lantana_heap_lang/lang.v`, `lantana_heap_lang/primitive_laws.v` |
| `lwp` | `lwp`, notation `lWP e @ s; i; E {{ Φ }}` | `program_logic/weakestpre.v` |
| obligation state `Ω`, witness state `W` | `obls` (`gmap oid obl`), `witnesses` (`gmap oid witness`) | `base_logic/obligation.v`, `base_logic/witness.v` |
| model interpretation `M` | `model_interp` | `base_logic/mupd.v` |
| model update modality | `mupd` / `fmupd`; the `lwp`-facing forms are `sfmupd`, `sfgupd`, and `lwpupd` | `base_logic/mupd.v`, `program_logic/sfmupd.v`, `program_logic/sfgupd.v`, `program_logic/weakestpre.v` |
| fair-scheduler invariant `H` | `owit_inv` | `base_logic/owit.v` |
| state interpretation `S` | `state_interp` (heap-lang instance) and `history_interp` (wrapper for adequacy proof) | `lantana_heap_lang/primitive_laws.v`, `program_logic/history_interp.v` |
| **Theorem 1 (Adequacy)** | `lwp_adequacy` | `program_logic/adequacy.v` |
| Iris-style safety (cf. Iris's `adequate`) | `lwp_adequacy_safety_iris`: in every fair *run* the scheduled thread is never stuck, and whenever thread `j` is a value `v`, its postcondition holds (`safety_iris`). A `run` is a behavior in which a stuck scheduled thread may also repeat its configuration (`thread_stuck`), so stuck executions are runs; every behavior is a run (`behavior_run`) | `program_logic/adequacy_iris.v`, `program_logic/language.v`, `program_logic/temporal_property.v` |

### Case studies (§2 to §7)

All in `lantana_heap_lang/examples/`.

| Paper | Rocq | File |
|---|---|---|
| Flag module: `init`/`set`/`wait`; `isFlag`; `FlagObl`; SPEC-INIT/SPEC-SET/SPEC-WAIT | `init`/`set`/`wait`; `is_flag` (syntactic form `is_flag_tf`); `flag_tk`; `Flag_init_fbspec` / `Flag_set_fbspec` / `Flag_wait_fbspec` (from `Flag_*_spec`) | `flag.v` |
| `main` (§2) and its trace property | `main`, `FlagFork_main_fbspec` (texan form `FlagFork_main_spec`), end-to-end `main_adequacy` | `flag_fork.v` |
| `nest` / `nondet` (§4.3); SPEC-NEST/SPEC-NONDET | `nest` / `nondet`; `Nondet_nest_fbspec` / `Nondet_nondet_fbspec` (from `Nondet_*_spec`) | `nondet.v` |
| Handoff: `send`/`receive`; `HandoffBuf`; `isHandoff`; `TaskSpec`; SPEC-SEND/SPEC-RECEIVE | `send`/`receive`; `handoff_inv`; `is_handoff`; `is_task` (in the paper's format: `is_task_fbtriple`); `Handoff_send_fbspec` / `Handoff_receive_fbspec` (from `Handoff_*_spec`) | `handoff.v` |
| `handoffMain` (§5.2); SPEC-HANDOFF-MAIN | `main`, `main_fbspec` (texan form `main_spec`), `handoff_client_adequacy` | `handoff_client.v` |
| Ticket lock (§7.1): `TLInv`; `TLObl`; SPEC-ACQUIRE/SPEC-RELEASE | `is_fair_lock`; `lock_token`; `TicketLock_init_fbspec` / `TicketLock_acquire_fbspec` (general form) / `TicketLock_release_fbspec` / `TicketLock_delete_fbspec` (from `TicketLock_*_spec`; the specifications in Rocq are more generalized than ones in the paper) | `ticket_lock.v` |
| Queue (§7.2): `QInv` (`QData`/`QState`/`QObls`/`QPrimary`); SPEC-ENQUEUE/SPEC-DEQUEUE | `is_queue` (with `queue_worker` for the primary); `Queue_init_fbspec` / `Queue_enqueue_fbspec` / `Queue_dequeue_fbspec` (general form; the paper shows the non-worker, non-empty case) (from `Queue_*_spec`) | `queue.v` |
| Task queue (§7.3): `TQInv`; SPEC-PUT-TASK/SPEC-WORKER | `is_task_queue`; `TaskQueue_init_fbspec` / `TaskQueue_put_task_fbspec` / `TaskQueue_run_task_fbspec` (general form) / `TaskQueue_worker_fbspec` (from `TaskQueue_*_spec`) | `task_queue.v` |
| Reentrant client `decr` / `clientMain` (§7.3); SPEC-DECR/SPEC-DECR-CLIENTMAIN | `decr_reentrant` / `main`; `decr_reentrant_fbspec` (from `decr_reentrant_spec`) / `main_fbspec` (texan form `main_spec`); `task_queue_client_adequacy` | `task_queue_client.v` |

The per-example `*_adequacy` theorems (`flag_client_adequacy`, `main_adequacy`,
`handoff_client_adequacy`, `task_queue_client_adequacy`) are end-to-end
instantiations of Theorem 1, deriving the trace-level temporal property of the
respective client program. The `*_safety_adequacy` theorems
(`flag_client_safety_adequacy`, `main_safety_adequacy`,
`handoff_client_safety_adequacy`, `task_queue_client_safety_adequacy`)
instantiate `lwp_adequacy_safety_iris` for the same programs: in every fair run,
the scheduled thread is never stuck, and each thread that terminates returns the
value its specification promises.
`flag_client.v` uses adequacy to prove a property about a memory location, beyond termination;
its threads' closed specifications are `writer_fbspec` and `reader_fbspec`.
`paradox.v` proves the unsoundness counterexample remarked at the end of §6.2.
