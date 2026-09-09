# Precise thread expressions: refactoring plan

Date: 2026-09-08. Last updated: 2026-09-09.

Authority: the user's `termination_plan.md`, the workspace `AGENTS.md`, and
the current Rocq sources. The user-authored plan is not modified.

Status: the user authorized the upstream context generalization on 2026-09-08.
M1 below is now the first implementation milestone. Its design is fixed:
language-specific represented contexts, application, identity, and composition;
the existing semantic `LanguageCtx` laws remain the conditions on a context.
M1–M7 are complete. All modules and four undecorated closed clients compile,
including their direct value-reachability adequacy results. The final full
96-source build and subsequent no-op build passed. The context-instance
regressions and assumptions audit passed; see Section 8 for the final
verification record and changed-file inventory.

## 1. Requirements and boundaries

- Remove the logical label API (`label_def`, its sealing machinery, label
  predicates/notations, `lwpupd_label`, and label-based exit reasoning).
- Replace `pred_label` with an atomic property of the precise thread
  expression, and interpret it using client-owned `thread_expr`.
- Make HeapLang's `state_interp_aux` `True`; retain the authoritative thread
  map in `state_interp`.
- Thread expression ownership through execution rules and specifications,
  preserving the caller's context from precondition to postcondition.
- Keep the fuel bound outside context quantification: `∃ μ, ∀ ... C ...`.
- Remove terminal `Label`/`Exit` decorations from examples and establish
  actual value reachability at the empty context.
- Recheck every example and the entire `_CoqProject` build.
- No Git operations, cleanup, toolchain reconfiguration, proof admissions,
  new axioms, weakened results, or changes to foundational assumptions.
- Inside `lantana/`, `program_logic/` is now authorized for the context
  generalization and its proof adaptations. Other upstream files remain
  outside scope. All of
  `lantana_heap_lang/` is in scope. Vendored dependencies and copied Ordinal
  sources are not implementation targets.

The minimal syntax change removes the *assertion API* and terminal program
decorations. It need not remove the `Label` expression constructor itself or
rewrite its syntax/operational metatheory: keeping an unused expression
constructor does not retain label-based termination reasoning.

## 2. Baseline source-derived dependency and ownership map

Paths in this table are relative to `liveness/`. This section records the
pre-refactoring source study; “current” below refers to that baseline,
not the completed interface described in the milestone results.

| Source | Current role | Required work |
| --- | --- | --- |
| `lantana/program_logic/language.v` | `ctx` was `expr → expr`; `LanguageCtx` gives step preservation/inversion | M1: language-specific represented contexts with application, identity, composition |
| `lantana/program_logic/weakestpre.v` | Both `lwpupd_def` and `lwp_step` quantify over contexts | M1: retain the rules, adapt identity/composition and their application equalities |
| `lantana/base_logic/thread_map.v` | Authoritative expression map and owned per-thread fragments | Reuse `thread_map_thread_read`, `thread_map_thread_update`, `thread_map_new_thread`, and `thread_map_init`; no changes planned |
| `lantana/program_logic/lifting.v`, `ectx_lifting.v` | Pure steps transport a fixed resource `ς i`; base-step rules expose the actual ambient context | Generalize resource transport to the source/target expression, keeping masks, credits, fuel, and fork accounting intact |
| `lantana_heap_lang/lang.v` | Defines `state_pred` and its trace interpretation, before the context-item datatype | Replace the label predicate; arrange definitions/imports coherently if using a list of context items |
| `lantana_heap_lang/primitive_laws.v` | Defines thread fragments, auxiliary interpretation, label access, all primitive rules | Move fragments to clients, update primitive rules, provide context lemmas and value-based discharge |
| `lantana_heap_lang/derived_laws.v`, `proofmode.v` | Derived memory rules and pure/bind tactics | Transport the additional resource; focus and unfocus it with the same context as the WP |
| `lantana_heap_lang/examples/*.v` | Module specifications, higher-order task specifications, clients, and adequacy instances | Propagate ownership through calls/loops/forks and replace label goals with precise expression goals |

Important existing facts:

1. `thread_expr i e` currently abbreviates `thread i true e 1`, not a
   duplicable fact. Its full fraction is needed for the map update.
2. `state_interp_aux` currently owns **every** thread fragment. The current
   pure instance and atomic rules obtain the active fragment from this map,
   update it, and put it back. Replacing that map by `True` therefore requires
   updating all these rules together with their clients.
3. `state_sat` currently interprets `pred_label` with an unrestricted
   existential function. The replacement must use an exact lookup, without
   recreating that existential loss of information.
4. The current logical `label` does constrain its existential function by
   `LanguageCtx`. This is still different from preserving one particular
   caller context.
5. The generic adequacy theorem already accepts arbitrary language-supplied
   atomic predicates and an auxiliary interpretation. Moving initial thread
   fragments into its program-proof continuation does not, by itself, require
   changing the adequacy theorem.
6. `Exit` is a sealed application whose body contains `Label "exit"`. Its
   rule obtains later credits from a real pure step. Removing the wrapper
   requires moving discharge to the value state and obtaining the needed
   credits from earlier real steps, not inventing a zero-step credit rule.
7. `Handoff.is_task` embeds a persistent, fuel-bounded function specification.
   Its context quantification and expression resource must change too.
   `TaskQueue.is_task_queue` uses this predicate transitively.
8. `paradox.v` assumes the deliberately problematic `lantanaGS_no_lc` rule
   *as a theorem parameter* to derive its counterexample. This is not a
   license to assume any new rule for the ordinary development. Its migration
   must retain that explicit conditional status.

## 3. Implemented client-facing API

Use `C` for expression contexts; existing example proofs extensively use `K`
for obligation sets. Prefer `list ectx_item` for the client context, with
`fill C e` and `[]` for the empty context. This matches `reshape_expr` and the
existing bind tactics.

The intended definitions, schematically, are:

```coq
thread_expr i C e := thread i true (fill C e) 1.
state_sat σ Θ (pred_expr i C e) := Θ !! i = Some (fill C e).
state_pred_interp (pred_expr i C e) := thread_expr i C e.
state_interp_aux σ Θ κs := True.
```

`lang.v` declares `state_pred` and `state_sat` after `fill_item` and before
the language structures that use them. Its trace interpretation spells
filling as `foldl (flip fill_item) e C`, definitionally equal to `fill C e`.
The constructor stores both the supplied context and the expression; it
does not existentially forget either.

A representative module specification is:

```coq
⊢ ∃ μ, ∀ C ...,
  l{{{ thread_expr i C (f a) ∗ existing_precondition μ }}}
    f a @ i
  l{{{ v, RET v; thread_expr i C (of_val v) ∗ existing_postcondition v }}}.
```

The full fraction remains linear. It cannot be left in a persistent invariant
while also being handed to the next step, duplicated between caller and
callee, or kept unchanged by ordinary framing across a physical step.

For syntactic contexts, the existing convention is:

```coq
fill (Cinner ++ Couter) e = fill Couter (fill Cinner e).
```

Focus/unfocus lemmas and tactics must respect this order. Empty-context value
ownership reads as `Θ !! i = Some (of_val v)`. Consequently a temporal
`Finally` of that atomic property states actual eventual value reachability;
the context is not existentially quantified in the termination conclusion.

## 4. Context-interface gate: resolve before changing the API

This section preserves the original design investigation. M1 resolved the
gate; its references to the old function-context WP are historical.

### The exact missing proof obligation

Suppose a caller owns `thread_expr i C e1`, and a lifting lemma opens the
current `lwp_step`. Write `J` for the ambient function supplied by that step.
The available pure facts are:

```text
LanguageCtx J
Θ !! i = Some (J e1)
Θ !! i = Some (fill C e1)       -- read from the owned fragment
```

Thus `J e1 = fill C e1`. The physical post-state in `lwp_step`, however,
contains `J e2`. To return `thread_expr i C e2`, the map update needs:

```text
J e2 = fill C e2.
```

Equality of the two pre-state expressions does not itself supply this
equality. In particular, equality on one argument is not equality of
functions. The syntactic `fill_item_no_val_inj` and context decomposition
lemmas do not apply directly to the arbitrary function `J`.

For a deterministic pure step, there is a local route: lift the step under
the actual context and use determinism under the caller's context. This
route has now been proved in the separate experiment as
`pure_context_agreement`, with no global assumptions. It does not settle
every atomic rule. `ChooseNat` is an essential test: its chosen return value
is not determined by the heap, observations, or fork map.

### Checked evidence and its limits

Following the user's suggestion, the syntactic-context part was also checked
using the machinery built from `fill_item_no_val_inj`. The existing
`base_redex_unique` lemma allows a short proof of:

```text
prim_step i e σ ids κ e' σ' efs →
fill C e = fill D e → C = D
```

Decompose the step into its base redex and context `R`. Both whole
expressions then have that same base redex under `R ++ C` and `R ++ D`.
Base-redex uniqueness identifies these lists, and prefix cancellation gives
`C = D`. The context-decomposition mixin underlying `base_redex_unique` is
proved using `fill_item_no_val_inj` in `ectxi_language.v`.

Both `heap_contexts_agree` and its successor-equality corollary compiled,
and both printed `Closed under the global context`. They work for any
actual primitive step, **including nondeterministic steps**. No determinism
assumption or expression-size function is needed for this result.

This confirms that syntactic context agreement is straightforward. The
remaining issue is specifically the bridge from an arbitrary
`J : expr → expr` satisfying `LanguageCtx J` to such a syntactic context.
The current WP supplies no list representation of `J`.

A separate Rocq experiment defines a language with Boolean values and a
single `coin` expression that can step to either value. The function that
fixes `coin` and flips Boolean values satisfies all three **current**
`LanguageCtx` fields. It agrees with the identity on `coin` but disagrees on
its successor `value true`.

Rocq 9.0.0 checked the experiment, including:

```text
Print Assumptions ContextProbe.context_agreement_not_generic.
Closed under the global context
```

This establishes that the needed successor agreement cannot be obtained
from the generic `LanguageCtx` laws alone, even for an observation-free step
that preserves state and forks no threads. It is **not** a counterexample to
HeapLang itself, to Lantana's existing adequacy theorem, or to the desired
termination argument. A HeapLang-specific characterization could conceivably
prove the missing property using more of HeapLang's semantics; no such
characterization has been established by this study.

### Scope decision

The direct structural route is to make the contexts quantified by the WP
come from a chosen, compositional context representation, with HeapLang
instantiated by lists of context items. Identity, composition, and step
preservation/inversion must all be proved for that representation; no
context-agreement law may simply be assumed.

This route reaches upstream of `lifting.v`: at least the context interface
used in `weakestpre.v` must change, and the design may also require
`language.v` and the `ectx_language.v` / `ectxi_language.v` adapters. The
generic bind/update proofs and adequacy dependency closure must then be
rechecked. Exactly where to package the context representation should be
settled before editing those files.

That route requires user authorization under `termination_plan.md`. The
alternative is to keep the upstream interface and first prove the requisite
HeapLang-specific characterization locally. That would be additional
metatheory rather than the expected mechanical resource migration.

**Decision resolved by the user:** generalize the context interface in
`lantana/program_logic/`, preserving the current WP rules. No HeapLang-specific
context-equality assumption is to be imposed on all languages.

### M1 design (approved scope; implementation target)

Extend `language` with a context type `ctx`, application `ctx_apply`, an empty
context `ctx_id`, and composition `ctx_comp`. Require only the two application
laws `ctx_id e = e` and `ctx_comp K1 K2 e = K1 (K2 e)`. Keep `LanguageCtx`
as the existing three semantic laws, now for represented contexts. Its
identity and composition instances are derived, not assumed. Preserve `K e`
notation through a coercion of context application.

The generic theory must not assume context injectivity or decomposition.
In particular, a language can use `unit` with identity application as its
only context, or use the old function representation. For evaluation-context
languages use their existing context type, empty context, composition, and
fill; for HeapLang these reduce to lists, `[]`, reversed append for
outer-first composition, and `fill`. The already checked context-equality
lemma then applies directly to the contexts quantified by the WP.

Validate M1 by compiling all existing WP rules and all 96 current sources
*before* replacing label predicates or auxiliary ownership. Include checked
limited-context and function-context instantiations to demonstrate genuine
generality, and the HeapLang context-equality theorem without new assumptions.

## 5. Milestones and acceptance checks

### M0 — Study and baseline: complete

- Read the user plan and governing instructions.
- Trace expression ownership, lifting, bind tactics, primitive rules,
  higher-order specifications, client initialization, and adequacy.
- Check active paper text that currently explains labels and termination.
- Confirm the existing build is up to date and all 96 manifest-listed source
  checksums match the successful baseline build.
- Compile the context-interface experiment without new assumptions.
- Prove deterministic successor agreement and syntactic HeapLang context
  agreement using the existing context-decomposition machinery.

### M1 — Generalize the context interface: complete; first implementation milestone

- Resolve Section 4 and prove the required compatibility lemmas.
- Verify both empty and nonempty contexts.
- Check deterministic pure reduction, `ChooseNat`, allocation, and fork.
- Preserve arbitrary returned values, fresh locations/thread IDs, and
  nondeterminism; do not weaken their specifications to make proofs work.
- Record the exact final context representation and allowed file list here.

Acceptance: a checked context-preservation foundation for all primitive
families, not just the deterministic examples. Only then is the complete
refactoring plan stable enough for the broad API migration.

Result: `ctx`, `ctx_apply`, `ctx_id`, and `ctx_comp` are language fields;
`LanguageCtxMixin` contains exactly the two application laws. The old
`LanguageCtx` semantic conditions and WP rule statements are retained over
represented contexts. `fill_ctx_step_inj` in `ectxi_language.v` proves the
required equality for every actual step, without a determinism assumption.
Its HeapLang specialization, the identity-only context instance, and the
function-context instance all checked with no global assumptions. All existing
examples compiled without specification or proof changes. The only HeapLang
source adjustment was spelling six applications in `primitive_laws.v` as
`fill K ...` after inversion exposes the raw context-list type.

Verification: full build succeeded across `m1-build.log`,
`m1-build-resume.log`, and `m1-build-final.log` under
`/tmp/lantana-context-refactor.KtB3k8/`. A second incremental check is recorded
in `m1-verification.log`. An independent source checkpoint is
`m1-sources.tgz`; no Git operation was used. Brief filesystem clock-skew
warnings occurred during dependency regeneration; the subsequent incremental
check is used to confirm no targets remain pending.

### M2 — Generalize the generic lifting resource transport: narrow checks complete

- Replace the unchanged resource `ς i` by transport that can distinguish
  pre-step and post-step expressions.
- Keep the existing step/fuel/obligation/later-credit proof structure.
- For iterated pure execution, carry the evolving expression resource
  through the induction; an unindexed `Nat.iter` over identical resources
  is not enough by itself.
- Update `lwp_lift_pure_step_no_fork`, its deterministic specialization,
  `lwp_pure_step`, `_alt`, `_simple`, and the corresponding base-step wrapper.
- Ensure the class or lemma premises express an update that is actually
  proved by the HeapLang instance; no newly assumed update principle.

Acceptance: compile `lantana/program_logic/lifting.vo` and
`lantana/program_logic/ectx_lifting.vo`, plus any explicitly authorized
upstream dependency changes from M1.

Result: `PureExecSI` transports `ς i e1` to `ς i e2`, with the actual
observation-free, state-preserving, non-forking step as a premise. The
iterated rule carries the initial token beside `Nat.iter` and gives the
final token to its continuation. Both `lifting.vo` and `ectx_lifting.vo`
compile; an incremental recheck after session resumption reports both up
to date. HeapLang clients still require migration before a full build.

### M3 — Precise state predicates and HeapLang primitive rules: narrow checks complete

- Install the new atomic predicate and prove `state_interp_wf` by exact
  thread-map lookup.
- Set auxiliary ownership to `True` and replace the old trivial pure-step
  instance with client-owned expression transport.
- Replace `thread_exprs_update_one`'s whole-map interface with an update
  using the one owned fragment and the authoritative map.
- Update all active primitive rules: pure steps, fork, `ChooseNat`,
  allocation, free, load, store, exchange, both CAS outcomes, FAA, prophecy
  creation, and their derived wrappers.
- A fork consumes the parent's pre-step fragment, returns its unit-result
  fragment, and supplies a fresh child fragment at context `[]` to the child
  proof. It does not duplicate the parent's fragment.
- Remove the logical label API and replace the label-based exit rule with
  value-state obligation discharge using real available later credits.
- Remove dead commented label proofs that otherwise misleadingly describe
  the removed ownership API; avoid unrelated comment cleanup.

Acceptance: compile `primitive_laws.vo` and `derived_laws.vo`, including the
array/vector wrapper rules. Check exact post-state expressions for both CAS
branches and the parent/child fork split.

Result (2026-09-09): `lang.v` now has `pred_expr i C e` with exact lookup
semantics. `primitive_laws.v` uses `thread_expr i C e`, auxiliary `True`,
and a checked client-owned `PureExecSI` instance. All primitive and derived
array/vector rules compile. Fork returns the parent token and a freshly
allocated child token at `[]`. `thread_expr_terminate` discharges the actual
empty-context value atom using two existing later credits, deletes the
terminal carrier, and returns the value token with `thP_done`. The logical
label API and its commented-out obsolete proofs are removed. Proof-mode
and examples were subsequently completed in M4–M6.

### M4 — Proof-mode support and a small pilot: complete

- Update pure-step proof-mode lemmas to transport the expression token.
- Add focus/unfocus support using the same decomposition as `lwp_bind` and
  `lwp_bind_step`. Do not rewrite an unknown outer context by guesswork.
- Keep existing `TG`, `GF`, witness, and later-credit patterns recognizable;
  use a consistent separate name such as `TE` for expression ownership.
- Update one small function and one nonempty-context call as pilot proofs.
- Verify a call returns ownership at the original outer context, and a
  complete closed call reaches `thread_expr i [] (of_val v)`.

Acceptance: compile `proofmode.vo` and the pilot example. Exercise actual
bind/unbind and pure-step tactics, not only direct applications of lemmas.

Result (2026-09-09): `proofmode.vo`, `extended_int.vo`, and `flag.vo`
compile. `lwp_pure` reserves the spatial hypothesis named `TE`; its
continuation returns the updated `TE` after the existing carrier, fuel,
witness, and credit arguments. `thread_expr_focus "TE" e` focuses or
unfocuses using existing context items only. Bind and finish tactics use
it to maintain the matching expression. The Flag wait proof exercises
nonempty contexts and carries `TE` through witness induction. The new
specifications quantify over arbitrary caller contexts after the fuel
bound and return the token at that same context.

The M3 library checkpoint is
`/tmp/lantana-context-refactor.KtB3k8/m3-library-sources.tgz`.
No new admissions or axiom declarations occur in the edited source areas.

### M5 — Migrate all module and higher-order specifications: complete

Result (2026-09-09): `extended_int.vo`, `flag.vo`, `nondet.vo`,
`handoff.vo`, both ticket locks, `queue.vo`, `task_queue.vo`, and
`paradox.vo` compile with context-preserving ownership. `Handoff.is_task`
and the reentrant task specification quantify over the caller context after
their fuel bounds. Parent/child fork proofs transport distinct tokens.
The TaskQueue worker retains its deliberately nonterminating `False`
postcondition.

Paradox's `lantanaGS_no_lc` class and the explicit premise of `loop_paradox`
are unchanged. Its no-credit loop reduces to the very same expression, so
its token can remain unchanged without assuming generic no-credit token
transport. The ordinary-credit loop uses the new transport rule. Both
loop specifications retain the token through induction and return it in
their hypothetical terminating postcondition.

For parallel builds,
`make -f Makefile.coq --jobserver-style=pipe -j8 ...` avoids stale temporary
jobserver-FIFO warnings left by an interrupted diagnostic build.

Suggested dependency order:

1. `extended_int.v`, `flag.v`, and `nondet.v`.
2. `handoff.v`, including `is_task` and its function-specification clients.
3. Both `ticket_lock.v` and `ticket_lock2.v`; then `queue.v`.
4. `task_queue.v`, including its nonterminating worker and its fork site.
5. `paradox.v`, preserving the explicit conditional nature of its no-credit
   counterexample and its current logical conclusion.

Keep `∃ μ` outside the new context quantifier, including higher-order task
specifications. Loop and witness inductions must carry the expression token
in their induction resources. Do not claim termination of a deliberately
nonterminating worker; transport its token through recursive execution.

Acceptance: each module compiles after its dependencies. Retain existing
data invariants, layer relations, witness reasoning, and return-value facts.

### M6 — Undecorated clients and direct termination adequacy: complete

- Remove `Label`/`Exit` decorations from `flag_client.v`, `flag_fork.v`,
  `handoff_client.v`, and `task_queue_client.v`.
- Replace terminal temporal atoms with exact empty-context value atoms;
  retain each client's existing return value and other temporal properties.
- In each adequacy initialization, retain the fragments returned by
  `thread_map_init` for the program-proof continuation. Supply `True` to the
  auxiliary-interpretation conjunct instead of consuming those fragments.
- Update the corresponding `main_pre` / client-precondition lemmas and
  their `tf_to_tp` reductions. The generic temporal operators and scheduling
  assumptions should not be changed for this ownership migration.
- Discharge terminal obligations at the actual value state; retain correct
  carrier deletion and `lift_term`/`thP_done` reasoning.
- State or prove the simple trace-level corollary that the resulting
  `Finally` atom means the thread eventually contains `of_val v`.

Acceptance: all client adequacy files compile, their temporal conclusions
contain precise value reachability, and no example still uses a label as a
termination marker. The memory-property result of `flag_client.v` remains.

Result (2026-09-09): all four closed clients compile. Their terminal atoms
use `exits v@i`, meaning `pred_expr i [] (of_val v)`, and their closed
specifications require the initial token at `[]` and return the final token
at `[]`. Reusable functions instead quantify over arbitrary contexts.
Initial tokens remain outside the temporal formula and are passed to its
program continuation, while the auxiliary interpretation is `True`.

| Adequacy result | Eventual thread exit | Other conclusions preserved |
| --- | --- | --- |
| `flag_client.flag_client_adequacy` | writer: unit; reader: `#1` | `is_flag_tp` and the `#0`-until-`#1` memory property |
| `flag_fork.main_adequacy` | main: `#42` | return-value postcondition and fork proof |
| `handoff_client.handoff_client_adequacy` | main: `#1` | higher-order handoff and fork proof |
| `task_queue_client.task_queue_client_adequacy` | main: `#1` | reentrant-task reasoning; no claim that its worker terminates |

The new checked `exits_finally_iff` in `primitive_laws.v` states exactly:

```coq
tp_trace (tp_finally (exits v@i))%P τ ↔
∃ n, τ.1 ≤ n ∧ (τ.2 n).1.1.1 !! i = Some (of_val v).
```

This equivalence needs no behavior or fairness assumption; the client
adequacy theorems establish its left-hand side under their unchanged
behavior, fair-scheduling, and initial-configuration premises.
Terminal discharge consumes two previously earned later credits: the Flag
writer/reader retain them from their module call's ten credits; the other
clients retain them from their initial lambda step's hundred credits.
There is no invented execution step or value-state credit generation.
All terminal `Label` decorations and the sealed `Exit` wrapper are removed;
the unused `Label` AST constructor and operational metatheory remain.

### M7 — Whole-development audit and handoff: complete

- Run the full `make -j8 all`, followed by another incremental build.
- Check the complete `_CoqProject` target set; add a file there only if the
  final implementation genuinely introduces a new first-party Rocq module.
- Scan edited sources for admissions and axiom declarations, and compare
  foundational-assumption declarations against the untouched baseline.
- Inspect `Print Assumptions` for the client adequacy results and new
  context/termination lemmas; distinguish inherited assumptions from any
  accidental additions.
- Search active sources for the removed logical label API and stale
  `state_interp_aux` fragment-map manipulations.
- Update this document with milestone results, build logs, changed files,
  and any unresolved issue. Never mark an unchecked milestone complete.

Result (2026-09-09): the full 96-source target set and a subsequent no-op
build passed. Final context-instance tests and `Print Assumptions` checks
passed. The source audit found no new admissions or axioms, no changes
outside the authorized Rocq areas, and no remaining logical label API or
terminal label decorations. Full details follow in Section 8.

## 6. Paper correspondence

The active include graph is `paper.tex` → `body/part.tex` → introduction,
key-ideas, logic-guarantee, logic-rely, logic-offload, soundness, case-studies,
and related work. Backup drafts were not used to justify this plan.

The active `body/key-ideas.tex` explains terminal `Label`/`Return` markers;
`body/soundness.tex` defines the label atom and its lifting to trace
properties; `macros.tex` implements `\Return` through `\Label` and the
terminal predicate through the label predicate. The refactored code will
intentionally differ from that presentation.

This task does not edit/rebuild the paper or replace `paper.pdf`. Record the
post-refactoring paper/code difference at handoff; do not silently rewrite
the submitted artifact or claim the paper was updated.

## 7. Historical M0 verification record and probes

The bullets and probe source in this section describe the original study,
before production edits. In particular, the function-context experiment
uses the old `Language` constructor; it is retained as historical evidence,
not as a regression test for the final interface.

- Existing switch: `lantana`; OCaml 5.2.1; Rocq 9.0.0.
- At M0: `opam exec --switch=lantana -- make -j8 all` succeeded and
  reported no outstanding work. This was an incremental baseline check,
  not a new forced rebuild.
- All 96 source checksums in
  `/tmp/lantana-build.WQ3gzy/firstparty.sha256` matched.
- The generic counterexample, deterministic successor-agreement lemma,
  syntactic HeapLang context-agreement lemma, and its successor corollary
  compiled successfully; each printed `Closed under the global context`.
- Temporary probe: `/tmp/lantana-termination.9xnlWT/context_probe.v`.
- Temporary HeapLang probe:
  `/tmp/lantana-termination.9xnlWT/heap_context_probe.v`.
- At that M0 checkpoint, no production source edits, Git operations, paper
  edits, or toolchain changes had been made during the refactoring study.

The exact probe source is retained below so that this evidence is not lost
when temporary files disappear. Run it from `liveness/` with the existing
switch and the project's `-Q lantana lantana -Q lantana_heap_lang
lantana.heap_lang` mappings. It is deliberately not added to `_CoqProject`.

```coq
From lantana.program_logic Require Import language.

Module ContextProbe.
Inductive exp := coin | value (b : bool).
Definition get_value e := match e with value b => Some b | coin => None end.
Inductive step (i : thread_id) (s : unit) (ids : thread_ids) :
    exp -> list unit -> exp -> unit -> gmap thread_id exp -> Prop :=
  | choose b : step i s ids coin [] (value b) s ∅.
Definition prim i e s ids obs e' s' forks := step i s ids e obs e' s' forks.
Definition sat (_ : unit) (_ : gmap thread_id exp) (_ : unit) := True.

Lemma mixin : LanguageMixin value get_value prim.
Proof.
  split.
  - done.
  - intros [|b] b'; simpl; congruence.
  - intros ???????? H. by inversion H.
  - intros ???????? H. inversion H; subst. rewrite dom_empty_L. set_solver.
Qed.
Canonical Structure coin_lang := Language (state_sat := sat) mixin.

Definition flip e := match e with coin => coin | value b => value (negb b) end.

Global Instance flip_ctx : @LanguageCtx coin_lang flip.
Proof.
  split.
  - intros [] H; done.
  - intros ???????? H. inversion H; subst. constructor.
  - intros i e s ids obs e' s' forks Hnv Hstep.
    destruct e as [|b]; last discriminate.
    inversion Hstep; subst.
    exists (value (negb b)). split; first by simpl; rewrite Bool.negb_involutive.
    constructor.
Qed.

Lemma before_equal : flip coin = id coin.
Proof. reflexivity. Qed.
Lemma after_different : flip (value true) <> id (value true).
Proof. discriminate. Qed.

Lemma context_agreement_not_generic :
  ~ (forall (K C : ctx coin_lang) (e e' : expr coin_lang),
      LanguageCtx K -> LanguageCtx C ->
      to_val e = None ->
      prim_step 1%positive e tt ∅ [] e' tt ∅ ->
      K e = C e -> K e' = C e').
Proof.
  intros H.
  apply after_different.
  apply (H flip id coin (value true)); try apply _; try reflexivity.
  constructor.
Qed.
End ContextProbe.
Print Assumptions ContextProbe.context_agreement_not_generic.

Lemma pure_context_agreement {Λ : language} (K C : ctx Λ)
    (e e' : expr Λ) i σ ids :
  LanguageCtx K -> LanguageCtx C -> pure_step e e' ->
  prim_step i e σ ids [] e' σ ∅ -> K e = C e -> K e' = C e'.
Proof.
  intros HK HC HP HS HE.
  pose proof (fill_step (K := K) i e σ ids [] e' σ ∅ HS) as HKS.
  rewrite HE in HKS.
  pose proof (pure_step_ctx C e e' HP) as HCP.
  destruct HCP as [_ Hdet].
  destruct (Hdet i σ [] ids (K e') σ ∅ HKS) as (_ & _ & Heq & _).
  exact Heq.
Qed.
Print Assumptions pure_context_agreement.
```

The separate HeapLang probe is:

```coq
From lantana.heap_lang Require Import lang notation.

Lemma heap_contexts_agree (C D : list ectx_item) e i σ ids κ e' σ' efs :
  prim_step i e σ ids κ e' σ' efs ->
  fill C e = fill D e -> C = D.
Proof.
  intros [R r r' -> -> Hbase] HE.
  rewrite -!fill_app in HE.
  assert (base_reducible i r σ ids) as Hr.
  { exists κ, r', σ', efs. exact Hbase. }
  destruct (base_redex_unique (R ++ C) (R ++ D) i r r σ ids HE Hr Hr)
    as [HC _].
  change (R ++ C = R ++ D) in HC.
  by apply (inj (app R)).
Qed.

Lemma heap_context_successors_agree (C D : list ectx_item)
    e i σ ids κ e' σ' efs :
  prim_step i e σ ids κ e' σ' efs ->
  fill C e = fill D e -> fill C e' = fill D e'.
Proof.
  intros HS HE.
  by rewrite (heap_contexts_agree C D e i σ ids κ e' σ' efs HS HE).
Qed.

Print Assumptions heap_contexts_agree.
Print Assumptions heap_context_successors_agree.
```

## 8. Final verification and handoff (2026-09-09)

### Build and regression results

The existing `lantana` opam switch (Rocq 9.0.0, OCaml 5.2.1) was used.
No setup, installation, configuration, vendor modification, cleanup, or
Git operation was performed during this refactoring. Builds used the
existing Git-blocking wrapper in `PATH`:

```sh
export PATH="/tmp/lantana-build.WQ3gzy/no-git-bin:$PATH"
opam exec --switch=lantana -- make --jobserver-style=pipe -j8 all
```

Narrow checks preceded the affected dependency closures. `_CoqProject`
still lists the original 96 sources; no new production Rocq module or
build-manifest change was needed. The final full build passed after the
`Exit` wrapper removal. The next build reported:

```text
make[2]: Nothing to be done for 'real-all'.
```

The checked context regressions instantiate a language with only the
identity context (`unit`) and with ordinary function contexts. Both
identity instances and the HeapLang context-equality specialization printed
`Closed under the global context`. Generic `lwp_bind`, `lwp_bind_step`, and
`lwp_bind_lwpupd` retain their rules over the chosen context representation.

Logs and independent non-Git checkpoints are retained in
`/tmp/lantana-context-refactor.KtB3k8/`:

- `sources-before.tgz`, `sources-before.sha256`, and `before/`: original
  source checkpoint used for direct filesystem comparisons.
- `m1-sources.tgz`, `m3-library-sources.tgz`: earlier checked milestones.
- `m7-build.log`: first complete post-refactoring build.
- `m7-notation.log`, `m7-build-final.log`: wrapper removal and final closure.
- `m7-verification.log`: final no-op build.
- `context_instances.v`, `m7-context-instances.log`: final context tests.
- `m7_assumptions.v`, `m7-assumptions.log`: final assumptions audit.

These temporary files are supporting evidence, not a required part of the
source tree. The durable conclusions and audit commands are recorded here.

### Assumptions and scope audit

`fill_ctx_step_inj` and `exits_finally_iff` are closed under the global
context. The three logical helpers `thread_expr_ctx`,
`thread_expr_pure_exec_si`, and `thread_expr_terminate` use only the existing
logical development's inherited standard-library assumptions:

```text
Classical_Prop.classic
Epsilon.epsilon_statement
FunctionalExtensionality.functional_extensionality_dep
ProofIrrelevance.proof_irrelevance
PropExtensionality.propositional_extensionality
```

All four client adequacy results, the conditional `loop_paradox`, and
generic `lwp_adequacy` print exactly that set plus:

```text
ClassicalUniqueChoice.dependent_unique_choice
RelationalChoice.relational_choice
```

Thus the client results have the same global assumptions as generic
adequacy, not an axiom asserting termination or context equality.
`loop_paradox` still has its explicitly quantified no-credit-rule premise;
it is not an unconditional result or a global instance. Its class and
theorem premise were compared directly with the original source.

There are no `admit`, `Admitted`, `eadmit`, `Axiom`, or `Axioms` occurrences
in `lantana/program_logic/` or `lantana_heap_lang/`. A whole-tree text scan
also reports the pre-existing, unused `eadmit` tactic in copied
`lantana/ordinal/sflib.v`, commented-out proof text in `ordinal/cardinal.v`,
and an English use of “admit” in `base_logic/later_credits.v`; these files
are unchanged. No admission tactic was used by this work. Foundational
assumption declarations match the original source, and all Rocq sources
outside the authorized areas are byte-for-byte unchanged.

The removed APIs (`label_def`, `pred_label`, label assertions/notations,
`lwpupd_label`, `lwp_exit`, and `Exit`'s sealing machinery), the old
whole-map fragment helper, and the old trivial pure-step instance have no
remaining references in the authorized source areas. No example contains
`Label` or `Exit`. The unused `Label` AST and its operational metatheory
are intentionally retained, as allowed by the minimal syntax-change plan.

The assumption checks can be reproduced in Rocq with the project mappings
and the following imports/commands:

```coq
From lantana.heap_lang Require Import proofmode.
From lantana.heap_lang.examples Require Import
  flag_client flag_fork handoff_client task_queue_client paradox.
Print Assumptions fill_ctx_step_inj.
Print Assumptions thread_expr_ctx.
Print Assumptions thread_expr_pure_exec_si.
Print Assumptions thread_expr_terminate.
Print Assumptions exits_finally_iff.
Print Assumptions flag_client.flag_client_adequacy.
Print Assumptions flag_fork.main_adequacy.
Print Assumptions handoff_client.handoff_client_adequacy.
Print Assumptions task_queue_client.task_queue_client_adequacy.
Check paradox.loop_paradox.
Print Assumptions paradox.loop_paradox.
Print Assumptions lwp_adequacy.
```

### Changed files

Paths below are relative to `liveness/`. There are 26 changed Rocq sources:

- `lantana/program_logic/`: `language.v`, `ectx_language.v`,
  `ectxi_language.v`, `weakestpre.v`, `adequacy.v`, `adequacy_iris.v`,
  `lifting.v`, `ectx_lifting.v`.
- `lantana_heap_lang/`: `lang.v`, `notation.v`, `primitive_laws.v`,
  `derived_laws.v`, `proofmode.v`.
- `lantana_heap_lang/examples/`: `extended_int.v`, `flag.v`, `nondet.v`,
  `handoff.v`, `ticket_lock.v`, `ticket_lock2.v`, `queue.v`, `task_queue.v`,
  `paradox.v`, `flag_client.v`, `flag_fork.v`, `handoff_client.v`,
  `task_queue_client.v`.

This plan is the persistent implementation/verification document. The
user-authored `termination_plan.md` is unchanged. Build-generated outputs
were regenerated normally, never hand-edited.

### Remaining artifact difference

No refactoring milestone remains open. The LaTeX source and submitted
`paper.pdf` were neither edited nor rebuilt: they still present terminal
label markers. The development now establishes exact value reachability
for undecorated clients. Updating that paper presentation is a separate
task requiring the user's direction.

### Naming follow-up: thread exit

The terminal notation is now `exits v@i` in BI, temporal-formula, and
trace-property scopes; its trace lemma is `exits_finally_iff`. The earlier
name `returns` could be confused with an ordinary function return inside
a still-running thread. The definition is unchanged: the entire expression
of thread `i` is the value `v`, at the empty context. All four client files
and the current notation references in this plan use the new name; the
earlier M7 logs retain the historical spelling.

Validation: `primitive_laws.vo`, the full development, and a subsequent
no-op build passed after the rename. `Print Assumptions exits_finally_iff`
reports `Closed under the global context`. Logs are
`exits-rename-build.log` and `exits-rename-verification.log` in the same
temporary checkpoint directory. No proofs, semantics, assumptions, Git
state, or paper artifacts were changed by this naming follow-up.
