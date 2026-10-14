# `lantana/trace/`

What a verified program guarantees about its executions, and the adequacy theorems that turn
such a guarantee into a fact about every fair behavior.

Builds on `lantana/prelude/`, `lantana/algebra/`, `lantana/base_logic/`, `lantana/program_logic/`.
Used by `lantana_heap_lang/`, `lantana_heap_lang/examples/`.

Three kinds of properties:

- `trProp Λ` — predicates on traces: the *external* reading, where LTL is reasoned about
  (scope `%R`, entailment `R ⊆ S`).
- `trIProp Λ Σ := trace Λ → iProp Σ` — step-indexed trace predicates: the *internal* reading,
  which a run establishes (never user-facing).
- `trSpec Λ Σ` — an internal reading with an external one adequate for it (scope `%SPEC`,
  entailment `G ⊑ H`); the `G` of a guarantee `P ⊨ₜ G`.

The files form six groups, in build order. The four core definitions files (`trace_prop`,
`trspec`, `guarantee`, `temporal_formula`) each have a `*_rules.v` with the rules a user
applies; the other files keep their own rules. `trspec_model.v` holds what needs an allocated
instance of the logic (as in adequacy), and `temporal_formula_run.v` the run of any system with
the one-step property. Only `adequacy_*.v` depend on `lWP`.

```
trProp            trace_prop   trace_prop_rules   fair_scheduling
   ↓
trSpec           triprop   trspec   trspec_rules   trspec_fixpoint   trspec_model
   ↓
P ⊨ₜ G            guarantee   guarantee_rules
   ↓
alwaysI, untilI   temporal_formula   temporal_formula_run   temporal_formula_rules
   ↓
derived           guarantee_infer   guarantee_rec   guarantee_saved   until_chain
   ↓
adequacy          adequacy_step   adequacy_temporal   adequacy_safety
```

## Files

In dependency order: each file imports only files above it. *Imports* are the direct `Require`s (files of this directory, then other directories); *also
uses* lists the files of this directory whose definitions the file mentions but reaches only
through its imports.

| File | Contents | Imports | Also uses |
| --- | --- | --- | --- |
| `trace_prop.v` | Trace properties `trProp`: the LTL connectives (`□`, `◇`, `○`, `R Uₜ S`), the state atom `tr_state`, entailment `⊆`, fixpoints `tr_lfp`/`tr_gfp`. | `program_logic/language`, `prelude/axioms` |  |
| `trace_prop_rules.v` | The rules of `⊆`: the connectives and the state atoms, the laws of LTL, the fixpoint rules; `tr_unfold` as the escape hatch. | trace_prop, `prelude/axioms` |  |
| `fair_scheduling.v` | Fair scheduling (`fair_scheduling`): every active thread is eventually scheduled; a fairness counter `fscnt` bounds each wait (`beh_fscnt`, from `fair_scheduling_fscnt`). | trace_prop, `prelude/axioms` |  |
| `triprop.v` | Step-indexed trace predicates `trIProp` (`trI_always`, `trI_until`), generic in the step index; at the ordinals they give `tr_always` and `tr_until`. | trace_prop, `program_logic/temporal_class`, `base_logic/satisfiable` | |
| `trspec.v` | Trace specifications `trSpec`: an internal reading (`trIProp`) with an external one (`trProp`) adequate for it; the connectives, state atoms (`trSpec_state`), complete and instant properties. | triprop, `base_logic/satisfiable` | trace_prop |
| `trspec_rules.v` | The rules of `trSpec`: in-logic entailment `⊑` and the monotonicity of the connectives, complete and instant antecedents, the cast `trSpec_cast`, the reading class `TrSpecExt`. | trace_prop_rules, trspec | triprop, trace_prop |
| `trspec_fixpoint.v` | Least and greatest fixpoints `trSpec_mu`/`trSpec_nu` of monotone bodies (`TrSpecMono`); always and until as fixpoints. | trspec_rules, `base_logic/satisfiable`, `algebra/ordinal_existential_properties`, `prelude/axioms` | trspec, triprop, trace_prop_rules, trace_prop |
| `trspec_model.v` | The model: a property valid in the logic holds on the trace (`trSpec_valid_ext`); `⊑` is sound for complete properties (`trSpec_le_sound`) and not complete (`trSpec_always_elim_not_le`); a guarded fixpoint body has no fold. | trspec_fixpoint, `base_logic/satisfiable`, `algebra/ordinal_existential_properties`, `prelude/axioms` | trspec, triprop |
| `guarantee.v` | Temporal guarantees `P ⊨ₜ G` (`guar`): records (`record`), certificates (`cert`), bundles, the one-step property `sys_step` of a running system, and the canonical property `trSpec_canon`. | trspec_model, fair_scheduling | trspec |
| `guarantee_rules.v` | The rules of `P ⊨ₜ G`: monotonicity (`guar_mono`, `guar_weaken`, `guar_cast`), the connectives of `P`, `trSpec_canon Q` as the strongest guarantee of `Q` (`guar_canon_complete`), state atoms (`StateFact`), implications, big separating conjunctions. | guarantee | trspec_rules, trspec, triprop, trace_prop |
| `temporal_formula.v` | The temporal formulas `alwaysI` and `untilI` (with `finallyI`) as registered structures, and the done until `untilI_done` (not registered); the registry state as the interpretation of the temporal layer (`reg_temporal_interp`); reading the model under a model update (`sfmupd_read`); persistence and fraction instances. | guarantee_rules, `program_logic/obl_forest_instance` | guarantee, trspec |
| `temporal_formula_run.v` | The run: the registry is certified at every position (`reg_check`), and loops read a registered always or until off a run of any system with the one-step property (`sys_step_iter`, `always_run`, `until_run`). | temporal_formula | guarantee, triprop, fair_scheduling |
| `temporal_formula_rules.v` | The rules of the temporal formulas: allocation, access, discharge (`untilI_discharge_done` gives `untilI_done`), fractions, the proof-mode instances `IntoInv`/`IntoAcc` for `alwaysI`, and the guarantees `guar_alwaysI`, `guar_untilI`. | temporal_formula_run | temporal_formula, guarantee_rules, guarantee, trspec_rules, trspec, triprop |
| `guarantee_infer.v` | `IntoGuar` infers the guarantee of a formula from its shape, `IntoTrace` the trace property it guarantees (`tr_of`); unit checks. | temporal_formula_rules | temporal_formula, guarantee_rules, guarantee, trspec_rules, trspec, trace_prop_rules, trace_prop |
| `guarantee_rec.v` | Guarantees of fixpoints, and recursive structures through the registry (`nest`, `renew`). | guarantee_infer, trspec_fixpoint, `base_logic/satisfiable`, `algebra/ordinal_existential_properties`, `prelude/axioms` | temporal_formula_rules, temporal_formula, guarantee_rules, guarantee, trspec |
| `guarantee_saved.v` | Temporal formulas in ghost state: a saved proposition with its guarantee (`saved_guar`), and a ghost map of formulas chosen at run time, kept in one `alwaysI` (`request_map_inv`, `guar_request_map`). | guarantee_infer | temporal_formula_rules, temporal_formula, guarantee_rules, trspec |
| `until_chain.v` | Chains of untils (`untilI_chain`) whose ordinals decrease, so every chain is finite, with a ghost log of discharged links. | temporal_formula, `prelude/axioms` |  |
| `adequacy_step.v` | Facts about one `lWP` step used by both adequacy theorems: obligations, witnesses and the fairness counter. | triprop, fair_scheduling, `program_logic/weakestpre`, `base_logic/satisfiable` | trace_prop |
| `adequacy_temporal.v` | Theorem 1: `lWP` is a running system with the one-step property, so if the initial resources guarantee `G`, every fair behavior satisfies `trSpec_external G` (`lwp_adequacy_temporal`); stuck behaviors contradict `lWP` at `NotStuck`. | adequacy_step, guarantee_infer, `base_logic/satisfiable` | temporal_formula_run, temporal_formula, guarantee, trspec, fair_scheduling, trace_prop |
| `adequacy_safety.v` | Iris-style safety (`not_stuck`, `safety_iris`) on fair behaviors: the scheduled thread is never stuck, and whenever a chosen thread is a value, its postcondition holds (`lwp_adequacy_safety_iris`). | adequacy_step, guarantee_infer, `base_logic/satisfiable` | temporal_formula, triprop, fair_scheduling, trace_prop |

Outside this directory, `lantana_heap_lang/primitive_laws.v` imports `triprop`, `adequacy_step`,
`guarantee_infer` and `adequacy_temporal`, and `lantana_heap_lang/temporal_laws.v` imports
`guarantee_infer`; the clients in `lantana_heap_lang/examples/` import `adequacy_safety` for
their safety theorems. Everything else reaches the trace layer through these imports.
