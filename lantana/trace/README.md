# `lantana/trace`

What a verified program guarantees about its executions, and the adequacy theorems that turn
such a guarantee into a fact about every fair run.

Three kinds of properties:

- `trProp Λ` — predicates on traces: the *external* reading, where LTL is reasoned about
  (scope `%R`, entailment `R ⊆ S`).
- `trIProp Λ Σ := trace Λ → iProp Σ` — step-indexed trace predicates: the *internal* reading,
  which a run establishes (never user-facing).
- `itrProp Λ Σ` — an internal reading with an external one adequate for it (scope `%ITR`,
  entailment `G ⊑ H`); the `G` of a guarantee `P ⊨ₜ G`.

The files form six groups, in build order. The four core definitions files (`trace_prop`,
`itrprop`, `guarantee`, `temporal_formula`) each have a `*_rules.v` with the rules a user
applies; the other files keep their own rules. `itrprop_model.v` holds what needs an allocated
instance of the logic (as in adequacy), and `temporal_formula_run.v` the run of any system with
the one-step property. Only `fuel_burning_triple.v` and `adequacy_*.v` depend on `lWP`.

```
trProp            trace_prop   trace_prop_rules   fair_scheduling
   ↓
itrProp           triprop   itrprop   itrprop_rules   itrprop_fixpoint   itrprop_model
   ↓
P ⊨ₜ G            guarantee   guarantee_rules
   ↓
alwaysI, untilI   temporal_formula   temporal_formula_run   temporal_formula_rules
   ↓
derived           guarantee_infer   guarantee_rec   guarantee_saved   until_chain   fuel_burning_triple
   ↓
adequacy          adequacy_step   adequacy_temporal   adequacy_safety
```

## Files

*Imports* are the direct `Require`s (files of this directory, then other directories); *also
uses* lists the files of this directory whose definitions the file mentions but reaches only
through its imports.

| File | Contents | Imports | Also uses |
| --- | --- | --- | --- |
| `trace_prop.v` | Trace properties `trProp`: the LTL connectives (`□`, `◇`, `○`, `R Uₜ S`), the state atom `tr_state`, entailment `⊆`, fixpoints `tr_lfp`/`tr_gfp`. | `program_logic/language`, `prelude/axioms` |  |
| `trace_prop_rules.v` | The rules of `⊆`: the connectives and the state atoms, the laws of LTL, the fixpoint rules; `tr_unfold` as the escape hatch. | trace_prop, `prelude/axioms` |  |
| `fair_scheduling.v` | Fair scheduling (`fair_scheduling`): every active thread is eventually scheduled; a fairness counter `fscnt` bounds each wait (`beh_fscnt`, from `fair_scheduling_fscnt`). | trace_prop, `prelude/axioms` |  |
| `triprop.v` | Step-indexed trace predicates `trIProp` (`trI_always`, `trI_until`), generic in the step index; at the ordinals they give `tr_always` and `tr_until`. | trace_prop, `program_logic/temporal_class`, `base_logic/satisfiable` | |
| `itrprop.v` | Internalized trace properties `itrProp`: an internal reading (`trIProp`) with an external one (`trProp`) adequate for it; the connectives, state atoms (`itrProp_state`), complete and instant properties. | triprop, `base_logic/satisfiable` | trace_prop |
| `itrprop_rules.v` | The rules of `itrProp`: in-logic entailment `⊑` and the monotonicity of the connectives, complete and instant antecedents, the cast `itrProp_cast`, the reading class `ItrPropExt`. | trace_prop_rules, itrprop | triprop, trace_prop |
| `itrprop_fixpoint.v` | Least and greatest fixpoints `itrProp_mu`/`itrProp_nu` of monotone bodies (`ItrPropMono`); always and until as fixpoints. | itrprop_rules, `base_logic/satisfiable`, `algebra/ordinal_existential_properties`, `prelude/axioms` | itrprop, triprop, trace_prop_rules, trace_prop |
| `itrprop_model.v` | The model: a property valid in the logic holds on the trace (`itrProp_valid_ext`); `⊑` is sound for complete properties (`itrProp_le_sound`) and not complete (`itrProp_always_elim_not_le`); a guarded fixpoint body has no fold. | itrprop_fixpoint, `base_logic/satisfiable`, `algebra/ordinal_existential_properties`, `prelude/axioms` | itrprop, triprop |
| `guarantee.v` | Temporal guarantees `P ⊨ₜ G` (`temporal`): records `tguar`, certificates, bundles, the one-step property `sys_step` of a running system, and the canonical property `itrProp_sem`. | itrprop_model, fair_scheduling | itrprop |
| `guarantee_rules.v` | The rules of `P ⊨ₜ G`: monotonicity (`temporal_mono`, `temporal_weaken`, `temporal_cast`), the connectives of `P`, `itrProp_sem Q` as the strongest guarantee of `Q` (`temporal_sem_complete`), state atoms (`StateFact`), implications, big separating conjunctions. | guarantee | itrprop_rules, itrprop, triprop, trace_prop |
| `temporal_formula.v` | The temporal formulas `alwaysI` and `untilI` (with `finallyI`) as registered structures, and the done until `untilI_done` (not registered); the registry state as the interpretation of the temporal layer (`treg_temporal_interp`); reading the model under a model update (`sfmupd_read`); persistence and fraction instances. | guarantee_rules, `program_logic/obl_forest_instance` | guarantee, itrprop |
| `temporal_formula_run.v` | The run: the registry is certified at every position (`treg_check`), and loops read a registered always or until off a run of any system with the one-step property (`sys_step_iter`, `always_run`, `until_run`). | temporal_formula | guarantee, triprop, fair_scheduling |
| `temporal_formula_rules.v` | The rules of the temporal formulas: allocation, access, discharge (`untilI_discharge_done` gives `untilI_done`), fractions, the proof-mode instances `IntoInv`/`IntoAcc` for `alwaysI`, and the guarantees `temporal_always`, `temporal_until`. | temporal_formula_run | temporal_formula, guarantee_rules, guarantee, itrprop_rules, itrprop, triprop |
| `guarantee_infer.v` | `IntoTemporal` infers the guarantee of a formula from its shape, `IntoTrace` the trace property it guarantees (`tr_of`); unit checks. | temporal_formula_rules | temporal_formula, guarantee_rules, guarantee, itrprop_rules, itrprop, trace_prop_rules, trace_prop |
| `guarantee_rec.v` | Guarantees of fixpoints, and recursive structures through the registry (`nest`, `renew`). | guarantee_infer, itrprop_fixpoint, `base_logic/satisfiable`, `algebra/ordinal_existential_properties`, `prelude/axioms` | temporal_formula_rules, temporal_formula, guarantee_rules, guarantee, itrprop |
| `guarantee_saved.v` | Temporal formulas in ghost state: a saved proposition with its guarantee (`saved_temporal`), and a ghost map of formulas chosen at run time, kept in one `alwaysI` (`registry_inv`, `registry_temporal`). | guarantee_infer | temporal_formula_rules, temporal_formula, guarantee_rules, itrprop |
| `until_chain.v` | Chains of untils (`untilI_chain`) whose ordinals decrease, so every chain is finite, with a ghost log of discharged links. | temporal_formula, `prelude/axioms` |  |
| `fuel_burning_triple.v` | The paper's fuel-burning triple on top of `lWP`, with triple-level rules for witness induction and untils. | guarantee_infer, `program_logic/weakestpre` | temporal_formula_rules, temporal_formula |
| `adequacy_step.v` | Facts about one `lWP` step used by both adequacy theorems: obligations, witnesses and the fairness counter. | triprop, fair_scheduling, `program_logic/weakestpre`, `base_logic/satisfiable` | trace_prop |
| `adequacy_temporal.v` | Theorem 1: `lWP` is a running system with the one-step property, so if the initial resources guarantee `G`, every fair run satisfies `itrProp_external G` (`lwp_adequacy_temporal`). | adequacy_step, guarantee_infer, `base_logic/satisfiable` | temporal_formula_run, temporal_formula, guarantee, itrprop, fair_scheduling, trace_prop |
| `adequacy_safety.v` | Iris-style safety (`not_stuck`, `safety_iris`) on fair runs: the scheduled thread is never stuck, and a chosen thread's postcondition holds when it terminates (`lwp_adequacy_safety_iris`). | adequacy_step, guarantee_infer, `base_logic/satisfiable` | temporal_formula, triprop, fair_scheduling, trace_prop |

Outside this directory, `lantana_heap_lang/primitive_laws.v` imports `triprop`, `adequacy_step`,
`guarantee_infer` and `adequacy_temporal`, and `lantana_heap_lang/temporal_laws.v` imports
`guarantee_infer`; everything else reaches the trace layer through them.
