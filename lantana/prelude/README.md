# `lantana/prelude/`

Rocq-generic facts with no Iris: the classical axioms the development assumes, facts about the
ordinals of both copies of the Ordinal library (the opam package, whose ordinals are `Ord.t`, and
the copy in `ordinal/`, whose ordinals `ord.t` are the layers), and a well-founded lexicographic
product.

Builds on `ordinal/`. Used by `lantana/algebra/`, `lantana/program_logic/`, `lantana/trace/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `axioms.v` | — | The classical axioms of the development, from Rocq's standard library under short names: functional extensionality (`func_ext`, `func_ext_dep`), excluded middle (`classic`), proof irrelevance, choice, and propositional extensionality. |
| `wf_structs.v` | — | The lexicographic product `prod_eq_lt EA RA RB` of two relations, whose first component is compared up to an equivalence `EA`: it is well founded when both relations are (`prod_eq_lt_well_founded`), and transitive when both are. Not imported by any file. |
| `ordinal_facts.v` | — | For the opam ordinals `Ord.t` with the Hessenberg sum `⊕`: the class `ord_mono_fun_class` of inflationary monotone functions `η`, and small facts about `ω`, `Ord.S` and `⊕` (`ord_lt_one`, `ord_S_add`). |
| `ordinal_copy_facts.v` | — | For the copy's ordinals `ord.t`, the layers (`lantana/algebra/layer.v`): `ord_mono_fun_class` as above, suprema of ordinal-valued functions (`limit_fun`), facts about `ω`, `⊕`, Jacobsthal multiplication and exponentiation, and ordinals of well-founded relations (`ord.from_wf`). |

## Notes

- `axioms.v` is imported by `lantana/algebra/` (`ocm.v`, `measure.v`) and by `lantana/trace/`;
  `ordinal_facts.v` by `lantana/algebra/` (`measure.v`, `ordinal_wfocm.v`) and
  `lantana/program_logic/language.v`; `ordinal_copy_facts.v` by `lantana/algebra/layer.v`.
- The two ordinal files define the same class `ord_mono_fun_class` for the two types of
  ordinals. Using two copies of the Ordinal library is deliberate: layers are instantiated with
  ordinals, and their universe must be below that of the ordinals `Ord.t` that measure fuel (see
  the header of `lantana/algebra/layer.v`).
