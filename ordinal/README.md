# `ordinal/`

A copy of the Ordinal library (https://github.com/snu-sf/Ordinal, version 0.5.6), distributed
under the MIT license (`LICENSE`): constructive ordinals `ord.t` with their order, arithmetic, and
classical facts. The files are in the namespace `lantana.ordinal`. Lantana uses this copy for
layers `ℓ : ord.t` (through `lantana/prelude/ordinal_copy_facts.v` and
`lantana/algebra/layer.v`, and the instance `ordinal_auth_mra_class` in
`lantana/algebra/auth_mra.v`), while the fuel and witness amounts use the opam-installed copy of
the same library (`Ord.t`); using two copies sidesteps a universe inconsistency.

Builds on nothing in Lantana. Used by `lantana/prelude/`, `lantana/algebra/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `sflib.v` | — | The SNU tactic library sflib (https://github.com/snu-sf/sflib), as bundled with Ordinal: tactics such as `des`, `clarify`, `inv`, `hexploit`, `i`, `ss`, `econs`. |
| `basics.v` | `sflib.v` | Facts about well-founded relations: Cantor's theorem, well-foundedness of transitive closures and of the pair relation `double_rel`, and a double well-founded induction principle. |
| `ordinal.v` | `basics.v`, `sflib.v` | The ordinals `ord.t`, as well-founded trees `ord.build (os : A → ord.t)`, with `ord.le`, `ord.lt`, `ord.eq`, zero, successor, suprema (`ord.join`, `ord.union`), ranks in a well-founded relation (`ord.from_wf`, `ord.from_wf_set`), transfinite recursion (`ord.rec`, `ord.orec`), `ω`, and Hartogs numbers. Notations `<=`, `<`, `==`, `ω` are in `ordinal_scope` (`%ordi`). |
| `arithmetic.v` | `basics.v`, `ordinal.v`, `sflib.v` | Ordinal addition, multiplication and exponentiation (`ordArith.add`, `ordArith.mult`, `ordArith.expn`; notations `+`, `*`, `^`), defined by transfinite recursion, with their monotonicity and algebraic laws. |
| `hessenberg.v` | `arithmetic.v`, `basics.v`, `ordinal.v`, `sflib.v` | The Hessenberg natural sum `⊕` (`hessenberg.add`: commutative, associative, strictly monotone in both arguments), and the Jacobsthal multiplication `×` and exponentiation `↑` built on it (`jacobsthal.mult`, `jacobsthal.expn`). |
| `inaccessibility.v` | `arithmetic.v`, `basics.v`, `ordinal.v`, `sflib.v` | `inaccessible X base next k`: `k` is above `base` and closed under `next`, `X`-indexed suprema and binary unions. The ordinal of a type of `X`-branching trees is such a bound, also for the arithmetic operations. **Not used by Lantana:** Imported only by `inaccessible.v`, which is itself unused. |
| `totalness.v` | `ordinal.v`, `sflib.v` | Totality of the order on `ord.t` implies excluded middle, and excluded middle implies trichotomy. |
| `wf_rel.v` | `basics.v`, `ordinal.v`, `sflib.v` | Compares the ordinals of different well-founded relations (`ord.from_wf`, `ord.from_wf_set`): under inclusion, injections, relations transported along a function (`projected_rel`), and restriction below an element (`cut_rel`). |
| `classical_ordinal.v` | `basics.v`, `ordinal.v`, `sflib.v`, `totalness.v`, `wf_rel.v` | Facts that need classical logic and choice (`ClassicalChoice`), in module `classicOrd`: trichotomy and totality of the order, least elements (`meet_exists`), the successor-or-limit case split, zero/successor/limit induction, and more laws of `ord.rec`. |
| `classical_hessenberg.v` | `arithmetic.v`, `basics.v`, `classical_ordinal.v`, `hessenberg.v`, `ordinal.v`, `sflib.v` | Classical laws of Jacobsthal arithmetic (`classicJacobsthal`): `×` distributes over `⊕` and is associative; for `0 < b`, `b ↑ (o0 + o1) == (b ↑ o0) × (b ↑ o1)` and `b ↑ (o0 * o1) == (b ↑ o0) ↑ o1`. |
| `fixedpoint.v` | `basics.v`, `classical_ordinal.v`, `ordinal.v`, `sflib.v` | The Bourbaki–Witt fixed-point theorem, by transfinite iteration up to a Hartogs number, and least and greatest fixed points (`mu`, `nu`) of monotone operators on predicates. **Not used by Lantana:** Imported only by `well_ordering.v` and `zorn.v`, which are themselves unused. |
| `to_set.v` | `basics.v`, `classical_ordinal.v`, `ordinal.v`, `sflib.v`, `wf_rel.v` | The converse of `ord.from_wf_set`: every ordinal is the ordinal of a well-founded relation (`toSet.toSet`), and of a well-founded total order (`toSet.to_total_set`). **Not used by Lantana:** Imported only by `cardinal.v`, which is itself unused. |
| `well_ordering.v` | `basics.v`, `classical_ordinal.v`, `fixedpoint.v`, `ordinal.v`, `sflib.v` | The well-ordering theorem (every type has a well-founded total order), extension of a well-founded relation to a well-founded total one, and comparability of types by injections. **Not used by Lantana:** Imported only by `cardinal.v`, which is itself unused. |
| `cardinal.v` | `basics.v`, `classical_ordinal.v`, `ordinal.v`, `sflib.v`, `to_set.v`, `well_ordering.v`, `wf_rel.v` | Cardinals as ordinals: the cardinal of a type (`cardinal.cardinal`), comparison by injections, the next cardinal, and the aleph and beth hierarchies. **Not used by Lantana:** Imported only by `inaccessible.v`, which is itself unused. |
| `inaccessible.v` | `arithmetic.v`, `basics.v`, `cardinal.v`, `classical_ordinal.v`, `inaccessibility.v`, `ordinal.v`, `sflib.v` | `kappa := ord.large`, the supremum of the ordinals of well-founded relations on types of a smaller universe, is regular and strongly inaccessible, and closed under alephs, beths and ordinal arithmetic. **Not used by Lantana:** Not imported by any file. |
| `zorn.v` | `basics.v`, `classical_ordinal.v`, `fixedpoint.v`, `ordinal.v`, `sflib.v` | Several forms of Zorn's lemma, proved with ordinals. **Not used by Lantana:** Not imported by any file. |

## Notes

- The files are those of coq-ordinal 0.5.6 (the version `configure`
  installs), with renames so that both copies can be loaded together: file names in snake case;
  modules in lower case (`Ord` → `ord`, `OrdArith` → `ordArith`, `Hessenberg` → `hessenberg`,
  `ClassicOrd` → `classicOrd`, …); the notation scope `ord_scope` (`%ord`) → `ordinal_scope`
  (`%ordi`); sflib's internal names and hint database → `sflibord`; and `ToSet.to_set` → `toSet.toSet`.
  The proofs are unchanged.
- So in Lantana, `ord.t` and `%ordi` refer to this copy, and `Ord.t` and `%ord` to the opam copy.
- The seven files marked "Not used by Lantana" are kept so that the copy stays complete. They
  are still built (they are listed in `_CoqProject`).
