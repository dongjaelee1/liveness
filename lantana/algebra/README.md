# `lantana/algebra/`

The resource algebras (Iris cameras) of the logic and the structures they are built from: cameras
for fuel, credits and transfinite later credits; the measures and layers in which fuel is counted,
interpreted into the ordinals of the Ordinal library; and lemmas about finite maps of sets (stdpp)
used by the ghost state. `ordinal_existential_properties.v` connects these ordinals to the
step-indices of Transfinite Iris.

Builds on `lantana/prelude/`. Used by `lantana/base_logic/`, `lantana/program_logic/`, `lantana_heap_lang/`, `lantana_heap_lang/examples/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `auth_mra.v` | — | `auth_mra R`: the authoritative camera over Iris's monotone resource algebra for a relation `R`, with fractional authority `●AM a` and lower-bound knowledge `◯AM a`. Also the class `auth_mra_class` and the lexicographic order `lex_R`. |
| `list_of_sets.v` | — | Lists of sets: `union_list_of_sets`, `disjoint_list_of_sets`, and their behavior under list operations and updates of single elements. |
| `map_of_sets.v` | — | Maps of sets: `union_sets`, `disjoint_sets`, the restriction `filter_sets` to a set of keys, and their behavior under map operations and partitions of the keys. |
| `measure.v` | — | The paper's measures: the syntax `measure` (embedded well-founded orders, `ms_large`, sum, product, exponent, and the extension measure `ms_extend`), its interpretation `measure_rep` into ordinals at a layer of a `layer_class`, and `Layerless` measures. |
| `layer.v` | `measure.v` | The internal layers `layer := ord.t × nat`, ordered lexicographically, as an instance of `layer_class`; ordinal notations. |
| `ocm.v` | — | Ordered commutative monoids (`OCM.t`, with a total preorder), and the `quotient` and `partition` structures over them used by `bank.v` and `bcred.v`. |
| `bank.v` | `ocm.v` | The bank camera for obligation fuel: `cash a` is fuel, and `debt a q` a fraction of the supply `a` that bounds all cash. Cash is issued from the full supply (`debt_owe`) and paid back to lower it (`debt_pay`). |
| `bcred.v` | `ocm.v` | The bounded-credit camera, used for carrier fuel and witness credits: `credit a` bounded by the duplicable `credit_bound a`, with splitting and spending (`credit_spend`). |
| `ordinal_existential_properties.v` | — | Transfinite Iris's existential property for the type `Ord.t` at the ordinal step-index `ordI` (an existential over `Ord.t` commutes with step-indexing), used by the adequacy proofs (`adequacy.v`, `adequacy_iris.v`). |
| `ordinal_ucmra.v` | — | `OrdUR`: the discrete, cancelable unital camera of ordinals `Ord.t` with the Hessenberg sum, used for transfinite later credits. |
| `wfocm.v` | `ocm.v` | Well-founded ordered commutative monoids (`WFOCM.t`): an OCM with a well-founded strict order compatible with addition. |
| `ordinal_wfocm.v` | `wfocm.v` | The ordinals `Ord.t` with the Hessenberg sum as a WFOCM (`ord_wfocm`), and the class `OrdFromWFOCM` of WFOCMs whose embedding into the ordinals respects addition and order. |

## Notes

`ocm.v`, `bank.v` and `bcred.v` follow the modules `OCM`, `Fuel` and `CounterRA` of the Lilo and
FOS developments.
