# `lantana/prelude/`

General facts used throughout Lantana: the classical axioms the development assumes, ordinal arithmetic on top of the Ordinal library and stdpp, for both copies of the library (the opam package, whose ordinals are `Ord.t`, and the copy in `ordinal/`, whose ordinals `ord.t` are the layers), and well-founded relations.

Builds on `ordinal/`. Used by `lantana/algebra/`, `lantana/program_logic/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `axioms.v` | — | The classical axioms of the development, from the Rocq standard library under short names: excluded middle (`classic`), proof irrelevance, propositional and functional extensionality (`func_ext`), and choice. |
| `ordinal_facts.v` | — | Facts about ordinals of the Ordinal library (Hessenberg sum, Jacobsthal product and power, ordinals of well-founded relations), and the class `ord_mono_fun_class` of increasing ordinal functions `η`. |
| `ordinal_copy_facts.v` | — | The same facts for the copy in `ordinal/` (`ord.t`), used for layers (`lantana/algebra/layer.v`). |
| `wf_structs.v` | `axioms.v` | Well-founded relations: transitive closure, well-founded trees `ord_tree` in which every family has an upper bound, and orders on `nat`, `option`, sums and pairs (including lexicographic orders). |
