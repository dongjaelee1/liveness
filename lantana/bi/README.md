# `lantana/bi/`

The interface and notations of Lantana's weakest preconditions `lWP e @ s; i; E {{ Φ }}`, which have a thread id `i`, and of their Texan triples. Adapted from Iris's `iris/bi/weakestpre.v`.

Builds on nothing else in Lantana. Used by `lantana/program_logic/`.

## Files

In dependency order: each file imports only files above it.

| File | Imports from this directory | Contents |
|---|---|---|
| `weakestpre.v` | — | The class `Lwp` with the notations `lWP e @ s; i; E {{ Φ }}` (and its `NotStuck`/`MaybeStuck` forms) and Texan triples `l{{{ P }}} e @ i; E l{{{ RET v; Q }}}`. |
