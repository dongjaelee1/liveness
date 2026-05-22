From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.

Definition union_list_of_sets `{!EqDecision E} `{!Countable E} (L : list (gset E)) : gset E :=
  foldr (λ B A, B ∪ A) ∅ L.
Definition disjoint_list_of_sets `{!EqDecision E} `{!Countable E} (L : list (gset E)) : Prop :=
  ∀ j1 j2 s1 s2, j1 ≠ j2 → L !! j1 = Some s1 → L !! j2 = Some s2 → s1 ## s2.
