From iris.algebra Require Export gmap.
From iris.prelude Require Import options.

Notation tree K A := (gmap K (A * (list K))%type).

Inductive is_tree {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type} : K → tree K A → Prop :=
| is_tree_leaf k t a : t = {[k := (a, [])]} → is_tree k t
| is_tree_node k t n a (cs : list (K * tree K A)) :
  n = {[k := (a, fst <$> cs)]} →
  t = n ∪ (⋃ (snd <$> cs)) →
  map_disjoint_list (n :: (snd <$> cs)) →
  (∀ c r, (c, r) ∈ cs → is_tree c r) →
  is_tree k t.

Section tree.

End tree.
