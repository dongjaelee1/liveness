From iris.algebra Require Export gmap.
From iris.prelude Require Import options.

Notation tree K A := (gmap K (A * (list K))).

Inductive tree_wf {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type} : K → tree K A → Prop :=
| tree_wf_leaf r t a : t = {[r := (a, [])]} → tree_wf r t
| tree_wf_node r t n a (cs : list (K * tree K A)) :
  n = {[r := (a, fst <$> cs)]} →
  t = n ∪ (⋃ (snd <$> cs)) →
  map_disjoint_list (n :: (snd <$> cs)) →
  (∀ k u, (k, u) ∈ cs → tree_wf k u) →
  tree_wf r t.

Section tree.
  Context {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type}.

End tree.

Notation forest K A := (gmap K (list (K * tree K A))).

Definition forest_to_trees {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type}
  (f : forest K A) : list (K * tree K A) :=
  map_fold (λ k t l, l ++ t) [] f.

Definition forest_to_map {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type}
  (f : forest K A) : gmap K A :=
  fst <$> ⋃ ((snd <$> (forest_to_trees f)) : list (tree K A)).

Definition forest_wf_trees {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type}
  (f : forest K A) : Prop :=
  map_disjoint_list ((snd <$> (forest_to_trees f)) : list (tree K A)).

Section forest.
  Context {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type}.

End forest.
