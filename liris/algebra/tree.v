From iris.algebra Require Export gmap.
From iris.prelude Require Import options.

(* Notation tree K A := (gmap K (A * (list K))%type). *)
(* Definition tree (K : Type) {EqDecision0 : EqDecision K} {H : Countable K} (A : Type) := *)
(*   gmap K (A * (list positive))%type. *)
Definition tree (A : Type) :=
  gmap positive (A * (list positive))%type.

Lemma check {A : Type} (t1 t2 : tree A) :
  t1 ∪ t2 = t1 ∪ t2.
Lemma check {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type} (t1 t2 : tree K A) :
  t1 ∪ t2 = t1 ∪ t2.

Inductive is_tree {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type} : K → tree K A → Prop :=
| is_tree_leaf k a : is_tree k {[k := (a, [])]}
| is_tree_node k a (ts : list (K * tree K A)) :
  map_disjoint_list (snd <$> ts) →
  is_tree k (⋃ (snd <$> ts)).

Section tree.

End tree.
