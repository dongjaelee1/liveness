From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
From liris.cgraphs Require Export cgraph.
From liris.cgraphs Require Import mapexcl.

Section tree.
  Context {V : Type}.
  Context `{Countable V}.
  Context `{SI : indexT} {L : ofe}.
  Implicit Type t : cgraph V L.
  Implicit Type n : gmap V L.
  Implicit Type v u : V.

  Definition node t v : Prop := is_Some (t !! v).
  Definition root t v : Prop := node t v ∧ in_labels t v ≡ ε.
  Definition internal t v : Prop := node t v ∧ (∃ x, in_labels t v ≡ {[x]}).
  Definition tree_wf t : Prop := cgraph_wf t ∧ (∀ v, node t v → (root t v ∨ internal t v)).

  Inductive descendants t : V → (gset V) → Prop :=
  | descendant_child v Δ (cds : gmap V (gset V)) :
    node t v →
    dom (out_edges t v) = dom cds →
    Δ = map_fold (λ _ cd s, cd ∪ s) ∅ cds →
    (∀ c cd, cds !! c = Some cd → descendants t c cd) →
    descendants t v Δ.
  Definition descendant t : relation V := λ v u, ∃ Δ, descendants t v Δ ∧ u ∈ Δ.

  Definition parent t (v π : V) : Prop := v ∈ dom (out_edges t π).

End tree.
