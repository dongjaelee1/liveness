From iris.algebra Require Import gmap_view gmap gset mra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.

(* A node is identified by its key *)
Definition digraph_key := positive.
(* A node has a monotonically updatable data of type A, an iProp, and keys of its children.
   Set of children monotonically grows.
 *)
Definition digraph `{SI : indexT} {A : Type} (R : relation A) {Σ : gFunctors} :=
  gmap digraph_key (prod (prod (mra R) (iProp Σ)) (gset digraph_key)).
Definition digraphR `{SI : indexT} {A : Type} (R : relation A) (Σ : gFunctors) :=
  gmap_viewR digraph_key (prodR (prodR (mraUR R) (agreeR $ (laterO (iPropO Σ)))) (gsetUR digraph_key)).
Definition digraphUR `{SI : indexT} {A : Type} (R : relation A) (Σ : gFunctors) :=
  gmap_viewUR digraph_key (prodR (prodR (mraUR R) (agreeR $ (laterO (iPropO Σ)))) (gsetUR digraph_key)).

(** The ghost state for digraph *)
Class digraphGpreS `{SI : indexT} {A : Type} (R : relation A) (Σ : gFunctors) :=
  DigraphGpreS {
      #[local] digraphGpreS_inG :: inG Σ (digraphUR R Σ)
    }.

Class digraphGS `{SI : indexT} {A : Type} (R : relation A) (Σ : gFunctors) :=
  DigraphGS {
      #[local] digraphGS_inG :: inG Σ (digraphUR R Σ);
      digraphGS_name : gname;
    }.
Global Hint Mode digraphGS - - ! - : typeclass_instances.

Definition digraphΣ `{SI : indexT} {A : Type} (R : relation A) : gFunctors :=
  #[GFunctor (gmap_viewTRF digraph_key (prodTRF (prodTRF (mraUR R) (agreeTRF $ (laterTF idTF))) (gsetUR digraph_key)))].

Global Instance subG_digraphΣ `{SI : indexT} {A : Type} (R : relation A) {Σ} : subG (digraphΣ R) Σ → (digraphGpreS R Σ).
Proof. solve_inG. Qed.

Section digraph.
  Context `{SI : indexT} {A : Type} (R : relation A) `{!digraphGS R Σ}.

  TODO

gset_local_update:
  ∀ {SI : indexT} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} (X Y X' : gset K), X ⊆ X' → (X, Y) ~l~> (X', X')
gset_included: ∀ {SI : indexT} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} (X Y : gset K), X "≼" Y ↔ X ⊆ Y

End digraph.
