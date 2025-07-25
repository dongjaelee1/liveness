From iris.algebra Require Import gmap_view gmap mono_list.
From liris.algebra Require Import auth_mra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.

(* A vertex is identified by its key *)
Definition digraph_id := positive.
(* A vertex may own an iProp, a monotonically updatable data of type A,
   a flag (false means the vertex owns the iProp), and keys of its children.
   List of children can only monotonically grow.
 *)
Definition digraph (A : Type) :=
  gmap digraph_id (prod (prod A bool) (list digraph_id)).
Definition digraph_full `{SI : indexT} (A : Type) {Σ : gFunctors} :=
  gmap digraph_id (prod (prod (prod A bool) (list digraph_id)) (iProp Σ)).

(** The ghost state for digraph *)
Module digraphGS.
  Class digraphGpreS `{SI : indexT} (A : Type) (R : relation A) (Σ : gFunctors) : Set :=
    DigraphGpreS {
        digraphGpreS_prop :: inG Σ (gmap_viewR digraph_id (agreeR $ (laterO (iPropO Σ))));
        digraphGpreS_state :: inG Σ (gmapUR digraph_id (prodUR (prodUR (auth_mraUR R) (auth_mraUR bool_le)) (mono_listUR digraph_id)));
      }.

  Class digraphGS `{SI : indexT} (A : Type) (R : relation A) (Σ : gFunctors) : Set :=
    DigraphGS {
        digraphGS_inG :: digraphGpreS A R Σ;
        prop_name : gname;
        state_name : gname;
      }.
  Global Hint Mode digraphGS - - - - : typeclass_instances.

  Definition digraphΣ `{SI : indexT} (A : Type) (R : relation A) : gFunctors :=
    #[GFunctor (gmap_viewTRF digraph_id (agreeTRF $ (laterTF idTF)));
      GFunctor (gmapTRF digraph_id (prodTRF (prodTRF (auth_mraUR R) (auth_mraUR bool_le)) (mono_listUR digraph_id)))
      ].

  Global Instance subG_digraphΣ `{SI : indexT} (A : Type) (R : relation A) {Σ} : subG (digraphΣ A R) Σ → (digraphGpreS A R Σ).
  Proof. solve_inG. Qed.

End digraphGS.
Import digraphGS.

(* User interface *)
Local Existing Instances digraphGS_inG digraphGpreS_prop digraphGpreS_state.

Definition prop_unfold `{SI : indexT} {Σ} (P : iProp Σ) : later (iProp Σ) := Next P.
Definition digP_prop `{SI : indexT} `{!digraphGS A R Σ} (i : digraph_id) (P : iProp Σ) : iProp Σ :=
  own prop_name (gmap_view_frag i DfracDiscarded (to_agree $ prop_unfold P)).
Global Typeclasses Opaque digP_prop.
Global Instance: Params (@prop_unfold) 2 := {}.
Global Instance: Params (@digP_prop) 6 := {}.

Definition digP_elem `{SI : indexT} `{!digraphGS A R Σ} (i : digraph_id) : iProp Σ :=
  ∃ P, digP_prop i P.
Global Typeclasses Opaque digP_elem.
Global Instance: Params (@digP_elem) 6 := {}.

Definition digS_data `{SI : indexT} `{!digraphGS A R Σ} (i : digraph_id) (a : A) : iProp Σ :=
  own state_name ({[ i := (◯AM[R] a : auth_mraUR _, ε, ε) ]}).
Global Typeclasses Opaque digS_data.
Global Instance: Params (@digS_data) 6 := {}.

Definition digS_flag `{SI : indexT} `{!digraphGS A R Σ} (i : digraph_id) (b : bool) : iProp Σ :=
  own state_name ({[ i := (ε, ◯AM[bool_le] b : auth_mraUR _, ε) ]}).
Global Typeclasses Opaque digS_flag.
Global Instance: Params (@digS_flag) 6 := {}.

Definition digS_arcs `{SI : indexT} `{!digraphGS A R Σ} (i : digraph_id) (l : list digraph_id) : iProp Σ :=
  own state_name ({[ i := (ε, ε, ◯ML l) ]}).
Global Typeclasses Opaque digS_arcs.
Global Instance: Params (@digS_arcs) 6 := {}.

Definition digS_arcs_auth `{SI : indexT} `{!digraphGS A R Σ} (i : digraph_id) (l : list digraph_id) : iProp Σ :=
  own state_name ({[ i := (ε, ε, ●ML l) ]}).
Global Typeclasses Opaque digS_arcs_auth.
Global Instance: Params (@digS_arcs_auth) 6 := {}.

Definition digraph_sat `{SI : indexT} `{!digraphGS A R Σ} (Γ : digraph A) : iProp Σ :=
  locked
    (∃ (DG : digraph_full A),
        (⌜ Γ = fst <$> DG ⌝) ∗
        (own prop_name (gmap_view_auth (DfracOwn 1) (to_agree <$> (prop_unfold <$> (snd <$> DG))))) ∗
        ([∗ map] i ↦ vP ∈ DG,
           match vP with
           | (a, f, l, P) => (if f then ▷ P else emp) ∗
                            
           end)
    )%I.

Section digraph.
  Context `{SI : indexT} {A : Type} (R : relation A) `{!digraphGS A R Σ}.

  Local Instance prop_unfold_contractive : Contractive (@prop_unfold SI Σ).
  Proof. solve_contractive. Qed.
  Global Instance digP_prop_contractive i : Contractive (@digP_prop SI _ R Σ _ i).
  Proof. solve_contractive. Qed.
  Global Instance digP_prop_persistent i P : Persistent (digP_prop i P).
  Proof. rewrite /digP_prop. apply _. Qed.
  Global Instance digP_elem_persistent i : Persistent (digP_elem i).
  Proof. rewrite /digP_elem. apply _. Qed.

  Global Instance digS_data_persistent i a : Persistent (digS_data i a).
  Proof. rewrite /digS_data. apply _. Qed.
  Global Instance digS_flag_persistent i b : Persistent (digS_flag i b).
  Proof. rewrite /digS_flag. apply _. Qed.
  Global Instance digS_arcs_persistent i l : Persistent (digS_arcs i l).
  Proof. rewrite /digS_arcs. apply _. Qed.

  TODO

gset_local_update:
  ∀ {SI : indexT} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} (X Y X' : gset K), X ⊆ X' → (X, Y) ~l~> (X', X')
gset_included: ∀ {SI : indexT} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} (X Y : gset K), X "≼" Y ↔ X ⊆ Y

End digraph.
