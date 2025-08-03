From iris.algebra Require Import gmap_view gmap mono_list.
From liris.algebra Require Import auth_mra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.

(* A vertex is identified by its key *)
Definition vertex := positive.
(* A vertex may own an iProp, a monotonically updatable data of type A,
   a flag (false means the vertex owns the iProp), and keys of its children.
   List of children can only monotonically grow.
 *)
Definition digraph (A : Type) :=
  gmap vertex (prod (prod A (list vertex)) bool).
Definition digraph_aux `{SI : indexT} (A : Type) {Σ : gFunctors} :=
  gmap vertex (prod (prod (prod A (list vertex)) bool) (iProp Σ)).

(** The ghost state for digraph *)
Module digraphGS.
  Class digraphGpreS `{SI : indexT} (A : Type) (R : relation A) (Σ : gFunctors) : Set :=
    DigraphGpreS {
        digraphGpreS_prop :: inG Σ (gmap_viewR vertex (agreeR $ (laterO (iPropO Σ))));
        digraphGpreS_state :: inG Σ (gmapUR vertex (prodUR (prodUR (auth_mraUR R) (mono_listUR vertex)) (auth_mraUR bool_le)));
      }.

  Class digraphGS `{SI : indexT} (A : Type) (R : relation A) (Σ : gFunctors) : Set :=
    DigraphGS {
        digraphGS_inG :: digraphGpreS A R Σ;
        prop_name : gname;
        state_name : gname;
      }.
  Global Hint Mode digraphGS - - - - : typeclass_instances.

  Definition digraphΣ `{SI : indexT} (A : Type) (R : relation A) : gFunctors :=
    #[GFunctor (gmap_viewTRF vertex (agreeTRF $ (laterTF idTF)));
      GFunctor (gmapTRF vertex (prodTRF (prodTRF (auth_mraUR R) (mono_listUR vertex)) (auth_mraUR bool_le)))
      ].

  Global Instance subG_digraphΣ `{SI : indexT} (A : Type) (R : relation A) {Σ} : subG (digraphΣ A R) Σ → (digraphGpreS A R Σ).
  Proof. solve_inG. Qed.

End digraphGS.
Import digraphGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances digraphGS_inG digraphGpreS_prop digraphGpreS_state.

Definition prop_unfold `{SI : indexT} {Σ} (P : iProp Σ) : later (iProp Σ) := Next P.
Definition digP_prop `{SI : indexT} `{!digraphGS A R Σ} (i : vertex) (P : iProp Σ) : iProp Σ :=
  own prop_name (gmap_view_frag i DfracDiscarded (to_agree $ prop_unfold P)).
Global Typeclasses Opaque digP_prop.
Global Instance: Params (@prop_unfold) 2 := {}.
Global Instance: Params (@digP_prop) 6 := {}.

Definition digP_elem `{SI : indexT} `{!digraphGS A R Σ} (i : vertex) : iProp Σ :=
  ∃ P, digP_prop i P.
Global Typeclasses Opaque digP_elem.
Global Instance: Params (@digP_elem) 6 := {}.

Definition digS_data `{SI : indexT} `{!digraphGS A R Σ} (i : vertex) (a : A) : iProp Σ :=
  own state_name ({[ i := (◯AM[R] a : auth_mraUR _, ε, ε) ]}).
Global Typeclasses Opaque digS_data.
Global Instance: Params (@digS_data) 6 := {}.

Definition digS_data_auth `{SI : indexT} `{!digraphGS A R Σ} (i : vertex) (q : Qp) (a : A) : iProp Σ :=
  own state_name ({[ i := (●AM{#q}[R] a : auth_mraUR _, ε, ε) ]}).
Global Typeclasses Opaque digS_data_auth.
Global Instance: Params (@digS_data_auth) 6 := {}.

Definition digS_arcs `{SI : indexT} `{!digraphGS A R Σ} (i : vertex) (l : list vertex) : iProp Σ :=
  own state_name ({[ i := (ε, ◯ML l, ε) ]}).
Global Typeclasses Opaque digS_arcs.
Global Instance: Params (@digS_arcs) 6 := {}.

Definition digS_arcs_auth `{SI : indexT} `{!digraphGS A R Σ} (i : vertex) (q : Qp) (l : list vertex) : iProp Σ :=
  own state_name ({[ i := (ε, ●ML{#q} l, ε) ]}).
Global Typeclasses Opaque digS_arcs_auth.
Global Instance: Params (@digS_arcs_auth) 6 := {}.

Definition digS_flag `{SI : indexT} `{!digraphGS A R Σ} (i : vertex) (b : bool) : iProp Σ :=
  own state_name ({[ i := (ε, ε, ◯AM[bool_le] b : auth_mraUR _) ]}).
Global Typeclasses Opaque digS_flag.
Global Instance: Params (@digS_flag) 6 := {}.

Definition digS_flag_auth `{SI : indexT} `{!digraphGS A R Σ} (i : vertex) (q : Qp) (b : bool) : iProp Σ :=
  own state_name ({[ i := (ε, ε, ●AM{#q}[bool_le] b : auth_mraUR _) ]}).
Global Typeclasses Opaque digS_flag_auth.
Global Instance: Params (@digS_flag_auth) 6 := {}.

Definition dsat `{SI : indexT} `{!digraphGS A R Σ} (Γ : digraph A) : iProp Σ :=
  locked
    (∃ (DG : digraph_aux A),
        (⌜ Γ = fst <$> DG ⌝) ∗
        (own prop_name (gmap_view_auth (DfracOwn 1) (to_agree <$> (prop_unfold <$> (snd <$> DG))))) ∗
        ([∗ map] i ↦ V ∈ DG,
           match V with
           | (a, l, f, P) =>
               (digS_data_auth i (1/2)%Qp a) ∗
               (digS_arcs_auth i (1/2)%Qp l) ∗
               (digS_flag_auth i (1/2)%Qp f) ∗
               (if f
                then ([∗ list] j ∈ l, digS_flag j true)
                else (▷ P) ∗ ([∗ list] j ∈ l, digS_flag_auth j (1/2)%Qp false ∨ digS_flag j true))
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

  (* TODO *)

End digraph.
