From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.base_logic Require Export opreds.
From lantana.program_logic Require Export temporal_registry.

(** * Ghost state of the temporal layer

    [temporalGS] bundles the ghost state of the obligation model, of the history and of the
    registry of trace-visible structures. [TemporalInterp] is the interpretation of the
    temporal layer: a resource that the program logic threads together with the history
    interpretation ([history_tinterp]), without knowing its content. The temporal layer
    (temporal_guarantee.v) fixes it to the state of the registry; until then it is a
    parameter, so the program logic stays independent of the temporal layer. *)

Class temporalGpreS `{SI : sidx} (Λ : language) (Σ : gFunctors) :=
  TemporalGpreS {
      #[local] temporalGpreS_mupd :: mupdGpreS Σ;
      #[local] temporal_histGpreS :: histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ));
      #[local] temporal_tregGpreS :: tregGS.tregGpreS Λ Σ;
    }.

Class temporalGS `{SI : sidx} (Λ : language) (Σ : gFunctors) :=
  TemporalG {
      (** Obligation model protocol, including invariants. *)
      #[global] temporal_mupdGS :: mupdGS Σ;
      #[global] temporal_histGS :: histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ));
      (** The registry of trace-visible structures (alwaysI, untilI). *)
      #[global] temporal_tregGS :: tregGS.tregGS Λ Σ;
    }.
Global Opaque temporal_mupdGS temporal_histGS temporal_tregGS.
Global Arguments TemporalG {SI Λ Σ}.

Definition temporalΣ `{SI : sidx} (Λ : language) : gFunctors :=
  #[mupdΣ; histGS.histΣ (state Λ * thread_pool Λ * list (observation Λ)); tregGS.tregΣ Λ].
Global Instance subG_temporalΣ `{SI : sidx} {Λ} {Σ} : subG (temporalΣ Λ) Σ → temporalGpreS Λ Σ.
Proof. solve_inG. Qed.

(** The interpretation of the temporal layer. Its only instance is the registry state
    (temporal_guarantee.v, [treg_temporal_interp]); it is keyed by the ghost state so that
    there is one interpretation per instance of the logic. *)
Class TemporalInterp `{SI : sidx} (Λ : language) (Σ : gFunctors)
  `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} := temporal_interp : iProp Σ.
Global Hint Mode TemporalInterp - - - - - : typeclass_instances.

(** The history interpretation together with the interpretation of the temporal layer:
    what the program logic threads between steps and through its model updates. An
    abbreviation, so that proofs see the pair. *)
Notation history_tinterp h n σ Θ κs := (history_interp h n σ Θ κs ∗ temporal_interp)%I.
