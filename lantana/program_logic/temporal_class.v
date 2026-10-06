From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.base_logic Require Export opreds.
From lantana.program_logic Require Export temporal_registry.
Export omodel.

(** * Ghost state of the temporal layer

    [temporalGS]: the ghost state of the obligation model, the history and the registry.
    [TemporalInterp]: the interpretation of the temporal layer, a parameter that the program
    logic threads without knowing its content; guarantee_struct.v fixes it to the registry. *)

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

(** Keyed by the ghost state: one interpretation per instance of the logic. *)
Class TemporalInterp `{SI : sidx} (Λ : language) (Σ : gFunctors)
  `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} := temporal_interp : iProp Σ.
Global Hint Mode TemporalInterp - - - - - : typeclass_instances.

(** What the program logic threads between steps and through model updates; a notation, so
    that proofs see the pair. *)
Notation history_tinterp h n σ Θ κs := (history_interp h n σ Θ κs ∗ temporal_interp)%I.
