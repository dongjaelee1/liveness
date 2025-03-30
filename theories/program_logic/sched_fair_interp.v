From iris.algebra Require Import gmap mono_nat.
From iris.bi Require Import lib.cmra.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liveness Require Export bank language.

Module schedfairGS.
  Class schedfairGpreS `{SI : indexT} `{OCM : OrderedCM.t A leR addO} (Σ : gFunctors) : Set :=
    SchedfairGpreS {
        schedfairGpreS_state : inG Σ (gmapUR thread_id (prodUR bankUR mono_natUR));
      }.

  Class schedfairGS `{SI : indexT} `{OCM : OrderedCM.t A leR addO} (Σ : gFunctors) : Set :=
    SchedfairG {
        schedfair_inG : schedfairGpreS Σ;
        state_name : gname;
      }.

  Definition schedfairΣ `{SI : indexT} `{OCM : OrderedCM.t A leR addO} : gFunctors :=
    #[GFunctor (gmapTRF thread_id (prodTRF bankUR mono_natUR))
      ].

  Global Instance subG_schedfairΣ `{SI : indexT} `{OCM : OrderedCM.t A leR addO} {Σ} : subG schedfairΣ Σ → (schedfairGpreS Σ).
  Proof.
    solve_inG.
  Qed.

End schedfairGS.
Import schedfairGS.

(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances schedfair_inG schedfairGpreS_state.

Definition sfS_exec `{SI : indexT} {Λ : language} `{!schedfairGS Σ} (i : thread_id) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (ε, ●MN{#q} 0) ]} : gmap _ (prod (@bank _ _ _ (@fuel_wf Λ).(WFOrderedCM.orderedCM)) _)).
Global Typeclasses Opaque sfS_exec.
Global Instance: Params (@sfS_exec) 5 := {}.

Definition sfS_term_auth `{SI : indexT} {Λ : language} `{!schedfairGS Σ} (i : thread_id) : iProp Σ :=
  own state_name ({[ i := (ε : bankUR, ●MN 1) ]} : gmap _ (prod (@bank _ _ _ (@fuel_wf Λ).(WFOrderedCM.orderedCM)) _)).
Global Typeclasses Opaque sfS_term_auth.
Global Instance: Params (@sfS_term_auth) 5 := {}.

Definition sfS_term `{SI : indexT} {Λ : language} `{!schedfairGS Σ} (i : thread_id) : iProp Σ :=
  own state_name ({[ i := (ε : bankUR, ◯MN 1) ]} : gmap _ (prod (@bank _ _ _ (@fuel_wf Λ).(WFOrderedCM.orderedCM)) _)).
Global Typeclasses Opaque sfS_term.
Global Instance: Params (@sfS_term) 5 := {}.

Definition sfS_fuel_bound `{SI : indexT} {Λ : language} `{!schedfairGS Σ} (i : thread_id) (a : fuel Λ) (q : Qp) : iProp Σ :=
  own state_name ({[ i := (debt a q, ε) ]} : gmap _ (prod (@bank _ _ _ (@fuel_wf Λ).(WFOrderedCM.orderedCM)) _)).
Global Typeclasses Opaque sfS_fuel_bound.
Global Instance: Params (@sfS_fuel_bound) 5 := {}.

Definition sfS_fuel_credit `{SI : indexT} {Λ : language} `{!schedfairGS Σ} (i : thread_id) (a : fuel Λ) : iProp Σ :=
  own state_name ({[ i := (cash a, ε) ]} : gmap _ (prod (@bank _ _ _ (@fuel_wf Λ).(WFOrderedCM.orderedCM)) _)).
Global Typeclasses Opaque sfS_fuel_credit.
Global Instance: Params (@sfS_fuel_credit) 5 := {}.

Definition schedfairI `{SI : indexT} {Λ : language} `{!@schedfairGS SI _ _ _ _ Σ}
  (ϕ : sched_fuels Λ) : iProp Σ :=
  locked
    ([∗ map] i ↦ oF ∈ ϕ,
       match oF with
       | Some f =>
           (∃ f', ⌜fuel_leR f f'⌝ ∗ sfS_fuel_credit i f' ∗ sfS_exec i 1)
       | None =>
           (∃ f', sfS_fuel_bound i f' 1)
       end
    )%I.
