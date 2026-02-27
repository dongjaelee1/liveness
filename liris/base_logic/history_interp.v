From iris.algebra Require Import mono_list.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.base_logic Require Export osat.

Definition event (St : Type) := (prod (prod nat St) obligations).
Canonical Structure eventO `{SI : indexT} (St : Type) := leibnizO (event St).

(** The ghost state for history. *)
Module histGS.

  Class histGpreS `{SI : indexT} (Σ : gFunctors) (St : Type) : Set :=
    HistGpreS {
        histGpreS_hist : inG Σ (mono_listUR (eventO St));
      }.

  Class histGS `{SI : indexT} (Σ : gFunctors) (St : Type) : Set :=
    HistG {
        hist_inG : histGpreS Σ St;
        hist_name : gname;
      }.

  Definition histΣ `{SI : indexT} (St : Type) : gFunctors :=
    #[GFunctor (mono_listUR (eventO St))
      ].

  Global Instance subG_histΣ `{SI : indexT} {Σ} {St} : subG (histΣ St) Σ → (histGpreS Σ St).
  Proof. solve_inG. Qed.

End histGS.
Import histGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances hist_inG histGpreS_hist.

Local Definition hG_history_auth_def `{SI : indexT} `{@histGS SI Σ St}
  (h : list (event St)) : iProp Σ :=
  (own hist_name (●ML h))%I.
Local Definition hG_history_auth_aux : seal (@hG_history_auth_def). Proof. by eexists. Qed.
Definition hG_history_auth := hG_history_auth_aux.(unseal).
Local Definition hG_history_auth_unseal :
  @hG_history_auth = @hG_history_auth_def := hG_history_auth_aux.(seal_eq).
Global Arguments hG_history_auth {SI Σ St _}.

Local Definition hG_event_def `{SI : indexT} `{@histGS SI Σ St}
  (e : event St) : iProp Σ :=
  (∃ (p : list (event St)), own hist_name (◯ML (p ++ [e])))%I.
Local Definition hG_event_aux : seal (@hG_event_def). Proof. by eexists. Qed.
Definition hG_event := hG_event_aux.(unseal).
Local Definition hG_event_unseal :
  @hG_event = @hG_event_def := hG_event_aux.(seal_eq).
Global Arguments hG_event {SI Σ St _}.

(** Properties *)
Section proof.
  Context `{SI : indexT} `{HIST : !histGS Σ St}.

End proof.

(** State interpretation and predicates defined by the language,
    with the thread ids to connect to the obligation model. *)
Class state_interp_class `{SI : indexT} (Σ : gFunctors) (St Π : Type) :=
  { state_interp : St → gset positive → iProp Σ;
    state_pred : Π → iProp Σ;
    state_sat : St → Π → Prop;
    state_interp_wf :
    (∀ (σ : St) Θ (π : Π), (state_interp σ Θ ∗ state_pred π) ⊢ ⌜ state_sat σ π ⌝);
  }.

Definition event_fulfilled_state `{SI : indexT} `{@histGS SI Σ St} `{@state_interp_class SI Σ St Π}
  (k : oid) (π : Π) : iProp Σ :=
  (∃ (e : event St), hG_event e ∗ ⌜ e.2 !! k = Some (obligation_fulfilled) ⌝ ∧ ⌜ state_sat e.1.2 π ⌝)%I.
Global Typeclasses Opaque event_fulfilled_state.
Global Instance: Params (@event_fulfilled_state) 6 := {}.

Definition event_fulfilled_alive `{SI : indexT} `{@histGS SI Σ St}
  (k κ : oid) : iProp Σ :=
  (∃ (e : event St), hG_event e ∗ ⌜ e.2 !! k = Some (obligation_fulfilled) ⌝ ∧
                     ⌜ (∃ f o, e.2 !! κ = Some (obligation_assigned f o)) ∨ (e.2 !! κ = Some (obligation_fulfilled)) ⌝)%I.
Global Typeclasses Opaque event_fulfilled_alive.
Global Instance: Params (@event_fulfilled_alive) 4 := {}.

Definition history_wf {St} (h : list (event St)) : Prop :=
  ∀ i (e1 e2 : event St), (h !! i = Some e1) → (h !! (S i) = Some e2) → (obls_advance e1.2 e2.2).

Definition history_interp `{SI : indexT} `{@histGS SI Σ St} `{@state_interp_class SI Σ St Π}
  `{!@osatGS.osatGS _ Σ} `{!ord_mono_fun_class}
  (h : list (event St)) (t : nat) (σ : St) (Θ : gset positive) (Ω : obligations) : iProp Σ :=
  (⌜ history_wf h ⌝ ∧ ⌜ last h = Some ((t, σ), Ω) ⌝ ∧ hG_history_auth h ∗ state_interp σ Θ ∗ osat Ω)%I.
Global Typeclasses Opaque history_interp.
Global Instance: Params (@history_interp) 8 := {}.

(** Properties *)
Section hist.
  Context `{SI : indexT} `{HIST : !histGS Σ St} `{SIC : !state_interp_class Σ St Π}
    `{OSAT : !osatGS.osatGS Σ} `{OMF : !ord_mono_fun_class}.

End hist.
