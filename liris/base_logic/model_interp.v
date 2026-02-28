From iris.algebra Require Import mono_list.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.base_logic Require Export owit othread.

Canonical Structure obligationO `{SI : indexT} := leibnizO obligation.

(** The ghost state for model history. *)
Module mhistGS.

  Class mhistGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    MhistGpreS {
        mhistGpreS_hist : inG Σ (mono_listUR (obligations));
      }.

  Class mhistGS `{SI : indexT} (Σ : gFunctors) : Set :=
    MhistG {
        mhist_inG : mhistGpreS Σ;
        hist_name : gname;
      }.

  Definition mhistΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (mono_listUR (obligations))
      ].

  Global Instance subG_mhistΣ `{SI : indexT} {Σ} : subG (mhistΣ) Σ → (mhistGpreS Σ).
  Proof. solve_inG. Qed.

End mhistGS.
Import mhistGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances mhist_inG mhistGpreS_hist.

Local Definition mhG_history_auth_def `{SI : indexT} `{@mhistGS SI Σ}
  (h : list obligations) : iProp Σ :=
  (own hist_name (●ML h))%I.
Local Definition mhG_history_auth_aux : seal (@mhG_history_auth_def). Proof. by eexists. Qed.
Definition mhG_history_auth := mhG_history_auth_aux.(unseal).
Local Definition mhG_history_auth_unseal :
  @mhG_history_auth = @mhG_history_auth_def := mhG_history_auth_aux.(seal_eq).
Global Arguments mhG_history_auth {SI Σ _}.

Local Definition mhG_event_def `{SI : indexT} `{@mhistGS SI Σ}
  (n : nat) (e : obligations) : iProp Σ :=
  (∃ (h : list obligations), (⌜ length h = (S n) ∧ last h = Some e ⌝) ∧ own hist_name (◯ML h))%I.
Local Definition mhG_event_aux : seal (@mhG_event_def). Proof. by eexists. Qed.
Definition mhG_event := mhG_event_aux.(unseal).
Local Definition mhG_event_unseal :
  @mhG_event = @mhG_event_def := mhG_event_aux.(seal_eq).
Global Arguments mhG_event {SI Σ _}.

TODO

(** Properties *)
Section proof.
  Context `{SI : indexT} `{MHIST : !mhistGS Σ St}.

  Global Instance mhGmhistory_auth_timeless h : Timeless (mhGmhistory_auth h).
  Proof. rewrite mhGmhistory_auth_unseal /mhGmhistory_auth_def. apply _. Qed.

  Global Instance mhGevent_persistent n e : Persistent (mhGevent n e).
  Proof. rewrite mhGevent_unseal /mhGevent_def. apply _. Qed.
  Global Instance mhGevent_timeless n e : Timeless (mhGevent n e).
  Proof. rewrite mhGevent_unseal /mhGevent_def. apply _. Qed.

  Lemma mhGmhistory_auth_app h1 h2 :
    mhGmhistory_auth h1 ⊢ |==> mhGmhistory_auth (h1 ++ h2).
  Proof.
    rewrite mhGmhistory_auth_unseal /mhGmhistory_auth_def.
    apply own_update, mono_list_update. exists h2. auto.
  Qed.

  Lemma mhGmhistory_event h n e :
    (h !! n = Some e) →
    mhGmhistory_auth h ⊢ mhGevent n e.
  Proof.
    rewrite mhGmhistory_auth_unseal /mhGmhistory_auth_def. rewrite mhGevent_unseal /mhGevent_def.
    iIntros (LU) "H". apply list_elem_of_split_length in LU. destruct LU as (l1&l2&?&?).
    iExists (l1 ++ [e]). iSplit.
    { iPureIntro. subst. rewrite length_app last_app. simpl. split; auto. lia. }
    rewrite mono_list_auth_lb_op. iDestruct "H" as "[_ H]".
    rewrite -(mono_list_lb_op_r _ (h : list (leibnizO _))).
    { iDestruct "H" as "[_ $]". }
    exists l2. subst. rewrite cons_middle app_assoc. auto.
  Qed.

  Lemma mhGevent_mhistory_lookup h n e :
    mhGmhistory_auth h ∗ mhGevent n e ⊢ ⌜ h !! n = Some e ⌝.
  Proof.
    rewrite mhGmhistory_auth_unseal /mhGmhistory_auth_def. rewrite mhGevent_unseal /mhGevent_def.
    iIntros "(H& (%&%& E))". iCombine "H E" gives %V. apply mono_list_both_valid in V. destruct V.
    apply leibniz_equiv in H0. destruct H. subst. iPureIntro.
    rewrite last_lookup H in H1. simpl in H1. rewrite lookup_app_l; auto. rewrite H. lia.
  Qed.

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

Definition event_fulfilled_state `{SI : indexT} `{@mmhistGS SI Σ St} `{@state_interp_class SI Σ St Π}
  (k : oid) (π : Π) : iProp Σ :=
  (∃ (e : event St), mhGevent e ∗ ⌜ e.2 !! k = Some (obligation_fulfilled) ⌝ ∧
                     ⌜ state_sat e.1.2 π ⌝)%I.
Global Typeclasses Opaque event_fulfilled_state.
Global Instance: Params (@event_fulfilled_state) 6 := {}.

Definition event_fulfilled_alive `{SI : indexT} `{@mmhistGS SI Σ St}
  (k κ : oid) : iProp Σ :=
  (∃ (e : event St), mhGevent e ∗ ⌜ e.2 !! k = Some (obligation_fulfilled) ⌝ ∧
                     ⌜ (e.2 !! κ ≠ Some (obligation_expired)) ⌝)%I.
                     (* ⌜ (∃ f o, e.2 !! κ = Some (obligation_assigned f o)) ∨ (e.2 !! κ = Some (obligation_fulfilled)) ⌝)%I. *)
Global Typeclasses Opaque event_fulfilled_alive.
Global Instance: Params (@event_fulfilled_alive) 4 := {}.

Definition mmhistory_wf {St} (h : list (event St)) : Prop :=
  ∀ i (e1 e2 : event St), (h !! i = Some e1) → (h !! (S i) = Some e2) → (obls_advance e1.2 e2.2).

Definition mmhistory_interp `{SI : indexT} `{@mmhistGS SI Σ St} `{@state_interp_class SI Σ St Π}
  `{!@osatGS.osatGS _ Σ} `{!ord_mono_fun_class}
  (h : list (event St)) (t : nat) (σ : St) (Θ : gset positive) (Ω : obligations) : iProp Σ :=
  (⌜ mmhistory_wf h ⌝ ∧ ⌜ last h = Some ((t, σ), Ω) ⌝ ∧ mhGmmhistory_auth h ∗ state_interp σ Θ ∗ osat Ω)%I.
Global Typeclasses Opaque mmhistory_interp.
Global Instance: Params (@mmhistory_interp) 8 := {}.

(** Properties *)
Section mmhist.
  Context `{SI : indexT} `{MMHIST : !mmhistGS Σ St} `{SIC : !state_interp_class Σ St Π}
    `{OSAT : !osatGS.osatGS Σ} `{OMF : !ord_mono_fun_class}.

End mmhist.
