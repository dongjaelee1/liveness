From iris.algebra Require Import mono_list.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.program_logic Require Export language.

(** The ghost state for history. *)
Module histGS.

  Class histGpreS `{SI : indexT} (Σ : gFunctors) (St : Type) : Set :=
    HistGpreS {
        histGpreS_hist : inG Σ (mono_listUR (leibnizO St));
      }.

  Class histGS `{SI : indexT} (Σ : gFunctors) (St : Type) : Set :=
    HistG {
        hist_inG : histGpreS Σ St;
        hist_name : gname;
      }.

  Definition histΣ `{SI : indexT} (St : Type) : gFunctors :=
    #[GFunctor (mono_listUR (leibnizO St))
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
  (h : list St) : iProp Σ :=
  (own hist_name (●ML (h : list (leibnizO _))))%I.
Local Definition hG_history_auth_aux : seal (@hG_history_auth_def). Proof. by eexists. Qed.
Definition hG_history_auth := hG_history_auth_aux.(unseal).
Local Definition hG_history_auth_unseal :
  @hG_history_auth = @hG_history_auth_def := hG_history_auth_aux.(seal_eq).
Global Arguments hG_history_auth {SI Σ St _}.

Local Definition hG_event_def `{SI : indexT} `{@histGS SI Σ St}
  (n : nat) (e : St) : iProp Σ :=
  (∃ (h : list St), (⌜ length h = (S n) ∧ last h = Some e ⌝) ∧ own hist_name (◯ML (h : list (leibnizO _))))%I.
Local Definition hG_event_aux : seal (@hG_event_def). Proof. by eexists. Qed.
Definition hG_event := hG_event_aux.(unseal).
Local Definition hG_event_unseal :
  @hG_event = @hG_event_def := hG_event_aux.(seal_eq).
Global Arguments hG_event {SI Σ St _}.

(** Properties *)
Section proof.
  Context `{SI : indexT} `{HIST : !histGS Σ St}.

  Global Instance hG_history_auth_timeless h : Timeless (hG_history_auth h).
  Proof. rewrite hG_history_auth_unseal /hG_history_auth_def. apply _. Qed.

  Global Instance hG_event_persistent n e : Persistent (hG_event n e).
  Proof. rewrite hG_event_unseal /hG_event_def. apply _. Qed.
  Global Instance hG_event_timeless n e : Timeless (hG_event n e).
  Proof. rewrite hG_event_unseal /hG_event_def. apply _. Qed.

  Lemma hG_history_auth_app h1 h2 :
    hG_history_auth h1 ⊢ |==> hG_history_auth (h1 ++ h2).
  Proof.
    rewrite hG_history_auth_unseal /hG_history_auth_def.
    apply own_update, mono_list_update. exists h2. auto.
  Qed.

  Lemma hG_history_event h n e :
    (h !! n = Some e) →
    hG_history_auth h ⊢ hG_event n e.
  Proof.
    rewrite hG_history_auth_unseal /hG_history_auth_def. rewrite hG_event_unseal /hG_event_def.
    iIntros (LU) "H". apply list_elem_of_split_length in LU. destruct LU as (l1&l2&?&?).
    iExists (l1 ++ [e]). iSplit.
    { iPureIntro. subst. rewrite length_app last_app. simpl. split; auto. lia. }
    rewrite mono_list_auth_lb_op. iDestruct "H" as "[_ H]".
    rewrite -(mono_list_lb_op_r _ (h : list (leibnizO _))).
    { iDestruct "H" as "[_ $]". }
    exists l2. subst. rewrite cons_middle app_assoc. auto.
  Qed.

  Lemma hG_event_history_lookup h n e :
    hG_history_auth h ∗ hG_event n e ⊢ ⌜ h !! n = Some e ⌝.
  Proof.
    rewrite hG_history_auth_unseal /hG_history_auth_def. rewrite hG_event_unseal /hG_event_def.
    iIntros "(H& (%&%& E))". iCombine "H E" gives %V. apply mono_list_both_valid in V. destruct V.
    apply leibniz_equiv in H0. destruct H. subst. iPureIntro.
    rewrite last_lookup H in H1. simpl in H1. rewrite lookup_app_l; auto. rewrite H. lia.
  Qed.

End proof.

(** State interpretation and predicates defined by the language,
    with the thread ids to connect to the obligation model. *)
Class state_interp_class `{SI : indexT} (Λ : language) (Σ : gFunctors) :=
  { state_interp : state Λ → thread_pool Λ → list (observation Λ) → iProp Σ;
    state_pred_interp : state_pred Λ → iProp Σ;
    state_interp_wf :
    (∀ σ Θ κs π, (state_interp σ Θ κs ∗ state_pred_interp π) ⊢ ⌜ state_sat σ Θ π ⌝);
  }.

Definition history_interp `{SI : indexT} `{@state_interp_class SI Λ Σ}
  `{@histGS SI Σ ((state Λ) * (thread_pool Λ) * (list (observation Λ)))}
  (h : list ((state Λ) * (thread_pool Λ) * (list (observation Λ))))
  (n : nat) σ Θ κs : iProp Σ :=
  locked (⌜ length h = (S n) ∧ last h = Some ((σ, Θ), κs) ⌝ ∗ hG_history_auth h ∗ state_interp σ Θ κs)%I.
Global Typeclasses Opaque history_interp.
Global Instance: Params (@history_interp) 5 := {}.

Local Definition event_pred_def `{SI : indexT} `{@state_interp_class SI Λ Σ}
  `{@histGS SI Σ ((state Λ) * (thread_pool Λ) * (list (observation Λ)))}
  (n : nat) σ Θ κs (π : state_pred Λ) : iProp Σ :=
  (hG_event n (σ, Θ, κs) ∗ ⌜ state_sat σ Θ π ⌝)%I.
Local Definition event_pred_aux : seal (@event_pred_def). Proof. by eexists. Qed.
Definition event_pred := event_pred_aux.(unseal).
Local Definition event_pred_unseal :
  @event_pred = @event_pred_def := event_pred_aux.(seal_eq).
Global Arguments event_pred {SI Λ Σ _ _}.

(** Properties *)
Section hist.
  Context `{SI : indexT} `{SIC : @state_interp_class SI Λ Σ}.
  Context `{HIST : @histGS SI Σ ((state Λ) * (thread_pool Λ) * (list (observation Λ)))}.

  Global Instance event_pred_persistent n σ Θ κs π : Persistent (event_pred n σ Θ κs π).
  Proof. rewrite event_pred_unseal /event_pred_def. apply _. Qed.
  Global Instance event_pred_timeless n σ Θ κs π : Timeless (event_pred n σ Θ κs π).
  Proof. rewrite event_pred_unseal /event_pred_def. apply _. Qed.

  Lemma history_interp_wf h n σ Θ κs :
    history_interp h n σ Θ κs ⊢ ⌜ length h = (S n) ∧ last h = Some (σ, Θ, κs) ⌝.
  Proof. rewrite /history_interp -lock. iIntros "[$ _]". Qed.

  Lemma history_interp_lookup h n σ Θ κs :
    history_interp h n σ Θ κs ⊢ ⌜ h !! n = Some (σ, Θ, κs) ⌝.
  Proof.
    iIntros "HI". iPoseProof (history_interp_wf with "HI") as "%". destruct H.
    rewrite last_lookup H in H0. auto.
  Qed.

  Lemma history_interp_step h n σ1 σ2 Θ1 Θ2 κs1 κs2 :
    (history_interp h n σ1 Θ1 κs1)
    ⊢ (state_interp σ1 Θ1 κs1) ∗
    (state_interp σ2 Θ2 κs2 ==∗ history_interp (h ++ [(σ2, Θ2, κs2)]) (S n) σ2 Θ2 κs2).
  Proof.
    rewrite /history_interp -!lock. iIntros "(%& Ha& $)". iIntros "SI".
    iMod (hG_history_auth_app _ [(σ2, Θ2, κs2)] with "Ha") as "Ha". iFrame. iPureIntro.
    destruct H. rewrite length_app H last_app. simpl. split; auto. lia.
  Qed.

  Lemma history_interp_event_pred_any n σ Θ κs π h n' σ' Θ' κs' :
    (h !! n = Some (σ, Θ, κs)) →
    (state_sat σ Θ π) →
    history_interp h n' σ' Θ' κs' ⊢ event_pred n σ Θ κs π.
  Proof.
    rewrite /history_interp -lock event_pred_unseal /event_pred_def.
    iIntros (LU Sat) "(%& Ha& SI)". destruct H. iPoseProof (hG_history_event _ _ _ LU with "Ha") as "#He".
    iFrame "He". auto.
  Qed.

  Lemma history_interp_event_pred_now π h n σ Θ κs :
    (state_sat σ Θ π) →
    history_interp h n σ Θ κs ⊢ event_pred n σ Θ κs π.
  Proof.
    iIntros (Sat) "HI". iPoseProof (history_interp_lookup with "HI") as "%".
    iApply (history_interp_event_pred_any with "HI"); eauto.
  Qed.

  Lemma event_pred_history_interp_lookup n σ Θ κs π h n' σ' Θ' κs' :
    history_interp h n' σ' Θ' κs' ∗ event_pred n σ Θ κs π ⊢ ⌜ h !! n = Some (σ, Θ, κs) ∧ state_sat σ Θ π ⌝.
  Proof.
    rewrite /history_interp -lock event_pred_unseal /event_pred_def. iIntros "((%& Ha& SI)& (#He& %))".
    destruct H. iPoseProof (hG_event_history_lookup with "[$Ha $He]") as "%". eauto.
  Qed.

End hist.

(* Allocation of a history interpretation. *)
Lemma history_interp_init `{SI : indexT} `{SIC : !state_interp_class Λ Σ}
  `{HIST : !histGS Σ ((state Λ) * (thread_pool Λ) * (list (observation Λ)))}
  σ Θ κs :
  state_interp σ Θ κs
  ⊢ |==> ∃ _ : histGS Σ ((state Λ) * (thread_pool Λ) * (list (observation Λ))), history_interp [(σ, Θ, κs)] 0 σ Θ κs.
Proof.
  iIntros "SI".
  iMod (own_alloc (●ML ([(σ, Θ, κs)] : list (leibnizO _)) : mono_listUR (leibnizO _))) as (γH) "HH";
    first by apply mono_list_auth_valid.
  iModIntro; iExists (HistG SI _ _ _ γH).
  rewrite /history_interp -lock hG_history_auth_unseal /hG_history_auth_def. iFrame.
  iPureIntro. simpl. done.
Qed.
