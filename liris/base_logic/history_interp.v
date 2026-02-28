From iris.algebra Require Import mono_list.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.

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
Class state_interp_class `{SI : indexT} (Σ : gFunctors) (St Π : Type) :=
  { state_interp : St → gset positive → iProp Σ;
    state_pred : Π → iProp Σ;
    state_sat : St → Π → Prop;
    state_interp_wf :
    (∀ (σ : St) Θ (π : Π), (state_interp σ Θ ∗ state_pred π) ⊢ ⌜ state_sat σ π ⌝);
  }.

Local Definition event_pred_def `{SI : indexT} `{@histGS SI Σ St} `{@state_interp_class SI Σ St Π}
  (n : nat) (π : Π) : iProp Σ :=
  (∃ (e : St), hG_event n e ∗ ⌜ state_sat e π ⌝)%I.
Local Definition event_pred_aux : seal (@event_pred_def). Proof. by eexists. Qed.
Definition event_pred := event_pred_aux.(unseal).
Local Definition event_pred_unseal :
  @event_pred = @event_pred_def := event_pred_aux.(seal_eq).
Global Arguments event_pred {SI Σ St _ Π _}.

Definition history_interp `{SI : indexT} `{@histGS SI Σ St} `{@state_interp_class SI Σ St Π}
  (h : list St) (n : nat) (σ : St) (Θ : gset positive) : iProp Σ :=
  locked (⌜ length h = (S n) ∧ last h = Some σ ⌝ ∗ hG_history_auth h ∗ state_interp σ Θ)%I.
Global Typeclasses Opaque history_interp.
Global Instance: Params (@history_interp) 6 := {}.

(** Properties *)
Section hist.
  Context `{SI : indexT} `{HIST : !histGS Σ St} `{SIC : !state_interp_class Σ St Π}.

  Global Instance event_pred_persistent n π : Persistent (event_pred n π).
  Proof. rewrite event_pred_unseal /event_pred_def. apply _. Qed.
  Global Instance event_pred_timeless n π : Timeless (event_pred n π).
  Proof. rewrite event_pred_unseal /event_pred_def. apply _. Qed.

  Lemma history_interp_wf h n σ Θ :
    history_interp h n σ Θ ⊢ ⌜ length h = (S n) ∧ last h = Some σ ⌝.
  Proof. rewrite /history_interp -lock. iIntros "[$ _]". Qed.

  Lemma history_interp_lookup h n σ Θ :
    history_interp h n σ Θ ⊢ ⌜ h !! n = Some σ ⌝.
  Proof.
    iIntros "HI". iPoseProof (history_interp_wf with "HI") as "%". destruct H.
    rewrite last_lookup H in H0. auto.
  Qed.

  Lemma history_interp_step h n σ1 σ2 Θ1 Θ2 :
    (history_interp h n σ1 Θ1)
    ⊢ (state_interp σ1 Θ1) ∗
    (state_interp σ2 Θ2 ==∗ history_interp (h ++ [σ2]) (S n) σ2 Θ2).
  Proof.
    rewrite /history_interp -!lock. iIntros "(%& Ha& $)". iIntros "SI".
    iMod (hG_history_auth_app _ [σ2] with "Ha") as "Ha". iFrame. iPureIntro.
    destruct H. rewrite length_app H last_app. simpl. split; auto. lia.
  Qed.

  Lemma history_interp_event_pred_any m e π h n σ Θ :
    (h !! m = Some e) →
    (state_sat e π) →
    history_interp h n σ Θ ⊢ event_pred m π.
  Proof.
    rewrite /history_interp -lock event_pred_unseal /event_pred_def. iIntros (LU Sat) "(%& Ha& SI)".
    destruct H. iPoseProof (hG_history_event _ _ _ LU with "Ha") as "#He".
    iFrame "He". auto.
  Qed.

  Lemma history_interp_event_pred_now π h n σ Θ :
    (state_sat σ π) →
    history_interp h n σ Θ ⊢ event_pred n π.
  Proof.
    iIntros (Sat) "HI". iPoseProof (history_interp_lookup with "HI") as "%".
    iApply (history_interp_event_pred_any with "HI"); eauto.
  Qed.

  Lemma event_pred_history_interp_lookup h n σ Θ m π :
    history_interp h n σ Θ ∗ event_pred m π ⊢ ∃ e, ⌜ h !! m = Some e ∧ state_sat e π ⌝.
  Proof.
    rewrite /history_interp -lock event_pred_unseal /event_pred_def. iIntros "((%& Ha& SI)& (%& #He& %))".
    destruct H. iPoseProof (hG_event_history_lookup with "[$Ha $He]") as "%". eauto.
  Qed.

End hist.

(* Allocation of a history interpretation. *)
Lemma history_interp_init `{SI : indexT} `{HIST : !histGS Σ St} `{SIC : !state_interp_class Σ St Π}
  σ Θ :
  state_interp σ Θ ⊢ |==> ∃ _ : histGS Σ St, history_interp [σ] 0 σ Θ.
Proof.
  iIntros "SI".
  iMod (own_alloc (●ML ([σ] : list (leibnizO _)) : mono_listUR (leibnizO St))) as (γH) "HH";
    first by apply mono_list_auth_valid.
  iModIntro; iExists (HistG SI _ St _ γH).
  rewrite /history_interp -lock hG_history_auth_unseal /hG_history_auth_def. iFrame.
  iPureIntro. simpl. done.
Qed.
