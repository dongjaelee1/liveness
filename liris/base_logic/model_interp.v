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
        mhistGpreS_hist : inG Σ (mono_listUR (prod nat obligations));
      }.

  Class mhistGS `{SI : indexT} (Σ : gFunctors) : Set :=
    MhistG {
        mhist_inG : mhistGpreS Σ;
        hist_name : gname;
      }.

  Definition mhistΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (mono_listUR (prod nat obligations))
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
  (h : list (nat * obligations)) : iProp Σ :=
  (own hist_name (●ML h))%I.
Local Definition mhG_history_auth_aux : seal (@mhG_history_auth_def). Proof. by eexists. Qed.
Definition mhG_history_auth := mhG_history_auth_aux.(unseal).
Local Definition mhG_history_auth_unseal :
  @mhG_history_auth = @mhG_history_auth_def := mhG_history_auth_aux.(seal_eq).
Global Arguments mhG_history_auth {SI Σ _}.

Local Definition mhG_event_def `{SI : indexT} `{@mhistGS SI Σ}
  (i n : nat) (e : obligations)  : iProp Σ :=
  (∃ (h : list (nat * obligations)), (⌜ length h = (S i) ∧ last h = Some (n, e) ⌝) ∧ own hist_name (◯ML h))%I.
Local Definition mhG_event_aux : seal (@mhG_event_def). Proof. by eexists. Qed.
Definition mhG_event := mhG_event_aux.(unseal).
Local Definition mhG_event_unseal :
  @mhG_event = @mhG_event_def := mhG_event_aux.(seal_eq).
Global Arguments mhG_event {SI Σ _}.

(** Properties *)
Section proof.
  Context `{SI : indexT} `{HIST : !mhistGS Σ}.

  Global Instance mhG_history_auth_timeless h : Timeless (mhG_history_auth h).
  Proof. rewrite mhG_history_auth_unseal /mhG_history_auth_def. apply _. Qed.

  Global Instance mhG_event_persistent i n e : Persistent (mhG_event i n e).
  Proof. rewrite mhG_event_unseal /mhG_event_def. apply _. Qed.
  Global Instance mhG_event_timeless i n e : Timeless (mhG_event i n e).
  Proof. rewrite mhG_event_unseal /mhG_event_def. apply _. Qed.

  Lemma mhG_history_auth_app h1 h2 :
    mhG_history_auth h1 ⊢ |==> mhG_history_auth (h1 ++ h2).
  Proof.
    rewrite mhG_history_auth_unseal /mhG_history_auth_def.
    apply own_update, mono_list_update. exists h2. auto.
  Qed.

  Lemma mhG_history_event h i e :
    (h !! i = Some e) →
    mhG_history_auth h ⊢ mhG_event i e.1 e.2.
  Proof.
    rewrite mhG_history_auth_unseal /mhG_history_auth_def. rewrite mhG_event_unseal /mhG_event_def.
    iIntros (LU) "H". apply list_elem_of_split_length in LU. destruct LU as (l1&l2&?&?).
    iExists (l1 ++ [e]). iSplit.
    { iPureIntro. subst. rewrite length_app last_app. simpl. destruct e. split; auto. lia. }
    rewrite mono_list_auth_lb_op. iDestruct "H" as "[_ H]".
    rewrite -(mono_list_lb_op_r _ h).
    { iDestruct "H" as "[_ $]". }
    exists l2. subst. rewrite cons_middle app_assoc. auto.
  Qed.

  Lemma mhG_event_history_lookup h i n e :
    mhG_history_auth h ∗ mhG_event i n e ⊢ ⌜ h !! i = Some (n, e) ⌝.
  Proof.
    rewrite mhG_history_auth_unseal /mhG_history_auth_def. rewrite mhG_event_unseal /mhG_event_def.
    iIntros "(H& (%&%& E))". iCombine "H E" gives %V. apply mono_list_both_valid in V. destruct V.
    apply leibniz_equiv in H0. destruct H. subst. iPureIntro.
    rewrite last_lookup H in H1. simpl in H1. rewrite lookup_app_l; auto. rewrite H. lia.
  Qed.

End proof.

Definition model_history_wf (h : list (nat * obligations)) : Prop :=
  ∀ i (e1 e2 : nat * obligations),
  (h !! i = Some e1) → (h !! (S i) = Some e2) →
  (e1.1 ≤ e2.1 ∧ obls_advance e1.2 e2.2).

Definition model_history_interp `{SI : indexT} `{@mhistGS SI Σ}
  (h : list (prod nat obligations)) (i n : nat) (Ω : obligations) : iProp Σ :=
  locked (⌜ model_history_wf h ∧ length h = (S i) ∧ last h = Some (n, Ω) ⌝ ∗ mhG_history_auth h)%I.
Global Typeclasses Opaque model_history_interp.
Global Instance: Params (@model_history_interp) 3 := {}.

(* Turn Until into a persistent predicate. *)
Local Definition event_alive_def `{SI : indexT} `{@mhistGS SI Σ}
  (i n : nat) (k : oid) : iProp Σ :=
  (∃ e, mhG_event i n e ∗ ⌜ ∃ o, (e !! k = Some o) ∧ o ≠ obligation_expired ⌝)%I.
Local Definition event_alive_aux : seal (@event_alive_def). Proof. by eexists. Qed.
Definition event_alive := event_alive_aux.(unseal).
Local Definition event_alive_unseal :
  @event_alive = @event_alive_def := event_alive_aux.(seal_eq).
Global Arguments event_alive {SI Σ _}.

(* Use to turn state predicates at the moment of fulfill into persistent predicates. *)
Local Definition event_fulfilled_def `{SI : indexT} `{@mhistGS SI Σ}
  (i n : nat) (k : oid) : iProp Σ :=
  (∃ e, mhG_event i n e ∗ ⌜ e !! k = Some obligation_fulfilled ⌝)%I.
Local Definition event_fulfilled_aux : seal (@event_fulfilled_def). Proof. by eexists. Qed.
Definition event_fulfilled := event_fulfilled_aux.(unseal).
Local Definition event_fulfilled_unseal :
  @event_fulfilled = @event_fulfilled_def := event_fulfilled_aux.(seal_eq).
Global Arguments event_fulfilled {SI Σ _}.

(** Properties *)
Section hist.
  Context `{SI : indexT} `{HIST : !mhistGS Σ}.

  Global Instance model_history_interp_timeless h i n Ω : Timeless (model_history_interp h i n Ω).
  Proof. rewrite /model_history_interp -lock. apply _. Qed.

  Global Instance event_alive_persistent i n k : Persistent (event_alive i n k).
  Proof. rewrite event_alive_unseal /event_alive_def. apply _. Qed.
  Global Instance event_alive_timeless i n k : Timeless (event_alive i n k).
  Proof. rewrite event_alive_unseal /event_alive_def. apply _. Qed.

  Global Instance event_fulfilled_persistent i n k : Persistent (event_fulfilled i n k).
  Proof. rewrite event_fulfilled_unseal /event_fulfilled_def. apply _. Qed.
  Global Instance event_fulfilled_timeless i n k : Timeless (event_fulfilled i n k).
  Proof. rewrite event_fulfilled_unseal /event_fulfilled_def. apply _. Qed.

  TODO
  Lemma history_interp_wf h n σ Θ :
    history_interp h n σ Θ ⊢ ⌜ length h = (S n) ∧ last h = Some (σ, Θ) ⌝.
  Proof. rewrite /history_interp -lock. iIntros "[$ _]". Qed.

  Lemma history_interp_lookup h n σ Θ :
    history_interp h n σ Θ ⊢ ⌜ h !! n = Some (σ, Θ) ⌝.
  Proof.
    iIntros "HI". iPoseProof (history_interp_wf with "HI") as "%". destruct H.
    rewrite last_lookup H in H0. auto.
  Qed.

  Lemma history_interp_step h n σ1 σ2 Θ1 Θ2 :
    (history_interp h n σ1 Θ1)
    ⊢ (state_interp σ1 Θ1) ∗
    (state_interp σ2 Θ2 ==∗ history_interp (h ++ [(σ2, Θ2)]) (S n) σ2 Θ2).
  Proof.
    rewrite /history_interp -!lock. iIntros "(%& Ha& $)". iIntros "SI".
    iMod (hG_history_auth_app _ [(σ2, Θ2)] with "Ha") as "Ha". iFrame. iPureIntro.
    destruct H. rewrite length_app H last_app. simpl. split; auto. lia.
  Qed.

  Lemma history_interp_event_pred_any m e π h n σ Θ :
    (h !! m = Some e) →
    (state_sat e.1 e.2 π) →
    history_interp h n σ Θ ⊢ event_pred m π.
  Proof.
    rewrite /history_interp -lock event_pred_unseal /event_pred_def. iIntros (LU Sat) "(%& Ha& SI)".
    destruct H. iPoseProof (hG_history_event _ _ _ LU with "Ha") as "#He".
    iFrame "He". auto.
  Qed.

  Lemma history_interp_event_pred_now π h n σ Θ :
    (state_sat σ Θ π) →
    history_interp h n σ Θ ⊢ event_pred n π.
  Proof.
    iIntros (Sat) "HI". iPoseProof (history_interp_lookup with "HI") as "%".
    iApply (history_interp_event_pred_any with "HI"); eauto.
  Qed.

  Lemma event_pred_history_interp_lookup h n σ Θ m π :
    history_interp h n σ Θ ∗ event_pred m π ⊢ ∃ e, ⌜ h !! m = Some e ∧ state_sat e.1 e.2 π ⌝.
  Proof.
    rewrite /history_interp -lock event_pred_unseal /event_pred_def. iIntros "((%& Ha& SI)& (%& #He& %))".
    destruct H. iPoseProof (hG_event_history_lookup with "[$Ha $He]") as "%". eauto.
  Qed.

End hist.

(* Allocation of a history interpretation. *)
Lemma history_interp_init `{SI : indexT} `{HIST : !histGS Σ (prod St (gset positive))} `{SIC : !state_interp_class Σ St Π}
  σ Θ :
  state_interp σ Θ ⊢ |==> ∃ _ : histGS Σ (prod St (gset positive)), history_interp [(σ, Θ)] 0 σ Θ.
Proof.
  iIntros "SI".
  iMod (own_alloc (●ML ([(σ, Θ)] : list (leibnizO _)) : mono_listUR (leibnizO _))) as (γH) "HH";
    first by apply mono_list_auth_valid.
  iModIntro; iExists (HistG SI _ (prod St (gset positive)) _ γH).
  rewrite /history_interp -lock hG_history_auth_unseal /hG_history_auth_def. iFrame.
  iPureIntro. simpl. done.
Qed.
