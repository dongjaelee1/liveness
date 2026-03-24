From iris.algebra Require Import mono_list.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.base_logic Require Export obligation.

Canonical Structure oblO `{SI : indexT} `{OC : obl_class} := leibnizO obl.

(** The ghost state for model history. *)
Module mhistGS.

  Class mhistGpreS `{SI : indexT} (Σ : gFunctors) `{OC : obl_class} : Set :=
    MhistGpreS {
        mhistGpreS_hist : inG Σ (mono_listUR (prod nat obls));
      }.

  Class mhistGS `{SI : indexT} (Σ : gFunctors) `{OC : obl_class} : Set :=
    MhistG {
        mhist_inG : mhistGpreS Σ;
        hist_name : gname;
      }.

  Definition mhistΣ `{SI : indexT} `{OC : obl_class} : gFunctors :=
    #[GFunctor (mono_listUR (prod nat obls))
      ].

  Global Instance subG_mhistΣ `{SI : indexT} {Σ} `{OC : obl_class} : subG (mhistΣ) Σ → (mhistGpreS Σ).
  Proof. solve_inG. Qed.

End mhistGS.
Import mhistGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances mhist_inG mhistGpreS_hist.

Definition event_le `{OC : obl_class} : (nat * obls) → (nat * obls) → Prop :=
  λ e1 e2, (e1.1 ≤ e2.1 ∧ obls_le e1.2 e2.2).

Definition model_history_wf `{OC : obl_class} (h : list (nat * obls)) : Prop :=
  ∀ i (e1 e2 : nat * obls),
  (h !! i = Some e1) → (h !! (S i) = Some e2) → event_le e1 e2.

(** Properties of wf. *)
Section proof.
  Context `{OC : obl_class}.

  Global Instance event_le_reflexive : Reflexive event_le.
  Proof. repeat intro. destruct x; done. Qed.
  Global Instance event_le_transitive : Transitive event_le.
  Proof. repeat intro. destruct x, y, z, H, H0. split; etrans; eauto. Qed.

  Lemma model_history_wf_lookup_1 h i j e1 e2 :
    model_history_wf h → h !! i = Some e1 → h !! j = Some e2 → i ≤ j → event_le e1 e2.
  Proof.
    revert i j e1 e2. induction h; intros. 1: done.
    destruct i, j; simpl in *.
    - inv H1. done.
    - inv H1. pose proof H. destruct (h !! 0) eqn:LU1.
      + specialize (H0 0 e1 p). etrans; first eapply H0; eauto.
        eapply (IHh 0 j); auto. 2: lia. repeat intro. eapply (H (S i)); simpl; auto.
      + apply lookup_ge_None in LU1. apply lookup_lt_Some in H4. lia.
    - inv H2.
    - eapply (IHh i j); eauto. 2: lia. repeat intro. eapply (H (S i0)); simpl; auto.
  Qed.

  Lemma model_history_wf_cons e h :
    model_history_wf (e :: h) ↔ (model_history_wf h ∧ ∀ i a, (h !! i = Some a) → event_le e a).
  Proof.
    split; intros.
    - split.
      + repeat intro. specialize (H (S i) e1 e2). apply H; simpl; auto.
      + intros. eapply (model_history_wf_lookup_1 _ 0 (S i) _ _ H); auto. lia.
    - destruct H. repeat intro. destruct i; simpl in *.
      + inv H1. eauto.
      + eapply H; eauto.
  Qed.

  Lemma model_history_wf_app h1 h2 :
    (model_history_wf h1 ∧ model_history_wf h2 ∧ (∀ i e a, h1 !! i = Some e → head h2 = Some a → event_le e a))
    ↔ model_history_wf (h1 ++ h2).
  Proof.
    rewrite head_lookup. split; intros.
    - destruct H as (?&?&?). repeat intro. apply lookup_app_Some in H2, H3. destruct H2, H3; eauto.
      + destruct H3. destruct (h2 !! 0) eqn:LU2.
        * etrans; first (eapply H1; eauto). eapply model_history_wf_lookup_1. 2,3: eauto. 1: auto. 1: lia.
        * apply lookup_ge_None in LU2. apply lookup_lt_Some in H4. lia.
      + destruct H2. apply lookup_lt_Some in H3. lia.
      + destruct H2, H3. eapply model_history_wf_lookup_1. 2,3: eauto. 1: auto. 1: lia.
    - split_and !.
      + repeat intro. eapply (H i); rewrite lookup_app; [by rewrite H0 | by rewrite H1].
      + repeat intro.
        assert (h1 !! (length h1 + i) = None).
        { apply lookup_ge_None. lia. }
        assert (h1 !! S (length h1 + i) = None).
        { apply lookup_ge_None. lia. }
        eapply (H (length h1 + i)); rewrite lookup_app; [rewrite H2 | rewrite H3].
        * replace (length h1 + i - length h1) with i by lia. auto.
        * replace (S (length h1 + i) - length h1) with (S i) by lia. auto.
      + intros. eapply (model_history_wf_lookup_1 _ i (length h1) e a H).
        * rewrite lookup_app H0. auto.
        * rewrite lookup_app. rewrite lookup_ge_None_2; auto. replace (length h1 - length h1) with 0 by lia. auto.
        * apply lookup_lt_Some in H0. lia.
  Qed.

  Lemma model_history_wf_lookup_2 h i j e1 e2 :
    model_history_wf h → h !! i = Some e1 → h !! j = Some e2 → event_le e1 e2 →
    (i ≤ j ∨ (e1.1 = e2.1 ∧ obls_keep e1.2 e2.2)).
  Proof.
    revert i j e1 e2. induction h; intros. 1: done.
    destruct i, j; simpl in *; auto. 1: lia.
    - right. inv H1. apply model_history_wf_cons in H. destruct H. apply H1 in H0.
      destruct H0, H2. destruct e1, e2. split; first lia. apply obls_le_antisymmetric; eauto.
    - apply model_history_wf_cons in H. destruct H.
      pose proof (IHh _ _ _ _ H H0 H1 H2). destruct H4; eauto. left. lia.
  Qed.

End proof.

Local Definition mhG_history_auth_def `{SI : indexT} `{OC : obl_class} `{@mhistGS SI Σ OC}
  (h : list (nat * obls)) : iProp Σ :=
  (⌜ model_history_wf h ⌝ ∗ own hist_name (●ML h))%I.
Local Definition mhG_history_auth_aux : seal (@mhG_history_auth_def). Proof. by eexists. Qed.
Definition mhG_history_auth := mhG_history_auth_aux.(unseal).
Local Definition mhG_history_auth_unseal :
  @mhG_history_auth = @mhG_history_auth_def := mhG_history_auth_aux.(seal_eq).
Global Arguments mhG_history_auth {SI OC Σ _}.

Local Definition mhG_event_def `{SI : indexT} `{OC : obl_class} `{@mhistGS SI Σ OC}
  (i : nat) (e : nat * obls)  : iProp Σ :=
  (∃ (h : list (nat * obls)),
      (⌜ length h = (S i) ∧ last h = Some e ∧ model_history_wf h ⌝) ∧ own hist_name (◯ML h))%I.
Local Definition mhG_event_aux : seal (@mhG_event_def). Proof. by eexists. Qed.
Definition mhG_event := mhG_event_aux.(unseal).
Local Definition mhG_event_unseal :
  @mhG_event = @mhG_event_def := mhG_event_aux.(seal_eq).
Global Arguments mhG_event {SI OC Σ _}.

(** Properties *)
Section proof.
  Context `{SI : indexT} `{OC : obl_class} `{HIST : !mhistGS Σ}.

  Global Instance mhG_history_auth_timeless h : Timeless (mhG_history_auth h).
  Proof. rewrite mhG_history_auth_unseal /mhG_history_auth_def. apply _. Qed.

  Global Instance mhG_event_persistent i e : Persistent (mhG_event i e).
  Proof. rewrite mhG_event_unseal /mhG_event_def. apply _. Qed.
  Global Instance mhG_event_timeless i e : Timeless (mhG_event i e).
  Proof. rewrite mhG_event_unseal /mhG_event_def. apply _. Qed.

  Lemma mhG_history_auth_wf h :
    mhG_history_auth h ⊢ ⌜ model_history_wf h ⌝.
  Proof. rewrite mhG_history_auth_unseal /mhG_history_auth_def. iIntros "[$ _]". Qed.

  Lemma mhG_history_auth_app h1 h2 :
    (model_history_wf h2) →
    (∀ i e a, h1 !! i = Some e → head h2 = Some a → event_le e a) →
    mhG_history_auth h1 ⊢ |==> mhG_history_auth (h1 ++ h2).
  Proof.
    iIntros (MHw Head). rewrite mhG_history_auth_unseal /mhG_history_auth_def.
    iIntros "[% H]". iSplitR.
    { iPureIntro. apply model_history_wf_app. split_and !; auto. }
    iStopProof. apply own_update, mono_list_update. exists h2. auto.
  Qed.

  Lemma mhG_history_event h i e :
    (h !! i = Some e) →
    mhG_history_auth h ⊢ mhG_event i e.
  Proof.
    rewrite mhG_history_auth_unseal /mhG_history_auth_def. rewrite mhG_event_unseal /mhG_event_def.
    iIntros (LU) "[% H]". apply list_elem_of_split_length in LU. destruct LU as (l1&l2&?&?).
    iExists (l1 ++ [e]). iSplit.
    { iPureIntro. subst. rewrite length_app last_app. simpl. destruct e. split_and !; auto. 1: lia.
      rewrite cons_middle app_assoc in H. apply model_history_wf_app in H. destruct H as (?&?&?). auto. }
    rewrite mono_list_auth_lb_op. iDestruct "H" as "[_ H]".
    rewrite -(mono_list_lb_op_r _ h).
    { iDestruct "H" as "[_ $]". }
    exists l2. subst. rewrite cons_middle app_assoc. auto.
  Qed.

  Lemma mhG_event_history_lookup h i e :
    mhG_history_auth h ∗ mhG_event i e ⊢ ⌜ h !! i = Some e ⌝.
  Proof.
    rewrite mhG_history_auth_unseal /mhG_history_auth_def. rewrite mhG_event_unseal /mhG_event_def.
    iIntros "((%MHw& H)& (%&%& E))". iCombine "H E" gives %V. apply mono_list_both_valid in V. destruct V.
    apply leibniz_equiv in H0. destruct H as (?&?&?). subst. iPureIntro.
    rewrite last_lookup H in H1. simpl in H1. rewrite lookup_app_l; auto. rewrite H. lia.
  Qed.

  Lemma mhG_event_compare i j e1 e2 :
    i ≤ j →
    mhG_event i e1 ∗ mhG_event j e2 ⊢ ⌜ (e1.1 ≤ e2.1 ∧ obls_le e1.2 e2.2) ⌝.
  Proof.
    rewrite mhG_event_unseal /mhG_event_def.
    iIntros (LE) "((%h1& %& He1)& (%h2& %& He2))".
    iCombine "He1 He2" gives %V. apply mono_list_lb_op_valid_L in V.
    iPureIntro. destruct H as (?&?&?), H0 as (?&?&?). destruct V; cycle 1.
    { destruct H5. subst. destruct x.
      - rewrite app_nil_r in H2, H1, H. rewrite H3 in H1. inv H1. done.
      - rewrite length_app H0 in H. simpl in H. lia. }
    destruct H5. apply (model_history_wf_lookup_1 h2 i j (e1) (e2) H4); auto.
    - subst. rewrite last_lookup H in H1. rewrite lookup_app H1. auto.
    - rewrite last_lookup H0 in H3. done.
  Qed.

End proof.

Definition model_history_interp `{SI : indexT} `{OC : obl_class} `{@mhistGS SI Σ OC}
  (h : list (prod nat obls)) (i n : nat) (Ω : obls) : iProp Σ :=
  locked (⌜ length h = (S i) ∧ last h = Some (n, Ω) ⌝ ∗ mhG_history_auth h)%I.
Global Typeclasses Opaque model_history_interp.
Global Instance: Params (@model_history_interp) 4 := {}.

Local Definition event_obl_def `{SI : indexT} `{OC : obl_class} `{@mhistGS SI Σ OC}
  (i : nat) (e : nat * obls) (k : oid) (o : obl) : iProp Σ :=
  (mhG_event i e ∗ ⌜ e.2 !! k = Some o ⌝)%I.
Local Definition event_obl_aux : seal (@event_obl_def). Proof. by eexists. Qed.
Definition event_obl := event_obl_aux.(unseal).
Local Definition event_obl_unseal :
  @event_obl = @event_obl_def := event_obl_aux.(seal_eq).
Global Arguments event_obl {SI OC Σ _}.

(* We use this to record that Until was alive at this point of execution. *)
Definition event_obl_alive `{SI : indexT} `{OC : obl_class} `{@mhistGS SI Σ OC}
  (i : nat) (e : nat * obls) (k : oid) : iProp Σ :=
  (∃ o, event_obl i e k o ∧ ⌜ obl_le o obl_fulfilled ⌝).

(** Properties *)
Section hist.
  Context `{SI : indexT} `{OC : obl_class} `{HIST : !mhistGS Σ}.

  Global Instance model_history_interp_timeless h i n Ω : Timeless (model_history_interp h i n Ω).
  Proof. rewrite /model_history_interp -lock. apply _. Qed.

  Global Instance event_obl_persistent i n k o : Persistent (event_obl i n k o).
  Proof. rewrite event_obl_unseal /event_obl_def. apply _. Qed.
  Global Instance event_obl_timeless i n k o : Timeless (event_obl i n k o).
  Proof. rewrite event_obl_unseal /event_obl_def. apply _. Qed.

  Lemma model_history_interp_wf h n σ Θ :
    model_history_interp h n σ Θ ⊢ ⌜ model_history_wf h ∧ length h = (S n) ∧ last h = Some (σ, Θ) ⌝.
  Proof.
    rewrite /model_history_interp -lock. iIntros "(%& HA)".
    iPoseProof (mhG_history_auth_wf with "HA") as "%". iPureIntro. destruct H. auto.
  Qed.

  Lemma model_history_interp_lookup h n σ Θ :
    model_history_interp h n σ Θ ⊢ ⌜ h !! n = Some (σ, Θ) ⌝.
  Proof.
    iIntros "HI". iPoseProof (model_history_interp_wf with "HI") as "%".
    destruct H as (?&?&?). rewrite last_lookup H0 in H1. auto.
  Qed.

  Lemma model_history_interp_step h i n1 n2 Ω1 Ω2 :
    n1 ≤ n2 →
    obls_le Ω1 Ω2 →
    (model_history_interp h i n1 Ω1) ⊢ |==> model_history_interp (h ++ [(n2, Ω2)]) (S i) n2 Ω2.
  Proof.
    rewrite /model_history_interp -!lock. iIntros (LEn LEO) "(%& Ha)".
    iPoseProof (mhG_history_auth_wf with "Ha") as "%Hwf". destruct H.
    iMod (mhG_history_auth_app _ [(n2, Ω2)] with "Ha") as "Ha".
    { done. }
    { simpl. intros. inv H1. eapply (model_history_wf_lookup_1 h i0 i e (n1, Ω1)) in Hwf; auto.
      - etrans; eauto. split; auto.
      - rewrite last_lookup H in H0. auto.
      - apply lookup_lt_Some in H4. lia. }
    iFrame. iPureIntro.
    rewrite length_app H last_app. simpl. split; auto. lia.
  Qed.

  Lemma model_history_interp_event_obl_any j e k o h i n Ω :
    (h !! j = Some e) →
    (e.2 !! k = Some o) →
    model_history_interp h i n Ω ⊢ event_obl j e k o.
  Proof.
    rewrite /model_history_interp -lock event_obl_unseal /event_obl_def. iIntros (LU Sat) "(%& Ha)".
    destruct H. iPoseProof (mhG_history_event _ _ _ LU with "Ha") as "#He".
    iFrame "He". auto.
  Qed.

  Lemma model_history_interp_event_obl_now k o h i n Ω :
    (Ω !! k = Some o) →
    model_history_interp h i n Ω ⊢ event_obl i (n, Ω) k o.
  Proof.
    iIntros (Sat) "HI". iPoseProof (model_history_interp_lookup with "HI") as "%".
    iPoseProof (model_history_interp_event_obl_any with "HI") as "#He"; eauto.
  Qed.

  Lemma event_obl_model_history_interp_lookup h i n Ω j e k o :
    model_history_interp h i n Ω ∗ event_obl j e k o
    ⊢ ⌜ h !! j = Some e ∧ e.2 !! k = Some o ∧ (j ≤ i) ∧ (e.1 ≤ n) ∧ (obls_le e.2 Ω) ⌝.
  Proof.
    rewrite /model_history_interp -lock event_obl_unseal /event_obl_def. iIntros "((%& Ha)& (#He& %))".
    destruct H. iPoseProof (mhG_event_history_lookup with "[$Ha $He]") as "%".
    iPoseProof (mhG_history_auth_wf with "Ha") as "%WF".
    rewrite last_lookup H in H1. simpl in H1. assert (j < S i).
    { rewrite -H. apply lookup_lt_is_Some. eauto. }
    unshelve epose proof (model_history_wf_lookup_1 _ _ _ _ _ WF H2 H1 _). 1: lia.
    destruct H4. simpl in *. iPureIntro. split_and !; eauto. lia.
  Qed.

  Lemma event_obl_compare i j e1 e2 k o1 o2 :
    i ≤ j →
    event_obl i e1 k o1 ∗ event_obl j e2 k o2 ⊢ ⌜ (e1.1 ≤ e2.1 ∧ obls_le e1.2 e2.2 ∧ obl_le o1 o2) ⌝.
  Proof.
    rewrite event_obl_unseal /event_obl_def.
    iIntros (LE) "((#He1& %)& (#He2& %))".
    iPoseProof (mhG_event_compare i j with "[$He1 $He2]") as "%"; first auto. destruct H1.
    iPureIntro. split_and !; auto.
    destruct H2. eapply H3; eauto.
  Qed.

End hist.

(* Allocation of a history interpretation. *)
Lemma model_history_interp_init `{SI : indexT} `{OC : obl_class} `{!mhistGpreS Σ} n Ω :
  ⊢ |==> ∃ _ : mhistGS Σ, model_history_interp [(n, Ω)] 0 n Ω.
Proof.
  iMod (own_alloc (●ML ([(n, Ω)]) : mono_listUR (prod nat obls))) as (γH) "HH";
    first by apply mono_list_auth_valid.
  iModIntro; iExists (MhistG SI _ _ _ γH).
  rewrite /model_history_interp -lock mhG_history_auth_unseal /mhG_history_auth_def.
  iFrame. iPureIntro. simpl. done.
Qed.
