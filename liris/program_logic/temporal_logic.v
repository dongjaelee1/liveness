From iris.proofmode Require Import base proofmode classes.
From iris.prelude Require Import options.
From liris.program_logic Require Export sfmupd temporal_formula.

(* FIXME: more to somewhere else. *)
Section aux.
  Context `{SI : indexT}.

  Global Instance big_opL_proper_eq {M : ofe} (o : M → M → M) `{!Monoid o} {A : Type} :
    Proper (pointwise_relation nat (pointwise_relation A eq) ==> eq ==> eq) (big_opL o).
  Proof.
    repeat intro. subst y0. revert x y H. rename x0 into l. induction l; intros f1 f2 Hf; simpl; auto.
    f_equal.
    - rewrite Hf. auto.
    - eapply IHl. repeat intro. rewrite Hf. auto.
  Qed.

End aux.

Fixpoint tf_logic `{SI : indexT} `{!state_interp_class Λ Σ Π} `{!ord_mono_fun_class}
  `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))}
  (Φ : @tf SI Σ Π) : iProp Σ :=
  match Φ with
  | tf_emp => emp%I
  | tf_atomic π => (state_pred_interp π)%I
  | tf_pure p => (⌜p⌝)%I
  | tf_ghost p => p%I
  | tf_and P Q => (tf_logic P ∧ tf_logic Q)%I
  | tf_or P Q => (tf_logic P ∨ tf_logic Q)%I
  | tf_impl P Q => (⌜P⌝ → tf_logic Q)%I
  | tf_forall A P => (∀ (a : A), tf_logic (P a))%I
  | tf_exist A P => (∃ (a : A), tf_logic (P a))%I
  | tf_sep P Q => (tf_logic P ∗ tf_logic Q)%I
  | tf_wand P Q => (⌜P⌝ -∗ tf_logic Q)%I
  | tf_pers P => (□ (tf_logic P))%I
  | tf_always N k P =>
      (oblP_expired k ∗
       oblP_inv N k False%I False%I (tf_logic P)%I)%I
  | tf_until N k P Q =>
      (oblP_alive k (1/2)%Qp ∗
       oblP_inv N k (tf_logic P)%I (tf_logic Q)%I (∃ n σ Θ κs i Ω, event_obl i (n, Ω) k obl_fulfilled ∗ tf_intuit n σ Θ κs i Ω Q)%I)%I
  end
with tf_intuit `{SI : indexT} `{!state_interp_class Λ Σ Π} `{!ord_mono_fun_class}
       `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))}
       n σ Θ κs i Ω (Φ : @tf SI Σ Π) : iProp Σ :=
       match Φ with
       | tf_emp => emp%I
       | tf_atomic π => (event_pred n σ Θ κs π)%I
       | tf_pure p => (⌜p⌝)%I
       | tf_ghost p => True%I
       | tf_and P Q => (tf_intuit n σ Θ κs i Ω P ∧ tf_intuit n σ Θ κs i Ω Q)%I
       | tf_or P Q => (tf_intuit n σ Θ κs i Ω P ∨ tf_intuit n σ Θ κs i Ω Q)%I
       | tf_impl P Q => (⌜P⌝ → tf_intuit n σ Θ κs i Ω Q)%I
       | tf_forall A P => (∀ (a : A), tf_intuit n σ Θ κs i Ω (P a))%I
       | tf_exist A P => (∃ (a : A), tf_intuit n σ Θ κs i Ω (P a))%I
       | tf_sep P Q => (tf_intuit n σ Θ κs i Ω P ∗ tf_intuit n σ Θ κs i Ω Q)%I
       | tf_wand P Q => (⌜P⌝ -∗ tf_intuit n σ Θ κs i Ω Q)%I
       | tf_pers P => (□ (tf_logic P))%I
       | tf_always N k P =>
           (oblP_expired k ∗
            oblP_inv N k False%I False%I (tf_logic P)%I)%I
       | tf_until N k P Q =>
           (event_obl_alive i (n, Ω) k ∗
            oblP_inv N k (tf_logic P)%I (tf_logic Q)%I (∃ n σ Θ κs i Ω, event_obl i (n, Ω) k obl_fulfilled ∗ tf_intuit n σ Θ κs i Ω Q)%I)%I
       end.

Global Arguments tf_logic {SI Λ Σ Π _ _ _ _}.
Global Arguments tf_intuit {SI Λ Σ Π _ _ _ _}.

Section proof.
  Context `{SI : indexT} `{SIC : !state_interp_class Λ Σ Π} `{OCM : !ord_mono_fun_class}.
  Context `{!mupdGS Σ} `{!histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))}.

  Global Instance tf_intuit_persistent n σ Θ κs i Ω Φ : Persistent (tf_intuit n σ Θ κs i Ω Φ).
  Proof.
    induction Φ; simpl; apply _.
  Qed.

  Lemma tf_logic_tf_intuit Φ h n σ Θ κs m i Ω W :
    (history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ tf_logic Φ) ⊢ tf_intuit n σ Θ κs i Ω Φ.
  Proof.
    revert h n σ Θ κs m i Ω W. induction Φ; iIntros (?????????) "(HI& MI& TL)"; simpl; auto.
    - rewrite /history_interp -lock. iDestruct "HI" as "(HI1& HI2& SI)".
      iPoseProof (state_interp_wf with "[$SI $TL]") as "%".
      iApply (history_interp_event_pred_now with "[HI1 HI2 SI]"). 1: auto.
      rewrite /history_interp -lock. iFrame.
    - iSplit.
      + iDestruct "TL" as "[TL _]". iApply IHΦ1. iFrame.
      + iDestruct "TL" as "[_ TL]". iApply IHΦ2. iFrame.
    - iDestruct "TL" as "[TL | TL]".
      + iLeft. iApply IHΦ1. iFrame.
      + iRight. iApply IHΦ2. iFrame.
    - iIntros (?). iPoseProof ("TL" with "[//]") as "TL". iApply IHΦ. iFrame.
    - iIntros (?). iPoseProof ("TL" $! a) as "TL". iApply H0. iFrame.
    - iDestruct "TL" as "(%& TL)". iExists a. iApply H0. iFrame.
    - iDestruct "TL" as "[TL1 TL2]".
      iPoseProof (IHΦ1 with "[$HI $MI $TL1]") as "#TI1". iPoseProof (IHΦ2 with "[$HI $MI $TL2]") as "#TI2".
      eauto.
    - iIntros (?). iPoseProof ("TL" with "[//]") as "TL". iApply IHΦ. iFrame.
    - iDestruct "TL" as "[OA #TL]". iFrame "TL". iDestruct "MI" as "(MI& S& MI2)".
      iEval (unfold_opreds) in "OA". iDestruct "OA" as "(#OE& OA)".
      iPoseProof (osat_lookup_alive with "[$S $OE $OA]") as "%". destruct H0 as [(?&?&?) | ?].
      + iPoseProof (model_history_interp_event_obl_now with "MI") as "#ME". 1: eauto.
        rewrite /event_obl_alive. eauto.
      + iPoseProof (model_history_interp_event_obl_now with "MI") as "#ME". 1: eauto.
        rewrite /event_obl_alive. eauto.
  Qed.

End proof.


TODO

(** Interpretation of tf to the full state (program and obligation state) predicate. *)
Fixpoint tf_full_state `{SI : indexT} `{!state_interp_class Σ St Π}
  (Φ : @tf SI Σ Π) (σ : St) (Θ : (gset positive)) (n : nat) (Ω : obls) : Prop :=
  match Φ with
  | tf_emp => True
  | tf_atomic π =>
      (state_sat σ Θ π)
  | tf_pure p => p
  | tf_ghost p => True
  | tf_and P Q => (tf_full_state P σ Θ n Ω ∧ tf_full_state Q σ Θ n Ω)
  | tf_or P Q => (tf_full_state P σ Θ n Ω ∨ tf_full_state Q σ Θ n Ω)
  | tf_impl P Q => (tf_full_state P σ Θ n Ω → tf_full_state Q σ Θ n Ω)
  | tf_forall A P => (∀ (a : A), tf_full_state (P a) σ Θ n Ω)
  | tf_exist A P => (∃ (a : A), tf_full_state (P a) σ Θ n Ω)
  | tf_sep P Q => (tf_full_state P σ Θ n Ω ∧ tf_full_state Q σ Θ n Ω)
  | tf_wand P Q => (tf_full_state P σ Θ n Ω → tf_full_state Q σ Θ n Ω)
  | tf_pers P => (tf_full_state P σ Θ n Ω)
  | tf_always N k P =>
      ((Ω !! k = Some obl_expired) ∧ tf_full_state P σ Θ n Ω)
  | tf_until N k P Q =>
      ((∃ f o, Ω !! k = Some (obl_assigned f o) ∧ tf_full_state P σ Θ n Ω) ∨
         ( Ω !! k = Some obl_fulfilled ∧ tf_full_state Q σ Θ n Ω))
  end.

(* When k fulfills Q, obl_inv k keeps ∃ i n, event_obl i n k obl_fulfilled ∗ tf_intuit n σ Θ κs i Ω Q.
   With this and full history interp, we retrieve the prefix of history-predicate that says Q is fulfilled. *)
(** Interpretation of tf to intuitionistical predicates. *)
Fixpoint tf_intuit `{SI : indexT} `{!mupdGS Σ} `{!histGS.histGS Σ (St * gset positive)} `{!state_interp_class Σ St Π}
  i n (Φ : @tf SI Σ Π) : iProp Σ :=
  match Φ with
  | tf_emp => emp%I
  | tf_atomic π => (event_pred n π)%I
  | tf_pure p => (⌜p⌝)%I
  | tf_ghost p => True%I
  | tf_and P Q => (tf_intuit n σ Θ κs i Ω P ∧ tf_intuit n σ Θ κs i Ω Q)%I
  | tf_or P Q => (tf_intuit n σ Θ κs i Ω P ∨ tf_intuit n σ Θ κs i Ω Q)%I
  | tf_impl P Q => (tf_intuit n σ Θ κs i Ω P → tf_intuit n σ Θ κs i Ω Q)%I
  | tf_forall A P => (∀ (a : A), tf_intuit n σ Θ κs i Ω (P a))%I
  | tf_exist A P => (∃ (a : A), tf_intuit n σ Θ κs i Ω (P a))%I
  | tf_sep P Q => (tf_intuit n σ Θ κs i Ω P ∗ tf_intuit n σ Θ κs i Ω Q)%I
  | tf_wand P Q => (tf_intuit n σ Θ κs i Ω P -∗ tf_intuit n σ Θ κs i Ω Q)%I
  | tf_pers P => (□ (tf_intuit n σ Θ κs i Ω P))%I (** Should just be P if want to use this in logic... *)
  | tf_always N k P =>
      (oblP_expired k ∗ (tf_intuit n σ Θ κs i Ω P))%I (** P should always be P, not like this... *)
  (* (oblP_expired k ∗ oblP_inv N k ⌜ False ⌝ ⌜ False ⌝ (tf_intuit n σ Θ κs i Ω P))%I (** P should always be P, not like this... *) *)
  | tf_until N k P Q =>
      ((∃ f o, event_obl i n k (obl_assigned f o) ∗ tf_intuit n σ Θ κs i Ω P) ∨
         (event_obl i n k (obl_fulfilled) ∗ tf_intuit n σ Θ κs i Ω Q))
        (* ((∃ f o, event_obl i n k (obl_assigned f o) ∗ *)
        (*          oblP_inv N k (tf_intuit n σ Θ κs i Ω P) (∃ j m, tf_intuit j m Q) (∃ j m, event_obl j m k obl_fulfilled ∗ tf_intuit j m Q)) ∨ *)
        (*    (event_obl i n k (obl_fulfilled) ∗ *)
        (*     oblP_inv N k (∃ j m, tf_intuit j m P) (tf_intuit n σ Θ κs i Ω Q) (event_obl i n k obl_fulfilled ∗ tf_intuit n σ Θ κs i Ω Q))) *)
  end.
Global Arguments tf_intuit {SI Σ _ St _ Π _}.

(** (tf_logic P ∗ full_history_interp h i n) -∗ tf_intuit n σ Θ κs i Ω P
    tf_intuit n σ Θ κs i Ω P ∗ full_history_interp h j m → ∃ (e : full state), h !! i = Some e ∧ tf_full_state P e
    h !! i = Some e ∧ tf_full_state P e ∗ ... → tf_trace_might_expired P tr
    Need to prove tf_trace_might_expired P tr first, and use it in the inductive case.
    Namely, tr_trace_might_expired P tr ∧ tf_intuit n σ Θ κs i Ω (where i n are current) → tf_trace P tr.
    Of course, tf_logic P ∗ full_history_interp h i n ⊢ tf_intuit n σ Θ κs i Ω should hold,
    so we get tf_intuit for the current state at the initial state of the program.
 *)

(** Define logical predicates for temporal formula. *)
(* Always P *)
Local Definition tlP_always_def `{SI : indexT} `{@mupdGS SI Σ} N k (P : iProp Σ) : iProp Σ :=
  (oblP_expired k ∗ oblP_inv N k ⌜ False ⌝ ⌜ False ⌝ P)%I.
Local Definition tlP_always_aux : seal (@tlP_always_def). Proof. by eexists. Qed.
Definition tlP_always := tlP_always_aux.(unseal).
Local Definition tlP_always_unseal :
  @tlP_always = @tlP_always_def := tlP_always_aux.(seal_eq).
Global Arguments tlP_always {SI Σ _}.

(* P Until Q *)
Local Definition tlP_until_def `{SI : indexT} `{@mupdGS SI Σ} N k (P Q : iProp Σ) : iProp Σ :=
  (oblP_alive k (1/2)%Qp ∗ oblP_inv N k P Q ⌜ True ⌝)%I.
Local Definition tlP_until_aux : seal (@tlP_until_def). Proof. by eexists. Qed.
Definition tlP_until := tlP_until_aux.(unseal).
Local Definition tlP_until_unseal :
  @tlP_until = @tlP_until_def := tlP_until_aux.(seal_eq).
Global Arguments tlP_until {SI Σ _}.

(* Eventually P *)
Definition tlP_eventually `{SI : indexT} `{@mupdGS SI Σ} N k (P : iProp Σ) : iProp Σ :=
  (tlP_until N k ⌜ True ⌝ P)%I.
Global Arguments tlP_eventually {SI Σ _}.

(* Local Definition tlP_eventually_def `{SI : indexT} `{@mupdGS SI Σ} N k v (P : iProp Σ) : iProp Σ := *)
(*   (tlP_until N k v ⌜ True ⌝ P)%I. *)
(* Local Definition tlP_eventually_aux : seal (@tlP_eventually_def). Proof. by eexists. Qed. *)
(* Definition tlP_eventually := tlP_eventually_aux.(unseal). *)
(* Local Definition tlP_eventually_unseal : *)
(*   @tlP_eventually = @tlP_eventually_def := tlP_eventually_aux.(seal_eq). *)
(* Global Arguments tlP_eventually {SI Σ _}. *)

(* P Weak until Q *)
Local Definition tlP_weakuntil_def `{SI : indexT} `{@mupdGS SI Σ} N k (P Q : iProp Σ) : iProp Σ :=
  (tlP_until N k P (Q ∨ ∃ k', tlP_always N k' P))%I.
Local Definition tlP_weakuntil_aux : seal (@tlP_weakuntil_def). Proof. by eexists. Qed.
Definition tlP_weakuntil := tlP_weakuntil_aux.(unseal).
Local Definition tlP_weakuntil_unseal :
  @tlP_weakuntil = @tlP_weakuntil_def := tlP_weakuntil_aux.(seal_eq).
Global Arguments tlP_weakuntil {SI Σ _}.

(* P Release Q *)
Definition tlP_release `{SI : indexT} `{@mupdGS SI Σ} N k (P Q : iProp Σ) : iProp Σ :=
  (tlP_weakuntil N k Q (Q ∗ P))%I.
Global Arguments tlP_release {SI Σ _}.

(* Local Definition tlP_release_def `{SI : indexT} `{@mupdGS SI Σ} N k v (P Q : iProp Σ) : iProp Σ := *)
(*   (tlP_weakuntil N k v Q (Q ∗ P))%I. *)
(* Local Definition tlP_release_aux : seal (@tlP_release_def). Proof. by eexists. Qed. *)
(* Definition tlP_release := tlP_release_aux.(unseal). *)
(* Local Definition tlP_release_unseal : *)
(*   @tlP_release = @tlP_release_def := tlP_release_aux.(seal_eq). *)
(* Global Arguments tlP_release {SI Σ _}. *)

(* P Strong release Q *)
Definition tlP_strongrelease `{SI : indexT} `{@mupdGS SI Σ} N k (P Q : iProp Σ) : iProp Σ :=
  (tlP_until N k Q (Q ∗ P))%I.
Global Arguments tlP_strongrelease {SI Σ _}.

(* Local Definition tlP_strongrelease_def `{SI : indexT} `{@mupdGS SI Σ} N k v (P Q : iProp Σ) : iProp Σ := *)
(*   (tlP_until N k v Q (Q ∗ P))%I. *)
(* Local Definition tlP_strongrelease_aux : seal (@tlP_strongrelease_def). Proof. by eexists. Qed. *)
(* Definition tlP_strongrelease := tlP_strongrelease_aux.(unseal). *)
(* Local Definition tlP_strongrelease_unseal : *)
(*   @tlP_strongrelease = @tlP_strongrelease_def := tlP_strongrelease_aux.(seal_eq). *)
(* Global Arguments tlP_strongrelease {SI Σ _}. *)

Section proof.
  Context `{SI : indexT} `{!mupdGS Σ}.

  Local Ltac unfold_temps :=
    try rewrite tlP_always_unseal /tlP_always_def;
    try rewrite tlP_until_unseal /tlP_until_def;
    try rewrite /tlP_eventually;
    try rewrite tlP_weakuntil_unseal /tlP_weakuntil_def;
    try rewrite /tlP_release;
    try rewrite /tlP_strongrelease.

  Lemma tlP_always_unfold N k (P : iProp Σ) :
    tlP_always N k P = (oblP_inv N k 0 ⌜ False ⌝ P ⌜ False ⌝)%I.
  Proof. rewrite tlP_always_unseal. done. Qed.
  Lemma tlP_until_unfold N k (P Q : iProp Σ) :
    tlP_until N k P Q = (oblP_inv N k 0 P Q ⌜ True ⌝)%I.
  Proof. rewrite tlP_until_unseal. done. Qed.
  Lemma tlP_eventually_unfold N k (P : iProp Σ) :
    tlP_eventually N k P = (tlP_until N k ⌜ True ⌝ P)%I.
  Proof. done. Qed.
  Lemma tlP_weakuntil_unfold N k (P Q : iProp Σ) :
    tlP_weakuntil N k P Q = (tlP_until N k P (Q ∨ ∃ k', tlP_always N k' P))%I.
  Proof. rewrite tlP_weakuntil_unseal. done. Qed.
  Lemma tlP_release_unfold N k (P Q : iProp Σ) :
    tlP_release N k P Q = (tlP_weakuntil N k Q (Q ∗ P))%I.
  Proof. done. Qed.
  Lemma tlP_strongrelease_unfold N k (P Q : iProp Σ) :
    tlP_strongrelease N k P Q = (tlP_until N k Q (Q ∗ P))%I.
  Proof. done. Qed.

  (** Always *)
  Global Instance tlP_always_persistent N k P : Persistent (tlP_always N k P).
  Proof. unfold_temps. apply _. Qed.
  Global Instance tlP_always_contractive N k : Contractive (tlP_always N k).
  Proof. unfold_temps. apply _. Qed.
  Global Instance tlP_always_ne N k : NonExpansive (tlP_always N k).
  Proof. apply _. Qed.

  Lemma tlP_always_alloc_0 Θ :
    ⊢ |=[Θ]=>g ∃ k, gl k 0 ∗ tlP_current k 0 1 ∗ tlP_done k 0 ∗
                   (∀ E N (P : iProp Σ), (▷ P) ={E}=∗ tlP_always N k P).
  Proof.
    unfold_temps.
    iMod (tlP_alloc_done_0 _ (λ _, 0%ordi) 0%M 0) as "(%& _& $& $& #Gd& _& _& _& H)".
    iModIntro. iFrame "Gd". iIntros (???). iApply "H".
  Qed.

  Lemma tlP_always_acc E N k P :
    ↑N ⊆ E →
    tlP_done k 0 -∗
    tlP_always N k P ={E,E ∖ ↑N}=∗
    (▷ (P)) ∗ ((▷ (P)) ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_temps.
    iIntros (MASK) "#Gd #GV". iMod (oblP_inv_acc with "GV") as "[H ACC]". 1: auto.
    iDestruct "H" as "[[>(_& %) | H] | >(_& %)]"; [done | | done].
    iModIntro. iSplitL "H".
    { iNext. iDestruct "H" as "[_ $]". }
    iIntros "HP". iApply "ACC". iNext. iApply oblP_inv_cases_unfold. iLeft; iRight. eauto.
  Qed.

  (** Until *)
  Global Instance tlP_until_persistent N k P Q : Persistent (tlP_until N k P Q).
  Proof. unfold_temps. apply _. Qed.
  Global Instance tlP_until_contractive_1 N k Q : Contractive (λ P, tlP_until N k P Q).
  Proof. unfold_temps. apply _. Qed.
  Global Instance tlP_until_contractive_2 N k P : Contractive (λ Q, tlP_until N k P Q).
  Proof. unfold_temps. apply _. Qed.
  Global Instance tlP_until_ne_1 N k Q : NonExpansive (λ P, tlP_until N k P Q).
  Proof. apply _. Qed.
  Global Instance tlP_until_ne_2 N k P : NonExpansive (λ Q, tlP_until N k P Q).
  Proof. apply _. Qed.

  Lemma tlP_until_alloc_0 Θ i G q ℓ μ :
    th_obls i G q -∗
    |=[Θ]=>g ∃ k, ⌜G !! k = None⌝ ∗ th_obls i (<[k:=0]> G) q ∗ tlP_current k 0 (1 / 2) ∗ 
                 tlP_layers k (λ _, ℓ) ∗ gl k 0 ∗ tlP_fuel k ℓ μ ∗ wit_layer k 0 ℓ ∗
                 ([∗ set] u ∈ set_seq 0 0, tlP_done k u) ∗
                 ∀ E N (P Q : iProp Σ), ▷ P ={E}=∗ tlP_until N k P Q.
  Proof.
    unfold_temps.
    iIntros "TG". iMod (tlP_alloc_obl_0 _ _ _ _ (λ _, ℓ) μ 0 with "TG") as "(%& $& $& $& $& $& $& $& $& H)".
    iIntros "!> %%%%". iApply "H".
  Qed.

  Lemma tlP_until_done_alloc_0 Θ :
    ⊢ |=[Θ]=>g ∃ k, gl k 0 ∗ tlP_current k 0 1 ∗ tlP_done k 0 ∗
                   (∀ E N (P Q : iProp Σ), ▷ Q ={E}=∗ tlP_until N k P Q).
  Proof.
    unfold_temps.
    iMod (tlP_alloc_done_0 _ (λ _, 0%ordi) 0%M 0) as "(%& _& $& $& $& _& _& _& H)".
    iIntros "!> %%%%". iApply "H".
  Qed.

  Lemma tlP_until_fulfill_0 E i G q N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    tlP_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (th_obls i G q ∗ tlP_locked k 0 ∗ P)) ∗
    (th_obls i G q -∗
     tlP_locked k 0 -∗
     ∀ Θ, |=[Θ]=>g (th_obls i (delete k G) q ∗ tlP_current k 0 (1 / 2) ∗ tlP_done k 0) ∗
                (▷ Q ={E ∖ ↑N,E}=∗ True)).
  Proof.
    unfold_temps.
    iIntros (MASK LU) "TG #GV". iMod (tlP_unlock_0 with "TG GV") as "[$ ACC]". 1,2: auto.
    eauto.
  Qed.

  Lemma tlP_until_retrieve_0 E N k q (P Q : iProp Σ) :
    ↑N ⊆ E →
    tlP_current k 0 q -∗
    tlP_done k 0 -∗
    tlP_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (tlP_current k 0 q ∗ Q)) ∗
    (tlP_current k 0 1 -∗
     ∀ Θ, |=[Θ]=>g (gl k (S 0) ∗ tlP_done k (S 0) ∗ tlP_current k (S 0) 1) ∗
                (∀ E0, |={E0}=> oblP_inv N k (S 0) ⌜ False ⌝ ⌜ True ⌝ ⌜ False ⌝) ∗
                (|={E ∖ ↑N,E}=> True)).
  Proof.
    unfold_temps.
    iIntros (MASK) "Gc #Gd #GV". iMod (tlP_new_version_0 with "Gc Gd GV") as "[$ H]". 1: eauto.
    iIntros "!> Gc %". iPoseProof ("H" with "Gc") as "H". iPoseProof ("H" $! (S 0) with "[]") as "H".
    1: iPureIntro; lia.
    iMod ("H" $! _) as "(($& $& $& _)& A& B)". iModIntro. iSplitL "A".
    - iIntros (?). by iApply "A".
    - by iApply "B".
  Qed.

  Lemma tlP_until_acc_own E i G q N k P Q :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    tlP_until N k P Q ={E,E ∖ ↑N}=∗
    ▷ (th_obls i G q ∗ tlP_locked k 0 ∗ P) ∗
    (▷ oblP_inv_cases k 0 P Q (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_temps.
    iIntros (MASK Lu) "TG #GV". iMod (oblP_inv_acc_own with "TG GV") as "[$ $]". all: auto.
  Qed.

  Lemma tlP_until_acc_current E N k q P Q :
    ↑N ⊆ E →
    tlP_current k 0 q -∗
    tlP_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (tlP_current k 0 q ∗ (tlP_locked k 0 ∗ P ∨ tlP_done k 0 ∗ Q))) ∗
    (▷ oblP_inv_cases k 0 P Q (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_temps.
    iIntros (MASK) "Gc #GV". iMod (oblP_inv_acc_current_timeless with "Gc GV") as "[$ $]". all: auto.
  Qed.

  Lemma tlP_until_acc_current_done E N k q P Q :
    ↑N ⊆ E →
    tlP_current k 0 q -∗
    tlP_done k 0 -∗
    tlP_until N k P Q ={E,E ∖ ↑N}=∗
    (▷ (tlP_current k 0 q ∗ Q)) ∗
    (▷ oblP_inv_cases k 0 P Q (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    unfold_temps.
    iIntros (MASK) "Gc #Gd #GV". iMod (oblP_inv_acc_current_done_timeless with "Gc Gd GV") as "[$ $]". all: auto.
  Qed.

  (** Weak Until *)
  Global Instance tlP_weakuntil_persistent N k P Q : Persistent (tlP_weakuntil N k P Q).
  Proof. unfold_temps. apply _. Qed.
  Global Instance tlP_weakuntil_contractive_1 N k Q : Contractive (λ P, tlP_weakuntil N k P Q).
  Proof.
    (* FIXME: better proof? *)
    unfold_temps. repeat intro. rewrite tlP_until_contractive_1; last eauto.
    apply tlP_until_contractive_2. econstructor. intros. inv H. specialize (dist_later_lt _ H0).
    solve_proper.
  Qed.
  Global Instance tlP_weakuntil_contractive_2 N k P : Contractive (λ Q, tlP_weakuntil N k P Q).
  Proof.
    (* FIXME: better proof? *)
    unfold_temps. repeat intro.
    apply tlP_until_contractive_2. econstructor. intros. inv H. specialize (dist_later_lt _ H0).
    solve_proper.
  Qed.
  Global Instance tlP_weakuntil_ne_1 N k Q : NonExpansive (λ P, tlP_weakuntil N k P Q).
  Proof. apply _. Qed.
  Global Instance tlP_weakuntil_ne_2 N k P : NonExpansive (λ Q, tlP_weakuntil N k P Q).
  Proof. apply _. Qed.

  Lemma tlP_weakuntil_alloc_0 Θ i G q ℓ μ :
    th_obls i G q -∗
    |=[Θ]=>g ∃ k, ⌜G !! k = None⌝ ∗ th_obls i (<[k:=0]> G) q ∗ tlP_current k 0 (1 / 2) ∗ 
                 tlP_layers k (λ _, ℓ) ∗ gl k 0 ∗ tlP_fuel k ℓ μ ∗ wit_layer k 0 ℓ ∗
                 ([∗ set] u ∈ set_seq 0 0, tlP_done k u) ∗
                 (∀ E N (P Q : iProp Σ), ▷ P ={E}=∗ tlP_weakuntil N k P Q).
  Proof.
    unfold_temps.
    iIntros "TG". iMod (tlP_until_alloc_0 _ _ _ _ ℓ μ with "TG") as "(%& $& $& $& $& $& $& $& $& H)".
    iIntros "!> %%%%". iApply "H".
  Qed.

  Lemma tlP_weakuntil_done_alloc_0 Θ :
    ⊢ |=[Θ]=>g ∃ k, gl k 0 ∗ tlP_current k 0 1 ∗ tlP_done k 0 ∗
                   (∀ E N (P Q : iProp Σ), ▷ (Q ∨ ∃ k', tlP_always N k' P) ={E}=∗ tlP_weakuntil N k P Q).
  Proof.
    iMod (tlP_until_done_alloc_0) as "(%& $& $& $& H)".
    iIntros "!> %%%%". rewrite tlP_weakuntil_unfold. iApply "H".
  Qed.

  Lemma tlP_weakuntil_fulfill_0 E i G q N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    tlP_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (th_obls i G q ∗ tlP_locked k 0 ∗ P)) ∗
    (th_obls i G q -∗
     tlP_locked k 0 -∗
     ∀ Θ, |=[Θ]=>g (th_obls i (delete k G) q ∗ tlP_current k 0 (1 / 2) ∗ tlP_done k 0) ∗
                (▷ (Q ∨ ∃ k', tlP_always N k' P) ={E ∖ ↑N,E}=∗ True)).
  Proof.
    rewrite tlP_weakuntil_unfold.
    iIntros (MASK LU) "TG #GV". iMod (tlP_until_fulfill_0 with "TG GV") as "[$ ACC]". 1,2: auto.
    eauto.
  Qed.

  Lemma tlP_weakuntil_retrieve_0 E N k q (P Q : iProp Σ) :
    ↑N ⊆ E →
    tlP_current k 0 q -∗
    tlP_done k 0 -∗
    tlP_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (tlP_current k 0 q ∗ (Q ∨ ∃ k', tlP_always N k' P))) ∗
    (tlP_current k 0 1 -∗
     ∀ Θ, |=[Θ]=>g (gl k (S 0) ∗ tlP_done k (S 0) ∗ tlP_current k (S 0) 1) ∗
                (∀ E0, |={E0}=> oblP_inv N k (S 0) ⌜ False ⌝ ⌜ True ⌝ ⌜ False ⌝) ∗
                (|={E ∖ ↑N,E}=> True)).
  Proof.
    rewrite tlP_weakuntil_unfold.
    iIntros (MASK) "Gc #Gd #GV". iMod (tlP_until_retrieve_0 with "Gc Gd GV") as "[$ H]". 1: eauto.
    eauto.
  Qed.

  Lemma tlP_weakuntil_acc_own E i G q N k P Q :
    ↑N ⊆ E →
    G !! k = Some 0 →
    th_obls i G q -∗
    tlP_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    ▷ (th_obls i G q ∗ tlP_locked k 0 ∗ P) ∗
    (▷ oblP_inv_cases k 0 P (Q ∨ ∃ k', tlP_always N k' P) (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    rewrite tlP_weakuntil_unfold.
    iIntros (MASK Lu) "TG #GV". iMod (tlP_until_acc_own with "TG GV") as "[$ $]". all: auto.
  Qed.

  Lemma tlP_weakuntil_acc_current E N k q P Q :
    ↑N ⊆ E →
    tlP_current k 0 q -∗
    tlP_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (tlP_current k 0 q ∗ (tlP_locked k 0 ∗ P ∨ tlP_done k 0 ∗ (Q ∨ ∃ k', tlP_always N k' P)))) ∗
    (▷ oblP_inv_cases k 0 P (Q ∨ ∃ k', tlP_always N k' P) (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    rewrite tlP_weakuntil_unfold.
    iIntros (MASK) "Gc #GV". iMod (tlP_until_acc_current with "Gc GV") as "[$ $]". all: auto.
  Qed.

  Lemma tlP_weakuntil_acc_current_done E N k q P Q :
    ↑N ⊆ E →
    tlP_current k 0 q -∗
    tlP_done k 0 -∗
    tlP_weakuntil N k P Q ={E,E ∖ ↑N}=∗
    (▷ (tlP_current k 0 q ∗ (Q ∨ ∃ k', tlP_always N k' P))) ∗
    (▷ oblP_inv_cases k 0 P (Q ∨ ∃ k', tlP_always N k' P) (⌜ True ⌝)%I ={E ∖ ↑N,E}=∗ True).
  Proof.
    rewrite tlP_weakuntil_unfold.
    iIntros (MASK) "Gc #Gd #GV". iMod (tlP_until_acc_current_done with "Gc Gd GV") as "[$ $]". all: auto.
  Qed.

End proof.

(** Part 2. Interpretation of tf to iProp. *)
(* Defined by the programming language. *)
Class tf_atomic_interp_logic_class `{SI : indexT} (Σ : gFunctors) (Π : Type) :=
  tfa_atomic_interp_logic : Π → iProp Σ.

(** Interpretation of tf to iProp. *)
Fixpoint tf_interp_logic `{SI : indexT} `{@tf_atomic_interp_logic_class SI Σ Π} `{@mupdGS SI Σ} (Φ : tf) : iProp Σ :=
  match Φ with
  | tf_emp => emp%I
  | tf_atomic π => tfa_atomic_interp_logic π
  | tf_pure p => (⌜p⌝)%I
  | tf_ghost p => p
  | tf_and P Q => (tf_interp_logic P ∧ tf_interp_logic Q)%I
  | tf_or P Q => (tf_interp_logic P ∨ tf_interp_logic Q)%I
  | tf_impl P Q => (tf_interp_logic P → tf_interp_logic Q)%I
  | tf_forall A P => (∀ (a : A), tf_interp_logic (P a))%I
  | tf_exist A P => (∃ (a : A), tf_interp_logic (P a))%I
  | tf_sep P Q => (tf_interp_logic P ∗ tf_interp_logic Q)%I
  | tf_wand P Q => (tf_interp_logic P -∗ tf_interp_logic Q)%I
  | tf_variant N k v P Q R => oblP_inv N k v (tf_interp_logic P) (tf_interp_logic Q) (tf_interp_logic R)
  end.

Global Arguments tf_interp_logic {SI Σ Π _ _}.

(** Notations *)
Notation "'⟦' Φ '⟧ₗ'" := (tf_interp_logic Φ%F).

Section reduction.
  Context `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!mupdGS Σ}.

  Lemma tf_emp_interp_logic :
    ⟦tf_emp⟧ₗ = emp%I.
  Proof. done. Qed.
  Lemma tf_atomic_interp_logic π :
    ⟦tf_atomic π⟧ₗ = tfa_atomic_interp_logic π.
  Proof. done. Qed.
  Lemma tf_pure_interp_logic P :
    ⟦⌜P⌝⟧ₗ = (⌜P⌝)%I.
  Proof. done. Qed.
  Lemma tf_ghost_interp_logic P :
    ⟦⟨P⟩⟧ₗ = (P)%I.
  Proof. done. Qed.
  Lemma tf_and_interp_logic P Q :
    ⟦P ∧ Q⟧ₗ = (⟦P⟧ₗ ∧ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_or_interp_logic P Q :
    ⟦P ∨ Q⟧ₗ = (⟦P⟧ₗ ∨ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_impl_interp_logic P Q :
    ⟦P → Q⟧ₗ = (⟦P⟧ₗ → ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_forall_interp_logic A (P : A → tf) :
    ⟦∀ a, P a⟧ₗ = (∀ a, ⟦P a⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_exist_interp_logic A (P : A → tf) :
    ⟦∃ a, P a⟧ₗ = (∃ a, ⟦P a⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_sep_interp_logic P Q :
    ⟦P ∗ Q⟧ₗ = (⟦P⟧ₗ ∗ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_wand_interp_logic P Q :
    ⟦P -∗ Q⟧ₗ = (⟦P⟧ₗ -∗ ⟦Q⟧ₗ)%I.
  Proof. done. Qed.
  Lemma tf_variant_interp_logic N k v P Q R :
    ⟦tf_variant N k v P Q R⟧ₗ = (oblP_inv N k v ⟦P⟧ₗ ⟦Q⟧ₗ ⟦R⟧ₗ)%I.
  Proof. done. Qed.

  Lemma tf_always_interp_logic N k P :
    ⟦tf_always N k P⟧ₗ = tlP_always N k ⟦P⟧ₗ.
  Proof. rewrite tf_always_unfold tlP_always_unfold. done. Qed.
  Lemma tf_until_interp_logic N k P Q :
    ⟦tf_until N k P Q⟧ₗ = tlP_until N k ⟦P⟧ₗ ⟦Q⟧ₗ.
  Proof. rewrite tf_until_unfold tlP_until_unfold. done. Qed.
  Lemma tf_eventually_interp_logic N k P :
    ⟦tf_eventually N k P⟧ₗ = tlP_eventually N k ⟦P⟧ₗ.
  Proof. rewrite tf_eventually_unfold tlP_eventually_unfold tf_until_interp_logic. done. Qed.
  Lemma tf_weakuntil_interp_logic N k P Q :
    ⟦tf_weakuntil N k P Q⟧ₗ = tlP_weakuntil N k ⟦P⟧ₗ ⟦Q⟧ₗ.
  Proof.
    rewrite tf_weakuntil_unfold tlP_weakuntil_unfold tf_until_interp_logic. simpl.
    rewrite temporal_formula.tf_always_unseal /temporal_formula.tf_always_def.
    rewrite tlP_always_unseal /tlP_always_def. simpl. done.
  Qed.
  Lemma tf_release_interp_logic N k P Q :
    ⟦tf_release N k P Q⟧ₗ = tlP_release N k ⟦P⟧ₗ ⟦Q⟧ₗ.
  Proof. rewrite tf_release_unfold tlP_release_unfold tf_weakuntil_interp_logic. done. Qed.
  Lemma tf_strongrelease_interp_logic N k P Q :
    ⟦tf_strongrelease N k P Q⟧ₗ = tlP_strongrelease N k ⟦P⟧ₗ ⟦Q⟧ₗ.
  Proof. rewrite tf_strongrelease_unfold tlP_strongrelease_unfold tf_until_interp_logic. done. Qed.

End reduction.
(* Making this opaque is reasonable only if we have a better reduction tactic than simpl. *)
(* Global Opaque tf_interp. *)

(** Ofe and Monoid structure. *)
Global Instance tf_equiv `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!mupdGS Σ} : Equiv tf :=
  λ Φ1 Φ2, ⟦Φ1⟧ₗ ≡ ⟦Φ2⟧ₗ.
Global Instance tf_equiv_Equivalence `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!mupdGS Σ} : Equivalence tf_equiv.
Proof.
  unfold tf_equiv. econstructor.
  - repeat intro. done.
  - repeat intro. rewrite H. done.
  - repeat intro. etrans; eauto.
Qed.
Canonical Structure tfO `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!mupdGS Σ} : ofe :=
  (Ofe tf (discrete_ofe_mixin tf_equiv_Equivalence)).

Class tf_op_interp_comm `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{@mupdGS SI Σ}
  (tf_o : tf → tf → tf) (iProp_o : iProp Σ → iProp Σ → iProp Σ) :=
  tf_op_interp_comm_intro : ∀ (P Q : tf), ⟦tf_o P Q⟧ₗ = (iProp_o ⟦P⟧ₗ ⟦Q⟧ₗ)%I.

Class tf_monoid_unit_interp_eq `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!mupdGS Σ}
  (tf_o : tf → tf → tf) `{!Monoid tf_o} (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o} :=
  tf_monoid_unit_interp_eq_intro : ⟦ monoid_unit ⟧ₗ = monoid_unit.

Section instances.
  Context `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!mupdGS Σ}.

  Global Instance tf_and_interp_comm : tf_op_interp_comm tf_and bi_and.
  Proof. econstructor. Qed.
  Global Instance tf_or_interp_comm : tf_op_interp_comm tf_or bi_or.
  Proof. econstructor. Qed.
  Global Instance tf_impl_interp_comm : tf_op_interp_comm tf_impl bi_impl.
  Proof. econstructor. Qed.
  Global Instance tf_sep_interp_comm : tf_op_interp_comm tf_sep bi_sep.
  Proof. econstructor. Qed.
  Global Instance tf_wand_interp_comm : tf_op_interp_comm tf_wand bi_wand.
  Proof. econstructor. Qed.

  Program Global Instance tf_and_monoid : Monoid tf_and := Build_Monoid _ _ _ tf_emp _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_and_interp_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_and_interp_logic tf_emp_interp_logic left_id. done. Qed.

  Program Global Instance tf_or_monoid : Monoid tf_or := Build_Monoid _ _ _ (⌜ False ⌝)%F _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_or_interp_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_or_interp_logic tf_pure_interp_logic left_id. done. Qed.

  Program Global Instance tf_sep_monoid : Monoid tf_sep := Build_Monoid _ _ _ tf_emp _ _ _ _.
  Next Obligation. repeat intro. do 5 red. do 5 red in H, H0. rewrite !tf_sep_interp_logic H H0. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp_logic assoc. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp_logic comm. done. Qed.
  Next Obligation. repeat intro. do 3 red. rewrite !tf_sep_interp_logic tf_emp_interp_logic left_id. done. Qed.

  Global Instance tf_and_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_and bi_and.
  Proof. econstructor. Qed.
  Global Instance tf_or_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_or bi_or.
  Proof. econstructor. Qed.
  Global Instance tf_sep_monoid_unit_interp_eq : tf_monoid_unit_interp_eq tf_sep bi_sep.
  Proof. econstructor. Qed.

End instances.

Section big_op.
  Context `{SI : indexT} `{!tf_atomic_interp_logic_class Σ Π} `{!mupdGS Σ}.

  Lemma tf_big_opL_interp
    (tf_o : tf → tf → tf) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    A (P : nat → A → tf) (l : list A) :
    ⟦[^tf_o list] n ↦ a ∈ l, P n a⟧ₗ = ([^iProp_o list] n ↦ a ∈ l, (⟦P n a⟧ₗ))%I.
  Proof.
    cut (∀ m, ⟦[^tf_o list] n ↦ a ∈ l, P (m + n) a⟧ₗ = ([^iProp_o list] n ↦ a ∈ l, (⟦P (m + n) a⟧ₗ))%I).
    { intros. specialize (H 0). simpl in H. auto. }
    induction l; intros; simpl; auto.
    rewrite (tf_op_interp_comm0). f_equal.
    erewrite (big_opL_proper_eq tf_o).
    - erewrite (IHl (S m)). apply big_opL_proper_eq; auto.
      repeat intro. replace (S m + a0) with (m + S a0) by lia. auto.
    - repeat intro. replace (S m + a0) with (m + S a0) by lia. auto.
    - auto.
  Qed.

  Lemma tf_big_opM_interp
    (tf_o : tf → tf → tf) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    K `{!EqDecision K} `{!Countable K} A
    (P : K → A → tf) (m : gmap K A) :
    ⟦[^tf_o map] k ↦ a ∈ m, P k a⟧ₗ = ([^iProp_o map] k ↦ a ∈ m, (⟦P k a⟧ₗ))%I.
  Proof.
    rewrite !big_op.big_opM_unseal /big_op.big_opM_def.
    erewrite (big_opL_proper_eq tf_o _ (λ n x, P x.1 x.2)); last eauto.
    - erewrite (big_opL_proper_eq iProp_o _ (λ n x, ⟦P x.1 x.2⟧ₗ)); last eauto.
      + eapply tf_big_opL_interp; eauto.
      + repeat intro. unfold uncurry. destruct a0. done.
    - repeat intro. unfold uncurry. destruct a0. done.
  Qed.

  Lemma tf_big_opS_interp
    (tf_o : tf → tf → tf) `{!Monoid tf_o}
    (iProp_o : iProp Σ → iProp Σ → iProp Σ) `{!Monoid iProp_o}
    `{!tf_op_interp_comm tf_o iProp_o}
    `{!tf_monoid_unit_interp_eq tf_o iProp_o}
    A `{!EqDecision A} `{!Countable A}
    (P : A → tf) (s : gset A) :
    ⟦[^tf_o set] a ∈ s, P a⟧ₗ = ([^iProp_o set] a ∈ s, (⟦P a⟧ₗ))%I.
  Proof.
    rewrite !big_op.big_opS_unseal /big_op.big_opS_def.
    erewrite (big_opL_proper_eq tf_o _ (λ n x, P x)); last eauto.
    - erewrite (big_opL_proper_eq iProp_o _ (λ n x, ⟦P x⟧ₗ)); last eauto.
      + eapply tf_big_opL_interp; eauto.
      + done.
    - done.
  Qed.

End big_op.
