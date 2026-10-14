From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export trspec_model fair_scheduling.
From transfinite.stepindex Require Import ordinals.

(** * Temporal guarantees [P ⊨ₜ G]: records, certificates and the one-step property

    Temporal formulas are ordinary iProps; [P ⊨ₜ G] is a persistent iProp saying that whenever
    [P] holds, the rest of the execution satisfies the trace property [G]. Adequacy concludes
    [trSpec_external G].

    At position [n], [P ⊨ₜ G] turns [P] into a record [record G n], which gives the reading of
    [G] at [n] once the step from [n] is made. A record may be written in the pre-step update
    of step [n] (e.g. by discharging an until), so it is eliminated after the step, against
    the bundle of certificates for [n]: each registered structure (temporal_registry.v) has
    its content certified at every position. A record holds for any running system with the
    one-step property [sys_step]; [lWP] is one (adequacy_temporal.v).

    An existential is trace-visible ([trSpec_exist]) only over small types (nat, Z, loc, gname,
    ...), otherwise ghost ([guar_exist_ghost]). The trace property of the adequacy is
    fixed at the meta level: dynamic names reach it through trace-visible existentials.

    The rules are in guarantee_rules.v. *)

(** ** Guarantees *)

Section guarantee.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : trSpec Λ Σ.
  Implicit Types P Q : iProp Σ.

  (** The history [h] is the one of the trace [τf]. *)
  Definition hist_trace (h : list (state Λ * thread_pool Λ * list (observation Λ)))
    (τf : nat → (thread_pool Λ * state Λ) * thread_id * list (observation Λ)) : Prop :=
    ∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → ∃ i', τf n' = ((Θ', σ'), i', κs').

  (** The fairness measure drops across a step, for every obligation assigned before and
      after it. *)
  Definition obls_drop (m m' : thread_id → Ord.t → Ord.t) (Ω Ω' : obls) : Prop :=
    ∀ k fu o fu' o', Ω !! k = Some (obl_assigned fu o) → Ω' !! k = Some (obl_assigned fu' o') →
      (m' o' fu' < m o fu)%ord.

  Local Notation recT := ((trace Λ -d> iPropO Σ) -d> nat -d> iPropO Σ).
  (** A running system: a resource indexed by the position and the configuration. *)
  Local Notation sysT := (nat → state Λ → thread_pool Λ → list (observation Λ) → iProp Σ).

  (** The certificate of a registered item at [n]: a later-guarded record of its content at
      [n]. For an until, the record of its left or right formula at [n], or, if it was
      discharged at [n' ≤ n], the record of its right formula at [n']. *)
  Definition cert_pre (tg : recT) (n : nat) (e : reg_entry) : iProp Σ :=
    match e with
    | RMark => True
    | RAlways _ γ => ∃ f, saved_trI γ f ∗ ▷ tg f n
    | RUntil _ k γP γQ =>
        ∃ fP fQ, saved_trI γP fP ∗ saved_trI γQ fQ ∗
          (▷ (tg fP n ∨ tg fQ n) ∨
           ▷ (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tg fQ n'))
    end.

  (** The bundle for position [n]: a registry prefix ending with the marker of [n] and the
      certificates of its entries. *)
  Definition bundle_pre (tg : recT) (l : list (nat * reg_entry)) (n : nat) : iProp Σ :=
    reg_lb l ∗ ⌜last l = Some (n, RMark)⌝ ∗ [∗ list] pe ∈ l, cert_pre tg n pe.2.

  (** The one-step property of [Sys]: from a consistent system at [n], the bundle for [n]
      (the check), then after the step the system at [S n], the facts about the step and
      later credits. The modalities are those of [trI_always] and [trI_until]. *)
  Definition sys_step_pre (tg : recT) (Sys : sysT) : iProp Σ :=
    □ ∀ (c : nat) h n σ Θ κs g v Ω W τf γ,
      ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_measure γ) Ω W ∧ hist_trace h τf⌝ -∗
      history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
      |={⊤,∅}=> ∃ l, bundle_pre tg l n ∗ ▷ |={∅,⊤}=> |={⊤,∅}=> ALC (|={∅,⊤}=>
        ∃ σ' Θ' κs' g' v' Ω' W' γ',
          ⌜behavior (S n, τf) ∧ beh_fscnt (S n, τf) γ' ∧ owit_inv_lb (fair_measure γ') Ω' W' ∧
           hist_trace (h ++ [(σ', Θ', κs')]) τf ∧ obls_drop (fair_measure γ) (fair_measure γ') Ω Ω'⌝ ∗
          £n c ∗ history_interp (h ++ [(σ', Θ', κs')]) (S n) σ' Θ' κs' ∗
          model_interp g' v' Ω' W' (S n) (dom Θ') ∗ Sys (S n) σ' Θ' κs').

  (** A record for [f] at [n]: for any system satisfying the one-step property, given the
      bundle for [n] and the system at [S n] consistent with the trace, [f] holds at [n] on
      the trace. *)
  Definition record_pre (tg : recT) : recT :=
    λ f n, (□ ∀ (Sys : sysT) l h g v Ω W τf γ σ Θ κs,
      sys_step_pre tg Sys -∗
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_measure γ) Ω W ∧ hist_trace h τf⌝ -∗
      bundle_pre tg l n -∗
      history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
      f (n, τf))%I.

  Local Instance cert_pre_contractive n e : Contractive (λ tg : recT, cert_pre tg n e).
  Proof.
    intros m tg1 tg2 Htg. destruct e; simpl; [done| |].
    - f_equiv=> f. f_equiv. f_contractive. by apply Htg.
    - f_equiv=> fP. f_equiv=> fQ. do 3 f_equiv.
      + f_contractive. f_equiv; by apply Htg.
      + f_contractive. f_equiv=> n'. f_equiv=> i'. f_equiv=> Ω'. do 2 f_equiv. by apply Htg.
  Qed.

  Local Instance bundle_pre_contractive l n : Contractive (λ tg : recT, bundle_pre tg l n).
  Proof.
    intros m tg1 tg2 Htg. rewrite /bundle_pre. do 2 f_equiv.
    apply big_sepL_ne. intros ???. by apply cert_pre_contractive.
  Qed.

  Local Instance sys_step_pre_contractive Sys : Contractive (λ tg : recT, sys_step_pre tg Sys).
  Proof.
    intros m tg1 tg2 Htg. rewrite /sys_step_pre.
    do 31 f_equiv. by apply bundle_pre_contractive.
  Qed.

  Local Instance record_pre_contractive : Contractive record_pre.
  Proof.
    intros m tg1 tg2 Htg f n. rewrite /record_pre. f_equiv. do 12 (f_equiv=> ?).
    f_equiv; first by apply sys_step_pre_contractive.
    do 2 f_equiv. by apply bundle_pre_contractive.
  Qed.

  Definition record_trI : recT := fixpoint record_pre.
  Lemma record_trI_unfold f n : record_trI f n ⊣⊢ record_pre record_trI f n.
  Proof. apply (fixpoint_unfold record_pre). Qed.

  Global Instance record_trI_persistent f n : Persistent (record_trI f n).
  Proof. rewrite record_trI_unfold. apply _. Qed.
  Global Instance record_trI_ne n : NonExpansive (λ f, record_trI f n).
  Proof.
    intros m f1 f2 Hf. rewrite !record_trI_unfold /record_pre. solve_proper.
  Qed.
  Global Instance record_trI_proper n : Proper ((≡) ==> (⊣⊢)) (λ f, record_trI f n).
  Proof. apply ne_proper, _. Qed.
  (** Records of internally equal readings (the agreement of saved readings is internal). *)
  Lemma record_trI_eq (f g : trace Λ -d> iPropO Σ) n : f ≡ g -∗ record_trI f n -∗ record_trI g n.
  Proof. iIntros "Heq H". iApply (internal_eq_rewrite f g (λ f, record_trI f n) with "Heq H"). Qed.

  (** Records of a trace property, the bundle, the certificates and the step property. *)
  Definition record G n : iProp Σ := record_trI (trSpec_internal G) n.
  Definition bundle l n : iProp Σ := bundle_pre record_trI l n.
  Definition cert n e : iProp Σ := cert_pre record_trI n e.
  Definition sys_step (Sys : sysT) : iProp Σ := sys_step_pre record_trI Sys.
  (* Opaque for the proof mode: [iNext] must not strip the laters of the certificates. *)
  Global Typeclasses Opaque bundle cert sys_step.

  (** [P ⊨ₜ G]: whenever [P] holds, the rest of the execution satisfies [G]. *)
  Definition guar P G : iProp Σ :=
    □ ∀ h n σ Θ κs m i Ω W,
      history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ P -∗ record G n.

  Global Instance record_persistent G n : Persistent (record G n).
  Proof. apply _. Qed.
  Global Instance cert_pre_persistent n e : Persistent (cert_pre record_trI n e).
  Proof. destruct e; apply _. Qed.
  Global Instance cert_persistent n e : Persistent (cert n e).
  Proof. rewrite /cert. apply _. Qed.
  Global Instance bundle_persistent l n : Persistent (bundle l n).
  Proof. rewrite /bundle /bundle_pre. apply _. Qed.
  Global Instance sys_step_persistent Sys : Persistent (sys_step Sys).
  Proof. rewrite /sys_step /sys_step_pre. apply _. Qed.
  Global Instance guar_persistent P G : Persistent (guar P G).
  Proof. apply _. Qed.

  Lemma record_trI_intro f n :
    (□ ∀ (Sys : sysT) l h g v Ω W τf γ σ Θ κs,
      sys_step Sys -∗
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_measure γ) Ω W ∧ hist_trace h τf⌝ -∗
      bundle l n -∗
      history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
      f (n, τf)) ⊢ record_trI f n.
  Proof. by rewrite record_trI_unfold. Qed.

  Lemma record_trI_elim f (Sys : sysT) l h n g v Ω W τf γ σ Θ κs :
    record_trI f n -∗
    sys_step Sys -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_measure γ) Ω W ∧ hist_trace h τf⌝ -∗
    bundle l n -∗
    history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
    f (n, τf).
  Proof. rewrite record_trI_unfold. iIntros "#HG #ST H #B W". by iApply ("HG" with "ST H B W"). Qed.

  Lemma record_intro G n :
    (□ ∀ (Sys : sysT) l h g v Ω W τf γ σ Θ κs,
      sys_step Sys -∗
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_measure γ) Ω W ∧ hist_trace h τf⌝ -∗
      bundle l n -∗
      history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
      trSpec_internal G (n, τf)) ⊢ record G n.
  Proof. apply record_trI_intro. Qed.

  Lemma record_elim G (Sys : sysT) l h n g v Ω W τf γ σ Θ κs :
    record G n -∗
    sys_step Sys -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_measure γ) Ω W ∧ hist_trace h τf⌝ -∗
    bundle l n -∗
    history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
    trSpec_internal G (n, τf).
  Proof. apply record_trI_elim. Qed.

  Lemma guar_elim P G h n σ Θ κs m i Ω W :
    guar P G -∗
    history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ P -∗ record G n.
  Proof. iIntros "#HG H". by iApply "HG". Qed.

  (** For the certificates: a later-guarded content gives a later-guarded record. *)
  Lemma guar_elim_later P G h n σ Θ κs m i Ω W :
    guar P G -∗
    ▷ P ∗ history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) -∗ ▷ record G n.
  Proof. iIntros "#HG (HP& HI& MI)". iNext. iApply ("HG" with "[$HI $MI $HP]"). Qed.

  (** The same with a later-guarded guarantee, as stored with a registered structure. *)
  Lemma guar_elim_later_guar P G h n σ Θ κs m i Ω W :
    ▷ guar P G -∗
    ▷ P ∗ history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) -∗ ▷ record G n.
  Proof. iIntros "#HG (HP& HI& MI)". iNext. iApply ("HG" with "[$HI $MI $HP]"). Qed.

  Global Instance guar_ne G : NonExpansive (λ P, guar P G).
  Proof. rewrite /guar. solve_proper. Qed.
  Global Instance guar_proper G : Proper ((≡) ==> (⊣⊢)) (λ P, guar P G).
  Proof. apply ne_proper, _. Qed.
  (* The applied form, for [f_equiv] and [solve_contractive]. *)
  Global Instance guar_proper_ne n : Proper (dist n ==> (=) ==> dist n) guar.
  Proof. intros P P' HP G ? <-. by apply guar_ne. Qed.

  Lemma record_mono G G' n : trSpec_le G G' → record G n ⊢ record G' n.
  Proof.
    iIntros (Hle) "#HG". iApply record_intro. iIntros "!>" (????????????) "#ST %H #B W".
    iApply Hle. by iApply (record_elim with "HG ST [//] B W").
  Qed.

End guarantee.

Notation "P ⊨ₜ G" := (guar P%I G%SPEC) (at level 70, format "P  ⊨ₜ  G") : bi_scope.

(** The canonical trace property of an iProp: the meet of all trace properties that it
    validly guarantees. The registered structures store it for their contents, so temporal
    formulas carry no trace-property annotations. *)
Definition trSpec_canon `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (Q : iProp Σ) : trSpec Λ Σ :=
  trSpec_forall (λ G : {G : trSpec Λ Σ | ⊢ Q ⊨ₜ G}, proj1_sig G).
(* Opaque for the proof mode: unification must not compare two [trSpec_canon] through their
   bodies (the index type is a proposition about the argument). *)
Global Typeclasses Opaque trSpec_canon.
