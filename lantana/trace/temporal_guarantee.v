From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export temporal_tps.
From transfinite.stepindex Require Import ordinals.

(** * Temporal guarantees

    Temporal formulas are ordinary iProps. What makes an iProp [P] temporal is a separate,
    persistent iProp [P ⊨ₜ G] stating that, whenever [P] holds, the rest of the execution
    satisfies the trace property [G] (temporal_tps.v). Quantifiers are iProp's own (over any
    type, e.g. over iProp), temporal formulas can be stored in invariants and saved
    propositions, and program proofs never leave iProp. Adequacy concludes [tps_tr G], and
    hence any trace predicate it implies.

    Records and certificates. [P ⊨ₜ G] turns [P] at a position [n] of the run into a record
    [tguar G n]: a persistent wand that yields the step-indexed reading of [G] at [n] once
    the run has made the step from [n] to [S n]. A record may be written by a thread in the
    pre-step model update of step [n] (e.g. by discharging an until), so it can only be
    eliminated afterwards, against the system at [S n] and a bundle of certificates for [n]:
    every trace-visible structure ([alwaysI], [untilI]) is registered (temporal_registry.v)
    and, at every position, the content of each registered item is certified as a
    later-guarded record. The step-indexed readings of always and until (adequacy.v) decide
    a position only after the step from it, so that a pre-step discharge at [n] is read off
    the obligation invariant at [S n].

    The running system is abstract in a record: a record is valid for any system that
    satisfies the one-step property [sys_step] (certify the registry, then step fairly, giving
    the bundle of the position, the interpretations after the step and later credits). The
    temporal layer therefore does not depend on the weakest precondition; Lantana's [lWP]
    is one system with the step property ([sys_step_lwp], guarantee_adequacy.v), and the
    state of the registry is the interpretation of the temporal layer that the program logic
    threads ([TemporalInterp], temporal_class.v). Registration is a plain model update.

    Contents: guarantees and records ([tguar]); the registered structures [alwaysI] and
    [untilI]; rules for the connectives; rules for [alwaysI] and [untilI]; the loops that
    read the registered structures off a run; inference of guarantees ([IntoTemporal]);
    examples. The adequacy for [lWP] is in guarantee_adequacy.v.

    Limitations, by design:
    - A quantifier can be trace-visible ([tps_exist]) only over types with the existential
      property of the step index (nat, Z, loc, gname, ...): over larger types (iProp, tps) no
      sound adequacy could read the witness off the trace. Over those, existentials are ghost
      ([temporal_exist_ghost]): the guarantee of the body must not depend on the witness.
    - The trace property [G] of the adequacy is fixed at the meta level; dynamically created
      names reach it through trace-visible existentials, typically under a [finally]
      allocated at time 0 (see lantana_heap_lang/examples/flag_fork.v).
    - The step-indexed readings are specific to [ordSI].
    - A registered structure stores the readings of its contents when it is registered
      ([alwaysI] and [untilI] the canonical ones, [alwaysI_guar] and [untilI_guar] given
      ones); recursion through a registered structure goes through [alwaysI_guar] or
      [untilI_guar] (temporal_fixpoint.v, [nest] and [renew]).
    - Allocating an [alwaysI] or an [untilI] registers it: the allocation rules are model
      updates ([|={E}=>m]), which read the position of the run. *)

(** ** Guarantees *)

Section guarantee.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : tps Λ Σ.
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

  Local Notation tgT := ((trace Λ -d> iPropO Σ) -d> nat -d> iPropO Σ).
  (** A running system: a resource indexed by the position and the configuration. *)
  Local Notation sysT := (nat → state Λ → thread_pool Λ → list (observation Λ) → iProp Σ).

  (** The certificate of a registered item at position [n]: a later-guarded record of its
      content at [n] ([tg f n] is the record for the step-indexed reading [f]). For an until,
      either the records of its left and right formulas (one of them holds at [n]) or, if it
      was discharged at [n' ≤ n], the record of its right formula at [n']. *)
  Definition cert_pre (tg : tgT) (n : nat) (e : rentry) : iProp Σ :=
    match e with
    | RMark => True
    | RAlways _ γ => ∃ f, saved_ti γ f ∗ ▷ tg f n
    | RUntil _ k γP γQ =>
        ∃ fP fQ, saved_ti γP fP ∗ saved_ti γQ fQ ∗
          (▷ (tg fP n ∨ tg fQ n) ∨
           ▷ (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tg fQ n'))
    end.

  (** The bundle for position [n]: a registry prefix ending with the marker of [n] and the
      certificates of its entries. *)
  Definition bundle_pre (tg : tgT) (l : list (nat * rentry)) (n : nat) : iProp Σ :=
    reg_lb l ∗ ⌜last l = Some (n, RMark)⌝ ∗ [∗ list] pe ∈ l, cert_pre tg n pe.2.

  (** The one-step property of a system [Sys]: from a consistent system at [n], the bundle for
      [n] (the check), then, after the step, the system at [S n] with the facts about the
      step and later credits for the continuation. The modalities are those of the
      step-indexed readings (adequacy.v): the check is the first fancy update with the later,
      the step the second with the credits. *)
  Definition sys_step_pre (tg : tgT) (Sys : sysT) : iProp Σ :=
    □ ∀ (c : nat) h n σ Θ κs g v Ω W τf γ,
      ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
      history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
      |={⊤,∅}=> ∃ l, bundle_pre tg l n ∗ ▷ |={∅,⊤}=> |={⊤,∅}=> ALC (|={∅,⊤}=>
        ∃ σ' Θ' κs' g' v' Ω' W' γ',
          ⌜behavior (S n, τf) ∧ beh_fscnt (S n, τf) γ' ∧ owit_inv_lb (fair_sched_fun γ') Ω' W' ∧
           hist_trace (h ++ [(σ', Θ', κs')]) τf ∧ obls_drop (fair_sched_fun γ) (fair_sched_fun γ') Ω Ω'⌝ ∗
          £n c ∗ history_interp (h ++ [(σ', Θ', κs')]) (S n) σ' Θ' κs' ∗
          model_interp g' v' Ω' W' (S n) (dom Θ') ∗ Sys (S n) σ' Θ' κs').

  (** A record for [f] at [n]: for any system satisfying the one-step property, given the
      bundle for [n] and the system at [S n] consistent with the trace, [f] holds at [n] on
      the trace. *)
  Definition tguar_pre (tg : tgT) : tgT :=
    λ f n, (□ ∀ (Sys : sysT) l h g v Ω W τf γ σ Θ κs,
      sys_step_pre tg Sys -∗
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
      bundle_pre tg l n -∗
      history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
      f (n, τf))%I.

  Local Instance cert_pre_contractive n e : Contractive (λ tg : tgT, cert_pre tg n e).
  Proof.
    intros m tg1 tg2 Htg. destruct e; simpl; [done| |].
    - f_equiv=> f. f_equiv. f_contractive. by apply Htg.
    - f_equiv=> fP. f_equiv=> fQ. do 3 f_equiv.
      + f_contractive. f_equiv; by apply Htg.
      + f_contractive. f_equiv=> n'. f_equiv=> i'. f_equiv=> Ω'. do 2 f_equiv. by apply Htg.
  Qed.

  Local Instance bundle_pre_contractive l n : Contractive (λ tg : tgT, bundle_pre tg l n).
  Proof.
    intros m tg1 tg2 Htg. rewrite /bundle_pre. do 2 f_equiv.
    apply big_sepL_ne. intros ???. by apply cert_pre_contractive.
  Qed.

  Local Instance sys_step_pre_contractive Sys : Contractive (λ tg : tgT, sys_step_pre tg Sys).
  Proof.
    intros m tg1 tg2 Htg. rewrite /sys_step_pre.
    do 31 f_equiv. by apply bundle_pre_contractive.
  Qed.

  Local Instance tguar_pre_contractive : Contractive tguar_pre.
  Proof.
    intros m tg1 tg2 Htg f n. rewrite /tguar_pre. f_equiv. do 12 (f_equiv=> ?).
    f_equiv; first by apply sys_step_pre_contractive.
    do 2 f_equiv. by apply bundle_pre_contractive.
  Qed.

  Definition tguar_ti : tgT := fixpoint tguar_pre.
  Lemma tguar_ti_unfold f n : tguar_ti f n ⊣⊢ tguar_pre tguar_ti f n.
  Proof. apply (fixpoint_unfold tguar_pre). Qed.

  Global Instance tguar_ti_persistent f n : Persistent (tguar_ti f n).
  Proof. rewrite tguar_ti_unfold. apply _. Qed.
  Global Instance tguar_ti_ne n : NonExpansive (λ f, tguar_ti f n).
  Proof.
    intros m f1 f2 Hf. rewrite !tguar_ti_unfold /tguar_pre. solve_proper.
  Qed.
  Global Instance tguar_ti_proper n : Proper ((≡) ==> (⊣⊢)) (λ f, tguar_ti f n).
  Proof. apply ne_proper, _. Qed.
  (** Records of internally equal readings (the agreement of saved readings is internal). *)
  Lemma tguar_ti_eq (f g : trace Λ -d> iPropO Σ) n : f ≡ g -∗ tguar_ti f n -∗ tguar_ti g n.
  Proof. iIntros "Heq H". iApply (internal_eq_rewrite f g (λ f, tguar_ti f n) with "Heq H"). Qed.

  (** Records of a trace property, the bundle, the certificates and the step property. *)
  Definition tguar G n : iProp Σ := tguar_ti (tps_ti G) n.
  Definition bundle l n : iProp Σ := bundle_pre tguar_ti l n.
  Definition cert n e : iProp Σ := cert_pre tguar_ti n e.
  Definition sys_step (Sys : sysT) : iProp Σ := sys_step_pre tguar_ti Sys.
  (* Opaque for the proof mode: [iNext] must not strip the laters of the certificates. *)
  Global Typeclasses Opaque bundle cert sys_step.

  (** [P ⊨ₜ G]: whenever [P] holds, the rest of the execution satisfies [G]. *)
  Definition temporal P G : iProp Σ :=
    □ ∀ h n σ Θ κs m i Ω W,
      history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ P -∗ tguar G n.

  Global Instance tguar_persistent G n : Persistent (tguar G n).
  Proof. apply _. Qed.
  Global Instance cert_pre_persistent n e : Persistent (cert_pre tguar_ti n e).
  Proof. destruct e; apply _. Qed.
  Global Instance cert_persistent n e : Persistent (cert n e).
  Proof. rewrite /cert. apply _. Qed.
  Global Instance bundle_persistent l n : Persistent (bundle l n).
  Proof. rewrite /bundle /bundle_pre. apply _. Qed.
  Global Instance sys_step_persistent Sys : Persistent (sys_step Sys).
  Proof. rewrite /sys_step /sys_step_pre. apply _. Qed.
  Global Instance temporal_persistent P G : Persistent (temporal P G).
  Proof. apply _. Qed.

  Lemma tguar_ti_intro f n :
    (□ ∀ (Sys : sysT) l h g v Ω W τf γ σ Θ κs,
      sys_step Sys -∗
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
      bundle l n -∗
      history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
      f (n, τf)) ⊢ tguar_ti f n.
  Proof. by rewrite tguar_ti_unfold. Qed.

  Lemma tguar_ti_elim f (Sys : sysT) l h n g v Ω W τf γ σ Θ κs :
    tguar_ti f n -∗
    sys_step Sys -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
    bundle l n -∗
    history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
    f (n, τf).
  Proof. rewrite tguar_ti_unfold. iIntros "#HG #ST H #B W". by iApply ("HG" with "ST H B W"). Qed.

  Lemma tguar_intro G n :
    (□ ∀ (Sys : sysT) l h g v Ω W τf γ σ Θ κs,
      sys_step Sys -∗
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
      bundle l n -∗
      history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
      tps_ti G (n, τf)) ⊢ tguar G n.
  Proof. apply tguar_ti_intro. Qed.

  (** Eliminating a record: against the bundle of its position and the system after the step. *)
  Lemma tguar_elim G (Sys : sysT) l h n g v Ω W τf γ σ Θ κs :
    tguar G n -∗
    sys_step Sys -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
    bundle l n -∗
    history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
    tps_ti G (n, τf).
  Proof. apply tguar_ti_elim. Qed.

  (** Producing a record from a guarantee and the content at the current position. *)
  Lemma temporal_elim P G h n σ Θ κs m i Ω W :
    temporal P G -∗
    history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ P -∗ tguar G n.
  Proof. iIntros "#HG H". by iApply "HG". Qed.

  (** The same from a later-guarded content: a later-guarded record (the certificates). *)
  Lemma temporal_elim_later P G h n σ Θ κs m i Ω W :
    temporal P G -∗
    ▷ P ∗ history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) -∗ ▷ tguar G n.
  Proof. iIntros "#HG (HP& HI& MI)". iNext. iApply ("HG" with "[$HI $MI $HP]"). Qed.

  (** The same from a later-guarded guarantee, as stored with a registered structure. *)
  Lemma temporal_elim_later_guar P G h n σ Θ κs m i Ω W :
    ▷ temporal P G -∗
    ▷ P ∗ history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) -∗ ▷ tguar G n.
  Proof. iIntros "#HG (HP& HI& MI)". iNext. iApply ("HG" with "[$HI $MI $HP]"). Qed.

  Global Instance temporal_ne G : NonExpansive (λ P, temporal P G).
  Proof. rewrite /temporal. solve_proper. Qed.
  Global Instance temporal_proper G : Proper ((≡) ==> (⊣⊢)) (λ P, temporal P G).
  Proof. apply ne_proper, _. Qed.
  (* The applied form, for [f_equiv] and [solve_contractive]. *)
  Global Instance temporal_proper_ne n : Proper (dist n ==> (=) ==> dist n) temporal.
  Proof. intros P P' HP G ? <-. by apply temporal_ne. Qed.

  Lemma tguar_mono G G' n : tps_le G G' → tguar G n ⊢ tguar G' n.
  Proof.
    iIntros (Hle) "#HG". iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W".
    iApply Hle. by iApply (tguar_elim with "HG ST [//] B W").
  Qed.

End guarantee.

Notation "P ⊨ₜ G" := (temporal P%I G%S) (at level 70, format "P  ⊨ₜ  G") : bi_scope.

(** The canonical trace property of an iProp: the meet of all trace properties that it
    validly guarantees. Every iProp guarantees it ([temporal_sem]), and it implies each of
    them ([tps_sem_le]). The registered structures store it for their contents, so temporal
    formulas carry no trace-property annotations. *)
Definition tps_sem `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (Q : iProp Σ) : tps Λ Σ :=
  tps_forall (λ G : {G : tps Λ Σ | ⊢ Q ⊨ₜ G}, proj1_sig G).
(* Opaque for the proof mode: unification must not compare two [tps_sem] through their
   bodies (the index type is a proposition about the argument). *)
Global Typeclasses Opaque tps_sem.

(** Once discharged, the obligation invariant of an until keeps the record of its right
    formula at the discharge event. *)
Notation until_disch k G2 :=
  (∃ n' i' Ω', event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n')%I (only parsing).

(** ** The registry and the registered structures

    The registry state holds, for every registered item, its handle: the saved
    step-indexed readings of its contents and its invariant, which a run opens at every
    position to certify the content. The state is the interpretation of the temporal layer
    ([TemporalInterp]), threaded by the program logic with the history interpretation. *)
Definition treg_handle `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (e : rentry) : iProp Σ :=
  match e with
  | RMark => True
  | RAlways N γ => ∃ (P : iProp Σ) (G : tps Λ Σ), saved_ti γ (tps_ti G) ∗ inv N P ∗ ▷ (P ⊨ₜ G)
  | RUntil N k γP γQ =>
      ∃ (P : iProp Σ) (G1 G2 : tps Λ Σ), saved_ti γP (tps_ti G1) ∗ saved_ti γQ (tps_ti G2) ∗
        oblP_inv N k P (until_disch k G2) ∗ ▷ (P ⊨ₜ G1)
  end.
Definition treg_state `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : iProp Σ := treg_st treg_handle.
Global Instance treg_temporal_interp `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : TemporalInterp Λ Σ :=
  treg_state.
Lemma temporal_interp_treg `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : temporal_interp = treg_state.
Proof. done. Qed.

(** An invariant whose content is trace-visible through a guarantee [G] of its content [P]:
    the invariant, registered with the reading [G] and a (later-guarded) proof that the
    content guarantees [G], and the record of [G] at its registration position. The proof
    may be an iProp hypothesis available at registration: one that depends on a token
    ([alwaysI_register]), or a closed one about a recursively defined structure
    (temporal_fixpoint.v). The common cases: [alwaysI N P] reads as the canonical trace
    property of [P]; [alwaysI_as N P V], the invariant [P] seen as a consequence [V] of its
    content (from [□ (P -∗ V)]), reads as that of [V]. Sealed: the proof mode must not unify
    two structures through their bodies. *)
Local Definition alwaysI_guar_def `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (N : namespace) (P : iProp Σ) (G : tps Λ Σ) : iProp Σ :=
  ∃ j r γ st, reg_idx j r (RAlways N γ) ∗ hG_event r st ∗
              saved_ti γ (tps_ti G) ∗ inv N P ∗ ▷ (P ⊨ₜ G) ∗ ▷ tguar G r.
Local Definition alwaysI_guar_aux : seal (@alwaysI_guar_def). Proof. by eexists. Qed.
Definition alwaysI_guar := alwaysI_guar_aux.(unseal).
Global Arguments alwaysI_guar {Λ Σ _ _} N P G.
Local Lemma alwaysI_guar_unseal : @alwaysI_guar = @alwaysI_guar_def.
Proof. rewrite -alwaysI_guar_aux.(seal_eq) //. Qed.
Lemma alwaysI_guar_unfold `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N P G :
  alwaysI_guar N P G = (∃ j r γ st, reg_idx j r (RAlways N γ) ∗ hG_event r st ∗
                        saved_ti γ (tps_ti G) ∗ inv N P ∗ ▷ (P ⊨ₜ G) ∗ ▷ tguar G r)%I.
Proof. by rewrite alwaysI_guar_unseal. Qed.
Definition alwaysI_as `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (N : namespace) (P V : iProp Σ) : iProp Σ :=
  alwaysI_guar N P (tps_sem V).
Definition alwaysI `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
  alwaysI_as N P P.
(* Opaque for the proof mode: [iNext] must not unfold a structure to strip its inner later. *)
Global Typeclasses Opaque alwaysI_as alwaysI.

(** The persistent part of an until with readings [G1], [G2] of its left and right formulas
    [P], [Q]: its obligation invariant, registered with the readings and (later-guarded)
    proofs that the formulas guarantee them, and the record of [G1] at its allocation
    position, where its obligation was assigned. Once the obligation is discharged, the
    invariant keeps the record of [G2] at the discharge. *)
Definition untilI_guar_pers `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (N : namespace) (k : positive) (P Q : iProp Σ) (G1 G2 : tps Λ Σ) : iProp Σ :=
  ∃ j r γP γQ st v Ω fu o,
    reg_idx j r (RUntil N k γP γQ) ∗ hG_event r st ∗
    saved_ti γP (tps_ti G1) ∗ saved_ti γQ (tps_ti G2) ∗
    oblP_inv N k P (until_disch k G2) ∗ ▷ (P ⊨ₜ G1) ∗ ▷ (Q ⊨ₜ G2) ∗
    event_obl v (r, Ω) k (obl_assigned fu o) ∗ ▷ tguar G1 r.
Global Typeclasses Opaque untilI_guar_pers.
(** With the canonical readings. *)
Definition untilI_pers `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (N : namespace) (k : positive) (P Q : iProp Σ) : iProp Σ :=
  untilI_guar_pers N k P Q (tps_sem P) (tps_sem Q).
Global Typeclasses Opaque untilI_pers.

(** [P] until [Q] using namespace [N] and obligation [k], read as [G1] until [G2]: the token
    of the assigned obligation with the persistent part. As for [alwaysI_guar], the proofs
    that the formulas guarantee their readings may be iProp hypotheses at allocation, e.g.
    closed proofs about a recursively defined structure (temporal_fixpoint.v, [renew]). *)
Local Definition untilI_guar_def `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  N k (q : Qp) (P Q : iProp Σ) (G1 G2 : tps Λ Σ) : iProp Σ :=
  oblP_assigned k (q/2)%Qp ∗ untilI_guar_pers N k P Q G1 G2.
(* Sealed: the proof mode splits it by fractions, and unification (e.g. in [iFrame]) does not
   unfold it. *)
Local Definition untilI_guar_aux : seal (@untilI_guar_def). Proof. by eexists. Qed.
Definition untilI_guar := untilI_guar_aux.(unseal).
Global Arguments untilI_guar {Λ Σ _ _} N k q P Q G1 G2.
Local Lemma untilI_guar_unseal : @untilI_guar = @untilI_guar_def.
Proof. rewrite -untilI_guar_aux.(seal_eq) //. Qed.
Lemma untilI_guar_unfold `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N k q P Q G1 G2 :
  untilI_guar N k q P Q G1 G2 = (oblP_assigned k (q/2)%Qp ∗ untilI_guar_pers N k P Q G1 G2)%I.
Proof. by rewrite untilI_guar_unseal. Qed.

(** [P] until [Q], read with the canonical trace properties of its formulas. Sealed on its
    own, so that unification compares two untils by their formulas only. *)
Local Definition untilI_def `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N k (q : Qp) (P Q : iProp Σ) : iProp Σ :=
  untilI_guar N k q P Q (tps_sem P) (tps_sem Q).
Local Definition untilI_aux : seal (@untilI_def). Proof. by eexists. Qed.
Definition untilI := untilI_aux.(unseal).
Global Arguments untilI {Λ Σ _ _} N k q P Q.
Local Lemma untilI_unseal : @untilI = @untilI_def.
Proof. rewrite -untilI_aux.(seal_eq) //. Qed.
Lemma untilI_guar_canonical `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N k q P Q :
  untilI N k q P Q = untilI_guar N k q P Q (tps_sem P) (tps_sem Q).
Proof. by rewrite untilI_unseal. Qed.
Lemma untilI_unfold `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N k q P Q :
  untilI N k q P Q = (oblP_assigned k (q/2)%Qp ∗ untilI_pers N k P Q)%I.
Proof. by rewrite untilI_guar_canonical untilI_guar_unfold. Qed.

Definition finallyI `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N k (q : Qp) (Q : iProp Σ) : iProp Σ :=
  untilI N k q True Q.

(** ** Rules *)

Section rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : tps Λ Σ.

  Lemma temporal_weaken P G G' : tps_le G G' → P ⊨ₜ G ⊢ P ⊨ₜ G'.
  Proof.
    iIntros (Hle) "#HG !>". iIntros (?????????) "H". iApply tguar_mono; first done. by iApply "HG".
  Qed.

  Lemma temporal_mono P Q G : □ (Q -∗ P) -∗ P ⊨ₜ G -∗ Q ⊨ₜ G.
  Proof.
    iIntros "#HQP #HG !>". iIntros (?????????) "(HI& MI& HQ)". iApply "HG". iFrame. by iApply "HQP".
  Qed.

  Lemma temporal_true P : ⊢ P ⊨ₜ tps_true.
  Proof.
    iIntros "!>" (?????????) "_". iApply tguar_intro. iIntros "!>" (????????????) "_ _ _ _". done.
  Qed.

  Lemma temporal_pure (φ : Prop) : ⊢ ⌜φ⌝ ⊨ₜ tps_pure φ.
  Proof.
    iIntros "!>" (?????????) "(_& _& %Hφ)". iApply tguar_intro. iIntros "!>" (????????????) "_ _ _ _". done.
  Qed.

  Lemma temporal_atomic π : ⊢ state_pred_interp π ⊨ₜ tps_atomic π.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& _& TL)".
    rewrite /history_interp. iDestruct "HI" as "(HI1& HI2& SI)".
    iPoseProof (state_interp_wf with "[$SI $TL]") as "%".
    iPoseProof (history_interp_event_pred_now with "[HI1 HI2 SI]") as "#TF". 1: done.
    { rewrite /history_interp. iFrame. }
    iApply tguar_intro.
    iIntros "!>" (Sys l h' g v2 Ω2 W' τf γ σ' Θ' κs') "_ %Hf _ (HI'& MI& Sys)".
    destruct Hf as (BEH& FS& LB& HIST).
    simpl. unfold ti_atomic. iPoseProof (event_pred_history_interp_lookup with "[$HI' $TF]") as "%H'".
    destruct H' as [H' ?]. simpl. apply HIST in H'. destruct H' as [? H']. rewrite H'. auto.
  Qed.

  Lemma temporal_and P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∧ Q) ⊨ₜ (G1 ∧ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& HPQ)".
    iPoseProof (temporal_elim with "HG1 [$HI $MI HPQ]") as "#T1"; first by iDestruct "HPQ" as "[$ _]".
    iPoseProof (temporal_elim with "HG2 [$HI $MI HPQ]") as "#T2"; first by iDestruct "HPQ" as "[_ $]".
    iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W". iSplit.
    - by iApply (tguar_elim with "T1 ST [//] B W").
    - by iApply (tguar_elim with "T2 ST [//] B W").
  Qed.

  Lemma temporal_sep P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∗ Q) ⊨ₜ (G1 ∧ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& HP& HQ)".
    iPoseProof (temporal_elim with "HG1 [$HI $MI $HP]") as "#T1".
    iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#T2".
    iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W". iSplit.
    - by iApply (tguar_elim with "T1 ST [//] B W").
    - by iApply (tguar_elim with "T2 ST [//] B W").
  Qed.

  Lemma temporal_or P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∨ Q) ⊨ₜ (G1 ∨ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& [HP | HQ])".
    - iPoseProof (temporal_elim with "HG1 [$HI $MI $HP]") as "#T1".
      iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W". iLeft.
      by iApply (tguar_elim with "T1 ST [//] B W").
    - iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#T2".
      iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W". iRight.
      by iApply (tguar_elim with "T2 ST [//] B W").
  Qed.

  Lemma temporal_impl (φ : Prop) P G : P ⊨ₜ G -∗ (⌜φ⌝ → P) ⊨ₜ (⌜φ⌝ → G).
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& HP)".
    destruct (Classical_Prop.classic φ) as [Hφ|Hφ].
    - iPoseProof (temporal_elim with "HG [$HI $MI HP]") as "#T"; first by iApply "HP".
      iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W". rewrite /= /ti_impl. iIntros (_).
      by iApply (tguar_elim with "T ST [//] B W").
    - iApply tguar_intro. iIntros "!>" (????????????) "_ _ _ _". rewrite /= /ti_impl. by iIntros (?).
  Qed.

  (** Universal quantification over any type. *)
  Lemma temporal_forall {X : Type} (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∀ x, P x) ⊨ₜ tps_forall G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& HP)".
    iAssert (∀ x, tguar (G x) _)%I with "[-]" as "#T".
    { iIntros (x). iApply (temporal_elim with "HG"). iFrame. iApply "HP". }
    iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W". iIntros (x).
    by iApply (tguar_elim with "T ST [//] B W").
  Qed.

  Lemma temporal_sem Q : ⊢ Q ⊨ₜ tps_sem Q.
  Proof.
    iApply (temporal_mono (∀ _ : {G : tps Λ Σ | ⊢ Q ⊨ₜ G}, Q)%I with "[]").
    { iIntros "!> HQ" (?). done. }
    iApply temporal_forall. iIntros ([G HG]). iApply HG.
  Qed.
  Lemma tps_sem_le Q G : (⊢ Q ⊨ₜ G) → tps_le (tps_sem Q) G.
  Proof.
    intros HG ??. rewrite /= /ti_forall. iIntros "H". iApply ("H" $! (exist (λ G, ⊢ Q ⊨ₜ G) G HG)).
  Qed.
  Lemma tps_sem_tr Q G τ : (⊢ Q ⊨ₜ G) → tps_tr (tps_sem Q) τ → tps_tr G τ.
  Proof. intros HG H. apply (H (exist (λ G, ⊢ Q ⊨ₜ G) G HG)). Qed.

  (** Trace-visible existential quantification, over small types. *)
  Lemma temporal_exist {X : Type} `{!TypeExistentialProperty X ordI} (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∃ x, P x) ⊨ₜ tps_exist G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& [%x HP])".
    iPoseProof (temporal_elim with "HG [$HI $MI $HP]") as "#T".
    iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W". iExists x.
    by iApply (tguar_elim with "T ST [//] B W").
  Qed.

  (** Ghost existential quantification, over any type: the witness does not show in the
      trace property. *)
  Lemma temporal_exist_ghost {X : Type} (P : X → iProp Σ) G :
    (∀ x, P x ⊨ₜ G) -∗ (∃ x, P x) ⊨ₜ G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& [%x HP])". iApply (temporal_elim with "HG"). iFrame.
  Qed.

  (** An iProp carrying its own guarantee: such pairs can be stored in invariants and
      saved propositions, and quantified over. *)
  Lemma temporal_certified G : ⊢ (∃ P, P ∗ P ⊨ₜ G) ⊨ₜ G.
  Proof.
    iIntros "!>" (?????????) "(HI& MI& (%P& HP& #HG))". iApply (temporal_elim with "HG"). iFrame.
  Qed.

  Lemma temporal_persistently P G : P ⊨ₜ G -∗ □ P ⊨ₜ G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& #HP)". iApply (temporal_elim with "HG"). iFrame "HI MI HP".
  Qed.

  (** A persistent token excluding a branch of a disjunction: the guarantee of the other
      branch is a guarantee of the whole. With [alwaysI_register_guar], this exports a
      stronger reading of an invariant once the token is at hand. *)
  Lemma temporal_or_excl (A B C : iProp Σ) G `{!Persistent C} :
    (C ∗ A ⊢ False) → C -∗ B ⊨ₜ G -∗ (A ∨ B) ⊨ₜ G.
  Proof.
    iIntros (Hexcl) "#HC #HB". iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& [HA|HB'])".
    - iExFalso. iApply Hexcl. iFrame "HC HA".
    - iApply (temporal_elim with "HB"). iFrame.
  Qed.

End rules.

(** ** Reading the model under a model update

    Allocation of a registered structure reads the history and the model (to produce the
    record of the content at the current position) and updates the registry state. *)
Section mupd_read.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma mupd_read n D (P : iProp Σ) :
    (∀ g i Ω W, model_interp g i Ω W n D -∗ model_interp g i Ω W n D ∗ P) ⊢ |=[n,D]=>m P.
  Proof.
    iIntros "H". iApply mupd_nd_step. iIntros (g i Ω W) "MI".
    iDestruct ("H" with "MI") as "[MI HP]". iModIntro. iExists Ω.
    iSplit; first (iPureIntro; apply obls_ndf_refl).
    iIntros (W2 [WS OI2]). rewrite /model_interp. iDestruct "MI" as "(MHI& S& T& A& G& W& %OI)".
    iMod (model_history_interp_step _ _ n n _ Ω with "MHI") as "MHI"; [done|done|].
    iPoseProof (owit_mon W W2 with "W") as "W".
    { eapply wits_lef_same_wits_mon; [done| |done]. by apply wits_ndf_wits_lef. }
    iModIntro. iFrame. iSplit; first done. by iApply mupd_intro.
  Qed.

  (** The same at the level of [sfmupd], with the history and the registry: fancy updates
      may happen before and after reading the model. *)
  Lemma sfmupd_read_fupd E (P : iProp Σ) :
    (∀ h n σ Θ κs,
      history_interp h n σ Θ κs -∗ treg_state -∗ |={E,∅}=> ∀ g i Ω W,
        model_interp g i Ω W n (dom Θ) -∗
        model_interp g i Ω W n (dom Θ) ∗ |={∅,E}=> history_interp h n σ Θ κs ∗ treg_state ∗ P) ⊢ |={E}=>m P.
  Proof.
    iIntros "H". unfold_sfmupd. iIntros (h n σ Θ κs) "[HI TI]". rewrite /fmupd.
    iMod ("H" with "HI TI") as "H". iModIntro.
    iApply mupd_read. iIntros (g i Ω W) "MI". iDestruct ("H" with "MI") as "($& HP)".
    iMod "HP" as "(HI& TI& HP)". iModIntro. iFrame.
  Qed.

  Lemma sfmupd_read E (P : iProp Σ) :
    (∀ h n σ Θ κs g i Ω W,
      history_interp h n σ Θ κs -∗ treg_state -∗ model_interp g i Ω W n (dom Θ) -∗
      model_interp g i Ω W n (dom Θ) ∗ |={E}=> history_interp h n σ Θ κs ∗ treg_state ∗ P) ⊢ |={E}=>m P.
  Proof.
    iIntros "H". iApply sfmupd_read_fupd. iIntros (h n σ Θ κs) "HI TI".
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    iIntros (g i Ω W) "MI". iDestruct ("H" with "HI TI MI") as "($& HP)".
    iMod "close" as "_". iMod "HP" as "(HI& TI& HP)". iModIntro. iFrame.
  Qed.

End mupd_read.

(** ** Rules for [alwaysI] *)
Section always_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Global Instance alwaysI_guar_persistent N P G : Persistent (alwaysI_guar N P G).
  Proof. rewrite alwaysI_guar_unfold. apply _. Qed.
  Global Instance alwaysI_as_persistent N P V : Persistent (alwaysI_as N P V).
  Proof. rewrite /alwaysI_as. apply _. Qed.
  Global Instance alwaysI_persistent N P : Persistent (alwaysI N P).
  Proof. rewrite /alwaysI. apply _. Qed.
  Global Instance treg_handle_persistent e : Persistent (treg_handle e).
  Proof. destruct e; apply _. Qed.

  (** The structure is contractive in its content, which occurs only in the invariant and
      in the stored guarantee: structures can be defined by guarded recursion
      (temporal_fixpoint.v). *)
  Global Instance alwaysI_guar_contractive N G : Contractive (λ P, alwaysI_guar N P G).
  Proof. rewrite alwaysI_guar_unseal /alwaysI_guar_def. solve_contractive. Qed.

  Lemma alwaysI_guar_inv N P G : alwaysI_guar N P G ⊢ inv N P.
  Proof. rewrite alwaysI_guar_unfold. iIntros "(%&%&%&%& _& _& _& $& _)". Qed.
  Lemma alwaysI_guar_temporal N P G : alwaysI_guar N P G ⊢ ▷ (P ⊨ₜ G).
  Proof. rewrite alwaysI_guar_unfold. iIntros "(%&%&%&%& _& _& _& _& $& _)". Qed.
  Lemma alwaysI_as_inv N P V : alwaysI_as N P V ⊢ inv N P.
  Proof. apply alwaysI_guar_inv. Qed.
  Lemma alwaysI_inv N P : alwaysI N P ⊢ inv N P.
  Proof. apply alwaysI_as_inv. Qed.

  Lemma alwaysI_guar_acc E N P G :
    ↑N ⊆ E → alwaysI_guar N P G ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. iIntros (?) "#H". iApply inv_acc; first done. by iApply alwaysI_guar_inv. Qed.
  Lemma alwaysI_as_acc E N P V :
    ↑N ⊆ E → alwaysI_as N P V ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. apply alwaysI_guar_acc. Qed.
  Lemma alwaysI_acc E N P :
    ↑N ⊆ E → alwaysI N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. apply alwaysI_as_acc. Qed.

  (** Proof mode integration: [iInv] opens these like invariants. *)
  Global Instance into_inv_alwaysI_guar N P G : IntoInv (alwaysI_guar N P G) N := {}.
  Global Instance into_acc_alwaysI_guar N P G E :
    IntoAcc (X := unit) (alwaysI_guar N P G)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". by iApply alwaysI_guar_acc.
  Qed.
  Global Instance into_inv_alwaysI_as N P V : IntoInv (alwaysI_as N P V) N := {}.
  Global Instance into_acc_alwaysI_as N P V E :
    IntoAcc (X := unit) (alwaysI_as N P V)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". by iApply alwaysI_as_acc.
  Qed.
  Global Instance into_inv_alwaysI N P : IntoInv (alwaysI N P) N := {}.
  Global Instance into_acc_alwaysI N P E :
    IntoAcc (X := unit) (alwaysI N P)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". by iApply alwaysI_acc.
  Qed.

  (** Registering an existing invariant with a guarantee of its content (an iProp
      hypothesis, later-guarded): a model update that records the content at the current
      position. *)
  Lemma alwaysI_register_guar E N P G :
    ↑N ⊆ E →
    inv N P -∗ ▷ (P ⊨ₜ G) -∗ |={E}=>m alwaysI_guar N P G.
  Proof.
    iIntros (HNE) "#Hinv #HG". iApply sfmupd_read_fupd. iIntros (h n σ Θ κs) "HI TI".
    iMod (inv_acc with "Hinv") as "[HP Hclose]"; first done.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    iIntros (g i Ω W) "MI".
    iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#C".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MI". iMod "close" as "_". iMod ("Hclose" with "HP") as "_".
    iMod (saved_ti_alloc (tps_ti G)) as (γ) "#Hγ".
    iMod (treg_st_register treg_handle (RAlways N γ) with "TI [] HI") as "(HI& TI& (%j& #Hj))".
    { iIntros (st) "_". simpl. iExists P, G. iFrame "Hγ Hinv HG". }
    iModIntro. iFrame "HI TI". rewrite alwaysI_guar_unfold. iExists j, n, γ, _. iFrame "Hj HE Hγ Hinv HG C".
  Qed.
  (** The same, read as a consequence [V] of the content. *)
  Lemma alwaysI_register E N P V :
    ↑N ⊆ E →
    inv N P -∗ □ (P -∗ V) -∗ |={E}=>m alwaysI_as N P V.
  Proof.
    iIntros (HNE) "#Hinv #HPV".
    iApply (alwaysI_register_guar with "Hinv []"); first done.
    iNext. iApply (temporal_mono with "HPV"). iApply temporal_sem.
  Qed.

  (** Allocation registers the invariant and records its content at the current position. *)
  Lemma alwaysI_alloc_guar E N P G :
    ▷ (P ⊨ₜ G) -∗ ▷ P -∗ |={E}=>m alwaysI_guar N P G.
  Proof.
    iIntros "#HG HP". iApply sfmupd_read. iIntros (h n σ Θ κs g i Ω W) "HI TI MI".
    iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#C".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MI".
    iMod (saved_ti_alloc (tps_ti G)) as (γ) "#Hγ".
    iMod (inv_alloc N _ P with "HP") as "#Hinv".
    iMod (treg_st_register treg_handle (RAlways N γ) with "TI [] HI") as "(HI& TI& (%j& #Hj))".
    { iIntros (st) "_". simpl. iExists P, G. iFrame "Hγ Hinv HG". }
    iModIntro. iFrame "HI TI". rewrite alwaysI_guar_unfold. iExists j, n, γ, _. iFrame "Hj HE Hγ Hinv HG C".
  Qed.
  Lemma alwaysI_alloc E N P :
    ▷ P -∗ |={E}=>m alwaysI N P.
  Proof.
    iIntros "HP". iApply (alwaysI_alloc_guar with "[] HP").
    iNext. iApply temporal_sem.
  Qed.

End always_rules.

(** ** Rules for [untilI_guar] and [untilI] *)
Section until_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Global Instance untilI_guar_pers_persistent N k P Q G1 G2 :
    Persistent (untilI_guar_pers N k P Q G1 G2).
  Proof. rewrite /untilI_guar_pers. apply _. Qed.
  Global Instance untilI_pers_persistent N k P Q : Persistent (untilI_pers N k P Q).
  Proof. rewrite /untilI_pers. apply _. Qed.

  (* The contractiveness of the obligation invariant, in the form [f_contractive] uses. *)
  Local Instance oblP_inv_contractive_l n N k :
    Proper (dist_later n ==> (=) ==> dist n) (oblP_inv (Σ:=Σ) N k).
  Proof. intros P P' HP R ? <-. by apply oblP_inv_contractive_1. Qed.
  (** The structure is contractive in its formulas, which occur only in the invariant and in
      the stored guarantees: structures can be defined by guarded recursion through either
      side (temporal_fixpoint.v). *)
  Global Instance untilI_guar_contractive_l N k q Q G1 G2 :
    Contractive (λ P, untilI_guar N k q P Q G1 G2).
  Proof. rewrite untilI_guar_unseal /untilI_guar_def /untilI_guar_pers. solve_contractive. Qed.
  Global Instance untilI_guar_contractive_r N k q P G1 G2 :
    Contractive (λ Q, untilI_guar N k q P Q G1 G2).
  Proof. rewrite untilI_guar_unseal /untilI_guar_def /untilI_guar_pers. solve_contractive. Qed.

  Lemma untilI_guar_pers_inv N k P Q G1 G2 :
    untilI_guar_pers N k P Q G1 G2 ⊢ oblP_inv N k P (until_disch k G2).
  Proof. rewrite /untilI_guar_pers. iIntros "(%&%&%&%&%&%&%&%&%& _& _& _& _& $& _)". Qed.
  Lemma untilI_pers_inv N k P Q : untilI_pers N k P Q ⊢ oblP_inv N k P (until_disch k (tps_sem Q)).
  Proof. apply untilI_guar_pers_inv. Qed.
  Lemma untilI_guar_pers_temporal N k P Q G1 G2 :
    untilI_guar_pers N k P Q G1 G2 ⊢ ▷ (P ⊨ₜ G1) ∗ ▷ (Q ⊨ₜ G2).
  Proof. rewrite /untilI_guar_pers. iIntros "(%&%&%&%&%&%&%&%&%& _& _& _& _& _& $& $& _)". Qed.
  Lemma untilI_guar_temporal N k q P Q G1 G2 :
    untilI_guar N k q P Q G1 G2 ⊢ ▷ (P ⊨ₜ G1) ∗ ▷ (Q ⊨ₜ G2).
  Proof. rewrite untilI_guar_unfold. iIntros "[_ U]". by iApply untilI_guar_pers_temporal. Qed.

  (** Fractions *)
  Lemma untilI_guar_frac_split N k q q1 q2 P Q G1 G2 :
    (q = q1 + q2)%Qp →
    ⊢ untilI_guar N k q P Q G1 G2 -∗ (untilI_guar N k q1 P Q G1 G2 ∗ untilI_guar N k q2 P Q G1 G2).
  Proof.
    iIntros (He) "U". rewrite !untilI_guar_unfold He Qp.div_add_distr. iDestruct "U" as "([$ $]& #U)". auto.
  Qed.
  Lemma untilI_guar_frac_add N k q1 q2 q P Q G1 G2 P' Q' G1' G2' :
    (q = q1 + q2)%Qp →
    untilI_guar N k q1 P Q G1 G2 -∗ untilI_guar N k q2 P' Q' G1' G2' -∗ untilI_guar N k q P Q G1 G2.
  Proof.
    intros Hq. subst q.
    rewrite !untilI_guar_unfold Qp.div_add_distr. iIntros "[Oa1 $] [Oa2 _]".
    by iCombine "Oa1 Oa2" as "Oa".
  Qed.

  Global Instance untilI_guar_fractional N k P Q G1 G2 : Fractional (λ q, untilI_guar N k q P Q G1 G2).
  Proof.
    intros p q. rewrite !untilI_guar_unfold. iSplit.
    - iIntros "(Oa& #OI)". iFrame "OI". rewrite !Qp.div_add_distr. iDestruct "Oa" as "[Oa Oa']". iFrame.
    - iIntros "((Oa1& #Oi)& Oa2& _)". iFrame "Oi". rewrite !Qp.div_add_distr. iCombine "Oa1 Oa2" as "$".
  Qed.
  Global Instance untilI_guar_as_fractional N k q P Q G1 G2 :
    AsFractional (untilI_guar N k q P Q G1 G2) (λ q, untilI_guar N k q P Q G1 G2) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma untilI_frac_split N k q q1 q2 P Q :
    (q = q1 + q2)%Qp →
    ⊢ untilI N k q P Q -∗ (untilI N k q1 P Q ∗ untilI N k q2 P Q).
  Proof. rewrite !untilI_guar_canonical. apply untilI_guar_frac_split. Qed.
  Lemma untilI_frac_add N k q1 q2 q P Q P' Q' :
    (q = q1 + q2)%Qp →
    untilI N k q1 P Q -∗ untilI N k q2 P' Q' -∗ untilI N k q P Q.
  Proof. rewrite !untilI_guar_canonical. apply untilI_guar_frac_add. Qed.

  Global Instance untilI_fractional N k P Q : Fractional (λ q, untilI N k q P Q).
  Proof. intros p q. rewrite !untilI_guar_canonical. apply (untilI_guar_fractional N k P Q _ _ p q). Qed.
  Global Instance untilI_as_fractional N k q P Q : AsFractional (untilI N k q P Q) (λ q, untilI N k q P Q) q.
  Proof. split; [auto|apply _]. Qed.

  (** Update rules. Allocation of the until registers it (a model update, reading the model)
      with the readings of its formulas and later-guarded proofs that the formulas guarantee
      them; the record of the left formula at the current position is produced from it. *)
  Lemma untilI_guar_alloc E p K ℓ μ :
    parP_le p ℓ -∗ parP_kids p K -∗
    |={E}=>m ∃ k, ⌜k ∉ K⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 ∀ E' N (P Q : iProp Σ) G1 G2,
                   ▷ (P ⊨ₜ G1) -∗ ▷ (Q ⊨ₜ G2) -∗ ▷ P -∗ |={E'}=>m untilI_guar N k 1 P Q G1 G2.
  Proof.
    iIntros "B Kp". iMod (obl_alloc_assigned with "B Kp") as "(%k& $& $& $& Oa& $& $& ACC)".
    iIntros "!> %E' %N %P %Q %G1 %G2 #HG1 #HG2 HC".
    iApply sfmupd_read. iIntros (h n σ Θ κs gm i Ω W) "HI TI MI".
    iPoseProof (temporal_elim_later_guar P G1 with "HG1 [$HC $HI $MI]") as "#C".
    iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "(#OE& Oa)".
    iPoseProof (osat_lookup_assigned with "[$S $OE $Oa]") as "%Hk". destruct Hk as (fu& o& Hk).
    iPoseProof (model_history_interp_event_obl_now with "MHI") as "#EA". 1: eauto.
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MHI S MI".
    iMod ("ACC" $! E' N P (until_disch k G2) with "HC") as "#OI".
    iMod (saved_ti_alloc (tps_ti G1)) as (γP) "#HγP".
    iMod (saved_ti_alloc (tps_ti G2)) as (γQ) "#HγQ".
    iMod (treg_st_register treg_handle (RUntil N k γP γQ) with "TI [] HI") as "(HI& TI& (%j& #Hj))".
    { iIntros (st) "_". simpl. iExists P, G1, G2. iFrame "HγP HγQ OI HG1". }
    iModIntro. iFrame "HI TI". rewrite untilI_guar_unfold /untilI_guar_pers. iSplitL "Oa".
    { iEval (unfold_opreds). iFrame "OE Oa". }
    iExists j, n, γP, γQ, _, i, Ω, fu, o. iFrame "Hj HE HγP HγQ OI HG1 HG2 EA C".
  Qed.

  Lemma untilI_alloc E p K ℓ μ :
    parP_le p ℓ -∗ parP_kids p K -∗
    |={E}=>m ∃ k, ⌜k ∉ K⌝ ∗ parP_kids p ({[k]} ∪ K) ∗ oblP_kids k ∅ ∗
                 oblP_fuel k ℓ μ ∗ witP_layer k ℓ ∗
                 ∀ E' N (P Q : iProp Σ), ▷ P -∗ |={E'}=>m untilI N k 1 P Q.
  Proof.
    iIntros "B Kp". iMod (untilI_guar_alloc with "B Kp") as "(%k& %Hk& Kp& Kk& F& W& ACC)".
    iModIntro. iExists k. iFrame "Kp Kk F W". iSplitR; first done.
    iIntros (E' N P Q) "HP". rewrite untilI_guar_canonical.
    iApply ("ACC" with "[] [] HP"); iNext; iApply temporal_sem.
  Qed.

  (** An already discharged obligation invariant, with the record of a guarantee [G] of [Q]
      at the current position (no until is created, so nothing is registered). *)
  Lemma untilI_discharged_alloc_guar E ℓ μ (Q : iProp Σ) G :
    Q ⊨ₜ G -∗ Q -∗
    |={E}=>m Q ∗ ∃ k, oblP_discharged k ∗
                        (∀ E' N (P : iProp Σ), |={E'}=> oblP_inv N k P (until_disch k G)) ∗
                        oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof.
    iIntros "#HG2 HQ".
    unfold_sfmupd. rewrite /fmupd. iIntros (?????) "[SI TI]".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    unfold_opreds. iApply mupd_nd_step. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
    assert (NEW : ∃ k, Ω1 !! k = None).
    { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
    destruct NEW as (k& NEWk).
    assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
    iMod (osat_alloc_obl_discharged _ k (measure_rep ℓ ((1 ⊕ ▽) × μ)%M) with "S")
      as "(S& #Gwf& #Ge& #Gu& Gf& %OStep)". 1: auto.
    iMod (owit_alloc_witness_discharged _ k (η (measure_rep ℓ ((1 ⊕ ▽) × μ)%M)) with "[$W $Gu]") as "(W& #Ww)".
    { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
    iPoseProof (oassigned_add_obl with "[$A $Ge Gu]") as "A".
    { iRight. iFrame "Gu". }
    iPoseProof (oforest_alloc_discharged _ _ k with "G") as "G"; first done.
    set (Ω2:=(<[k:=(obl_discharged)]> Ω1)).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { apply obls_lef_obls_le, obls_ndf_obls_lef. by apply obls_ndf_insert_fresh. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. by apply obls_ndf_insert_fresh. }
    iIntros (W2 [WStep GWI2]) "!>".
    iPoseProof (owit_mon _ W2 with "W") as "W".
    { eapply wits_ndf_insert_wits_mon; [exact GWI|exact NEWk|exact WStep|exact GWI2|].
      intros w2 Hw2. specialize (GWI2 k). rewrite lookup_insert_eq Hw2 in GWI2.
      inversion GWI2; subst. by destruct w2. }
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. iFrame. }
    iPoseProof (temporal_elim with "HG2 [$SI $HI $S $O $A $G $W $HQ]") as "#HQi". 1: eauto.
    rewrite /model_interp. iFrame "HI S O A G W". iSplitR; first eauto.
    iModIntro. iMod "close" as "_". iModIntro. iFrame "SI TI HQ". iExists k. iFrame "Ge Ww Gf Gu".
    iSplitR; last (iExists _; iFrame "Gwf").
    iIntros (E' N P).
    iMod (oblG_inv_alloc_discharged _ N _ _ P False with "[$Gu]") as "#GVar"; cycle 1.
    { iFrame "GVar". done. }
    iFrame "Eo HQi".
  Qed.
  Lemma untilI_discharged_alloc E ℓ μ (Q : iProp Σ) :
    Q -∗
    |={E}=>m Q ∗ ∃ k, oblP_discharged k ∗
                        (∀ E' N (P : iProp Σ), |={E'}=> oblP_inv N k P (until_disch k (tps_sem Q))) ∗
                        oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof. iIntros "HQ". iApply (untilI_discharged_alloc_guar with "[] HQ"). iApply temporal_sem. Qed.

  (** Discharge: [P] is taken out of the until; once [Q] holds, the obligation [k] (a
      childless child of [p]) is discharged, and the record of [G2] at the discharge position
      (from [Q] and its stored guarantee) is left in the invariant. *)
  Lemma untilI_guar_discharge E N k (P Q : iProp Σ) G1 G2 :
    ↑N ⊆ E →
    untilI_guar N k 1 P Q G1 G2 ={E,E ∖ ↑N}=∗
    ▷ (P ∗ ∀ p K, ⌜k ∈ K⌝ → parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
         ∀ E', |={E'}=>m |={E ∖ ↑N,E}=> (Q ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k)).
  Proof.
    rewrite untilI_guar_unfold. iIntros (HN) "(Oa& #U)".
    iPoseProof (untilI_guar_pers_inv with "U") as "#OI".
    iDestruct (untilI_guar_pers_temporal with "U") as "[_ #HG2]".
    iMod (oblP_inv_acc_assigned with "OI") as "H"; first done.
    iDestruct ("H" with "Oa") as "[H ACC]".
    iModIntro. iNext. iDestruct "H" as "(Oa1& Oa2& $)". iCombine "Oa1 Oa2" as "Oa".
    iIntros (p K Hk) "Kp Kk HQ %E'".
    iMod (obl_discharge_leaf with "Kp Kk Oa") as "[$ #D]"; first done.
    iDestruct (oblP_discharged_unfold with "D") as "[#Oe #Od]".
    iMod (sfmupd_read _ (Q ∗ until_disch k G2) with "[HQ]") as "[HQ #R]".
    { iIntros (h n σ Θ κs g i Ω W) "HI TI MI".
      iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#TQ".
      iDestruct "MI" as "(MHI& S& MI)".
      iDestruct (osat_lookup_discharged with "[$S $Oe $Od]") as %Hkd.
      iPoseProof (model_history_interp_event_obl_now with "MHI") as "#EF"; first exact Hkd.
      iFrame "MHI S MI". iModIntro. iFrame "HI TI HQ". iExists n, i, Ω. iFrame "EF TQ". }
    iModIntro. iMod ("ACC" with "[]") as "_".
    { iNext. rewrite oblP_variant_unfold. iRight. iFrame "D R". }
    iModIntro. iFrame "HQ D".
  Qed.
  Lemma untilI_discharge E N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    untilI N k 1 P Q ={E,E ∖ ↑N}=∗
    ▷ (P ∗ ∀ p K, ⌜k ∈ K⌝ → parP_kids p K -∗ oblP_kids k ∅ -∗ Q -∗
         ∀ E', |={E'}=>m |={E ∖ ↑N,E}=> (Q ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k)).
  Proof. rewrite untilI_guar_canonical. apply untilI_guar_discharge. Qed.

  (** Access rules *)
  Lemma untilI_guar_discharged_false N k q P Q G1 G2 :
    untilI_guar N k q P Q G1 G2 -∗ oblP_discharged k -∗ False.
  Proof.
    rewrite !untilI_guar_unfold. iIntros "[Oa _] #Of".
    iPoseProof (oblP_assigned_discharged_false with "Oa Of") as "%". done.
  Qed.
  Lemma untilI_discharged_false N k q P Q :
    untilI N k q P Q -∗ oblP_discharged k -∗ False.
  Proof. rewrite untilI_guar_canonical. apply untilI_guar_discharged_false. Qed.

  Lemma untilI_guar_acc E N k q P Q G1 G2 :
    ↑N ⊆ E →
    untilI_guar N k q P Q G1 G2 ={E,E ∖ ↑N}=∗
    ▷ (P ∗ (▷ P ={E ∖ ↑N,E}=∗ untilI_guar N k q P Q G1 G2)).
  Proof.
    rewrite !untilI_guar_unfold. iIntros (Hmask) "(Oa& #U)".
    iPoseProof (untilI_guar_pers_inv with "U") as "#OI".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: set_solver.
    iPoseProof ("H" with "Oa") as "[H ACC]".
    iModIntro. iNext. iDestruct "H" as "(Oa& Oa2& $)". iIntros "HP". iFrame "Oa U". iApply "ACC".
    iNext. iApply oblP_variant_unfold. iLeft. iFrame.
  Qed.
  Lemma untilI_acc E N k q P Q :
    ↑N ⊆ E →
    untilI N k q P Q ={E,E ∖ ↑N}=∗
    ▷ (P ∗ (▷ P ={E ∖ ↑N,E}=∗ untilI N k q P Q)).
  Proof. rewrite untilI_guar_canonical. apply untilI_guar_acc. Qed.

  (** Discharge with the right formula at hand, using a later credit (the left formula is
      dropped). *)
  Lemma untilI_guar_discharge_lc E N k p K P Q G1 G2 :
    ↑N ⊆ E → k ∈ K →
    £ (2 : Ord.t) -∗ parP_kids p K -∗ oblP_kids k ∅ -∗ untilI_guar N k 1 P Q G1 G2 -∗ Q -∗
    |={E}=>m Q ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof.
    iIntros (Hmask Hk) "LC Kp Kk HU HQ".
    iMod (untilI_guar_discharge with "HU") as "HU"; first set_solver.
    iPoseProof (tlc_split_one with "LC") as "[_ LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iDestruct "HU" as "[_ HU]". iPoseProof ("HU" $! p K Hk with "Kp Kk HQ") as "HU".
    iMod ("HU" $! (E ∖ ↑N)) as "HU".
    iMod "HU" as "($& $& $)". done.
  Qed.

  (** Discharge a finally with its right formula at hand, using a later credit. *)
  Lemma finallyI_discharge E N k p K Q :
    ↑N ⊆ E → k ∈ K →
    £ (2 : Ord.t) -∗ parP_kids p K -∗ oblP_kids k ∅ -∗ finallyI N k 1 Q -∗ Q -∗
    |={E}=>m Q ∗ parP_kids p (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof. rewrite /finallyI untilI_guar_canonical. apply untilI_guar_discharge_lc. Qed.

  (** The same, with the children as [untilI_alloc] returns them. *)
  Lemma finallyI_discharge' E N k p K (Q : iProp Σ) :
    ↑N ⊆ E → k ∉ K →
    £ (2 : Ord.t) -∗ parP_kids p ({[k]} ∪ K) -∗ oblP_kids k ∅ -∗ finallyI N k 1 Q -∗ Q -∗
    |={E}=>m Q ∗ parP_kids p K ∗ oblP_discharged k.
  Proof.
    iIntros (HN Hk) "LC Kp Kk HF HQ".
    iMod (finallyI_discharge with "LC Kp Kk HF HQ") as "($& Kp& $)"; [done|set_solver|].
    assert (({[k]} ∪ K) ∖ {[k]} = K) as -> by set_solver. done.
  Qed.

End until_rules.

Section state_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma temporal_state (φ : state Λ → thread_pool Λ → Prop) (P : iProp Σ) :
    (∀ σ Θ κs, state_interp σ Θ κs ∗ P ⊢ ⌜φ σ Θ⌝) → ⊢ P ⊨ₜ tps_state φ.
  Proof.
    iIntros (Hφ). iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& _& HP)".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iAssert (⌜φ σ Θ⌝)%I with "[HI HP]" as %Hs.
    { rewrite /history_interp. iDestruct "HI" as "(_& _& SI)". iApply Hφ. iFrame. }
    iApply tguar_intro.
    iIntros "!>" (Sys l h' g v2 Ω2 W' τf γ σ' Θ' κs') "_ %H _ (HI'& MI& Sys)".
    destruct H as (BEH& FS& LB& HIST).
    iPoseProof (history_interp_hG_event_lookup with "[$HI' $HE]") as "%Hh".
    apply HIST in Hh as [? Hτ]. simpl. rewrite Hτ. done.
  Qed.

End state_rules.

Section impl_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  (** A guarantee extends to an implication whose complete antecedent, together with it,
      entails the consequent. With a pure antecedent this is [temporal_impl] weakened. *)
  Lemma temporal_impl_intro P A H G `{!TpsComplete A} :
    tps_le (tps_and A H) G → P ⊨ₜ H ⊢ P ⊨ₜ tps_impl A G.
  Proof. intros HG. by apply temporal_weaken, tps_impl_intro. Qed.

  Lemma temporal_impl_weaken P A G : P ⊨ₜ G ⊢ P ⊨ₜ tps_impl A G.
  Proof. apply temporal_weaken, tps_impl_intro_le. Qed.

End impl_rules.

(** ** Certification

    At a position, a run opens every registered item and produces a later-guarded record of
    each content. The contents stay in their invariants. *)
Section certification.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Local Lemma until_cert_assigned k (P R : iProp Σ) G1 G2 h n σ Θ κs g v Ω W fu o :
    Ω !! k = Some (obl_assigned fu o) →
    ▷ (P ⊨ₜ G1) -∗
    ▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ R)) ∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) -∗
    ▷ (tguar G1 n ∨ tguar G2 n).
  Proof.
    iIntros (Hk) "#HG (Var& HI& MI)". iNext. iDestruct "Var" as "[[_ HP]|[Of _]]".
    - iLeft. iApply (temporal_elim P G1 with "HG [$HI $MI $HP]").
    - iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "Of". iDestruct "Of" as "[#Oe #Of]".
      iDestruct (osat_lookup_discharged with "[$S $Oe $Of]") as %H. rewrite Hk in H. done.
  Qed.

  Local Lemma until_cert_discharged k (P : iProp Σ) G2 h n σ Θ κs g v Ω W :
    Ω !! k = Some obl_discharged →
    ▷ ((oblP_assigned k (1/2) ∗ P) ∨ (oblP_discharged k ∗ until_disch k G2)) ∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) -∗
    ▷ (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n').
  Proof.
    iIntros (Hk) "(Var& HI& MI)". iNext. iDestruct "MI" as "(MHI& S& _)".
    iDestruct "Var" as "[[Oa _]|[_ R]]".
    - iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "[#Oe Oa]".
      iDestruct (osat_lookup_assigned with "[$S $Oe $Oa]") as %(?&?&H). rewrite Hk in H. done.
    - iDestruct "R" as "(%n'& %i'& %Ω'& #EF& #TF)".
      iDestruct (event_obl_model_history_interp_lookup with "[$MHI $EF]") as %(_& _& _& Hn& _).
      iExists n', i', Ω'. iFrame "EF TF". done.
  Qed.

  (** The certificate of one registered item. *)
  Lemma cert_of_handle n e h σ Θ κs g v Ω W :
    treg_handle e -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤}=∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ cert n e.
  Proof.
    iIntros "#Hd HI MI". destruct e; simpl.
    - by iFrame.
    - iDestruct "Hd" as "(%P& %G& #SP& #Hinv& #HG)".
      iMod (inv_acc with "Hinv") as "[HP Hclose]"; first done.
      iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#C".
      iMod ("Hclose" with "HP") as "_". iModIntro. iFrame "HI MI". iExists _. iFrame "SP C".
    - iDestruct "Hd" as "(%P& %G1& %G2& #SP& #SQ& #OI& #HG)".
      iAssert (⌜∃ o, Ω !! k = Some o⌝)%I as %[o Hk].
      { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "OI". iDestruct "OI" as "[#Oe _]".
        iDestruct (osat_elem_lookup with "[$S $Oe]") as "[%H|[_ %H]]"; iPureIntro.
        - destruct H as (?&?&?). eauto.
        - eauto. }
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first done.
      destruct o.
      + iPoseProof (until_cert_assigned k P _ G1 G2 with "HG [$Var $HI $MI]") as "#C"; first done.
        iMod ("ACC" with "[Var]") as "_"; first by iNext; iApply oblP_variant_unfold.
        iModIntro. iFrame "HI MI". iExists _, _. iFrame "SP SQ". by iLeft.
      + iPoseProof (until_cert_discharged with "[$Var $HI $MI]") as "#C"; first done.
        iMod ("ACC" with "[Var]") as "_"; first by iNext; iApply oblP_variant_unfold.
        iModIntro. iFrame "HI MI". iExists _, _. iFrame "SP SQ". by iRight.
  Qed.

  Lemma certify_entries n l h σ Θ κs g v Ω W :
    treg_entries treg_handle l -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤}=∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ [∗ list] pe ∈ l, cert n pe.2.
  Proof.
    iIntros "#Hl HI MI". iInduction l as [|pe l] "IH".
    - iModIntro. iFrame. done.
    - rewrite /treg_entries !big_sepL_cons. iDestruct "Hl" as "[[_ #Hd] #Hl']".
      iMod (cert_of_handle with "Hd HI MI") as "(HI& MI& #C)".
      iMod ("IH" with "Hl' HI MI") as "($& $& #Cs)". iModIntro. iFrame "C Cs".
  Qed.

  (** The check at position [n]: the marker is appended to the registry and every entry is
      certified. The lower bound of the marked registry and the certificates form the
      bundle for [n]. *)
  Lemma treg_mark n l h σ Θ κs :
    reg_auth l -∗ treg_entries treg_handle l -∗ history_interp h n σ Θ κs ==∗
    history_interp h n σ Θ κs ∗ reg_auth (l ++ [(n, RMark)]) ∗
    treg_entries treg_handle (l ++ [(n, RMark)]) ∗ reg_lb (l ++ [(n, RMark)]).
  Proof.
    iIntros "Ha #Hl HI".
    iDestruct (treg_entries_bound with "Hl HI") as %Hb.
    iMod (reg_auth_append l n RMark with "Ha") as "[Ha #Hj]"; first done.
    iDestruct (history_interp_hG_event_now with "HI") as "#Hnow".
    iDestruct (reg_auth_lb with "Ha") as "#Hlb".
    iModIntro. iFrame "HI Ha Hlb".
    rewrite /treg_entries big_sepL_app big_sepL_singleton. iFrame "Hl". iSplit; [by iExists _|done].
  Qed.

  Lemma bundle_intro n l :
    last l = Some (n, RMark) →
    reg_lb l -∗ ([∗ list] pe ∈ l, cert n pe.2) -∗ bundle l n.
  Proof.
    iIntros (Hlast) "#Hlb #Cs". iEval (rewrite /cert) in "Cs". rewrite /bundle /bundle_pre.
    iFrame "Hlb". iSplit; first done. iFrame "Cs".
  Qed.

  (** The check as a whole: from the registry state and the interpretations at [n], the
      bundle for [n] and the state back. *)
  Lemma treg_check n h σ Θ κs g v Ω W :
    treg_state -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤}=∗
    treg_state ∗ history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ ∃ l, bundle l n.
  Proof.
    iIntros "(%l& Ha& #Hl) HI MI".
    iMod (treg_mark n l with "Ha Hl HI") as "(HI& Ha& #Hl'& #Hlb)".
    iMod (certify_entries n _ with "Hl' HI MI") as "(HI& MI& #Cs)".
    iPoseProof (bundle_intro n _ with "Hlb Cs") as "#B"; first by rewrite last_snoc.
    iModIntro. iFrame "HI MI B". iExists _. iFrame "Ha Hl'".
  Qed.

End certification.

(** ** Reading the registered structures off a run

    For any system satisfying the one-step property: the always of a registered invariant and
    the until of a registered obligation invariant. The loops take the certificate of the
    structure they read from the bundle of each position. *)
Section loops.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Local Notation sysT := (nat → state Λ → thread_pool Λ → list (observation Λ) → iProp Σ).

  Lemma behavior_S n (τf : nat → trace_state Λ) : behavior (n, τf) → behavior (S n, τf).
  Proof. intros BEH. inversion BEH. by subst. Qed.

  Local Lemma model_interp_event_obl k o g v Ω W n D :
    Ω !! k = Some o → model_interp g v Ω W n D ⊢ event_obl v (n, Ω) k o.
  Proof. iIntros (Hk) "(MHI& _)". by iApply model_history_interp_event_obl_now. Qed.

  (** The certificate of a registered always at a position [n] after its registration
      position [r]: from the bundle, or, at [r] itself, the allocation record. *)
  Lemma bundle_always_cert l n j r N γ G :
    r ≤ n →
    bundle l n -∗ reg_idx j r (RAlways N γ) -∗ saved_ti γ (tps_ti G) -∗
    (⌜r = n⌝ -∗ ▷ tguar G n) -∗ ▷ tguar G n.
  Proof.
    iIntros (Hrn) "#B #Hj #Hγ AC". rewrite /bundle /bundle_pre. iDestruct "B" as "(#Hlb& %Hlast& #Cs)".
    iDestruct (reg_idx_lb_pos with "Hlb Hj") as %[Hin|Hle]; first done.
    - iDestruct (big_sepL_lookup with "Cs") as "Cj"; first done. simpl.
      iDestruct "Cj" as (f) "[#Hf #Cj]". iDestruct (saved_ti_agree_fun with "Hf Hγ") as "#Heq".
      iNext. rewrite /tguar. iApply (tguar_ti_eq with "Heq Cj").
    - iApply "AC". iPureIntro. lia.
  Qed.

  (** The same for an until. *)
  Lemma bundle_until_cert l n j r N k γP γQ G1 G2 :
    r ≤ n →
    bundle l n -∗ reg_idx j r (RUntil N k γP γQ) -∗
    saved_ti γP (tps_ti G1) -∗ saved_ti γQ (tps_ti G2) -∗
    (⌜r = n⌝ -∗ ▷ (tguar G1 n ∨ tguar G2 n)) -∗
    ▷ (tguar G1 n ∨ tguar G2 n) ∨
    ▷ (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n').
  Proof.
    iIntros (Hrn) "#B #Hj #HγP #HγQ AC". rewrite /bundle /bundle_pre. iDestruct "B" as "(#Hlb& %Hlast& #Cs)".
    iDestruct (reg_idx_lb_pos with "Hlb Hj") as %[Hin|Hle]; first done.
    - iDestruct (big_sepL_lookup with "Cs") as "Cj"; first done. iEval (simpl) in "Cj".
      iDestruct "Cj" as (fP fQ) "(#HfP& #HfQ& [Cj|Cj])".
      + iLeft. iDestruct (saved_ti_agree_fun with "HfP HγP") as "#HeqP".
        iDestruct (saved_ti_agree_fun with "HfQ HγQ") as "#HeqQ".
        iNext. rewrite /tguar. iDestruct "Cj" as "[Cj|Cj]".
        * iLeft. iApply (tguar_ti_eq with "HeqP Cj").
        * iRight. iApply (tguar_ti_eq with "HeqQ Cj").
      + iRight. iDestruct (saved_ti_agree_fun with "HfQ HγQ") as "#HeqQ".
        iNext. iDestruct "Cj" as (n' i' Ω'') "(%& #EF& Cj)". iExists n', i', Ω''. iFrame "EF".
        iSplit; first done. rewrite /tguar. iApply (tguar_ti_eq with "HeqQ Cj").
    - iLeft. iApply "AC". iPureIntro. lia.
  Qed.

  (** One iteration of a loop, in the shape of the step-indexed readings: the check gives
      the bundle, from which the certificate [C] of the structure being read is taken; the
      shape's later strips its later; the step gives the system at [S n], the facts about
      the step and [c] later credits to the continuation. *)
  Lemma sys_step_iter (Sys : sysT) (c : nat) h n σ Θ κs g v Ω W τf γ (C Φ : iProp Σ) :
    sys_step Sys -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
    (∀ l, bundle l n -∗ ▷ C) -∗
    ▷ (∀ l σ' Θ' κs' g' v' Ω' W' γ',
       ⌜behavior (S n, τf) ∧ beh_fscnt (S n, τf) γ' ∧ owit_inv_lb (fair_sched_fun γ') Ω' W' ∧
        hist_trace (h ++ [(σ', Θ', κs')]) τf ∧ obls_drop (fair_sched_fun γ) (fair_sched_fun γ') Ω Ω'⌝ -∗
       bundle l n -∗ C -∗ £n c -∗
       history_interp (h ++ [(σ', Θ', κs')]) (S n) σ' Θ' κs' ∗ model_interp g' v' Ω' W' (S n) (dom Θ') ∗
       Sys (S n) σ' Θ' κs' -∗
       |={⊤}=> Φ) -∗
    |={⊤,∅}=> ▷ |={∅,⊤}=> |={⊤,∅}=> ALC (|={∅,⊤}=> Φ).
  Proof.
    iIntros "#ST %H Sys HC K". rewrite /sys_step /sys_step_pre.
    iMod ("ST" $! c with "[//] Sys") as (l) "[#B Step]".
    iDestruct ("HC" with "B") as "C".
    iModIntro. iNext. iMod "Step". iModIntro. iMod "Step". iModIntro.
    iApply (ALC_wand with "[K C] Step").
    iIntros ">(%σ'& %Θ'& %κs'& %g'& %v'& %Ω'& %W'& %γ'& %Hf& LC& HI& MI& Sys)".
    iApply ("K" with "[//] B C LC [$HI $MI $Sys]").
  Qed.

  (** *** The always loop *)
  Lemma always_run (Sys : sysT) N γ G j r :
    sys_step Sys -∗ reg_idx j r (RAlways N γ) -∗ saved_ti γ (tps_ti G) -∗
    ∀ h n σ Θ κs g v Ω W τf γ',
      ⌜r < n ∧ behavior (n, τf) ∧ beh_fscnt (n, τf) γ' ∧ owit_inv_lb (fair_sched_fun γ') Ω W ∧ hist_trace h τf⌝ -∗
      history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
      ti_always (tps_ti G) (ti_pure True) (n, τf).
  Proof.
    iIntros "#ST #Hj #Hγ" (h n σ Θ κs g v Ω W τf γ') "%H Sys".
    iLöb as "IH" forall (h n σ Θ κs g v Ω W τf γ' H).
    destruct H as (Hrn& BEH& FS& LB& HIST).
    rewrite ti_always_unfold /ti_always_pre.
    iApply (sys_step_iter Sys 0 _ _ _ _ _ _ _ _ _ _ _ (tguar G n) with "ST [%] Sys [] []").
    { split_and!; done. }
    { iIntros (l) "#B". iApply (bundle_always_cert with "B Hj Hγ []"); first lia.
      iIntros (?). lia. }
    iIntros "!>" (l σ' Θ' κs' g' v' Ω' W' γ'') "%Hstep #B #C _ Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& DROP).
    iModIntro. iSplit; [|iSplit; first done].
    - iApply (tguar_elim with "C ST [%] B Sys"). split_and!; done.
    - unfold trace_next. simpl. iApply ("IH" with "[%] Sys"). split_and!; [lia|done..].
  Qed.

  (** The registered structures guarantee the always and the until of their stored
      readings. *)
  Lemma temporal_always_guar N P G : ⊢ alwaysI_guar N P G ⊨ₜ tps_always G.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& #A)". rewrite alwaysI_guar_unfold.
    iDestruct "A" as (j r γ st) "(#Hj& #HE& #Hγ& #Hinv& #HG& #AC)".
    iDestruct (history_interp_hG_event_lookup with "[$HI $HE]") as %Hr.
    iDestruct (history_interp_wf with "HI") as %[Hlen _].
    assert (Hrn : r ≤ n) by (apply lookup_lt_Some in Hr; lia).
    iApply tguar_intro.
    iIntros "!>" (Sys l h' g v' Ω' W' τf γ' σ' Θ' κs') "#ST %Hf #B Sys".
    destruct Hf as (BEH& FS& LB& HIST).
    iDestruct (bundle_always_cert with "B Hj Hγ []") as "#C"; first done.
    { iIntros (->). done. }
    rewrite /= ti_always_unfold /ti_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iApply ALC_intro. iMod "close" as "_". iModIntro.
    iSplit; [|iSplit; first done].
    - iApply (tguar_elim with "C ST [%] B Sys"). split_and!; done.
    - iApply (always_run with "ST Hj Hγ [%] Sys"). simpl.
      split_and!; [lia|by apply behavior_S|exact FS|done|done].
  Qed.

  Lemma temporal_always_as N P V : ⊢ alwaysI_as N P V ⊨ₜ tps_always (tps_sem V).
  Proof. apply temporal_always_guar. Qed.
  Lemma temporal_always N P : ⊢ alwaysI N P ⊨ₜ tps_always (tps_sem P).
  Proof. apply temporal_always_as. Qed.

  (** *** The until loop

      Once the obligation is discharged, the record of the right formula at the current
      position is at hand: step, and decide with it. *)
  Lemma until_run_discharged (Sys : sysT) (fP : tiProp Λ Σ) G2 a h n σ Θ κs g v Ω W τf γ :
    sys_step Sys -∗ tguar G2 n -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
    ti_until Ord.lt a fP (tps_ti G2) (n, τf).
  Proof.
    iIntros "#ST #TQ %H Sys". destruct H as (BEH& FS& LB& HIST).
    rewrite ti_until_unfold /ti_until_pre.
    iApply (sys_step_iter Sys 0 _ _ _ _ _ _ _ _ _ _ _ True%I with "ST [%] Sys [] []").
    { split_and!; done. }
    { by iIntros (l) "_". }
    iIntros "!>" (l σ' Θ' κs' g' v' Ω' W' γ') "%Hstep #B _ _ Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& DROP).
    iModIntro. iLeft. iApply (tguar_elim with "TQ ST [%] B Sys"). split_and!; done.
  Qed.

  (** While the obligation is assigned, with the measure of its state at the check: the
      bundle decides which content holds at [n]; the obligation at [S n], read with a credit
      of the step, decides the continuation. *)
  Lemma until_run (Sys : sysT) N k γP γQ j r (P : iProp Σ) G1 G2 :
    sys_step Sys -∗ reg_idx j r (RUntil N k γP γQ) -∗
    saved_ti γP (tps_ti G1) -∗ saved_ti γQ (tps_ti G2) -∗
    oblP_inv N k P (until_disch k G2) -∗
    ∀ h n σ Θ κs g v Ω W τf γ fu o,
      ⌜r < n ∧ behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
       hist_trace h τf ∧ Ω !! k = Some (obl_assigned fu o)⌝ -∗
      history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ Sys n σ Θ κs -∗
      ti_until Ord.lt (Ord.S (fair_sched_fun γ o fu)) (tps_ti G1) (tps_ti G2) (n, τf).
  Proof.
    iIntros "#ST #Hj #HγP #HγQ #OI". iIntros (h n σ Θ κs g v Ω W τf γ fu o) "%H Sys".
    iLöb as "IH" forall (h n σ Θ κs g v Ω W τf γ fu o H).
    destruct H as (Hrn& BEH& FS& LB& HIST& Hk).
    iAssert (event_obl v (n, Ω) k (obl_assigned fu o))%I as "#EA".
    { iDestruct "Sys" as "(_& MI& _)". by iApply (model_interp_event_obl with "MI"). }
    rewrite ti_until_unfold /ti_until_pre.
    iApply (sys_step_iter Sys 1 _ _ _ _ _ _ _ _ _ _ _
              ((tguar G1 n ∨ tguar G2 n) ∨
               (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n'))%I
              with "ST [%] Sys [] []").
    { split_and!; done. }
    { iIntros (l) "#B". iDestruct (bundle_until_cert with "B Hj HγP HγQ []") as "[C|C]"; first lia.
      - iIntros (?). lia.
      - iNext. by iLeft.
      - iNext. by iRight. }
    iIntros "!>" (l σ' Θ' κs' g' v' Ω' W' γ') "%Hstep #B #C LC Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& DROP).
    iDestruct "C" as "[[TrecP|TrecQ]|(%n'& %i'& %Ω''& %Hn'& EF& TQ')]".
    - (* [P] holds at [n]: the obligation at [S n] decides *)
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first solve_ndisj.
      iMod (lc_fupd_elim_later with "LC Var") as "Var".
      iDestruct "Var" as "[[Oa' HP']|[Of R]]".
      + iAssert (⌜∃ fu' o', Ω' !! k = Some (obl_assigned fu' o')⌝)%I as %(fu'& o'& Hk').
        { iDestruct "Sys" as "(_& (_& S& _)& _)". iEval (unfold_opreds) in "Oa'". iDestruct "Oa'" as "[#Oe Oa']".
          iDestruct (osat_lookup_assigned with "[$S $Oe $Oa']") as %(?&?&?). eauto. }
        iMod ("ACC" with "[Oa' HP']") as "_".
        { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
        iModIntro. iRight. iSplit.
        { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply DROP; eauto. }
        unfold trace_next. simpl.
        iApply ("IH" with "[%] Sys"). split_and!; [lia|done..].
      + (* discharged during the step, at [n] (before the step) or at [S n] (after) *)
        iDestruct "R" as "(%n'& %i'& %Ω''& #EF& #TQ')".
        iAssert (⌜n' ≤ S n⌝)%I as %Hn'.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EF]") as %(_& _& _& ?& _). done. }
        iAssert (⌜n ≤ n'⌝)%I as %Hn.
        { destruct (le_gt_dec i' v) as [Hle|Hlt].
          - iDestruct (event_obl_compare i' v with "[$EF $EA]") as %(_& _& Hle'); first done. done.
          - iDestruct (event_obl_compare v i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
        iMod ("ACC" with "[Of]") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iFrame "Of". iExists n', i', Ω''. iFrame "EF TQ'". }
        iModIntro. destruct (decide (n' = n)) as [->|Hne].
        * iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
        * assert (n' = S n) as -> by lia.
          iRight. iSplit.
          { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
          iExists Ord.O. iSplit; first (iPureIntro; apply Ord.S_pos).
          unfold trace_next. simpl.
          iApply (until_run_discharged with "ST TQ' [%] Sys"). split_and!; [by apply behavior_S|done..].
    - (* [Q] holds at [n] *)
      iModIntro. iLeft. iApply (tguar_elim with "TrecQ ST [%] B Sys"). split_and!; done.
    - (* discharged before the check: the discharge was at [n] *)
      iAssert (⌜n ≤ n'⌝)%I as %Hn.
      { destruct (le_gt_dec i' v) as [Hle|Hlt].
        - iDestruct (event_obl_compare i' v with "[$EF $EA]") as %(_& _& Hle'); first done. done.
        - iDestruct (event_obl_compare v i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
      assert (n' = n) as -> by lia.
      iModIntro. iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
  Qed.

  Lemma temporal_until_guar N k q P Q G1 G2 : ⊢ untilI_guar N k q P Q G1 G2 ⊨ₜ tps_until G1 G2.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& U)". rewrite untilI_guar_unfold /untilI_guar_pers.
    iDestruct "U" as "[Oa #U]".
    iDestruct "U" as (j r γP γQ st v Ω1 fu1 o1) "(#Hj& #HE& #HγP& #HγQ& #OI& _& _& #EA1& #AC)".
    iAssert (⌜∃ fu o, Ω !! k = Some (obl_assigned fu o)⌝)%I as %(fu& o& Hk).
    { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "[#Oe Oa]".
      iDestruct (osat_lookup_assigned with "[$S $Oe $Oa]") as %(?&?&?). eauto. }
    iPoseProof (model_interp_event_obl with "MI") as "#EA"; first exact Hk.
    iDestruct (history_interp_hG_event_lookup with "[$HI $HE]") as %Hr.
    iDestruct (history_interp_wf with "HI") as %[Hlen _].
    assert (Hrn : r ≤ n) by (apply lookup_lt_Some in Hr; lia).
    iApply tguar_intro.
    iIntros "!>" (Sys l h' g v' Ω' W' τf γ' σ' Θ' κs') "#ST %Hf #B Sys".
    destruct Hf as (BEH& FS& LB& HIST).
    (* the certificate of this until for [n]: from the bundle, or its allocation records *)
    iDestruct (bundle_until_cert with "B Hj HγP HγQ []") as "#C"; first done.
    { iIntros (->). iNext. by iLeft. }
    rewrite /= /ti_exist. iExists (Ord.S (Ord.S (fair_sched_ub fu))).
    rewrite ti_until_unfold /ti_until_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    rewrite (ALC_credits _ _ (Ord.from_nat 1) (|={∅,⊤}=> _)%I). iApply ALC_intro. iIntros "LC".
    iMod "close" as "_".
    iDestruct "C" as "[[TrecP|TrecQ]|(%n'& %i'& %Ω''& %Hn'& #EF& #TQ')]".
    - (* [P] at [n]: the obligation at [S n] decides *)
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first solve_ndisj.
      iMod (lc_fupd_elim_later with "LC Var") as "Var".
      iDestruct "Var" as "[[Oa' HP']|[Of R]]".
      + iAssert (⌜∃ fu' o', Ω' !! k = Some (obl_assigned fu' o')⌝)%I as %(fu'& o'& Hk').
        { iDestruct "Sys" as "(_& (_& S& _)& _)". iEval (unfold_opreds) in "Oa'". iDestruct "Oa'" as "[#Oe Oa']".
          iDestruct (osat_lookup_assigned with "[$S $Oe $Oa']") as %(?&?&?). eauto. }
        iAssert (⌜(fu' w≤ fu)⌝)%I as %Hfu.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EA]") as %(_& _& _& _& [_ Hle]).
          iPureIntro. specialize (Hle _ _ _ Hk Hk'). destruct Hle as [[? _]|?]; [done|by apply WFOCM.lt_le]. }
        iMod ("ACC" with "[Oa' HP']") as "_".
        { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
        iModIntro. iRight. iSplit.
        { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply Ord.le_lt_lt; first apply fair_sched_fun_ub.
          eapply Ord.le_lt_lt; [by apply fair_sched_ub_le_proper|apply Ord.S_lt]. }
        unfold trace_next. simpl.
        iApply (until_run with "ST Hj HγP HγQ OI [%] Sys").
        split_and!; [lia|by apply behavior_S|done|done|done|done].
      + iDestruct "R" as "(%n'& %i'& %Ω''& #EF& #TQ')".
        iAssert (⌜n' ≤ S n⌝)%I as %Hn'.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EF]") as %(_& _& _& ?& _). done. }
        iAssert (⌜n ≤ n'⌝)%I as %Hn.
        { destruct (le_gt_dec i' i) as [Hle|Hlt].
          - iDestruct (event_obl_compare i' i with "[$EF $EA]") as %(_& _& Hle'); first done. done.
          - iDestruct (event_obl_compare i i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
        iMod ("ACC" with "[Of]") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iFrame "Of". iExists n', i', Ω''. iFrame "EF TQ'". }
        iModIntro. destruct (decide (n' = n)) as [->|Hne].
        * iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
        * assert (n' = S n) as -> by lia.
          iRight. iSplit.
          { iApply (tguar_elim with "TrecP ST [%] B Sys"). split_and!; done. }
          iExists Ord.O. iSplit; first (iPureIntro; apply Ord.S_pos).
          unfold trace_next. simpl.
          iApply (until_run_discharged with "ST TQ' [%] Sys").
          split_and!; [by apply behavior_S|done|done|done].
    - (* [Q] at [n] *)
      iModIntro. iLeft. iApply (tguar_elim with "TrecQ ST [%] B Sys"). split_and!; done.
    - (* discharged before the check: the discharge was at [n] *)
      iAssert (⌜n ≤ n'⌝)%I as %Hn.
      { destruct (le_gt_dec i' i) as [Hle|Hlt].
        - iDestruct (event_obl_compare i' i with "[$EF $EA]") as %(_& _& Hle'); first done. done.
        - iDestruct (event_obl_compare i i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
      assert (n' = n) as -> by lia.
      iModIntro. iLeft. iApply (tguar_elim with "TQ' ST [%] B Sys"). split_and!; done.
  Qed.

  Lemma temporal_until N k q P Q : ⊢ untilI N k q P Q ⊨ₜ tps_until (tps_sem P) (tps_sem Q).
  Proof. rewrite untilI_guar_canonical. apply temporal_until_guar. Qed.

  (** With valid guarantees of the contents. *)
  Lemma temporal_always_as_valid N P V G : (⊢ V ⊨ₜ G) → ⊢ alwaysI_as N P V ⊨ₜ tps_always G.
  Proof.
    intros HG. iApply (temporal_weaken _ (tps_always (tps_sem V))).
    { apply tps_always_mono. by apply tps_sem_le. }
    iApply temporal_always_as.
  Qed.
  Lemma temporal_always_valid N P G : (⊢ P ⊨ₜ G) → ⊢ alwaysI N P ⊨ₜ tps_always G.
  Proof. apply temporal_always_as_valid. Qed.
  Lemma temporal_until_valid N k q P Q G1 G2 :
    (⊢ P ⊨ₜ G1) → (⊢ Q ⊨ₜ G2) → ⊢ untilI N k q P Q ⊨ₜ tps_until G1 G2.
  Proof.
    intros HG1 HG2. iApply (temporal_weaken _ (tps_until (tps_sem P) (tps_sem Q))).
    { apply tps_until_mono; by apply tps_sem_le. }
    iApply temporal_until.
  Qed.

End loops.

(** ** Inferring guarantees

    Every iProp guarantees its canonical trace property [tps_sem], but that mentions the
    ghost-state instances; an adequacy needs one that does not. [IntoTemporal P G] computes
    such a [G] from the shape of [P]; any iProp at all guarantees [tps_true], which is the
    fallback for leaves without an instance. Formulas contain no inferred trace properties
    (the registered structures store [tps_sem]), so the search runs only when a guarantee is
    wanted, in one of two modes:
    - inference ([G] unknown: [tsem P], [tps_of P]), deterministic. For an existential the
      strongest guarantee of the body is inferred; if it does not depend on the witness the
      quantifier is a ghost one, otherwise it is trace-visible (types with the existential
      property) or the existential is dropped ([tps_true]);
    - checking against a given [G] ([into_temporal P G]), where an existential is
      trace-visible exactly when [G] is a [tps_exist] over the same type. *)
Class IntoTemporal `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (P : iProp Σ) (G : tps Λ Σ) :=
  into_temporal : ⊢ P ⊨ₜ G.
Global Arguments into_temporal {_ _ _ _} _ _ {_}.
Global Hint Mode IntoTemporal - - - - ! - : typeclass_instances.
(* The search compares guarantees by their formula and trace property: unfolding [temporal]
   when an instance does not match makes the failure very slow. *)
Global Typeclasses Opaque temporal.
(* Likewise for the connectives, which are records ([tps_true] and [tps_finally] stay
   abbreviations). User definitions of trace properties are still unfolded. *)
Global Typeclasses Opaque tps_pure tps_atomic tps_and tps_or tps_impl tps_forall tps_exist
  tps_always tps_until tps_state.

(** Big separating conjunctions guarantee the guarded family of their elements' guarantees. *)
Section big_op_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma temporal_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ) (G : K → A → tps Λ Σ) :
    (∀ k x, Φ k x ⊨ₜ G k x) -∗
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊨ₜ tps_forall (λ k, tps_forall (λ x, tps_impl ⌜m !! k = Some x⌝ (G k x))).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ k x, ⌜m !! k = Some x⌝ → Φ k x)%I with "[]").
    { iIntros "!> H" (k x Hk). by iApply (big_sepM_lookup with "H"). }
    iApply temporal_forall. iIntros (k). iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

  Lemma temporal_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → tps Λ Σ) :
    (∀ k x, Φ k x ⊨ₜ G k x) -∗
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊨ₜ tps_forall (λ k, tps_forall (λ x, tps_impl ⌜l !! k = Some x⌝ (G k x))).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ k x, ⌜l !! k = Some x⌝ → Φ k x)%I with "[]").
    { iIntros "!> H" (k x Hk). by iApply (big_sepL_lookup with "H"). }
    iApply temporal_forall. iIntros (k). iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

  Lemma temporal_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → tps Λ Σ) :
    (∀ x, Φ x ⊨ₜ G x) -∗
    ([∗ set] x ∈ X, Φ x) ⊨ₜ tps_forall (λ x, tps_impl ⌜x ∈ X⌝ (G x)).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ x, ⌜x ∈ X⌝ → Φ x)%I with "[]").
    { iIntros "!> H" (x Hx). by iApply (big_sepS_elem_of with "H"). }
    iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

End big_op_rules.

(** How an existential over a family of guarantees is guaranteed, when inferring. *)
Class SimplExist `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (G : X → tps Λ Σ) (G' : tps Λ Σ) :=
  simpl_exist (P : X → iProp Σ) : (∀ x, P x ⊨ₜ G x) ⊢ (∃ x, P x) ⊨ₜ G'.
Global Hint Mode SimplExist - - - - - ! - : typeclass_instances.

(** Existentials, dispatched on whether the target is known (hints after [into_temporal]).
    Records, so that a failing unification does not unfold them. *)
Class IntoTemporalExist `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (P : X → iProp Σ) (G : tps Λ Σ) :=
  { into_temporal_exist_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoTemporalExist - - - - - ! - : typeclass_instances.
(** Against a known target: trace-visible if the target is a [tps_exist] (possibly behind
    definitions), ghost otherwise. *)
Class IntoTemporalExistCheck `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} {X : Type} (P : X → iProp Σ) (G : tps Λ Σ) :=
  { into_temporal_exist_check_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoTemporalExistCheck - - - - - ! ! : typeclass_instances.

(** The trace property inferred for [P]. *)
Definition tsem `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (P : iProp Σ) {G : tps Λ Σ} `{!IntoTemporal P G} : tps Λ Σ := G.
Global Arguments tsem {_ _ _ _} _ {_ _}.

(** The inferred trace property of [P], computed so that it no longer mentions ghost-state
    instances: [Definition G : tps Λ Σ := ltac:(tps_of P).] in a section with the instances
    yields a [G] that can be used in an adequacy statement. *)
Ltac tps_of P := let G := eval cbv [tsem] in (tsem P%I) in exact G.

(** [t] is an evar, possibly applied: the target is unknown. *)
Ltac evar_headed t := idtac; lazymatch t with ?f _ => evar_headed f | _ => is_evar t end.

Section into_temporal.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : tps Λ Σ.

  (** The fallback, used through the hint below. *)
  Lemma into_temporal_default P : IntoTemporal P tps_true.
  Proof. apply temporal_true. Qed.
  Global Instance into_temporal_pure φ : IntoTemporal (⌜φ⌝ : iProp Σ) (tps_pure φ) | 10.
  Proof. apply temporal_pure. Qed.
  Global Instance into_temporal_sep P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∗ Q) (G1 ∧ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_sep; [iApply H1|iApply H2]. Qed.
  Global Instance into_temporal_and P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∧ Q) (G1 ∧ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_and; [iApply H1|iApply H2]. Qed.
  Global Instance into_temporal_or P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (P ∨ Q) (G1 ∨ G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. iApply temporal_or; [iApply H1|iApply H2]. Qed.

  Global Instance simpl_exist_ghost {X} G : SimplExist (λ _ : X, G) G | 0.
  Proof. intros P. iIntros "H". by iApply temporal_exist_ghost. Qed.
  Global Instance simpl_exist_visible {X} `{!TypeExistentialProperty X ordI} (G : X → tps Λ Σ) :
    SimplExist G (tps_exist G) | 10.
  Proof. intros P. iIntros "H". by iApply temporal_exist. Qed.
  (* Total, so that inference never backtracks into the body. *)
  Global Instance simpl_exist_true {X} (G : X → tps Λ Σ) : SimplExist G tps_true | 100.
  Proof. intros P. iIntros "_". iApply temporal_true. Qed.

  Global Instance into_temporal_exist {X} (P : X → iProp Σ) G :
    IntoTemporalExist P G → IntoTemporal (∃ x, P x) G | 10.
  Proof. by intros []. Qed.
  Lemma into_temporal_exist_infer {X} (P : X → iProp Σ) (Gx : X → tps Λ Σ) G :
    (∀ x, IntoTemporal (P x) (Gx x)) → SimplExist Gx G → IntoTemporalExist P G.
  Proof. intros H HS. constructor. unfold IntoTemporal in *. iApply HS. iIntros (x). iApply H. Qed.
  Lemma into_temporal_exist_check {X} (P : X → iProp Σ) G :
    IntoTemporalExistCheck P G → IntoTemporalExist P G.
  Proof. by intros [?]. Qed.
  Global Instance into_temporal_exist_visible_check {X} `{!TypeExistentialProperty X ordI}
    (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, IntoTemporal (P x) (G x)) → IntoTemporalExistCheck P (tps_exist G) | 0.
  Proof. intros H. constructor. unfold IntoTemporal in *. iApply temporal_exist. iIntros (x). iApply H. Qed.
  Global Instance into_temporal_exist_ghost_check {X} (P : X → iProp Σ) G :
    (∀ x, IntoTemporal (P x) G) → IntoTemporalExistCheck P G | 10.
  Proof. intros H. constructor. unfold IntoTemporal in *. iApply temporal_exist_ghost. iIntros (x). iApply H. Qed.

  Global Instance into_temporal_impl (φ : Prop) P G :
    IntoTemporal P G → IntoTemporal (⌜φ⌝ → P) (⌜φ⌝ → G) | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_impl. iApply H. Qed.
  Global Instance into_temporal_forall {X} (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, IntoTemporal (P x) (G x)) → IntoTemporal (∀ x, P x) (tps_forall G) | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_forall. iIntros (x). iApply H. Qed.
  Global Instance into_temporal_persistently P G :
    IntoTemporal P G → IntoTemporal (□ P) G | 10.
  Proof. intros H. unfold IntoTemporal in *. iApply temporal_persistently. iApply H. Qed.
  Global Instance into_temporal_alwaysI_guar N P G :
    IntoTemporal (alwaysI_guar N P G) (tps_always G) | 10.
  Proof. apply temporal_always_guar. Qed.
  Global Instance into_temporal_alwaysI_as N P V G :
    IntoTemporal V G → IntoTemporal (alwaysI_as N P V) (tps_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_always_as_valid. Qed.
  Global Instance into_temporal_alwaysI N P G :
    IntoTemporal P G → IntoTemporal (alwaysI N P) (tps_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_always_valid. Qed.
  Global Instance into_temporal_untilI_guar N k q P Q G1 G2 :
    IntoTemporal (untilI_guar N k q P Q G1 G2) (tps_until G1 G2) | 10.
  Proof. apply temporal_until_guar. Qed.
  Global Instance into_temporal_untilI N k q P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (untilI N k q P Q) (tps_until G1 G2) | 10.
  Proof. intros H1 H2. unfold IntoTemporal in *. by apply temporal_until_valid. Qed.
  Global Instance into_temporal_state_pred π : IntoTemporal (state_pred_interp π) (tps_atomic π) | 10.
  Proof. apply temporal_atomic. Qed.

  Global Instance into_temporal_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ)
    (G : K → A → tps Λ Σ) :
    (∀ k x, IntoTemporal (Φ k x) (G k x)) →
    IntoTemporal ([∗ map] k ↦ x ∈ m, Φ k x)
      (tps_forall (λ k, tps_forall (λ x, tps_impl ⌜m !! k = Some x⌝ (G k x)))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepM. iIntros (k x). iApply HG. Qed.
  Global Instance into_temporal_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → tps Λ Σ) :
    (∀ k x, IntoTemporal (Φ k x) (G k x)) →
    IntoTemporal ([∗ list] k ↦ x ∈ l, Φ k x)
      (tps_forall (λ k, tps_forall (λ x, tps_impl ⌜l !! k = Some x⌝ (G k x)))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepL. iIntros (k x). iApply HG. Qed.
  Global Instance into_temporal_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → tps Λ Σ) :
    (∀ x, IntoTemporal (Φ x) (G x)) →
    IntoTemporal ([∗ set] x ∈ X, Φ x) (tps_forall (λ x, tps_impl ⌜x ∈ X⌝ (G x))) | 10.
  Proof. intros HG. unfold IntoTemporal in *. iApply temporal_big_sepS. iIntros (x). iApply HG. Qed.

  Lemma tsem_temporal (Q : iProp Σ) G `{!IntoTemporal Q G} : ⊢ Q ⊨ₜ tsem Q.
  Proof. done. Qed.

End into_temporal.

(* Existentials. With an unknown target, the strongest guarantee of the body is inferred and
   then collapsed ([SimplExist]). With a known target, the body is checked against it
   ([IntoTemporalExistCheck]). *)
Global Hint Extern 0 (IntoTemporalExist _ ?G) =>
  evar_headed G; notypeclasses refine (into_temporal_exist_infer _ _ _ _ _) : typeclass_instances.
Global Hint Extern 0 (IntoTemporalExist _ ?G) =>
  assert_fails (evar_headed G);
  notypeclasses refine (into_temporal_exist_check _ _ _) : typeclass_instances.

(* The fallback, for an unknown target or [tps_true], and only once the formula and the
   ghost-state instances contain no evars (resolution is retried once they are solved). *)
Global Hint Extern 100 (@IntoTemporal ?Λ ?Σ ?Ht ?Hs ?P ?G) =>
  assert_fails (has_evar Λ); assert_fails (has_evar Σ); assert_fails (has_evar Ht); assert_fails (has_evar Hs);
  assert_fails (has_evar P);
  first [evar_headed G | unify G (@tps_true Λ Σ)];
  notypeclasses refine (into_temporal_default P) : typeclass_instances.

(** ** Examples and unit checks *)
Section examples.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  (** Ghost quantification over iProp, scoping over two temporal operators. *)
  Local Lemma ex_iprop N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ) ⊨ₜ
      (tps_always tps_true ∧ tps_finally tps_true).
  Proof.
    iApply temporal_exist_ghost. iIntros (Ψ).
    iApply temporal_sep; [iApply temporal_always_valid; apply temporal_true|].
    iApply temporal_until_valid; apply temporal_true.
  Qed.

  (** An invariant whose content changes over time, each content carrying its own guarantee. *)
  Local Lemma ex_dynamic_inv N G : ⊢ alwaysI N (∃ P : iProp Σ, P ∗ P ⊨ₜ G) ⊨ₜ tps_always G.
  Proof. iApply temporal_always_valid. iApply temporal_certified. Qed.

  (** The same guarantee, inferred. *)
  Local Lemma ex_iprop_inferred N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ) ⊨ₜ
      (tps_always tps_true ∧ tps_until (tps_pure True) tps_true).
  Proof. apply (into_temporal _ _). Qed.

  (** Trace-visible quantification over a small type is inferred when the guarantee of
      the body depends on the witness. *)
  Local Lemma ex_visible_inferred N (f : nat → Prop) :
    ⊢ (∃ n : nat, alwaysI N ⌜f n⌝) ⊨ₜ tps_exist (λ n : nat, tps_always (tps_pure (f n))).
  Proof. apply (into_temporal _ _). Qed.

  (** The inferred trace property as a closed term. *)
  Local Definition ex_tps_of N1 N2 k : tps Λ Σ :=
    ltac:(tps_of ((∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k 1 Ψ)%I)).
  Local Lemma ex_tps_of_eq N1 N2 k :
    ex_tps_of N1 N2 k = (tps_always tps_true ∧ tps_until (tps_pure True) tps_true)%S.
  Proof. done. Qed.

  (** A higher-order specification quantifies over the content together with its guarantee
      (the guarantee of the content of an [alwaysI] must be valid, not a hypothesis). *)
  Local Lemma ex_higher_order N G :
    ⊢ (∃ P : iProp Σ, alwaysI N (P ∗ P ⊨ₜ G)) ⊨ₜ tps_always G.
  Proof.
    iApply temporal_exist_ghost. iIntros (P). iApply temporal_always_valid.
    iApply (temporal_mono (∃ P, P ∗ P ⊨ₜ G)%I with "[]"); first by iIntros "!> H"; iExists P.
    iApply temporal_certified.
  Qed.

  (** A temporal antecedent used inside the logic: assuming that the run eventually reaches
      [π], the in-logic reading of that eventuality (with its measure) is available by
      completeness, here to strengthen a guarantee. *)
  Local Lemma ex_impl_temporal P π G :
    P ⊨ₜ G ⊢ P ⊨ₜ tps_impl (tps_finally (tps_atomic π)) (tps_and (tps_finally (tps_atomic π)) G).
  Proof.
    apply (temporal_impl_intro _ _ _ _ (tps_le_refl _)).
  Qed.

  (** The rule one might hope for, an iProp implication guaranteeing the implication of the
      guarantees, is unsound: it guarantees a trace property that no trace has. (The
      antecedent's resources are not determined by the trace.) *)
  Local Lemma naive_impl_rule_unsound :
    (∀ (P1 P2 : iProp Σ) G1 G2, (⊢ P1 ⊨ₜ G1) → (⊢ P2 ⊨ₜ G2) → ⊢ (P1 → P2) ⊨ₜ tps_impl G1 G2) →
    ⊢ True ⊨ₜ tps_impl tps_true (tps_pure False).
  Proof.
    intros Hrule.
    assert (HF : ∀ G, ⊢ (False : iProp Σ) ⊨ₜ G).
    { intros G. rewrite /temporal. iIntros "!>" (?????????) "(_& _& [])". }
    iApply (temporal_mono (False → False)%I with "[]"); first by iIntros "!> _ []".
    iApply Hrule; [apply temporal_true|apply HF].
  Qed.

  Local Lemma tps_impl_true_false_empty τ : ¬ tps_tr (tps_impl (Λ:=Λ) (Σ:=Σ) tps_true (tps_pure False)) τ.
  Proof. intros H. by apply H. Qed.

End examples.
