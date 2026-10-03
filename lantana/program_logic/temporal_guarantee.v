From iris.proofmode Require Import base proofmode classes.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.program_logic Require Export temporal_tps.
From transfinite.stepindex Require Import ordinals.
From lantana.base_logic Require Import satisfiable.
From lantana.algebra Require Import ordinal_existential_properties.
From lantana.prelude Require Import axioms.

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
    the adequacy proof registers every trace-visible structure ([alwaysI], [untilI]) in the
    registry (temporal_registry.v) and, at every position, certifies the content of each
    registered item as a later-guarded record. The step-indexed readings of always and until
    (adequacy.v) decide a position only after the step from it, so that a pre-step discharge
    at [n] is read off the obligation invariant at [S n].

    Contents: guarantees and records ([tguar]); the registered structures [alwaysI] and
    [untilI]; rules for the connectives; rules for [alwaysI] and [untilI]; adequacy;
    inference of guarantees ([IntoTemporal]).

    Limitations, by design:
    - A quantifier can be trace-visible ([tps_exist]) only over types with the existential
      property of the step index (nat, Z, loc, gname, ...): over larger types (iProp, tps) no
      sound adequacy could read the witness off the trace. Over those, existentials are ghost
      ([temporal_exist_ghost]): the guarantee of the body must not depend on the witness.
    - The trace property [G] of the adequacy is fixed at the meta level; dynamically created
      names reach it through trace-visible existentials, typically under a [finally]
      allocated at time 0 (see lantana_heap_lang/examples/flag_fork.v).
    - [tguar] mentions the running system ([lwp_fix]), so this layer is specific to Lantana's
      weakest precondition and to [ordSI].
    - [alwaysI] and [untilI] store the canonical trace properties [tps_sem] of their contents,
      so they are not contractive in them: recursion through a registered structure cannot be
      defined, and their rules take validity premises [(⊢ P ⊨ₜ G) → ...] rather than
      hypotheses [▷ (P ⊨ₜ G)]. Guarded recursion on trace properties is supported
      (temporal_fixpoint.v).
    - Allocating an [alwaysI] or an [untilI] registers it: the allocation rules are model
      updates ([|={E}=>g]) that take the registry [treg] and a later credit. *)

(** ** Guarantees *)

Section guarantee.
  Context `{!lantanaGS Λ Σ}.
  Implicit Types G : tps Λ Σ.
  Implicit Types P Q : iProp Σ.

  (** The running system: every thread runs its [lwp_fix]. *)
  Definition threads_run (s : stuckness)
    (TQ : gmap thread_id ((expr Λ) * (thread_id → val Λ → iProp Σ))) : iProp Σ :=
    [∗ map] i ↦ '(e, Q) ∈ TQ, match to_val e with
                              | Some v => (lift_term i Q) v
                              | None => lwp_fix s i ⊤ e (lift_term i Q)
                              end.

  (** The history [h] is the one of the trace [τf]. *)
  Definition hist_trace (h : list (state Λ * thread_pool Λ * list (observation Λ)))
    (τf : nat → (thread_pool Λ * state Λ) * thread_id * list (observation Λ)) : Prop :=
    ∀ n' σ' Θ' κs', h !! n' = Some (σ', Θ', κs') → ∃ i', τf n' = ((Θ', σ'), i', κs').

  Local Notation tgT := ((trace Λ -d> iPropO Σ) -d> nat -d> iPropO Σ).

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

  (** A record for [f] at [n]: given the bundle for [n] and a running system at [S n]
      consistent with the trace, [f] holds at [n] on the trace. *)
  Definition tguar_pre (tg : tgT) : tgT :=
    λ f n, (□ ∀ l s h TQ g v Ω W τf γ σ Θ κs,
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
       hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
      bundle_pre tg l n -∗
      (history_interp h (S n) σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W (S n) (dom Θ) ∗
      threads_run s TQ -∗
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

  Local Instance tguar_pre_contractive : Contractive tguar_pre.
  Proof.
    intros m tg1 tg2 Htg f n. rewrite /tguar_pre.
    do 29 f_equiv. by apply bundle_pre_contractive.
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

  (** Records of a trace property, the bundle and the certificates. *)
  Definition tguar G n : iProp Σ := tguar_ti (tps_ti G) n.
  Definition bundle l n : iProp Σ := bundle_pre tguar_ti l n.
  Definition cert n e : iProp Σ := cert_pre tguar_ti n e.
  (* Opaque for the proof mode: [iNext] must not strip the laters of the certificates. *)
  Global Typeclasses Opaque bundle cert.

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
  Global Instance temporal_persistent P G : Persistent (temporal P G).
  Proof. apply _. Qed.

  Lemma tguar_ti_intro f n :
    (□ ∀ l s h TQ g v Ω W τf γ σ Θ κs,
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
       hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
      bundle l n -∗
      (history_interp h (S n) σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W (S n) (dom Θ) ∗
      threads_run s TQ -∗
      f (n, τf)) ⊢ tguar_ti f n.
  Proof. by rewrite tguar_ti_unfold. Qed.

  Lemma tguar_ti_elim f l s h n TQ g v Ω W τf γ σ Θ κs :
    tguar_ti f n -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
     hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
    bundle l n -∗
    (history_interp h (S n) σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W (S n) (dom Θ) ∗
    threads_run s TQ -∗
    f (n, τf).
  Proof. rewrite tguar_ti_unfold. iIntros "#HG H #B W". by iApply ("HG" with "H B W"). Qed.

  Lemma tguar_intro G n :
    (□ ∀ l s h TQ g v Ω W τf γ σ Θ κs,
      ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
       hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
      bundle l n -∗
      (history_interp h (S n) σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W (S n) (dom Θ) ∗
      threads_run s TQ -∗
      tps_ti G (n, τf)) ⊢ tguar G n.
  Proof. apply tguar_ti_intro. Qed.

  (** Eliminating a record: against the bundle of its position and the system after the step. *)
  Lemma tguar_elim G l s h n TQ g v Ω W τf γ σ Θ κs :
    tguar G n -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
     hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
    bundle l n -∗
    (history_interp h (S n) σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W (S n) (dom Θ) ∗
    threads_run s TQ -∗
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
    iIntros (Hle) "#HG". iApply tguar_intro. iIntros "!>" (?????????????) "%H #B W".
    iApply Hle. by iApply (tguar_elim with "HG [//] B W").
  Qed.

End guarantee.

Notation "P ⊨ₜ G" := (temporal P%I G%S) (at level 70, format "P  ⊨ₜ  G") : bi_scope.

(** The canonical trace property of an iProp: the meet of all trace properties that it
    validly guarantees. Every iProp guarantees it ([temporal_sem]), and it implies each of
    them ([tps_sem_le]). The registered structures store it for their contents, so temporal
    formulas carry no trace-property annotations. *)
Definition tps_sem `{!lantanaGS Λ Σ} (Q : iProp Σ) : tps Λ Σ :=
  tps_forall (λ G : {G : tps Λ Σ | ⊢ Q ⊨ₜ G}, proj1_sig G).
(* Opaque for the proof mode: unification must not compare two [tps_sem] through their
   bodies (the index type is a proposition about the argument). *)
Global Typeclasses Opaque tps_sem.

(** Once discharged, the obligation invariant of an until keeps the record of its right
    formula at the discharge event. *)
Notation until_disch k G2 :=
  (∃ n' i' Ω', event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n')%I (only parsing).

(** ** The registered structures

    The registry invariant [treg] holds, for every registered item, its handle: the saved
    step-indexed readings of its contents and its invariant, which the adequacy proof opens
    at every position to certify the content. *)
Definition treg_handle `{!lantanaGS Λ Σ} (e : rentry) : iProp Σ :=
  match e with
  | RMark => True
  | RAlways N γ => ∃ (P : iProp Σ) (G : tps Λ Σ), saved_ti γ (tps_ti G) ∗ inv N P ∗ ▷ (P ⊨ₜ G)
  | RUntil N k γP γQ =>
      ∃ P Q : iProp Σ, saved_ti γP (tps_ti (tps_sem P)) ∗ saved_ti γQ (tps_ti (tps_sem Q)) ∗
        oblP_inv N k P Q (until_disch k (tps_sem Q))
  end.
Definition treg `{!lantanaGS Λ Σ} : iProp Σ := treg_inv treg_handle.

(** An invariant whose content is trace-visible through a guarantee [G] of its content [P]:
    the invariant, registered with the reading [G] and a (later-guarded) proof that the
    content guarantees [G], and the record of [G] at its registration position. The proof
    may be an iProp hypothesis available at registration: one that depends on a token
    ([alwaysI_register] with a view), or a closed one about a recursively defined structure
    (temporal_fixpoint.v). The common cases: [alwaysI N P] reads as the canonical trace
    property of [P]; a view [V] of [P] ([alwaysI_view], from [□ (P -∗ V)]) reads as that of
    [V]. Sealed: the proof mode must not unify two structures through their bodies. *)
Local Definition alwaysI_guar_def `{!lantanaGS Λ Σ} (N : namespace) (P : iProp Σ) (G : tps Λ Σ) : iProp Σ :=
  ∃ j r γ st, reg_idx j r (RAlways N γ) ∗ hG_event r st ∗
              saved_ti γ (tps_ti G) ∗ inv N P ∗ ▷ (P ⊨ₜ G) ∗ treg ∗ ▷ tguar G r.
Local Definition alwaysI_guar_aux : seal (@alwaysI_guar_def). Proof. by eexists. Qed.
Definition alwaysI_guar := alwaysI_guar_aux.(unseal).
Global Arguments alwaysI_guar {Λ Σ _} N P G.
Local Lemma alwaysI_guar_unseal : @alwaysI_guar = @alwaysI_guar_def.
Proof. rewrite -alwaysI_guar_aux.(seal_eq) //. Qed.
Lemma alwaysI_guar_unfold `{!lantanaGS Λ Σ} N P G :
  alwaysI_guar N P G = (∃ j r γ st, reg_idx j r (RAlways N γ) ∗ hG_event r st ∗
                        saved_ti γ (tps_ti G) ∗ inv N P ∗ ▷ (P ⊨ₜ G) ∗ treg ∗ ▷ tguar G r)%I.
Proof. by rewrite alwaysI_guar_unseal. Qed.
Definition alwaysI_view `{!lantanaGS Λ Σ} (N : namespace) (P V : iProp Σ) : iProp Σ :=
  alwaysI_guar N P (tps_sem V).
Definition alwaysI `{!lantanaGS Λ Σ} (N : namespace) (P : iProp Σ) : iProp Σ := alwaysI_view N P P.
(* Opaque for the proof mode: [iNext] must not unfold a structure to strip its inner later. *)
Global Typeclasses Opaque alwaysI_view alwaysI.

(** The persistent part of an until: its obligation invariant, registered, with the records
    of its contents at its allocation position, where its obligation was assigned. *)
Definition untilI_pers `{!lantanaGS Λ Σ} (N : namespace) (k : positive) (P Q : iProp Σ) : iProp Σ :=
  ∃ j r γP γQ st v Ω fu o,
    reg_idx j r (RUntil N k γP γQ) ∗ hG_event r st ∗
    saved_ti γP (tps_ti (tps_sem P)) ∗ saved_ti γQ (tps_ti (tps_sem Q)) ∗
    oblP_inv N k P Q (until_disch k (tps_sem Q)) ∗ treg ∗
    event_obl v (r, Ω) k (obl_assigned fu o) ∗ ▷ (tguar (tps_sem P) r ∨ tguar (tps_sem Q) r).
Global Typeclasses Opaque untilI_pers.

(** [P] until [Q] using namespace [N] and obligation [k]. *)
Local Definition untilI_def `{!lantanaGS Λ Σ} N k (b : bool) (q : Qp) (P Q : iProp Σ) : iProp Σ :=
  oblP_assigned k b (q/2)%Qp ∗ untilI_pers N k P Q.
(* Sealed: the proof mode splits it by fractions, and unification (e.g. in [iFrame]) does not
   unfold it. *)
Local Definition untilI_aux : seal (@untilI_def). Proof. by eexists. Qed.
Definition untilI := untilI_aux.(unseal).
Global Arguments untilI {Λ Σ _} N k b q P Q.
Local Lemma untilI_unseal : @untilI = @untilI_def.
Proof. rewrite -untilI_aux.(seal_eq) //. Qed.
Lemma untilI_unfold `{!lantanaGS Λ Σ} N k b q P Q :
  untilI N k b q P Q = (oblP_assigned k b (q/2)%Qp ∗ untilI_pers N k P Q)%I.
Proof. by rewrite untilI_unseal. Qed.

Definition finallyI `{!lantanaGS Λ Σ} N k (b : bool) (q : Qp) (Q : iProp Σ) : iProp Σ :=
  untilI N k b q True Q.

(** ** Rules *)

Section rules.
  Context `{!lantanaGS Λ Σ}.
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
    iIntros "!>" (?????????) "_". iApply tguar_intro. iIntros "!>" (?????????????) "_ _ _". done.
  Qed.

  Lemma temporal_pure (φ : Prop) : ⊢ ⌜φ⌝ ⊨ₜ tps_pure φ.
  Proof.
    iIntros "!>" (?????????) "(_& _& %Hφ)". iApply tguar_intro. iIntros "!>" (?????????????) "_ _ _". done.
  Qed.

  Lemma temporal_atomic π : ⊢ state_pred_interp π ⊨ₜ tps_atomic π.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& _& TL)".
    rewrite /history_interp. iDestruct "HI" as "(HI1& HI2& SI)".
    iPoseProof (state_interp_wf with "[$SI $TL]") as "%".
    iPoseProof (history_interp_event_pred_now with "[HI1 HI2 SI]") as "#TF". 1: done.
    { rewrite /history_interp. iFrame. }
    iApply tguar_intro.
    iIntros "!>" (l s h' TQ g v2 Ω2 W' τf γ σ' Θ' κs' (BEH& FS& LB& HIST& EQTQ)) "_ ([HI' SIa]& MI& WPs)".
    simpl. unfold ti_atomic. iPoseProof (event_pred_history_interp_lookup with "[$HI' $TF]") as "%H'".
    destruct H' as [H' ?]. simpl. apply HIST in H'. destruct H' as [? H']. rewrite H'. auto.
  Qed.

  Lemma temporal_and P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∧ Q) ⊨ₜ (G1 ∧ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& HPQ)".
    iPoseProof (temporal_elim with "HG1 [$HI $MI HPQ]") as "#T1"; first by iDestruct "HPQ" as "[$ _]".
    iPoseProof (temporal_elim with "HG2 [$HI $MI HPQ]") as "#T2"; first by iDestruct "HPQ" as "[_ $]".
    iApply tguar_intro. iIntros "!>" (?????????????) "%H #B W". iSplit.
    - by iApply (tguar_elim with "T1 [//] B W").
    - by iApply (tguar_elim with "T2 [//] B W").
  Qed.

  Lemma temporal_sep P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∗ Q) ⊨ₜ (G1 ∧ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& HP& HQ)".
    iPoseProof (temporal_elim with "HG1 [$HI $MI $HP]") as "#T1".
    iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#T2".
    iApply tguar_intro. iIntros "!>" (?????????????) "%H #B W". iSplit.
    - by iApply (tguar_elim with "T1 [//] B W").
    - by iApply (tguar_elim with "T2 [//] B W").
  Qed.

  Lemma temporal_or P Q G1 G2 : P ⊨ₜ G1 -∗ Q ⊨ₜ G2 -∗ (P ∨ Q) ⊨ₜ (G1 ∨ G2).
  Proof.
    iIntros "#HG1 #HG2 !>" (?????????) "(HI& MI& [HP | HQ])".
    - iPoseProof (temporal_elim with "HG1 [$HI $MI $HP]") as "#T1".
      iApply tguar_intro. iIntros "!>" (?????????????) "%H #B W". iLeft.
      by iApply (tguar_elim with "T1 [//] B W").
    - iPoseProof (temporal_elim with "HG2 [$HI $MI $HQ]") as "#T2".
      iApply tguar_intro. iIntros "!>" (?????????????) "%H #B W". iRight.
      by iApply (tguar_elim with "T2 [//] B W").
  Qed.

  Lemma temporal_impl (φ : Prop) P G : P ⊨ₜ G -∗ (⌜φ⌝ → P) ⊨ₜ (⌜φ⌝ → G).
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& HP)".
    destruct (Classical_Prop.classic φ) as [Hφ|Hφ].
    - iPoseProof (temporal_elim with "HG [$HI $MI HP]") as "#T"; first by iApply "HP".
      iApply tguar_intro. iIntros "!>" (?????????????) "%H #B W". rewrite /= /ti_impl. iIntros (_).
      by iApply (tguar_elim with "T [//] B W").
    - iApply tguar_intro. iIntros "!>" (?????????????) "_ _ _". rewrite /= /ti_impl. by iIntros (?).
  Qed.

  (** Universal quantification over any type. *)
  Lemma temporal_forall {X : Type} (P : X → iProp Σ) (G : X → tps Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∀ x, P x) ⊨ₜ tps_forall G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& HP)".
    iAssert (∀ x, tguar (G x) _)%I with "[-]" as "#T".
    { iIntros (x). iApply (temporal_elim with "HG"). iFrame. iApply "HP". }
    iApply tguar_intro. iIntros "!>" (?????????????) "%H #B W". iIntros (x).
    by iApply (tguar_elim with "T [//] B W").
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
    iApply tguar_intro. iIntros "!>" (?????????????) "%H #B W". iExists x.
    by iApply (tguar_elim with "T [//] B W").
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

(** ** Reading the model under a ghost update

    Allocation of a registered structure reads the history and the model (to produce the
    record of the content at the current position) without changing them. *)
Section gupd_read.
  Context `{!lantanaGS Λ Σ}.

  Lemma gupd_read n D (P : iProp Σ) :
    (∀ g i Ω W, model_interp g i Ω W n D -∗ model_interp g i Ω W n D ∗ P) ⊢ |=[n,D]=>g P.
  Proof.
    iIntros "H". iApply gupd_unfold. iRight. iIntros (g i Ω W) "MI".
    iDestruct ("H" with "MI") as "[MI HP]". iModIntro. iExists Ω. iSplit; first (iPureIntro; by left).
    iIntros (W2 [WS OI2]). rewrite /model_interp. iDestruct "MI" as "(MHI& S& T& A& G& W& %OI)".
    iMod (model_history_interp_step _ _ n n _ Ω with "MHI") as "MHI"; [done|done|].
    iPoseProof (owit_mon W W2 with "W") as "W".
    { eapply owit_inv_rc_step_same_gls; [done| |done]. by apply wits_nd_step_wits_step_o. }
    iModIntro. iFrame. iSplit; first done. by iApply gupd_intro.
  Qed.

  (** The same at the level of [sfgupd], with the history: fancy updates may happen before
      and after reading the model. *)
  Lemma sfgupd_read_fupd E (P : iProp Σ) :
    (∀ h n σ Θ κs,
      history_interp h n σ Θ κs -∗ |={E,∅}=> ∀ g i Ω W,
        model_interp g i Ω W n (dom Θ) -∗
        model_interp g i Ω W n (dom Θ) ∗ |={∅,E}=> history_interp h n σ Θ κs ∗ P) ⊢ |={E}=>g P.
  Proof.
    iIntros "H". unfold_sfgupd. iIntros (h n σ Θ κs) "HI". rewrite /fgupd.
    iMod ("H" with "HI") as "H". iModIntro.
    iApply gupd_read. iIntros (g i Ω W) "MI". iDestruct ("H" with "MI") as "($& HP)".
    iMod "HP" as "[HI HP]". iModIntro. iFrame.
  Qed.

  Lemma sfgupd_read E (P : iProp Σ) :
    (∀ h n σ Θ κs g i Ω W,
      history_interp h n σ Θ κs -∗ model_interp g i Ω W n (dom Θ) -∗
      model_interp g i Ω W n (dom Θ) ∗ |={E}=> history_interp h n σ Θ κs ∗ P) ⊢ |={E}=>g P.
  Proof.
    iIntros "H". iApply sfgupd_read_fupd. iIntros (h n σ Θ κs) "HI".
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    iIntros (g i Ω W) "MI". iDestruct ("H" with "HI MI") as "($& HP)".
    iMod "close" as "_". iMod "HP" as "[HI HP]". iModIntro. iFrame.
  Qed.

End gupd_read.

(** ** Rules for [alwaysI] *)
Section always_rules.
  Context `{!lantanaGS Λ Σ}.

  Global Instance alwaysI_guar_persistent N P G : Persistent (alwaysI_guar N P G).
  Proof. rewrite alwaysI_guar_unfold. apply _. Qed.
  Global Instance alwaysI_view_persistent N P V : Persistent (alwaysI_view N P V).
  Proof. rewrite /alwaysI_view. apply _. Qed.
  Global Instance alwaysI_persistent N P : Persistent (alwaysI N P).
  Proof. rewrite /alwaysI. apply _. Qed.
  Global Instance treg_handle_persistent e : Persistent (treg_handle e).
  Proof. destruct e; apply _. Qed.
  Global Instance treg_persistent : Persistent treg.
  Proof. apply _. Qed.

  (** The structure is contractive in its content, which occurs only in the invariant and
      in the stored guarantee: structures can be defined by guarded recursion
      (temporal_fixpoint.v). *)
  Global Instance alwaysI_guar_contractive N G : Contractive (λ P, alwaysI_guar N P G).
  Proof. rewrite alwaysI_guar_unseal /alwaysI_guar_def. solve_contractive. Qed.

  Lemma alwaysI_guar_inv N P G : alwaysI_guar N P G ⊢ inv N P.
  Proof. rewrite alwaysI_guar_unfold. iIntros "(%&%&%&%& _& _& _& $& _)". Qed.
  Lemma alwaysI_guar_treg N P G : alwaysI_guar N P G ⊢ treg.
  Proof. rewrite alwaysI_guar_unfold. iIntros "(%&%&%&%& _& _& _& _& _& $& _)". Qed.
  Lemma alwaysI_guar_temporal N P G : alwaysI_guar N P G ⊢ ▷ (P ⊨ₜ G).
  Proof. rewrite alwaysI_guar_unfold. iIntros "(%&%&%&%& _& _& _& _& $& _)". Qed.
  Lemma alwaysI_view_inv N P V : alwaysI_view N P V ⊢ inv N P.
  Proof. apply alwaysI_guar_inv. Qed.
  Lemma alwaysI_view_treg N P V : alwaysI_view N P V ⊢ treg.
  Proof. apply alwaysI_guar_treg. Qed.
  Lemma alwaysI_inv N P : alwaysI N P ⊢ inv N P.
  Proof. apply alwaysI_view_inv. Qed.
  Lemma alwaysI_treg N P : alwaysI N P ⊢ treg.
  Proof. apply alwaysI_view_treg. Qed.

  Lemma alwaysI_guar_acc E N P G :
    ↑N ⊆ E → alwaysI_guar N P G ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. iIntros (?) "#H". iApply inv_acc; first done. by iApply alwaysI_guar_inv. Qed.
  Lemma alwaysI_view_acc E N P V :
    ↑N ⊆ E → alwaysI_view N P V ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. apply alwaysI_guar_acc. Qed.
  Lemma alwaysI_acc E N P :
    ↑N ⊆ E → alwaysI N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. apply alwaysI_view_acc. Qed.

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
  Global Instance into_inv_alwaysI_view N P V : IntoInv (alwaysI_view N P V) N := {}.
  Global Instance into_acc_alwaysI_view N P V E :
    IntoAcc (X := unit) (alwaysI_view N P V)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros (?) "#Hinv _". by iApply alwaysI_view_acc.
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
      position, consuming the registry and a later credit. *)
  Lemma alwaysI_register_guar E N P G :
    ↑tregN ⊆ E → ↑N ⊆ E →
    inv N P -∗ ▷ (P ⊨ₜ G) -∗ treg -∗ £n 1 -∗ |={E}=>g alwaysI_guar N P G.
  Proof.
    iIntros (HE HNE) "#Hinv #HG #TR LC". iApply sfgupd_read_fupd. iIntros (h n σ Θ κs) "HI".
    iMod (inv_acc with "Hinv") as "[HP Hclose]"; first done.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    iIntros (g i Ω W) "MI".
    iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#C".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MI". iMod "close" as "_". iMod ("Hclose" with "HP") as "_".
    iMod (saved_ti_alloc (tps_ti G)) as (γ) "#Hγ".
    iMod (treg_register treg_handle E (RAlways N γ) with "LC TR [] HI") as "[HI (%j& #Hj)]"; first done.
    { iIntros (st) "_". simpl. iExists P, G. iFrame "Hγ Hinv HG". }
    iModIntro. iFrame "HI". rewrite alwaysI_guar_unfold. iExists j, n, γ, _. iFrame "Hj HE Hγ Hinv HG TR C".
  Qed.
  (** The same under a view [V] of the content. *)
  Lemma alwaysI_register E N P V :
    ↑tregN ⊆ E → ↑N ⊆ E →
    inv N P -∗ □ (P -∗ V) -∗ treg -∗ £n 1 -∗ |={E}=>g alwaysI_view N P V.
  Proof.
    iIntros (HE HNE) "#Hinv #HPV #TR LC".
    iApply (alwaysI_register_guar with "Hinv [] TR LC"); [done..|].
    iNext. iApply (temporal_mono with "HPV"). iApply temporal_sem.
  Qed.

  (** Allocation registers the invariant and records its content at the current position. *)
  Lemma alwaysI_alloc_guar E N P G :
    ↑tregN ⊆ E →
    ▷ (P ⊨ₜ G) -∗ treg -∗ £n 1 -∗ ▷ P -∗ |={E}=>g alwaysI_guar N P G.
  Proof.
    iIntros (HE) "#HG #TR LC HP". iApply sfgupd_read. iIntros (h n σ Θ κs g i Ω W) "HI MI".
    iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#C".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MI".
    iMod (saved_ti_alloc (tps_ti G)) as (γ) "#Hγ".
    iMod (inv_alloc N _ P with "HP") as "#Hinv".
    iMod (treg_register treg_handle E (RAlways N γ) with "LC TR [] HI") as "[HI (%j& #Hj)]"; first done.
    { iIntros (st) "_". simpl. iExists P, G. iFrame "Hγ Hinv HG". }
    iModIntro. iFrame "HI". rewrite alwaysI_guar_unfold. iExists j, n, γ, _. iFrame "Hj HE Hγ Hinv HG TR C".
  Qed.
  Lemma alwaysI_alloc E N P :
    ↑tregN ⊆ E →
    treg -∗ £n 1 -∗ ▷ P -∗ |={E}=>g alwaysI N P.
  Proof.
    iIntros (HE) "#TR LC HP". iApply (alwaysI_alloc_guar with "[] TR LC HP"); first done.
    iNext. iApply temporal_sem.
  Qed.

End always_rules.

(** ** Rules for [untilI] *)
Section until_rules.
  Context `{!lantanaGS Λ Σ}.

  Global Instance untilI_pers_persistent N k P Q : Persistent (untilI_pers N k P Q).
  Proof. rewrite /untilI_pers. apply _. Qed.

  Lemma untilI_pers_inv N k P Q : untilI_pers N k P Q ⊢ oblP_inv N k P Q (until_disch k (tps_sem Q)).
  Proof. rewrite /untilI_pers. iIntros "(%&%&%&%&%&%&%&%&%& _& _& _& _& $& _)". Qed.
  Lemma untilI_pers_treg N k P Q : untilI_pers N k P Q ⊢ treg.
  Proof. rewrite /untilI_pers. iIntros "(%&%&%&%&%&%&%&%&%& _& _& _& _& _& $& _)". Qed.
  Lemma untilI_treg N k b q P Q : untilI N k b q P Q ⊢ treg.
  Proof. rewrite untilI_unfold. iIntros "[_ U]". by iApply untilI_pers_treg. Qed.

  (** Until *)
  Lemma untilI_frac_split N k b q q1 q2 P Q :
    (q = q1 + q2)%Qp →
    ⊢ untilI N k b q P Q -∗ (untilI N k b q1 P Q ∗ untilI N k b q2 P Q).
  Proof.
    iIntros (He) "U". rewrite !untilI_unfold He Qp.div_add_distr. iDestruct "U" as "([$ $]& #U)". auto.
  Qed.
  Lemma untilI_frac_add N k b1 b2 q1 q2 q P Q P' Q' :
    (q = q1 + q2)%Qp →
    untilI N k b1 q1 P Q -∗ untilI N k b2 q2 P' Q' -∗ untilI N k b1 q P Q.
  Proof.
    intros Hq. subst q.
    rewrite !untilI_unfold Qp.div_add_distr. iIntros "[Oa1 $] [Oa2 _]".
    iPoseProof (oblP_assigned_agree with "Oa1 Oa2") as "%". subst.
    by iCombine "Oa1 Oa2" as "Oa".
  Qed.

  Global Instance untilI_fractional N k b P Q : Fractional (λ q, untilI N k b q P Q).
  Proof.
    intros p q. rewrite !untilI_unfold. iSplit.
    - iIntros "(Oa& #OI)". iFrame "OI". rewrite !Qp.div_add_distr. iDestruct "Oa" as "[Oa Oa']". iFrame.
    - iIntros "((Oa1& #Oi)& Oa2& _)". iFrame "Oi". rewrite !Qp.div_add_distr. iCombine "Oa1 Oa2" as "$".
  Qed.
  Global Instance untilI_as_fractional N k b q P Q : AsFractional (untilI N k b q P Q) (λ q, untilI N k b q P Q) q.
  Proof. split; [auto|apply _]. Qed.

  (** Update rules. Allocation of the until registers it (a model update, reading the model). *)
  Lemma untilI_alloc E g K (b : bool) ℓ1 ℓ2 μ :
    (ℓ1 <= ℓ2)%ordi →
    crP_obls g ℓ1 K -∗
    |={E}=>g ∃ k, ⌜k ∉ K⌝ ∗ crP_obls g ℓ1 ({[k]} ∪ K) ∗
                 oblP_fuel k ℓ2 μ ∗ witP_layer k ℓ2 ∗
                 ∀ E' N (P Q : iProp Σ), ⌜↑tregN ⊆ E'⌝ -∗ treg -∗ £n 1 -∗
                   ▷ (if b then Q else P) -∗ |={E'}=>g untilI N k b 1 P Q.
  Proof.
    iIntros (Ltl) "TG". iMod (obl_alloc_assigned with "TG") as "(%k& $& $& Oa& $& $& ACC)". 1: auto.
    iIntros "!> %E' %N %P %Q %HE #TR LC HC".
    iApply sfgupd_read. iIntros (h n σ Θ κs gm i Ω W) "HI MI".
    iAssert (▷ (tguar (tps_sem P) n ∨ tguar (tps_sem Q) n))%I as "#C".
    { destruct b.
      - iPoseProof (temporal_elim_later with "[] [$HC $HI $MI]") as "#C"; first iApply temporal_sem.
        iNext. by iRight.
      - iPoseProof (temporal_elim_later with "[] [$HC $HI $MI]") as "#C"; first iApply temporal_sem.
        iNext. by iLeft. }
    iDestruct "MI" as "(MHI& S& MI)". iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "(#OE& Oa)".
    iPoseProof (osat_lookup_assigned with "[$S $OE $Oa]") as "%Hk". destruct Hk as (fu& o& Hk).
    iPoseProof (model_history_interp_event_obl_now with "MHI") as "#EA". 1: eauto.
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MHI S MI".
    iMod ("ACC" $! E' N P Q (until_disch k (tps_sem Q)) with "HC") as "#OI".
    iMod (saved_ti_alloc (tps_ti (tps_sem P))) as (γP) "#HγP".
    iMod (saved_ti_alloc (tps_ti (tps_sem Q))) as (γQ) "#HγQ".
    iMod (treg_register treg_handle E' (RUntil N k γP γQ) with "LC TR [] HI") as "[HI (%j& #Hj)]"; first done.
    { iIntros (st) "_". simpl. iExists P, Q. iFrame "HγP HγQ OI". }
    iModIntro. iFrame "HI". rewrite untilI_unfold /untilI_pers. iSplitL "Oa".
    { iEval (unfold_opreds). iFrame "OE Oa". }
    iExists j, n, γP, γQ, _, i, Ω, fu, o. iFrame "Hj HE HγP HγQ OI TR EA C".
  Qed.

  (** An already discharged obligation invariant, with the record of [Q] at the current
      position (no until is created, so nothing is registered). *)
  Lemma untilI_discharged_alloc E ℓ μ (Q : iProp Σ) :
    Q -∗
    |={E}=>g Q ∗ ∃ k, oblP_discharged k ∗
                        (∀ E' N (P : iProp Σ), |={E'}=> oblP_inv N k P Q (until_disch k (tps_sem Q))) ∗
                        oblP_fuel k ℓ μ ∗ witP_layer k ℓ.
  Proof.
    iIntros "HQ". iPoseProof (temporal_sem Q) as "#HG2".
    unfold_sfgupd. rewrite /fgupd. iIntros (?????) "SI".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    unfold_opreds. iApply gupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
    assert (NEW : ∃ k, Ω1 !! k = None).
    { exists (fresh (dom Ω1)). apply not_elem_of_dom. apply is_fresh. }
    destruct NEW as (k& NEWk).
    assert (NinOk1 : k ∉ dom Ω1) by (eapply not_elem_of_dom; eauto).
    iMod (osat_alloc_obl_discharged _ k (measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M) with "S") as "(S& #Gwf& #Ge& #Gu& Gf& %OStep)". 1: auto.
    iMod (owit_alloc_witness_discharged _ k (η (measure_rep (ℓ, 1) ((1 ⊕ ▽) × μ)%M)) with "[$W $Gu]") as "(W& #Ww)".
    { apply owit_inv_dom in GWI. rewrite -GWI. by apply not_elem_of_dom. }
    iPoseProof (oassigned_add_obl with "[$A $Ge Gu]") as "A".
    { iRight. iFrame "Gu". }
    set (Ω2:=(<[k:=(obl_discharged)]> Ω1)).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 2. eauto. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. econstructor 2. econstructor 2. auto. }
    iIntros (? [WStep GWI2]) "!>".
    unshelve epose proof (owit_inv_alloc_discharged Ω1 k W1 NinOk1 GWI W2 _ GWI2) as (NinWk1& WMon).
    { inv WStep; eauto. econstructor 2. apply wits_nd_step_wits_step. auto. }
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. iFrame. }
    iPoseProof (temporal_elim with "HG2 [$SI $HI $S $O $A $G $W $HQ]") as "#HQi". 1: eauto.
    rewrite /model_interp. iFrame "HI S O A G W". iSplitR; first eauto.
    iModIntro. iMod "close" as "_". iModIntro. iFrame "SI HQ". iExists k. iFrame "Ge Ww Gf Gu".
    iIntros (E' N P).
    iMod (oblG_inv_alloc_discharged _ N _ _ P Q with "[$Gu]") as "#GVar"; cycle 1.
    { iFrame "GVar". done. }
    iFrame "Eo HQi".
  Qed.

  (** TODO: Timeless version *)
  Lemma untilI_to_true E N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    untilI N k false 1 P Q ={E,E ∖ ↑N}=∗
    ▷ (P ∗ ∀ E', |={E'}=>g ((▷ Q) ={E ∖ ↑N,E}=∗ untilI N k true 1 P Q)).
  Proof.
    rewrite !untilI_unfold. iIntros (HM) "(Oa& #U)". iPoseProof (untilI_pers_inv with "U") as "#Oi".
    iMod (obl_assigned_to_true with "Oi Oa") as "[H ACC]". 1: auto.
    iModIntro. iNext. iDestruct "H" as "[Oa $]".
    iIntros "%". iPoseProof ("ACC" with "Oa") as "ACC". iMod ("ACC" $! E') as "[Oa ACC]".
    iIntros "!> HQ". iMod ("ACC" with "HQ") as "_". iFrame "Oa U". done.
  Qed.

  (** TODO: Timeless version *)
  Lemma untilI_true_to_discharge E N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    untilI N k true 1 P Q ={E,E ∖ ↑N}=∗
    ∀ g ℓ K,
    (⌜k ∈ K⌝) → crP_obls g ℓ K -∗
    ∀ E', ▷ (|={E'}=>m |={E ∖ ↑N,E}=> (Q ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)).
  Proof.
    rewrite !untilI_unfold. iIntros (HMask) "(Oa& #U)". iPoseProof (untilI_pers_inv with "U") as "#OI".
    iPoseProof (temporal_sem Q) as "#HG2".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: auto.
    iIntros "!> %%% %LUGk TG %". iDestruct ("H" with "Oa") as "[H ACC]".
    iNext. iDestruct "H" as "(Oa1& Oa2& HQ)". iCombine "Oa1 Oa2" as "Oa".
    unfold_sfmupd. rewrite /fmupd. iIntros (?????) "SI".
    iApply fupd_mask_intro. 1: set_solver. iIntros "close".
    (* FIXME: it would be better if we don't need to unfold everything and re-do the proof here... *)
    unfold_opreds. iDestruct "TG" as "(%& #Oe& Gg& Gt& Gw& #Gb& OS)".
    iDestruct "OI" as "(#Ge& Gvar)". iDestruct "Oa" as "(_& Gl)".
    iApply mupd_unfold. iRight. iIntros (????) "(HI& S& O& A& G& W& %GWI)".
    iPoseProof (big_sepS_delete _ _ _ LUGk with "OS") as "[(_& Go& Oo) OS]".
    iPoseProof (osat_lookup_assigned with "[$S $Ge $Gl]") as "%LUO1l".
    iPoseProof (osat_lookup_owner with "[$S $Ge $Go]") as "%LUO1o".
    destruct LUO1l as (?&?&LUO1l). destruct LUO1o as (?&LUO1o).
    rewrite LUO1l in LUO1o. inv LUO1o. rename x1 into a.
    iPoseProof (oassigned_delete_obl _ k with "A") as "(A& _& [(%& Go1& Oo1& _) | #Gu])".
    { apply elem_of_dom. eauto. }
    2:{ iExFalso. iPoseProof (oblG_assigned_discharged_false with "[$Gl $Gu]") as "%". done. }
    iPoseProof (oblG_owner_agree _ i i1 with "[$Go $Go1]") as "%". destruct H as [<- _].
    iDestruct "Oo" as "[Oo Oo']". iCombine "Oo1 Oo'" as "Oo'". iCombine "Oo Oo'" as "Oo".
    iPoseProof (othread_elem with "[$O $Oe]") as "%Ini".
    iMod (ocarrier_delete_obl with "[$O $G $Gg $Oo]") as "(O& G& Gg& Go2)". 1,2: auto.
    iDestruct "Go" as "[Go Go']". iCombine "Go1 Go2" as "Go1". iCombine "Go' Go1" as "Go'". iCombine "Go Go'" as "Go".
    iMod (osat_discharge with "[$S $Ge $Gl $Go]") as "(S& #Gu& %Gstep)".
    assert (LUW : ∃ b, W1 !! k = Some (witness_assigned b) ∧ (b <= η a)%ord).
    { specialize (GWI k). rewrite LUO1l in GWI. inv GWI. destruct y; try done. eauto. }
    destruct LUW as (b&LUW1& LEab).
    iPoseProof (owit_discharge with "[$W $Gu]") as "W". 1: eauto.
    iPoseProof (oassigned_add_obl _ k with "[$A $Ge]") as "A".
    { iRight. eauto. }
    set (Ω2:=(<[k:=(obl_discharged)]> Ω1)).
    assert (Gstep' : obl_step (obl_assigned a i) obl_discharged) by (by econstructor 2).
    iMod (model_history_interp_step _ _ n n _ Ω2 with "HI") as "HI". 1: auto.
    { subst Ω2. apply obls_step_rc_obls_le. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
    iPoseProof (model_history_interp_event_obl_now k with "HI") as "#Eo".
    { subst Ω2. apply lookup_insert_eq. }
    iModIntro. iExists Ω2. iSplitR.
    { iPureIntro. econstructor 2. econstructor 1. exists k. do 2 eexists. split_and !; eauto. }
    iIntros (? [WStep GWI2]).
    pose proof (owit_inv_discharge _ _ _ _ _ LUO1l GWI Gstep' W2 WStep GWI2) as (?& LUW& WMon).
    rewrite LUW1 in LUW. inv LUW.
    iPoseProof (owit_mon _ _ WMon with "W") as "W".
    iAssert (oassigned (dom Ω2))%I with "[A]" as "A".
    { subst Ω2. rewrite dom_insert_L. replace ({[k]} ∪ dom Ω1 ∖ {[k]}) with (({[k]} ∪ dom Ω1)). 1: iFrame.
      apply elem_of_dom_2 in LUO1l. rewrite -union_difference_L; set_solver. }
    iPoseProof (temporal_elim with "HG2 [$SI $HI $S $O $A $G $W $HQ]") as "#HQi". 1: eauto.
    rewrite /model_interp. iFrame "HI S O W A G".
    iApply fupd_intro. iSplitR; first eauto. iIntros "!>". iFrame "Oe Ge Gb Gu Gg Gt SI".
    iMod "close" as "_". iModIntro. iMod ("ACC" with "[]") as "_".
    { iNext. iRight. iRight. iFrame "Ge Gu Eo HQi". }
    iModIntro. iFrame.
  Qed.

  Lemma untilI_discharge E N k (P Q : iProp Σ) :
    ↑N ⊆ E →
    untilI N k false 1 P Q ={E,E ∖ ↑N}=∗
    ▷ (P ∗
       ∀ E', |={E'}=>g ((▷ Q) ={E ∖ ↑N}=∗
                       ∀ g ℓ K, (⌜k ∈ K⌝) → crP_obls g ℓ K -∗
                                ∀ E'', ▷ (|={E''}=>m |={E ∖ ↑N,E}=> (Q ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k)))).
  Proof.
    iIntros (HN) "Uk". iMod (untilI_to_true with "Uk") as "H". 1: auto.
    iModIntro. iNext. iDestruct "H" as "($& H)". iIntros (?).
    iMod ("H" $! E') as "H". iIntros "!> HQ". iMod ("H" with "HQ") as "H".
    iMod (untilI_true_to_discharge with "H") as "H". 1: auto.
    iIntros "!> %%% % TG". iPoseProof ("H" with "[//] TG") as "H".
    iIntros (?). iNext. iMod ("H" $! E'') as "H". iModIntro. iFrame.
  Qed.

  (** Access rules *)
  Lemma untilI_discharged_false N k b q P Q :
    untilI N k b q P Q -∗ oblP_discharged k -∗ False.
  Proof.
    rewrite !untilI_unfold. iIntros "[Oa _] #Of".
    iPoseProof (oblP_assigned_discharged_false with "Oa Of") as "%". done.
  Qed.

  Lemma untilI_acc E N k b q P Q :
    ↑N ⊆ E →
    untilI N k b q P Q ={E,E ∖ ↑N}=∗
    ▷ ((if b then Q else P) ∗ ((▷ if b then Q else P) ={E ∖ ↑N,E}=∗ untilI N k b q P Q)).
  Proof.
    rewrite !untilI_unfold. iIntros (Hmask) "(Oa& #U)". iPoseProof (untilI_pers_inv with "U") as "#OI".
    iMod (oblP_inv_acc_assigned with "OI") as "H". 1: set_solver.
    iPoseProof ("H" with "Oa") as "[H ACC]".
    iModIntro. iNext. iDestruct "H" as "(Oa& H)". destruct b.
    - iDestruct "H" as "(Oa2& $)". iIntros "HQ". iFrame "Oa U". iApply "ACC".
      iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame.
    - iDestruct "H" as "(Oa2& $)". iIntros "HP". iFrame "Oa U". iApply "ACC".
      iNext. iApply oblP_variant_unfold. iLeft. iFrame.
  Qed.

End until_rules.

Section until_derived.
  Context `{!lantanaGS Λ Σ}.

  (** Discharge a finally with its right formula at hand, using two later credits. *)
  Lemma finallyI_discharge E N k g ℓ K Q :
    ↑N ⊆ E → k ∈ K →
    £ (2 : Ord.t) -∗ crP_obls g ℓ K -∗ finallyI N k false 1 Q -∗ Q -∗
    |={E}=>m Q ∗ crP_obls g ℓ (K ∖ {[k]}) ∗ oblP_discharged k.
  Proof.
    iIntros (Hmask Hk) "LC Cg HF HQ".
    iMod (untilI_discharge with "HF") as "HF"; first set_solver.
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iDestruct "HF" as "[_ HF]". iMod ("HF" $! _) as "HF".
    iMod ("HF" with "[HQ]") as "HF".
    { iNext. iFrame. }
    iPoseProof ("HF" with "[//] Cg") as "HF".
    iPoseProof (tlc_split_one with "LC") as "[LC LC1]"; first eauto.
    iApply (lc_sfmupd_add_later with "LC1"). iNext.
    iMod ("HF" $! _) as "HF". iMod "HF" as "($& $& $)". done.
  Qed.

  (** The same, with the obligation set split. *)
  Lemma finallyT_discharge E N k g ℓ K (Q : iProp Σ) :
    ↑N ⊆ E → k ∉ K →
    £ (2 : Ord.t) -∗ crP_obls g ℓ ({[k]} ∪ K) -∗ finallyI N k false 1 Q -∗ Q -∗
    |={E}=>m Q ∗ crP_obls g ℓ K ∗ oblP_discharged k.
  Proof.
    iIntros (HN Hk) "LC Cg HF HQ".
    iMod (finallyI_discharge with "LC Cg HF HQ") as "($& Cg& $)"; [done|set_solver|].
    assert (({[k]} ∪ K) ∖ {[k]} = K) as -> by set_solver. done.
  Qed.

End until_derived.

Section state_rules.
  Context `{!lantanaGS Λ Σ}.

  Lemma temporal_state (φ : state Λ → thread_pool Λ → Prop) (P : iProp Σ) :
    (∀ σ Θ κs, state_interp σ Θ κs ∗ P ⊢ ⌜φ σ Θ⌝) → ⊢ P ⊨ₜ tps_state φ.
  Proof.
    iIntros (Hφ). iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& _& HP)".
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iAssert (⌜φ σ Θ⌝)%I with "[HI HP]" as %Hs.
    { rewrite /history_interp. iDestruct "HI" as "(_& _& SI)". iApply Hφ. iFrame. }
    iApply tguar_intro.
    iIntros "!>" (l s h' TQ g v2 Ω2 W' τf γ σ' Θ' κs' (BEH& FS& LB& HIST& EQTQ)) "_ ([HI' SIa]& MI& WPs)".
    iPoseProof (history_interp_hG_event_lookup with "[$HI' $HE]") as "%Hh".
    apply HIST in Hh as [? Hτ]. simpl. rewrite Hτ. done.
  Qed.

End state_rules.

Section impl_rules.
  Context `{!lantanaGS Λ Σ}.

  (** A guarantee extends to an implication whose complete antecedent, together with it,
      entails the consequent. With a pure antecedent this is [temporal_impl] weakened. *)
  Lemma temporal_impl_intro P A H G `{!TpsComplete A} :
    tps_le (tps_and A H) G → P ⊨ₜ H ⊢ P ⊨ₜ tps_impl A G.
  Proof. intros HG. by apply temporal_weaken, tps_impl_intro. Qed.

  Lemma temporal_impl_weaken P A G : P ⊨ₜ G ⊢ P ⊨ₜ tps_impl A G.
  Proof. apply temporal_weaken, tps_impl_intro_le. Qed.

End impl_rules.

(** ** Certification

    At a position, the adequacy proof opens the registry and every registered item, and
    produces a later-guarded record of each content. The contents stay in their invariants. *)
Section certification.
  Context `{!lantanaGS Λ Σ}.

  Local Lemma until_cert_assigned k (P Q R : iProp Σ) h n σ Θ κs g v Ω W fu o :
    Ω !! k = Some (obl_assigned fu o) →
    ▷ ((oblP_assigned k false (1/2) ∗ P) ∨ (oblP_assigned k true (1/2) ∗ Q) ∨ (oblP_discharged k ∗ R)) ∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) -∗
    ▷ (tguar (tps_sem P) n ∨ tguar (tps_sem Q) n).
  Proof.
    iIntros (Hk) "(Var& HI& MI)". iNext. iDestruct "Var" as "[[_ HP]|[[_ HQ]|[Of _]]]".
    - iLeft. iApply (temporal_elim P (tps_sem P) with "[] [$HI $MI $HP]"). iApply temporal_sem.
    - iRight. iApply (temporal_elim Q (tps_sem Q) with "[] [$HI $MI $HQ]"). iApply temporal_sem.
    - iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "Of". iDestruct "Of" as "[#Oe #Of]".
      iDestruct (osat_lookup_discharged with "[$S $Oe $Of]") as %H. rewrite Hk in H. done.
  Qed.

  Local Lemma until_cert_discharged k (P Q : iProp Σ) h n σ Θ κs g v Ω W :
    Ω !! k = Some obl_discharged →
    ▷ ((oblP_assigned k false (1/2) ∗ P) ∨ (oblP_assigned k true (1/2) ∗ Q) ∨
       (oblP_discharged k ∗ until_disch k (tps_sem Q))) ∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) -∗
    ▷ (∃ n' i' Ω', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω') k obl_discharged ∗ tguar (tps_sem Q) n').
  Proof.
    iIntros (Hk) "(Var& HI& MI)". iNext. iDestruct "MI" as "(MHI& S& _)".
    iDestruct "Var" as "[[Oa _]|[[Oa _]|[_ R]]]".
    - iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "[#Oe Oa]".
      iDestruct (osat_lookup_assigned with "[$S $Oe $Oa]") as %(?&?&H). rewrite Hk in H. done.
    - iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "[#Oe Oa]".
      iDestruct (osat_lookup_assigned with "[$S $Oe $Oa]") as %(?&?&H). rewrite Hk in H. done.
    - iDestruct "R" as "(%n'& %i'& %Ω'& #EF& #TF)".
      iDestruct (event_obl_model_history_interp_lookup with "[$MHI $EF]") as %(_& _& _& Hn& _).
      iExists n', i', Ω'. iFrame "EF TF". done.
  Qed.

  (** The certificate of one registered item, with the registry closed. *)
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
    - iDestruct "Hd" as "(%P& %Q& #SP& #SQ& #OI)".
      iAssert (⌜∃ o, Ω !! k = Some o⌝)%I as %[o Hk].
      { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "OI". iDestruct "OI" as "[#Oe _]".
        iDestruct (osat_elem_lookup with "[$S $Oe]") as "[%H|[_ %H]]"; iPureIntro.
        - destruct H as (?&?&?). eauto.
        - eauto. }
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first done.
      destruct o.
      + iPoseProof (until_cert_assigned with "[$Var $HI $MI]") as "#C"; first done.
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

  (** The check at position [n]: the marker is appended to the registry (which is then
      closed again), and every entry is certified. The lower bound of the marked registry
      and the certificates form the bundle for [n]. *)
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

End certification.

(** ** Adequacy, up to trace implication *)
Section adequacy.
  Context `{!lantanaGS Λ Σ}.

  Lemma behavior_S n (τf : nat → trace_state Λ) : behavior (n, τf) → behavior (S n, τf).
  Proof. intros BEH. inversion BEH. by subst. Qed.

  (** *** The fairness measure drops across a step

      For every obligation assigned before and after the step. *)
  Definition obls_drop (m m' : thread_id → Ord.t → Ord.t) (Ω Ω' : obls) : Prop :=
    ∀ k fu o fu' o', Ω !! k = Some (obl_assigned fu o) → Ω' !! k = Some (obl_assigned fu' o') →
      (m' o' fu' < m o fu)%ord.

  Local Lemma obl_le_measure γ fu o fu' o' :
    obl_le (obl_assigned fu o) (obl_assigned fu' o') →
    (fair_sched_fun γ o' fu' <= fair_sched_fun γ o fu)%ord.
  Proof.
    intros [[Hle <-]|Hlt].
    - apply Hessenberg.le_add_l, Jacobsthal.le_mult_r. done.
    - apply Ord.lt_le, fair_sched_fun_mon_gen. done.
  Qed.

  (** Under [obls_le], an assigned obligation comes from an assigned one. *)
  Local Lemma obls_le_assigned_inv Ω Ω' k x fu' o' :
    obls_le Ω Ω' → Ω !! k = Some x → Ω' !! k = Some (obl_assigned fu' o') →
    ∃ fu o, x = obl_assigned fu o ∧ obl_le (obl_assigned fu o) (obl_assigned fu' o').
  Proof.
    intros [_ H] Hk Hk'. specialize (H _ _ _ Hk Hk'). destruct x as [fu o|]; [eauto|done].
  Qed.

  (** A step of the scheduled thread [i1]: its obligations lose fuel, the counters of the
      other active threads drop. *)
  Lemma obls_drop_step γ γ2 i1 (τ : trace Λ) Ω Ω0 Ω2 Ω' :
    obls_le Ω Ω0 → (Ω0 ↪ₚ Ω2 | obl_cond_owner i1) → obls_le Ω2 Ω' →
    obls_thread_active Ω2 τ → trace_thread τ = i1 → fscnt_next_rel τ γ γ2 →
    obls_drop (fair_sched_fun γ) (fair_sched_fun γ2) Ω Ω'.
  Proof.
    intros LEO0 [StepO _] LEO' OTA Hi FSrel k fu o fu' o' Hk Hk'.
    assert (Hk0 : ∃ x0, Ω0 !! k = Some x0).
    { destruct LEO0 as [Hdom _]. apply elem_of_dom, Hdom, elem_of_dom. eauto. }
    destruct Hk0 as [x0 Hk0].
    destruct LEO0 as [_ Hle0]. specialize (Hle0 _ _ _ Hk Hk0).
    specialize (StepO k). rewrite Hk0 in StepO.
    destruct (Ω2 !! k) as [x2|] eqn:Hk2; last by inv StepO.
    pose proof (obls_le_assigned_inv _ _ _ _ _ _ LEO' Hk2 Hk') as (fu2& o2& ->& Hle2).
    apply (obl_le_measure γ2) in Hle2.
    destruct x0 as [fu0 o0|]; last first.
    { inv StepO. match goal with H : _ ∨ _ |- _ => destruct H as [[HC _]|[_ Heq]]; [simpl in HC; done|done] end. }
    apply (obl_le_measure γ) in Hle0.
    inv StepO. match goal with H : _ ∨ _ |- _ => destruct H as [[HC Hstep]|[HC Heq]] end.
    - simpl in HC. subst o0.
      inv Hstep; match goal with H : obl_progress _ _ |- _ => inv H | H : obl_discharge _ _ |- _ => inv H end.
      eapply Ord.le_lt_lt; first exact Hle2. eapply Ord.lt_le_lt; last exact Hle0.
      apply fair_sched_fun_mon_gen. done.
    - inv Heq. simpl in HC.
      pose proof (OTA k _ Hk2) as TA. simpl in TA.
      specialize (FSrel o2). unfold fscnt_next_rel_th in FSrel.
      rewrite decide_False in FSrel; last by intros ->.
      rewrite decide_False in FSrel; last by intros F; eapply thread_active_and_not_false.
      eapply Ord.le_lt_lt; first exact Hle2. eapply Ord.lt_le_lt; last exact Hle0.
      apply Hessenberg.lt_add_r, OrdArith.lt_from_nat. done.
  Qed.

  (** A step of a finished thread: it owns nothing, every counter drops. *)
  Lemma obls_drop_na γ γ2 (τ : trace Λ) Ω :
    ts_emb (thread_na (trace_thread τ)) τ → obls_thread_active Ω τ → fscnt_next_rel τ γ γ2 →
    obls_drop (fair_sched_fun γ) (fair_sched_fun γ2) Ω Ω.
  Proof.
    intros TNA OTA FSrel k fu o fu' o' Hk Hk'. rewrite Hk in Hk'. inv Hk'.
    pose proof (OTA k _ Hk) as TA. simpl in TA.
    specialize (FSrel o'). unfold fscnt_next_rel_th in FSrel.
    rewrite decide_False in FSrel; last by intros ->; eapply thread_active_and_not_false.
    rewrite decide_False in FSrel; last by intros F; eapply thread_active_and_not_false.
    apply Hessenberg.lt_add_r, OrdArith.lt_from_nat. done.
  Qed.

  (** *** One step of the run

      From a consistent system at [n]: the system at [S n], the facts about the step, and
      later credits for the continuation (which may use fancy updates). *)
  Lemma run_step (c : nat) s h n σ Θ TQ κs g v Ω W τf γ (Φ : iProp Σ) :
    ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
     hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
    (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W n (dom Θ) ∗ threads_run s TQ -∗
    (∀ σ' Θ' κs' TQ' g' v' Ω' W' γ',
       ⌜behavior (S n, τf) ∧ beh_fscnt (S n, τf) γ' ∧ owit_inv_lb (fair_sched_fun γ') Ω' W' ∧
        hist_trace (h ++ [(σ', Θ', κs')]) τf ∧ Θ' = fst <$> TQ' ∧
        obls_drop (fair_sched_fun γ) (fair_sched_fun γ') Ω Ω'⌝ -∗
       £n c -∗
       (history_interp (h ++ [(σ', Θ', κs')]) (S n) σ' Θ' κs' ∗ state_interp_aux σ' Θ' κs') ∗
       model_interp g' v' Ω' W' (S n) (dom Θ') ∗ threads_run s TQ' -∗
       |={⊤}=> Φ) -∗
    |={⊤,∅}=> ALC (|={∅,⊤}=> Φ).
  Proof.
    iIntros "%H ([HI SIa]& MI& WPs) K". destruct H as (BEH& FS& LB& HIST& EQTQ). rewrite /threads_run.
    inversion BEH. clear BEH. subst n0 τf0.
    iPoseProof (history_interp_lookup with "HI") as "%LUhn". apply HIST in LUhn. destruct LUhn as (i'&LUhn).
    rewrite H1 in LUhn. inversion LUhn. clear LUhn. subst ρ1 i' κs.
    rename κs0 into κs, H1 into TRn, H3 into TRn1, H4 into BEH'.
    iAssert ([∗ map] i ↦ e ∈ Θ, match to_val e with | Some _ => (thP_done i) | None => True end)%I as "#THs".
    { subst. iApply big_sepM_fmap. iApply (big_sepM_impl with "WPs").
      iIntros "!> %%% H". destruct x. simpl. destruct (to_val e); auto. iDestruct "H" as "[$ _]". }
    iPoseProof (history_interp_lookup with "HI") as "%Hlu".
    destruct H2 as [TStep | TDone].
    - iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TStep. clear TStep. inversion H. clear H. subst Θ0 σ ρ2. rename H1 into PStep, H0 into LUTi1.
      assert (LUTQi1 : ∃ Q, TQ !! i1 = Some (e1, Q)).
      { subst Θ. rewrite lookup_fmap_Some in LUTi1. destruct LUTi1 as (?&?&?). destruct x. subst. eauto. }
      destruct LUTQi1 as (Q& LUTQi1). iPoseProof (big_sepM_delete _ _ _ _ LUTQi1 with "WPs") as "[WP WPs]".
      pose proof (val_stuck _ _ _ _ _ _ _ _ PStep) as He1. rewrite He1.
      iPoseProof (lwp_fix_unfold_fix with "WP") as "WP". rewrite /lwp_pre He1 /lwp_step.
      iSpecialize ("WP" $! ctx_id). iEval (rewrite !ctx_id_apply) in "WP".
      iMod ("WP" with "[] [//] [$HI $SIa]") as "WP".
      { iPureIntro. apply _. }
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv".
      iMod (model_interp_mupd_steps with "WP MI") as "(WP& %g0& %v0& %Ω0 & %W0& %& MI)".
      2: eapply LB.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [LEO0 LB0].
      iPoseProof (model_interp_owit_inv with "MI") as "%OWinv0".
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA0". 1,2: eauto.
      iDestruct "WP" as "[%NStuck WP]".
      iPoseProof ("WP" with "[//]") as "WP".
      iEval (rewrite !ctx_id_apply) in "WP". rewrite /mprog.
      iMod ("WP" with "MI") as "(%Ω2& %ProgO& WP)".
      assert (TNow : trace_thread (n, τf) = i1).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      pose proof (mprog_exists_step i1 Ω0 Ω2 W0 (n, τf) γ (eq_sym TNow) OTA0 OWinv0 LB0 FS ProgO) as H.
      destruct H as (W2& γ2& ProgW& OWinv2& LB2& FS2& FSrel).
      iMod ("WP" $! W2 with "[]") as "[MI WP]".
      { iPureIntro. split; auto. }
      iPoseProof (get_obls_thread_active_gen with "[$MI $THs]") as "%OTA2". 1,2: eauto.
      rewrite /mphys. iMod ("WP" with "MI") as "[MI WP]". iModIntro.
      rewrite (ALC_credits _ _ (Ord.from_nat c) (|={∅,⊤}=> Φ)%I). iMod "WP". iIntros "LC". simpl.
      iMod (model_interp_mupd_steps with "WP MI") as "(WP& %g'& %v'& %Ω3& %W3& %& MI)".
      2: eapply LB2.
      { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
      destruct H as [LEO LB3]. iMod "WP" as "(HI& WP& Efs)".
      unfold trace_next in *. simpl in *. assert (TDisj : Θ ##ₘ efs).
      { eapply map_disjoint_dom_2, fork_thread_ids; eauto. }
      remember ((<[i1:=e2]> Θ) ∪ efs) as Θ2.
      replace (dom (<[i1:=e2]> Θ) ∪ dom efs) with (dom Θ2); cycle 1.
      { subst Θ2. rewrite dom_union_L. auto. }
      remember ((λ e, (e, fork_post)) <$> efs : gmap thread_id (expr Λ * (thread_id → val Λ → iProp Σ))) as TQefs.
      iAssert ([∗ map] j ↦ '(e, Q) ∈ TQefs, lwpupd j ⊤ e (match to_val e with
                                                          | Some v => lift_term j Q v
                                                          | None => lwp_fix s j ⊤ e (lift_term j Q)
                                                          end))%I with "[Efs]" as "Efs".
      { subst TQefs. iApply big_sepM_fmap. iApply (big_sepM_impl with "Efs"). iIntros "!> %%% WP".
        destruct (to_val x) eqn:EQx.
        - rewrite lwp_fix_unfold_fix /lwp_pre EQx. iApply lwpupd_trans. iApply "WP".
        - iApply "WP". }
      iMod (all_interp_lwpupd_steps_gmap γ2 with "Efs HI MI") as "(Efs& HI& %g2& %v2& %Ω4& %W4& %& MI)".
      { subst Θ2 TQefs. rewrite -map_fmap_compose. unfold compose. simpl. rewrite map_fmap_id.
        apply map_union_subseteq_r. apply map_disjoint_insert_l_2; auto. apply not_elem_of_dom.
        apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. }
      1: auto. destruct H as [LEO2 LB4].
      assert (EQTQ2 : Θ2 = fst <$> (<[i1:=(e2, Q)]> TQ ∪ TQefs)).
      { subst. rewrite map_fmap_union fmap_insert -map_fmap_compose /compose map_fmap_id. done. }
      assert (TQDisj : <[i1:=(e2, Q)]> TQ ##ₘ TQefs).
      { subst. apply map_disjoint_dom. rewrite dom_fmap_L dom_insert_lookup_L; eauto.
        apply map_disjoint_dom in TDisj. rewrite dom_fmap_L in TDisj. auto. }
      iDestruct "HI" as "[HI SIa]".
      iPoseProof (history_interp_wf with "HI") as "%HistWF".
      assert (HIST' : hist_trace (h ++ [(σ2, Θ2, κs)]) τf).
      { intros n' σ' Θ' κs' H. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
        - inv H. eapply HIST in LUh. eauto.
        - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
          inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
          destruct HistWF as [Hlen _]. rewrite length_app in Hlen. simpl in Hlen.
          assert (Hh : length h = S n) by lia. rewrite Hh TRn1. eauto. }
      destruct (to_val e2) eqn:He2.
      + rewrite lwp_fix_unfold_fix /lwp_pre He2.
        iMod (all_interp_lwpupd_steps γ2 with "WP [$HI $SIa] MI") as "(WP& [HI SIa]& %g3& %v3& %Ω5& %W5& %& MI)".
        { subst Θ2. rewrite lookup_union_l; first apply lookup_insert_eq.
          apply not_elem_of_dom. apply elem_of_dom_2 in LUTi1. apply map_disjoint_dom in TDisj. set_solver + LUTi1 TDisj. }
        1: eapply LB4. destruct H as [LEO3 LB5].
        iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix s j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union; first done.
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iApply ("K" with "[%] LC [$HI $SIa $MI $WPs]"). split_and!; eauto.
        eapply (obls_drop_step _ _ i1 (n, τf) _ Ω0 Ω2); eauto.
        etrans; first exact LEO. etrans; [exact LEO2|exact LEO3].
      + iAssert ([∗ map] j ↦ '(e, Q) ∈ (<[i1:=(e2, Q)]> TQ ∪ TQefs),
                   (match to_val e with
                    | Some v => lift_term j Q v
                    | None => lwp_fix s j ⊤ e (lift_term j Q)
                    end))%I with "[WPs WP Efs]" as "WPs".
        { iApply big_sepM_union; first done.
          iFrame "Efs". rewrite big_sepM_insert_delete. iFrame. rewrite He2. iFrame. }
        iApply ("K" with "[%] LC [$HI $SIa $MI $WPs]"). split_and!; eauto.
        eapply (obls_drop_step _ _ i1 (n, τf) _ Ω0 Ω2); eauto.
        etrans; [exact LEO|exact LEO2].
    - iPoseProof (get_obls_thread_active with "[$HI $MI $WPs]") as "%OTA". 1,2: eauto.
      inversion TDone. clear TDone. inversion H. clear H. subst Θ0 σ1 ρ2.
      destruct H1 as (He1&<-&<-&->&->). destruct He1 as [v1 He1]. simpl in *.
      rewrite map_union_empty insert_id in TRn1. 2: auto.
      iPoseProof (history_interp_step with "HI") as "[SI ACC]". iMod ("ACC" with "SI") as "HI".
      pose proof (exists_fscnt_next _ _ FS). destruct H as (γ2& FS2& FSrel).
      unfold trace_next in *. simpl in *.
      assert (TNow : trace_thread (n, τf) = i1).
      { unfold trace_thread, trace_now. simpl. rewrite TRn. done. }
      assert (TNA : ts_emb (thread_na i1) (n, τf)).
      { unfold ts_emb, thread_na. simpl. rewrite TRn. right. eauto. }
      rewrite -TNow in TNA. pose proof (owit_inv_lb_step_na_turn _ _ _ _ _ TNA OTA LB FSrel) as LB2.
      iDestruct "MI" as "[MHI MI]". iMod (model_history_interp_step _ _ _ (S n) with "MHI") as "MHI".
      1: lia. 1: reflexivity.
      iPoseProof (history_interp_wf with "HI") as "%HistWF".
      assert (HIST' : hist_trace (h ++ [(σ, Θ, κs)]) τf).
      { intros n' σ' Θ' κs' H. rewrite lookup_app in H. destruct (h !! n') eqn:LUh.
        - inv H. eapply HIST in LUh. eauto.
        - rewrite lookup_cons in H. destruct (n' - length h) eqn:Hn'; last done.
          inv H. apply lookup_ge_None in LUh. assert (n' = length h) by lia. subst n'.
          destruct HistWF as [Hlen _]. rewrite length_app in Hlen. simpl in Hlen.
          assert (Hh : length h = S n) by lia. rewrite Hh TRn1. eauto. }
      iApply fupd_mask_intro. 1: set_solver. iIntros "close".
      rewrite (ALC_credits _ _ (Ord.from_nat c) (|={∅,⊤}=> Φ)%I). iApply ALC_intro. iIntros "LC". iMod "close" as "_".
      iApply ("K" with "[%] LC [$HI $SIa $MHI $MI $WPs]"). split_and!; eauto.
      eapply obls_drop_na; eauto.
  Qed.

  (** *** The always loop

      From a consistent system at [n]: certify every registered item (the shape's later
      strips the registry list and the content of this invariant), step, and decide [n]
      with the record of the content, then continue. *)
  Lemma always_run N P G :
    treg -∗ inv N P -∗ ▷ (P ⊨ₜ G) -∗
    ∀ s h n σ Θ TQ κs g v Ω W τf γ,
      ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
       hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
      £n 1 -∗
      (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W n (dom Θ) ∗ threads_run s TQ -∗
      ti_always (tps_ti G) (ti_pure True) (n, τf).
  Proof.
    iIntros "#TR #Hinv #HG". iIntros (s h n σ Θ TQ κs g v Ω W τf γ) "%H LC ([HI SIa]& MI& WPs)".
    iLöb as "IH" forall (s h n σ Θ TQ κs g v Ω W τf γ H).
    destruct H as (BEH& FS& LB& HIST& EQTQ).
    rewrite ti_always_unfold /ti_always_pre.
    (* the record of this invariant's content at [n] *)
    iMod (inv_acc with "Hinv") as "[HP HcloseP]"; first done.
    iPoseProof (temporal_elim_later_guar P G with "HG [$HP $HI $MI]") as "#Trec".
    iMod ("HcloseP" with "HP") as "_".
    (* the check: mark the registry (with the credit) and certify *)
    iMod (inv_acc with "TR") as "[R HcloseR]"; first done.
    iMod (lc_fupd_elim_later with "LC R") as (l) "[Ha #Hl]".
    iMod (treg_mark n l with "Ha Hl HI") as "(HI& Ha& #Hl'& #Hlb)".
    iMod ("HcloseR" with "[Ha]") as "_".
    { iNext. iExists _. iFrame "Ha Hl'". }
    iMod (certify_entries n _ with "Hl' HI MI") as "(HI& MI& #Cs)".
    iPoseProof (bundle_intro n _ with "Hlb Cs") as "#B"; first by rewrite last_snoc.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply (run_step 1 with "[%] [$HI $SIa $MI $WPs]"); first by split_and!.
    iIntros (σ' Θ' κs' TQ' g' v' Ω' W' γ') "%Hstep LC Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& EQTQ'& DROP).
    iModIntro. iSplit; [|iSplit; first done].
    - iApply (tguar_elim with "Trec [%] B Sys"). split_and!; done.
    - iDestruct "Sys" as "([HI' SIa']& MI'& WPs')". unfold trace_next. simpl.
      iApply ("IH" with "[%] LC HI' SIa' MI' WPs'"). split_and!; done.
  Qed.

  (** The registered structures guarantee the always of their stored reading, and the until
      of the canonical trace properties of their contents. *)
  Lemma temporal_always_guar N P G : ⊢ alwaysI_guar N P G ⊨ₜ tps_always G.
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& #A)". rewrite alwaysI_guar_unfold.
    iDestruct "A" as (j r γ st) "(#Hj& #HE& #Hγ& #Hinv& #HG& #TR& #AC)".
    iDestruct (history_interp_hG_event_lookup with "[$HI $HE]") as %Hr.
    iDestruct (history_interp_wf with "HI") as %[Hlen _].
    assert (Hrn : r ≤ n) by (apply lookup_lt_Some in Hr; lia).
    iApply tguar_intro.
    iIntros "!>" (l s h' TQ g v' Ω' W' τf γ' σ' Θ' κs' (BEH& FS& LB& HIST& EQTQ)) "#B Sys".
    (* the certificate of this invariant for [n]: from the bundle, or its allocation record *)
    iAssert (▷ tguar G n)%I as "#C".
    { rewrite /bundle /bundle_pre. iDestruct "B" as "(#Hlb& %Hlast& #Cs)".
      iDestruct (reg_idx_lb_pos with "Hlb Hj") as %[Hin|Hle]; first done.
      - iDestruct (big_sepL_lookup with "Cs") as "Cj"; first done. simpl.
        iDestruct "Cj" as (f) "[#Hf #Cj]". iDestruct (saved_ti_agree_fun with "Hf Hγ") as "#Heq".
        iNext. rewrite /tguar. iApply (tguar_ti_eq with "Heq Cj").
      - assert (r = n) as -> by lia. done. }
    rewrite /= ti_always_unfold /ti_always_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    rewrite (ALC_credits _ _ (Ord.from_nat 1) (|={∅,⊤}=> _)%I). iApply ALC_intro. iIntros "LC".
    iMod "close" as "_". iModIntro.
    iSplit; [|iSplit; first done].
    - iApply (tguar_elim with "C [%] B Sys"). split_and!; done.
    - iApply (always_run with "TR Hinv HG [%] LC Sys"). simpl.
      split_and!; [by apply behavior_S|exact FS|done|done|done].
  Qed.

  Lemma temporal_always_view N P V : ⊢ alwaysI_view N P V ⊨ₜ tps_always (tps_sem V).
  Proof. apply temporal_always_guar. Qed.
  Lemma temporal_always N P : ⊢ alwaysI N P ⊨ₜ tps_always (tps_sem P).
  Proof. apply temporal_always_view. Qed.

  Local Lemma model_interp_event_obl k o g v Ω W n D :
    Ω !! k = Some o → model_interp g v Ω W n D ⊢ event_obl v (n, Ω) k o.
  Proof. iIntros (Hk) "(MHI& _)". by iApply model_history_interp_event_obl_now. Qed.

  (** *** The until loop

      Once the obligation is discharged, the record of the right formula at the current
      position is at hand: certify, step, and decide with it. *)
  Lemma until_run_discharged (fP : tiProp Λ Σ) (Q : iProp Σ) a s h n σ Θ TQ κs g v Ω W τf γ :
    treg -∗ tguar (tps_sem Q) n -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
     hist_trace h τf ∧ Θ = fst <$> TQ⌝ -∗
    £n 1 -∗
    (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W n (dom Θ) ∗ threads_run s TQ -∗
    ti_until Ord.lt a fP (tps_ti (tps_sem Q)) (n, τf).
  Proof.
    iIntros "#TR #TQ %H LC ([HI SIa]& MI& WPs)". destruct H as (BEH& FS& LB& HIST& EQTQ).
    rewrite ti_until_unfold /ti_until_pre.
    iMod (inv_acc with "TR") as "[R HcloseR]"; first done.
    iMod (lc_fupd_elim_later with "LC R") as (l) "[Ha #Hl]".
    iMod (treg_mark n l with "Ha Hl HI") as "(HI& Ha& #Hl'& #Hlb)".
    iMod ("HcloseR" with "[Ha]") as "_".
    { iNext. iExists _. iFrame "Ha Hl'". }
    iMod (certify_entries n _ with "Hl' HI MI") as "(HI& MI& #Cs)".
    iPoseProof (bundle_intro n _ with "Hlb Cs") as "#B"; first by rewrite last_snoc.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply (run_step 0 with "[%] [$HI $SIa $MI $WPs]"); first by split_and!.
    iIntros (σ' Θ' κs' TQ' g' v' Ω' W' γ') "%Hstep LC Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& EQTQ'& DROP).
    iModIntro. iLeft. iApply (tguar_elim with "TQ [%] B Sys"). split_and!; done.
  Qed.

  (** While the obligation is assigned, with the measure of its state at the check: mark
      the registry (with a credit of the previous step), read the obligation invariant with
      the shape's later, certify, step, read the obligation at [S n] with a credit of the
      step, decide. *)
  Lemma until_run N k (P Q : iProp Σ) :
    treg -∗ oblP_inv N k P Q (until_disch k (tps_sem Q)) -∗
    ∀ s h n σ Θ TQ κs g v Ω W τf γ fu o,
      ⌜behavior (n, τf) ∧ beh_fscnt (n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧
       hist_trace h τf ∧ Θ = fst <$> TQ ∧ Ω !! k = Some (obl_assigned fu o)⌝ -∗
      £n 1 -∗
      (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗ model_interp g v Ω W n (dom Θ) ∗ threads_run s TQ -∗
      ti_until Ord.lt (Ord.S (fair_sched_fun γ o fu)) (tps_ti (tps_sem P)) (tps_ti (tps_sem Q)) (n, τf).
  Proof.
    iIntros "#TR #OI". iIntros (s h n σ Θ TQ κs g v Ω W τf γ fu o) "%H LC ([HI SIa]& MI& WPs)".
    iLöb as "IH" forall (s h n σ Θ TQ κs g v Ω W τf γ fu o H).
    destruct H as (BEH& FS& LB& HIST& EQTQ& Hk).
    iPoseProof (model_interp_event_obl with "MI") as "#EA"; first exact Hk.
    rewrite ti_until_unfold /ti_until_pre.
    (* the check: mark the registry, with the credit *)
    iMod (inv_acc with "TR") as "[R HcloseR]"; first done.
    iMod (lc_fupd_elim_later with "LC R") as (l) "[Ha #Hl]".
    iMod (treg_mark n l with "Ha Hl HI") as "(HI& Ha& #Hl'& #Hlb)".
    iMod ("HcloseR" with "[Ha]") as "_".
    { iNext. iExists _. iFrame "Ha Hl'". }
    (* the obligation invariant at [n], with the shape's later *)
    iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first done.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_".
    iDestruct "Var" as "[[Oa HP]|[[Oa HQ]|[Of _]]]"; last first.
    { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "Of". iDestruct "Of" as "[#Oe #Of]".
      iDestruct (osat_lookup_discharged with "[$S $Oe $Of]") as %H. rewrite Hk in H. done. }
    - (* [Q] holds at [n] *)
      iPoseProof (temporal_elim Q (tps_sem Q) with "[] [$HI $MI $HQ]") as "#TrecQ"; first iApply temporal_sem.
      iMod ("ACC" with "[Oa HQ]") as "_".
      { iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame. }
      iMod (certify_entries n _ with "Hl' HI MI") as "(HI& MI& #Cs)".
      iPoseProof (bundle_intro n _ with "Hlb Cs") as "#B"; first by rewrite last_snoc.
      iModIntro.
      iApply (run_step 0 with "[%] [$HI $SIa $MI $WPs]"); first by split_and!.
      iIntros (σ' Θ' κs' TQ' g' v' Ω' W' γ') "%Hstep LC Sys".
      destruct Hstep as (BEH'& FS'& LB'& HIST'& EQTQ'& DROP).
      iModIntro. iLeft. iApply (tguar_elim with "TrecQ [%] B Sys"). split_and!; done.
    - (* [P] holds at [n] *)
      iPoseProof (temporal_elim P (tps_sem P) with "[] [$HI $MI $HP]") as "#TrecP"; first iApply temporal_sem.
      iMod ("ACC" with "[Oa HP]") as "_".
      { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
      iMod (certify_entries n _ with "Hl' HI MI") as "(HI& MI& #Cs)".
      iPoseProof (bundle_intro n _ with "Hlb Cs") as "#B"; first by rewrite last_snoc.
      iModIntro.
      iApply (run_step 2 with "[%] [$HI $SIa $MI $WPs]"); first by split_and!.
      iIntros (σ' Θ' κs' TQ' g' v' Ω' W' γ') "%Hstep LC Sys".
      destruct Hstep as (BEH'& FS'& LB'& HIST'& EQTQ'& DROP).
      iPoseProof (tlc_split_one 2 1 with "LC") as "[LC LC1]"; first done.
      (* the obligation at [S n] *)
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first solve_ndisj.
      iMod (lc_fupd_elim_later with "LC1 Var") as "Var".
      iDestruct "Var" as "[[Oa' HP']|[[Oa' HQ']|[Of R]]]".
      + iAssert (⌜∃ fu' o', Ω' !! k = Some (obl_assigned fu' o')⌝)%I as %(fu'& o'& Hk').
        { iDestruct "Sys" as "(_& (_& S& _)& _)". iEval (unfold_opreds) in "Oa'". iDestruct "Oa'" as "[#Oe Oa']".
          iDestruct (osat_lookup_assigned with "[$S $Oe $Oa']") as %(?&?&?). eauto. }
        iMod ("ACC" with "[Oa' HP']") as "_".
        { iNext. iApply oblP_variant_unfold. iLeft. iFrame. }
        iModIntro. iRight. iSplit.
        { iApply (tguar_elim with "TrecP [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply DROP; eauto. }
        iDestruct "Sys" as "([HI' SIa']& MI'& WPs')". unfold trace_next. simpl.
        iApply ("IH" with "[%] LC HI' SIa' MI' WPs'"). split_and!; done.
      + iAssert (⌜∃ fu' o', Ω' !! k = Some (obl_assigned fu' o')⌝)%I as %(fu'& o'& Hk').
        { iDestruct "Sys" as "(_& (_& S& _)& _)". iEval (unfold_opreds) in "Oa'". iDestruct "Oa'" as "[#Oe Oa']".
          iDestruct (osat_lookup_assigned with "[$S $Oe $Oa']") as %(?&?&?). eauto. }
        iMod ("ACC" with "[Oa' HQ']") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame. }
        iModIntro. iRight. iSplit.
        { iApply (tguar_elim with "TrecP [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply DROP; eauto. }
        iDestruct "Sys" as "([HI' SIa']& MI'& WPs')". unfold trace_next. simpl.
        iApply ("IH" with "[%] LC HI' SIa' MI' WPs'"). split_and!; done.
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
        { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of". iExists n', i', Ω''. iFrame "EF TQ'". }
        iModIntro. destruct (decide (n' = n)) as [->|Hne].
        * iLeft. iApply (tguar_elim with "TQ' [%] B Sys"). split_and!; done.
        * assert (n' = S n) as -> by lia.
          iRight. iSplit.
          { iApply (tguar_elim with "TrecP [%] B Sys"). split_and!; done. }
          iExists Ord.O. iSplit; first (iPureIntro; apply Ord.S_pos).
          unfold trace_next. simpl.
          iApply (until_run_discharged with "TR TQ' [%] LC Sys"). split_and!; done.
  Qed.

  Lemma temporal_until N k b q P Q : ⊢ untilI N k b q P Q ⊨ₜ tps_until (tps_sem P) (tps_sem Q).
  Proof.
    iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& U)". rewrite untilI_unfold /untilI_pers.
    iDestruct "U" as "[Oa #U]".
    iDestruct "U" as (j r γP γQ st v Ω1 fu1 o1) "(#Hj& #HE& #HγP& #HγQ& #OI& #TR& #EA1& #AC)".
    iAssert (⌜∃ fu o, Ω !! k = Some (obl_assigned fu o)⌝)%I as %(fu& o& Hk).
    { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "Oa". iDestruct "Oa" as "[#Oe Oa]".
      iDestruct (osat_lookup_assigned with "[$S $Oe $Oa]") as %(?&?&?). eauto. }
    iPoseProof (model_interp_event_obl with "MI") as "#EA"; first exact Hk.
    iDestruct (history_interp_hG_event_lookup with "[$HI $HE]") as %Hr.
    iDestruct (history_interp_wf with "HI") as %[Hlen _].
    assert (Hrn : r ≤ n) by (apply lookup_lt_Some in Hr; lia).
    iApply tguar_intro.
    iIntros "!>" (l s h' TQ g v' Ω' W' τf γ' σ' Θ' κs' (BEH& FS& LB& HIST& EQTQ)) "#B Sys".
    (* the certificate of this until for [n]: from the bundle, or its allocation records *)
    iAssert (▷ (tguar (tps_sem P) n ∨ tguar (tps_sem Q) n) ∨
             ▷ (∃ n' i' Ω'', ⌜n' ≤ n⌝ ∗ event_obl i' (n', Ω'') k obl_discharged ∗ tguar (tps_sem Q) n'))%I as "#C".
    { rewrite /bundle /bundle_pre. iDestruct "B" as "(#Hlb& %Hlast& #Cs)".
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
      - assert (r = n) as -> by lia. by iLeft. }
    rewrite /= /ti_exist. iExists (Ord.S (Ord.S (fair_sched_ub fu))).
    rewrite ti_until_unfold /ti_until_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    rewrite (ALC_credits _ _ (Ord.from_nat 2) (|={∅,⊤}=> _)%I). iApply ALC_intro. iIntros "LC".
    iPoseProof (tlc_split_one 2 1 with "LC") as "[LC LC1]"; first done.
    iMod "close" as "_".
    iDestruct "C" as "[[TrecP|TrecQ]|(%n'& %i'& %Ω''& %Hn'& #EF& #TQ')]".
    - (* [P] at [n]: the obligation at [S n] decides *)
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first solve_ndisj.
      iMod (lc_fupd_elim_later with "LC1 Var") as "Var".
      iDestruct "Var" as "[[Oa' HP']|[[Oa' HQ']|[Of R]]]".
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
        { iApply (tguar_elim with "TrecP [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply Ord.le_lt_lt; first apply fair_sched_fun_ub.
          eapply Ord.le_lt_lt; [by apply fair_sched_ub_le_proper|apply Ord.S_lt]. }
        iDestruct "Sys" as "([HI' SIa']& MI'& WPs')". unfold trace_next. simpl.
        iApply (until_run with "TR OI [%] LC [$HI' $SIa' $MI' $WPs']").
        split_and!; [by apply behavior_S|done|done|done|done|done].
      + iAssert (⌜∃ fu' o', Ω' !! k = Some (obl_assigned fu' o')⌝)%I as %(fu'& o'& Hk').
        { iDestruct "Sys" as "(_& (_& S& _)& _)". iEval (unfold_opreds) in "Oa'". iDestruct "Oa'" as "[#Oe Oa']".
          iDestruct (osat_lookup_assigned with "[$S $Oe $Oa']") as %(?&?&?). eauto. }
        iAssert (⌜(fu' w≤ fu)⌝)%I as %Hfu.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EA]") as %(_& _& _& _& [_ Hle]).
          iPureIntro. specialize (Hle _ _ _ Hk Hk'). destruct Hle as [[? _]|?]; [done|by apply WFOCM.lt_le]. }
        iMod ("ACC" with "[Oa' HQ']") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iLeft. iFrame. }
        iModIntro. iRight. iSplit.
        { iApply (tguar_elim with "TrecP [%] B Sys"). split_and!; done. }
        iExists (Ord.S (fair_sched_fun γ' o' fu')). iSplit.
        { iPureIntro. apply Ord.lt_S. eapply Ord.le_lt_lt; first apply fair_sched_fun_ub.
          eapply Ord.le_lt_lt; [by apply fair_sched_ub_le_proper|apply Ord.S_lt]. }
        iDestruct "Sys" as "([HI' SIa']& MI'& WPs')". unfold trace_next. simpl.
        iApply (until_run with "TR OI [%] LC [$HI' $SIa' $MI' $WPs']").
        split_and!; [by apply behavior_S|done|done|done|done|done].
      + iDestruct "R" as "(%n'& %i'& %Ω''& #EF& #TQ')".
        iAssert (⌜n' ≤ S n⌝)%I as %Hn'.
        { iDestruct "Sys" as "(_& (MHI'& _)& _)".
          iDestruct (event_obl_model_history_interp_lookup with "[$MHI' $EF]") as %(_& _& _& ?& _). done. }
        iAssert (⌜n ≤ n'⌝)%I as %Hn.
        { destruct (le_gt_dec i' i) as [Hle|Hlt].
          - iDestruct (event_obl_compare i' i with "[$EF $EA]") as %(_& _& Hle'); first done. done.
          - iDestruct (event_obl_compare i i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
        iMod ("ACC" with "[Of]") as "_".
        { iNext. iApply oblP_variant_unfold. iRight. iRight. iFrame "Of". iExists n', i', Ω''. iFrame "EF TQ'". }
        iModIntro. destruct (decide (n' = n)) as [->|Hne].
        * iLeft. iApply (tguar_elim with "TQ' [%] B Sys"). split_and!; done.
        * assert (n' = S n) as -> by lia.
          iRight. iSplit.
          { iApply (tguar_elim with "TrecP [%] B Sys"). split_and!; done. }
          iExists Ord.O. iSplit; first (iPureIntro; apply Ord.S_pos).
          unfold trace_next. simpl.
          iApply (until_run_discharged with "TR TQ' [%] LC Sys").
          split_and!; [by apply behavior_S|done|done|done|done].
    - (* [Q] at [n] *)
      iModIntro. iLeft. iApply (tguar_elim with "TrecQ [%] B Sys"). split_and!; done.
    - (* discharged before the check: the discharge was at [n] *)
      iAssert (⌜n ≤ n'⌝)%I as %Hn.
      { destruct (le_gt_dec i' i) as [Hle|Hlt].
        - iDestruct (event_obl_compare i' i with "[$EF $EA]") as %(_& _& Hle'); first done. done.
        - iDestruct (event_obl_compare i i' with "[$EA $EF]") as %(Hle'& _& _); first lia. done. }
      assert (n' = n) as -> by lia.
      iModIntro. iLeft. iApply (tguar_elim with "TQ' [%] B Sys"). split_and!; done.
  Qed.

  (** With valid guarantees of the contents. *)
  Lemma temporal_always_view_valid N P V G : (⊢ V ⊨ₜ G) → ⊢ alwaysI_view N P V ⊨ₜ tps_always G.
  Proof.
    intros HG. iApply (temporal_weaken _ (tps_always (tps_sem V))).
    { apply tps_always_mono. by apply tps_sem_le. }
    iApply temporal_always_view.
  Qed.
  Lemma temporal_always_valid N P G : (⊢ P ⊨ₜ G) → ⊢ alwaysI N P ⊨ₜ tps_always G.
  Proof. apply temporal_always_view_valid. Qed.
  Lemma temporal_until_valid N k b q P Q G1 G2 :
    (⊢ P ⊨ₜ G1) → (⊢ Q ⊨ₜ G2) → ⊢ untilI N k b q P Q ⊨ₜ tps_until G1 G2.
  Proof.
    intros HG1 HG2. iApply (temporal_weaken _ (tps_until (tps_sem P) (tps_sem Q))).
    { apply tps_until_mono; by apply tps_sem_le. }
    iApply temporal_until.
  Qed.

  (** The program logic from position [n]: certify, step, and eliminate the record of the
      initial formula. *)
  Lemma lwp_ti_logic_temporal s h n σ Θ (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)) κs g v Ω W τf γ
    (G : tps Λ Σ) :
    behavior (n, τf) →
    beh_fscnt (n, τf) γ →
    owit_inv_lb (fair_sched_fun γ) Ω W →
    hist_trace h τf →
    (£n 1 ∗ treg ∗
     (history_interp h n σ Θ κs ∗ state_interp_aux σ Θ κs) ∗
      model_interp g v Ω W n (dom Θ) ∗
      (|={⊤}=>m ∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                  (P -∗ |={⊤}=>m [∗ map] i↦e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ v, lift_term i Ψ v }}))))
      ⊢ |={⊤,∅}=> ALC (|={∅,⊤}=> tps_ti G (n, τf)).
  Proof.
    iIntros (BEH FS LB HIST) "(LC& #TR& [HI SIa]& MI& WPs)".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "((%P& #HG& HP& WPs)& HI& %&%&%&%& %H& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO1 LB1].
    iPoseProof (temporal_elim with "HG [$HI $MI $HP]") as "#TF".
    iPoseProof ("WPs" with "HP") as "WPs".
    iMod (all_interp_sfmupd_steps (fair_sched_fun γ) with "WPs HI MI") as "(WPs& HI& %&%&%&%& %H& MI)".
    { split; [apply fair_sched_fun_mon | apply fair_sched_fun_ub]. }
    1: auto.
    destruct H as [LEO2 LB2].
    iPoseProof (big_sepM2_alt with "WPs") as "[%Dom WPs]".
    remember (map_zip Θ Ψs) as TQ. assert (EQTQ : Θ = fst <$> TQ).
    { subst. rewrite fst_map_zip; auto. intro k. rewrite -!elem_of_dom Dom. auto. }
    iAssert ([∗ map] i↦'(e, Q) ∈ TQ,
               lwpupd i ⊤ e (match to_val e with
                             | Some v => (lift_term i Q) v
                             | None => lwp_fix s i ⊤ e (lift_term i Q)
                             end))%I with "[WPs]" as "WPs".
    { iApply (big_sepM_impl with "WPs"). iIntros "!> %%% H". destruct x.
      rewrite lwp_unfold_fix. iEval (rewrite lwp_fix_unfold_fix /lwp_pre) in "H".
      simpl. destruct (to_val e) eqn:He.
      - iApply lwpupd_trans. iApply "H".
      - rewrite lwp_fix_unfold_fix /lwp_pre He. iFrame. }
    iMod (all_interp_lwpupd_steps_gmap γ with "WPs [$HI $SIa] MI") as "(WPs& HI& %&%&%&%& %H& MI)".
    { subst Θ. done. }
    { auto. }
    destruct H as [LEO3 LB3]. iDestruct "HI" as "[HI SIa]".
    (* the check at [n], with the later credit *)
    iMod (inv_acc with "TR") as "[R HcloseR]"; first solve_ndisj.
    iMod (lc_fupd_elim_later with "LC R") as (l) "[Ha #Hl]".
    iMod (treg_mark n l with "Ha Hl HI") as "(HI& Ha& #Hl'& #Hlb)".
    iMod ("HcloseR" with "[Ha]") as "_".
    { iNext. iExists _. iFrame "Ha Hl'". }
    iMod (certify_entries n _ with "Hl' HI MI") as "(HI& MI& #Cs)".
    iPoseProof (bundle_intro n _ with "Hlb Cs") as "#B"; first by rewrite last_snoc.
    iApply (run_step 0 with "[%] [$HI $SIa $MI $WPs]"); first by split_and!.
    iIntros (σ2 Θ2 κs2 TQ2 g2 v2 Ω2 W2 γ2) "%Hstep LC' Sys".
    destruct Hstep as (BEH'& FS'& LB'& HIST'& EQTQ'& DROP).
    iModIntro. iApply (tguar_elim with "TF [%] B Sys"). split_and!; done.
  Qed.

End adequacy.

(** The program logic establishes [G]; anything implied by its trace property holds. *)
Theorem lwp_adequacy_temporal (Σ : gFunctors) (Λ : language)
  `{!mupdGpreS Σ} `{!histGS.histGpreS Σ (state Λ * thread_pool Λ * list (observation Λ))} `{!tregGS.tregGpreS Λ Σ}
  s σ Θ i κs (G : tps Λ Σ) (R : trProp Λ) :
  (∀ τ, tps_tr G τ → R τ) →
  ∀ (τ : trace Λ),
  behavior τ →
  fair_scheduling τ →
  (τ.1 = 0) →
  (τ.2 0 = (Θ, σ, i, κs)) →
  (∀ `{Htemporal : !temporalGS Λ Σ},
     ∃ (c : Ord.t),
     ⊢ |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                (fork_post : thread_id → val Λ → iProp Σ)
                (Ψs : gmap thread_id (H:=pos_countable) (thread_id → val Λ → iProp Σ)),
     let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
     state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
     (treg -∗ £ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
      |={⊤}=>m (∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                  (P -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))) →
  R τ.
Proof.
  intros HR τ BEH FS INIT1 INIT2 Hwp. apply HR.
  assert (iProp_sat
            (|==> ∃ (Hmupd : mupdGS Σ) (Hhist : histGS.histGS Σ (state Λ * thread_pool Λ * list (observation Λ))) (Htreg : tregGS.tregGS Λ Σ),
                let _ : temporalGS Λ Σ := TemporalG Hmupd Hhist Htreg in
                (∃ x : Ord.t, rupd_pred (rupdG:=auth_rupdGS_instance Σ _) x) ∗
                wsat.wsat ∗ wsat.ownE ⊤ ∗
                |={⊤,∅}=> ALC (|={∅,⊤}=> tps_ti G τ))) as Hsat; cycle 1.
  { apply sat_bupd, sat_exists in Hsat. destruct Hsat as (Hmupd& Hsat). apply sat_exists in Hsat. destruct Hsat as (Hhist& Hsat). apply sat_exists in Hsat. destruct Hsat as (Htreg& Hsat).
    set (Htemp := TemporalG Hmupd Hhist Htreg : temporalGS Λ Σ).
    apply (tps_good G (temporalGS0:=Htemp) emp).
    apply (sat_fupd ∅), sat_ALC, (sat_fupd ⊤).
    unfold iProp_sat_lc_at_frame. apply sat_sat_frame. unfold iProp_sat_lc_at, sat_frame. unfold iProp_sat_lc, sat_frame.
    eapply sat_mono. 2: eapply Hsat. simpl. iIntros "($& $& $& $)". }
  assert (Hwp' : ⊢ ∀ Htemporal : temporalGS Λ Σ,
            ∃ (c : Ord.t),
            |={⊤}=> ∃ (Hsic : state_interp_class Λ Σ)
                     (fork_post : thread_id → val Λ → iProp Σ)
                     (Ψs : gmap thread_id (thread_id → val Λ → iProp Σ)),
            let _ : lantanaGS Λ Σ := LantanaG Htemporal Hsic fork_post in
            state_interp σ Θ κs ∗ state_interp_aux σ Θ κs ∗
            (treg -∗ £ c -∗ ([∗ set] i ∈ dom Θ, thP_carriers i ∅) -∗
             |={⊤}=>m (∃ (P : iProp Σ), (P ⊨ₜ G) ∗ P ∗
                         (P -∗ |={⊤}=>m [∗ map] i ↦ e;Ψ ∈ Θ;Ψs, lwpupd i ⊤ e (lWP e @ s; i; ⊤ {{ lift_term i Ψ }}))))).
  { iIntros (Htemp). destruct (Hwp Htemp) as [x Hx]. iExists x. iApply Hx. }
  eapply sat_wand; cycle 1.
  { eapply Hwp'. }
  apply (sat_mono True); cycle 1.
  { apply iProp_sat_intro. }
  iIntros "_ H".
  iMod (model_interp_alloc 0) as "(%Hmupd& R& W& WOE& MI)".
  iMod (history_interp_init σ Θ κs) as "(%Hhist& HI)".
  iMod (treg_alloc (Λ:=Λ)) as "(%Htreg& TR)".
  iExists Hmupd, Hhist, Htreg.
  set (Htemp := TemporalG Hmupd Hhist Htreg : temporalGS Λ Σ).
  iDestruct ("H" $! Htemp) as "(%c& H)".
  iDestruct "R" as "(%x& R)".
  iMod (own_update _ (● x) with "R") as "[R LC]".
  { apply (auth_update_alloc x (((c ⋅ Ord.from_nat 1) : ordinal_ucmra.OrdUR) ⋅ x)).
    apply (op_local_update_discrete x ε (c ⋅ Ord.from_nat 1)).
    intros ?. apply auth_valid_trivial. }
  iModIntro. iFrame "R W WOE". rewrite (right_id ε).
  iDestruct (rupdF_split with "LC") as "[LC LC1]".
  iMod "H" as "(%Hsic& %fork_post& %Ψs& SI& SIa& WPs)".
  iMod ("HI" $! Hsic with "SI") as "HI". iDestruct "MI" as "(MHI& S& T& A& G& MI)".
  iMod (thP_carriers_alloc_threads (dom Θ) with "[$T $G]") as "(T& G& Ths)". 1: set_solver.
  set (Hlantana := LantanaG Htemp Hsic fork_post : lantanaGS Λ Σ).
  iMod (treg_inv_alloc (treg_handle (lantanaGS0:=Hlantana)) with "TR") as "#TR".
  iPoseProof ("WPs" with "TR LC Ths") as "WPs". rewrite union_empty_l_L.
  destruct τ as [n τf]. simpl in INIT1, INIT2. subst n.
  apply fair_scheduling_fscnt in FS. destruct FS as (γ& FS).
  iApply (lwp_ti_logic_temporal (lantanaGS0:=Hlantana) with "[$LC1 $TR $HI $SIa $MHI $S $T $A $G $MI $WPs]").
  1,2: eauto. 1: apply map_Forall2_empty.
  { intros n' σ' Θ' κs' Hlu. rewrite lookup_cons in Hlu. destruct n'; last done. inv Hlu. rewrite INIT2. eauto. }
Qed.

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
Class IntoTemporal `{!lantanaGS Λ Σ} (P : iProp Σ) (G : tps Λ Σ) :=
  into_temporal : ⊢ P ⊨ₜ G.
Global Arguments into_temporal {_ _ _} _ _ {_}.
Global Hint Mode IntoTemporal - - - ! - : typeclass_instances.
(* The search compares guarantees by their formula and trace property: unfolding [temporal]
   when an instance does not match makes the failure very slow. *)
Global Typeclasses Opaque temporal.
(* Likewise for the connectives, which are records ([tps_true] and [tps_finally] stay
   abbreviations). User definitions of trace properties are still unfolded. *)
Global Typeclasses Opaque tps_pure tps_atomic tps_and tps_or tps_impl tps_forall tps_exist
  tps_always tps_until tps_state.

(** Big separating conjunctions guarantee the guarded family of their elements' guarantees. *)
Section big_op_rules.
  Context `{!lantanaGS Λ Σ}.

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
Class SimplExist `{!lantanaGS Λ Σ} {X : Type} (G : X → tps Λ Σ) (G' : tps Λ Σ) :=
  simpl_exist (P : X → iProp Σ) : (∀ x, P x ⊨ₜ G x) ⊢ (∃ x, P x) ⊨ₜ G'.
Global Hint Mode SimplExist - - - - ! - : typeclass_instances.

(** Existentials, dispatched on whether the target is known (hints after [into_temporal]).
    Records, so that a failing unification does not unfold them. *)
Class IntoTemporalExist `{!lantanaGS Λ Σ} {X : Type} (P : X → iProp Σ) (G : tps Λ Σ) :=
  { into_temporal_exist_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoTemporalExist - - - - ! - : typeclass_instances.
(** Against a known target: trace-visible if the target is a [tps_exist] (possibly behind
    definitions), ghost otherwise. *)
Class IntoTemporalExistCheck `{!lantanaGS Λ Σ} {X : Type} (P : X → iProp Σ) (G : tps Λ Σ) :=
  { into_temporal_exist_check_body : ⊢ (∃ x, P x) ⊨ₜ G }.
Global Hint Mode IntoTemporalExistCheck - - - - ! ! : typeclass_instances.

(** The trace property inferred for [P]. *)
Definition tsem `{!lantanaGS Λ Σ} (P : iProp Σ) {G : tps Λ Σ} `{!IntoTemporal P G} : tps Λ Σ := G.
Global Arguments tsem {_ _ _} _ {_ _}.

(** [P] until [Q], and finally [Q]. *)
Notation untilT N k q P Q := (untilI N k false q P%I Q%I).
Notation finallyT N k q Q := (finallyI N k false q Q%I).

(** The inferred trace property of [P], computed so that it no longer mentions ghost-state
    instances: [Definition G : tps Λ Σ := ltac:(tps_of P).] in a section with the instances
    yields a [G] that can be used in an adequacy statement. *)
Ltac tps_of P := let G := eval cbv [tsem] in (tsem P%I) in exact G.

(** [t] is an evar, possibly applied: the target is unknown. *)
Ltac evar_headed t := idtac; lazymatch t with ?f _ => evar_headed f | _ => is_evar t end.

Section into_temporal.
  Context `{!lantanaGS Λ Σ}.
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
  Global Instance into_temporal_alwaysI_view N P V G :
    IntoTemporal V G → IntoTemporal (alwaysI_view N P V) (tps_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_always_view_valid. Qed.
  Global Instance into_temporal_alwaysI N P G :
    IntoTemporal P G → IntoTemporal (alwaysI N P) (tps_always G) | 10.
  Proof. intros H. unfold IntoTemporal in *. by apply temporal_always_valid. Qed.
  Global Instance into_temporal_untilI N k b q P Q G1 G2 :
    IntoTemporal P G1 → IntoTemporal Q G2 → IntoTemporal (untilI N k b q P Q) (tps_until G1 G2) | 10.
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
   ghost-state instance contain no evars (resolution is retried once they are solved). *)
Global Hint Extern 100 (@IntoTemporal ?Λ ?Σ ?H ?P ?G) =>
  assert_fails (has_evar Λ); assert_fails (has_evar Σ); assert_fails (has_evar H);
  assert_fails (has_evar P);
  first [evar_headed G | unify G (@tps_true Λ Σ)];
  notypeclasses refine (into_temporal_default P) : typeclass_instances.

(** ** Examples *)
Section examples.
  Context `{!lantanaGS Λ Σ}.

  (** Ghost quantification over iProp, scoping over two temporal operators. *)
  Local Lemma ex_iprop N1 N2 k :
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyI N2 k false 1 Ψ) ⊨ₜ
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
    ⊢ (∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyT N2 k 1 Ψ) ⊨ₜ
      (tps_always tps_true ∧ tps_until (tps_pure True) tps_true).
  Proof. apply (into_temporal _ _). Qed.

  (** Trace-visible quantification over a small type is inferred when the guarantee of
      the body depends on the witness. *)
  Local Lemma ex_visible_inferred N (f : nat → Prop) :
    ⊢ (∃ n : nat, alwaysI N ⌜f n⌝) ⊨ₜ tps_exist (λ n : nat, tps_always (tps_pure (f n))).
  Proof. apply (into_temporal _ _). Qed.

  (** The inferred trace property as a closed term. *)
  Local Definition ex_tps_of N1 N2 k : tps Λ Σ :=
    ltac:(tps_of ((∃ Ψ : iProp Σ, alwaysI N1 Ψ ∗ finallyT N2 k 1 Ψ)%I)).
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
