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

  (** Records of a trace property, the bundle and the certificates. *)
  Definition tguar G n : iProp Σ := tguar_ti (tps_ti G) n.
  Definition bundle l n : iProp Σ := bundle_pre tguar_ti l n.
  Definition cert n e : iProp Σ := cert_pre tguar_ti n e.

  (** [P ⊨ₜ G]: whenever [P] holds, the rest of the execution satisfies [G]. *)
  Definition temporal P G : iProp Σ :=
    □ ∀ h n σ Θ κs m i Ω W,
      history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ P -∗ tguar G n.

  Global Instance tguar_persistent G n : Persistent (tguar G n).
  Proof. apply _. Qed.
  Global Instance cert_persistent n e : Persistent (cert n e).
  Proof. rewrite /cert. destruct e; apply _. Qed.
  Global Instance bundle_persistent l n : Persistent (bundle l n).
  Proof. apply _. Qed.
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
  | RAlways N γ => ⌜N ## tregN⌝ ∗ ∃ P : iProp Σ, saved_ti γ (tps_ti (tps_sem P)) ∗ inv N P
  | RUntil N k γP γQ =>
      ⌜N ## tregN⌝ ∗ ∃ P Q : iProp Σ, saved_ti γP (tps_ti (tps_sem P)) ∗ saved_ti γQ (tps_ti (tps_sem Q)) ∗
        oblP_inv N k P Q (until_disch k (tps_sem Q))
  end.
Definition treg `{!lantanaGS Λ Σ} : iProp Σ := treg_inv treg_handle.

(** An invariant whose content is trace-visible: an invariant, registered, with the record
    of its content at its allocation position. *)
Definition alwaysI `{!lantanaGS Λ Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
  ∃ j r γ st, ⌜N ## tregN⌝ ∗ reg_idx j r (RAlways N γ) ∗ hG_event r st ∗
              saved_ti γ (tps_ti (tps_sem P)) ∗ inv N P ∗ treg ∗ ▷ tguar (tps_sem P) r.
(* Opaque for the proof mode: [iNext] must not unfold a structure to strip its inner later. *)
Global Typeclasses Opaque alwaysI.

(** The persistent part of an until: its obligation invariant, registered, with the records
    of its contents at its allocation position, where its obligation was assigned. *)
Definition untilI_pers `{!lantanaGS Λ Σ} (N : namespace) (k : positive) (P Q : iProp Σ) : iProp Σ :=
  ∃ j r γP γQ st v Ω fu o,
    ⌜N ## tregN⌝ ∗ reg_idx j r (RUntil N k γP γQ) ∗ hG_event r st ∗
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

  (** The same at the level of [sfgupd]: reading the history too, which the final fancy
      update may still use. *)
  Lemma sfgupd_read E (P : iProp Σ) :
    (∀ h n σ Θ κs g i Ω W,
      history_interp h n σ Θ κs -∗ model_interp g i Ω W n (dom Θ) -∗
      model_interp g i Ω W n (dom Θ) ∗ |={E}=> history_interp h n σ Θ κs ∗ P) ⊢ |={E}=>g P.
  Proof.
    iIntros "H". unfold_sfgupd. iIntros (h n σ Θ κs) "HI". rewrite /fgupd.
    iApply fupd_mask_intro; first set_solver. iIntros "close".
    iApply gupd_read. iIntros (g i Ω W) "MI". iDestruct ("H" with "HI MI") as "($& HP)".
    iMod "close" as "_". iMod "HP" as "[HI HP]". iModIntro. iFrame.
  Qed.

End gupd_read.

(** ** Rules for [alwaysI] *)
Section always_rules.
  Context `{!lantanaGS Λ Σ}.

  Global Instance alwaysI_persistent N P : Persistent (alwaysI N P).
  Proof. rewrite /alwaysI. apply _. Qed.
  Global Instance treg_handle_persistent e : Persistent (treg_handle e).
  Proof. destruct e; apply _. Qed.
  Global Instance treg_persistent : Persistent treg.
  Proof. apply _. Qed.

  Lemma alwaysI_inv N P : alwaysI N P ⊢ inv N P.
  Proof. rewrite /alwaysI. iIntros "(%&%&%&%& _& _& _& _& $& _)". Qed.
  Lemma alwaysI_treg N P : alwaysI N P ⊢ treg.
  Proof. rewrite /alwaysI. iIntros "(%&%&%&%& _& _& _& _& _& $& _)". Qed.

  Lemma alwaysI_acc E N P :
    ↑N ⊆ E → alwaysI N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof. iIntros (?) "#H". iApply inv_acc; first done. by iApply alwaysI_inv. Qed.

  (** Allocation registers the invariant and records its content at the current position:
      a model update, reading the model. *)
  Lemma alwaysI_alloc E N P :
    ↑tregN ⊆ E → N ## tregN →
    treg -∗ £n 1 -∗ ▷ P -∗ |={E}=>g alwaysI N P.
  Proof.
    iIntros (HE HN) "#TR LC HP". iApply sfgupd_read. iIntros (h n σ Θ κs g i Ω W) "HI MI".
    iPoseProof (temporal_elim_later with "[] [$HP $HI $MI]") as "#C"; first iApply temporal_sem.
    iPoseProof (history_interp_hG_event_now with "HI") as "#HE".
    iFrame "MI".
    iMod (saved_ti_alloc (tps_ti (tps_sem P))) as (γ) "#Hγ".
    iMod (inv_alloc N _ P with "HP") as "#Hinv".
    iMod (treg_register treg_handle E (RAlways N γ) with "LC TR [] HI") as "[HI (%j& #Hj)]"; first done.
    { iIntros (st) "_". simpl. iSplit; first done. iExists P. iFrame "Hγ Hinv". }
    iModIntro. iFrame "HI". rewrite /alwaysI. iExists j, n, γ, _. iFrame "#". done.
  Qed.

End always_rules.

(** ** Rules for [untilI] *)
Section until_rules.
  Context `{!lantanaGS Λ Σ}.

  Global Instance untilI_pers_persistent N k P Q : Persistent (untilI_pers N k P Q).
  Proof. rewrite /untilI_pers. apply _. Qed.

  Lemma untilI_pers_inv N k P Q : untilI_pers N k P Q ⊢ oblP_inv N k P Q (until_disch k (tps_sem Q)).
  Proof. rewrite /untilI_pers. iIntros "(%&%&%&%&%&%&%&%&%& _& _& _& _& _& $& _)". Qed.
  Lemma untilI_pers_treg N k P Q : untilI_pers N k P Q ⊢ treg.
  Proof. rewrite /untilI_pers. iIntros "(%&%&%&%&%&%&%&%&%& _& _& _& _& _& _& $& _)". Qed.
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
                 ∀ E' N (P Q : iProp Σ), ⌜↑tregN ⊆ E' ∧ N ## tregN⌝ -∗ treg -∗ £n 1 -∗
                   ▷ (if b then Q else P) -∗ |={E'}=>g untilI N k b 1 P Q.
  Proof.
    iIntros (Ltl) "TG". iMod (obl_alloc_assigned with "TG") as "(%k& $& $& Oa& $& $& ACC)". 1: auto.
    iIntros "!> %E' %N %P %Q [%HE %HN] #TR LC HC".
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
    { iIntros (st) "_". simpl. iSplit; first done. iExists P, Q. iFrame "HγP HγQ OI". }
    iModIntro. iFrame "HI". rewrite untilI_unfold /untilI_pers. iSplitL "Oa".
    { iEval (unfold_opreds). iFrame "OE Oa". }
    iExists j, n, γP, γQ, _, i, Ω, fu, o. iSplit; first done. iFrame "Hj HE HγP HγQ OI TR EA C".
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

  (** The certificate of one registered item. *)
  Lemma cert_of_handle n e h σ Θ κs g v Ω W :
    treg_handle e -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤ ∖ ↑tregN}=∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ cert n e.
  Proof.
    iIntros "#Hd HI MI". destruct e; simpl.
    - by iFrame.
    - iDestruct "Hd" as "(%HN& %P& #SP& #Hinv)".
      iMod (inv_acc with "Hinv") as "[HP Hclose]"; first solve_ndisj.
      iPoseProof (temporal_elim_later with "[] [$HP $HI $MI]") as "#C"; first iApply temporal_sem.
      iMod ("Hclose" with "HP") as "_". iModIntro. iFrame "HI MI". iExists _. iFrame "SP C".
    - iDestruct "Hd" as "(%HN& %P& %Q& #SP& #SQ& #OI)".
      iAssert (⌜∃ o, Ω !! k = Some o⌝)%I as %[o Hk].
      { iDestruct "MI" as "(_& S& _)". iEval (unfold_opreds) in "OI". iDestruct "OI" as "[#Oe _]".
        iDestruct (osat_elem_lookup with "[$S $Oe]") as "[%H|[_ %H]]"; iPureIntro.
        - destruct H as (?&?&?). eauto.
        - eauto. }
      iMod (oblP_inv_acc with "OI") as "[Var ACC]"; first solve_ndisj.
      destruct o.
      + iPoseProof (until_cert_assigned with "[$Var $HI $MI]") as "#C"; first done.
        iMod ("ACC" with "[Var]") as "_"; first by iNext; iApply oblP_variant_unfold.
        iModIntro. iFrame "HI MI". iExists _, _. iFrame "SP SQ". by iLeft.
      + iPoseProof (until_cert_discharged with "[$Var $HI $MI]") as "#C"; first done.
        iMod ("ACC" with "[Var]") as "_"; first by iNext; iApply oblP_variant_unfold.
        iModIntro. iFrame "HI MI". iExists _, _. iFrame "SP SQ". by iRight.
  Qed.

  Lemma certify_entries n l h σ Θ κs g v Ω W :
    treg_entries treg_handle l -∗ history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤ ∖ ↑tregN}=∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗ [∗ list] pe ∈ l, cert n pe.2.
  Proof.
    iIntros "#Hl HI MI". iInduction l as [|pe l] "IH".
    - iModIntro. iFrame. done.
    - rewrite /treg_entries !big_sepL_cons. iDestruct "Hl" as "[[_ #Hd] #Hl']".
      iMod (cert_of_handle with "Hd HI MI") as "(HI& MI& #C)".
      iMod ("IH" with "Hl' HI MI") as "($& $& #Cs)". iModIntro. iFrame "C Cs".
  Qed.

  (** The check at position [n], with the registry open: certify every entry and append the
      marker. The result is the bundle for [n]. *)
  Lemma certify n l h σ Θ κs g v Ω W :
    reg_auth l -∗ treg_entries treg_handle l -∗
    history_interp h n σ Θ κs -∗ model_interp g v Ω W n (dom Θ) ={⊤ ∖ ↑tregN}=∗
    history_interp h n σ Θ κs ∗ model_interp g v Ω W n (dom Θ) ∗
    reg_auth (l ++ [(n, RMark)]) ∗ treg_entries treg_handle (l ++ [(n, RMark)]) ∗ bundle (l ++ [(n, RMark)]) n.
  Proof.
    iIntros "Ha #Hl HI MI".
    iDestruct (treg_entries_bound with "Hl HI") as %Hb.
    iMod (certify_entries with "Hl HI MI") as "(HI& MI& #Cs)".
    iMod (reg_auth_append l n RMark with "Ha") as "[Ha #Hj]"; first done.
    iDestruct (history_interp_hG_event_now with "HI") as "#Hnow".
    iDestruct (reg_auth_lb with "Ha") as "#Hlb".
    iModIntro. iFrame "HI MI Ha". iSplit.
    { rewrite /treg_entries big_sepL_app big_sepL_singleton. iFrame "Hl". iSplit; [by iExists _|done]. }
    rewrite /bundle /bundle_pre. iFrame "Hlb". iSplit; first by rewrite last_snoc.
    rewrite big_sepL_app big_sepL_singleton. iFrame "Cs".
  Qed.

End certification.

(** ** Adequacy, up to trace implication *)
Section adequacy.
  Context `{!lantanaGS Λ Σ}.

  (** The registered structures guarantee the always and until of the canonical trace
      properties of their contents. *)
  Lemma temporal_always N P : ⊢ alwaysI N P ⊨ₜ tps_always (tps_sem P).
  Proof.
  Admitted. (* LOOP-ADMIT: M5, the always loop (certify, step, decide). *)

  Lemma temporal_until N k b q P Q : ⊢ untilI N k b q P Q ⊨ₜ tps_until (tps_sem P) (tps_sem Q).
  Proof.
  Admitted. (* LOOP-ADMIT: M5, the until loop (certify, step, read the obligation at S n, decide). *)

  (** With valid guarantees of the contents. *)
  Lemma temporal_always_valid N P G : (⊢ P ⊨ₜ G) → ⊢ alwaysI N P ⊨ₜ tps_always G.
  Proof.
    intros HG. iApply (temporal_weaken _ (tps_always (tps_sem P))).
    { apply tps_always_mono. by apply tps_sem_le. }
    iApply temporal_always.
  Qed.
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
  Admitted. (* LOOP-ADMIT: M5, one iteration of the run at the initial position. *)

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
