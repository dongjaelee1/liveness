From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export itprop_rules.
From transfinite.stepindex Require Import ordinals.

(** * Temporal guarantees [P ⊨ₜ G]: records, the one-step property, rules for connectives

    Temporal formulas are ordinary iProps; [P ⊨ₜ G] is a persistent iProp saying that whenever
    [P] holds, the rest of the execution satisfies the trace property [G]. Adequacy concludes
    [itProp_external G].

    At position [n], [P ⊨ₜ G] turns [P] into a record [tguar G n], which gives the reading of
    [G] at [n] once the step from [n] is made. A record may be written in the pre-step update
    of step [n] (e.g. by discharging an until), so it is eliminated after the step, against
    the bundle of certificates for [n]: each registered structure (temporal_registry.v) has
    its content certified at every position. A record holds for any running system with the
    one-step property [sys_step]; [lWP] is one (adequacy_temporal.v).

    An existential is trace-visible ([itProp_exist]) only over small types (nat, Z, loc, gname,
    ...), otherwise ghost ([temporal_exist_ghost]). The trace property of the adequacy is
    fixed at the meta level: dynamic names reach it through trace-visible existentials. *)

(** ** Guarantees *)

Section guarantee.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : itProp Λ Σ.
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

  (** The certificate of a registered item at [n]: a later-guarded record of its content at
      [n]. For an until, the record of its left or right formula at [n], or, if it was
      discharged at [n' ≤ n], the record of its right formula at [n']. *)
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

  (** The one-step property of [Sys]: from a consistent system at [n], the bundle for [n]
      (the check), then after the step the system at [S n], the facts about the step and
      later credits. The modalities are those of [trI_always] and [trI_until]. *)
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
  Definition tguar G n : iProp Σ := tguar_ti (itProp_internal G) n.
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
      itProp_internal G (n, τf)) ⊢ tguar G n.
  Proof. apply tguar_ti_intro. Qed.

  Lemma tguar_elim G (Sys : sysT) l h n g v Ω W τf γ σ Θ κs :
    tguar G n -∗
    sys_step Sys -∗
    ⌜behavior (n, τf) ∧ beh_fscnt (S n, τf) γ ∧ owit_inv_lb (fair_sched_fun γ) Ω W ∧ hist_trace h τf⌝ -∗
    bundle l n -∗
    history_interp h (S n) σ Θ κs ∗ model_interp g v Ω W (S n) (dom Θ) ∗ Sys (S n) σ Θ κs -∗
    itProp_internal G (n, τf).
  Proof. apply tguar_ti_elim. Qed.

  Lemma temporal_elim P G h n σ Θ κs m i Ω W :
    temporal P G -∗
    history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) ∗ P -∗ tguar G n.
  Proof. iIntros "#HG H". by iApply "HG". Qed.

  (** For the certificates: a later-guarded content gives a later-guarded record. *)
  Lemma temporal_elim_later P G h n σ Θ κs m i Ω W :
    temporal P G -∗
    ▷ P ∗ history_interp h n σ Θ κs ∗ model_interp m i Ω W n (dom Θ) -∗ ▷ tguar G n.
  Proof. iIntros "#HG (HP& HI& MI)". iNext. iApply ("HG" with "[$HI $MI $HP]"). Qed.

  (** The same with a later-guarded guarantee, as stored with a registered structure. *)
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

  Lemma tguar_mono G G' n : itProp_le G G' → tguar G n ⊢ tguar G' n.
  Proof.
    iIntros (Hle) "#HG". iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W".
    iApply Hle. by iApply (tguar_elim with "HG ST [//] B W").
  Qed.

End guarantee.

Notation "P ⊨ₜ G" := (temporal P%I G%IT) (at level 70, format "P  ⊨ₜ  G") : bi_scope.

(** The canonical trace property of an iProp: the meet of all trace properties that it
    validly guarantees. The registered structures store it for their contents, so temporal
    formulas carry no trace-property annotations. *)
Definition itProp_sem `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (Q : iProp Σ) : itProp Λ Σ :=
  itProp_forall (λ G : {G : itProp Λ Σ | ⊢ Q ⊨ₜ G}, proj1_sig G).
(* Opaque for the proof mode: unification must not compare two [itProp_sem] through their
   bodies (the index type is a proposition about the argument). *)
Global Typeclasses Opaque itProp_sem.

(** ** Rules *)

Section rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.
  Implicit Types G : itProp Λ Σ.

  Lemma temporal_weaken P G G' : G ⊑ G' → P ⊨ₜ G ⊢ P ⊨ₜ G'.
  Proof.
    iIntros (Hle) "#HG !>". iIntros (?????????) "H". iApply tguar_mono; first done. by iApply "HG".
  Qed.

  (** Every trace-level consequence [R] of [G] is guaranteed along with [G], as the cast of
      [G] to [R]: the general way to export what a guarantee implies. *)
  Lemma temporal_cast P G R (pf : itProp_external G ⊆ R) : P ⊨ₜ G ⊢ P ⊨ₜ itProp_cast G R pf.
  Proof. apply temporal_weaken, itProp_cast_le. Qed.

  Lemma temporal_mono P Q G : □ (Q -∗ P) -∗ P ⊨ₜ G -∗ Q ⊨ₜ G.
  Proof.
    iIntros "#HQP #HG !>". iIntros (?????????) "(HI& MI& HQ)". iApply "HG". iFrame. by iApply "HQP".
  Qed.

  Lemma temporal_true P : ⊢ P ⊨ₜ itProp_true.
  Proof.
    iIntros "!>" (?????????) "_". iApply tguar_intro. iIntros "!>" (????????????) "_ _ _ _". done.
  Qed.

  Lemma temporal_pure (φ : Prop) : ⊢ ⌜φ⌝ ⊨ₜ itProp_pure φ.
  Proof.
    iIntros "!>" (?????????) "(_& _& %Hφ)". iApply tguar_intro. iIntros "!>" (????????????) "_ _ _ _". done.
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

  (** The right formula fulfils an until at once; the later of the guarantee is stripped
      by the step of the until. *)
  Lemma temporal_until_now P G1 G2 : ▷ (P ⊨ₜ G2) -∗ P ⊨ₜ itProp_until G1 G2.
  Proof.
    iIntros "#HG !>" (h n σ Θ κs m i Ω W) "(HI& MI& HP)".
    iPoseProof (temporal_elim_later_guar P G2 with "HG [$HP $HI $MI]") as "#T".
    iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W".
    rewrite /= /trI_exist. iExists Ord.O. rewrite trI_until_unfold /trI_until_pre.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iNext. iMod "close" as "_". iModIntro.
    iApply fupd_mask_intro; first set_solver. iIntros "close". iApply ALC_intro. iMod "close" as "_".
    iModIntro. iLeft. by iApply (tguar_elim with "T ST [//] B W").
  Qed.

  (** Universal quantification over any type. *)
  Lemma temporal_forall {X : Type} (P : X → iProp Σ) (G : X → itProp Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∀ x, P x) ⊨ₜ itProp_forall G.
  Proof.
    iIntros "#HG !>" (?????????) "(HI& MI& HP)".
    iAssert (∀ x, tguar (G x) _)%I with "[-]" as "#T".
    { iIntros (x). iApply (temporal_elim with "HG"). iFrame. iApply "HP". }
    iApply tguar_intro. iIntros "!>" (????????????) "#ST %H #B W". iIntros (x).
    by iApply (tguar_elim with "T ST [//] B W").
  Qed.

  Lemma temporal_sem Q : ⊢ Q ⊨ₜ itProp_sem Q.
  Proof.
    iApply (temporal_mono (∀ _ : {G : itProp Λ Σ | ⊢ Q ⊨ₜ G}, Q)%I with "[]").
    { iIntros "!> HQ" (?). done. }
    iApply temporal_forall. iIntros ([G HG]). iApply HG.
  Qed.
  Lemma itProp_sem_le Q G : (⊢ Q ⊨ₜ G) → itProp_le (itProp_sem Q) G.
  Proof.
    intros HG ??. rewrite /= /trI_forall. iIntros "H". iApply ("H" $! (exist (λ G, ⊢ Q ⊨ₜ G) G HG)).
  Qed.
  Lemma itProp_sem_ext Q G τ : (⊢ Q ⊨ₜ G) → itProp_external (itProp_sem Q) τ → itProp_external G τ.
  Proof. intros HG H. apply (H (exist (λ G, ⊢ Q ⊨ₜ G) G HG)). Qed.

  (** [itProp_sem Q] is the greatest lower bound of the properties [Q] validly guarantees: the
      rules for guarantees are complete, up to in-logic entailment, through it. *)
  Lemma temporal_sem_complete Q G : (⊢ Q ⊨ₜ G) ↔ itProp_sem Q ⊑ G.
  Proof.
    split; first apply itProp_sem_le. intros Hle.
    iApply (temporal_weaken _ _ _ Hle). iApply temporal_sem.
  Qed.

  (** Its trace reading: the strongest trace property [Q] validly guarantees. [Q] guarantees
      a trace property [R] iff it validly guarantees some [G] whose trace reading implies
      [R]. *)
  Definition tr_sem Q : trProp Λ := itProp_external (itProp_sem Q).
  Lemma tr_sem_le Q R : tr_sem Q ⊆ R ↔ ∃ G, (⊢ Q ⊨ₜ G) ∧ itProp_external G ⊆ R.
  Proof.
    split.
    - intros HR. exists (itProp_sem Q). split; [apply temporal_sem|done].
    - intros (G & HG & HR) τ Hτ. apply HR. by eapply itProp_sem_ext.
  Qed.

  (** Trace-visible existential quantification, over small types. *)
  Lemma temporal_exist {X : Type} `{!TypeExistentialProperty X ordI} (P : X → iProp Σ) (G : X → itProp Λ Σ) :
    (∀ x, P x ⊨ₜ G x) -∗ (∃ x, P x) ⊨ₜ itProp_exist G.
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

  (** A persistent token [C] excluding [A]: a guarantee of [B] is one of [A ∨ B]. With
      [alwaysI_register_guar], this gives a stronger reading of an invariant. *)
  Lemma temporal_or_excl (A B C : iProp Σ) G `{!Persistent C} :
    (C ∗ A ⊢ False) → C -∗ B ⊨ₜ G -∗ (A ∨ B) ⊨ₜ G.
  Proof.
    iIntros (Hexcl) "#HC #HB". iIntros "!>" (h n σ Θ κs m i Ω W) "(HI& MI& [HA|HB'])".
    - iExFalso. iApply Hexcl. iFrame "HC HA".
    - iApply (temporal_elim with "HB"). iFrame.
  Qed.

End rules.

(** ** State atoms

    The atoms of temporal properties are facts about the current state: an iProp [P]
    determines [φ] when the state interpretation and [P] entail [φ] ([StateFact]), and then
    [P] guarantees [itProp_state φ] ([temporal_state_fact]). A language provides the facts of
    its assertions, e.g. [l ↦ v] for heap_lang (temporal_laws.v). *)
Section state_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Class StateFact (P : iProp Σ) (φ : state Λ → thread_pool Λ → Prop) : Prop :=
    state_fact σ Θ κs : state_interp σ Θ κs ∗ P ⊢ ⌜φ σ Θ⌝.

  Lemma temporal_state (φ : state Λ → thread_pool Λ → Prop) (P : iProp Σ) :
    (∀ σ Θ κs, state_interp σ Θ κs ∗ P ⊢ ⌜φ σ Θ⌝) → ⊢ P ⊨ₜ itProp_state φ.
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

  Lemma temporal_state_fact P φ `{!StateFact P φ} : ⊢ P ⊨ₜ itProp_state φ.
  Proof. apply temporal_state, state_fact. Qed.

End state_rules.

(** ** Implications

    The antecedent [A] of [A → G] is read on the trace ([itProp_impl]), so [A → G] is [¬A ∨ G]
    ([itProp_impl_or_not]). An implication is a statement about traces, and the general way
    to export one is the cast ([temporal_cast]): from [P ⊨ₜ H] and
    [itProp_external A ∧ itProp_external H ⊆ R] on traces, where every law of LTL is available, [P]
    guarantees [itProp_external A → R]. The rules below stay in the logic and produce the connective
    [itProp_impl] itself: from a complete antecedent ([temporal_impl_intro]), by weakening
    ([temporal_impl_weaken]), and for a pure antecedent of an iProp implication
    ([temporal_impl]). An iProp antecedent that the context does not provide cannot be used:
    see [naive_impl_rule_unsound] in guarantee_infer.v. *)
Section impl_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma temporal_impl_intro P A H G `{!ItPropComplete A} :
    (A ∧ H)%IT ⊑ G → P ⊨ₜ H ⊢ P ⊨ₜ (A → G).
  Proof. intros HG. by apply temporal_weaken, itProp_impl_intro. Qed.

  Lemma temporal_impl_weaken P A G : P ⊨ₜ G ⊢ P ⊨ₜ (A → G).
  Proof. apply temporal_weaken, itProp_impl_intro_le. Qed.

  (** A pure antecedent is decided outside the logic. *)
  Lemma temporal_impl (φ : Prop) P G : P ⊨ₜ G -∗ (⌜φ⌝ → P) ⊨ₜ (⌜φ⌝ → G).
  Proof.
    iIntros "#HG". destruct (Classical_Prop.classic φ) as [Hφ|Hφ].
    - iApply temporal_impl_weaken. iApply (temporal_mono with "[] HG"). iIntros "!> HP". by iApply "HP".
    - iApply (temporal_weaken _ itProp_true); last iApply temporal_true.
      intros ??. rewrite /= /trI_impl. by iIntros "_ %".
  Qed.

End impl_rules.

(** Big separating conjunctions guarantee the guarded family of their elements' guarantees. *)
Section big_op_rules.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Lemma temporal_big_sepM `{Countable K} {A} (m : gmap K A) (Φ : K → A → iProp Σ) (G : K → A → itProp Λ Σ) :
    (∀ k x, Φ k x ⊨ₜ G k x) -∗
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊨ₜ itProp_forall (λ k, itProp_forall (λ x, itProp_impl ⌜m !! k = Some x⌝ (G k x))).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ k x, ⌜m !! k = Some x⌝ → Φ k x)%I with "[]").
    { iIntros "!> H" (k x Hk). by iApply (big_sepM_lookup with "H"). }
    iApply temporal_forall. iIntros (k). iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

  Lemma temporal_big_sepL {A} (l : list A) (Φ : nat → A → iProp Σ) (G : nat → A → itProp Λ Σ) :
    (∀ k x, Φ k x ⊨ₜ G k x) -∗
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊨ₜ itProp_forall (λ k, itProp_forall (λ x, itProp_impl ⌜l !! k = Some x⌝ (G k x))).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ k x, ⌜l !! k = Some x⌝ → Φ k x)%I with "[]").
    { iIntros "!> H" (k x Hk). by iApply (big_sepL_lookup with "H"). }
    iApply temporal_forall. iIntros (k). iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

  Lemma temporal_big_sepS `{Countable A} (X : gset A) (Φ : A → iProp Σ) (G : A → itProp Λ Σ) :
    (∀ x, Φ x ⊨ₜ G x) -∗
    ([∗ set] x ∈ X, Φ x) ⊨ₜ itProp_forall (λ x, itProp_impl ⌜x ∈ X⌝ (G x)).
  Proof.
    iIntros "#HG". iApply (temporal_mono (∀ x, ⌜x ∈ X⌝ → Φ x)%I with "[]").
    { iIntros "!> H" (x Hx). by iApply (big_sepS_elem_of with "H"). }
    iApply temporal_forall. iIntros (x). iApply temporal_impl. iApply "HG".
  Qed.

End big_op_rules.
