From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export guarantee.
From transfinite.stepindex Require Import ordinals.

(** * The registry state and the registered structures, with their rules

    From here on, the interpretation of the temporal layer ([TemporalInterp],
    temporal_class.v) is the registry state ([treg_temporal_interp]). *)

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
    (guarantee_rec.v). The common cases: [alwaysI N P] reads as the canonical trace
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
    closed proofs about a recursively defined structure (guarantee_rec.v, [renew]). *)
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
      (guarantee_rec.v). *)
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
      side (guarantee_rec.v). *)
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
