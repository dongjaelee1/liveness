From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.
From lantana.trace Require Export guarantee_rules.
From lantana.program_logic Require Export obl_forest_instance.
From transfinite.stepindex Require Import ordinals.

(** * The temporal formulas [alwaysI], [untilI], and the registry state

    Here the interpretation of the temporal layer becomes the registry state
    ([treg_temporal_interp]). This file defines the formulas; temporal_formula_run.v
    certifies them along a run, and temporal_formula_rules.v has their rules. *)

(** Once discharged, the obligation invariant of an until keeps the record of its right
    formula at the discharge event. *)
Notation until_disch k G2 :=
  (∃ n' i' Ω', event_obl i' (n', Ω') k obl_discharged ∗ tguar G2 n')%I (only parsing).

(** ** The registry and the registered structures

    The handle of a registered item: the saved readings of its contents and its invariant,
    which a run opens at every position to certify the content. *)
Definition treg_handle `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (e : rentry) : iProp Σ :=
  match e with
  | RMark => True
  | RAlways N γ => ∃ (P : iProp Σ) (G : itrProp Λ Σ), saved_ti γ (itrProp_internal G) ∗ inv N P ∗ ▷ (P ⊨ₜ G)
  | RUntil N k γP γQ =>
      ∃ (P : iProp Σ) (G1 G2 : itrProp Λ Σ), saved_ti γP (itrProp_internal G1) ∗ saved_ti γQ (itrProp_internal G2) ∗
        oblP_inv N k P (until_disch k G2) ∗ ▷ (P ⊨ₜ G1)
  end.
Definition treg_state `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : iProp Σ := treg_st treg_handle.
Global Instance treg_temporal_interp `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : TemporalInterp Λ Σ :=
  treg_state.
Lemma temporal_interp_treg `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} : temporal_interp = treg_state.
Proof. done. Qed.

(** An invariant [P] made trace-visible through a guarantee [G] of its content: registered
    with [G] and a later-guarded proof of [P ⊨ₜ G] (which may be a hypothesis at
    registration), and the record of [G] at its registration. [alwaysI N P] reads as
    [itrProp_sem P], [alwaysI_as N P V] as [itrProp_sem V]. Sealed: the proof mode must not unify two
    structures through their bodies. *)
Local Definition alwaysI_guar_def `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (N : namespace) (P : iProp Σ) (G : itrProp Λ Σ) : iProp Σ :=
  ∃ j r γ st, reg_idx j r (RAlways N γ) ∗ hG_event r st ∗
              saved_ti γ (itrProp_internal G) ∗ inv N P ∗ ▷ (P ⊨ₜ G) ∗ ▷ tguar G r.
Local Definition alwaysI_guar_aux : seal (@alwaysI_guar_def). Proof. by eexists. Qed.
Definition alwaysI_guar := alwaysI_guar_aux.(unseal).
Global Arguments alwaysI_guar {Λ Σ _ _} N P G.
Local Lemma alwaysI_guar_unseal : @alwaysI_guar = @alwaysI_guar_def.
Proof. rewrite -alwaysI_guar_aux.(seal_eq) //. Qed.
Lemma alwaysI_guar_unfold `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N P G :
  alwaysI_guar N P G = (∃ j r γ st, reg_idx j r (RAlways N γ) ∗ hG_event r st ∗
                        saved_ti γ (itrProp_internal G) ∗ inv N P ∗ ▷ (P ⊨ₜ G) ∗ ▷ tguar G r)%I.
Proof. by rewrite alwaysI_guar_unseal. Qed.
Definition alwaysI_as `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (N : namespace) (P V : iProp Σ) : iProp Σ :=
  alwaysI_guar N P (itrProp_sem V).
Definition alwaysI `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
  alwaysI_as N P P.
(* Opaque for the proof mode: [iNext] must not unfold a structure to strip its inner later. *)
Global Typeclasses Opaque alwaysI_as alwaysI.

(** The persistent part of [P] until [Q], read as [G1] until [G2]: its registered obligation
    invariant, later-guarded proofs of [P ⊨ₜ G1] and [Q ⊨ₜ G2], and the record of [G1] at
    its allocation. *)
Definition untilI_guar_pers `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (N : namespace) (k : positive) (P Q : iProp Σ) (G1 G2 : itrProp Λ Σ) : iProp Σ :=
  ∃ j r γP γQ st v Ω fu o,
    reg_idx j r (RUntil N k γP γQ) ∗ hG_event r st ∗
    saved_ti γP (itrProp_internal G1) ∗ saved_ti γQ (itrProp_internal G2) ∗
    oblP_inv N k P (until_disch k G2) ∗ ▷ (P ⊨ₜ G1) ∗ ▷ (Q ⊨ₜ G2) ∗
    event_obl v (r, Ω) k (obl_assigned fu o) ∗ ▷ tguar G1 r.
Global Typeclasses Opaque untilI_guar_pers.
(** With the canonical readings. *)
Definition untilI_pers `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  (N : namespace) (k : positive) (P Q : iProp Σ) : iProp Σ :=
  untilI_guar_pers N k P Q (itrProp_sem P) (itrProp_sem Q).
Global Typeclasses Opaque untilI_pers.

(** [P] until [Q] with namespace [N] and obligation [k], read as [G1] until [G2]: the token
    of the assigned obligation and the persistent part. *)
Local Definition untilI_guar_def `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  N k (q : Qp) (P Q : iProp Σ) (G1 G2 : itrProp Λ Σ) : iProp Σ :=
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
  untilI_guar N k q P Q (itrProp_sem P) (itrProp_sem Q).
Local Definition untilI_aux : seal (@untilI_def). Proof. by eexists. Qed.
Definition untilI := untilI_aux.(unseal).
Global Arguments untilI {Λ Σ _ _} N k q P Q.
Local Lemma untilI_unseal : @untilI = @untilI_def.
Proof. rewrite -untilI_aux.(seal_eq) //. Qed.
Lemma untilI_guar_canonical `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N k q P Q :
  untilI N k q P Q = untilI_guar N k q P Q (itrProp_sem P) (itrProp_sem Q).
Proof. by rewrite untilI_unseal. Qed.
Lemma untilI_unfold `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N k q P Q :
  untilI N k q P Q = (oblP_assigned k (q/2)%Qp ∗ untilI_pers N k P Q)%I.
Proof. by rewrite untilI_guar_canonical untilI_guar_unfold. Qed.

Definition finallyI `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} N k (q : Qp) (Q : iProp Σ) : iProp Σ :=
  untilI N k q True Q.

(** A done until, fulfilled at its allocation: its right formula [Q], the discharged
    obligation [k], and a later-guarded proof of [Q ⊨ₜ G2]. Wherever it is held, [Q] holds,
    so it is read as [G1] until [G2] for any [G1]; nothing is registered. A persistent part
    alone would guarantee no until: a persistent resource holds at every later position.
    Sealed, like [untilI_guar]. *)
Local Definition untilI_done_guar_def `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}
  k (Q : iProp Σ) (G2 : itrProp Λ Σ) : iProp Σ :=
  Q ∗ oblP_discharged k ∗ ▷ (Q ⊨ₜ G2).
Local Definition untilI_done_guar_aux : seal (@untilI_done_guar_def). Proof. by eexists. Qed.
Definition untilI_done_guar := untilI_done_guar_aux.(unseal).
Global Arguments untilI_done_guar {Λ Σ _ _} k Q G2.
Local Lemma untilI_done_guar_unseal : @untilI_done_guar = @untilI_done_guar_def.
Proof. rewrite -untilI_done_guar_aux.(seal_eq) //. Qed.
Lemma untilI_done_guar_unfold `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} k Q G2 :
  untilI_done_guar k Q G2 = (Q ∗ oblP_discharged k ∗ ▷ (Q ⊨ₜ G2))%I.
Proof. by rewrite untilI_done_guar_unseal. Qed.
(** With the canonical reading. *)
Definition untilI_done `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} k (Q : iProp Σ) : iProp Σ :=
  untilI_done_guar k Q (itrProp_sem Q).
Global Typeclasses Opaque untilI_done.

(** ** Reading the model under a model update

    Allocation reads the history and the model, to record the content at the current
    position, and updates the registry state. *)
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

  (** The same for [sfmupd], with fancy updates before and after reading the model. *)
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

(** ** Structure of [alwaysI] *)
Section always_struct.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Global Instance alwaysI_guar_persistent N P G : Persistent (alwaysI_guar N P G).
  Proof. rewrite alwaysI_guar_unfold. apply _. Qed.

  Global Instance alwaysI_as_persistent N P V : Persistent (alwaysI_as N P V).
  Proof. rewrite /alwaysI_as. apply _. Qed.

  Global Instance alwaysI_persistent N P : Persistent (alwaysI N P).
  Proof. rewrite /alwaysI. apply _. Qed.

  Global Instance treg_handle_persistent e : Persistent (treg_handle e).
  Proof. destruct e; apply _. Qed.

  (** Contractive in the content: structures can be defined by guarded recursion. *)

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

End always_struct.

(** ** Structure of [untilI] *)
Section until_struct.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ}.

  Global Instance untilI_guar_pers_persistent N k P Q G1 G2 :
    Persistent (untilI_guar_pers N k P Q G1 G2).
  Proof. rewrite /untilI_guar_pers. apply _. Qed.

  Global Instance untilI_pers_persistent N k P Q : Persistent (untilI_pers N k P Q).
  Proof. rewrite /untilI_pers. apply _. Qed.
  (** A done until is persistent if its right formula is. *)

  Global Instance untilI_done_guar_persistent k Q G2 :
    Persistent Q → Persistent (untilI_done_guar k Q G2).
  Proof. rewrite untilI_done_guar_unfold. apply _. Qed.

  Global Instance untilI_done_persistent k Q : Persistent Q → Persistent (untilI_done k Q).
  Proof. rewrite /untilI_done. apply _. Qed.

  (* The contractiveness of the obligation invariant, in the form [f_contractive] uses. *)

  Local Instance oblP_inv_contractive_l n N k :
    Proper (dist_later n ==> (=) ==> dist n) (oblP_inv (Σ:=Σ) N k).
  Proof. intros P P' HP R ? <-. by apply oblP_inv_contractive_1. Qed.
  (** Contractive in both formulas: structures can be defined by guarded recursion through
      either side. *)

  Global Instance untilI_guar_contractive_l N k q Q G1 G2 :
    Contractive (λ P, untilI_guar N k q P Q G1 G2).
  Proof. rewrite untilI_guar_unseal /untilI_guar_def /untilI_guar_pers. solve_contractive. Qed.

  Global Instance untilI_guar_contractive_r N k q P G1 G2 :
    Contractive (λ Q, untilI_guar N k q P Q G1 G2).
  Proof. rewrite untilI_guar_unseal /untilI_guar_def /untilI_guar_pers. solve_contractive. Qed.

  Lemma untilI_guar_pers_inv N k P Q G1 G2 :
    untilI_guar_pers N k P Q G1 G2 ⊢ oblP_inv N k P (until_disch k G2).
  Proof. rewrite /untilI_guar_pers. iIntros "(%&%&%&%&%&%&%&%&%& _& _& _& _& $& _)". Qed.

  Lemma untilI_pers_inv N k P Q : untilI_pers N k P Q ⊢ oblP_inv N k P (until_disch k (itrProp_sem Q)).
  Proof. apply untilI_guar_pers_inv. Qed.

  Lemma untilI_guar_pers_temporal N k P Q G1 G2 :
    untilI_guar_pers N k P Q G1 G2 ⊢ ▷ (P ⊨ₜ G1) ∗ ▷ (Q ⊨ₜ G2).
  Proof. rewrite /untilI_guar_pers. iIntros "(%&%&%&%&%&%&%&%&%& _& _& _& _& _& $& $& _)". Qed.

  Lemma untilI_guar_temporal N k q P Q G1 G2 :
    untilI_guar N k q P Q G1 G2 ⊢ ▷ (P ⊨ₜ G1) ∗ ▷ (Q ⊨ₜ G2).
  Proof. rewrite untilI_guar_unfold. iIntros "[_ U]". by iApply untilI_guar_pers_temporal. Qed.

  (** Fractions *)

  Global Instance untilI_guar_fractional N k P Q G1 G2 : Fractional (λ q, untilI_guar N k q P Q G1 G2).
  Proof.
    intros p q. rewrite !untilI_guar_unfold. iSplit.
    - iIntros "(Oa& #OI)". iFrame "OI". rewrite !Qp.div_add_distr. iDestruct "Oa" as "[Oa Oa']". iFrame.
    - iIntros "((Oa1& #Oi)& Oa2& _)". iFrame "Oi". rewrite !Qp.div_add_distr. iCombine "Oa1 Oa2" as "$".
  Qed.

  Global Instance untilI_guar_as_fractional N k q P Q G1 G2 :
    AsFractional (untilI_guar N k q P Q G1 G2) (λ q, untilI_guar N k q P Q G1 G2) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance untilI_fractional N k P Q : Fractional (λ q, untilI N k q P Q).
  Proof. intros p q. rewrite !untilI_guar_canonical. apply (untilI_guar_fractional N k P Q _ _ p q). Qed.

  Global Instance untilI_as_fractional N k q P Q : AsFractional (untilI N k q P Q) (λ q, untilI N k q P Q) q.
  Proof. split; [auto|apply _]. Qed.

End until_struct.
