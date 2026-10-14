From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import saved_prop ghost_map.
From lantana.trace Require Export guarantee_infer.

(** * Temporal formulas in ghost state

    A saved proposition names a temporal formula; stored with its guarantee, the pair
    guarantees that property by itself. Also a ghost map of temporal formulas chosen at
    run time. *)

Section saved.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!savedPropG Σ}.
  Implicit Types G : itrProp Λ Σ.

  (** [γ] names the temporal formula [P], which guarantees [G]. *)
  Definition saved_guar (γ : gname) (P : iProp Σ) G : iProp Σ :=
    γ ↪PROP□ P ∗ P ⊨ₜ G.

  Global Instance saved_guar_persistent γ P G : Persistent (saved_guar γ P G).
  Proof. apply _. Qed.

  Lemma saved_guar_alloc P G : P ⊨ₜ G ==∗ ∃ γ, saved_guar γ P G.
  Proof.
    iIntros "#HG". iMod (saved_prop_alloc P DfracDiscarded) as (γ) "#Hγ"; first done.
    iModIntro. iExists γ. by iFrame "#".
  Qed.

  Lemma saved_guar_agree γ P Q G G' :
    saved_guar γ P G -∗ saved_guar γ Q G' -∗ ▷ (P ≡ Q).
  Proof. iIntros "[HP _] [HQ _]". iApply (saved_prop_agree with "HP HQ"). Qed.

  (** A formula packed with its guarantee guarantees that property. *)
  Global Instance into_guar_packed P G : IntoGuar (P ⊨ₜ G ∗ P) G | 5.
  Proof.
    rewrite /IntoGuar. iApply (guar_mono (∃ P', P' ∗ P' ⊨ₜ G)%I with "[]").
    { iIntros "!> [#HG HP]". iExists P. by iFrame. }
    iApply guar_packed.
  Qed.

  Global Instance into_guar_saved_guar γ P G : IntoGuar (saved_guar γ P G ∗ P) G | 5.
  Proof.
    rewrite /IntoGuar. iApply (guar_mono (P ⊨ₜ G ∗ P)%I with "[]").
    { iIntros "!> [[_ #HG] HP]". by iFrame. }
    iApply (into_guar _ _).
  Qed.

End saved.

(** A ghost map of temporal formulas, one per request, chosen at run time. Its invariant
    guarantees, at all times, the trace property of every registered request. *)
Section request_map.
  Context `{!temporalGS Λ Σ} `{!state_interp_class Λ Σ} `{!savedPropG Σ, !ghost_mapG Σ nat gname}.
  Implicit Types G : nat → itrProp Λ Σ.

  Definition request_map_inv γm G : iProp Σ :=
    ∃ m : gmap nat gname, ghost_map_auth_frac γm 1 m ∗
      [∗ map] r ↦ γr ∈ m, ∃ P, saved_guar γr P (G r) ∗ P.

  (** Inferred: the requests' names are ghost (they do not show), the map is trace-visible. *)
  Lemma guar_request_map N γm G :
    ⊢ alwaysI N (request_map_inv γm G) ⊨ₜ
      itrProp_always (itrProp_exist (λ m : gmap nat gname,
        itrProp_true ∧ itrProp_forall (λ r, itrProp_forall (λ γr, itrProp_impl ⌜m !! r = Some γr⌝ (G r))))).
  Proof. apply (into_guar _ _). Qed.

  (** Allocation, with no request registered yet: a registered invariant. *)
  Lemma request_map_alloc E N G :
    ⊢ |={E}=>m ∃ γm, alwaysI N (request_map_inv γm G).
  Proof.
    iMod (ghost_map_alloc_empty (K:=nat) (V:=gname)) as (γm) "Ha".
    iMod (alwaysI_alloc E N (request_map_inv γm G) with "[Ha]") as "$"; last done.
    iNext. iExists ∅. iFrame. by rewrite big_sepM_empty.
  Qed.

End request_map.
