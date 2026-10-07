From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import saved_prop ghost_map.
From lantana.trace Require Export guarantee_infer.

(** * Temporal formulas in ghost state

    A saved proposition names a temporal formula; stored with its guarantee, the pair is
    self-certifying. Also a registry of temporal formulas chosen at runtime. *)

Section saved.
  Context `{!lantanaGS Λ Σ, !savedPropG Σ}.
  Implicit Types G : tprop Λ Σ.

  (** [γ] names the temporal formula [P], which guarantees [G]. *)
  Definition saved_temporal (γ : gname) (P : iProp Σ) G : iProp Σ :=
    γ ↪PROP□ P ∗ P ⊨ₜ G.

  Global Instance saved_temporal_persistent γ P G : Persistent (saved_temporal γ P G).
  Proof. apply _. Qed.

  Lemma saved_temporal_alloc P G : P ⊨ₜ G ==∗ ∃ γ, saved_temporal γ P G.
  Proof.
    iIntros "#HG". iMod (saved_prop_alloc P DfracDiscarded) as (γ) "#Hγ"; first done.
    iModIntro. iExists γ. by iFrame "#".
  Qed.

  Lemma saved_temporal_agree γ P Q G G' :
    saved_temporal γ P G -∗ saved_temporal γ Q G' -∗ ▷ (P ≡ Q).
  Proof. iIntros "[HP _] [HQ _]". iApply (saved_prop_agree with "HP HQ"). Qed.

  (** Certified formulas guarantee their certificate's trace property. *)
  Global Instance into_temporal_certified P G : IntoTemporal (P ⊨ₜ G ∗ P) G | 5.
  Proof.
    rewrite /IntoTemporal. iApply (temporal_mono (∃ P', P' ∗ P' ⊨ₜ G)%I with "[]").
    { iIntros "!> [#HG HP]". iExists P. by iFrame. }
    iApply temporal_certified.
  Qed.

  Global Instance into_temporal_saved_temporal γ P G : IntoTemporal (saved_temporal γ P G ∗ P) G | 5.
  Proof.
    rewrite /IntoTemporal. iApply (temporal_mono (P ⊨ₜ G ∗ P)%I with "[]").
    { iIntros "!> [[_ #HG] HP]". by iFrame. }
    iApply (into_temporal _ _).
  Qed.

End saved.

(** A registry of temporal formulas, one per request, chosen at runtime. Its invariant
    guarantees, at all times, the trace property of every registered request. *)
Section request_registry.
  Context `{!lantanaGS Λ Σ, !savedPropG Σ, !ghost_mapG Σ nat gname}.
  Implicit Types G : nat → tprop Λ Σ.

  Definition registry_inv γm G : iProp Σ :=
    ∃ m : gmap nat gname, ghost_map_auth_frac γm 1 m ∗
      [∗ map] r ↦ γr ∈ m, ∃ P, saved_temporal γr P (G r) ∗ P.

  (** Inferred: the requests' names are ghost (they do not show), the map is trace-visible. *)
  Lemma registry_temporal N γm G :
    ⊢ alwaysI N (registry_inv γm G) ⊨ₜ
      tprop_always (tprop_exist (λ m : gmap nat gname,
        tprop_true ∧ tprop_forall (λ r, tprop_forall (λ γr, tprop_impl ⌜m !! r = Some γr⌝ (G r))))).
  Proof. apply (into_temporal _ _). Qed.

  (** Allocation, with no request registered yet: a registered invariant. *)
  Lemma registry_alloc E N G :
    ⊢ |={E}=>m ∃ γm, alwaysI N (registry_inv γm G).
  Proof.
    iMod (ghost_map_alloc_empty (K:=nat) (V:=gname)) as (γm) "Ha".
    iMod (alwaysI_alloc E N (registry_inv γm G) with "[Ha]") as "$"; last done.
    iNext. iExists ∅. iFrame. by rewrite big_sepM_empty.
  Qed.

End request_registry.
