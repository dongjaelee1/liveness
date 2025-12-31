From iris.algebra Require Import gmap_view gset coPset reservation_map dfrac_agree.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Export wfocm.
From liris.algebra Require Import auth_mra bank.
From liris.base_logic Require Export invariants.
From liris.base_logic Require Export ghost_lock.

Section aux.
  (* Maybe move to somewhere *)
  Context `{SI : indexT} {Σ : gFunctors} {A : cmra} {GA : inG Σ A} {GR : inG Σ (reservation_mapR A)}.

  Lemma reservation_map_token_alloc_singleton (name : gname) D k a :
    k ∉ D →
    ✓ a →
    (own name (reservation_map_token (A:=A) (⊤ ∖ gset_to_coPset D)))
    ⊢ (own name (reservation_map_token (A:=A) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
        |==> (own name (reservation_map_data k a)).
  Proof.
    iIntros (Hk Ha) "Htk". rewrite (reservation_map_token_difference (gset_to_coPset {[k]}) (⊤ ∖ gset_to_coPset D)); cycle 1.
    { apply elem_of_subseteq. intros. rewrite elem_of_difference. split; first set_solver.
      intro F. rewrite !elem_of_gset_to_coPset in H F. set_solver.
    }
    iDestruct "Htk" as "[Htk H]".
    assert (⊤ ∖ gset_to_coPset D ∖ gset_to_coPset {[k]} = ⊤ ∖ gset_to_coPset ({[k]} ∪ D)).
    { apply leibniz_equiv. intros x. rewrite !elem_of_difference. split; intros.
      - destruct H as ((_&?)&?). split; first set_solver. intros F. apply elem_of_gset_to_coPset, elem_of_union in F.
        destruct F; [apply H0 | apply H]; apply elem_of_gset_to_coPset; set_solver.
      - destruct H as (_&?). split; first (split; first set_solver);
          intros F; apply elem_of_gset_to_coPset in F; apply H, elem_of_gset_to_coPset; set_solver.
    }
    rewrite H. iFrame "H".
    iMod (own_update with "Htk") as "H".
    { eapply (reservation_map_alloc _ k a); auto. apply elem_of_gset_to_coPset; set_solver. }
    by iFrame.
  Qed.

End aux.

(** The ghost state for ghost locks *)
Module glsatGS.

  Class glsatGpreS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set :=
    GlsatGpreS {
        glsatGpreS_witfun : inG Σ (gmap_viewR gl_id (agreeR (leibnizO gl_witness)));
        glsatGpreS_state : inG Σ (reservation_mapUR (reservation_mapUR (dfrac_agreeR natO)));
        (* glsatGpreS_state : inG Σ (reservation_mapUR (dfrac_agreeR natO)); *)
        glsatGpreS_version : inG Σ (reservation_mapUR (auth_mraUR le));
        glsatGpreS_fuel : inG Σ (reservation_mapUR bankUR);
        (* Keep track of the current owner of each lock, if the owner exists *)
        glsatGpreS_owner : inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO gl_owner)));
      }.

  Class glsatGS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set :=
    GlsatG {
        glsat_inG : glsatGpreS Σ;
        witfun_name : gname;
        state_name : gname;
        version_name : gname;
        fuel_name : gname;
        owner_name : gname;
      }.

  Definition glsatΣ `{SI : indexT} `{GL : ghost_lock_class} : gFunctors :=
    #[GFunctor (gmap_viewR gl_id (agreeR (leibnizO gl_witness)));
      GFunctor (reservation_mapUR (reservation_mapUR (dfrac_agreeR $ natO)));
      (* GFunctor (reservation_mapUR (dfrac_agreeR $ natO)); *)
      GFunctor (reservation_mapUR (auth_mraUR le));
      GFunctor (reservation_mapUR bankUR);
      GFunctor (reservation_mapUR (dfrac_agreeR $ (leibnizO gl_owner)))
      ].

  Global Instance subG_glsatΣ `{SI : indexT} `{GL : ghost_lock_class} {Σ} : subG (glsatΣ) Σ → (glsatGpreS Σ).
  Proof. solve_inG. Qed.

End glsatGS.
Import glsatGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances glsat_inG
  glsatGpreS_witfun glsatGpreS_state glsatGpreS_version glsatGpreS_fuel glsatGpreS_owner.

(* Witfun: Witness for each version *)
Definition glG_witfun `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (ξ : gl_witness) : iProp Σ :=
  own witfun_name (gmap_view_frag k DfracDiscarded (to_agree (ξ : leibnizO gl_witness))).
Global Typeclasses Opaque glG_witfun.
Global Instance: Params (@glG_witfun) 5 := {}.

Definition glG_elem `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) : iProp Σ :=
  ∃ ξ, glG_witfun k ξ.
Global Typeclasses Opaque glG_elem.
Global Instance: Params (@glG_elem) 5 := {}.

Local Definition glG_witfun_auth_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (m : gmap gl_id gl_witness) : iProp Σ :=
  own witfun_name (gmap_view_auth (V:=agreeR (leibnizO gl_witness)) (DfracOwn 1) (to_agree <$> m)).

(* State: locked or unlocked for each version *)
Definition glG_locked `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data k (reservation_map_data (encode v) (to_frac_agree q 0))).
Global Typeclasses Opaque glG_locked.
Global Instance: Params (@glG_locked) 5 := {}.

Definition glG_unlocked `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own state_name (reservation_map_data k (reservation_map_data (encode v) (to_dfrac_agree DfracDiscarded 1))).
Global Typeclasses Opaque glG_unlocked.
Global Instance: Params (@glG_unlocked) 5 := {}.

Local Definition glG_state_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own state_name (reservation_map_token (A:=reservation_mapUR (dfrac_agreeR natO)) E).
Local Definition glG_state_token_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (E : coPset) : iProp Σ :=
  own state_name (reservation_map_data k (reservation_map_token (A:=dfrac_agreeR natO) E)).

(* Version: tracks the version *)
Definition glG_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (q : Qp) : iProp Σ :=
  own version_name (reservation_map_data k (●AM{#q}[le] v)).
Global Typeclasses Opaque glG_version.
Global Instance: Params (@glG_version) 5 := {}.

Definition glG_version_lb `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own version_name (reservation_map_data k (◯AM[le] v)).
Global Typeclasses Opaque glG_version_lb.
Global Instance: Params (@glG_version_lb) 5 := {}.

Definition glG_version_pin `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own version_name (reservation_map_data k (●AM□[le] v)).
Global Typeclasses Opaque glG_version_pin.
Global Instance: Params (@glG_version_pin) 5 := {}.

Definition glG_version_done `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  ∃ v', ⌜ v < v' ⌝ ∗ glG_version_lb k v'.
Global Typeclasses Opaque glG_version_done.
Global Instance: Params (@glG_version_done) 5 := {}.

Local Definition glG_version_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own version_name (reservation_map_token (A:=auth_mraUR le) E).

(* Fuel: manage credits for a lock's fuel *)
Definition glG_fuel `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (a : gl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bankUR) k (cash a)).
Global Typeclasses Opaque glG_fuel.
Global Instance: Params (@glG_fuel) 5 := {}.

Definition glG_fuel_supply `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (a : gl_fuel) (q : Qp) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bankUR) k (debt a q)).
Global Typeclasses Opaque glG_fuel_supply.
Global Instance: Params (@glG_fuel_supply) 5 := {}.

Local Definition glG_fuel_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_token (A:=bankUR) E).

(* Owner: tracks the owner thread of a lock *)
Definition glG_owner `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (t : gl_owner) (q : Qp) : iProp Σ :=
  own owner_name (reservation_map_data k (to_frac_agree q (t : leibnizO gl_owner))).
Global Typeclasses Opaque glG_owner.
Global Instance: Params (@glG_owner) 5 := {}.

Local Definition glG_owner_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO gl_owner)) E).

(* Variant: P until Q and then always R. For each version, three cases:
   1. locked at version v with P
   2. unlocked at version v with Q
   3. version v done with R
   WP ensures that when unlocking, glG_unlocked with version v is visited at least once
 *)
Definition glG_variant_internal `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (q : Qp) (P Q R : iProp Σ) : iProp Σ :=
  (((glG_locked k v q ∗ P) ∨ (glG_unlocked k v ∗ Q)) ∨ (glG_version_done k v ∗ R)).

(* Definition glG_variant_internal `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (v : gl_version) (q : Qp) (P Q R : iProp Σ) : iProp Σ := *)
(*   (((glG_locked k v q ∗ glG_version k v q ∗ P) ∨ *)
(*       (glG_unlocked k v ∗ glG_version k v q ∗ Q)) ∨ *)
(*      (glG_unlocked k v ∗ glG_version_done k v ∗ R)). *)

Definition glG_variant `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ}
  (N : namespace) (k : gl_id) (v : gl_version) (q : Qp) (P Q R : iProp Σ) : iProp Σ :=
  inv N (glG_variant_internal k v q P Q R).

(* Definition glG_always `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ} *)
(*   (N : namespace) (k : gl_id) (v : gl_version) (P : iProp Σ) : iProp Σ := *)
(*   glG_unlocked k v ∗ glG_version_pin k v ∗ inv N P. *)

(* Global protocol for ghost locks. *)
Definition glsat `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (Ω : ghost_locks) : iProp Σ :=
  locked
    ((∃ (Wfs : gmap gl_id gl_witness), (⌜ dom Ω = dom Wfs ⌝) ∗ glG_witfun_auth_id Wfs) ∗
     glG_state_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     glG_version_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     glG_fuel_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     glG_owner_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     ([∗ map] k ↦ '(v, g) ∈ Ω,
        glG_version k v (1/2/2)%Qp ∗
        glG_state_token_version k (⊤ ∖ gset_to_coPset (set_map encode (set_seq 0 (S v) : gset gl_version))) ∗
        ([∗ set] u ∈ (set_seq 0 v), glG_version_lb k u ∗ glG_unlocked k u) ∗
        glG_version_lb k v ∗
        ∃ ξ, glG_witfun k ξ ∗
        ∃ α, glG_fuel_supply k α (1)%Qp ∗
        (⌜ α w≤ Σ[ξ] v ⌝) ∗
        (** Ghost lock is locked or unlocked or unlocked and pinned *)
        match g with
        | gl_locked a t =>
            glG_locked k v (1/2/2)%Qp ∗
            (⌜ α w≤ a ⌝) ∗
            glG_owner k t (1/2/2)%Qp
        | gl_unlocked =>
            glG_unlocked k v ∗
            (∃ t, glG_owner k t (1)%Qp)
        end))%I.

(* Definition glsat `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (Ω : ghost_locks) : iProp Σ := *)
(*   locked *)
(*     (glG_witfun_auth_id (gset_to_gmap () (dom Ω)) ∗ *)
(*      glG_state_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗ *)
(*      glG_version_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗ *)
(*      glG_fuel_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗ *)
(*      glG_owner_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗ *)
(*      ([∗ map] k ↦ '(v, g) ∈ Ω, *)
(*         glG_witfun k ∗ *)
(*         glG_version k v (1/2/2)%Qp ∗ *)
(*         (∃ (vs : gset gl_version), *)
(*             glG_state_token_version k (⊤ ∖ gset_to_coPset (set_map encode vs)) ∗ *)
(*             ([∗ set] u ∈ vs, glG_version_lb k u ∗ ((glG_unlocked k u ∗ ⌜ u < v ⌝) ∨ ⌜ u = v ⌝)) *)
(*         ) ∗ *)
(*         (** Ghost lock is active: locked or unlocked, or retired: unlocked and pinned *) *)
(*         match g with *)
(*         | gl_locked a t => *)
(*             glG_locked k v (1/2/2)%Qp ∗ *)
(*             (∃ α, (⌜ α w≤ a ⌝) ∗ glG_fuel_supply k α (1/2)%Qp) ∗ *)
(*             glG_owner k t (1/2/2)%Qp *)
(*         | gl_unlocked => *)
(*             glG_unlocked k v ∗ *)
(*             ((∃ α, glG_fuel_supply k α (1/2)%Qp) *)
(*              ∨ *)
(*                (glG_version_pin k v ∗ (∃ α, glG_fuel_supply k α (1)%Qp))) ∗ *)
(*             (∃ t, glG_owner k t (1)%Qp) *)
(*         end))%I. *)

(** Properties *)
Section glsat.
  Context `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ}.

  (** Instances *)
  (* Witfun *)
  Global Instance glG_witfun_persistent k ξ : Persistent (glG_witfun k ξ).
  Proof. rewrite /glG_witfun. apply _. Qed.
  Global Instance glG_witfun_timeless k ξ : Timeless (glG_witfun k ξ).
  Proof. rewrite /glG_witfun. apply _. Qed.

  Global Instance glG_elem_persistent k : Persistent (glG_elem k).
  Proof. rewrite /glG_elem. apply _. Qed.
  Global Instance glG_elem_timeless k : Timeless (glG_elem k).
  Proof. rewrite /glG_elem. apply _. Qed.

  Local Instance glG_witfun_auth_id_timeless m : Timeless (glG_witfun_auth_id m).
  Proof. rewrite /glG_witfun_auth_id. apply _. Qed.

  (* State *)
  Global Instance glG_unlocked_persistent k v : Persistent (glG_unlocked k v).
  Proof. rewrite /glG_unlocked. apply _. Qed.

  Global Instance glG_locked_timeless k v q : Timeless (glG_locked k v q).
  Proof. rewrite /glG_locked. apply _. Qed.
  Global Instance glG_unlocked_timeless k v : Timeless (glG_unlocked k v).
  Proof. rewrite /glG_unlocked. apply _. Qed.

  Global Instance glG_locked_fractional k v :
    Fractional (glG_locked k v).
  Proof.
    rewrite /glG_locked. intros p q.
    by rewrite -own_op -!reservation_map_data_op -dfrac_agree_op.
  Qed.
  Global Instance glG_locked_as_fractional k v q :
    AsFractional (glG_locked k v q) (glG_locked k v) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance glG_state_token_id_timeless E : Timeless (glG_state_token_id E).
  Proof. rewrite /glG_state_token_id. apply _. Qed.
  Local Instance glG_state_token_version_timeless k E : Timeless (glG_state_token_version k E).
  Proof. rewrite /glG_state_token_version. apply _. Qed.

  (* Version *)
  Global Instance glG_version_lb_persistent k v : Persistent (glG_version_lb k v).
  Proof. rewrite /glG_version_lb. apply _. Qed.
  Global Instance glG_version_pin_persistent k v : Persistent (glG_version_pin k v).
  Proof. rewrite /glG_version_pin. apply _. Qed.
  Global Instance glG_version_done_persistent k v : Persistent (glG_version_done k v).
  Proof. rewrite /glG_version_done. apply _. Qed.

  Global Instance glG_version_timeless k v q : Timeless (glG_version k v q).
  Proof. rewrite /glG_version. apply _. Qed.
  Global Instance glG_version_lb_timeless k v : Timeless (glG_version_lb k v).
  Proof. rewrite /glG_version_lb. apply _. Qed.
  Global Instance glG_version_pin_timeless k v : Timeless (glG_version_pin k v).
  Proof. rewrite /glG_version_pin. apply _. Qed.
  Global Instance glG_version_done_timeless k v : Timeless (glG_version_done k v).
  Proof. rewrite /glG_version_done. apply _. Qed.

  Global Instance glG_version_fractional k v :
    Fractional (glG_version k v).
  Proof.
    rewrite /glG_version. intros p q. by rewrite -own_op -reservation_map_data_op -auth_mra_auth_dfrac_op.
  Qed.
  Global Instance glG_version_as_fractional k v q :
    AsFractional (glG_version k v q) (glG_version k v) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance glG_version_token_id_timeless E : Timeless (glG_version_token_id E).
  Proof. rewrite /glG_version_token_id. apply _. Qed.

  (* Fuel *)
  Global Instance glG_fuel_timeless k a : Timeless (glG_fuel k a).
  Proof. rewrite /glG_fuel. apply _. Qed.
  Global Instance glG_fuel_supply_timeless k a q : Timeless (glG_fuel_supply k a q).
  Proof. rewrite /glG_fuel_supply. apply _. Qed.

  Global Instance glG_fuel_supply_fractional k a :
    Fractional (glG_fuel_supply k a).
  Proof.
    rewrite /glG_fuel_supply. intros p q. by rewrite -own_op -!reservation_map_data_op debt_split.
  Qed.
  Global Instance glG_fuel_supply_as_fractional k a q :
    AsFractional (glG_fuel_supply k a q) (glG_fuel_supply k a) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance glG_fuel_token_id_timeless E : Timeless (glG_fuel_token_id E).
  Proof. rewrite /glG_fuel_token_id. apply _. Qed.

  (* Owner *)
  Global Instance glG_owner_timeless k t q : Timeless (glG_owner k t q).
  Proof. rewrite /glG_owner. apply _. Qed.

  Global Instance glG_owner_fractional k t :
    Fractional (glG_owner k t).
  Proof.
    rewrite /glG_owner. intros p q. by rewrite -own_op -!reservation_map_data_op -frac_agree_op.
  Qed.
  Global Instance glG_owner_as_fractional k t q :
    AsFractional (glG_owner k t q) (glG_owner k t) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance glG_owner_token_id_timeless E : Timeless (glG_owner_token_id E).
  Proof. rewrite /glG_owner_token_id. apply _. Qed.

  (* Variant *)
  Global Instance glG_variant_contractive_1 N k v q Q R : Contractive (λ P, @glG_variant SI _ Σ _ _ N k v q P Q R).
  Proof. rewrite /glG_variant /glG_variant_internal. solve_contractive. Qed.
  Global Instance glG_variant_contractive_2 N k v q P R : Contractive (λ Q, @glG_variant SI _ Σ _ _ N k v q P Q R).
  Proof. rewrite /glG_variant /glG_variant_internal. solve_contractive. Qed.
  Global Instance glG_variant_contractive_3 N k v q P Q : Contractive (λ R, @glG_variant SI _ Σ _ _ N k v q P Q R).
  Proof. rewrite /glG_variant /glG_variant_internal. solve_contractive. Qed.

  Global Instance glG_variant_persistent N k v q P Q R : Persistent (glG_variant N k v q P Q R).
  Proof. apply _. Qed.

  (* Global Instance glG_always_contractive N k v : Contractive (λ P, glG_always N k v P). *)
  (* Proof. rewrite /glG_always. solve_contractive. Qed. *)

  (* Global Instance glG_always_persistent N k v P : Persistent (glG_always N k v P). *)
  (* Proof. apply _. Qed. *)

  (* Sat *)
  Global Instance glsat_timeless Ω : Timeless (glsat Ω).
  Proof. rewrite /glsat -lock. apply _. Qed.

  (** Witfun rules *)
  Lemma glG_witfun_lookup (Wfs : gmap gl_id gl_witness) k ξ :
    glG_witfun_auth_id Wfs ∗ glG_witfun k ξ
    ⊢ ⌜ Wfs !! k = Some ξ ⌝.
  Proof.
    rewrite /glG_witfun_auth_id /glG_witfun -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
    case: (Wfs !! k)=> [Q|] /=; last first.
    { by iDestruct "HQ'" as %?. }
    iDestruct "HQ'" as %[= <-].
    rewrite !to_agree_includedI; simpl.
    iPoseProof (internal_eq_sym with "Hincl") as "H". iPoseProof (discrete_eq with "H") as "%HG".
    rewrite HG. done.
  Qed.

  Lemma glG_witfun_agree k ξ1 ξ2 :
    glG_witfun k ξ1 ∗ glG_witfun k ξ2 ⊢ ⌜ ξ1 = ξ2 ⌝.
  Proof.
    rewrite /glG_witfun -own_op own_valid gmap_view_frag_op_validI.
    iIntros "(_&H)". rewrite to_agree_op_validI. iPoseProof (discrete_eq with "H") as "%". done.
  Qed.

  Lemma glG_witfun_elem k ξ :
    glG_witfun k ξ ⊢ glG_elem k.
  Proof. rewrite /glG_elem. eauto. Qed.

  Lemma glG_witfun_alloc (Wfs : gmap gl_id gl_witness) k ξ :
    Wfs !! k = None →
    glG_witfun_auth_id Wfs
    ⊢ |==> glG_witfun_auth_id (<[k:=ξ]>Wfs) ∗
        glG_witfun k ξ.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "[H Hw]".
    { eapply (gmap_view_alloc _ k (DfracDiscarded) (to_agree $ (ξ : leibnizO _))); try done.
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; first done. by apply not_elem_of_dom.
    }
    rewrite /glG_witfun_auth_id /glG_witfun. rewrite fmap_insert. by iFrame.
  Qed.

  (** State rules *)
  Lemma glG_locked_to_unlocked_2 k v q1 q2 :
    (q1 + q2 = 1)%Qp →
    glG_locked k v q1 ∗ glG_locked k v q2 ⊢ |==> glG_unlocked k v.
  Proof.
    rewrite /glG_locked /glG_unlocked -!own_op -!reservation_map_data_op.
    intros Heq. apply own_update, reservation_map_update, reservation_map_update.
    etransitivity; first eapply frac_agree_update_2; auto.
    rewrite -dfrac_agree_op dfrac_op_own Heq. eapply dfrac_agree_persist.
  Qed.

  Lemma glG_locked_frac_valid k v q :
    glG_locked k v q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_locked. iIntros "H".
    iPoseProof (own_valid with "H") as "%Hv". do 2 (apply reservation_map_data_valid in Hv).
    iApply frac_agree_validI. done.
  Qed.

  Lemma glG_locked_unlocked_false k v q :
    glG_locked k v q ∗ glG_unlocked k v ⊢ False.
  Proof.
    rewrite /glG_locked /glG_unlocked. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. do 2 apply reservation_map_data_valid in V.
    apply dfrac_agree_op_valid in V. destruct V. done.
  Qed.

  Lemma glG_state_id_alloc D k E :
    k ∉ D →
    glG_state_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_state_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        glG_state_token_version k E.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (reservation_map_token (A:=dfrac_agreeR natO) E) with "Htk") as "[Htk >H]"; auto.
    { apply reservation_map_token_valid. }
    rewrite /glG_state_token_version. by iFrame.
  Qed.

  Lemma glG_state_alloc_gen k (D : gset gl_version) v s :
    v ∉ D →
    glG_state_token_version k (⊤ ∖ gset_to_coPset (set_map encode D))
    ⊢ |==> glG_state_token_version k (⊤ ∖ gset_to_coPset (set_map encode ({[v]} ∪ D))) ∗
        own state_name (reservation_map_data k (reservation_map_data (encode v) (to_frac_agree 1 s))).
  Proof.
    iIntros (Hk) "Htk". rewrite /glG_state_token_version.
    rewrite (reservation_map_token_difference
               (gset_to_coPset (set_map encode ({[v]} : gset nat)))
               (⊤ ∖ gset_to_coPset (set_map encode D))); cycle 1.
    { apply elem_of_subseteq. intros. rewrite elem_of_difference. split; first set_solver.
      intro F. rewrite !elem_of_gset_to_coPset in H F. apply elem_of_map_1 in H, F.
      destruct H as (?& ?& ?), F as (?& ?& ?). subst. apply encode_inj in H1. subst.
      set_solver.
    }
    iDestruct "Htk" as "[Htk H]".
    assert (⊤ ∖ gset_to_coPset (set_map encode D) ∖ gset_to_coPset (set_map encode ({[v]} : gset nat)) = ⊤ ∖ gset_to_coPset (set_map encode ({[v]} ∪ D))).
    { apply leibniz_equiv. intros x. rewrite !elem_of_difference. split; intros.
      - destruct H as ((_&?)&?). split; first set_solver.
        intros F. rewrite set_map_union_L in F. apply elem_of_gset_to_coPset, elem_of_union in F.
        destruct F; [apply H0 | apply H]; apply elem_of_gset_to_coPset; set_solver.
      - destruct H as (_&?). split; first (split; first set_solver);
          intros F; apply elem_of_gset_to_coPset in F; apply H, elem_of_gset_to_coPset; set_solver.
    }
    rewrite H. iFrame "H".
    iMod (own_update with "Htk") as "H".
    { eapply reservation_map_update. eapply (reservation_map_alloc _ (encode v) (to_frac_agree 1 s)); auto.
      - apply elem_of_gset_to_coPset; set_solver.
      - done.
    }
    by iFrame.
  Qed.

  Lemma glG_state_alloc_gen_seq k s l n (f : gl_version → nat) :
    glG_state_token_version k (⊤ ∖ gset_to_coPset (set_map encode (set_seq s l : gset gl_version)))
    ⊢ |==> glG_state_token_version k (⊤ ∖ gset_to_coPset (set_map encode (set_seq s (l + n) : gset gl_version))) ∗
        [∗ set] u ∈ set_seq (s + l) n, own state_name (reservation_map_data k (reservation_map_data (encode u) (to_frac_agree 1 (f u)))).
  Proof.
    revert s l. induction n; iIntros (??) "H".
    { simpl. rewrite Nat.add_right_id big_sepS_empty. by iFrame. }
    replace (l + S n) with (S (l + n)) by lia. rewrite !set_seq_S_end_union_L.
    rewrite big_sepS_union; cycle 1.
    { apply set_seq_S_end_disjoint. }
    iMod (IHn with "H") as "[H $]". iMod (glG_state_alloc_gen _ _ (s + l + n) (f (s + l + n)) with "H") as "(H& R)".
    { intros F. apply elem_of_set_seq in F. lia. }
    rewrite (assoc Nat.add) big_sepS_singleton. by iFrame.
  Qed.

  Lemma glG_locked_is_allocated (vs : gset gl_version) k v q :
    glG_state_token_version k (⊤ ∖ gset_to_coPset (set_map encode vs)) ∗ glG_locked k v q
    ⊢ ⌜ v ∈ vs ⌝.
  Proof.
    iIntros "[H Gl]". rewrite /glG_state_token_version /glG_locked.
    destruct (decide (v ∈ vs)); first done. iExFalso.
    iMod (glG_state_alloc_gen _ _ v 1 with "H") as "[H G]"; first auto.
    iPoseProof (own_op with "[$Gl $G]") as "G".
    rewrite -!reservation_map_data_op. iPoseProof (own_valid with "G") as "%V".
    do 2 apply reservation_map_data_valid in V. apply frac_agree_op_valid in V.
    destruct V. done.
  Qed.
  Lemma glG_unlocked_is_allocated (vs : gset gl_version) k v :
    glG_state_token_version k (⊤ ∖ gset_to_coPset (set_map encode vs)) ∗ glG_unlocked k v
    ⊢ ⌜ v ∈ vs ⌝.
  Proof.
    iIntros "[H Gl]". rewrite /glG_state_token_version /glG_unlocked.
    destruct (decide (v ∈ vs)); first done. iExFalso.
    iMod (glG_state_alloc_gen _ _ v 2 with "H") as "[H G]"; first auto.
    iPoseProof (own_op with "[$Gl $G]") as "G".
    rewrite -!reservation_map_data_op. iPoseProof (own_valid with "G") as "%V".
    do 2 apply reservation_map_data_valid in V. apply dfrac_agree_op_valid in V.
    destruct V. done.
  Qed.

  (** Version rules *)
  Lemma glG_version_update_mon k v1 v2 :
    (v1 ≤ v2) →
    glG_version k v1 1 ⊢ |==> glG_version k v2 1.
  Proof.
    rewrite /glG_version. intros Hle.
    apply own_update, reservation_map_update, auth_mra_update; eauto.
    apply _.
  Qed.
  Lemma glG_version_update_mon_2 k v1 v2 q1 q2 :
    (q1 + q2 = 1)%Qp →
    (v1 ≤ v2) →
    glG_version k v1 q1 ∗ glG_version k v1 q2 ⊢ |==> glG_version k v2 q1 ∗ glG_version k v2 q2.
  Proof.
    intros Hq Hle. rewrite /glG_version -!own_op -!reservation_map_data_op.
    apply own_update, reservation_map_update.
    rewrite -!auth_mra_auth_dfrac_op !dfrac_op_own !Hq.
    apply auth_mra_update; eauto. apply _.
  Qed.
  Lemma glG_version_update_pin k v q :
    glG_version k v q ⊢ |==> glG_version_pin k v.
  Proof.
    rewrite /glG_version /glG_version_pin.
    apply own_update, reservation_map_update, auth_mra_auth_persist; eauto.
  Qed.

  Lemma glG_version_lb_mon k v1 v2 :
    (v2 ≤ v1) →
    glG_version_lb k v1 ⊢ glG_version_lb k v2.
  Proof.
    rewrite /glG_version_lb. iIntros (Hle) "H". rewrite (auth_mra_know_op _ v2 v1); auto.
    iDestruct "H" as "[H1 H2]". done.
  Qed.
  Lemma glG_version_get_done k v1 v2 :
    (v2 < v1) →
    glG_version_lb k v1 ⊢ glG_version_done k v2.
  Proof.
    rewrite /glG_version_done. iIntros (Hle) "H". iExists v1. by iFrame.
  Qed.

  Lemma glG_version_get_lb_eq k v q :
    glG_version k v q ⊢ glG_version_lb k v.
  Proof.
    rewrite /glG_version /glG_version_lb.
    rewrite auth_mra_auth_know_op.
    rewrite reservation_map_data_op own_op. iIntros "[_ $]".
  Qed.
  Lemma glG_version_get_lb k v1 v2 q :
    (v2 ≤ v1) →
    glG_version k v1 q ⊢ glG_version_lb k v2.
  Proof.
    iIntros (Hle) "GLV". iPoseProof (glG_version_get_lb_eq with "GLV") as "#GLVL".
    iApply (glG_version_lb_mon with "GLVL"). done.
  Qed.
  Lemma glG_version_pin_get_lb k v1 v2 :
    (v2 ≤ v1) →
    glG_version_pin k v1 ⊢ glG_version_lb k v2.
  Proof.
    rewrite /glG_version_pin /glG_version_lb.
    rewrite auth_mra_auth_know_op.
    rewrite reservation_map_data_op own_op.
    iIntros (Hv) "[_ H2]". rewrite (auth_mra_know_op _ v2 v1); auto.
    iDestruct "H2" as "[H1 H2]". done.
  Qed.

  Lemma glG_version_frac_valid k v q :
    glG_version k v q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_version. iIntros "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    apply auth_mra_auth_dfrac_valid in Hv. done.
  Qed.

  Lemma glG_version_agree k v1 v2 q1 q2 :
    glG_version k v1 q1 ∗ glG_version k v2 q2 ⊢ ⌜ v1 = v2 ∧ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_version. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    eapply auth_mra_auth_dfrac_op_valid in Hv; auto; try apply _.
    destruct Hv. apply leibniz_equiv in H0. done.
  Qed.
  Lemma glG_version_pin_agree k v1 v2 :
    glG_version_pin k v1 ∗ glG_version_pin k v2 ⊢ ⌜ v1 = v2 ⌝.
  Proof.
    rewrite /glG_version_pin. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    eapply auth_mra_auth_dfrac_op_valid in Hv; auto; try apply _.
    destruct Hv. apply leibniz_equiv in H0. done.
  Qed.

  Lemma glG_version_pin_false k v1 v2 :
    glG_version k v1 1 ∗ glG_version_pin k v2 ⊢ False.
  Proof.
    rewrite /glG_version /glG_version_pin. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    eapply auth_mra_auth_dfrac_op_valid in Hv; auto; try apply _.
    destruct Hv. done.
  Qed.

  Lemma glG_version_lb_lb k q v1 v2 :
    glG_version k v1 q ∗ glG_version_lb k v2 ⊢ ⌜ (v2 ≤ v1) ⌝.
  Proof.
    rewrite /glG_version /glG_version_lb. rewrite -own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    apply auth_mra_both_dfrac_valid in Hv.
    - destruct Hv. done.
    - apply _.
  Qed.
  Lemma glG_version_pin_pin k q v1 v2 :
    glG_version k v1 q ∗ glG_version_pin k v2 ⊢ ⌜ v1 = v2 ⌝.
  Proof.
    rewrite /glG_version /glG_version_pin. rewrite -own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    eapply auth_mra_auth_dfrac_op_valid in Hv; auto; try apply _.
    - destruct Hv. apply leibniz_equiv in H0. done.
  Qed.
  Lemma glG_version_pin_lb k v1 v2 :
    glG_version_pin k v1 ∗ glG_version_lb k v2 ⊢ ⌜ (v2 ≤ v1) ⌝.
  Proof.
    rewrite /glG_version_pin /glG_version_lb. rewrite -own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    apply auth_mra_both_dfrac_valid in Hv.
    - destruct Hv. done.
    - apply _.
  Qed.

  Lemma glG_version_done_valid k v1 v2 q :
    glG_version k v1 q ∗ glG_version_done k v2 ⊢ ⌜ v2 < v1 ⌝.
  Proof.
    rewrite /glG_version_done. iIntros "(Gv& (%&%&#Gvl))".
    iPoseProof (glG_version_lb_lb with "[$Gv $Gvl]") as "%". iPureIntro. lia.
  Qed.
  Lemma glG_version_pin_done_valid k v1 v2 :
    glG_version_pin k v1 ∗ glG_version_done k v2 ⊢ ⌜ v2 < v1 ⌝.
  Proof.
    rewrite /glG_version_done. iIntros "(Gv& (%&%&#Gvl))".
    iPoseProof (glG_version_pin_lb with "[$Gv $Gvl]") as "%". iPureIntro. lia.
  Qed.

  Lemma glG_version_alloc D k v :
    k ∉ D →
    glG_version_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_version_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        glG_version k v 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●AM[le] v) with "Htk") as "[Htk >H]"; auto.
    { apply auth_mra_auth_valid. }
    rewrite /glG_version. by iFrame.
  Qed.

  (** Fuel rules *)
  Lemma glG_fuel_eq k a0 a1 :
    a0 w= a1 →
    glG_fuel k a0 = glG_fuel k a1.
  Proof. intros EQ. rewrite /glG_fuel. by erewrite cash_eq. Qed.
  Lemma glG_fuel_eq_list L a0 a1 :
    a0 w= a1 →
    ([∗ list] k ∈ L, glG_fuel k a0)%I ≡ ([∗ list] k ∈ L, glG_fuel k a1)%I.
  Proof. intros. apply big_opL_proper. intros. erewrite glG_fuel_eq; eauto. Qed.
  Lemma glG_fuel_eq_set L a0 a1 :
    a0 w= a1 →
    ([∗ set] k ∈ L, glG_fuel k a0)%I ≡ ([∗ set] k ∈ L, glG_fuel k a1)%I.
  Proof. intros. apply big_opS_proper. intros. erewrite glG_fuel_eq; eauto. Qed.

  Lemma glG_fuel_mon k a0 a1 :
    a0 w≤ a1 →
    glG_fuel k a1 ⊢ |==> glG_fuel k a0.
  Proof.
    intros LE. rewrite /glG_fuel. apply own_update.
    by apply reservation_map_update, cash_update.
  Qed.
  Lemma glG_fuel_mon_list L a0 a1 :
    a0 w≤ a1 →
    ([∗ list] k ∈ L, glG_fuel k a1) ⊢ |==> ([∗ list] k ∈ L, glG_fuel k a0).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_mon.
  Qed.
  Lemma glG_fuel_mon_set L a0 a1 :
    a0 w≤ a1 →
    ([∗ set] k ∈ L, glG_fuel k a1) ⊢ |==> ([∗ set] k ∈ L, glG_fuel k a0).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_mon.
  Qed.

  Lemma glG_fuel_split k a0 a1 :
    glG_fuel k (a0 w+ a1) ⊣⊢ glG_fuel k a0 ∗ glG_fuel k a1.
  Proof.
    rewrite /glG_fuel. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -cash_add) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite -cash_add). iSplitL "H1"; iFrame.
  Qed.
  Lemma glG_fuel_split_list L a0 a1 :
    ([∗ list] k ∈ L, glG_fuel k (a0 w+ a1)) ⊣⊢ ([∗ list] k ∈ L, glG_fuel k a0) ∗ ([∗ list] k ∈ L, glG_fuel k a1).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply glG_fuel_split.
  Qed.
  Lemma glG_fuel_split_set L a0 a1 :
    ([∗ set] k ∈ L, glG_fuel k (a0 w+ a1)) ⊣⊢ ([∗ set] k ∈ L, glG_fuel k a0) ∗ ([∗ set] k ∈ L, glG_fuel k a1).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply glG_fuel_split.
  Qed.

  Lemma glG_fuel_mon_split k a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    glG_fuel k a2 ⊢ |==> glG_fuel k a0 ∗ glG_fuel k a1.
  Proof.
    intros LE. iIntros "H". iApply glG_fuel_split. iApply glG_fuel_mon; done.
  Qed.
  Lemma glG_fuel_mon_split_list L a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    ([∗ list] k ∈ L, glG_fuel k a2) ⊢ |==> ([∗ list] k ∈ L, glG_fuel k a0) ∗ ([∗ list] k ∈ L, glG_fuel k a1).
  Proof.
    iIntros (LE) "H". iPoseProof (glG_fuel_mon_list with "H") as ">H"; first done.
    by iApply glG_fuel_split_list.
  Qed.
  Lemma glG_fuel_mon_split_set L a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    ([∗ set] k ∈ L, glG_fuel k a2) ⊢ |==> ([∗ set] k ∈ L, glG_fuel k a0) ∗ ([∗ set] k ∈ L, glG_fuel k a1).
  Proof.
    iIntros (LE) "H". iPoseProof (glG_fuel_mon_set with "H") as ">H"; first done.
    by iApply glG_fuel_split_set.
  Qed.

  Lemma glG_fuel_lt k a0 a1 :
    a0 w< a1 →
    glG_fuel k a1 ⊢ |==> glG_fuel k a0 ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ glG_fuel k c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (glG_fuel_mon_split _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.
  Lemma glG_fuel_lt_list L a0 a1 :
    a0 w< a1 →
    ([∗ list] k ∈ L, glG_fuel k a1) ⊢ |==> ([∗ list] k ∈ L, glG_fuel k a0) ∗ ([∗ list] k ∈ L, ∃ c, ⌜ wzero w< c ⌝ ∗ glG_fuel k c).
  Proof.
    iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_lt.
  Qed.
  Lemma glG_fuel_lt_set L a0 a1 :
    a0 w< a1 →
    ([∗ set] k ∈ L, glG_fuel k a1) ⊢ |==> ([∗ set] k ∈ L, glG_fuel k a0) ∗ ([∗ set] k ∈ L, ∃ c, ⌜ wzero w< c ⌝ ∗ glG_fuel k c).
  Proof.
    iIntros (LE) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_lt.
  Qed.

  Lemma glG_fuel_supply_mon k a0 a1 q :
    a0 w≤ a1 →
    glG_fuel_supply k a0 q ⊢ |==> glG_fuel_supply k a1 q.
  Proof.
    intros LE. rewrite /glG_fuel_supply. apply own_update.
    by apply reservation_map_update, debt_update.
  Qed.

  Lemma glG_fuel_supply_add k a0 a1 q0 q1 :
    glG_fuel_supply k a0 q0 ∗ glG_fuel_supply k a1 q1
    ⊢ ∃ b, glG_fuel_supply k b (q0 + q1) ∗ ⌜ b w≤ a0 ∧ b w≤ a1 ⌝.
  Proof.
    rewrite /glG_fuel_supply. iIntros "[H1 H2]".
    iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame).
    iEval (rewrite -!reservation_map_data_op) in "H".
    destruct (debt_add a0 a1 q0 q1) as (b&Heq&Hle0&Hle1). rewrite Heq.
    iExists _. iSplitL; done.
  Qed.

  Lemma glG_fuel_supply_dfrac_valid k a q :
    glG_fuel_supply k a q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_fuel_supply. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite !reservation_map_data_valid in V.
    rewrite bank_valid_debt in V. destruct V. auto.
  Qed.

  Lemma glG_fuel_supply_issue k a0 a1 :
    glG_fuel_supply k a0 (1)%Qp
    ⊢ |==> glG_fuel_supply k (a0 w+ a1) (1)%Qp ∗ glG_fuel k a1.
  Proof.
    rewrite /glG_fuel_supply -own_op. apply own_update.
    rewrite -!reservation_map_data_op. apply reservation_map_update.
    apply debt_owe.
  Qed.
  Lemma glG_fuel_supply_issue_2 k q0 q1 a0 a1 b :
    (q0 + q1 = 1)%Qp →
    glG_fuel_supply k a0 q0 ∗ glG_fuel_supply k a1 q1
    ⊢ |==> glG_fuel_supply k (a0 w+ b) q0 ∗ glG_fuel_supply k (a0 w+ b) q1 ∗ glG_fuel k b.
  Proof.
    iIntros (Heq) "H". iDestruct (glG_fuel_supply_add with "H") as "(%&H&%)".
    iMod (glG_fuel_supply_mon _ _ a0 with "H") as "H".
    { destruct H. auto. }
    rewrite Heq. iMod (glG_fuel_supply_issue _ _ b with "H") as "[H Hp]".
    iEval (rewrite -Heq) in "H". iDestruct "H" as "[H0 H1]". by iFrame.
  Qed.

  Lemma glG_fuel_spend k a0 a1 q :
    glG_fuel_supply k a0 q ∗ glG_fuel k a1
    ⊢ |==> ∃ a2, ⌜(a1 w+ a2) w≤ a0⌝ ∗ glG_fuel_supply k a2 q.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -!reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ x, ∃ a2, (x = (debt a2 q)) ∧ (a1 w+ a2 w≤ a0))
                (λ m, ∃ a2, (m = (reservation_map_data k (debt a2 q))) ∧ (a1 w+ a2 w≤ a0))
             ).
      { eapply debt_pay. }
      { intros. destruct H as (a2&A0&A1). eexists. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplitR; done.
  Qed.
  Lemma glG_fuel_spend_2 k a0 a1 q0 q1 c :
    glG_fuel_supply k a0 q0 ∗ glG_fuel_supply k a1 q1 ∗ glG_fuel k c
    ⊢ |==> ∃ a2, (⌜(c w+ a2) w≤ a0 ∧ (c w+ a2) w≤ a1⌝) ∗
              glG_fuel_supply k a2 q0 ∗ glG_fuel_supply k a2 q1.
  Proof.
    iIntros "(H0&H1&H2)". iDestruct (glG_fuel_supply_add with "[H0 H1]") as "(%&H&%)"; first iFrame.
    iMod (glG_fuel_spend with "[H H2]") as "(%&%&H)"; first iFrame.
    iDestruct "H" as "[H0 H1]". iModIntro. iFrame. iPureIntro. destruct H. split.
    - etransitivity; [eapply H0 | eauto].
    - etransitivity; [eauto | eapply H].
  Qed.

  Lemma glG_fuel_alloc D k a :
    k ∉ D →
    glG_fuel_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_fuel_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        glG_fuel_supply k a 1 ∗ glG_fuel k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (debt a 1 ⋅ cash a) with "Htk") as "[Htk >H]"; auto.
    { apply bank_valid_debt_cash. split; done. }
    rewrite !reservation_map_data_op. iDestruct "H" as "[H1 H2]".
    rewrite /glG_fuel_supply /glG_fuel. by iFrame.
  Qed.

  (** Owner rules *)
  Lemma glG_owner_agree k t1 t2 q1 q2 :
    glG_owner k t1 q1 ∗ glG_owner k t2 q2 ⊢ ⌜ t1 = t2 ∧ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_owner. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    apply frac_agree_op_valid in Hv. iPureIntro. destruct Hv. done.
  Qed.

  Lemma glG_owner_valid k t q :
    glG_owner k t q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_owner. iIntros "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    by iApply (frac_agree_validI).
  Qed.

  Lemma glG_owner_update_2 k t1 t2 q1 q2 t :
    (q1 + q2 = 1)%Qp →
    glG_owner k t1 q1 ∗ glG_owner k t2 q2 ⊢ |==> glG_owner k t q1 ∗ glG_owner k t q2.
  Proof.
    rewrite /glG_owner -!own_op -!reservation_map_data_op.
    intros Heq. by apply own_update, reservation_map_update, frac_agree_update_2.
  Qed.
  Lemma glG_owner_update k t1 t2 :
    glG_owner k t1 1 ⊢ |==> glG_owner k t2 1.
  Proof.
    iIntros "H". iDestruct "H" as "[H1 H2]".
    iMod (glG_owner_update_2 _ _ _ _ _ t2 with "[H1 H2]") as "[H1 H2]"; [| iFrame |].
    { by rewrite Qp.div_2. }
    iCombine "H1 H2" as "H". done.
  Qed.

  Lemma glG_owner_alloc D k t :
    k ∉ D →
    glG_owner_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_owner_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗ glG_owner k t 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (to_frac_agree 1 (t : leibnizO _)) with "Htk") as "[Htk >H]"; auto.
    { done. }
    rewrite /glG_owner. by iFrame.
  Qed.

  (** glG_variant rules *)
  Lemma glG_variant_acc E N k v q P Q R :
    ↑N ⊆ E →
    glG_variant N k v q P Q R ={E,E ∖ ↑N}=∗
    ▷ glG_variant_internal k v q P Q R ∗
    (▷ glG_variant_internal k v q P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU". iPoseProof (inv_acc with "GU") as "$"; eauto.
  Qed.

  Lemma glG_variant_acc_version E N k v q1 q2 P Q R :
    ↑N ⊆ E →
    glG_variant N k v q1 P Q R -∗ glG_version k v q2 ={E,E ∖ ↑N}=∗
    (▷ (glG_version k v q2 ∗
        ((glG_locked k v q1 ∗ P) ∨
           (glG_unlocked k v ∗ Q)))) ∗
    (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC".
      + iNext. iDestruct "H" as "[H | H]"; iFrame.
      + iIntros "H". iApply "ACC". done.
    - iModIntro. iSplitR "ACC"; last iFrame.
      iNext. iDestruct "H" as "(Gvd& _)".
      iPoseProof (glG_version_done_valid with "[$GV $Gvd]") as "%". lia.
  Qed.

  Lemma glG_variant_acc_locked E N k v q1 q2 P Q R :
    ↑N ⊆ E →
    glG_variant N k v q1 P Q R -∗ glG_locked k v q2
    ={E,E ∖ ↑N}=∗
    (▷ (glG_locked k v q2 ∗
        ((glG_locked k v q1 ∗ P) ∨
           (glG_version_done k v ∗ R)))) ∗
    (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC".
      + iNext. iDestruct "H" as "[H | H]"; first iFrame.
        iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
      + done.
    - iModIntro. iSplitR "ACC"; iFrame.
  Qed.

  Lemma glG_variant_acc_unlocked E N k v q1 P Q R :
    ↑N ⊆ E →
    glG_variant N k v q1 P Q R -∗ glG_unlocked k v
    ={E,E ∖ ↑N}=∗
    (▷ (Q ∨ (glG_version_done k v ∗ R))) ∗
    (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC"; last done.
      iNext. iDestruct "H" as "[H | [_ $]]".
      iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - iModIntro. iSplitR "ACC"; iFrame.
  Qed.
  Lemma glG_variant_acc_unlocked_pin E N k v q1 P Q R :
    ↑N ⊆ E →
    glG_variant N k v q1 P Q R -∗ glG_unlocked k v -∗ glG_version_pin k v
    ={E,E ∖ ↑N}=∗
    (▷ Q) ∗
    (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV Gvp". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC"; last done.
      iNext. iDestruct "H" as "[H | [_ $]]".
      iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - iModIntro. iSplitR "ACC"; last iFrame.
      iNext. iDestruct "H" as "[#Gvd _]".
      iPoseProof (glG_version_pin_done_valid with "[$Gvp $Gvd]") as "%". lia.
  Qed.

  Lemma glG_variant_acc_version_locked E N k v q1 q2 q3 P Q R :
    ↑N ⊆ E →
    glG_variant N k v q1 P Q R -∗ glG_version k v q2 -∗ glG_locked k v q3 ={E,E ∖ ↑N}=∗
    ▷ (glG_version k v q2 ∗ glG_locked k v q3 ∗ (glG_locked k v q1 ∗ P)) ∗
    (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV GL". iMod (glG_variant_acc_version with "GU GV") as "[H ACC]"; first auto.
    iModIntro. iSplitR "ACC".
    - iNext. iDestruct "H" as "(Gv& [H | H])"; first iFrame.
      iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - done.
  Qed.

  Lemma glG_variant_acc_version_unlocked E N k v q1 q2 P Q R :
    ↑N ⊆ E →
    glG_variant N k v q1 P Q R -∗ glG_version k v q2 -∗ glG_unlocked k v ={E,E ∖ ↑N}=∗
    ▷ (glG_version k v q2 ∗ glG_unlocked k v ∗ (glG_unlocked k v ∗ Q)) ∗
    (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV GL". iMod (glG_variant_acc_version with "GU GV") as "[H ACC]"; first auto.
    iModIntro. iSplitR "ACC".
    - iNext. iDestruct "H" as "(Gv& [H | H])"; last iFrame.
      iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - done.
  Qed.

  (* Lemma glG_variant_acc_done E N k v q1 P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q1 P Q R -∗ glG_version_done k v ={E,E ∖ ↑N}=∗ *)
  (*   (▷ (glG_version_done k v ∗ R)) ∗ *)
  (*   (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "#GU #GD". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto. *)
  (*   - iModIntro. iSplitR "ACC". *)
  (*     + iNext. iDestruct "H" as "[(H& _) | (H& _)]". *)
  (*       * iPoseProof (glG_version_done_valid with "[$]") as "%". lia. *)
  (*       * iPoseProof (glG_version_done_valid with "[$]") as "%". lia. *)
  (*     + done. *)
  (*   - iModIntro. iFrame. *)
  (* Qed. *)

  (* Allocates *)
  Lemma glG_variant_alloc_locked E N k v q P Q R :
    (▷ (glG_locked k v q ∗ P)) ={E}=∗ glG_variant N k v q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.
  Lemma glG_variant_alloc_unlocked E N k v q P Q R :
    (▷ (glG_unlocked k v ∗ Q)) ={E}=∗ glG_variant N k v q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.
  Lemma glG_variant_alloc_done E N k v q P Q R :
    (▷ (glG_version_done k v ∗ R)) ={E}=∗ glG_variant N k v q P Q R.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.

  (* (** glG_always rules *) *)
  (* Lemma glG_always_unfold N k v P : *)
  (*   glG_always N k v P -∗ (glG_done k ∗ glG_version_pin k v ∗ inv N P). *)
  (* Proof. iIntros "$". Qed. *)

  (* Lemma glG_always_acc E N k v P : *)
  (*   ↑N ⊆ E → *)
  (*   glG_always N k v P ={E,E ∖ ↑N}=∗ *)
  (*   glG_done k ∗ glG_version_pin k v ∗ (▷ P) ∗ *)
  (*   ((▷ P) ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "(#GLD& #GVP& #IP)". iMod (inv_acc with "IP") as "[P ACC]"; first auto. *)
  (*   iFrame. auto. *)
  (* Qed. *)

  (* Lemma glG_always_alloc E N k v P : *)
  (*   glG_done k -∗ glG_version_pin k v -∗ (▷ P) ={E}=∗ glG_always N k v P. *)
  (* Proof. iIntros "$ $ P". iApply inv_alloc. iFrame. Qed. *)

  (** glsat rules *)
  Lemma glsat_elem Ω k :
    glsat Ω ∗ glG_elem k ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /glG_elem.
    rewrite /glsat -!lock. iIntros "(Hsat& (%& #Ge))".
    iDestruct "Hsat" as "((%& %& HE)& HS& HV& HF& HO& HM)".
    iPoseProof (glG_witfun_lookup with "[$]") as "%".
    rewrite H. apply elem_of_dom_2 in H0. auto.
  Qed.
  Lemma glsat_elem_lookup Ω k :
    glsat Ω ∗ glG_elem k
    ⊢ ∃ v, (⌜ (∃ a t, Ω !! k = Some (v, gl_locked a t)) ⌝) ∨
             (glG_unlocked k v ∗ (⌜ Ω !! k = Some (v, gl_unlocked) ⌝)).
  Proof.
    iIntros "(Hsat & #Ge)". iPoseProof (glsat_elem with "[$]") as "%".
    apply elem_of_dom in H. destruct H.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete _ _ _ _ H with "HM") as "[H _]".
    destruct x. iDestruct "H" as "(Gv2& VSa& VS& #Gvl& %& #Gwf& %& Gfs& %& H)". destruct g0.
    - iExists _. iLeft. iPureIntro. eauto.
    - iDestruct "H" as "(#Gu& _)"; eauto.
  Qed.

  Lemma glsat_lookup_version Ω k v q :
    glsat Ω ∗ glG_elem k ∗ glG_version k v q
    ⊢ ∃ g, ⌜Ω !! k = Some (v, g)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gv)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    destruct o. iDestruct "LU" as "(Gv2& VSa& VS& #Gvl& %& Gwf& %& Gfs& %Bound& Mk)".
    iPoseProof (glG_version_agree with "[$Gv $Gv2]") as "%". destruct H; subst; eauto.
  Qed.
  Lemma glsat_lookup_version_lb Ω k v :
    glsat Ω ∗ glG_elem k ∗ glG_version_lb k v
    ⊢ ∃ v' g, ⌜Ω !! k = Some (v', g) ∧ v ≤ v'⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gv)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    destruct o. iDestruct "LU" as "(Gv2& VSa& VS& #Gvl& %& Gwf& %& Gfs& %Bound& Mk)".
    iPoseProof (glG_version_lb_lb with "[$Gv $Gv2]") as "%". eauto.
  Qed.
  Lemma glsat_lookup_version_done Ω k v :
    glsat Ω ∗ glG_elem k ∗ glG_version_done k v
    ⊢ ∃ v' g, ⌜Ω !! k = Some (v', g) ∧ v < v'⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gv)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    destruct o. iDestruct "LU" as "(Gv2& VSa& VS& #Gvl& %& Gwf& %& Gfs& %Bound& Mk)".
    iPoseProof (glG_version_done_valid with "[$Gv $Gv2]") as "%". eauto.
  Qed.

  Lemma glsat_lookup_locked Ω k v q :
    glsat Ω ∗ glG_elem k ∗ glG_locked k v q
    ⊢ ∃ a t, ⌜Ω !! k = Some (v, gl_locked a t)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    destruct o. iDestruct "LU" as "(Gv2& VSa& VS& #Gvl& %& Gwf& %& Gfs& %Bound& Mk)".
    iPoseProof (glG_locked_is_allocated with "[$VSa $Gl]") as "%INv".
    pose proof INv. apply elem_of_set_seq in H. assert (0 ≤ v < (0 + g) ∨ v = g) by lia. destruct H0.
    { assert (v ∈ (set_seq 0 g : gset gl_version)) by (by eapply elem_of_set_seq).
      iPoseProof (big_sepS_delete _ _ _ H1 with "VS") as "[[Gvl2 Gu] VS]".
      iPoseProof (glG_locked_unlocked_false with "[$Gl $Gu]") as "%". done. }
    subst g. destruct g0; eauto.
    iDestruct "Mk" as "(#Gu& _)". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
  Qed.
  Lemma glsat_lookup_unlocked Ω k v :
    glsat Ω ∗ glG_elem k ∗ glG_unlocked k v
    ⊢ ⌜ Ω !! k = Some (v, gl_unlocked) ∨ ∃ v' g, v < v' ∧ Ω !! k = Some (v', g) ⌝.
  Proof.
    iIntros "(Hsat & #Ge & #Gu)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    destruct o. iDestruct "LU" as "(Gv2& VSa& VS& #Gvl& %& Gwf& %& Gfs& %Bound& Mk)".
    iPoseProof (glG_unlocked_is_allocated with "[$VSa $Gu]") as "%INv".
    pose proof INv. apply elem_of_set_seq in H. assert (0 ≤ v < (0 + g) ∨ v = g) by lia. destruct H0.
    - iRight. iExists g. iPureIntro. eexists. split_and !; eauto. lia.
    - subst g. destruct g0; eauto.
      iDestruct "Mk" as "(Gl& _)". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
  Qed.
  Lemma glsat_lookup_owner Ω k t q :
    glsat Ω ∗ glG_elem k ∗ glG_owner k t q
    ⊢ ∃ v a, ⌜Ω !! k = Some (v, gl_locked a t)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Go)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    destruct o. iDestruct "LU" as "(Gv2& VSa& VS& #Gvl& %& Gwf& %& Gfs& %Bound& Mk)".
    destruct g0.
    - iDestruct "Mk" as "(Gl& %& Go2)".
      iPoseProof (glG_owner_agree with "[$Go $Go2]") as "(%&%)". subst. eauto.
    - iDestruct "Mk" as "(_& %& Go2)".
      iPoseProof (glG_owner_agree with "[$Go $Go2]") as "(%&%)".
      apply Qp.not_add_le_r in H0. done.
  Qed.

  Lemma glsat_alloc_gl_locked Ω k ξ v t :
    k ∉ dom Ω →
    glsat Ω
    ⊢ |==> glsat (<[k:=(v, gl_locked (Σ[ξ] v) t)]>Ω) ∗
        glG_witfun k ξ ∗
        glG_elem k ∗
        glG_locked k v (1/2 + 1/2/2)%Qp ∗
        glG_version k v (1/2 + 1/2/2)%Qp ∗
        glG_fuel k (Σ[ξ] v) ∗
        glG_owner k t (1/2 + 1/2/2)%Qp ∗
        ([∗ set] u ∈ (set_seq 0 v), glG_version_lb k u ∗ glG_unlocked k u) ∗
        (⌜ Ω ↪ₐ (<[k:=(v, gl_locked (Σ[ξ] v) t)]>Ω) ⌝).
  Proof.
    iIntros (Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iDestruct "HE" as "(%& %Dom& HE)".
    iMod (glG_witfun_alloc _ k ξ with "HE") as "[HE #Gwf]".
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    iMod (glG_state_id_alloc _ k (⊤ ∖ gset_to_coPset (set_map encode (∅ : gset gl_version))) with "HS") as "[HS HSVk]"; first auto.
    iMod (glG_state_alloc_gen_seq _ 0 0 (S v) (λ u, 0) with "HSVk") as "[HSVk Gl]".
    iEval (rewrite set_seq_S_end_union_L) in "Gl". iPoseProof (big_sepS_union with "Gl") as "[Gl Gus]".
    { apply set_seq_S_end_disjoint. }
    rewrite big_sepS_singleton.
    iAssert (glG_locked k v 1)%I with "Gl" as "Gl".
    iAssert (|==> [∗ set] u ∈ (set_seq 0 v), glG_unlocked k u)%I with "[Gus]" as ">#Gus".
    { simpl. iClear "Gwf". iStopProof. induction v; iIntros "Gus".
      { simpl. rewrite !big_sepS_empty. done. }
      rewrite !set_seq_S_end_union_L. rewrite !big_sepS_union.
      2,3: apply set_seq_S_end_disjoint.
      rewrite !big_sepS_singleton. iDestruct "Gus" as "[Gu Gus]". iMod (IHv with "Gus") as "$".
      iAssert (glG_locked k v 1)%I with "Gu" as "Gu". iDestruct "Gu" as "[Gu1 Gu2]".
      iApply glG_locked_to_unlocked_2; last iFrame. apply Qp.div_2.
    }
    iMod (glG_version_alloc _ k v with "HV") as "[HV Gv]"; first auto.
    iMod (glG_fuel_alloc _ k (Σ[ξ] v) with "HF") as "(HF& Gfsp& Gf)"; first set_solver.
    iMod (glG_owner_alloc _ k t with "HO") as "[HO Go]"; first auto.
    iDestruct "Gl" as "[Gl1 [Gl2 Gl']]". iCombine "Gl1 Gl2" as "Gl".
    iDestruct "Gv" as "[Gv1 [Gv2 Gv']]". iCombine "Gv1 Gv2" as "Gv".
    iDestruct "Go" as "[Go1 [Go2 Go']]". iCombine "Go1 Go2" as "Go".
    iPoseProof (glG_version_get_lb_eq with "Gv") as "#Gvl".
    iAssert ([∗ set] u ∈ (set_seq 0 v), glG_version_lb k u)%I with "[]" as "#Glvs".
    { iClear "Gwf Gus". iStopProof. induction v; iIntros "#Glv".
      { done. }
      rewrite !set_seq_S_end_union_L. rewrite !big_sepS_union.
      2: apply set_seq_S_end_disjoint.
      rewrite !big_sepS_singleton. iPoseProof (glG_version_lb_mon _ _ v with "Glv") as "#Glv2".
      1: auto.
      iFrame "Glv2". iPoseProof (IHv with "Glv2") as "$".
    }
    iPoseProof (big_sepS_sep with "[Glvs Gus]") as "#Grs".
    { iSplitL; [iFrame "Glvs" | iFrame "Gus"]. }
    iPoseProof (glG_witfun_elem with "Gwf") as "#Ge".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HV HF HO". iFrame "Ge Gl Gv Gf Go Gwf Grs".
    iSplitL; cycle 1.
    { iPureIntro. exists k, v. split; eauto. }
    iSplitR.
    { rewrite dom_insert_L Dom. done. }
    iApply big_sepM_insert; first auto. iFrame. iFrame "Gwf Grs Gvl". auto.
  Qed.

  Lemma glsat_alloc_gl_unlocked Ω k ξ v :
    Inhabited gl_owner →
    k ∉ dom Ω →
    glsat Ω
    ⊢ |==> glsat (<[k:=(v, gl_unlocked)]>Ω) ∗
        glG_witfun k ξ ∗
        glG_elem k ∗
        glG_unlocked k v ∗
        glG_version k v (1/2 + 1/2/2)%Qp ∗
        glG_fuel k (Σ[ξ] v) ∗
        ([∗ set] u ∈ (set_seq 0 v), glG_version_lb k u ∗ glG_unlocked k u) ∗
        (⌜ Ω ↪ₐ (<[k:=(v, gl_unlocked)]>Ω) ⌝).
  Proof.
    iIntros (INH Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iDestruct "HE" as "(%& %Dom& HE)".
    iMod (glG_witfun_alloc _ k ξ with "HE") as "[HE #Gwf]".
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    iMod (glG_state_id_alloc _ k (⊤ ∖ gset_to_coPset (set_map encode (∅ : gset gl_version))) with "HS") as "[HS HSVk]"; first auto.
    iMod (glG_state_alloc_gen_seq _ 0 0 (S v) (λ u, 0) with "HSVk") as "[HSVk Gl]".
    iEval (rewrite set_seq_S_end_union_L) in "Gl". iPoseProof (big_sepS_union with "Gl") as "[Gl Gus]".
    { apply set_seq_S_end_disjoint. }
    rewrite big_sepS_singleton.
    iAssert (glG_locked k v 1)%I with "Gl" as "[Gl1 Gl2]".
    iMod (glG_locked_to_unlocked_2 with "[$Gl1 $Gl2]") as "#Gu". 1: apply Qp.div_2.
    iAssert (|==> [∗ set] u ∈ (set_seq 0 v), glG_unlocked k u)%I with "[Gus]" as ">#Gus".
    { simpl. iClear "Gwf Gu". iStopProof. induction v; iIntros "Gus".
      { simpl. rewrite !big_sepS_empty. done. }
      rewrite !set_seq_S_end_union_L. rewrite !big_sepS_union.
      2,3: apply set_seq_S_end_disjoint.
      rewrite !big_sepS_singleton. iDestruct "Gus" as "[Gu Gus]". iMod (IHv with "Gus") as "$".
      iAssert (glG_locked k v 1)%I with "Gu" as "Gu". iDestruct "Gu" as "[Gu1 Gu2]".
      iApply glG_locked_to_unlocked_2; last iFrame. apply Qp.div_2.
    }
    iMod (glG_version_alloc _ k v with "HV") as "[HV Gv]"; first auto.
    iMod (glG_fuel_alloc _ k (Σ[ξ] v) with "HF") as "(HF& Gfsp& Gf)"; first set_solver.
    iMod (glG_owner_alloc _ k (inhabitant (A:=gl_owner)) with "HO") as "[HO Go]"; first auto.
    iDestruct "Gv" as "[Gv1 [Gv2 Gv']]". iCombine "Gv1 Gv2" as "Gv".
    iPoseProof (glG_version_get_lb_eq with "Gv") as "#Gvl".
    iAssert ([∗ set] u ∈ (set_seq 0 v), glG_version_lb k u)%I with "[]" as "#Glvs".
    { iClear "Gwf Gus Gu". iStopProof. induction v; iIntros "#Glv".
      { done. }
      rewrite !set_seq_S_end_union_L. rewrite !big_sepS_union.
      2: apply set_seq_S_end_disjoint.
      rewrite !big_sepS_singleton. iPoseProof (glG_version_lb_mon _ _ v with "Glv") as "#Glv2".
      1: auto.
      iFrame "Glv2". iPoseProof (IHv with "Glv2") as "$".
    }
    iPoseProof (big_sepS_sep with "[Glvs Gus]") as "#Grs".
    { iSplitL; [iFrame "Glvs" | iFrame "Gus"]. }
    iPoseProof (glG_witfun_elem with "Gwf") as "#Ge".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HV HF HO". iFrame "Ge Gu Gv Gf Gwf Grs".
    iSplitL; cycle 1.
    { iPureIntro. exists k, v. split; auto. }
    iSplitR.
    { rewrite dom_insert_L Dom. done. }
    iApply big_sepM_insert; first auto. iFrame. iFrame "Gwf Grs Gvl". auto.
  Qed.

  (* ghost_lock_step rules: progress, unlock, lock *)
  Lemma glsat_progress_one Ω k v a t c :
    (Ω !! k = Some (v, gl_locked a t)) →
    (wzero w< c) →
    glsat Ω ∗ glG_fuel k c
    ⊢ |==> ∃ a', glsat (<[k:=(v, gl_locked a' t)]>Ω) ∗
              (⌜ ghost_lock_step (v, gl_locked a t) (v, gl_locked a' t) ⌝).
  Proof.
    intros LU Hc. iIntros "(Hsat & Gf)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(Gvk& VSa& VS& #Gvl& %& #Gwf& %& Gfs& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& %LEa& Gok)".
    iMod (glG_fuel_spend with "[$Gfs $Gf]") as "(%&%&Gfs)".
    assert (LT : a2 w< α).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (v, gl_locked a2 t)) with "[HM VSa VS Glk Gvk Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gvl Gwf". iPureIntro. split; last done.
      etrans; last eauto. apply WFOCM.lt_le. auto. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HE HS HV HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. econstructor. eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma glsat_progress Ω (C : gl_cond) :
    (∀ k g, C k g → ∃ v a o, g = (v, gl_locked a o)) →
    glsat Ω ∗
    ([∗ map] k ↦ g ∈ Ω, (⌜ C k g ⌝ ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ glG_fuel k c) ∨ (⌜ ¬ C k g ⌝))
    ⊢ |==> ∃ Ω', glsat Ω' ∗ (⌜ Ω ↪ₚ Ω' | C ⌝).
  Proof.
    iIntros (HC) "(Hsat & Cs)".
    iAssert (∃ Ω1 Ω2, (⌜ Ω1 ##ₘ Ω2 ∧ Ω = Ω1 ∪ Ω2 ∧ map_Forall (λ k g, C k g) Ω1 ∧ map_Forall (λ k g, ¬ C k g) Ω2 ⌝) ∗
                      ([∗ map] k ↦ g ∈ Ω1, (⌜ C k g ⌝ ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ glG_fuel k c)) ∗
                      ([∗ map] k ↦ g ∈ Ω2, (⌜ ¬ C k g ⌝))
            )%I with "[Cs]" as "(%& %& (%Disj& %EQO& %CO1& %CO2)& Cs& NCs)".
    { iStopProof. induction Ω using map_ind; iIntros "M".
      { iExists ∅, ∅. rewrite !big_sepM_empty. done. }
      rewrite !big_sepM_insert; auto. iDestruct "M" as "(H& M)".
      iPoseProof (IHΩ with "M") as "(%& %& (%Disj& %EqO& %HC1& %HC2)& M1& M2)". clear IHΩ.
      assert (i ∉ dom Ω1 ∧ i ∉ dom Ω2).
      { subst. apply not_elem_of_dom in H. set_solver + H. }
      destruct H0 as [Nin1 Nin2]. apply not_elem_of_dom in Nin1, Nin2.
      iDestruct "H" as "[(%Ci& (%& %Hc& Gfi)) | %NCi]".
      - iExists (<[i:=x]>Ω1), Ω2. iFrame. iSplitR.
        { iPureIntro. split_and !; auto.
          - apply map_disjoint_insert_l_2; auto.
          - subst. apply insert_union_l.
          - apply map_Forall_insert; auto. }
        iApply big_sepM_insert; auto. iFrame. done.
      - iExists Ω1, (<[i:=x]>Ω2). iFrame. iSplitR.
        { iPureIntro. split_and !; auto.
          - apply map_disjoint_insert_r_2; auto.
          - subst. apply insert_union_r; auto.
          - apply map_Forall_insert; auto. }
        iApply big_sepM_insert; auto.
    }
    assert (Sub : Ω1 ⊆ Ω).
    { subst. apply map_union_subseteq_l. }
    iAssert (|==> ∃ Ω' : ghost_locks, glsat Ω' ∗ ⌜Ω ↪ₚ Ω' | (λ k _, k ∈ dom Ω1)⌝)%I with "[-]" as ">H"; cycle 1.
    { iDestruct "H" as "(%& S& %)". iModIntro. iFrame. iPureIntro. destruct H as [H Hkeep].
      split; last auto.
      eapply gls_cond_rel_iff_lookup; first eapply H.
      intros. simpl. subst. split; intros.
      - apply elem_of_dom in H1. destruct H1. erewrite lookup_union_Some_l in H0; last eauto. inv H0.
        apply CO1 in H1. auto.
      - apply lookup_union_Some in H0; last auto. destruct H0.
        + apply elem_of_dom; eauto.
        + apply CO2 in H0. done.
    }
    iClear "NCs". iStopProof. clear dependent Ω2. revert CO1 Ω Sub.
    induction Ω1 using map_ind; iIntros (CO Ω Sub) "(S& M)".
    { iExists Ω. iModIntro. iFrame. iPureIntro. split; last done.
      repeat intro. destruct (Ω !! i) eqn:LUi.
      - econstructor. right. split; intros; done.
      - econstructor.
    }
    rewrite !big_sepM_insert; auto. apply map_Forall_insert in CO; auto. destruct CO as (Ci& CO).
    iDestruct "M" as "((_& %& %LTc& Bpi)& M)".
    iMod (IHΩ1 CO with "[$S $M]") as "(%& S& %Prog1)".
    { etransitivity; last eapply Sub. eapply insert_subseteq; auto. }
    clear IHΩ1.
    assert (LUi1 : Ω !! i = Some x).
    { eapply lookup_weaken; last eapply Sub. apply lookup_insert_eq. }
    assert (LUi2 : Ω' !! i = Some x).
    { destruct Prog1 as [Prog1 Hkeep]. specialize (Prog1 i). erewrite LUi1 in Prog1. inv Prog1.
      destruct H2.
      - destruct H0. apply not_elem_of_dom in H. done.
      - destruct H0. subst. auto.
    }
    pose proof Ci. apply HC in H0. destruct H0 as (v'& a& t& ?). subst.
    iMod (glsat_progress_one with "[$S $Bpi]") as "(%& S& %Progi)"; auto.
    { eauto. }
    iFrame. iPureIntro. simpl. assert (Prog2 : Ω' ↪ₚ <[i:=(v', gl_locked a' t)]> Ω' | λ k _, k = i).
    { split.
      - intro j. destruct (decide (j = i)).
        { subst. rewrite LUi2. rewrite lookup_insert_eq. econstructor. left. split; done. }
        rewrite lookup_insert_ne; auto. destruct (Ω' !! j) eqn:LUj; econstructor. right; split; done.
      - intro j. destruct (decide (j = i)).
        { subst. rewrite LUi2. rewrite lookup_insert_eq. econstructor. done. }
        rewrite lookup_insert_ne; auto. done.
    }
    (* Disjoint gl_conds *)
    destruct Prog1 as [Prog1 Hkeep1], Prog2 as [Prog2 Hkeep2]. split; last (etrans; eauto).
    eapply gls_cond_rel_split_cond. 4,5: eauto. all: simpl.
    - intros. rewrite dom_insert_L. set_solver.
    - intros. destruct (decide (k = i)); auto. subst. left. by apply not_elem_of_dom.
    - repeat intro. auto.
  Qed.

  Lemma glsat_progress_one_owner Ω k v a t1 t2 c :
    (Ω !! k = Some (v, gl_locked a t1)) →
    (wzero w< c) →
    glsat Ω ∗ glG_owner k t1 (1/2 + 1/2/2)%Qp ∗ glG_fuel k c
    ⊢ |==> ∃ a', glsat (<[k:=(v, gl_locked a' t2)]>Ω) ∗ glG_owner k t2 (1/2 + 1/2/2)%Qp ∗
              (⌜ ghost_lock_step (v, gl_locked a t1) (v, gl_locked a' t2) ⌝).
  Proof.
    intros LU Hc. iIntros "(Hsat& Go& Gf)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(Gvk& VSa& VS& #Gvl& %& #Gwf& %& Gfs& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& %LEa& Gok)".
    iMod (glG_fuel_spend with "[$Gfs $Gf]") as "(%&%&Gfs)".
    assert (LT : a2 w< α).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iMod (glG_owner_update_2 _ _ _ _ _ t2 with "[$Go $Gok]") as "[Go Gok]".
    { rewrite -Qp.add_assoc !Qp.div_2. done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (v, gl_locked a2 t2)) with "[HM VSa VS Glk Gvk Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gvl Gwf". iPureIntro. split; last done.
      etrans; last eauto. apply WFOCM.lt_le. auto. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HE HS HV HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. econstructor. eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma Qp_add_help_1 : (1 / 2 + 1 / 2 / 2 + 1 / 2 / 2 = 1)%Qp.
  Proof. by rewrite -Qp.add_assoc !Qp.div_2. Qed.

  Lemma glsat_unlock Ω k v t :
    glsat Ω ∗ glG_elem k ∗ glG_locked k v (1/2 + 1/2/2)%Qp ∗ glG_owner k t (1/2 + 1/2/2)%Qp
    ⊢ |==> glsat (<[k:=(v, gl_unlocked)]>Ω) ∗
        glG_unlocked k v ∗
        (⌜ ∀ a, ghost_lock_step (v, gl_locked a t) (v, gl_unlocked) ⌝).
  Proof.
    iIntros "(Hsat& #Ge& Gl& Go)".
    iPoseProof (glsat_lookup_locked with "[$Hsat $Ge $Gl]") as "(%&%& %LU)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(Gvk& VSa& VS& #Gvl& %& #Gwf& %& Gfs& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& %LEa& Gok)".
    iMod (glG_locked_to_unlocked_2 with "[$Gl $Glk]") as "#Gu".
    { apply Qp_add_help_1. }
    iPoseProof (glG_owner_agree with "[$Go $Gok]") as "(%& %)". clear H0. subst t0.
    iCombine "Go Gok" as "Gok". rewrite Qp_add_help_1.
    iModIntro.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (v, gl_unlocked)) with "[HM VSa VS Gu Gvk Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gvl Gwf Gu". auto. }
    rewrite dom_insert_lookup_L; last done. iFrame "HE HS HV HF HO".
    rewrite insert_delete_eq. iFrame. iFrame "Gu".
    iPureIntro. econstructor.
  Qed.

  Lemma glsat_version_pin_false Ω k v1 v2 :
    glsat Ω ∗ glG_elem k ∗ glG_version k v1 (1/2 + 1/2/2)%Qp ∗ glG_version_pin k v2
    ⊢ False.
  Proof.
    iIntros "(Hsat& #Ge& Gv& #Gvp)".
    iPoseProof (glsat_lookup_version with "[$Hsat $Ge $Gv]") as "(%& %LU)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(Gvk& VSa& VS& #Gvl& %& #Gwf& %& Gfs& %Bound& Mk)".
    iCombine "Gv Gvk" as "Gv". rewrite Qp_add_help_1.
    iPoseProof (glG_version_pin_false with "[$Gv $Gvp]") as "%". done.
  Qed.

  Lemma glsat_lock Ω k ξ v1 v2 t :
    v1 < v2 →
    glsat Ω ∗
    glG_witfun k ξ ∗ glG_unlocked k v1 ∗ glG_version k v1 (1/2 + 1/2/2)%Qp
    ⊢ |==> glsat (<[k:=(v2, gl_locked (Σ[ξ] v2) t)]>Ω) ∗
        glG_locked k v2 (1/2 + 1/2/2)%Qp ∗
        glG_version k v2 (1/2 + 1/2/2)%Qp ∗
        glG_fuel k (Σ[ξ]{S v1, v2}) ∗
        glG_owner k t (1/2 + 1/2/2)%Qp ∗
        ([∗ set] u ∈ (set_seq (S v1) (v2 - v1 - 1)), glG_version_lb k u ∗ glG_unlocked k u) ∗
        (⌜ ghost_lock_step (v1, gl_unlocked) (v2, gl_locked (Σ[ξ] v2) t) ⌝).
  Proof.
    iIntros (LTv) "(Hsat& #Gwf& #Gu& Gv)".
    iPoseProof (glG_witfun_elem with "Gwf") as "#Ge".
    iPoseProof (glsat_lookup_unlocked with "[$Hsat $Ge $Gu]") as "%LU".
    iPoseProof (glsat_lookup_version with "[$Hsat $Ge $Gv]") as "(%& %LU2)".
    destruct LU as [LU | (?&?&?&?)]; cycle 1.
    { rewrite H0 in LU2. inv LU2. lia. }
    rewrite LU in LU2. inv LU2.    
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(Gvk& VSa& VS& #Gvl& %& #Gwf2& %& Gfs& %Bound& _& %& Gok)".
    iPoseProof (glG_witfun_agree with "[]") as "%EQ".
    { iSplitL; [iFrame "Gwf" | iFrame "Gwf2"]. }
    subst ξ0. iClear "Gwf2".
    iMod (glG_state_alloc_gen_seq _ _ _ (v2 - v1) (λ _, 0) with "VSa") as "[VSa Gls]".
    assert (∃ δ, v2 - v1 = S δ).
    { inv LTv.
      - exists O. lia.
      - exists (m - v1). lia.
    }
    destruct H as (δ& EQd).
    iEval (rewrite EQd set_seq_S_end_union_L) in "Gls".
    iPoseProof (big_sepS_union with "Gls") as "[Gl Gus]".
    { apply set_seq_S_end_disjoint. }
    rewrite big_sepS_singleton.
    iAssert (glG_locked k v2 1)%I with "[Gl]" as "Gl".
    { replace (0 + S v1 + δ) with v2 by lia. done. }
    iAssert (|==> [∗ set] u ∈ (set_seq (S v1) (v2 - v1 - 1)), glG_unlocked k u)%I with "[Gus]" as ">#Gus".
    { simpl. iClear "Gwf Gu Ge Gvl". replace (v2 - v1 - 1) with δ by lia.
      remember (S v1) as v. clear dependent v1.
      iStopProof. revert v. induction δ; iIntros (?) "Gus".
      { simpl. rewrite !big_sepS_empty. done. }
      rewrite !set_seq_S_end_union_L. rewrite !big_sepS_union.
      2,3: apply set_seq_S_end_disjoint.
      rewrite !big_sepS_singleton. iDestruct "Gus" as "[Gu Gus]". iMod (IHδ with "Gus") as "$".
      iAssert (glG_locked k (v + δ) 1)%I with "Gu" as "Gu". iDestruct "Gu" as "[Gu1 Gu2]".
      iApply glG_locked_to_unlocked_2; last iFrame. apply Qp.div_2.
    }
    iDestruct "Gl" as "(Gl& [Gl' Gl2])". iCombine "Gl Gl'" as "Gl".
    iMod (glG_version_update_mon_2 _ _ v2 with "[$Gv $Gvk]") as "[Gv Gvk]".
    { apply Qp_add_help_1. }
    { lia. }
    iMod (glG_fuel_supply_issue _ _ (Σ[ξ] {S v1, v2}) with "Gfs") as "(Gfs& Gf)".
    iMod (glG_owner_update _ _ t with "Gok") as "[Go Gok]". iDestruct "Gok" as "[Go' Gok]".
    iCombine "Go Go'" as "Go".
    iPoseProof (glG_version_get_lb _ _ v2 with "Gv") as "#Gvl2"; first auto.
    iAssert ([∗ set] u ∈ (set_seq (S v1) (v2 - v1 - 1)), glG_version_lb k u)%I with "[]" as "#Glvs".
    { iClear "Gwf Gu Ge Gvl Gus". replace (v2 - v1 - 1) with δ by lia.
      remember (S v1) as v. assert (v + δ ≤ v2) by lia. clear dependent v1.
      iStopProof. revert v H. induction δ; iIntros "% % #Glv".
      { done. }
      rewrite !set_seq_S_end_union_L. rewrite !big_sepS_union.
      2: apply set_seq_S_end_disjoint.
      rewrite !big_sepS_singleton. assert (v + δ ≤ v2) by lia.
      iPoseProof (glG_version_lb_mon _ _ (v + δ) with "Glv") as "#Glv2"; first auto.
      iFrame "Glv2". iPoseProof (IHδ with "Glv") as "$". auto.
    }
    iModIntro. iFrame "Gl Gv Gf Go".
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (v2, gl_locked (Σ[ξ] v2) t)) with "[HM VS VSa Gl2 Gvk Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". replace (S v1 + (v2 - v1)) with (S v2) by lia. iFrame. iFrame "Gvl2 Gwf".
      iSplitL.
      - replace (set_seq 0 v2) with (set_seq 0 ((S v1) + (v2 - v1 - 1)) : gset gl_version); cycle 1.
        { replace ((S v1) + (v2 - v1 - 1)) with v2 by lia. done. }
        rewrite (set_seq_add_L _ (S v1)). iApply big_sepS_union.
        { apply set_seq_add_disjoint. }
        rewrite !big_sepS_sep. iDestruct "VS" as "[VS1 VS2]". iFrame "Gus Glvs".
        rewrite !set_seq_S_end_union_L. rewrite !big_sepS_union.
        2,3: apply set_seq_S_end_disjoint.
        rewrite !big_sepS_singleton. iFrame. auto.
      - iPureIntro. split.
        all: etrans; last (rewrite gl_witness_sum_gen_sum_equiv_add; first reflexivity).
        2,4: eapply LTv.
        all: eapply OCM.add_le_proper; done.
    }
    rewrite dom_insert_lookup_L; last done. iFrame "HE HS HV HF HO".
    rewrite insert_delete_eq. iFrame. iSplitL.
    { iApply big_sepS_sep; eauto. }
    iPureIntro. econstructor. auto.
  Qed.

  (** Rules for glG_variant and glsat *)
  Lemma glsat_variant_acc_locked Ω k v q0 q1 E N P Q R :
    ↑N ⊆ E →
    glG_variant N k v q0 P Q R ∗
    glsat Ω ∗ glG_elem k ∗ glG_locked k v q1
    ⊢ |={E,E ∖ ↑N}=>
          ▷ (glsat Ω ∗ glG_locked k v q1 ∗ (glG_locked k v q0 ∗ P)) ∗
          (▷ glG_variant_internal k v q0 P Q R ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "(#Gvar& G& #Ge& Gl)".
    iMod (glG_variant_acc with "Gvar") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC".
      + iNext. iDestruct "H" as "[H | H]"; first iFrame.
        iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$Gl $H]") as "%". done.
      + done.
    - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "[#Gvd _]".
      iPoseProof (glsat_lookup_version_done with "[$G $Ge $Gvd]") as "%". destruct H as (?&?&?&?).
      iPoseProof (glsat_lookup_locked with "[$G $Ge $Gl]") as "%". destruct H1 as (?&?&?).
      rewrite H in H1. inv H1. lia.
  Qed.

  Lemma glsat_variant_unlock Ω k v t q0 q1 E N P Q R :
    (q0 + q1 = 1/2 + 1/2/2)%Qp →
    ↑N ⊆ E →
    glG_variant N k v q0 P Q R ∗
    glsat Ω ∗
    glG_elem k ∗ glG_locked k v q1 ∗ glG_owner k t (1/2 + 1/2/2)%Qp
    ⊢ |={E,E ∖ ↑N}=>
          ▷ ((glsat Ω ∗ glG_locked k v (1/2 + 1/2/2)%Qp ∗ glG_owner k t (1/2 + 1/2/2)%Qp ∗ P) ∗
             ((glsat Ω ∗ glG_locked k v (1/2 + 1/2/2)%Qp ∗ glG_owner k t (1/2 + 1/2/2)%Qp ∗ ▷ Q)
              ={E ∖ ↑N,E}=∗
              glsat (<[k:=(v, gl_unlocked)]>Ω) ∗
              glG_unlocked k v ∗
              (⌜ ∀ a, ghost_lock_step (v, gl_locked a t) (v, gl_unlocked) ⌝))).
  Proof.
    iIntros (Hq HE) "(#Gvar& G& #Ge& Gl& Go)".
    iMod (glsat_variant_acc_locked with "[$Gvar $G $Ge $Gl]") as "[H ACC]"; first auto.
    iModIntro. iNext. iDestruct "H" as "($& Gl1& Gl2& $)".
    iCombine "Gl2 Gl1" as "Gl". rewrite Hq. iFrame "Gl Go".
    iIntros "(G& Gl& Go& HQ)".
    iMod (glsat_unlock with "[$G $Ge $Gl $Go]") as "($& #Gu& $)". iFrame "Gu".
    iApply "ACC". iNext. iLeft. iRight. iFrame. eauto.
  Qed.

  Lemma glsat_variant_lock Ω k ξ v1 v2 t q0 q1 E N P Q R :
    (q0 + q1 = 1/2 + 1/2/2)%Qp →
    v1 < v2 →
    ↑N ⊆ E →
    glG_variant N k v1 q0 P Q R ∗
    glsat Ω ∗
    glG_witfun k ξ ∗ glG_unlocked k v1 ∗ glG_version k v1 (1/2 + 1/2/2)%Qp
    ⊢ |={E,E ∖ ↑N}=>
          ▷ ((glsat Ω ∗ glG_version k v1 (1/2 + 1/2/2)%Qp ∗ Q) ∗
             ((glsat Ω ∗ glG_version k v1 (1/2 + 1/2/2)%Qp ∗ (▷ R) ∗ (▷ P))
              ={E ∖ ↑N,E}=∗
              glsat (<[k:=(v2, gl_locked (Σ[ξ] v2) t)]>Ω) ∗
              glG_locked k v2 q1 ∗
              glG_version k v2 (1/2 + 1/2/2)%Qp ∗
              glG_fuel k (Σ[ξ]{S v1, v2}) ∗
              glG_owner k t (1/2 + 1/2/2)%Qp ∗
              ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u) ∗
              (⌜ ghost_lock_step (v1, gl_unlocked) (v2, gl_locked (Σ[ξ] v2) t) ⌝) ∗
              glG_variant N k v2 q0 P Q R)).
  Proof.
    iIntros (Hq Hv HE) "(#Gvar& G& #Gwf& #Gu& Gv)".
    iPoseProof (glG_witfun_elem with "Gwf") as "#Ge".
    iMod (glG_variant_acc_unlocked with "Gvar Gu") as "[H ACC]"; first auto.
    iModIntro. iNext. iDestruct "H" as "[$ | [#Gvd _]]"; cycle 1.
    { iPoseProof (glG_version_done_valid with "[$Gv $Gvd]") as "%". lia. }
    iFrame "G Gv". iIntros "(G& Gv& HR& HP)".
    iMod (glsat_lock _ _ _ v1 v2 t with "[$G $Gwf $Gu $Gv]") as "($& Gl& Gv& $& $& #Gus& $)"; first auto.
    iPoseProof (glG_version_get_lb _ _ v2 with "Gv") as "#Gvl"; first lia.
    iPoseProof (glG_version_get_done _ _ v1 with "Gvl") as "#Gvd"; first lia.
    iFrame "Gv".
    rewrite -!Hq. iDestruct "Gl" as "[Gl1 Gl2]". iFrame "Gl2 Gus".
    iMod ("ACC" with "[HR]") as "_".
    { iNext. iRight. iFrame. auto. }
    iApply glG_variant_alloc_locked. iFrame.
  Qed.

End glsat.

(* Allocation of an initial obligation protocol. *)
Lemma glsat_alloc `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGpreS Σ} :
  ⊢ |==> ∃ _ : glsatGS Σ, glsat ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR gl_id (agreeR (leibnizO gl_witness)))) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=reservation_mapUR (dfrac_agreeR natO)) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=auth_mraUR le) ⊤)) as (γV) "HV";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bankUR) ⊤)) as (γF) "HF";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=dfrac_agreeR (leibnizO gl_owner)) ⊤)) as (γO) "HO";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (GlsatG SI GL _ _ γE γS γV γF γO).
  rewrite /glsat -lock.
  iSplitL "HE".
  { iExists ∅. iFrame. done. }
  replace (⊤ ∖ gset_to_coPset (dom (∅ : ghost_locks))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
