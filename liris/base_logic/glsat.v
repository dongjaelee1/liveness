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
        glsatGpreS_elem : inG Σ (gmap_viewR gl_id unitUR);
        glsatGpreS_state : inG Σ (reservation_mapUR (dfrac_agreeR natO));
        glsatGpreS_version : inG Σ (reservation_mapUR (auth_mraUR glv_le));
        glsatGpreS_fuel : inG Σ (reservation_mapUR (reservation_mapUR bankUR));
        (* We keep track of current owner for each lock, if the owner exists *)
        glsatGpreS_owner : inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO gl_owner)));
      }.

  Class glsatGS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set :=
    GlsatG {
        glsat_inG : glsatGpreS Σ;
        elem_name : gname;
        state_name : gname;
        version_name : gname;
        fuel_name : gname;
        owner_name : gname;
      }.

  Definition glsatΣ `{SI : indexT} `{GL : ghost_lock_class} : gFunctors :=
    #[GFunctor (gmap_viewR gl_id unitUR);
      GFunctor (reservation_mapUR (dfrac_agreeR $ natO));
      GFunctor (reservation_mapUR (auth_mraUR glv_le));
      GFunctor (reservation_mapUR (reservation_mapUR bankUR));
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
  glsatGpreS_elem glsatGpreS_state glsatGpreS_version glsatGpreS_fuel glsatGpreS_owner.

(* Elem *)
Definition glG_elem `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) : iProp Σ :=
  own elem_name (gmap_view_frag k DfracDiscarded ()).
Global Typeclasses Opaque glG_elem.
Global Instance: Params (@glG_elem) 5 := {}.

Local Definition glG_elem_auth_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (m : gmap gl_id unit) : iProp Σ :=
  own elem_name (gmap_view_auth (V:=unitUR) (DfracOwn 1) m).

(* State: locked or unlocked *)
Definition glG_locked `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data k (to_dfrac_agree (DfracOwn q) 0)).
Global Typeclasses Opaque glG_locked.
Global Instance: Params (@glG_locked) 5 := {}.

Definition glG_unlocked `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data k (to_dfrac_agree (DfracOwn q) 1)).
Global Typeclasses Opaque glG_unlocked.
Global Instance: Params (@glG_unlocked) 5 := {}.

Definition glG_done `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) : iProp Σ :=
  own state_name (reservation_map_data k (to_dfrac_agree (DfracDiscarded) 2)).
Global Typeclasses Opaque glG_done.
Global Instance: Params (@glG_done) 5 := {}.

Local Definition glG_state_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own state_name (reservation_map_token (A:=dfrac_agreeR natO) E).

(* Version: tracks the version *)
Definition glG_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (q : Qp) : iProp Σ :=
  own version_name (reservation_map_data k (●AM{#q}[glv_le] v)).
Global Typeclasses Opaque glG_version.
Global Instance: Params (@glG_version) 5 := {}.

Definition glG_version_lb `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own version_name (reservation_map_data k (◯AM[glv_le] v)).
Global Typeclasses Opaque glG_version_lb.
Global Instance: Params (@glG_version_lb) 5 := {}.

Definition glG_version_pin `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own version_name (reservation_map_data k (●AM□[glv_le] v)).
Global Typeclasses Opaque glG_version_pin.
Global Instance: Params (@glG_version_pin) 5 := {}.

Local Definition glG_version_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own version_name (reservation_map_token (A:=auth_mraUR glv_le) E).

(* Fuel: manage credits for a lock's fuel *)
Definition glG_fuel `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (a : gl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data k (reservation_map_data (A:=bankUR) v (cash a))).
Global Typeclasses Opaque glG_fuel.
Global Instance: Params (@glG_fuel) 5 := {}.

Definition glG_fuel_supply `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (a : gl_fuel) (q : Qp) : iProp Σ :=
  own fuel_name (reservation_map_data k (reservation_map_data (A:=bankUR) v (debt a q))).
Global Typeclasses Opaque glG_fuel_supply.
Global Instance: Params (@glG_fuel_supply) 5 := {}.

Local Definition glG_fuel_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_token (A:=reservation_mapUR bankUR) E).
Local Definition glG_fuel_token_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_data k (reservation_map_token (A:=bankUR) E)).

(* Owner: tracks the owner thread of a lock *)
Definition glG_owner `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (t : gl_owner) (q : Qp) : iProp Σ :=
  own owner_name (reservation_map_data k (to_frac_agree q (t : leibnizO gl_owner))).
Global Typeclasses Opaque glG_owner.
Global Instance: Params (@glG_owner) 5 := {}.

Local Definition glG_owner_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO gl_owner)) E).

(* P Until Q: internal model. Three cases:
   1. locked at version v with P
   2. unlocked at version v with Q
   3. version v expired
   WP ensures that when unlocking, glG_unlocked is visited at least once
 *)
Definition glG_until_internal `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (q : Qp) (P Q : iProp Σ) : iProp Σ :=
  (((glG_locked k q ∗ glG_version k v q ∗ P) ∨
      (glG_unlocked k q ∗ glG_version k v q ∗ Q)) ∨
     (∃ v', (⌜ (v < v')%positive ⌝) ∗ glG_version_lb k v')).

Definition glG_until `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ}
  (N : namespace) (k : gl_id) (v : gl_version) (q : Qp) (P Q : iProp Σ) : iProp Σ :=
  inv N (glG_until_internal k v q P Q).

Definition glG_always `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ}
  (N : namespace) (k : gl_id) (v : gl_version) (P : iProp Σ) : iProp Σ :=
  glG_done k ∗ glG_version_pin k v ∗ inv N P.

(* Global protocol for ghost locks. *)
Definition glsat `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ}
  (Ω : ghost_locks) : iProp Σ :=
  locked
    (glG_elem_auth_id (gset_to_gmap () (dom Ω)) ∗
     glG_state_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     glG_version_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     glG_fuel_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     glG_owner_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     ([∗ map] k ↦ '(v, g) ∈ Ω,
        glG_elem k ∗
        ∃ (vs : gset gl_version),
          glG_fuel_token_version k (⊤ ∖ gset_to_coPset vs) ∗
          ([∗ set] ve ∈ vs, ⌜ glv_le ve v ⌝ ∗ glG_version_lb k ve) ∗
          (** Ghost lock is active: locked or unlocked, or retired: unlocked and pinned *)
          match g with
          | gl_locked a t =>
              glG_locked k (1/2/2)%Qp ∗ glG_version k v (1/2/2)%Qp ∗
              (∃ α, (⌜ WFOCM.leR α a ⌝) ∗ glG_fuel_supply k v α (1)%Qp) ∗
              glG_owner k t (1/2/2)%Qp
          | gl_unlocked =>
              ((glG_unlocked k (1/2/2)%Qp ∗ glG_version k v (1/2/2)%Qp) ∨
                 (glG_done k ∗ glG_version_pin k v)) ∗
              (∃ α, glG_fuel_supply k v α (1)%Qp) ∗
              (∃ t, glG_owner k t (1)%Qp)
          end))%I.


(* OLD *)

(* (** The ghost state for ghost locks *) *)
(* Module glsatGS. *)

(*   Class glsatGpreS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set := *)
(*     GlsatGpreS { *)
(*         glsatGpreS_elem : *)
(*         inG Σ (gmap_viewR gl_id unitUR); *)
(*         glsatGpreS_holds : *)
(*         inG Σ (gmap_viewR gl_id (prodR (agreeR $ (laterO (iPropO Σ))) (agreeR $ (laterO (iPropO Σ))))); *)
(*         glsatGpreS_state : *)
(*         inG Σ (reservation_mapUR (dfrac_agreeR natO)); *)
(*         glsatGpreS_version : *)
(*         inG Σ (reservation_mapUR (auth_mraUR glv_le)); *)
(*         glsatGpreS_fuel : *)
(*         inG Σ (reservation_mapUR (reservation_mapUR bankUR)); *)
(*         (* We keep track of current owner for each lock, if the owner exists *) *)
(*         glsatGpreS_owner : *)
(*         inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO gl_owner))); *)
(*       }. *)

(*   (* Class glsatGpreS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set := *) *)
(*   (*   GlsatGpreS { *) *)
(*   (*       glsatGpreS_elem : *) *)
(*   (*       inG Σ (gmap_viewR gl_id (gmap_viewR gl_version unitUR)); *) *)
(*   (*       glsatGpreS_holds : *) *)
(*   (*       inG Σ (gmap_viewR gl_id (gmap_viewR gl_version (prodR (agreeR $ (laterO (iPropO Σ))) (agreeR $ (laterO (iPropO Σ)))))); *) *)
(*   (*       (* Use encode of Countable to encode gl_version to positive *) *) *)
(*   (*       glsatGpreS_state : *) *)
(*   (*       inG Σ (reservation_mapUR (reservation_mapUR mono_natUR)); *) *)
(*   (*       glsatGpreS_version : *) *)
(*   (*       inG Σ (reservation_mapUR (auth_mraUR glv_le)); *) *)
(*   (*       glsatGpreS_fuel : *) *)
(*   (*       inG Σ (reservation_mapUR (reservation_mapUR bankUR)); *) *)
(*   (*       (* We only keep track of current owner for each lock, if the owner exists *) *) *)
(*   (*       glsatGpreS_owner : *) *)
(*   (*       inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO gl_owner))); *) *)
(*   (*     }. *) *)

(*   Class glsatGS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set := *)
(*     GlsatG { *)
(*         glsat_inG : glsatGpreS Σ; *)
(*         elem_name : gname; *)
(*         holds_name : gname; *)
(*         state_name : gname; *)
(*         version_name : gname; *)
(*         fuel_name : gname; *)
(*         owner_name : gname; *)
(*       }. *)

(*   Definition glsatΣ `{SI : indexT} `{GL : ghost_lock_class} : gFunctors := *)
(*     #[GFunctor (gmap_viewR gl_id unitUR); *)
(*       GFunctor (gmap_viewTRF gl_id (prodTRF (agreeTRF $ (laterTF idTF)) (agreeTRF $ (laterTF idTF)))); *)
(*       GFunctor (reservation_mapUR (dfrac_agreeR $ natO)); *)
(*       GFunctor (reservation_mapUR (auth_mraUR glv_le)); *)
(*       GFunctor (reservation_mapUR (reservation_mapUR bankUR)); *)
(*       GFunctor (reservation_mapUR (dfrac_agreeR $ (leibnizO gl_owner))) *)
(*       ]. *)

(*   (* Definition glsatΣ `{SI : indexT} `{GL : ghost_lock_class} : gFunctors := *) *)
(*   (*   #[GFunctor (gmap_viewR gl_id (gmap_viewR gl_version unitUR)); *) *)
(*   (*     GFunctor (gmap_viewTRF gl_id (gmap_viewTRF gl_version (prodTRF (agreeTRF $ (laterTF idTF)) (agreeTRF $ (laterTF idTF))))); *) *)
(*   (*     GFunctor (reservation_mapUR (reservation_mapUR mono_natUR)); *) *)
(*   (*     GFunctor (reservation_mapUR (auth_mraUR glv_le)); *) *)
(*   (*     GFunctor (reservation_mapUR (reservation_mapUR bankUR)); *) *)
(*   (*     GFunctor (reservation_mapUR (dfrac_agreeR $ (leibnizO gl_owner))) *) *)
(*   (*     ]. *) *)

(*   Global Instance subG_glsatΣ `{SI : indexT} `{GL : ghost_lock_class} {Σ} : subG (glsatΣ) Σ → (glsatGpreS Σ). *)
(*   Proof. solve_inG. Qed. *)

(* End glsatGS. *)
(* Import glsatGS. *)

(* (** User interface *) *)
(* (* Make the instances local to this file. We cannot use #[local] in the code *) *)
(* (* above, as that would make the instances local to the module. *) *)
(* Local Existing Instances glsat_inG *)
(*   glsatGpreS_elem glsatGpreS_holds glsatGpreS_state glsatGpreS_version glsatGpreS_fuel glsatGpreS_owner. *)

(* (* Elem *) *)
(* Definition glG_elem `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) : iProp Σ := *)
(*   own elem_name (gmap_view_frag k DfracDiscarded ()). *)
(* Global Typeclasses Opaque glG_elem. *)
(* Global Instance: Params (@glG_elem) 5 := {}. *)

(* Local Definition glG_elem_auth_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (m : gmap gl_id unit) : iProp Σ := *)
(*   own elem_name (gmap_view_auth (V:=unitUR) (DfracOwn 1) m). *)

(* (* Holds: P until Q *) *)
(* Definition holds_unfold `{SI : indexT} {Σ} (P : iProp Σ) : later (iProp Σ) := Next P. *)
(* Global Instance: Params (@holds_unfold) 2 := {}. *)

(* Definition glG_holds `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (P : iProp Σ) (Q : iProp Σ) : iProp Σ := *)
(*   own holds_name (gmap_view_frag k DfracDiscarded (to_agree $ holds_unfold P, to_agree $ holds_unfold Q)). *)
(* Global Typeclasses Opaque glG_holds. *)
(* Global Instance: Params (@glG_holds) 5 := {}. *)

(* Local Definition glG_holds_auth_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (m : gmap gl_id (iPropO Σ * iPropO Σ)) : iProp Σ := *)
(*   own holds_name (gmap_view_auth (V:=(prodR (agreeR $ (laterO (iPropO Σ))) (agreeR $ (laterO (iPropO Σ))))) *)
(*                     (DfracOwn 1) ((λ '(P, Q), (to_agree $ (holds_unfold P), to_agree $ (holds_unfold Q))) <$> m)). *)

(* (* State: locked or unlocked *) *)
(* Definition glG_locked `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (q : Qp) : iProp Σ := *)
(*   own state_name (reservation_map_data k (to_dfrac_agree (DfracOwn q) 0)). *)
(* Global Typeclasses Opaque glG_locked. *)
(* Global Instance: Params (@glG_locked) 5 := {}. *)

(* Definition glG_unlocked `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (q : Qp) : iProp Σ := *)
(*   own state_name (reservation_map_data k (to_dfrac_agree (DfracOwn q) 1)). *)
(* Global Typeclasses Opaque glG_unlocked. *)
(* Global Instance: Params (@glG_unlocked) 5 := {}. *)

(* Definition glG_done `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) : iProp Σ := *)
(*   own state_name (reservation_map_data k (to_dfrac_agree (DfracDiscarded) 1)). *)
(* Global Typeclasses Opaque glG_done. *)
(* Global Instance: Params (@glG_done) 5 := {}. *)

(* Local Definition glG_state_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (E : coPset) : iProp Σ := *)
(*   own state_name (reservation_map_token (A:=dfrac_agreeR natO) E). *)

(* (* Version: tracks the version *) *)
(* Definition glG_version_lb `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (v : gl_version) : iProp Σ := *)
(*   own version_name (reservation_map_data k (◯AM[glv_le] v)). *)
(* Global Typeclasses Opaque glG_version_lb. *)
(* Global Instance: Params (@glG_version_lb) 5 := {}. *)

(* Definition glG_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (v : gl_version) : iProp Σ := *)
(*   own version_name (reservation_map_data k (●AM[glv_le] v)). *)
(* Global Typeclasses Opaque glG_version. *)
(* Global Instance: Params (@glG_version) 5 := {}. *)

(* Definition glG_version_pin `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (v : gl_version) : iProp Σ := *)
(*   own version_name (reservation_map_data k (●AM□[glv_le] v)). *)
(* Global Typeclasses Opaque glG_version_pin. *)
(* Global Instance: Params (@glG_version_pin) 5 := {}. *)

(* Local Definition glG_version_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (E : coPset) : iProp Σ := *)
(*   own version_name (reservation_map_token (A:=auth_mraUR glv_le) E). *)

(* (* Fuel: manage credits for a lock's fuel *) *)
(* Definition glG_fuel `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (v : gl_version) (a : gl_fuel) : iProp Σ := *)
(*   own fuel_name (reservation_map_data k (reservation_map_data (A:=bankUR) (encode v) (cash a))). *)
(* Global Typeclasses Opaque glG_fuel. *)
(* Global Instance: Params (@glG_fuel) 5 := {}. *)

(* Definition glG_fuel_supply `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (v : gl_version) (a : gl_fuel) (q : Qp) : iProp Σ := *)
(*   own fuel_name (reservation_map_data k (reservation_map_data (A:=bankUR) (encode v) (debt a q))). *)
(* Global Typeclasses Opaque glG_fuel_supply. *)
(* Global Instance: Params (@glG_fuel_supply) 5 := {}. *)

(* Local Definition glG_fuel_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (E : coPset) : iProp Σ := *)
(*   own fuel_name (reservation_map_token (A:=reservation_mapUR bankUR) E). *)
(* Local Definition glG_fuel_token_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (E : coPset) : iProp Σ := *)
(*   own fuel_name (reservation_map_data k (reservation_map_token (A:=bankUR) E)). *)

(* (* Owner: tracks the owner thread of a lock *) *)
(* Definition glG_owner `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (k : gl_id) (t : gl_owner) (q : Qp) : iProp Σ := *)
(*   own owner_name (reservation_map_data k (to_frac_agree q (t : leibnizO gl_owner))). *)
(* Global Typeclasses Opaque glG_owner. *)
(* Global Instance: Params (@glG_owner) 5 := {}. *)

(* Local Definition glG_owner_token `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} *)
(*   (E : coPset) : iProp Σ := *)
(*   own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO gl_owner)) E). *)

(** Properties *)
Section glsat.
  Context `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ}.

  (** Instances *)
  (* Elem *)
  Global Instance glG_elem_persistent k : Persistent (glG_elem k).
  Proof. rewrite /glG_elem. apply _. Qed.

  Global Instance glG_elem_timeless k : Timeless (glG_elem k).
  Proof. rewrite /glG_elem. apply _. Qed.

  Local Instance glG_elem_auth_id_timeless m : Timeless (glG_elem_auth_id m).
  Proof. rewrite /glG_elem_auth_id. apply _. Qed.

  (* State *)
  Global Instance glG_done_persistent k : Persistent (glG_done k).
  Proof. rewrite /glG_done. apply _. Qed.

  Global Instance glG_locked_timeless k q : Timeless (glG_locked k q).
  Proof. rewrite /glG_locked. apply _. Qed.
  Global Instance glG_unlocked_timeless k q : Timeless (glG_unlocked k q).
  Proof. rewrite /glG_unlocked. apply _. Qed.
  Global Instance glG_done_timeless k : Timeless (glG_done k).
  Proof. rewrite /glG_done. apply _. Qed.

  Global Instance glG_locked_fractional k :
    Fractional (glG_locked k).
  Proof.
    rewrite /glG_locked. intros p q. by rewrite -own_op -reservation_map_data_op -dfrac_agree_op.
  Qed.
  Global Instance glG_locked_as_fractional k q :
    AsFractional (glG_locked k q) (glG_locked k) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance glG_unlocked_fractional k :
    Fractional (glG_unlocked k).
  Proof.
    rewrite /glG_unlocked. intros p q. by rewrite -own_op -reservation_map_data_op -dfrac_agree_op.
  Qed.
  Global Instance glG_unlocked_as_fractional k q :
    AsFractional (glG_unlocked k q) (glG_unlocked k) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance glG_state_token_id_timeless E : Timeless (glG_state_token_id E).
  Proof. rewrite /glG_state_token_id. apply _. Qed.

  (* Version *)
  Global Instance glG_version_lb_persistent k v : Persistent (glG_version_lb k v).
  Proof. rewrite /glG_version_lb. apply _. Qed.
  Global Instance glG_version_pin_persistent k v : Persistent (glG_version_pin k v).
  Proof. rewrite /glG_version_pin. apply _. Qed.

  Global Instance glG_version_timeless k v q : Timeless (glG_version k v q).
  Proof. rewrite /glG_version. apply _. Qed.
  Global Instance glG_version_lb_timeless k v : Timeless (glG_version_lb k v).
  Proof. rewrite /glG_version_lb. apply _. Qed.
  Global Instance glG_version_pin_timeless k v : Timeless (glG_version_pin k v).
  Proof. rewrite /glG_version_pin. apply _. Qed.

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
  Global Instance glG_fuel_timeless k v a : Timeless (glG_fuel k v a).
  Proof. rewrite /glG_fuel. apply _. Qed.
  Global Instance glG_fuel_supply_timeless k v a q : Timeless (glG_fuel_supply k v a q).
  Proof. rewrite /glG_fuel_supply. apply _. Qed.

  Global Instance glG_fuel_supply_fractional k v a :
    Fractional (glG_fuel_supply k v a).
  Proof.
    rewrite /glG_fuel_supply. intros p q. by rewrite -own_op -!reservation_map_data_op debt_split.
  Qed.
  Global Instance glG_fuel_supply_as_fractional k v a q :
    AsFractional (glG_fuel_supply k v a q) (glG_fuel_supply k v a) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance glG_fuel_token_id_timeless E : Timeless (glG_fuel_token_id E).
  Proof. rewrite /glG_fuel_token_id. apply _. Qed.
  Local Instance glG_fuel_token_version_timeless k E : Timeless (glG_fuel_token_version k E).
  Proof. rewrite /glG_fuel_token_version. apply _. Qed.

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

  (* Until and Always *)
  Global Instance glG_until_contractive_1 N k v q P : Contractive (λ Q, @glG_until SI _ Σ _ _ N k v q P Q).
  Proof. rewrite /glG_until /glG_until_internal. solve_contractive. Qed.
  Global Instance glG_until_contractive_2 N k v q Q : Contractive (λ P, @glG_until SI _ Σ _ _ N k v q P Q).
  Proof. rewrite /glG_until /glG_until_internal. solve_contractive. Qed.

  Global Instance glG_until_persistent N k v q P Q : Persistent (glG_until N k v q P Q).
  Proof. apply _. Qed.

  Global Instance glG_always_contractive N k v : Contractive (λ P, glG_always N k v P).
  Proof. rewrite /glG_always. solve_contractive. Qed.

  Global Instance glG_always_persistent N k v P : Persistent (glG_always N k v P).
  Proof. apply _. Qed.

  (* Sat *)
  Global Instance glsat_timeless Ω : Timeless (glsat Ω).
  Proof. rewrite /glsat -lock. apply _. Qed.

  (** Rules *)
  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

  (** Elem rules *)
  Lemma glG_elem_elem k (Ω : ghost_locks) :
    glG_elem_auth_id (gset_to_gmap () (dom Ω)) ∗
    glG_elem k
    ⊢ ⌜ k ∈ dom Ω ⌝.
  Proof.
    rewrite /glG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro.
    apply lookup_gset_to_gmap_Some in H. by destruct H.
  Qed.

  Lemma glG_elem_alloc (Ω : ghost_locks) k g :
    Ω !! k = None →
    glG_elem_auth_id (gset_to_gmap () (dom Ω))
    ⊢ |==> glG_elem_auth_id (gset_to_gmap () (dom (<[k:=g]>Ω))) ∗
        glG_elem k.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ k (DfracDiscarded) ()); try done.
      by apply lookup_gset_to_gmap_None, not_elem_of_dom.
    }
    iDestruct "H" as "[H He]". rewrite /glG_elem. iFrame "He".
    rewrite dom_insert_L gset_to_gmap_union_singleton. done.
  Qed.

  (** State rules *)
  Lemma glG_locked_to_unlocked_2 k q1 q2 :
    (q1 + q2 = 1)%Qp →
    glG_locked k q1 ∗ glG_locked k q2 ⊢ |==> glG_unlocked k q1 ∗ glG_unlocked k q2.
  Proof.
    rewrite /glG_locked /glG_unlocked -!own_op -!reservation_map_data_op.
    intros Heq. by apply own_update, reservation_map_update, frac_agree_update_2.
  Qed.
  Lemma glG_unlocked_to_done_2 k q1 q2 :
    (q1 + q2 = 1)%Qp →
    glG_unlocked k q1 ∗ glG_unlocked k q2 ⊢ |==> glG_done k.
  Proof.
    rewrite /glG_unlocked /glG_done -!own_op -!reservation_map_data_op.
    intros Heq. apply own_update, reservation_map_update. etrans.
    - by apply frac_agree_update_2.
    - rewrite -frac_agree_op. apply dfrac_agree_persist.
  Qed.

  Lemma glG_locked_frac_valid k q :
    glG_locked k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_locked. iIntros "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    by iApply (frac_agree_validI).
  Qed.
  Lemma glG_unlocked_frac_valid k q :
    glG_unlocked k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_unlocked. iIntros "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    by iApply (frac_agree_validI).
  Qed.

  Lemma glG_locked_unlocked_false k q1 q2 :
    glG_locked k q1 ∗ glG_unlocked k q2 ⊢ False.
  Proof.
    rewrite /glG_locked /glG_unlocked. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply dfrac_agree_op_valid in V. destruct V. done.
  Qed.
  Lemma glG_locked_done_false k q :
    glG_locked k q ∗ glG_done k ⊢ False.
  Proof.
    rewrite /glG_locked /glG_done. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply dfrac_agree_op_valid in V. destruct V. done.
  Qed.
  Lemma glG_unlocked_done_false k q :
    glG_unlocked k q ∗ glG_done k ⊢ False.
  Proof.
    rewrite /glG_unlocked /glG_done. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply dfrac_agree_op_valid in V. destruct V. done.
  Qed.

  Lemma glG_locked_alloc D k :
    k ∉ D →
    glG_state_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_state_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        glG_locked k 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (to_dfrac_agree (DfracOwn 1) 0) with "Htk") as "[Htk >H]"; auto.
    { done. }
    rewrite /glG_locked. by iFrame.
  Qed.

  (** Version rules *)
  Lemma glG_version_update_mon k v1 v2 :
    (v1 ≤ v2)%positive →
    glG_version k v1 1 ⊢ |==> glG_version k v2 1.
  Proof.
    rewrite /glG_version /glv_le. intros Hle.
    apply own_update, reservation_map_update, auth_mra_update; eauto.
    apply _.
  Qed.
  Lemma glG_version_update_pin k v q :
    glG_version k v q ⊢ |==> glG_version_pin k v.
  Proof.
    rewrite /glG_version /glG_version_pin.
    apply own_update, reservation_map_update, auth_mra_auth_persist; eauto.
  Qed.

  Lemma glG_version_lb_mon k v1 v2 :
    (v2 ≤ v1)%positive →
    glG_version_lb k v1 ⊢ glG_version_lb k v2.
  Proof.
    rewrite /glG_version_lb. iIntros (Hle) "H". rewrite (auth_mra_know_op _ v2 v1); auto.
    iDestruct "H" as "[H1 H2]". done.
  Qed.

  Lemma glG_version_get_lb_eq k v q :
    glG_version k v q ⊢ glG_version_lb k v.
  Proof.
    rewrite /glG_version /glG_version_lb.
    rewrite auth_mra_auth_know_op.
    rewrite reservation_map_data_op own_op. iIntros "[_ $]".
  Qed.
  Lemma glG_version_get_lb k v1 v2 q :
    (v2 ≤ v1)%positive →
    glG_version k v1 q ⊢ glG_version_lb k v2.
  Proof.
    iIntros (Hle) "GLV". iPoseProof (glG_version_get_lb_eq with "GLV") as "#GLVL".
    iApply (glG_version_lb_mon with "GLVL"). done.
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
    - destruct Hv. apply leibniz_equiv in H0. done.
    - repeat intro. eapply Pos.le_antisym; eauto.
  Qed.
  Lemma glG_version_lb_lb k q v1 v2 :
    glG_version k v1 q ∗ glG_version_lb k v2 ⊢ ⌜ (v2 ≤ v1)%positive ⌝.
  Proof.
    rewrite /glG_version /glG_version_lb /glv_le. rewrite -own_op -reservation_map_data_op.
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
    - repeat intro. eapply Pos.le_antisym; eauto.
  Qed.

  Lemma glG_version_alloc D k v :
    k ∉ D →
    glG_version_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_version_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        glG_version k v 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●AM[glv_le] v) with "Htk") as "[Htk >H]"; auto.
    { apply auth_mra_auth_valid. }
    rewrite /glG_version. by iFrame.
  Qed.

  (** Fuel rules *)
  Lemma glG_fuel_eq k v a0 a1 :
    a0 /= a1 →
    glG_fuel k v a0 = glG_fuel k v a1.
  Proof. intros EQ. rewrite /glG_fuel. by erewrite cash_eq. Qed.
  Lemma glG_fuel_eq_list L v a0 a1 :
    a0 /= a1 →
    ([∗ list] k ∈ L, glG_fuel k v a0)%I ≡ ([∗ list] k ∈ L, glG_fuel k v a1)%I.
  Proof. intros. apply big_opL_proper. intros. erewrite glG_fuel_eq; eauto. Qed.
  Lemma glG_fuel_eq_set L v a0 a1 :
    a0 /= a1 →
    ([∗ set] k ∈ L, glG_fuel k v a0)%I ≡ ([∗ set] k ∈ L, glG_fuel k v a1)%I.
  Proof. intros. apply big_opS_proper. intros. erewrite glG_fuel_eq; eauto. Qed.

  Lemma glG_fuel_mon k v a0 a1 :
    a0 /≤ a1 →
    glG_fuel k v a1 ⊢ |==> glG_fuel k v a0.
  Proof.
    intros LE. rewrite /glG_fuel. apply own_update.
    by apply reservation_map_update, reservation_map_update, cash_update.
  Qed.
  Lemma glG_fuel_mon_list L v a0 a1 :
    a0 /≤ a1 →
    ([∗ list] k ∈ L, glG_fuel k v a1) ⊢ |==> ([∗ list] k ∈ L, glG_fuel k v a0).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_mon.
  Qed.
  Lemma glG_fuel_mon_set L v a0 a1 :
    a0 /≤ a1 →
    ([∗ set] k ∈ L, glG_fuel k v a1) ⊢ |==> ([∗ set] k ∈ L, glG_fuel k v a0).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_mon.
  Qed.

  Lemma glG_fuel_split k v a0 a1 :
    glG_fuel k v (a0 /+ a1) ⊣⊢ glG_fuel k v a0 ∗ glG_fuel k v a1.
  Proof.
    rewrite /glG_fuel. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -cash_add) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite -cash_add). iSplitL "H1"; iFrame.
  Qed.
  Lemma glG_fuel_split_list L v a0 a1 :
    ([∗ list] k ∈ L, glG_fuel k v (a0 /+ a1)) ⊣⊢ ([∗ list] k ∈ L, glG_fuel k v a0) ∗ ([∗ list] k ∈ L, glG_fuel k v a1).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply glG_fuel_split.
  Qed.
  Lemma glG_fuel_split_set L v a0 a1 :
    ([∗ set] k ∈ L, glG_fuel k v (a0 /+ a1)) ⊣⊢ ([∗ set] k ∈ L, glG_fuel k v a0) ∗ ([∗ set] k ∈ L, glG_fuel k v a1).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply glG_fuel_split.
  Qed.

  Lemma glG_fuel_mon_split k v a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    glG_fuel k v a2 ⊢ |==> glG_fuel k v a0 ∗ glG_fuel k v a1.
  Proof.
    intros LE. iIntros "H". iApply glG_fuel_split. iApply glG_fuel_mon; done.
  Qed.
  Lemma glG_fuel_mon_split_list L v a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ list] k ∈ L, glG_fuel k v a2) ⊢ |==> ([∗ list] k ∈ L, glG_fuel k v a0) ∗ ([∗ list] k ∈ L, glG_fuel k v a1).
  Proof.
    iIntros (LE) "H". iPoseProof (glG_fuel_mon_list with "H") as ">H"; first done.
    by iApply glG_fuel_split_list.
  Qed.
  Lemma glG_fuel_mon_split_set L v a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ set] k ∈ L, glG_fuel k v a2) ⊢ |==> ([∗ set] k ∈ L, glG_fuel k v a0) ∗ ([∗ set] k ∈ L, glG_fuel k v a1).
  Proof.
    iIntros (LE) "H". iPoseProof (glG_fuel_mon_set with "H") as ">H"; first done.
    by iApply glG_fuel_split_set.
  Qed.

  Lemma glG_fuel_lt k v a0 a1 :
    a0 /< a1 →
    glG_fuel k v a1 ⊢ |==> glG_fuel k v a0 ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel k v c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (glG_fuel_mon_split _ _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.
  Lemma glG_fuel_lt_list L v a0 a1 :
    a0 /< a1 →
    ([∗ list] k ∈ L, glG_fuel k v a1) ⊢ |==> ([∗ list] k ∈ L, glG_fuel k v a0) ∗ ([∗ list] k ∈ L, ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel k v c).
  Proof.
    iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_lt.
  Qed.
  Lemma glG_fuel_lt_set L v a0 a1 :
    a0 /< a1 →
    ([∗ set] k ∈ L, glG_fuel k v a1) ⊢ |==> ([∗ set] k ∈ L, glG_fuel k v a0) ∗ ([∗ set] k ∈ L, ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel k v c).
  Proof.
    iIntros (LE) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_lt.
  Qed.

  Lemma glG_fuel_supply_mon k v a0 a1 q :
    a0 /≤ a1 →
    glG_fuel_supply k v a0 q ⊢ |==> glG_fuel_supply k v a1 q.
  Proof.
    intros LE. rewrite /glG_fuel_supply. apply own_update.
    by apply reservation_map_update, reservation_map_update, debt_update.
  Qed.

  Lemma glG_fuel_supply_add k v a0 a1 q0 q1 :
    glG_fuel_supply k v a0 q0 ∗ glG_fuel_supply k v a1 q1
    ⊢ ∃ b, glG_fuel_supply k v b (q0 + q1) ∗ ⌜ b /≤ a0 ∧ b /≤ a1 ⌝.
  Proof.
    rewrite /glG_fuel_supply. iIntros "[H1 H2]".
    iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame).
    iEval (rewrite -!reservation_map_data_op) in "H".
    destruct (debt_add a0 a1 q0 q1) as (b&Heq&Hle0&Hle1). rewrite Heq.
    iExists _. iSplitL; done.
  Qed.

  Lemma glG_fuel_supply_dfrac_valid k v a q :
    glG_fuel_supply k v a q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_fuel_supply. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite !reservation_map_data_valid in V.
    rewrite bank_valid_debt in V. destruct V. auto.
  Qed.

  Lemma glG_fuel_supply_issue k v q0 q1 a0 a1 :
    (q0 + q1 = 1)%Qp →
    glG_fuel_supply k v a0 (q0 + q1)%Qp
    ⊢ |==> glG_fuel_supply k v (a0 /+ a1) (q0 + q1)%Qp ∗ glG_fuel k v a1.
  Proof.
    rewrite /glG_fuel_supply -own_op. intros Heq. apply own_update.
    rewrite -!reservation_map_data_op. do 2 apply reservation_map_update.
    rewrite Heq. apply debt_owe.
  Qed.
  Lemma glG_fuel_supply_issue_2 k v q0 q1 a0 a1 b :
    (q0 + q1 = 1)%Qp →
    glG_fuel_supply k v a0 q0 ∗ glG_fuel_supply k v a1 q1
    ⊢ |==> glG_fuel_supply k v (a0 /+ b) q0 ∗ glG_fuel_supply k v (a0 /+ b) q1 ∗ glG_fuel k v b.
  Proof.
    iIntros (Heq) "H". iDestruct (glG_fuel_supply_add with "H") as "(%&H&%)".
    iMod (glG_fuel_supply_mon _ _ _ a0 with "H") as "H".
    { destruct H. auto. }
    iMod (glG_fuel_supply_issue _ _ _ _ _ b with "H") as "[H Hp]"; first done.
    iDestruct "H" as "[H0 H1]". by iFrame.
  Qed.

  Lemma glG_fuel_spend k v a0 a1 q :
    glG_fuel_supply k v a0 q ∗ glG_fuel k v a1
    ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ glG_fuel_supply k v a2 q.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -!reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ x, ∃ a2, (x = (reservation_map_data v (debt a2 q))) ∧ (a1 /+ a2 /≤ a0))
                (λ m, ∃ a2, (m = (reservation_map_data k (reservation_map_data v (debt a2 q)))) ∧ (a1 /+ a2 /≤ a0))
             ).
      { eapply reservation_map_updateP.
        { eapply debt_pay. }
        { intros. destruct H as (a2&A0&A1). eexists. by subst. }
      }
      { intros. destruct H as (a2&A0&A1). eexists. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplitR; done.
  Qed.
  Lemma glG_fuel_spend_2 k v a0 a1 q0 q1 c :
    glG_fuel_supply k v a0 q0 ∗ glG_fuel_supply k v a1 q1 ∗ glG_fuel k v c
    ⊢ |==> ∃ a2, (⌜(c /+ a2) /≤ a0 ∧ (c /+ a2) /≤ a1⌝) ∗
              glG_fuel_supply k v a2 q0 ∗ glG_fuel_supply k v a2 q1.
  Proof.
    iIntros "(H0&H1&H2)". iDestruct (glG_fuel_supply_add with "[H0 H1]") as "(%&H&%)"; first iFrame.
    iMod (glG_fuel_spend with "[H H2]") as "(%&%&H)"; first iFrame.
    iDestruct "H" as "[H0 H1]". iModIntro. iFrame. iPureIntro. destruct H. split.
    - etransitivity; [eapply H0 | eauto].
    - etransitivity; [eauto | eapply H].
  Qed.

  Lemma glG_fuel_id_alloc D k E :
    k ∉ D →
    glG_fuel_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_fuel_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        glG_fuel_token_version k E.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (reservation_map_token (A:=bankUR) E) with "Htk") as "[Htk >H]"; auto.
    { apply reservation_map_token_valid. }
    rewrite /glG_fuel_token_version. by iFrame.
  Qed.
  Lemma glG_fuel_alloc k D v a :
    v ∉ D →
    glG_fuel_token_version k (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_fuel_token_version k (⊤ ∖ gset_to_coPset ({[v]} ∪ D)) ∗
        glG_fuel_supply k v a 1 ∗ glG_fuel k v a.
  Proof.
    iIntros (Hk) "Htk". rewrite /glG_fuel_token_version.
    rewrite (reservation_map_token_difference (gset_to_coPset {[v]}) (⊤ ∖ gset_to_coPset D)); cycle 1.
    { apply elem_of_subseteq. intros. rewrite elem_of_difference. split; first set_solver.
      intro F. rewrite !elem_of_gset_to_coPset in H F. set_solver.
    }
    iDestruct "Htk" as "[Htk H]".
    assert (⊤ ∖ gset_to_coPset D ∖ gset_to_coPset {[v]} = ⊤ ∖ gset_to_coPset ({[v]} ∪ D)).
    { apply leibniz_equiv. intros x. rewrite !elem_of_difference. split; intros.
      - destruct H as ((_&?)&?). split; first set_solver. intros F. apply elem_of_gset_to_coPset, elem_of_union in F.
        destruct F; [apply H0 | apply H]; apply elem_of_gset_to_coPset; set_solver.
      - destruct H as (_&?). split; first (split; first set_solver);
          intros F; apply elem_of_gset_to_coPset in F; apply H, elem_of_gset_to_coPset; set_solver.
    }
    rewrite H. iFrame "H".
    iMod (own_update with "Htk") as "H".
    { eapply reservation_map_update. eapply (reservation_map_alloc _ v (debt a 1 ⋅ cash a)); auto.
      - apply elem_of_gset_to_coPset; set_solver.
      - apply bank_valid_debt_cash. split; done.
    }
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

  (** glG_until rules *)
  Lemma glG_until_acc E N k v q P Q :
    ↑N ⊆ E →
    glG_until N k v q P Q ={E,E ∖ ↑N}=∗
    ▷ glG_until_internal k v q P Q ∗
    (▷ glG_until_internal k v q P Q ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU". iPoseProof (inv_acc with "GU") as "$"; eauto.
  Qed.

  Lemma glG_until_acc_version E N k v q1 q2 P Q :
    ↑N ⊆ E →
    glG_until N k v q1 P Q -∗ glG_version k v q2 ={E,E ∖ ↑N}=∗
    glG_version k v q2 ∗
    (▷ ((glG_locked k q1 ∗ glG_version k v q1 ∗ P) ∨ (glG_unlocked k q1 ∗ glG_version k v q1 ∗ Q))) ∗
    ((▷ ((glG_locked k q1 ∗ glG_version k v q1 ∗ P) ∨ (glG_unlocked k q1 ∗ glG_version k v q1 ∗ Q)))
     ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (glG_until_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iFrame "GV". iSplitR "ACC".
      + iDestruct "H" as "[H | H]"; iFrame.
      + iIntros "H". iApply "ACC". iLeft. iDestruct "H" as "[H | H]"; iFrame.
    - iMod "H" as "(%&%&H)". iPoseProof (glG_version_lb_lb  with "[$GV $H]") as "%". lia.
  Qed.

  Lemma glG_until_acc_locked E N k v q1 q2 P Q :
    ↑N ⊆ E →
    glG_until N k v q1 P Q -∗ glG_locked k q2 ={E,E ∖ ↑N}=∗
    (▷ (glG_locked k q2 ∗
        ((glG_locked k q1 ∗ glG_version k v q1 ∗ P) ∨
           (∃ v', ⌜ Pos.lt v v' ⌝ ∗ glG_version_lb k v')))) ∗
    (((▷ (glG_locked k q1 ∗ glG_version k v q1 ∗ P) ∨ (∃ v', ⌜ Pos.lt v v' ⌝ ∗ glG_version_lb k v')))
     ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (glG_until_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC".
      + iNext. iDestruct "H" as "[H | H]"; first iFrame.
        iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
      + iIntros "H". iApply "ACC". iNext. iDestruct "H" as "[H | H]"; iFrame.
    - iModIntro. iSplitR "ACC"; iFrame.
      iIntros "H". iApply "ACC". iNext. iDestruct "H" as "[H | H]"; iFrame.
  Qed.
  Lemma glG_until_acc_unlocked E N k v q1 q2 P Q :
    ↑N ⊆ E →
    glG_until N k v q1 P Q -∗ glG_unlocked k q2 ={E,E ∖ ↑N}=∗
    (▷ (glG_unlocked k q2 ∗
        ((glG_unlocked k q1 ∗ glG_version k v q1 ∗ Q) ∨
           (∃ v', ⌜ Pos.lt v v' ⌝ ∗ glG_version_lb k v')))) ∗
    (((▷ (glG_unlocked k q1 ∗ glG_version k v q1 ∗ Q) ∨ (∃ v', ⌜ Pos.lt v v' ⌝ ∗ glG_version_lb k v')))
     ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV". iMod (glG_until_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC".
      + iNext. iDestruct "H" as "[H | H]"; last iFrame.
        iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
      + iIntros "H". iApply "ACC". iNext. iDestruct "H" as "[H | H]"; iFrame.
    - iModIntro. iSplitR "ACC"; iFrame.
      iIntros "H". iApply "ACC". iNext. iDestruct "H" as "[H | H]"; iFrame.
  Qed.

  Local Lemma glG_until_acc_done_1 E N k v q1 P Q :
    ↑N ⊆ E →
    glG_until N k v q1 P Q -∗ glG_done k ={E,E ∖ ↑N}=∗
    (▷ (∃ v', ⌜ Pos.lt v v' ⌝ ∗ glG_version_lb k v')) ∗
    ((∃ v', ⌜ Pos.lt v v' ⌝ ∗ glG_version_lb k v') ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU #GD". iMod (glG_until_acc with "GU") as "[[H | H] ACC]"; first auto.
    - iModIntro. iSplitR "ACC".
      + iNext. iDestruct "H" as "[(H& _) | (H& _)]".
        * iPoseProof (glG_locked_done_false with "[$]") as "%". done.
        * iPoseProof (glG_unlocked_done_false with "[$]") as "%". done.
      + iIntros "H". iApply "ACC". iFrame.
    - iModIntro. iSplitR "ACC"; iFrame.
      iIntros "H". iApply "ACC". iFrame.
  Qed.
  Lemma glG_until_acc_done E N k v q1 P Q :
    ↑N ⊆ E →
    glG_until N k v q1 P Q -∗ glG_done k ={E}=∗
    (∃ v', ⌜ Pos.lt v v' ⌝ ∗ glG_version_lb k v').
  Proof.
    iIntros (HE) "#GU #GD". iMod (glG_until_acc_done_1 with "GU GD") as "[>#H ACC]"; first auto.
    iMod ("ACC" with "H") as "ACC". done.
  Qed.

  Lemma glG_until_acc_version_locked E N k v q1 q2 q3 P Q :
    ↑N ⊆ E →
    glG_until N k v q1 P Q -∗ glG_version k v q2 -∗ glG_locked k q3 ={E,E ∖ ↑N}=∗
    glG_version k v q2 ∗
    ▷ (glG_locked k q3 ∗ (glG_locked k q1 ∗ glG_version k v q1 ∗ P)) ∗
    ((▷ (glG_locked k q1 ∗ glG_version k v q1 ∗ P)) ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV GL". iMod (glG_until_acc_version with "GU GV") as "(GV& H& ACC)"; first auto.
    iFrame "GV". iModIntro. iSplitR "ACC".
    - iNext. iDestruct "H" as "[H | H]"; first iFrame.
      iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - iIntros "H". iApply "ACC". iFrame.
  Qed.
  Lemma glG_until_acc_version_unlocked E N k v q1 q2 q3 P Q :
    ↑N ⊆ E →
    glG_until N k v q1 P Q -∗ glG_version k v q2 -∗ glG_unlocked k q3 ={E,E ∖ ↑N}=∗
    glG_version k v q2 ∗
    ▷ (glG_unlocked k q3 ∗ (glG_unlocked k q1 ∗ glG_version k v q1 ∗ Q)) ∗
    ((▷ (glG_unlocked k q1 ∗ glG_version k v q1 ∗ Q)) ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "#GU GV GL". iMod (glG_until_acc_version with "GU GV") as "(GV& H& ACC)"; first auto.
    iFrame "GV". iModIntro. iSplitR "ACC".
    - iNext. iDestruct "H" as "[H | H]"; last iFrame.
      iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - iIntros "H". iApply "ACC". iFrame.
  Qed.

  (* Allocates *)
  Lemma glG_until_alloc_locked E N k v q P Q :
    (▷ (glG_locked k q ∗ glG_version k v q ∗ P)) ={E}=∗ glG_until N k v q P Q.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.
  Lemma glG_until_alloc_unlocked E N k v q P Q :
    (▷ (glG_unlocked k q ∗ glG_version k v q ∗ Q)) ={E}=∗ glG_until N k v q P Q.
  Proof. iIntros "H". iApply inv_alloc. iFrame. Qed.

  (** glG_always rules *)
  Lemma glG_always_unfold N k v P :
    glG_always N k v P -∗ (glG_done k ∗ glG_version_pin k v ∗ inv N P).
  Proof. iIntros "$". Qed.

  Lemma glG_always_acc E N k v P :
    ↑N ⊆ E →
    glG_always N k v P ={E,E ∖ ↑N}=∗
    glG_done k ∗ glG_version_pin k v ∗ (▷ P) ∗
    ((▷ P) ={E ∖ ↑N,E}=∗ True).
  Proof.
    iIntros (HE) "(#GLD& #GVP& #IP)". iMod (inv_acc with "IP") as "[P ACC]"; first auto.
    iFrame. auto.
  Qed.

  Lemma glG_always_alloc E N k v P :
    glG_done k -∗ glG_version_pin k v -∗ (▷ P) ={E}=∗ glG_always N k v P.
  Proof. iIntros "$ $ P". iApply inv_alloc. iFrame. Qed.

  (** glsat rules *)
  Lemma glsat_elem k Ω :
    glsat Ω ∗ glG_elem k ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /glsat -!lock. iIntros "(Hsat& #Ge)".
    iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (glG_elem_elem with "[$]") as "%". done.
  Qed.
  Lemma glsat_elem_cases Ω k :
    glsat Ω ∗ glG_elem k
    ⊢ ∃ v, (⌜ (∃ a t, Ω !! k = Some (v, gl_locked a t)) ∨ (Ω !! k = Some (v, gl_unlocked)) ⌝) ∨
             (glG_done k ∗ glG_version_pin k v).
  Proof.
    iIntros "(Hsat & #Ge)". iPoseProof (glsat_elem with "[$]") as "%".
    apply elem_of_dom in H. destruct H.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete _ _ _ _ H with "HM") as "[H _]".
    destruct x. iDestruct "H" as "(_& %& H1& H2& H)". destruct g0.
    - iExists _. iLeft. iPureIntro. left. eauto.
    - iDestruct "H" as "([_ | #HD]& _)"; eauto.
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
    destruct o. iDestruct "LU" as "(_& %& Hvs& VS& Mk)". destruct g0.
    - iDestruct "Mk" as "(_& Gv2& _)".
      iPoseProof (glG_version_agree with "[$Gv $Gv2]") as "%". destruct H; subst; eauto.
    - iDestruct "Mk" as "([(_& Gv2) | (_& #Gv2)]& _)".
      + iPoseProof (glG_version_agree with "[$Gv $Gv2]") as "%". destruct H; subst; eauto.
      + iPoseProof (glG_version_pin_pin with "[$Gv $Gv2]") as "%". subst; eauto.
  Qed.
  Lemma glsat_lookup_locked Ω k q :
    glsat Ω ∗ glG_elem k ∗ glG_locked k q
    ⊢ ∃ v a t, ⌜Ω !! k = Some (v, gl_locked a t)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    destruct o. iDestruct "LU" as "(_& %& Hvs& VS& Mk)". destruct g0.
    - eauto.
    - iDestruct "Mk" as "([(Gu& Gv2) | (#Gd& #Gv2)]& _)".
      + iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
      + iPoseProof (glG_locked_done_false with "[$]") as "%". done.
  Qed.
  Lemma glsat_lookup_unlocked Ω k q :
    glsat Ω ∗ glG_elem k ∗ glG_unlocked k q
    ⊢ ∃ v, ⌜Ω !! k = Some (v, gl_unlocked)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gu)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    destruct o. iDestruct "LU" as "(_& %& Hvs& VS& Mk)". destruct g0.
    - iDestruct "Mk" as "(Gl& Gv& _)". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - eauto.
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
    destruct o. iDestruct "LU" as "(_& %& Hvs& VS& Mk)". destruct g0.
    - iDestruct "Mk" as "(Gl& Gv& Gf& Go2)".
      iPoseProof (glG_owner_agree with "[$Go $Go2]") as "(%&%)". subst. eauto.
    - iDestruct "Mk" as "(_& Gf& (%&Go2))".
      iPoseProof (glG_owner_agree with "[$Go $Go2]") as "(%&%)".
      apply Qp.not_add_le_r in H0. done.
  Qed.

  Lemma glsat_alloc_ghost_lock Ω k v a t :
    k ∉ dom Ω →
    glsat Ω
    ⊢ |==> glsat (<[k:=(v, gl_locked a t)]>Ω) ∗
        glG_elem k ∗
        glG_locked k (1/2 + 1/2/2)%Qp ∗ glG_version k v (1/2 + 1/2/2)%Qp ∗
        glG_fuel k v a ∗ glG_owner k t (1/2 + 1/2/2)%Qp.
  Proof.
    iIntros (Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iMod (glG_elem_alloc _ k (v, gl_locked a t) with "HE") as "[HE #Ge]"; first auto.
    iMod (glG_locked_alloc _ k with "HS") as "[HS Gl]"; first auto.
    iMod (glG_version_alloc _ k v with "HV") as "[HV Gv]"; first auto.
    iMod (glG_fuel_id_alloc _ k (⊤ ∖ gset_to_coPset ∅) with "HF") as "[HF HFv]"; first auto.
    iMod (glG_fuel_alloc k _ v a with "HFv") as "(HFv& Gfsp& Gf)"; first set_solver.
    iMod (glG_owner_alloc _ k t with "HO") as "[HO Go]"; first auto.
    iDestruct "Gl" as "[Gl1 [Gl2 Gl']]". iCombine "Gl1 Gl2" as "Gl".
    iDestruct "Gv" as "[Gv1 [Gv2 Gv']]". iCombine "Gv1 Gv2" as "Gv".
    iDestruct "Go" as "[Go1 [Go2 Go']]". iCombine "Go1 Go2" as "Go".
    iPoseProof (glG_version_get_lb_eq with "Gv") as "#Gvl".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HV HF HO". iFrame "Ge Gl Gv Gf Go".
    iApply big_sepM_insert; first auto. iFrame. iFrame "Ge".
    rewrite union_empty_r_L. rewrite big_sepS_singleton. iFrame "Gvl".
    iPureIntro. split; done.
  Qed.

  Lemma glsat_progress_one Ω k v a t c :
    (Ω !! k = Some (v, gl_locked a t)) →
    (/0 /< c) →
    glsat Ω ∗ glG_fuel k v c
    ⊢ |==> ∃ a', glsat (<[k:=(v, gl_locked a' t)]>Ω) ∗
              (⌜ ghost_lock_step (v, gl_locked a t) (v, gl_locked a' t) ⌝).
  Proof.
    intros LU Hc. iIntros "(Hsat & Gf)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(#Gek& %& HFTV& VS& (Glk& Gvk& (%& %LEa& Gfspk)& Gok))".
    iMod (glG_fuel_spend with "[$Gfspk $Gf]") as "(%&%&Gfspk)".
    assert (LT : a2 /< α).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (v, gl_locked a2 t)) with "[HM HFTV VS Glk Gvk Gok Gfspk]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. eauto. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HE HS HV HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. econstructor. eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma glsat_obl_progress Ω (C : gl_cond) :
    (∀ k g, C k g → ∃ v a o, g = (v, gl_locked a o)) →
    glsat Ω ∗
    ([∗ map] k ↦ g ∈ Ω, (⌜ C k g ⌝ ∗ ∃ v, ⌜ g.1 = v ⌝ ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel k v c)
                        ∨ (⌜ ¬ C k g ⌝))
    ⊢ |==> ∃ Ω', glsat Ω' ∗ (⌜ Ω ↪ₛ Ω' | C ⌝).
  Proof.
    iIntros (HC) "(Hsat & Cs)".
    iAssert (∃ Ω1 Ω2, (⌜ Ω1 ##ₘ Ω2 ∧ Ω = Ω1 ∪ Ω2 ∧ map_Forall (λ k g, C k g) Ω1 ∧ map_Forall (λ k g, ¬ C k g) Ω2 ⌝) ∗
                      ([∗ map] k ↦ g ∈ Ω1, (⌜ C k g ⌝ ∗ ∃ v, ⌜ g.1 = v ⌝ ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel k v c)) ∗
                      ([∗ map] k ↦ g ∈ Ω2, (⌜ ¬ C k g ⌝))
            )%I with "[Cs]" as "(%& %& (%Disj& %EQO& %CO1& %CO2)& Cs& NCs)".
    { iStopProof. induction Ω using map_ind; iIntros "M".
      { iExists ∅, ∅. rewrite !big_sepM_empty. done. }
      rewrite !big_sepM_insert; auto. iDestruct "M" as "(H& M)".
      iPoseProof (IHΩ with "M") as "(%& %& (%Disj& %EqO& %HC1& %HC2)& M1& M2)". clear IHΩ.
      assert (i ∉ dom Ω1 ∧ i ∉ dom Ω2).
      { subst. apply not_elem_of_dom in H. set_solver + H. }
      destruct H0 as [Nin1 Nin2]. apply not_elem_of_dom in Nin1, Nin2.
      iDestruct "H" as "[(%Ci& (%& %& %& %Hc& Gfi)) | %NCi]".
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
    iAssert (|==> ∃ Ω' : ghost_locks, glsat Ω' ∗ ⌜Ω ↪ₛ Ω' | (λ k _, k ∈ dom Ω1)⌝)%I with "[-]" as ">H"; cycle 1.
    { iDestruct "H" as "(%& S& %)". iModIntro. iFrame. iPureIntro.
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
    { iExists Ω. iModIntro. iFrame. iPureIntro. repeat intro. destruct (Ω !! i) eqn:LUi.
      - econstructor. right. split; intros; done.
      - econstructor.
    }
    rewrite !big_sepM_insert; auto. apply map_Forall_insert in CO; auto. destruct CO as (Ci& CO).
    iDestruct "M" as "((_& %& %Hver& %& %LTc& Bpi)& M)".
    iMod (IHΩ1 CO with "[$S $M]") as "(%& S& %Prog1)".
    { etransitivity; last eapply Sub. eapply insert_subseteq; auto. }
    clear IHΩ1.
    assert (LUi1 : Ω !! i = Some x).
    { eapply lookup_weaken; last eapply Sub. apply lookup_insert_eq. }
    assert (LUi2 : Ω' !! i = Some x).
    { specialize (Prog1 i). erewrite LUi1 in Prog1. inv Prog1. destruct H2.
      - destruct H0. apply not_elem_of_dom in H. done.
      - destruct H0. subst. auto.
    }
    pose proof Ci. apply HC in H0. destruct H0 as (v'& a& t& ?). subst.
    iMod (glsat_progress_one with "[$S $Bpi]") as "(%& S& %Progi)"; auto.
    { eauto. }
    iFrame. iPureIntro. simpl. assert (Prog2 : Ω' ↪ₛ <[i:=(v', gl_locked a' t)]> Ω' | λ k _, k = i).
    { intro j. destruct (decide (j = i)).
      { subst. rewrite LUi2. rewrite lookup_insert_eq. econstructor. left. split; done. }
      rewrite lookup_insert_ne; auto. destruct (Ω' !! j) eqn:LUj; econstructor. right; split; done.
    }
    (* Disjoint gl_conds *)
    eapply gls_cond_rel_split_cond. 4,5: eauto. all: simpl.
    - intros. rewrite dom_insert_L. set_solver.
    - intros. destruct (decide (k = i)); auto. subst. left. by apply not_elem_of_dom.
    - repeat intro. auto.
  Qed.

  Lemma glsat_progress_owner Ω k v a t1 t2 c :
    (Ω !! k = Some (v, gl_locked a t1)) →
    (/0 /< c) →
    glsat Ω ∗ glG_owner k t1 (1/2 + 1/2/2)%Qp ∗ glG_fuel k v c
    ⊢ |==> ∃ a', glsat (<[k:=(v, gl_locked a' t2)]>Ω) ∗ glG_owner k t2 (1/2 + 1/2/2)%Qp ∗
              (⌜ ghost_lock_step (v, gl_locked a t1) (v, gl_locked a' t2) ⌝).
  Proof.
    intros LU Hc. iIntros "(Hsat& Go& Gf)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HV& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(#Gek& %& HFTV& VS& (Glk& Gvk& (%& %LEa& Gfspk)& Gok))".
    iMod (glG_fuel_spend with "[$Gfspk $Gf]") as "(%&%&Gfspk)".
    assert (LT : a2 /< α).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iMod (glG_owner_update_2 _ _ _ _ _ t2 with "[$Go $Gok]") as "[Go Gok]".
    { rewrite -Qp.add_assoc !Qp.div_2. done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (v, gl_locked a2 t2)) with "[HM HFTV VS Glk Gvk Gok Gfspk]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. eauto. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HE HS HV HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. econstructor. eapply WFOCM.lt_le_lt; eauto.
  Qed.

  (* TODO: step rules: unlock, free, lock; done & pin rules *)

  Lemma glsat_obl_resolve_one Ω k P R x0 :
    glsat Ω ∗ glG_elem k ∗ glG_holds k P R ∗ (▷ R) ∗
    glG_locked k (1/2)%Qp ∗
    glG_owner k x0 (1/2)%Qp
    ⊢ |==> glsat (<[k:=odone P]>Ω) ∗ glG_unlocked k.
  Proof.
    iIntros "(Hsat & #He & #Hg & HR & Hs0 & Ho0)".
    iDestruct (glsat_obl_is_live with "[Hsat He Hs0]") as "(%&%LU)".
    { iFrame. eauto. }
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[Hk Hm]"; [eapply LU |].
    iDestruct "Hk" as "(Hs& Ho& (%&%&Hps))".
    iMod (glG_locked_to_done with "[Hs Hs0]") as "Hs".
    { iApply glG_locked_frac_op; last iFrame. by rewrite Qp.div_2. }
    iPoseProof (glG_unlocked_auth_done with "Hs") as "#Hsd".
    iPoseProof (glG_owner_agree with "[Ho Ho0]") as "%"; first iFrame.
    destruct H0. clear H1. subst x0.
    iCombine "Ho Ho0" as "Ho". iPoseProof (glG_owner_frac_op with "Ho") as "Ho".
    { by rewrite Qp.div_2. }
    iModIntro.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (odone P)) with "[Hm Hs Ho Hps HR]") as "Hm".
    { apply lookup_delete_eq. }
    { iFrame "Hm". iFrame. eauto. }
    rewrite dom_insert_lookup_L; last done. iFrame "HS HP".
    rewrite insert_delete_eq. iFrame. eauto.
  Qed.

  Lemma glsat_done_open Ω k P R :
    glsat Ω ∗ glG_holds k P R ∗ glG_unlocked k
    ⊢ (▷ R) ∗ (▷ R -∗ glsat Ω).
  Proof.
    iIntros "(Hsat & #Hg0 & #Hs0)".
    iPoseProof (glsat_obl_is_done with "[Hsat]") as "%Hdone"; [iFrame; eauto|].
    destruct Hdone as (?&LU&HP).
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iDestruct (big_sepM_delete _ _ k _ LU with "Hm") as "[Hk Hm]".
    iDestruct "Hk" as "( %&% & #Hg & %HPeq & HR & Hsa & %& Hps)".
    iPoseProof (glG_holds_agree with "[Hg Hg0]") as "(%Hpeq1 & HReq)".
    { iSplit; [iFrame "Hg" | iFrame "Hg0"]. }
    iSplitL "HR".
    { iNext. by iRewrite "HReq" in "HR". }
    iIntros "HR". iFrame "HS HP HG".
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (odone x)) with "[Hm Hsa Hps HR]") as "Hm".
    { apply lookup_delete_eq. }
    { iFrame "Hm". iFrame. iExists P. eauto. }
    rewrite insert_delete_eq insert_id; last done. iFrame. eauto.
  Qed.

  Lemma glsat_done_open_pers Ω k P R :
    Persistent R →
    glsat Ω ∗ glG_holds k P R ∗ glG_unlocked k
    ⊢ glsat Ω ∗ ▷ R.
  Proof.
    iIntros (PP) "H". iPoseProof (glsat_done_open with "H") as "[#HP Ho]".
    iSplitL; [|done]. iApply "Ho". done.
  Qed.

  Lemma glsat_live_open_owner Ω k q :
    glsat Ω ∗ glG_elem k ∗ glG_locked k q
    ⊢ ∃ i, glG_locked k q ∗ glG_locked k (1/2)%Qp ∗ glG_owner k i (1/2) ∗
           ((glG_locked k (1/2)%Qp ∗ glG_owner k i (1/2)) -∗ glsat Ω).
  Proof.
    iIntros "(Hsat & #He0 & Hs0)".
    iPoseProof (glsat_obl_is_live with "[Hsat Hs0]") as "%Hlive"; [iFrame; eauto|].
    destruct Hlive as (?&LU).
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS&HO&HP&HE & Hm)".
    iDestruct (big_sepM_delete _ _ k _ LU with "Hm") as "[Hk Hm]".
    iDestruct "Hk" as "( Hs & Ho & (%&%&Hps) )".
    iFrame "Hs0 Hs Ho". iIntros "[Hs Ho]". iFrame "HG HS HO HP HE". iSplitR; first done.
    iApply (big_sepM_delete _ _ k _ LU). iFrame. done.
  Qed.
  Lemma glsat_live_open Ω k q :
    glsat Ω ∗ glG_elem k ∗ glG_locked k q
    ⊢ glG_locked k q ∗ glG_locked k (1/2)%Qp ∗ (glG_locked k (1/2)%Qp -∗ glsat Ω).
  Proof.
    iIntros "(Hsat & #He0 & Hs0)".
    iPoseProof (glsat_live_open_owner with "[$]") as "(%&Bl&Bl2&Bo&S)". iFrame.
    iIntros "Bl". iApply "S". iFrame.
  Qed.

  Lemma glsat_lookup_owner Ω k τ q :
    glsat Ω ∗ glG_elem k ∗ glG_owner k τ q ⊢ ∃ d, ⌜ Ω !! k = Some (obl_live d) ∧ obl_owner d = τ ⌝.
  Proof.
    iIntros "(Hsat & #Hek1 & Hok)".
    iPoseProof (glsat_elem k with "[Hsat]") as "%Helem"; first iFrame; eauto.
    apply elem_of_dom in Helem. destruct Helem as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS&HO&HP&HE & Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[Hk Hm]"; [eapply LU |].
    destruct o.
    - iDestruct "Hk" as "( Hs & Ho & (%&%&Hps) )".
      iPoseProof (glG_owner_agree with "[Hok Ho]") as "%"; first iFrame. destruct H0.
      iExists o. iPureIntro. split; auto.
    - iDestruct "Hk" as "( %&% & #Hg & %HPeq & HR & Hsa & %&%& Ho & Hps)".
      iPoseProof (glG_owner_agree with "[Hok Ho]") as "%"; first iFrame. destruct H.
      exfalso. apply Qp.not_add_le_l in H0. auto.
  Qed.

  (* Update rules for glG_until *)






  (** Holds rules *)
  Lemma glG_holds_lookup (OProp : gmap positive (prop_of ps * iProp Σ)) k P R :
    own holds_name (gmap_view_auth (DfracOwn 1) ((λ '(P, R), (to_agree P, to_agree $ (holds_unfold R))) <$> OProp)) ∗
    glG_holds k P R
    ⊢ ∃ P' R', ⌜ OProp !! k = Some (P', R') ⌝ ∗ ⌜ P' = P ⌝ ∗ ▷ (R' ≡ R).
  Proof.
    rewrite /glG_holds -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
    case: (OProp !! k)=> [Q|] /=; last first.
    { by iDestruct "HQ'" as %?. }
    destruct Q as (P'&R'). iDestruct "HQ'" as %[= <-]. iExists P', R'; iSplit; first done.
    rewrite prod_includedI !to_agree_includedI; simpl. iDestruct "Hincl" as "[H1 H2]".
    rewrite /holds_unfold -later_equivI. iSplit.
    - iPoseProof (internal_eq_sym with "H1") as "H1". iPoseProof (discrete_eq with "H1") as "%HG". done.
    - iPoseProof (internal_eq_sym with "H2") as "H2". done.
  Qed.

  Lemma glG_holds_agree k P0 P1 R0 R1 :
    glG_holds k P0 R0 ∗ glG_holds k P1 R1 ⊢ ⌜ P0 ≡ P1 ⌝ ∗ ▷ (R0 ≡ R1).
  Proof.
    rewrite /glG_holds -own_op own_valid gmap_view_frag_op_validI.
    iIntros "(_&H)". rewrite -pair_op prod_validI; simpl. iDestruct "H" as "[% H]".
    rewrite /holds_unfold to_agree_op_validI -later_equivI. iFrame.
    iPureIntro. apply to_agree_op_valid in H. rewrite H. done.
  Qed.

  Lemma glG_holds_elem (OProp : gmap positive (prop_of ps * iProp Σ)) k P R :
    own holds_name (gmap_view_auth (DfracOwn 1) ((λ '(P, R), (to_agree P, to_agree $ (holds_unfold R))) <$> OProp)) ∗
    glG_holds k P R
    ⊢ ⌜ k ∈ dom OProp ⌝.
  Proof.
    iIntros "[H Hg]". iPoseProof (glG_holds_lookup with "[$]") as "(%&%&%&_)".
    iPureIntro. by apply elem_of_dom.
  Qed.


  (* (** Fuel bound rules *) *)
  (* Lemma glG_version_auth_alloc D k a : *)
  (*   k ∉ D → *)
  (*   (own version_name (reservation_map_token (A:=auth_mraUR (wfocm_geR)) (⊤ ∖ gset_to_coPset D))) *)
  (*   ⊢ |==> (own version_name (reservation_map_token (A:=auth_mraUR (wfocm_geR)) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗ *)
  (*          glG_version_auth k a. *)
  (* Proof. *)
  (*   iIntros (Hk) "Htk". *)
  (*   iPoseProof (reservation_map_token_alloc_singleton _ _ k (●AM[wfocm_geR] a) with "Htk") as "[Htk >H]"; auto. *)
  (*   - apply auth_mra_auth_valid. *)
  (*   - rewrite /glG_version_auth. by iFrame. *)
  (* Qed. *)

  (* Lemma glG_version_know k a : *)
  (*   glG_version_auth k a ⊢ glG_version k a. *)
  (* Proof. *)
  (*   rewrite /glG_version_auth /glG_version. rewrite auth_mra_auth_know_op. *)
  (*   rewrite reservation_map_data_op. iIntros "[H1 H2]". iFrame. *)
  (* Qed. *)

  (* Lemma glG_version_know_bound k a0 a1 : *)
  (*   glG_version_auth k a0 ∗ glG_version k a1 ⊢ ⌜ a0 /≤ a1 ⌝. *)
  (* Proof. *)
  (*   rewrite /glG_version_auth /glG_version -own_op -reservation_map_data_op. *)
  (*   iIntros "H". iPoseProof (own_valid with "H") as "%V". apply reservation_map_data_valid in V. *)
  (*   apply (auth_mra_both_valid wfocm_geR) in V. done. *)
  (* Qed. *)

  (* Lemma glG_version_auth_mon k a0 a1 : *)
  (*   a1 /≤ a0 → *)
  (*   glG_version_auth k a0 ⊢ |==> glG_version_auth k a1. *)
  (* Proof. iIntros (Ha). apply own_update, reservation_map_update, auth_mra_update; eauto. apply _. Qed. *)

  (* Lemma glG_version_mon k a0 a1 : *)
  (*   a0 /≤ a1 → *)
  (*   glG_version k a0 ⊢ glG_version k a1. *)
  (* Proof. iIntros (Ha). apply own_mono, reservation_map_data_mono, auth_mra_know_mono; eauto. apply _. Qed. *)



End glsat.

(* Allocation of an initial obligation protocol. *)
Lemma glsat_alloc `{SI : indexT} `{WFA : WFOCM.pack A} `{!glsatGpreS ps T Σ}
  `{obl_live_class A T WFOCM.ltR} `{obl_done_class ps} :
  ⊢ |==> ∃ _ : glsatGS ps T Σ, glsat ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR gl_id (prodR _ _))) as (γG) "HG";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=dfrac_agreeR (leibnizO T))⊤)) as (γO) "HO";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bankUR) ⊤)) as (γC) "HC";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR gl_id unitUR)) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (GlsatG SI _ WFA _ _ _ _ γG γS γO γC γE).
  rewrite /glsat -lock.
  iSplitL "HG"; first (iExists ∅; by iFrame).
  replace (⊤ ∖ gset_to_coPset (dom (∅ : ghost_locks))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
