From iris.algebra Require Import gmap_view reservation_map dfrac_agree mono_nat.
From iris.bi Require Import lib.cmra.
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
        glsatGpreS_elem :
        inG Σ (gmap_viewR gl_id (gmap_viewR gl_version unitUR));
        glsatGpreS_holds :
        inG Σ (gmap_viewR gl_id (gmap_viewR gl_version (prodR (agreeR $ (laterO (iPropO Σ))) (agreeR $ (laterO (iPropO Σ))))));
        (* Use encode of Countable to encode gl_version to positive *)
        glsatGpreS_state :
        inG Σ (reservation_mapUR (reservation_mapUR mono_natUR));
        glsatGpreS_version :
        inG Σ (reservation_mapUR (auth_mraUR glv_le));
        glsatGpreS_fuel :
        inG Σ (reservation_mapUR (reservation_mapUR bankUR));
        (* We only keep track of current owner for each lock, if the owner exists *)
        glsatGpreS_owner :
        inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO gl_owner)));
      }.

  Class glsatGS `{SI : indexT} `{GL : ghost_lock_class} (Σ : gFunctors) : Set :=
    GlsatG {
        glsat_inG : glsatGpreS Σ;
        elem_name : gname;
        holds_name : gname;
        state_name : gname;
        version_name : gname;
        fuel_name : gname;
        owner_name : gname;
      }.

  Definition glsatΣ `{SI : indexT} `{GL : ghost_lock_class} : gFunctors :=
    #[GFunctor (gmap_viewR gl_id (gmap_viewR gl_version unitUR));
      GFunctor (gmap_viewTRF gl_id (gmap_viewTRF gl_version (prodTRF (agreeTRF $ (laterTF idTF)) (agreeTRF $ (laterTF idTF)))));
      GFunctor (reservation_mapUR (reservation_mapUR mono_natUR));
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
  glsatGpreS_elem glsatGpreS_holds glsatGpreS_state glsatGpreS_version glsatGpreS_fuel glsatGpreS_owner.

(* Elem *)
Definition glG_elem `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own elem_name (gmap_view_frag k DfracDiscarded (gmap_view_frag v DfracDiscarded ())).
Global Typeclasses Opaque glG_elem.
Global Instance: Params (@glG_elem) 5 := {}.

Local Definition glG_elem_auth_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (m : gmap gl_id (gmap gl_version unit)) : iProp Σ :=
  own elem_name (gmap_view_auth (V:=gmap_viewR gl_version unitUR)
                   (DfracOwn 1) ((gmap_view_auth (DfracOwn 1)) <$> m)).
Local Definition glG_elem_auth_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (m : gmap gl_version unit) : iProp Σ :=
  own elem_name (gmap_view_frag (V:=gmap_viewR gl_version unitUR)
                   k (DfracOwn 1) (gmap_view_auth (DfracOwn 1) m)).

(* Holds *)
Definition holds_unfold `{SI : indexT} {Σ} (P : iProp Σ) : later (iProp Σ) := Next P.
Global Instance: Params (@holds_unfold) 2 := {}.

Definition glG_holds `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (n : gl_version) (P : iProp Σ) (Q : iProp Σ) : iProp Σ :=
  own holds_name (gmap_view_frag k DfracDiscarded (gmap_view_frag n DfracDiscarded (to_agree $ holds_unfold P, to_agree $ holds_unfold Q))).
Global Typeclasses Opaque glG_holds.
Global Instance: Params (@glG_holds) 5 := {}.

Local Definition glG_holds_auth_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (m : gmap gl_id (gmap gl_version (iPropO Σ * iPropO Σ))) : iProp Σ :=
  own holds_name (gmap_view_auth (V:=gmap_viewR gl_version (prodR (agreeR $ (laterO (iPropO Σ))) (agreeR $ (laterO (iPropO Σ)))))
                    (DfracOwn 1) ((gmap_view_auth (DfracOwn 1)) <$> ((λ vm, (λ '(P, Q), (to_agree $ (holds_unfold P), to_agree $ (holds_unfold Q))) <$> vm) <$> m))).
Local Definition glG_holds_auth_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (m : gmap gl_version (iPropO Σ * iPropO Σ)) : iProp Σ :=
  own holds_name (gmap_view_frag (V:=gmap_viewR gl_version (prodR (agreeR $ (laterO (iPropO Σ))) (agreeR $ (laterO (iPropO Σ)))))
                    k (DfracOwn 1) (gmap_view_auth (DfracOwn 1) ((λ '(P, Q), (to_agree $ (holds_unfold P), to_agree $ (holds_unfold Q))) <$> m))).

(* State: locked or unlocked with version *)
Definition glG_locked `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data k (reservation_map_data (encode v) (●MN{#q} 0))).
Global Typeclasses Opaque glG_locked.
Global Instance: Params (@glG_locked) 5 := {}.

Definition glG_unlocked_auth `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own state_name (reservation_map_data k (reservation_map_data (encode v) (●MN 1))).
Global Typeclasses Opaque glG_unlocked_auth.
Global Instance: Params (@glG_unlocked_auth) 5 := {}.

Definition glG_unlocked `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own state_name (reservation_map_data k (reservation_map_data (encode v) (◯MN 1))).
Global Typeclasses Opaque glG_unlocked.
Global Instance: Params (@glG_unlocked) 5 := {}.

Local Definition glG_state_token_id `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own state_name (reservation_map_token (A:=reservation_mapUR mono_natUR) E).
Local Definition glG_state_token_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (E : coPset) : iProp Σ :=
  own state_name (reservation_map_data k (reservation_map_token (A:=mono_natUR) E)).

(* Version: tracks an upperbound *)
Definition glG_version `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own version_name (reservation_map_data k (◯AM[glv_le] v)).
Global Typeclasses Opaque glG_version.
Global Instance: Params (@glG_version) 5 := {}.

Definition glG_version_auth `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) : iProp Σ :=
  own version_name (reservation_map_data k (●AM[glv_le] v)).
Global Typeclasses Opaque glG_version_auth.
Global Instance: Params (@glG_version_auth) 5 := {}.

Local Definition glG_version_token `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own version_name (reservation_map_token (A:=auth_mraUR glv_le) E).

(* Fuel: manage credits for lock's fuel *)
Definition glG_fuel `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (a : gl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data k (reservation_map_data (A:=bankUR) (encode v) (cash a))).
Global Typeclasses Opaque glG_fuel.
Global Instance: Params (@glG_fuel) 5 := {}.

Definition glG_fuel_supply `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (k : gl_id) (v : gl_version) (a : gl_fuel) (q : Qp) : iProp Σ :=
  own fuel_name (reservation_map_data k (reservation_map_data (A:=bankUR) (encode v) (debt a q))).
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

Local Definition glG_owner_token `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO gl_owner)) E).

(* TODO : add "key"s - ownE, ownD tokens for each gl_id, gl_token *)

(* Global invariant for ghost locks. *)
Definition glsat `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ}
  (Ω : ghost_locks) : iProp Σ :=
  locked
    ((∃ (Holds : gmap gl_id (iProp Σ * iProp Σ)),
         (⌜ dom Holds = dom Ω ⌝) ∗
         own holds_name (gmap_view_auth (DfracOwn 1) ((λ '(P, R), (to_agree P, to_agree $ (holds_unfold R))) <$> OProp))) ∗
     (own state_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO T))(⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own fuel_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (* (own version_name (reservation_map_token (A:=auth_mraUR (wfocm_geR)) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗ *)
     (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom Ω)))) ∗
     ([∗ map] k ↦ o ∈ Ω,
        match o with
        | inl d =>
            glG_locked k (1/2)%Qp ∗
            (glG_owner k (obl_owner d) (1/2)%Qp) ∗
            (∃ α, (⌜ WFOCM.leR α (obl_fuel d) ⌝) ∗ glG_fuel_supply k α (1)%Qp)
            (* (∃ α ℵ, (⌜ WFOCM.leR α (obl_fuel d) ∧ WFOCM.leR (obl_fuel d) ℵ ⌝) ∗ *)
            (*         glG_fuel_supply k α (1)%Qp ∗ glG_version_auth k ℵ) *)
        | inr d =>
            let P1 := (obl_atom d) in
            ∃ P2 R, glG_holds k P2 R ∗ ⌜ P1 ≡ P2 ⌝ ∗ ▷ R ∗
                    glG_unlocked_auth k ∗ ∃ θ α, glG_owner k θ 1 ∗ glG_fuel_supply k α 1
        end)
    )%I.

Definition glsat `{SI : indexT} `{GL : ghost_lock_class} `{!glsatGS Σ} `{!invGS Σ}
  (Ω : ghost_locks) : iProp Σ :=
  locked
    ((∃ (Holds : gmap gl_id (prop_of ps * iProp Σ)),
         (⌜ dom OProp = dom Ω ⌝) ∗
         own holds_name (gmap_view_auth (DfracOwn 1) ((λ '(P, R), (to_agree P, to_agree $ (holds_unfold R))) <$> OProp))) ∗
     (own state_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO T))(⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (own fuel_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗
     (* (own version_name (reservation_map_token (A:=auth_mraUR (wfocm_geR)) (⊤ ∖ gset_to_coPset (dom Ω)))) ∗ *)
     (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom Ω)))) ∗
     ([∗ map] k ↦ o ∈ Ω,
        match o with
        | inl d =>
            glG_locked k (1/2)%Qp ∗
            (glG_owner k (obl_owner d) (1/2)%Qp) ∗
            (∃ α, (⌜ WFOCM.leR α (obl_fuel d) ⌝) ∗ glG_fuel_supply k α (1)%Qp)
            (* (∃ α ℵ, (⌜ WFOCM.leR α (obl_fuel d) ∧ WFOCM.leR (obl_fuel d) ℵ ⌝) ∗ *)
            (*         glG_fuel_supply k α (1)%Qp ∗ glG_version_auth k ℵ) *)
        | inr d =>
            let P1 := (obl_atom d) in
            ∃ P2 R, glG_holds k P2 R ∗ ⌜ P1 ≡ P2 ⌝ ∗ ▷ R ∗
                    glG_unlocked_auth k ∗ ∃ θ α, glG_owner k θ 1 ∗ glG_fuel_supply k α 1
        end)
    )%I.

(** Properties *)
Section glsat.
  Context `{SI : indexT} `{WFA : WFOCM.pack A} `{!glsatGS ps T Σ}.
  Context `{Ξl : obl_live_class A T WFOCM.ltR} `{Ξd : obl_done_class ps}.

  Local Instance holds_unfold_contractive : Contractive (@holds_unfold SI Σ).
  Proof. solve_contractive. Qed.
  Global Instance glG_holds_contractive k P : Contractive (@glG_holds SI _ WFA ps T Σ _ k P).
  Proof. solve_contractive. Qed.

  Global Instance glG_holds_persistent k P R : Persistent (glG_holds k P R).
  Proof. rewrite /glG_holds. apply _. Qed.
  Global Instance glG_elem_persistent k : Persistent (glG_elem k).
  Proof. rewrite /glG_elem. apply _. Qed.
  Global Instance glG_unlocked_persistent k : Persistent (glG_unlocked k).
  Proof. rewrite /glG_unlocked. apply _. Qed.
  (* Global Instance glG_version_persistent k ℵ : Persistent (glG_version k ℵ). *)
  (* Proof. rewrite /glG_version. apply _. Qed. *)

  Global Instance glG_elem_timeless k : Timeless (glG_elem k).
  Proof. rewrite /glG_elem. apply _. Qed.
  Global Instance glG_locked_timeless k q : Timeless (glG_locked k q).
  Proof. rewrite /glG_locked. apply _. Qed.
  Global Instance glG_unlocked_timeless k : Timeless (glG_unlocked k).
  Proof. rewrite /glG_unlocked. apply _. Qed.
  Global Instance glG_fuel_timeless k b : Timeless (glG_fuel k b).
  Proof. rewrite /glG_fuel. apply _. Qed.
  (* Global Instance glG_version_timeless k a : Timeless (glG_version k a). *)
  (* Proof. rewrite /glG_version. apply _. Qed. *)

  (* frac instances *)
  Global Instance mono_nat_auth_own_fractional γ n :
    Fractional (λ q, mono_nat_auth_own γ q n).
  Proof. unseal. intros p q. rewrite -own_op -mono_nat_auth_dfrac_op //. Qed.
  Global Instance mono_nat_auth_own_as_fractional γ q n :
    AsFractional (mono_nat_auth_own γ q n) (λ q, mono_nat_auth_own γ q n) q.
  Proof. split; [auto|apply _]. Qed.


  Local Infix "/=" := OCM.eq (at level 70).
  Local Infix "/≤" := WFOCM.leR (at level 70).
  Local Infix "/+" := WFOCM.addO (at level 70).
  Local Infix "/<" := WFOCM.ltR (at level 70).
  Local Notation "/0" := OCM.unit.

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

  (** Elem rules *)
  Lemma glG_elem_alloc (Ω : obl_states) k M :
    Ω !! k = None →
    (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom Ω))))
    ⊢  |==> (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom (<[k:=M]>Ω))))) ∗
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

  Lemma glG_elem_elem k (Ω : obl_states) :
    (own elem_name (gmap_view_auth (DfracOwn 1) (gset_to_gmap () (dom Ω)))) ∗
    glG_elem k
    ⊢ ⌜ k ∈ dom Ω ⌝.
  Proof.
    rewrite /glG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro.
    apply lookup_gset_to_gmap_Some in H. by destruct H.
  Qed.

  (** Status rules *)
  Lemma glG_locked_done_false k q :
    glG_locked k q ∗ glG_unlocked k ⊢ False.
  Proof.
    rewrite /glG_locked /glG_unlocked. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma glG_unlocked_auth_done k :
    glG_unlocked_auth k ⊢ glG_unlocked k.
  Proof.
    rewrite /glG_unlocked_auth /glG_unlocked.
    apply own_mono.
    apply reservation_map_data_mono. apply mono_nat_included.
  Qed.

  Lemma glG_locked_to_done k :
    glG_locked k 1 ⊢ |==> glG_unlocked_auth k.
  Proof.
    rewrite /glG_locked /glG_unlocked_auth.
    apply own_update.
    apply reservation_map_update. apply mono_nat_update. auto.
  Qed.

  Lemma glG_locked_frac_op k q1 q2 q :
    q = (q1 + q2)%Qp →
    glG_locked k q1 ∗ glG_locked k q2 ⊣⊢ glG_locked k q.
  Proof.
    intros; subst. rewrite /glG_locked. iSplit; [iIntros "[H1 H2]" | iIntros "H"].
    - iCombine "H1 H2" as "H". done.
    - iDestruct "H" as "[H1 H2]". iFrame.
  Qed.
  Lemma glG_locked_div_2 k q :
    glG_locked k (q/2) ∗ glG_locked k (q/2) ⊣⊢ glG_locked k q.
  Proof. rewrite glG_locked_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma glG_locked_valid k q :
    glG_locked k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_locked. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply mono_nat_auth_dfrac_valid in V. by apply dfrac_valid in V.
  Qed.

  Lemma glG_locked_alloc D k :
    k ∉ D →
    (own state_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own state_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           glG_locked k 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN 0) with "Htk") as "[Htk >H]"; auto.
    { apply mono_nat_auth_valid. }
    rewrite /glG_locked. by iFrame.
  Qed.

  (** Fuel rules *)
  Lemma glG_fuel_eq i a0 a1 :
    a0 /= a1 →
    glG_fuel i a0 = glG_fuel i a1.
  Proof. intros EQ. rewrite /glG_fuel. by erewrite cash_eq. Qed.
  Lemma glG_fuel_eq_list L a0 a1 :
    a0 /= a1 →
    ([∗ list] i ∈ L, glG_fuel i a0)%I ≡ ([∗ list] i ∈ L, glG_fuel i a1)%I.
  Proof. intros. apply big_opL_proper. intros. erewrite glG_fuel_eq; eauto. Qed.
  Lemma glG_fuel_eq_set L a0 a1 :
    a0 /= a1 →
    ([∗ set] i ∈ L, glG_fuel i a0)%I ≡ ([∗ set] i ∈ L, glG_fuel i a1)%I.
  Proof. intros. apply big_opS_proper. intros. erewrite glG_fuel_eq; eauto. Qed.

  Lemma glG_fuel_mon i a0 a1 :
    a0 /≤ a1 →
    glG_fuel i a1 ⊢ |==> glG_fuel i a0.
  Proof.
    intros LE. rewrite /glG_fuel. apply own_update.
    by apply reservation_map_update, cash_update.
  Qed.
  Lemma glG_fuel_mon_list L a0 a1 :
    a0 /≤ a1 →
    ([∗ list] i ∈ L, glG_fuel i a1) ⊢ |==> ([∗ list] i ∈ L, glG_fuel i a0).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_mon.
  Qed.
  Lemma glG_fuel_mon_set L a0 a1 :
    a0 /≤ a1 →
    ([∗ set] i ∈ L, glG_fuel i a1) ⊢ |==> ([∗ set] i ∈ L, glG_fuel i a0).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_mon.
  Qed.

  Lemma glG_fuel_split i a0 a1 :
    glG_fuel i (a0 /+ a1) ⊣⊢ glG_fuel i a0 ∗ glG_fuel i a1.
  Proof.
    rewrite /glG_fuel. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -cash_add) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite -cash_add). iSplitL "H1"; iFrame.
  Qed.
  Lemma glG_fuel_split_list L a0 a1 :
    ([∗ list] i ∈ L, glG_fuel i (a0 /+ a1)) ⊣⊢ ([∗ list] i ∈ L, glG_fuel i a0) ∗ ([∗ list] i ∈ L, glG_fuel i a1).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply glG_fuel_split.
  Qed.
  Lemma glG_fuel_split_set L a0 a1 :
    ([∗ set] i ∈ L, glG_fuel i (a0 /+ a1)) ⊣⊢ ([∗ set] i ∈ L, glG_fuel i a0) ∗ ([∗ set] i ∈ L, glG_fuel i a1).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply glG_fuel_split.
  Qed.

  Lemma glG_fuel_mon_split i a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    glG_fuel i a2 ⊢ |==> glG_fuel i a0 ∗ glG_fuel i a1.
  Proof.
    intros LE. iIntros "H". iApply glG_fuel_split. iApply glG_fuel_mon; done.
  Qed.
  Lemma glG_fuel_mon_split_list L a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ list] i ∈ L, glG_fuel i a2) ⊢ |==> ([∗ list] i ∈ L, glG_fuel i a0) ∗ ([∗ list] i ∈ L, glG_fuel i a1).
  Proof.
    iIntros (LE) "H". iPoseProof (glG_fuel_mon_list with "H") as ">H"; first done.
    by iApply glG_fuel_split_list.
  Qed.
  Lemma glG_fuel_mon_split_set L a0 a1 a2 :
    a0 /+ a1 /≤ a2 →
    ([∗ set] i ∈ L, glG_fuel i a2) ⊢ |==> ([∗ set] i ∈ L, glG_fuel i a0) ∗ ([∗ set] i ∈ L, glG_fuel i a1).
  Proof.
    iIntros (LE) "H". iPoseProof (glG_fuel_mon_set with "H") as ">H"; first done.
    by iApply glG_fuel_split_set.
  Qed.

  Lemma glG_fuel_lt i a0 a1 :
    a0 /< a1 →
    glG_fuel i a1 ⊢ |==> glG_fuel i a0 ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel i c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (glG_fuel_mon_split _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.
  Lemma glG_fuel_lt_list L a0 a1 :
    a0 /< a1 →
    ([∗ list] i ∈ L, glG_fuel i a1) ⊢ |==> ([∗ list] i ∈ L, glG_fuel i a0) ∗ ([∗ list] i ∈ L, ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel i c).
  Proof.
    iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_lt.
  Qed.
  Lemma glG_fuel_lt_set L a0 a1 :
    a0 /< a1 →
    ([∗ set] i ∈ L, glG_fuel i a1) ⊢ |==> ([∗ set] i ∈ L, glG_fuel i a0) ∗ ([∗ set] i ∈ L, ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel i c).
  Proof.
    iIntros (LE) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply glG_fuel_lt.
  Qed.

  Lemma glG_fuel_supply_mon k a0 a1 q :
    a0 /≤ a1 →
    glG_fuel_supply k a0 q ⊢ |==> glG_fuel_supply k a1 q.
  Proof.
    intros LE. rewrite /glG_fuel_supply. apply own_update.
    by apply reservation_map_update, debt_update.
  Qed.

  Lemma glG_fuel_supply_add i a0 a1 q0 q1 :
    glG_fuel_supply i a0 q0 ∗ glG_fuel_supply i a1 q1
    ⊢ ∃ b, glG_fuel_supply i b (q0 + q1) ∗ ⌜ b /≤ a0 ∧ b /≤ a1 ⌝.
  Proof.
    rewrite /glG_fuel_supply. iIntros "[H1 H2]".
    iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame).
    iEval (rewrite -reservation_map_data_op) in "H".
    destruct (debt_add a0 a1 q0 q1) as (b&Heq&Hle0&Hle1). rewrite Heq.
    iExists _. iSplitL; done.
  Qed.

  Lemma glG_fuel_supply_split i a q0 q1 q :
    q = (q0 + q1)%Qp →
    glG_fuel_supply i a q ⊢ glG_fuel_supply i a q0 ∗ glG_fuel_supply i a q1.
  Proof.
    rewrite /glG_fuel_supply. iIntros (Hq) "H".
    iApply own_op. iEval (rewrite -reservation_map_data_op).
    subst. rewrite debt_split. done.
  Qed.
  Lemma glG_fuel_supply_div_2 k a q :
    glG_fuel_supply k a q ⊢ glG_fuel_supply k a (q/2) ∗ glG_fuel_supply k a (q/2).
  Proof. rewrite glG_fuel_supply_split; first done. by rewrite Qp.div_2. Qed.
  Lemma glG_fuel_supply_dfrac_valid k a q :
    glG_fuel_supply k a q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_fuel_supply. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    rewrite bank_valid_debt in V. destruct V. auto.
  Qed.

  Lemma glG_fuel_supply_issue i q0 q1 a0 a1 :
    (q0 + q1 = 1)%Qp →
    glG_fuel_supply i a0 (q0 + q1)%Qp ⊢ |==> glG_fuel_supply i (a0 /+ a1) (q0 + q1)%Qp ∗ glG_fuel i a1.
  Proof.
    rewrite /glG_fuel_supply -own_op. intros Heq. apply own_update.
    rewrite -reservation_map_data_op. apply reservation_map_update.
    rewrite Heq. apply debt_owe.
  Qed.
  Lemma glG_fuel_supply_issue_2 i q0 q1 a0 a1 b :
    (q0 + q1 = 1)%Qp →
    glG_fuel_supply i a0 q0 ∗ glG_fuel_supply i a1 q1
    ⊢ |==> glG_fuel_supply i (a0 /+ b) q0 ∗ glG_fuel_supply i (a0 /+ b) q1 ∗ glG_fuel i b.
  Proof.
    iIntros (Heq) "H". iDestruct (glG_fuel_supply_add with "H") as "(%&H&%)".
    iMod (glG_fuel_supply_mon _ _ a0 with "H") as "H".
    { destruct H. auto. }
    iMod (glG_fuel_supply_issue _ _ _ _ b with "H") as "[H Hp]"; first done.
    iDestruct (glG_fuel_supply_split _ _ q0 q1 with "H") as "[H0 H1]"; first done.
    by iFrame.
  Qed.

  Lemma glG_fuel_spend i a0 a1 q :
    glG_fuel_supply i a0 q ∗ glG_fuel i a1 ⊢ |==> ∃ a2, ⌜(a1 /+ a2) /≤ a0⌝ ∗ glG_fuel_supply i a2 q.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ k, ∃ a2, (k = (debt a2 q)) ∧ (a1 /+ a2 /≤ a0))
                (λ k, ∃ a2, (k = {[i := (debt a2 q)]}) ∧ (a1 /+ a2 /≤ a0))
             ).
      { eapply debt_pay. }
      { intros. destruct H as (a2&A0&A1). eexists. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplitR; done.
  Qed.
  Lemma glG_fuel_spend_2 i a0 a1 q0 q1 c :
    glG_fuel_supply i a0 q0 ∗ glG_fuel_supply i a1 q1 ∗ glG_fuel i c
    ⊢ |==> ∃ a2, ⌜(c /+ a2) /≤ a0 ∧ (c /+ a2) /≤ a1⌝ ∗ glG_fuel_supply i a2 q0 ∗ glG_fuel_supply i a2 q1.
  Proof.
    iIntros "(H0&H1&H2)". iDestruct (glG_fuel_supply_add with "[H0 H1]") as "(%&H&%)"; first iFrame.
    iMod (glG_fuel_spend with "[H H2]") as "(%&%&H)"; first iFrame.
    iDestruct (glG_fuel_supply_split with "H") as "[H0 H1]"; first reflexivity.
    iModIntro. iFrame. iPureIntro. destruct H. split.
    - etransitivity; [eapply H0 | eauto].
    - etransitivity; [eauto | eapply H].
  Qed.

  Lemma glG_fuel_alloc D k a :
    k ∉ D →
    (own fuel_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own fuel_name (reservation_map_token (A:=bankUR) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           glG_fuel_supply k a 1 ∗ glG_fuel k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (debt a 1 ⋅ cash a) with "Htk") as "[Htk >H]"; auto.
    { rewrite bank_valid_debt_cash. done. }
    iDestruct "H" as "[H1 H2]". rewrite /glG_fuel_supply /glG_fuel.
    by iFrame.
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

  (** Owner rules *)
  Lemma glG_owner_agree k θ0 θ1 q0 q1 :
    glG_owner k θ0 q0 ∗ glG_owner k θ1 q1 ⊢ ⌜ θ0 = θ1 ∧ (q0 + q1 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_owner. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    apply frac_agree_op_valid in Hv. iPureIntro. destruct Hv. done.
  Qed.

  Lemma glG_owner_frac_op k θ q0 q1 q :
    q = (q0 + q1)%Qp →
    glG_owner k θ q0 ∗ glG_owner k θ q1 ⊣⊢ glG_owner k θ q.
  Proof.
    intros; subst. rewrite /glG_owner. iSplit; [iIntros "[H1 H2]" | iIntros "H"].
    - iCombine "H1 H2" as "H". rewrite frac_agree_op. done.
    - rewrite frac_agree_op. iDestruct "H" as "[H1 H2]". iFrame.
  Qed.
  Lemma glG_owner_div_2 k θ q :
    glG_owner k θ (q/2) ∗ glG_owner k θ (q/2) ⊣⊢ glG_owner k θ q.
  Proof. rewrite glG_owner_frac_op; first done. by rewrite Qp.div_2. Qed.
  Lemma glG_owner_valid k θ q :
    glG_owner k θ q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /glG_owner. iIntros "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    by iApply (frac_agree_validI).
  Qed.

  Lemma glG_owner_update_2 k θ0 θ1 q0 q1 θ :
    (q0 + q1 = 1)%Qp →
    glG_owner k θ0 q0 ∗ glG_owner k θ1 q1 ⊢ |==> glG_owner k θ q0 ∗ glG_owner k θ q1.
  Proof.
    rewrite /glG_owner -!own_op -!reservation_map_data_op.
    intros Heq. by apply own_update, reservation_map_update, frac_agree_update_2.
  Qed.
  Lemma glG_owner_update k θ0 θ1 :
    glG_owner k θ0 1 ⊢ |==> glG_owner k θ1 1.
  Proof.
    iIntros "H". iPoseProof (glG_owner_div_2 with "H") as "[H1 H2]".
    iMod (glG_owner_update_2 _ _ _ _ _ θ1 with "[H1 H2]") as "[H1 H2]"; [| iFrame |].
    { by rewrite Qp.div_2. }
    iCombine "H1 H2" as "H". by iPoseProof (glG_owner_div_2 with "H") as "H".
  Qed.

  Lemma glG_owner_alloc D k θ :
    k ∉ D →
    (own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO T)) (⊤ ∖ gset_to_coPset D)))
    ⊢ |==> (own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO T)) (⊤ ∖ gset_to_coPset ({[k]} ∪ D)))) ∗
           glG_owner k θ 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (to_frac_agree 1 (θ : leibnizO _)) with "Htk") as "[Htk >H]"; auto.
    { done. }
    rewrite /glG_owner. by iFrame.
  Qed.

  (** glsat rules *)
  Lemma glsat_elem k Ω :
    glsat Ω ∗ glG_elem k ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /glsat -!lock. iIntros "(Hsat & He)".
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (glG_elem_elem with "[$]") as "%".
    done.
  Qed.
  Lemma glsat_holds_elem k P R Ω :
    glsat Ω ∗ glG_holds k P R ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /glsat -!lock. iIntros "(Hsat & He)".
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (glG_holds_elem with "[$]") as "%".
    by rewrite -Hdom.
  Qed.
  Lemma glsat_elem_cases Ω k :
    glsat Ω ∗ glG_elem k ⊢ ⌜ ∃ d, Ω !! k = Some (obl_live d) ⌝ ∨ glG_unlocked k.
  Proof.
    iIntros "(Hsat & He)". iPoseProof (glsat_elem with "[$]") as "%".
    apply elem_of_dom in H. destruct H.
    rewrite /glsat -!lock.
    iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    destruct x.
    - iLeft. eauto.
    - iPoseProof (big_sepM_delete _ _ _ _ H with "Hm") as "[H _]".
      iDestruct "H" as "(%&%&_&_&_&DA&_)". iRight. by iApply glG_unlocked_auth_done.
  Qed.

  Lemma glsat_obl_is_live Ω k q :
    glsat Ω ∗ glG_elem k ∗ glG_locked k q
    ⊢ ∃ d, ⌜Ω !! k = Some (obl_live d)⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExists o. done.
    - iExFalso. iDestruct "LU" as "(% & % & _ & _ & _ & DONE & _)".
      iPoseProof (glG_locked_done_false with "[Hl DONE]") as "%F"; [iFrame | done].
      iPoseProof (glG_unlocked_auth_done with "[$]") as "#D". done.
  Qed.
  Lemma glsat_obl_is_live_olive Ω k q :
    glsat Ω ∗ glG_elem k ∗ glG_locked k q
    ⊢ ∃ θ α, ⌜Ω !! k = Some (olive θ α)⌝.
  Proof.
    iIntros "H". iPoseProof (glsat_obl_is_live with "H") as "(%&%)".
    iPureIntro. destruct d. eauto.
  Qed.

  Lemma glsat_obl_is_done Ω k (P : prop_of ps) R :
    glsat Ω ∗ glG_holds k P R ∗ glG_unlocked k
    ⊢ ∃ P', ⌜Ω !! k = Some (odone P') ∧ P' ≡ P⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (glsat_holds_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExFalso. iDestruct "LU" as "(LIVE & _)".
      iPoseProof (glG_locked_done_false with "[LIVE Hl]") as "%F"; [iFrame | done].
    - iPoseProof (glG_holds_lookup with "[$]") as "(%&%&%&%&_)".
      iDestruct "LU" as "(%&%&Hg2&%&_)". iPoseProof (glG_holds_agree with "[He Hg2]") as "[% HR]".
      { iFrame "Hg2". eauto. }
      subst. iPureIntro. exists (obl_atom o). destruct o. rewrite -H2 /odone. simpl. split; eauto.
  Qed.

  Lemma glsat_obl_is_done_weak Ω k :
    glsat Ω ∗ glG_elem k ∗ glG_unlocked k
    ⊢ ∃ P, ⌜Ω !! k = Some (obl_done P)⌝.
  Proof.
    iIntros "(Hsat & #He & Hl)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[LU Hm]"; first eauto.
    destruct o.
    - iExFalso. iDestruct "LU" as "(LIVE & _)".
      iPoseProof (glG_locked_done_false with "[LIVE Hl]") as "%F"; [iFrame | done].
    - iExists o. done.
  Qed.
  Lemma glsat_obl_is_done_weak_set Ω D :
    glsat Ω ∗ ([∗ set] k ∈ D, glG_elem k ∗ glG_unlocked k)
    ⊢ [∗ set] k ∈ D, ⌜ ∃ P, Ω !! k = Some (obl_done P) ⌝.
  Proof.
    revert Ω. pattern D. revert D. apply set_ind.
    { solve_proper. }
    { iIntros (Ω) "[Hsat Hs]". rewrite big_opS_empty. done. }
    iIntros (k D NIN IH Ω) "[Hsat Hs]". rewrite !big_sepS_union; [|set_solver|set_solver].
    rewrite !big_sepS_singleton. iDestruct "Hs" as "[[Hi1 Hi2] Hs]".
    iPoseProof (glsat_obl_is_done_weak with "[Hsat Hi1 Hi2]") as "[% %]"; first iFrame. iSplitR.
    - iPureIntro. exists P. done.
    - iApply IH. iFrame.
  Qed.

  Lemma glsat_alloc_obl Ω k θ α P R :
    k ∉ dom Ω →
    glsat Ω
    ⊢ |==> glsat (<[k:=olive θ α]>Ω) ∗
        glG_holds k P R ∗
        glG_elem k ∗
        glG_locked k (1/2)%Qp ∗
        glG_owner k θ (1/2)%Qp ∗
        glG_fuel k α.
  Proof.
    iIntros (Hk) "Hsat".
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iMod (own_update with "HG") as "[HG Hg]".
    { eapply (gmap_view_alloc _ k DfracDiscarded (to_agree $ P, to_agree $ holds_unfold R)); try done.
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; [done | set_solver].
    }
    iMod (glG_locked_alloc _ k with "HS") as "[HS Hs]"; first done.
    iMod (glG_owner_alloc _ k θ with "HO") as "[HO Ho]"; first done.
    iMod (glG_fuel_alloc _ k α with "HP") as "(HP & Hps & Hp)"; first done.
    iPoseProof (glG_locked_div_2 with "Hs") as "[Hs1 Hs2]".
    iPoseProof (glG_owner_div_2 with "Ho") as "[Ho1 Ho2]".
    iMod (glG_elem_alloc _ k (olive θ α) with "HE") as "[HE He]"; first (by apply not_elem_of_dom).
    iModIntro. rewrite /glG_holds. iFrame "Hg Hs2 Hp He Ho2".
    iSplitL "HG".
    { iExists (<[k:=(P, R)]>OProp). iSplitR.
      - iPureIntro. set_solver.
      - rewrite fmap_insert. done.
    }
    rewrite dom_insert_L. iFrame "HS HO HP HE".
    iApply big_sepM_insert.
    { by apply not_elem_of_dom_1. }
    iFrame. eauto.
  Qed.

  Lemma glsat_obl_progress_one Ω k θ α c :
    (Ω !! k = Some (olive θ α)) →
    (/0 /< c) →
    glsat Ω ∗ glG_fuel k c
    ⊢ |==> ∃ α', glsat (<[k:=olive θ α']>Ω) ∗
              ⌜ obl_state_progress (olive θ α) (olive θ α') ⌝.
  Proof.
    intros LU Hc. iIntros "(Hsat & Hp)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "((%&%Hdom&HG) & HS& HO& HP& HE& Hm)".
    iPoseProof (big_sepM_delete with "Hm") as "[Hk Hm]"; [eapply LU |].
    iDestruct "Hk" as "(Hs& Ho& (%&%&Hps))".
    iMod (glG_fuel_spend _ α0 with "[$Hps $Hp]") as "(%&%&Hps)".
    assert (LT : a2 /< α0).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (olive θ a2)) with "[Hm Hs Ho Hps]") as "Hm".
    { apply lookup_delete_eq. }
    { iFrame "Hm". iFrame. simpl. done. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HS HE HP".
    rewrite insert_delete_eq. iFrame. simpl; iPureIntro; split_and !; auto.
    eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma glsat_obl_progress Ω (C : obl_cond) :
    (∀ k o, C k o → ∃ d, o = obl_live d) →
    glsat Ω ∗
    ([∗ map] k ↦ o ∈ Ω, (⌜ C k o ⌝ ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel k c) ∨ (⌜ ¬ C k o ⌝))
    ⊢ |==> ∃ Ω', glsat Ω' ∗ ⌜ Ω ↪ₚ Ω' | C ⌝.
  Proof.
    iIntros (HC) "(Hsat & Cs)".
    iAssert (∃ Ω1 Ω2, (⌜ Ω1 ##ₘ Ω2 ∧ Ω = Ω1 ∪ Ω2 ∧ map_Forall (λ k o, C k o) Ω1 ∧ map_Forall (λ k o, ¬ C k o) Ω2 ⌝) ∗
                      ([∗ map] k ↦ o ∈ Ω1, (⌜ C k o ⌝ ∗ ∃ c, ⌜ /0 /< c ⌝ ∗ glG_fuel k c)) ∗
                      ([∗ map] k ↦ o ∈ Ω2, (⌜ ¬ C k o ⌝))
            )%I with "[Cs]" as "(%& %& (%Disj& %EQO& %CO1& %CO2)& Cs& NCs)".
    { iStopProof. induction Ω using map_ind; iIntros "M".
      { iExists ∅, ∅. rewrite !big_sepM_empty. done. }
      rewrite !big_sepM_insert; auto. iDestruct "M" as "(H& M)".
      iPoseProof (IHΩ with "M") as "(%& %& (%Disj& %EqO& %HC1& %HC2)& M1& M2)". clear IHΩ.
      assert (i ∉ dom Ω1 ∧ i ∉ dom Ω2).
      { subst. apply not_elem_of_dom in H. set_solver + H. }
      destruct H0 as [Nin1 Nin2]. apply not_elem_of_dom in Nin1, Nin2.
      iDestruct "H" as "[(%Ci& (%& %Hc& Bpi)) | %NCi]".
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
    iAssert (|==> ∃ Ω' : obl_states, glsat Ω' ∗ ⌜Ω ↪ₚ Ω' | (λ k _, k ∈ dom Ω1)⌝)%I with "[-]" as ">H"; cycle 1.
    { iDestruct "H" as "(%& S& %)". iModIntro. iFrame. iPureIntro.
      eapply obl_states_cond_rel_iff_lookup; first eapply H.
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
      - econstructor. split; intros; done.
      - econstructor.
    }
    rewrite !big_sepM_insert; auto. apply map_Forall_insert in CO; auto. destruct CO as (Ci& CO).
    iDestruct "M" as "((_& %& %LTc& Bpi)& M)". iMod (IHΩ1 CO with "[$S $M]") as "(%& S& %Prog1)".
    { etransitivity; last eapply Sub. eapply insert_subseteq; auto. }
    clear IHΩ1.
    assert (LUi1 : Ω !! i = Some x).
    { eapply lookup_weaken; last eapply Sub. apply lookup_insert_eq. }
    assert (LUi2 : Ω' !! i = Some x).
    { eapply obl_states_cond_rel_lookup in Prog1. erewrite LUi1 in Prog1. inv Prog1. destruct H2.
      apply not_elem_of_dom in H. apply H2 in H. subst; auto.
    }
    pose proof Ci. apply HC in H0. destruct H0 as ([θ α]& ?).
    iMod (glsat_obl_progress_one with "[$S $Bpi]") as "(%& S& %Progi)"; auto.
    { subst; eauto. }
    iFrame. iPureIntro. assert (Prog2 : Ω' ↪ₚ <[i:=olive θ α']> Ω' | λ k _, k = i).
    { intro j. destruct (decide (j = i)).
      { subst. rewrite LUi2. rewrite lookup_insert_eq. econstructor. simpl. split; intros; done. }
      rewrite lookup_insert_ne; auto. destruct (Ω' !! j) eqn:LUj; econstructor. split; intros; done.
    }
    eapply obl_states_cond_rel_split_cond. 6,7: eauto. all: simpl.
    1,2: intros; solve_decision.
    1: apply _.
    - intros. rewrite dom_insert_L. set_solver.
    - repeat intro. auto.
  Qed.

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
  replace (⊤ ∖ gset_to_coPset (dom (∅ : obl_states))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
