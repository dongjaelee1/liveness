From iris.algebra Require Import gmap_view gset coPset reservation_map dfrac_agree mono_nat.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Import bank.
(* From liris.algebra Require Import auth_mra bank. *)
From liris.algebra Require Export ordinal_wfocm layer.
From liris.base_logic Require Export ghost_lock.
(* From liris.base_logic Require Export invariants ghost_lock. *)

(* FIXME: move to somewhere *)
Section aux.
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

Global Instance ord_ghost_lock_class : ghost_lock_class :=
  Build_ghost_lock_class Ord.t ord_wfocm_pack.

Canonical Structure layerO `{SI : indexT} := leibnizO layer.

(** The ghost state for ghost locks *)
Module glsatGS.

  Class glsatGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    GlsatGpreS {
        glsatGpreS_layer : inG Σ (gmap_viewR gl_id (agreeR (layerO)));
        glsatGpreS_state : inG Σ (reservation_mapUR mono_natUR);
        glsatGpreS_fuel : inG Σ (reservation_mapUR bankUR);
        (* Keep track of the current owner of each lock, if an owner exists *)
        glsatGpreS_owner : inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO ghost_lock_owner)));
      }.

  Class glsatGS `{SI : indexT} (Σ : gFunctors) : Set :=
    GlsatG {
        glsat_inG : glsatGpreS Σ;
        layer_name : gname;
        state_name : gname;
        fuel_name : gname;
        owner_name : gname;
      }.

  Definition glsatΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (gmap_viewR gl_id (agreeR (layerO)));
      GFunctor (reservation_mapUR (mono_natUR));
      GFunctor (reservation_mapUR bankUR);
      GFunctor (reservation_mapUR (dfrac_agreeR $ (leibnizO ghost_lock_owner)))
      ].

  Global Instance subG_glsatΣ `{SI : indexT} {Σ} : subG (glsatΣ) Σ → (glsatGpreS Σ).
  Proof. solve_inG. Qed.

End glsatGS.
Import glsatGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances glsat_inG
  glsatGpreS_layer glsatGpreS_state glsatGpreS_fuel glsatGpreS_owner.

(* Layer: layer of a ghost lock; layer can monotonically grow as version increases. *)
Definition glG_layer `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) (ℓ : layer) : iProp Σ :=
  own layer_name (gmap_view_frag k DfracDiscarded (to_agree (ℓ : layerO))).
Global Typeclasses Opaque glG_layer.
Global Instance: Params (@glG_layer) 3 := {}.

Definition glG_elem `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) : iProp Σ :=
  ∃ ℓ, glG_layer k ℓ.
Global Typeclasses Opaque glG_elem.
Global Instance: Params (@glG_elem) 3 := {}.

Local Definition glG_layer_auth_id `{SI : indexT} `{!glsatGS Σ}
  (m : gmap gl_id layer) : iProp Σ :=
  own layer_name (gmap_view_auth (V:=agreeR (layerO)) (DfracOwn 1) (to_agree <$> m)).

(* State: locked or unlocked for each version *)
Local Definition glG_state_gen `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) (q : dfrac) (n : nat) : iProp Σ :=
  own state_name (reservation_map_data k (●MN{q} n)).
Local Definition glG_state_know_gen `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) (n : nat) : iProp Σ :=
  own state_name (reservation_map_data k (◯MN n)).

Definition glG_locked `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) (q : Qp) : iProp Σ :=
  glG_state_gen k (DfracOwn q) 0.
Global Typeclasses Opaque glG_locked.
Global Instance: Params (@glG_locked) 3 := {}.

Definition glG_locked_know `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) : iProp Σ :=
  glG_state_know_gen k 0.
Global Typeclasses Opaque glG_locked_know.
Global Instance: Params (@glG_locked_know) 3 := {}.

Definition glG_unlocked `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) (q : Qp) : iProp Σ :=
  glG_state_gen k (DfracOwn q) 1.
Global Typeclasses Opaque glG_unlocked.
Global Instance: Params (@glG_unlocked) 3 := {}.

Definition glG_unlocked_know `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) : iProp Σ :=
  glG_state_know_gen k 1.
Global Typeclasses Opaque glG_unlocked_know.
Global Instance: Params (@glG_unlocked_know) 3 := {}.

Definition glG_retired `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) : iProp Σ :=
  glG_state_gen k (DfracDiscarded) 2.
Global Typeclasses Opaque glG_retired.
Global Instance: Params (@glG_retired) 3 := {}.

Local Definition glG_state_token_id `{SI : indexT} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own state_name (reservation_map_token (A:=(mono_natUR)) E).

(* Fuel: manage credits for a lock's fuel *)
Definition glG_fuel `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) (a : ghost_lock_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bankUR) k (cash a)).
Global Typeclasses Opaque glG_fuel.
Global Instance: Params (@glG_fuel) 3 := {}.

Definition glG_fuel_supply `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) (a : ghost_lock_fuel) (q : Qp) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bankUR) k (debt a q)).
Global Typeclasses Opaque glG_fuel_supply.
Global Instance: Params (@glG_fuel_supply) 3 := {}.

Local Definition glG_fuel_token_id `{SI : indexT} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_token (A:=bankUR) E).

(* Owner: tracks the owner thread of a lock *)
Definition glG_owner `{SI : indexT} `{!glsatGS Σ}
  (k : gl_id) (t : ghost_lock_owner) (q : Qp) : iProp Σ :=
  own owner_name (reservation_map_data k (to_frac_agree q (t : leibnizO ghost_lock_owner))).
Global Typeclasses Opaque glG_owner.
Global Instance: Params (@glG_owner) 3 := {}.

Local Definition glG_owner_token_id `{SI : indexT} `{!glsatGS Σ}
  (E : coPset) : iProp Σ :=
  own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO ghost_lock_owner)) E).

(* TODO *)
(* (* Variant: P until Q and then always R. For each version, three cases: *) *)
(* (*    1. locked at version v with P *) *)
(* (*    2. unlocked at version v with Q *) *)
(* (*    3. version v expired (moved on to a bigger version) with R *) *)
(* (*    WP ensures that when unlocking, glG_unlocked with version v is visited at least once *) *)
(* Definition glG_variant_internal `{SI : indexT} `{!glsatGS Σ} *)
(*   (k : gl_id) (q : Qp) (P Q R : iProp Σ) : iProp Σ := *)
(*   (((glG_locked k q ∗ P) ∨ (glG_unlocked k q ∗ Q)) ∨ (glG_retired k ∗ R)). *)

(* Definition glG_variant `{SI : indexT} `{!glsatGS Σ} `{!invGS Σ} *)
(*   (N : namespace) (k : gl_id) (q : Qp) (P Q R : iProp Σ) : iProp Σ := *)
(*   inv N (glG_variant_internal k q P Q R). *)

(* Global protocol to manage ghost locks. *)
Definition glsat `{SI : indexT} `{!glsatGS Σ} `{!ord_mono_fun_class}
  (Ω : ghost_locks) : iProp Σ :=
  locked
    ((∃ (Ls : gmap gl_id layer), (⌜ dom Ω = dom Ls ⌝) ∗ glG_layer_auth_id Ls) ∗
     glG_state_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     glG_fuel_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     glG_owner_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     ([∗ map] k ↦ g ∈ Ω,
        ∃ ℓ, glG_layer k ℓ ∗
        ∃ α, glG_fuel_supply k α (1)%Qp ∗
        ∃ μ, (⌜ (α <= measure ℓ μ)%ord ⌝) ∗
        match (g : ghost_lock (GL:=ord_ghost_lock_class)) with
        | ghost_lock_locked a t =>
            glG_locked k (1/2/2)%Qp ∗
            (⌜ (α <= a)%ord ⌝) ∗
            glG_owner k t (1/2/2)%Qp
        | ghost_lock_unlocked =>
            glG_unlocked k (1/2/2)%Qp ∗
            (∃ t, glG_owner k t (1)%Qp)
        | ghost_lock_retired =>
            glG_retired k ∗
            (∃ t, glG_owner k t (1)%Qp)
        end))%I.

(** Properties *)
Section glsat.
  Context `{SI : indexT} `{!glsatGS Σ} `{OMF : !ord_mono_fun_class}.

  (** Instances *)
  (* Layer *)
  Global Instance glG_layer_persistent k ℓ : Persistent (glG_layer k ℓ).
  Proof. rewrite /glG_layer. apply _. Qed.
  Global Instance glG_layer_timeless k ℓ : Timeless (glG_layer k ℓ).
  Proof. rewrite /glG_layer. apply _. Qed.

  Global Instance glG_elem_persistent k : Persistent (glG_elem k).
  Proof. rewrite /glG_elem. apply _. Qed.
  Global Instance glG_elem_timeless k : Timeless (glG_elem k).
  Proof. rewrite /glG_elem. apply _. Qed.

  Local Instance glG_layer_auth_id_timeless m : Timeless (glG_layer_auth_id m).
  Proof. rewrite /glG_layer_auth_id. apply _. Qed.

  (* State *)
  Global Instance glG_locked_know_persistent k : Persistent (glG_locked_know k).
  Proof. rewrite /glG_locked_know. apply _. Qed.
  Global Instance glG_unlocked_know_persistent k : Persistent (glG_unlocked_know k).
  Proof. rewrite /glG_unlocked_know. apply _. Qed.
  Global Instance glG_retired_persistent k : Persistent (glG_retired k).
  Proof. rewrite /glG_retired. apply _. Qed.

  Global Instance glG_locked_timeless k q : Timeless (glG_locked k q).
  Proof. rewrite /glG_locked. apply _. Qed.
  Global Instance glG_locked_know_timeless k : Timeless (glG_locked_know k).
  Proof. rewrite /glG_locked_know. apply _. Qed.
  Global Instance glG_unlocked_timeless k q : Timeless (glG_unlocked k q).
  Proof. rewrite /glG_unlocked. apply _. Qed.
  Global Instance glG_unlocked_know_timeless k : Timeless (glG_unlocked_know k).
  Proof. rewrite /glG_unlocked_know. apply _. Qed.
  Global Instance glG_retired_timeless k : Timeless (glG_retired k).
  Proof. rewrite /glG_retired. apply _. Qed.

  Global Instance glG_locked_fractional k : Fractional (glG_locked k).
  Proof.
    rewrite /glG_locked /glG_state_gen. intros p q.
    by rewrite -own_op -!reservation_map_data_op -mono_nat_auth_dfrac_op.
  Qed.
  Global Instance glG_locked_as_fractional k q :
    AsFractional (glG_locked k q) (glG_locked k) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance glG_unlocked_fractional k : Fractional (glG_unlocked k).
  Proof.
    rewrite /glG_unlocked /glG_state_gen. intros p q.
    by rewrite -own_op -!reservation_map_data_op -mono_nat_auth_dfrac_op.
  Qed.
  Global Instance glG_unlocked_as_fractional k q :
    AsFractional (glG_unlocked k q) (glG_unlocked k) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance glG_state_token_id_timeless E : Timeless (glG_state_token_id E).
  Proof. rewrite /glG_state_token_id. apply _. Qed.

  (* Fuel *)
  Global Instance glG_fuel_timeless k a : Timeless (glG_fuel k a).
  Proof. rewrite /glG_fuel. apply _. Qed.
  Global Instance glG_fuel_supply_timeless k a q : Timeless (glG_fuel_supply k a q).
  Proof. rewrite /glG_fuel_supply. apply _. Qed.

  Global Instance glG_fuel_supply_fractional k a : Fractional (glG_fuel_supply k a).
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

  (* (* Variant *) *)
  (* Global Instance glG_variant_contractive_1 N k v q Q R : Contractive (λ P, @glG_variant SI Σ _ _ N k v q P Q R). *)
  (* Proof. rewrite /glG_variant /glG_variant_internal. solve_contractive. Qed. *)
  (* Global Instance glG_variant_contractive_2 N k v q P R : Contractive (λ Q, @glG_variant SI Σ _ _ N k v q P Q R). *)
  (* Proof. rewrite /glG_variant /glG_variant_internal. solve_contractive. Qed. *)
  (* Global Instance glG_variant_contractive_3 N k v q P Q : Contractive (λ R, @glG_variant SI Σ _ _ N k v q P Q R). *)
  (* Proof. rewrite /glG_variant /glG_variant_internal. solve_contractive. Qed. *)

  (* Global Instance glG_variant_persistent N k v q P Q R : Persistent (glG_variant N k v q P Q R). *)
  (* Proof. apply _. Qed. *)

  (* Sat *)
  Global Instance glsat_timeless Ω : Timeless (glsat Ω).
  Proof. rewrite /glsat -lock. apply _. Qed.

  (** Layer rules *)
  Lemma glG_layer_lookup (Ls : gmap gl_id layer) k ℓ :
    glG_layer_auth_id Ls ∗ glG_layer k ℓ
    ⊢ ⌜ Ls !! k = Some ℓ ⌝.
  Proof.
    rewrite /glG_layer_auth_id /glG_layer. iIntros "(H1& H2)". iStopProof.
    rewrite -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
    case: (Ls !! k)=> [Q|] /=; last first.
    { by iDestruct "HQ'" as %?. }
    iDestruct "HQ'" as %[= <-].
    rewrite !to_agree_includedI; simpl.
    iPoseProof (internal_eq_sym with "Hincl") as "H". iPoseProof (discrete_eq with "H") as "%HG".
    rewrite HG. done.
  Qed.

  Lemma glG_layer_agree k ℓ1 ℓ2 :
    glG_layer k ℓ1 ∗ glG_layer k ℓ2 ⊢ ⌜ ℓ1 = ℓ2 ⌝.
  Proof.
    rewrite /glG_layer. iIntros "(H1& H2)". iStopProof.
    rewrite -own_op own_valid gmap_view_frag_op_validI.
    iIntros "(_&H)". rewrite to_agree_op_validI. iPoseProof (discrete_eq with "H") as "%". done.
  Qed.

  Lemma glG_layer_elem k ℓ :
    glG_layer k ℓ ⊢ glG_elem k.
  Proof. rewrite /glG_elem. eauto. Qed.

  Lemma glG_layer_alloc (Ls : gmap gl_id layer) k ℓ :
    Ls !! k = None →
    glG_layer_auth_id Ls
    ⊢ |==> glG_layer_auth_id (<[k:=ℓ]>Ls) ∗
        glG_layer k ℓ.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "[H Hw]".
    { eapply (gmap_view_alloc _ k (DfracDiscarded) (to_agree $ (ℓ : leibnizO _))); try done.
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; first done. by apply not_elem_of_dom. }
    rewrite /glG_layer_auth_id /glG_layer. rewrite fmap_insert. by iFrame.
  Qed.

  (** State rules *)
  Local Lemma glG_state_gen_valid_2 k dq1 dq2 n1 n2 :
    glG_state_gen k dq1 n1 ∗ glG_state_gen k dq2 n2
    ⊢ ⌜ (n1 = n2) ∧ ✓ (dq1 ⋅ dq2) ⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv".
    apply reservation_map_data_valid, mono_nat_auth_dfrac_op_valid in Hv.
    destruct Hv. subst. done.
  Qed.
  Local Lemma glG_state_gen_valid_1 k dq n :
    glG_state_gen k dq n ⊢ ⌜ ✓ dq ⌝.
  Proof.
    iIntros "H". iPoseProof (own_valid with "H") as "%Hv".
    apply reservation_map_data_valid, mono_nat_auth_dfrac_valid in Hv. done.
  Qed.

  Local Lemma glG_state_gen_update_2 k q1 q2 n1 n2 m :
    (n1 ≤ m) →
    (q1 + q2 = 1)%Qp →
    glG_state_gen k (DfracOwn q1) n1 ∗ glG_state_gen k (DfracOwn q2) n2
    ⊢ |==> glG_state_gen k (DfracOwn q1) m ∗ glG_state_gen k (DfracOwn q2) m.
  Proof.
    iIntros (Hle Heq) "H". iPoseProof (glG_state_gen_valid_2 with "H") as "%". destruct H; subst.
    rewrite /glG_state_gen -!own_op -!reservation_map_data_op.
    iStopProof. apply own_update, reservation_map_update.
    rewrite -!mono_nat_auth_dfrac_op !dfrac_op_own !Heq. apply mono_nat_update. auto.
  Qed.
  Local Lemma glG_state_gen_update_1 k n m :
    (n ≤ m) →
    glG_state_gen k (DfracOwn 1) n ⊢ |==> glG_state_gen k (DfracOwn 1) m.
  Proof.
    iIntros (Hle) "[H1 H2]". iMod (glG_state_gen_update_2 with "[$H1 $H2]") as "[H1 H2]".
    1: eauto.
    { apply Qp.div_2. }
    by iCombine "H1 H2" as "H".
  Qed.

  Lemma glG_locked_to_unlocked_2 k q1 q2 :
    (q1 + q2 = 1)%Qp →
    glG_locked k q1 ∗ glG_locked k q2 ⊢ |==> glG_unlocked k q1 ∗ glG_unlocked k q2.
  Proof. apply glG_state_gen_update_2. lia. Qed.
  Lemma glG_locked_to_unlocked k :
    glG_locked k 1 ⊢ |==> glG_unlocked k 1.
  Proof. apply glG_state_gen_update_1. lia. Qed.
  Lemma glG_unlocked_to_retired_2 k q1 q2 :
    (q1 + q2 = 1)%Qp →
    glG_unlocked k q1 ∗ glG_unlocked k q2 ⊢ |==> glG_retired k.
  Proof.
    iIntros (Hq) "H". iMod (glG_state_gen_update_2 _ _ _ _ _ 2 with "H") as "[H1 H2]"; auto.
    iCombine "H1 H2" as "H". rewrite Hq.
    iStopProof. apply own_update, reservation_map_update, mono_nat_auth_persist.
  Qed.
  Lemma glG_unlocked_to_retired k :
    glG_unlocked k 1 ⊢ |==> glG_retired k.
  Proof.
    iIntros "[H1 H2]". iMod (glG_unlocked_to_retired_2 with "[$H1 $H2]") as "$".
    { apply Qp.div_2. }
    done.
  Qed.

  Lemma glG_locked_frac_valid k q :
    glG_locked k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof. apply glG_state_gen_valid_1. Qed.
  Lemma glG_unlocked_frac_valid k q :
    glG_unlocked k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof. apply glG_state_gen_valid_1. Qed.
  Lemma glG_locked_unlocked_false k q1 q2 :
    glG_locked k q1 ∗ glG_unlocked k q2 ⊢ False.
  Proof.
    iIntros "H". iPoseProof (glG_state_gen_valid_2 with "H") as "%". by destruct H.
  Qed.
  Lemma glG_unlocked_retired_false k q :
    glG_unlocked k q ∗ glG_retired k ⊢ False.
  Proof.
    iIntros "H". iPoseProof (glG_state_gen_valid_2 with "H") as "%". by destruct H.
  Qed.
  Lemma glG_locked_retired_false k q :
    glG_locked k q ∗ glG_retired k ⊢ False.
  Proof.
    iIntros "H". iPoseProof (glG_state_gen_valid_2 with "H") as "%". by destruct H.
  Qed.

  (* Rules for know (lower bounds). *)
  Local Lemma glG_state_gen_know_valid k dq n1 n2 :
    glG_state_gen k dq n1 ∗ glG_state_know_gen k n2
    ⊢ ⌜ (n2 ≤ n1) ∧ ✓ dq ⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv".
    apply reservation_map_data_valid, mono_nat_both_dfrac_valid in Hv.
    destruct Hv. done.
  Qed.
  Lemma glG_locked_unlocked_know_false k q :
    glG_locked k q ∗ glG_unlocked_know k ⊢ False.
  Proof.
    iIntros "H". iPoseProof (glG_state_gen_know_valid with "H") as "%". destruct H. lia.
  Qed.

  Local Lemma glG_state_gen_get_know k dq n :
    glG_state_gen k dq n ⊢ glG_state_know_gen k n.
  Proof.
    rewrite /glG_state_gen /glG_state_know_gen. rewrite mono_nat_auth_lb_op.
    iIntros "[H1 H2]". done.
  Qed.
  Lemma glG_locked_get_know k q :
    glG_locked k q ⊢ glG_locked_know k.
  Proof. apply glG_state_gen_get_know. Qed.
  Lemma glG_unlocked_get_know k q :
    glG_unlocked k q ⊢ glG_unlocked_know k.
  Proof. apply glG_state_gen_get_know. Qed.

  Lemma glG_state_alloc D k (s : nat) :
    k ∉ D →
    glG_state_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> glG_state_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        glG_state_gen k (DfracOwn 1) s.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN{#1} s) with "Htk") as "[Htk >H]"; auto.
    { apply mono_nat_auth_valid. }
    by iFrame.
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
                (λ m, ∃ a2, (m = (reservation_map_data k (debt a2 q))) ∧ (a1 w+ a2 w≤ a0))).
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

  (* (** glG_variant rules *) *)
  (* Lemma glG_variant_acc E N k v q P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q P Q R ={E,E ∖ ↑N}=∗ *)
  (*   ▷ glG_variant_internal k v q P Q R ∗ *)
  (*   (▷ glG_variant_internal k v q P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "#GU". iPoseProof (inv_acc with "GU") as "$"; eauto. *)
  (* Qed. *)

  (* Lemma glG_variant_acc_version E N k v q1 q2 P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q1 P Q R -∗ glG_version k v q2 ={E,E ∖ ↑N}=∗ *)
  (*   (▷ (glG_version k v q2 ∗ *)
  (*       ((glG_locked k v q1 ∗ P) ∨ *)
  (*          (glG_unlocked k v ∗ Q)))) ∗ *)
  (*   (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "#GU GV". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto. *)
  (*   - iModIntro. iSplitR "ACC". *)
  (*     + iNext. iDestruct "H" as "[H | H]"; iFrame. *)
  (*     + iIntros "H". iApply "ACC". done. *)
  (*   - iModIntro. iSplitR "ACC"; last iFrame. *)
  (*     iNext. iDestruct "H" as "(_& Gvd& _)". *)
  (*     iPoseProof (glG_version_expired_valid with "[$GV $Gvd]") as "%". lia. *)
  (* Qed. *)

  (* Lemma glG_variant_acc_locked E N k v q1 q2 P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q1 P Q R -∗ glG_locked k v q2 *)
  (*   ={E,E ∖ ↑N}=∗ *)
  (*   (▷ (glG_locked k v q2 ∗ *)
  (*       ((glG_locked k v q1 ∗ P) ∨ *)
  (*          (glG_unlocked k v ∗ glG_version_expired k v ∗ R)))) ∗ *)
  (*   (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "#GU GV". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto. *)
  (*   - iModIntro. iSplitR "ACC". *)
  (*     + iNext. iDestruct "H" as "[H | H]"; first iFrame. *)
  (*       iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done. *)
  (*     + done. *)
  (*   - iModIntro. iSplitR "ACC"; iFrame. *)
  (* Qed. *)

  (* Lemma glG_variant_acc_unlocked E N k v q1 P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q1 P Q R -∗ glG_unlocked k v *)
  (*   ={E,E ∖ ↑N}=∗ *)
  (*   (▷ (Q ∨ (glG_unlocked k v ∗ glG_version_expired k v ∗ R))) ∗ *)
  (*   (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "#GU GV". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto. *)
  (*   - iModIntro. iSplitR "ACC"; last done. *)
  (*     iNext. iDestruct "H" as "[H | [_ $]]". *)
  (*     iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done. *)
  (*   - iModIntro. iSplitR "ACC"; iFrame. *)
  (* Qed. *)
  (* Lemma glG_variant_acc_unlocked_pin E N k v q1 P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q1 P Q R -∗ glG_unlocked k v -∗ glG_version_pin k v *)
  (*   ={E,E ∖ ↑N}=∗ *)
  (*   (▷ Q) ∗ *)
  (*   (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "#GU GV Gvp". iMod (glG_variant_acc with "GU") as "[[H | H] ACC]"; first auto. *)
  (*   - iModIntro. iSplitR "ACC"; last done. *)
  (*     iNext. iDestruct "H" as "[H | [_ $]]". *)
  (*     iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done. *)
  (*   - iModIntro. iSplitR "ACC"; last iFrame. *)
  (*     iNext. iDestruct "H" as "(_& #Gvd& _)". *)
  (*     iPoseProof (glG_version_pin_expired_valid with "[$Gvp $Gvd]") as "%". lia. *)
  (* Qed. *)

  (* Lemma glG_variant_acc_version_locked E N k v q1 q2 q3 P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q1 P Q R -∗ glG_version k v q2 -∗ glG_locked k v q3 ={E,E ∖ ↑N}=∗ *)
  (*   ▷ (glG_version k v q2 ∗ glG_locked k v q3 ∗ (glG_locked k v q1 ∗ P)) ∗ *)
  (*   (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "#GU GV GL". iMod (glG_variant_acc_version with "GU GV") as "[H ACC]"; first auto. *)
  (*   iModIntro. iSplitR "ACC". *)
  (*   - iNext. iDestruct "H" as "(Gv& [H | H])"; first iFrame. *)
  (*     iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done. *)
  (*   - done. *)
  (* Qed. *)

  (* Lemma glG_variant_acc_version_unlocked E N k v q1 q2 P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q1 P Q R -∗ glG_version k v q2 -∗ glG_unlocked k v ={E,E ∖ ↑N}=∗ *)
  (*   ▷ (glG_version k v q2 ∗ glG_unlocked k v ∗ (glG_unlocked k v ∗ Q)) ∗ *)
  (*   (▷ glG_variant_internal k v q1 P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "#GU GV GL". iMod (glG_variant_acc_version with "GU GV") as "[H ACC]"; first auto. *)
  (*   iModIntro. iSplitR "ACC". *)
  (*   - iNext. iDestruct "H" as "(Gv& [H | H])"; last iFrame. *)
  (*     iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done. *)
  (*   - done. *)
  (* Qed. *)

  (* (* Allocates *) *)
  (* Lemma glG_variant_alloc_locked E N k v q P Q R : *)
  (*   (▷ (glG_locked k v q ∗ P)) ={E}=∗ glG_variant N k v q P Q R. *)
  (* Proof. iIntros "H". iApply inv_alloc. iFrame. Qed. *)
  (* Lemma glG_variant_alloc_unlocked E N k v q P Q R : *)
  (*   (▷ (glG_unlocked k v ∗ Q)) ={E}=∗ glG_variant N k v q P Q R. *)
  (* Proof. iIntros "H". iApply inv_alloc. iFrame. Qed. *)
  (* Lemma glG_variant_alloc_expired E N k v q P Q R : *)
  (*   (▷ (glG_unlocked k v ∗ glG_version_expired k v ∗ R)) ={E}=∗ glG_variant N k v q P Q R. *)
  (* Proof. iIntros "H". iApply inv_alloc. iFrame. Qed. *)

  (** glsat rules *)
  Lemma glsat_elem Ω k :
    glsat Ω ∗ glG_elem k ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /glG_elem.
    rewrite /glsat -!lock. iIntros "(Hsat& (%& #Ge))".
    iDestruct "Hsat" as "((%& %& HE)& HS& HF& HO& HM)".
    iPoseProof (glG_layer_lookup with "[$]") as "%".
    rewrite H. apply elem_of_dom_2 in H0. auto.
  Qed.
  Lemma glsat_elem_lookup Ω k :
    glsat Ω ∗ glG_elem k
    ⊢ (⌜ ∃ a t, Ω !! k = Some (ghost_lock_locked a t) ⌝) ∨
        (⌜ Ω !! k = Some (ghost_lock_unlocked) ⌝) ∨
        (glG_retired k ∗ (⌜ Ω !! k = Some (ghost_lock_retired) ⌝)).
  Proof.
    iIntros "(Hsat & #Ge)". iPoseProof (glsat_elem with "[$]") as "%".
    apply elem_of_dom in H. destruct H.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete _ _ _ _ H with "HM") as "[H _]".
    iDestruct "H" as "(%& #Gy& %& Gfs& %& %& H)". destruct x.
    - iLeft. iPureIntro. eauto.
    - eauto.
    - iDestruct "H" as "(#Gu& _)"; eauto.
  Qed.

  Lemma glsat_lookup_locked Ω k q :
    glsat Ω ∗ glG_elem k ∗ glG_locked k q
    ⊢ ∃ a t, ⌜Ω !! k = Some (ghost_lock_locked a t)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o; first eauto.
    - iDestruct "Mk" as "(Gu& _)". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - iDestruct "Mk" as "(Gr& _)". iPoseProof (glG_locked_retired_false with "[$]") as "%". done.
  Qed.

  Lemma glsat_lookup_unlocked Ω k q :
    glsat Ω ∗ glG_elem k ∗ glG_unlocked k q
    ⊢ ⌜ Ω !! k = Some (ghost_lock_unlocked) ⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o; [| eauto |].
    - iDestruct "Mk" as "(Gu& _)". iPoseProof (glG_locked_unlocked_false with "[$]") as "%". done.
    - iDestruct "Mk" as "(Gr& _)". iPoseProof (glG_unlocked_retired_false with "[$]") as "%". done.
  Qed.

  Lemma glsat_lookup_retired Ω k :
    glsat Ω ∗ glG_elem k ∗ glG_retired k
    ⊢ ⌜ Ω !! k = Some (ghost_lock_retired) ⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o; last eauto.
    - iDestruct "Mk" as "(Gu& _)". iPoseProof (glG_locked_retired_false with "[$]") as "%". done.
    - iDestruct "Mk" as "(Gr& _)". iPoseProof (glG_unlocked_retired_false with "[$]") as "%". done.
  Qed.

  Lemma glsat_lookup_owner Ω k t q :
    glsat Ω ∗ glG_elem k ∗ glG_owner k t q
    ⊢ ∃ a, ⌜Ω !! k = Some (ghost_lock_locked a t)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Go)".
    iPoseProof (glsat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o.
    - iDestruct "Mk" as "(Gl& %& Go2)".
      iPoseProof (glG_owner_agree with "[$Go $Go2]") as "(%&%)". subst. eauto.
    - iDestruct "Mk" as "(_& %& Go2)".
      iPoseProof (glG_owner_agree with "[$Go $Go2]") as "(%&%)". apply Qp.not_add_le_r in H0. done.
    - iDestruct "Mk" as "(_& %& Go2)".
      iPoseProof (glG_owner_agree with "[$Go $Go2]") as "(%&%)". apply Qp.not_add_le_r in H0. done.
  Qed.

  Lemma glsat_alloc_ghost_lock_locked Ω k ℓ (μ : measurable_syntax) t :
    k ∉ dom Ω →
    glsat Ω
    ⊢ |==> glsat (<[k:=(ghost_lock_locked (measure ℓ μ) t)]>Ω) ∗
        glG_layer k ℓ ∗
        glG_elem k ∗
        glG_locked k (1/2 + 1/2/2)%Qp ∗
        glG_fuel k (measure ℓ μ) ∗
        glG_owner k t (1/2 + 1/2/2)%Qp ∗
        (⌜ Ω ↪ₐ (<[k:=(ghost_lock_locked (measure ℓ μ) t)]>Ω) ⌝).
  Proof.
    iIntros (Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iDestruct "HE" as "(%& %Dom& HE)".
    iMod (glG_layer_alloc _ k ℓ with "HE") as "[HE #Gwf]".
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    iMod (glG_state_alloc _ k 0 with "HS") as "[HS Gl]"; first auto.
    iAssert (glG_locked k 1)%I with "Gl" as "Gl".
    iMod (glG_fuel_alloc _ k (measure ℓ μ) with "HF") as "(HF& Gfsp& Gf)"; first set_solver.
    iMod (glG_owner_alloc _ k t with "HO") as "[HO Go]"; first auto.
    iDestruct "Gl" as "[Gl1 [Gl2 Gl']]". iCombine "Gl1 Gl2" as "Gl".
    iDestruct "Go" as "[Go1 [Go2 Go']]". iCombine "Go1 Go2" as "Go".
    iPoseProof (glG_layer_elem with "Gwf") as "#Ge".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HF HO". iFrame "Ge Gl Gf Go Gwf".
    iSplitL; cycle 1.
    { iPureIntro. exists k. split; eauto. }
    iSplitR.
    { rewrite dom_insert_L Dom. done. }
    iApply big_sepM_insert; first auto. iFrame. eauto.
  Qed.

  Lemma glsat_alloc_ghost_lock_unlocked Ω k :
    k ∉ dom Ω →
    glsat Ω
    ⊢ |==> glsat (<[k:=(ghost_lock_unlocked)]>Ω) ∗
        glG_elem k ∗
        glG_unlocked k (1/2 + 1/2/2)%Qp ∗
        (⌜ Ω ↪ₐ (<[k:=(ghost_lock_unlocked)]>Ω) ⌝).
  Proof.
    iIntros (Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iDestruct "HE" as "(%& %Dom& HE)".
    iMod (glG_layer_alloc _ k 0%ordi with "HE") as "[HE #Gwf]".
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    iMod (glG_state_alloc _ k 1 with "HS") as "[HS Gl]"; first auto.
    iAssert (glG_unlocked k 1)%I with "Gl" as "Gl".
    iMod (glG_fuel_alloc _ k 0%ord with "HF") as "(HF& Gfsp& Gf)"; first set_solver.
    iMod (glG_owner_alloc _ k inhabitant with "HO") as "[HO Go]"; first auto.
    iDestruct "Gl" as "[Gl1 [Gl2 Gl']]". iCombine "Gl1 Gl2" as "Gl".
    iPoseProof (glG_layer_elem with "Gwf") as "#Ge".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HF HO". iFrame "Ge Gl".
    iSplitL; cycle 1.
    { iPureIntro. exists k. split; eauto. }
    iSplitR.
    { rewrite dom_insert_L Dom. done. }
    iApply big_sepM_insert; first auto. iFrame. iFrame "Gwf".
    iExists 0%M. iPureIntro. apply Ord.O_bot.
  Qed.

  Lemma glsat_alloc_ghost_lock_retired Ω k :
    k ∉ dom Ω →
    glsat Ω
    ⊢ |==> glsat (<[k:=(ghost_lock_retired)]>Ω) ∗
        glG_elem k ∗
        glG_retired k ∗
        (⌜ Ω ↪ₐ (<[k:=(ghost_lock_retired)]>Ω) ⌝).
  Proof.
    iIntros (Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iDestruct "HE" as "(%& %Dom& HE)".
    iMod (glG_layer_alloc _ k 0%ordi with "HE") as "[HE #Gwf]".
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    iMod (glG_state_alloc _ k 2 with "HS") as "[HS Gl]"; first auto.
    iAssert (|==> glG_retired k)%I with "[Gl]" as ">#Gl".
    { rewrite /glG_retired. iClear "Gwf". iStopProof.
      apply own_update, reservation_map_update, mono_nat_auth_persist. }
    iMod (glG_fuel_alloc _ k 0%ord with "HF") as "(HF& Gfsp& Gf)"; first set_solver.
    iMod (glG_owner_alloc _ k inhabitant with "HO") as "[HO Go]"; first auto.
    iPoseProof (glG_layer_elem with "Gwf") as "#Ge".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HF HO". iFrame "Ge Gl".
    iSplitL; cycle 1.
    { iPureIntro. exists k. split; eauto. }
    iSplitR.
    { rewrite dom_insert_L Dom. done. }
    iApply big_sepM_insert; first auto. iFrame. iFrame "Gwf Gl".
    iExists 0%M. iPureIntro. apply Ord.O_bot.
  Qed.

  (** ghost lock step rules: progress, unlock, retire *)
  Lemma glsat_progress_one Ω k a t c :
    (Ω !! k = Some (ghost_lock_locked a t)) →
    (Ord.O < c)%ord →
    glsat Ω ∗ glG_fuel k c
    ⊢ |==> ∃ a', glsat (<[k:=(ghost_lock_locked a' t)]>Ω) ∗
              (⌜ ghost_lock_progress (ghost_lock_locked a t) (ghost_lock_locked a' t) ⌝).
  Proof.
    intros LU Hc. iIntros "(Hsat & Gf)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& %LEa& Gok)".
    iMod (glG_fuel_spend with "[$Gfs $Gf]") as "(%&%&Gfs)".
    assert (LT : a2 w< α).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (ghost_lock_locked a2 t)) with "[HM Glk Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gy". iExists μ. iPureIntro. split; last done.
      etrans; last eauto. apply WFOCM.lt_le. auto. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HE HS HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. econstructor. eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma glsat_progress Ω (C : gl_cond) :
    (∀ k g, C k g → ∃ a o, g = (ghost_lock_locked a o)) →
    glsat Ω ∗
    ([∗ map] k ↦ g ∈ Ω, (⌜ C k g ⌝ ∗ ∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ glG_fuel k c) ∨ (⌜ ¬ C k g ⌝))
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
    pose proof Ci. apply HC in H0. destruct H0 as (a& t& ?). subst.
    iMod (glsat_progress_one with "[$S $Bpi]") as "(%& S& %Progi)"; auto.
    { eauto. }
    iFrame. iPureIntro. simpl. assert (Prog2 : Ω' ↪ₚ <[i:=(ghost_lock_locked a' t)]> Ω' | λ k _, k = i).
    { split.
      - intro j. destruct (decide (j = i)).
        { subst. rewrite LUi2. rewrite lookup_insert_eq. econstructor. left. split; auto. by econstructor 1. }
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

  Lemma glsat_progress_one_owner Ω k a t1 t2 c :
    (Ω !! k = Some (ghost_lock_locked a t1)) →
    (Ord.O < c)%ord →
    glsat Ω ∗ glG_owner k t1 (1/2 + 1/2/2)%Qp ∗ glG_fuel k c
    ⊢ |==> ∃ a', glsat (<[k:=(ghost_lock_locked a' t2)]>Ω) ∗ glG_owner k t2 (1/2 + 1/2/2)%Qp ∗
              (⌜ ghost_lock_progress (ghost_lock_locked a t1) (ghost_lock_locked a' t2) ⌝).
  Proof.
    intros LU Hc. iIntros "(Hsat& Go& Gf)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& %LEa& Gok)".
    iMod (glG_fuel_spend with "[$Gfs $Gf]") as "(%&%&Gfs)".
    assert (LT : a2 w< α).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iMod (glG_owner_update_2 _ _ _ _ _ t2 with "[$Go $Gok]") as "[Go Gok]".
    { rewrite -Qp.add_assoc !Qp.div_2. done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (ghost_lock_locked a2 t2)) with "[HM Glk Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gy". iExists μ. iPureIntro. split; last done.
      etrans; last eauto. apply WFOCM.lt_le. auto. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HE HS HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. econstructor. eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma Qp_add_help_1 : (1 / 2 + 1 / 2 / 2 + 1 / 2 / 2 = 1)%Qp.
  Proof. by rewrite -Qp.add_assoc !Qp.div_2. Qed.

  Lemma glsat_unlock Ω k t :
    glsat Ω ∗ glG_elem k ∗ glG_locked k (1/2 + 1/2/2)%Qp ∗ glG_owner k t (1/2 + 1/2/2)%Qp
    ⊢ |==> glsat (<[k:=(ghost_lock_unlocked)]>Ω) ∗
        glG_unlocked k (1/2 + 1/2/2)%Qp ∗
        (⌜ ∀ a, ghost_lock_unlock (ghost_lock_locked a t) (ghost_lock_unlocked) ⌝).
  Proof.
    iIntros "(Hsat& #Ge& Gl& Go)".
    iPoseProof (glsat_lookup_locked with "[$Hsat $Ge $Gl]") as "(%&%& %LU)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& %LEa& Gok)".
    iMod (glG_locked_to_unlocked_2 with "[$Gl $Glk]") as "[Gu Guk]".
    { apply Qp_add_help_1. }
    iPoseProof (glG_owner_agree with "[$Go $Gok]") as "(%& %)". clear H0. subst t0.
    iCombine "Go Gok" as "Gok". rewrite Qp_add_help_1.
    iModIntro.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (ghost_lock_unlocked)) with "[HM Guk Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gy". eauto. }
    rewrite dom_insert_lookup_L; last done. iFrame "HE HS HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. intros. econstructor.
  Qed.

  Lemma glsat_retire Ω k :
    glsat Ω ∗ glG_elem k ∗ glG_unlocked k (1/2 + 1/2/2)%Qp
    ⊢ |==> glsat (<[k:=(ghost_lock_retired)]>Ω) ∗
        glG_retired k ∗
        (⌜ ghost_lock_retire (ghost_lock_unlocked) (ghost_lock_retired) ⌝).
  Proof.
    iIntros "(Hsat& #Ge& Gl)".
    iPoseProof (glsat_lookup_unlocked with "[$Hsat $Ge $Gl]") as "%LU".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& Gok)".
    iMod (glG_unlocked_to_retired_2 with "[$Gl $Glk]") as "#Gr".
    { apply Qp_add_help_1. }
    iModIntro.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (ghost_lock_retired)) with "[HM Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gy Gr". eauto. }
    rewrite dom_insert_lookup_L; last done. iFrame "HE HS HF HO".
    rewrite insert_delete_eq. iFrame. iFrame "Gr".
    iPureIntro. econstructor.
  Qed.

  (* (** Rules for glG_variant and glsat *) *)
  (* Lemma glsat_variant_acc_locked Ω k v q0 q1 E N P Q R : *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q0 P Q R ∗ *)
  (*   glsat Ω ∗ glG_elem k ∗ glG_locked k v q1 *)
  (*   ⊢ |={E,E ∖ ↑N}=> *)
  (*         ▷ (glsat Ω ∗ glG_locked k v q1 ∗ (glG_locked k v q0 ∗ P)) ∗ *)
  (*         (▷ glG_variant_internal k v q0 P Q R ={E ∖ ↑N,E}=∗ True). *)
  (* Proof. *)
  (*   iIntros (HE) "(#Gvar& G& #Ge& Gl)". *)
  (*   iMod (glG_variant_acc with "Gvar") as "[[H | H] ACC]"; first auto. *)
  (*   - iModIntro. iSplitR "ACC". *)
  (*     + iNext. iDestruct "H" as "[H | H]"; first iFrame. *)
  (*       iDestruct "H" as "[H _]". iPoseProof (glG_locked_unlocked_false with "[$Gl $H]") as "%". done. *)
  (*     + done. *)
  (*   - iModIntro. iSplitR "ACC"; last iFrame. iNext. iDestruct "H" as "(_& #Gvd& _)". *)
  (*     iPoseProof (glsat_lookup_version_expired with "[$G $Ge $Gvd]") as "%". destruct H as (?&?&?&?). *)
  (*     iPoseProof (glsat_lookup_locked with "[$G $Ge $Gl]") as "%". destruct H1 as (?&?&?). *)
  (*     rewrite H in H1. inv H1. lia. *)
  (* Qed. *)

  (* Lemma glsat_variant_unlock Ω k v t q0 q1 E N P Q R : *)
  (*   (q0 + q1 = 1/2 + 1/2/2)%Qp → *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v q0 P Q R ∗ *)
  (*   glsat Ω ∗ *)
  (*   glG_elem k ∗ glG_locked k v q1 ∗ glG_owner k t (1/2 + 1/2/2)%Qp *)
  (*   ⊢ |={E,E ∖ ↑N}=> *)
  (*         ▷ ((glsat Ω ∗ glG_locked k v (1/2 + 1/2/2)%Qp ∗ glG_owner k t (1/2 + 1/2/2)%Qp ∗ P) ∗ *)
  (*            ((glsat Ω ∗ glG_locked k v (1/2 + 1/2/2)%Qp ∗ glG_owner k t (1/2 + 1/2/2)%Qp ∗ ▷ Q) *)
  (*             ={E ∖ ↑N,E}=∗ *)
  (*             glsat (<[k:=(v, ghost_lock_unlocked)]>Ω) ∗ *)
  (*             glG_unlocked k v ∗ *)
  (*             (⌜ ∀ a, ghost_lock_step (v, ghost_lock_locked a t) (v, ghost_lock_unlocked) ⌝))). *)
  (* Proof. *)
  (*   iIntros (Hq HE) "(#Gvar& G& #Ge& Gl& Go)". *)
  (*   iMod (glsat_variant_acc_locked with "[$Gvar $G $Ge $Gl]") as "[H ACC]"; first auto. *)
  (*   iModIntro. iNext. iDestruct "H" as "($& Gl1& Gl2& $)". *)
  (*   iCombine "Gl2 Gl1" as "Gl". rewrite Hq. iFrame "Gl Go". *)
  (*   iIntros "(G& Gl& Go& HQ)". *)
  (*   iMod (glsat_unlock with "[$G $Ge $Gl $Go]") as "($& #Gu& $)". iFrame "Gu". *)
  (*   iApply "ACC". iNext. iLeft. iRight. iFrame. eauto. *)
  (* Qed. *)

  (* Lemma glsat_variant_lock Ω k v1 v2 ℓ μ t q0 q1 E N (P1 Q1 R1 P2 Q2 R2 : iProp Σ) : *)
  (*   (q0 + q1 = 1/2 + 1/2/2)%Qp → *)
  (*   v1 < v2 → *)
  (*   ↑N ⊆ E → *)
  (*   glG_variant N k v1 q0 P1 Q1 R1 ∗ *)
  (*   glsat Ω ∗ *)
  (*   glG_layer k ℓ ∗ glG_unlocked k v1 ∗ glG_version k v1 (1/2 + 1/2/2)%Qp *)
  (*   ⊢ |={E,E ∖ ↑N}=> *)
  (*         ▷ ((glsat Ω ∗ glG_version k v1 (1/2 + 1/2/2)%Qp ∗ Q1) ∗ *)
  (*            ((glsat Ω ∗ glG_version k v1 (1/2 + 1/2/2)%Qp ∗ (▷ R1) ∗ (▷ P2)) *)
  (*             ={E ∖ ↑N,E}=∗ *)
  (*             ∃ μ', glsat (<[k:=(v2, ghost_lock_locked (measure (ℓ v2) (μ')%M) t)]>Ω) ∗ *)
  (*             glG_locked k v2 q1 ∗ *)
  (*             glG_version k v2 (1/2 + 1/2/2)%Qp ∗ *)
  (*             glG_fuel k (measure (ℓ v2) μ) ∗ *)
  (*             glG_owner k t (1/2 + 1/2/2)%Qp ∗ *)
  (*             ([∗ set] u ∈ set_seq (S v1) (v2 - v1 - 1), glG_version_lb k u ∗ glG_unlocked k u) ∗ *)
  (*             (⌜ ghost_lock_step (v1, ghost_lock_unlocked) (v2, ghost_lock_locked (measure (ℓ v2) (μ')%M) t) ⌝) ∗ *)
  (*             glG_variant N k v2 q0 P2 Q2 R2)). *)
  (* Proof. *)
  (*   iIntros (Hq Hv HE) "(#Gvar& G& #Gwf& #Gu& Gv)". *)
  (*   iPoseProof (glG_layer_elem with "Gwf") as "#Ge". *)
  (*   iMod (glG_variant_acc_unlocked with "Gvar Gu") as "[H ACC]"; first auto. *)
  (*   iModIntro. iNext. iDestruct "H" as "[$ | (_& #Gvd& _)]"; cycle 1. *)
  (*   { iPoseProof (glG_version_expired_valid with "[$Gv $Gvd]") as "%". lia. } *)
  (*   iFrame "G Gv". iIntros "(G& Gv& HR& HP)". *)
  (*   iMod (glsat_lock _ _ v1 v2 ℓ μ t with "[$G $Gwf $Gu $Gv]") as "(%& $& Gl& Gv& $& $& #Gus& $)"; first auto. *)
  (*   iPoseProof (glG_version_get_lb _ _ v2 with "Gv") as "#Gvl"; first lia. *)
  (*   iPoseProof (glG_version_get_expired _ _ v1 with "Gvl") as "#Gvd"; first lia. *)
  (*   iFrame "Gv". *)
  (*   rewrite -!Hq. iDestruct "Gl" as "[Gl1 Gl2]". iFrame "Gl2 Gus". *)
  (*   iMod ("ACC" with "[HR]") as "_". *)
  (*   { iNext. iRight. iFrame. auto. } *)
  (*   iApply glG_variant_alloc_locked. iFrame. *)
  (* Qed. *)

  Lemma glsat_open_owner Ω k t q :
    glsat Ω ∗ glG_elem k ∗ glG_owner k t q
    ⊢ glG_owner k t q ∗
    (glG_locked k (1/2/2)%Qp ∗ glG_owner k t (1/2/2)%Qp) ∗
    ((glG_locked k (1/2/2)%Qp ∗ glG_owner k t (1/2/2)%Qp) -∗ glsat Ω).
  Proof.
    iIntros "(Hsat& #Ge& Go)".
    iPoseProof (glsat_lookup_owner with "[$Hsat $Ge $Go]") as "(%& %LU)".
    rewrite /glsat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& %LEa& Gok)".
    iFrame "Go Glk Gok". iIntros "[Glk Gok]".
    iFrame "HE HS HF HO". iApply (big_sepM_delete _ _ _ _ LU).
    iFrame "HM". iFrame. eauto.
  Qed.

End glsat.

(* Allocation of an initial obligation protocol. *)
Lemma glsat_alloc `{SI : indexT} `{!glsatGpreS Σ} `{!ord_mono_fun_class} :
  ⊢ |==> ∃ _ : glsatGS Σ, glsat ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR gl_id (agreeR (layerO)))) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=(mono_natUR)) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bankUR) ⊤)) as (γF) "HF";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=dfrac_agreeR (leibnizO ghost_lock_owner)) ⊤)) as (γO) "HO";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (GlsatG SI _ _ γE γS γF γO).
  rewrite /glsat -lock.
  iSplitL "HE".
  { iExists ∅. iFrame. done. }
  replace (⊤ ∖ gset_to_coPset (dom (∅ : ghost_locks))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
