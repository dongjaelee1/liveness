From iris.algebra Require Import gmap_view gset coPset reservation_map dfrac_agree mono_nat.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Export own.
From liris.algebra Require Import bank.
From liris.algebra Require Export ordinal_wfocm layer.
From liris.base_logic Require Export obligation.

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

Global Instance ord_obligation_class : obligation_class :=
  Build_obligation_class Ord.t ord_wfocm_pack.

Canonical Structure layerO `{SI : indexT} := leibnizO layer.

(** The ghost state for obligations *)
Module osatGS.

  Class osatGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OsatGpreS {
        osatGpreS_layer : inG Σ (gmap_viewR oid (agreeR (layerO)));
        osatGpreS_state : inG Σ (reservation_mapUR (prodUR mono_natUR mono_natUR));
        osatGpreS_fuel : inG Σ (reservation_mapUR bankUR);
        (* Keep track of the current owner of each obligation, if an owner exists *)
        osatGpreS_owner : inG Σ (reservation_mapUR (dfrac_agreeR (leibnizO obligation_owner)));
      }.

  Class osatGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OsatG {
        osat_inG : osatGpreS Σ;
        layer_name : gname;
        state_name : gname;
        fuel_name : gname;
        owner_name : gname;
      }.

  Definition osatΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (gmap_viewR oid (agreeR (layerO)));
      GFunctor (reservation_mapUR (prodUR mono_natUR mono_natUR));
      GFunctor (reservation_mapUR bankUR);
      GFunctor (reservation_mapUR (dfrac_agreeR $ (leibnizO obligation_owner)))
      ].

  Global Instance subG_osatΣ `{SI : indexT} {Σ} : subG (osatΣ) Σ → (osatGpreS Σ).
  Proof. solve_inG. Qed.

End osatGS.
Import osatGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances osat_inG
  osatGpreS_layer osatGpreS_state osatGpreS_fuel osatGpreS_owner.

(* Layer: layer of an obligation; layer can monotonically grow as version increases. *)
Definition oblG_layer `{SI : indexT} `{!osatGS Σ}
  (k : oid) (ℓ : layer) : iProp Σ :=
  own layer_name (gmap_view_frag k DfracDiscarded (to_agree (ℓ : layerO))).
Global Typeclasses Opaque oblG_layer.
Global Instance: Params (@oblG_layer) 3 := {}.

Definition oblG_elem `{SI : indexT} `{!osatGS Σ}
  (k : oid) : iProp Σ :=
  ∃ ℓ, oblG_layer k ℓ.
Global Typeclasses Opaque oblG_elem.
Global Instance: Params (@oblG_elem) 3 := {}.

Local Definition oblG_layer_auth_id `{SI : indexT} `{!osatGS Σ}
  (m : gmap oid layer) : iProp Σ :=
  own layer_name (gmap_view_auth (V:=agreeR (layerO)) (DfracOwn 1) (to_agree <$> m)).

Definition oblG_assigned `{SI : indexT} `{!osatGS Σ}
  (k : oid) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data k (●MN{#q} 0, ε)).
Global Typeclasses Opaque oblG_assigned.
Global Instance: Params (@oblG_assigned) 3 := {}.

Definition oblG_fulfilled `{SI : indexT} `{!osatGS Σ}
  (k : oid) : iProp Σ :=
  own state_name (reservation_map_data k (●MN□ 1, ε)).
Global Typeclasses Opaque oblG_fulfilled.
Global Instance: Params (@oblG_fulfilled) 3 := {}.

Definition oblG_alive `{SI : indexT} `{!osatGS Σ}
  (k : oid) (q : Qp) : iProp Σ :=
  own state_name (reservation_map_data k (ε, ●MN{#q} 0)).
Global Typeclasses Opaque oblG_alive.
Global Instance: Params (@oblG_alive) 3 := {}.

Definition oblG_expired `{SI : indexT} `{!osatGS Σ}
  (k : oid) : iProp Σ :=
  own state_name (reservation_map_data k (●MN□ 1, ●MN□ 1)).
Global Typeclasses Opaque oblG_expired.
Global Instance: Params (@oblG_expired) 3 := {}.

Local Definition oblG_state_token_id `{SI : indexT} `{!osatGS Σ}
  (E : coPset) : iProp Σ :=
  own state_name (reservation_map_token (A:=(prodUR mono_natUR mono_natUR)) E).

(* Fuel: manage credits for an obligation's fuel *)
Definition oblG_fuel `{SI : indexT} `{!osatGS Σ}
  (k : oid) (a : obligation_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bankUR) k (cash a)).
Global Typeclasses Opaque oblG_fuel.
Global Instance: Params (@oblG_fuel) 3 := {}.

Definition oblG_fuel_supply `{SI : indexT} `{!osatGS Σ}
  (k : oid) (a : obligation_fuel) (q : Qp) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bankUR) k (debt a q)).
Global Typeclasses Opaque oblG_fuel_supply.
Global Instance: Params (@oblG_fuel_supply) 3 := {}.

Local Definition oblG_fuel_token_id `{SI : indexT} `{!osatGS Σ}
  (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_token (A:=bankUR) E).

(* Owner: tracks the owner thread of an obligation *)
Definition oblG_owner `{SI : indexT} `{!osatGS Σ}
  (k : oid) (t : obligation_owner) (q : Qp) : iProp Σ :=
  own owner_name (reservation_map_data k (to_frac_agree q (t : leibnizO obligation_owner))).
Global Typeclasses Opaque oblG_owner.
Global Instance: Params (@oblG_owner) 3 := {}.

Local Definition oblG_owner_token_id `{SI : indexT} `{!osatGS Σ}
  (E : coPset) : iProp Σ :=
  own owner_name (reservation_map_token (A:=dfrac_agreeR (leibnizO obligation_owner)) E).

(* Global protocol to manage obligations. *)
Definition osat `{SI : indexT} `{!osatGS Σ} `{!ord_mono_fun_class}
  (Ω : obligations) : iProp Σ :=
  locked
    ((∃ (Ls : gmap oid layer), (⌜ dom Ω = dom Ls ⌝) ∗ oblG_layer_auth_id Ls) ∗
     oblG_state_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     oblG_fuel_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     oblG_owner_token_id (⊤ ∖ gset_to_coPset (dom Ω)) ∗
     ([∗ map] k ↦ g ∈ Ω,
        ∃ ℓ, oblG_layer k ℓ ∗
        ∃ α, oblG_fuel_supply k α (1)%Qp ∗
        ∃ μ, (⌜ (α <= measure ℓ μ)%ord ⌝) ∗
        match (g : obligation (OC:=ord_obligation_class)) with
        | obligation_assigned a t =>
            oblG_assigned k (1/2/2)%Qp ∗
            oblG_alive k (1/2/2)%Qp ∗
            (⌜ (α <= a)%ord ⌝) ∗
            oblG_owner k t (1/2/2)%Qp
        | obligation_fulfilled =>
            oblG_fulfilled k ∗
            oblG_alive k (1/2/2)%Qp ∗
            (∃ t, oblG_owner k t (1)%Qp)
        | obligation_expired =>
            oblG_expired k ∗
            (∃ t, oblG_owner k t (1)%Qp)
        end))%I.

(** Properties *)
Section osat.
  Context `{SI : indexT} `{!osatGS Σ} `{OMF : !ord_mono_fun_class}.

  (** Instances *)
  (* Layer *)
  Global Instance oblG_layer_persistent k ℓ : Persistent (oblG_layer k ℓ).
  Proof. rewrite /oblG_layer. apply _. Qed.
  Global Instance oblG_layer_timeless k ℓ : Timeless (oblG_layer k ℓ).
  Proof. rewrite /oblG_layer. apply _. Qed.

  Global Instance oblG_elem_persistent k : Persistent (oblG_elem k).
  Proof. rewrite /oblG_elem. apply _. Qed.
  Global Instance oblG_elem_timeless k : Timeless (oblG_elem k).
  Proof. rewrite /oblG_elem. apply _. Qed.

  Local Instance oblG_layer_auth_id_timeless m : Timeless (oblG_layer_auth_id m).
  Proof. rewrite /oblG_layer_auth_id. apply _. Qed.

  (* State *)
  Global Instance oblG_fulfilled_persistent k : Persistent (oblG_fulfilled k).
  Proof. rewrite /oblG_fulfilled. apply _. Qed.
  Global Instance oblG_expired_persistent k : Persistent (oblG_expired k).
  Proof. rewrite /oblG_expired. apply _. Qed.

  Global Instance oblG_assigned_timeless k q : Timeless (oblG_assigned k q).
  Proof. rewrite /oblG_assigned. apply _. Qed.
  Global Instance oblG_fulfilled_timeless k : Timeless (oblG_fulfilled k).
  Proof. rewrite /oblG_fulfilled. apply _. Qed.
  Global Instance oblG_alive_timeless k q : Timeless (oblG_alive k q).
  Proof. rewrite /oblG_alive. apply _. Qed.
  Global Instance oblG_expired_timeless k : Timeless (oblG_expired k).
  Proof. rewrite /oblG_expired. apply _. Qed.

  Global Instance oblG_assigned_fractional k : Fractional (oblG_assigned k).
  Proof.
    rewrite /oblG_assigned. intros p q.
    by rewrite -own_op -!reservation_map_data_op -pair_op -mono_nat_auth_dfrac_op.
  Qed.
  Global Instance oblG_assigned_as_fractional k q :
    AsFractional (oblG_assigned k q) (oblG_assigned k) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance oblG_alive_fractional k : Fractional (oblG_alive k).
  Proof.
    rewrite /oblG_alive. intros p q.
    by rewrite -own_op -!reservation_map_data_op -pair_op -mono_nat_auth_dfrac_op.
  Qed.
  Global Instance oblG_alive_as_fractional k q :
    AsFractional (oblG_alive k q) (oblG_alive k) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance oblG_state_token_id_timeless E : Timeless (oblG_state_token_id E).
  Proof. rewrite /oblG_state_token_id. apply _. Qed.

  (* Fuel *)
  Global Instance oblG_fuel_timeless k a : Timeless (oblG_fuel k a).
  Proof. rewrite /oblG_fuel. apply _. Qed.
  Global Instance oblG_fuel_supply_timeless k a q : Timeless (oblG_fuel_supply k a q).
  Proof. rewrite /oblG_fuel_supply. apply _. Qed.

  Global Instance oblG_fuel_supply_fractional k a : Fractional (oblG_fuel_supply k a).
  Proof.
    rewrite /oblG_fuel_supply. intros p q. by rewrite -own_op -!reservation_map_data_op debt_split.
  Qed.
  Global Instance oblG_fuel_supply_as_fractional k a q :
    AsFractional (oblG_fuel_supply k a q) (oblG_fuel_supply k a) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance oblG_fuel_token_id_timeless E : Timeless (oblG_fuel_token_id E).
  Proof. rewrite /oblG_fuel_token_id. apply _. Qed.

  (* Owner *)
  Global Instance oblG_owner_timeless k t q : Timeless (oblG_owner k t q).
  Proof. rewrite /oblG_owner. apply _. Qed.

  Global Instance oblG_owner_fractional k t :
    Fractional (oblG_owner k t).
  Proof.
    rewrite /oblG_owner. intros p q. by rewrite -own_op -!reservation_map_data_op -frac_agree_op.
  Qed.
  Global Instance oblG_owner_as_fractional k t q :
    AsFractional (oblG_owner k t q) (oblG_owner k t) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance oblG_owner_token_id_timeless E : Timeless (oblG_owner_token_id E).
  Proof. rewrite /oblG_owner_token_id. apply _. Qed.

  (* Sat *)
  Global Instance osat_timeless Ω : Timeless (osat Ω).
  Proof. rewrite /osat -lock. apply _. Qed.

  (** Layer rules *)
  Lemma oblG_layer_lookup (Ls : gmap oid layer) k ℓ :
    oblG_layer_auth_id Ls ∗ oblG_layer k ℓ
    ⊢ ⌜ Ls !! k = Some ℓ ⌝.
  Proof.
    rewrite /oblG_layer_auth_id /oblG_layer. iIntros "(H1& H2)". iStopProof.
    rewrite -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]". rewrite !lookup_fmap.
    case: (Ls !! k)=> [Q|] /=; last first.
    { by iDestruct "HQ'" as %?. }
    iDestruct "HQ'" as %[= <-].
    rewrite !to_agree_includedI; simpl.
    iPoseProof (internal_eq_sym with "Hincl") as "H". iPoseProof (discrete_eq with "H") as "%HG".
    rewrite HG. done.
  Qed.

  Lemma oblG_layer_agree k ℓ1 ℓ2 :
    oblG_layer k ℓ1 ∗ oblG_layer k ℓ2 ⊢ ⌜ ℓ1 = ℓ2 ⌝.
  Proof.
    rewrite /oblG_layer. iIntros "(H1& H2)". iStopProof.
    rewrite -own_op own_valid gmap_view_frag_op_validI.
    iIntros "(_&H)". rewrite to_agree_op_validI. iPoseProof (discrete_eq with "H") as "%". done.
  Qed.

  Lemma oblG_layer_elem k ℓ :
    oblG_layer k ℓ ⊢ oblG_elem k.
  Proof. rewrite /oblG_elem. eauto. Qed.

  Lemma oblG_layer_alloc (Ls : gmap oid layer) k ℓ :
    Ls !! k = None →
    oblG_layer_auth_id Ls
    ⊢ |==> oblG_layer_auth_id (<[k:=ℓ]>Ls) ∗
        oblG_layer k ℓ.
  Proof.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "[H Hw]".
    { eapply (gmap_view_alloc _ k (DfracDiscarded) (to_agree $ (ℓ : leibnizO _))); try done.
      rewrite !lookup_fmap. rewrite not_elem_of_dom_1; first done. by apply not_elem_of_dom. }
    rewrite /oblG_layer_auth_id /oblG_layer. rewrite fmap_insert. by iFrame.
  Qed.

  (** State rules *)
  Lemma oblG_assigned_frac_valid k q :
    oblG_assigned k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    iIntros "H". iPoseProof (own_valid with "H") as "%V".
    apply reservation_map_data_valid in V. destruct V.
    apply mono_nat_auth_dfrac_valid in H. done.
  Qed.
  Lemma oblG_assigned_fulfilled_false k q :
    oblG_assigned k q ∗ oblG_fulfilled k ⊢ False.
  Proof.
    rewrite /oblG_assigned /oblG_fulfilled. rewrite -own_op -reservation_map_data_op -pair_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%V".
    apply reservation_map_data_valid in V. destruct V.
    apply mono_nat_auth_dfrac_op_valid in H. destruct H. done.
  Qed.

  Lemma oblG_alive_frac_valid k q :
    oblG_alive k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    iIntros "H". iPoseProof (own_valid with "H") as "%V".
    apply reservation_map_data_valid in V. destruct V.
    apply mono_nat_auth_dfrac_valid in H0. done.
  Qed.
  Lemma oblG_alive_expired_false k q :
    oblG_alive k q ∗ oblG_expired k ⊢ False.
  Proof.
    rewrite /oblG_alive /oblG_expired. rewrite -own_op -reservation_map_data_op -pair_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%V".
    apply reservation_map_data_valid in V. destruct V.
    apply mono_nat_auth_dfrac_op_valid in H0. destruct H0. done.
  Qed.

  Lemma oblG_expired_fulfilled k :
    oblG_expired k ⊢ oblG_fulfilled k.
  Proof.
    rewrite /oblG_expired /oblG_fulfilled.
    replace (●MN□ 1, ●MN□ 1) with (●MN□ 1 ⋅ ε, ε ⋅ ●MN□ 1) by done.
    rewrite pair_op reservation_map_data_op. iIntros "[$ H2]".
  Qed.
  Lemma oblG_assigned_expired_false k q :
    oblG_assigned k q ∗ oblG_expired k ⊢ False.
  Proof.
    iIntros "[H1 #H2]". iPoseProof (oblG_expired_fulfilled with "H2") as "#H3".
    iApply (oblG_assigned_fulfilled_false with "[$]").
  Qed.

  Lemma oblG_assigned_to_fulfilled_2 k q1 q2 :
    (q1 + q2 = 1)%Qp →
    oblG_assigned k q1 ∗ oblG_assigned k q2 ⊢ |==> oblG_fulfilled k.
  Proof.
    iIntros (Heq) "H".
    rewrite /oblG_assigned /oblG_fulfilled -!own_op -!reservation_map_data_op -pair_op.
    iStopProof. apply own_update, reservation_map_update, prod_update; simpl. 2: done.
    rewrite -!mono_nat_auth_dfrac_op !dfrac_op_own !Heq.
    etrans; first apply (mono_nat_update 1); auto. apply mono_nat_auth_persist.
  Qed.
  Lemma oblG_assigned_to_fulfilled k :
    oblG_assigned k 1 ⊢ |==> oblG_fulfilled k.
  Proof. iIntros "[H1 H2]". iApply (oblG_assigned_to_fulfilled_2 with "[$]"). apply Qp.div_2. Qed.

  Lemma oblG_alive_to_expired_2 k q1 q2 :
    (q1 + q2 = 1)%Qp →
    oblG_fulfilled k ∗ oblG_alive k q1 ∗ oblG_alive k q2 ⊢ |==> oblG_expired k.
  Proof.
    iIntros (Heq) "H".
    rewrite /oblG_fulfilled /oblG_alive /oblG_expired -!own_op -!reservation_map_data_op -pair_op.
    iStopProof. simpl. apply own_update, reservation_map_update, prod_update; simpl. 1: done.
    rewrite -!mono_nat_auth_dfrac_op !dfrac_op_own !Heq.
    etrans; first apply (mono_nat_update 1); auto. apply mono_nat_auth_persist.
  Qed.
  Lemma oblG_alive_to_expired k :
    oblG_fulfilled k ∗ oblG_alive k 1 ⊢ |==> oblG_expired k.
  Proof. iIntros "[H0 [H1 H2]]". iApply (oblG_alive_to_expired_2 with "[$]"). apply Qp.div_2. Qed.

  Lemma oblG_alloc_assigned D k :
    k ∉ D →
    oblG_state_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> oblG_state_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        oblG_assigned k 1 ∗ oblG_alive k 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN 0 ⋅ ε, ε ⋅ ●MN 0) with "Htk") as "[Htk >H]"; auto.
    { apply pair_valid. split; apply mono_nat_auth_valid. }
    iDestruct "H" as "[H1 H2]". rewrite /oblG_assigned /oblG_alive. by iFrame.
  Qed.
  Lemma oblG_alloc_fulfilled D k :
    k ∉ D →
    oblG_state_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> oblG_state_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        oblG_fulfilled k ∗ oblG_alive k 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN□ 1 ⋅ ε, ε ⋅ ●MN 0) with "Htk") as "[Htk >H]"; auto.
    { apply pair_valid. split. 2: apply mono_nat_auth_valid. by apply mono_nat_auth_dfrac_valid. }
    iDestruct "H" as "[H1 H2]". rewrite /oblG_fulfilled /oblG_alive. by iFrame.
  Qed.
  Lemma oblG_alloc_expired D k :
    k ∉ D →
    oblG_state_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> oblG_state_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        oblG_expired k.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN□ 1, ●MN□ 1) with "Htk") as "[Htk >H]"; auto.
    { apply pair_valid. split; by apply mono_nat_auth_dfrac_valid. }
  Qed.

  (** Fuel rules *)
  Lemma oblG_fuel_eq k a0 a1 :
    a0 w= a1 →
    oblG_fuel k a0 = oblG_fuel k a1.
  Proof. intros EQ. rewrite /oblG_fuel. by erewrite cash_eq. Qed.
  Lemma oblG_fuel_eq_list L a0 a1 :
    a0 w= a1 →
    ([∗ list] k ∈ L, oblG_fuel k a0)%I ≡ ([∗ list] k ∈ L, oblG_fuel k a1)%I.
  Proof. intros. apply big_opL_proper. intros. erewrite oblG_fuel_eq; eauto. Qed.
  Lemma oblG_fuel_eq_set L a0 a1 :
    a0 w= a1 →
    ([∗ set] k ∈ L, oblG_fuel k a0)%I ≡ ([∗ set] k ∈ L, oblG_fuel k a1)%I.
  Proof. intros. apply big_opS_proper. intros. erewrite oblG_fuel_eq; eauto. Qed.

  Lemma oblG_fuel_mon k a0 a1 :
    a0 w≤ a1 →
    oblG_fuel k a1 ⊢ |==> oblG_fuel k a0.
  Proof.
    intros LE. rewrite /oblG_fuel. apply own_update.
    by apply reservation_map_update, cash_update.
  Qed.
  Lemma oblG_fuel_mon_list L a0 a1 :
    a0 w≤ a1 →
    ([∗ list] k ∈ L, oblG_fuel k a1) ⊢ |==> ([∗ list] k ∈ L, oblG_fuel k a0).
  Proof.
    iIntros (LE) "H". iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblG_fuel_mon.
  Qed.
  Lemma oblG_fuel_mon_set L a0 a1 :
    a0 w≤ a1 →
    ([∗ set] k ∈ L, oblG_fuel k a1) ⊢ |==> ([∗ set] k ∈ L, oblG_fuel k a0).
  Proof.
    iIntros (LE) "H". iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblG_fuel_mon.
  Qed.

  Lemma oblG_fuel_split k a0 a1 :
    oblG_fuel k (a0 w+ a1) ⊣⊢ oblG_fuel k a0 ∗ oblG_fuel k a1.
  Proof.
    rewrite /oblG_fuel. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite -cash_add) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite -cash_add). iSplitL "H1"; iFrame.
  Qed.
  Lemma oblG_fuel_split_list L a0 a1 :
    ([∗ list] k ∈ L, oblG_fuel k (a0 w+ a1)) ⊣⊢ ([∗ list] k ∈ L, oblG_fuel k a0) ∗ ([∗ list] k ∈ L, oblG_fuel k a1).
  Proof.
    rewrite -big_sepL_sep. iApply big_sepL_proper; intros. apply oblG_fuel_split.
  Qed.
  Lemma oblG_fuel_split_set L a0 a1 :
    ([∗ set] k ∈ L, oblG_fuel k (a0 w+ a1)) ⊣⊢ ([∗ set] k ∈ L, oblG_fuel k a0) ∗ ([∗ set] k ∈ L, oblG_fuel k a1).
  Proof.
    rewrite -big_sepS_sep. iApply big_sepS_proper; intros. apply oblG_fuel_split.
  Qed.

  Lemma oblG_fuel_mon_split k a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    oblG_fuel k a2 ⊢ |==> oblG_fuel k a0 ∗ oblG_fuel k a1.
  Proof.
    intros LE. iIntros "H". iApply oblG_fuel_split. iApply oblG_fuel_mon; done.
  Qed.
  Lemma oblG_fuel_mon_split_list L a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    ([∗ list] k ∈ L, oblG_fuel k a2) ⊢ |==> ([∗ list] k ∈ L, oblG_fuel k a0) ∗ ([∗ list] k ∈ L, oblG_fuel k a1).
  Proof.
    iIntros (LE) "H". iPoseProof (oblG_fuel_mon_list with "H") as ">H"; first done.
    by iApply oblG_fuel_split_list.
  Qed.
  Lemma oblG_fuel_mon_split_set L a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    ([∗ set] k ∈ L, oblG_fuel k a2) ⊢ |==> ([∗ set] k ∈ L, oblG_fuel k a0) ∗ ([∗ set] k ∈ L, oblG_fuel k a1).
  Proof.
    iIntros (LE) "H". iPoseProof (oblG_fuel_mon_set with "H") as ">H"; first done.
    by iApply oblG_fuel_split_set.
  Qed.

  Lemma oblG_fuel_lt k a0 a1 :
    a0 w< a1 →
    oblG_fuel k a1 ⊢ |==> oblG_fuel k a0 ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ oblG_fuel k c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (oblG_fuel_mon_split _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.
  Lemma oblG_fuel_lt_list L a0 a1 :
    a0 w< a1 →
    ([∗ list] k ∈ L, oblG_fuel k a1) ⊢ |==> ([∗ list] k ∈ L, oblG_fuel k a0) ∗ ([∗ list] k ∈ L, ∃ c, ⌜ wzero w< c ⌝ ∗ oblG_fuel k c).
  Proof.
    iIntros (LT) "H". rewrite -big_sepL_sep. iApply big_sepL_bupd. iApply (big_sepL_impl with "H").
    iModIntro. iIntros. by iApply oblG_fuel_lt.
  Qed.
  Lemma oblG_fuel_lt_set L a0 a1 :
    a0 w< a1 →
    ([∗ set] k ∈ L, oblG_fuel k a1) ⊢ |==> ([∗ set] k ∈ L, oblG_fuel k a0) ∗ ([∗ set] k ∈ L, ∃ c, ⌜ wzero w< c ⌝ ∗ oblG_fuel k c).
  Proof.
    iIntros (LE) "H". rewrite -big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "H").
    iModIntro. iIntros. by iApply oblG_fuel_lt.
  Qed.

  Lemma oblG_fuel_supply_mon k a0 a1 q :
    a0 w≤ a1 →
    oblG_fuel_supply k a0 q ⊢ |==> oblG_fuel_supply k a1 q.
  Proof.
    intros LE. rewrite /oblG_fuel_supply. apply own_update.
    by apply reservation_map_update, debt_update.
  Qed.

  Lemma oblG_fuel_supply_add k a0 a1 q0 q1 :
    oblG_fuel_supply k a0 q0 ∗ oblG_fuel_supply k a1 q1
    ⊢ ∃ b, oblG_fuel_supply k b (q0 + q1) ∗ ⌜ b w≤ a0 ∧ b w≤ a1 ⌝.
  Proof.
    rewrite /oblG_fuel_supply. iIntros "[H1 H2]".
    iPoseProof (own_op with "[H1 H2]") as "H"; first (iSplitL "H1"; iFrame).
    iEval (rewrite -!reservation_map_data_op) in "H".
    destruct (debt_add a0 a1 q0 q1) as (b&Heq&Hle0&Hle1). rewrite Heq.
    iExists _. iSplitL; done.
  Qed.

  Lemma oblG_fuel_supply_dfrac_valid k a q :
    oblG_fuel_supply k a q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblG_fuel_supply. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite !reservation_map_data_valid in V.
    rewrite bank_valid_debt in V. destruct V. auto.
  Qed.

  Lemma oblG_fuel_supply_issue k a0 a1 :
    oblG_fuel_supply k a0 (1)%Qp
    ⊢ |==> oblG_fuel_supply k (a0 w+ a1) (1)%Qp ∗ oblG_fuel k a1.
  Proof.
    rewrite /oblG_fuel_supply -own_op. apply own_update.
    rewrite -!reservation_map_data_op. apply reservation_map_update.
    apply debt_owe.
  Qed.
  Lemma oblG_fuel_supply_issue_2 k q0 q1 a0 a1 b :
    (q0 + q1 = 1)%Qp →
    oblG_fuel_supply k a0 q0 ∗ oblG_fuel_supply k a1 q1
    ⊢ |==> oblG_fuel_supply k (a0 w+ b) q0 ∗ oblG_fuel_supply k (a0 w+ b) q1 ∗ oblG_fuel k b.
  Proof.
    iIntros (Heq) "H". iDestruct (oblG_fuel_supply_add with "H") as "(%&H&%)".
    iMod (oblG_fuel_supply_mon _ _ a0 with "H") as "H".
    { destruct H. auto. }
    rewrite Heq. iMod (oblG_fuel_supply_issue _ _ b with "H") as "[H Hp]".
    iEval (rewrite -Heq) in "H". iDestruct "H" as "[H0 H1]". by iFrame.
  Qed.

  Lemma oblG_fuel_spend k a0 a1 q :
    oblG_fuel_supply k a0 q ∗ oblG_fuel k a1
    ⊢ |==> ∃ a2, ⌜(a1 w+ a2) w≤ a0⌝ ∗ oblG_fuel_supply k a2 q.
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
  Lemma oblG_fuel_spend_2 k a0 a1 q0 q1 c :
    oblG_fuel_supply k a0 q0 ∗ oblG_fuel_supply k a1 q1 ∗ oblG_fuel k c
    ⊢ |==> ∃ a2, (⌜(c w+ a2) w≤ a0 ∧ (c w+ a2) w≤ a1⌝) ∗
              oblG_fuel_supply k a2 q0 ∗ oblG_fuel_supply k a2 q1.
  Proof.
    iIntros "(H0&H1&H2)". iDestruct (oblG_fuel_supply_add with "[H0 H1]") as "(%&H&%)"; first iFrame.
    iMod (oblG_fuel_spend with "[H H2]") as "(%&%&H)"; first iFrame.
    iDestruct "H" as "[H0 H1]". iModIntro. iFrame. iPureIntro. destruct H. split.
    - etransitivity; [eapply H0 | eauto].
    - etransitivity; [eauto | eapply H].
  Qed.

  Lemma oblG_fuel_alloc D k a :
    k ∉ D →
    oblG_fuel_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> oblG_fuel_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        oblG_fuel_supply k a 1 ∗ oblG_fuel k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (debt a 1 ⋅ cash a) with "Htk") as "[Htk >H]"; auto.
    { apply bank_valid_debt_cash. split; done. }
    rewrite !reservation_map_data_op. iDestruct "H" as "[H1 H2]".
    rewrite /oblG_fuel_supply /oblG_fuel. by iFrame.
  Qed.

  (** Owner rules *)
  Lemma oblG_owner_agree k t1 t2 q1 q2 :
    oblG_owner k t1 q1 ∗ oblG_owner k t2 q2 ⊢ ⌜ t1 = t2 ∧ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblG_owner. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    apply frac_agree_op_valid in Hv. iPureIntro. destruct Hv. done.
  Qed.

  Lemma oblG_owner_valid k t q :
    oblG_owner k t q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /oblG_owner. iIntros "H".
    iPoseProof (own_valid with "H") as "%Hv". apply reservation_map_data_valid in Hv.
    by iApply (frac_agree_validI).
  Qed.

  Lemma oblG_owner_update_2 k t1 t2 q1 q2 t :
    (q1 + q2 = 1)%Qp →
    oblG_owner k t1 q1 ∗ oblG_owner k t2 q2 ⊢ |==> oblG_owner k t q1 ∗ oblG_owner k t q2.
  Proof.
    rewrite /oblG_owner -!own_op -!reservation_map_data_op.
    intros Heq. by apply own_update, reservation_map_update, frac_agree_update_2.
  Qed.
  Lemma oblG_owner_update k t1 t2 :
    oblG_owner k t1 1 ⊢ |==> oblG_owner k t2 1.
  Proof.
    iIntros "H". iDestruct "H" as "[H1 H2]".
    iMod (oblG_owner_update_2 _ _ _ _ _ t2 with "[H1 H2]") as "[H1 H2]"; [| iFrame |].
    { by rewrite Qp.div_2. }
    iCombine "H1 H2" as "H". done.
  Qed.

  Lemma oblG_owner_alloc D k t :
    k ∉ D →
    oblG_owner_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> oblG_owner_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗ oblG_owner k t 1.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (to_frac_agree 1 (t : leibnizO _)) with "Htk") as "[Htk >H]"; auto.
    { done. }
    rewrite /oblG_owner. by iFrame.
  Qed.

  (** osat rules *)
  Lemma osat_elem Ω k :
    osat Ω ∗ oblG_elem k ⊢ ⌜k ∈ dom Ω⌝.
  Proof.
    rewrite /oblG_elem.
    rewrite /osat -!lock. iIntros "(Hsat& (%& #Ge))".
    iDestruct "Hsat" as "((%& %& HE)& HS& HF& HO& HM)".
    iPoseProof (oblG_layer_lookup with "[$]") as "%".
    rewrite H. apply elem_of_dom_2 in H0. auto.
  Qed.
  Lemma osat_elem_lookup Ω k :
    osat Ω ∗ oblG_elem k
    ⊢ (⌜ ∃ a t, Ω !! k = Some (obligation_assigned a t) ⌝) ∨
        (oblG_fulfilled k ∗ ⌜ Ω !! k = Some (obligation_fulfilled) ⌝) ∨
        (oblG_expired k ∗ (⌜ Ω !! k = Some (obligation_expired) ⌝)).
  Proof.
    iIntros "(Hsat & #Ge)". iPoseProof (osat_elem with "[$]") as "%".
    apply elem_of_dom in H. destruct H.
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete _ _ _ _ H with "HM") as "[H _]".
    iDestruct "H" as "(%& #Gy& %& Gfs& %& %& H)". destruct x.
    - iLeft. iPureIntro. eauto.
    - iDestruct "H" as "(#Gu& _)"; eauto.
    - iDestruct "H" as "(#Gu& _)"; eauto.
  Qed.

  Lemma osat_lookup_assigned Ω k q :
    osat Ω ∗ oblG_elem k ∗ oblG_assigned k q
    ⊢ ∃ a t, ⌜Ω !! k = Some (obligation_assigned a t)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (osat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o; first eauto.
    - iDestruct "Mk" as "(Gu& _)". iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
    - iDestruct "Mk" as "(Gr& _)". iPoseProof (oblG_assigned_expired_false with "[$]") as "%". done.
  Qed.

  Lemma osat_lookup_fulfilled Ω k :
    osat Ω ∗ oblG_elem k ∗ oblG_fulfilled k
    ⊢ ⌜ (Ω !! k = Some (obligation_fulfilled)) ⌝ ∨ ⌜ (Ω !! k = Some (obligation_expired)) ⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (osat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o; [| eauto | eauto].
    iDestruct "Mk" as "(Ga& _)". iPoseProof (oblG_assigned_fulfilled_false with "[$]") as "%". done.
  Qed.

  Lemma osat_lookup_alive Ω k q :
    osat Ω ∗ oblG_elem k ∗ oblG_alive k q
    ⊢ (∃ a t, ⌜Ω !! k = Some (obligation_assigned a t)⌝) ∨ ⌜(Ω !! k = Some (obligation_fulfilled))⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (osat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o; [eauto | eauto |].
    iDestruct "Mk" as "(Gr& _)". iPoseProof (oblG_alive_expired_false with "[$]") as "%". done.
  Qed.

  Lemma osat_lookup_expired Ω k :
    osat Ω ∗ oblG_elem k ∗ oblG_expired k
    ⊢ ⌜ Ω !! k = Some (obligation_expired) ⌝.
  Proof.
    iIntros "(Hsat & #Ge & Gl)".
    iPoseProof (osat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o; last eauto.
    - iDestruct "Mk" as "(Gu& _)". iPoseProof (oblG_assigned_expired_false with "[$]") as "%". done.
    - iDestruct "Mk" as "(_& Gr& _)". iPoseProof (oblG_alive_expired_false with "[$]") as "%". done.
  Qed.

  Lemma osat_lookup_owner Ω k t q :
    osat Ω ∗ oblG_elem k ∗ oblG_owner k t q
    ⊢ ∃ a, ⌜Ω !! k = Some (obligation_assigned a t)⌝.
  Proof.
    iIntros "(Hsat & #Ge & Go)".
    iPoseProof (osat_elem with "[$]") as "%Hin".
    apply elem_of_dom in Hin; destruct Hin as [o LU].
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[LU _]"; first eauto.
    iDestruct "LU" as "(%& Gy& %& Gfs& %& %Bound& Mk)". destruct o.
    - iDestruct "Mk" as "(Gl& Ga& %& Go2)".
      iPoseProof (oblG_owner_agree with "[$Go $Go2]") as "(%&%)". subst. eauto.
    - iDestruct "Mk" as "(_& _& %& Go2)".
      iPoseProof (oblG_owner_agree with "[$Go $Go2]") as "(%&%)". apply Qp.not_add_le_r in H0. done.
    - iDestruct "Mk" as "(_& %& Go2)".
      iPoseProof (oblG_owner_agree with "[$Go $Go2]") as "(%&%)". apply Qp.not_add_le_r in H0. done.
  Qed.

  Lemma osat_alloc_obligation_assigned Ω k ℓ (μ : measurable_syntax) t :
    k ∉ dom Ω →
    osat Ω
    ⊢ |==> osat (<[k:=(obligation_assigned (measure ℓ μ) t)]>Ω) ∗
        oblG_layer k ℓ ∗
        oblG_elem k ∗
        oblG_assigned k (1/2 + 1/2/2)%Qp ∗
        oblG_alive k (1/2 + 1/2/2)%Qp ∗
        oblG_fuel k (measure ℓ μ) ∗
        oblG_owner k t (1/2 + 1/2/2)%Qp ∗
        (⌜ Ω ↪ₐ (<[k:=(obligation_assigned (measure ℓ μ) t)]>Ω) ⌝).
  Proof.
    iIntros (Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iDestruct "HE" as "(%& %Dom& HE)".
    iMod (oblG_layer_alloc _ k ℓ with "HE") as "[HE #Gwf]".
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    iMod (oblG_alloc_assigned _ k with "HS") as "(HS& Gl& Ga)"; first auto.
    iMod (oblG_fuel_alloc _ k (measure ℓ μ) with "HF") as "(HF& Gfsp& Gf)"; first set_solver.
    iMod (oblG_owner_alloc _ k t with "HO") as "[HO Go]"; first auto.
    iDestruct "Gl" as "[Gl1 [Gl2 Gl']]". iCombine "Gl1 Gl2" as "Gl".
    iDestruct "Ga" as "[Ga1 [Ga2 Ga']]". iCombine "Ga1 Ga2" as "Ga".
    iDestruct "Go" as "[Go1 [Go2 Go']]". iCombine "Go1 Go2" as "Go".
    iPoseProof (oblG_layer_elem with "Gwf") as "#Ge".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HF HO". iFrame "Ge Gl Ga Gf Go Gwf".
    iSplitL; cycle 1.
    { iPureIntro. exists k. split; eauto. }
    iSplitR.
    { rewrite dom_insert_L Dom. done. }
    iApply big_sepM_insert; first auto. iFrame. eauto.
  Qed.

  Lemma osat_alloc_obligation_fulfilled Ω k :
    k ∉ dom Ω →
    osat Ω
    ⊢ |==> osat (<[k:=(obligation_fulfilled)]>Ω) ∗
        oblG_elem k ∗
        oblG_fulfilled k ∗
        oblG_alive k (1/2 + 1/2/2)%Qp ∗
        (⌜ Ω ↪ₐ (<[k:=(obligation_fulfilled)]>Ω) ⌝).
  Proof.
    iIntros (Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iDestruct "HE" as "(%& %Dom& HE)".
    iMod (oblG_layer_alloc _ k 0%ordi with "HE") as "[HE #Gwf]".
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    iMod (oblG_alloc_fulfilled _ k with "HS") as "(HS& #Gl& Ga)"; first auto.
    iMod (oblG_fuel_alloc _ k 0%ord with "HF") as "(HF& Gfsp& Gf)"; first set_solver.
    iMod (oblG_owner_alloc _ k inhabitant with "HO") as "[HO Go]"; first auto.
    iDestruct "Ga" as "[Ga1 [Ga2 Ga']]". iCombine "Ga1 Ga2" as "Ga".
    iPoseProof (oblG_layer_elem with "Gwf") as "#Ge".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HF HO". iFrame "Ge Gl Ga".
    iSplitL; cycle 1.
    { iPureIntro. exists k. split; eauto. }
    iSplitR.
    { rewrite dom_insert_L Dom. done. }
    iApply big_sepM_insert; first auto. iFrame. iFrame "Gwf Gl".
    iExists 0%M. iPureIntro. apply Ord.O_bot.
  Qed.

  Lemma osat_alloc_obligation_expired Ω k :
    k ∉ dom Ω →
    osat Ω
    ⊢ |==> osat (<[k:=(obligation_expired)]>Ω) ∗
        oblG_elem k ∗
        oblG_expired k ∗
        (⌜ Ω ↪ₐ (<[k:=(obligation_expired)]>Ω) ⌝).
  Proof.
    iIntros (Hk) "Hsat". pose proof Hk as Nin. apply not_elem_of_dom in Nin.
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iDestruct "HE" as "(%& %Dom& HE)".
    iMod (oblG_layer_alloc _ k 0%ordi with "HE") as "[HE #Gwf]".
    { apply not_elem_of_dom. rewrite -Dom. auto. }
    iMod (oblG_alloc_expired _ k with "HS") as "[HS #Gl]"; first auto.
    iMod (oblG_fuel_alloc _ k 0%ord with "HF") as "(HF& Gfsp& Gf)"; first set_solver.
    iMod (oblG_owner_alloc _ k inhabitant with "HO") as "[HO Go]"; first auto.
    iPoseProof (oblG_layer_elem with "Gwf") as "#Ge".
    iModIntro. rewrite !dom_insert_L. iFrame "HE HS HF HO". iFrame "Ge Gl".
    iSplitL; cycle 1.
    { iPureIntro. exists k. split; eauto. }
    iSplitR.
    { rewrite dom_insert_L Dom. done. }
    iApply big_sepM_insert; first auto. iFrame. iFrame "Gwf Gl".
    iExists 0%M. iPureIntro. apply Ord.O_bot.
  Qed.

  (** ghost lock step rules: progress, unlock, retire *)
  Lemma osat_progress_one Ω k a t c :
    (Ω !! k = Some (obligation_assigned a t)) →
    (Ord.O < c)%ord →
    osat Ω ∗ oblG_fuel k c
    ⊢ |==> ∃ a', osat (<[k:=(obligation_assigned a' t)]>Ω) ∗
              (⌜ obligation_progress (obligation_assigned a t) (obligation_assigned a' t) ⌝).
  Proof.
    intros LU Hc. iIntros "(Hsat & Gf)".
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& Gak& %LEa& Gok)".
    iMod (oblG_fuel_spend with "[$Gfs $Gf]") as "(%&%&Gfs)".
    assert (LT : a2 w< α).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (obligation_assigned a2 t)) with "[HM Glk Gak Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gy". iExists μ. iPureIntro. split; last done.
      etrans; last eauto. apply WFOCM.lt_le. auto. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HE HS HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. econstructor. eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma osat_progress Ω (C : obl_cond) :
    (∀ k g, C k g → ∃ a o, g = (obligation_assigned a o)) →
    osat Ω ∗
    ([∗ map] k ↦ g ∈ Ω, (⌜ C k g ⌝ ∗ ∃ c, ⌜ (Ord.O < c)%ord ⌝ ∗ oblG_fuel k c) ∨ (⌜ ¬ C k g ⌝))
    ⊢ |==> ∃ Ω', osat Ω' ∗ (⌜ Ω ↪ₚ Ω' | C ⌝).
  Proof.
    iIntros (HC) "(Hsat & Cs)".
    iAssert (∃ Ω1 Ω2, (⌜ Ω1 ##ₘ Ω2 ∧ Ω = Ω1 ∪ Ω2 ∧ map_Forall (λ k g, C k g) Ω1 ∧ map_Forall (λ k g, ¬ C k g) Ω2 ⌝) ∗
                      ([∗ map] k ↦ g ∈ Ω1, (⌜ C k g ⌝ ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ oblG_fuel k c)) ∗
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
    iAssert (|==> ∃ Ω' : obligations, osat Ω' ∗ ⌜Ω ↪ₚ Ω' | (λ k _, k ∈ dom Ω1)⌝)%I with "[-]" as ">H"; cycle 1.
    { iDestruct "H" as "(%& S& %)". iModIntro. iFrame. iPureIntro. destruct H as [H Hkeep].
      split; last auto.
      eapply obls_cond_rel_iff_lookup; first eapply H.
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
    iMod (osat_progress_one with "[$S $Bpi]") as "(%& S& %Progi)"; auto.
    { eauto. }
    iFrame. iPureIntro. simpl. assert (Prog2 : Ω' ↪ₚ <[i:=(obligation_assigned a' t)]> Ω' | λ k _, k = i).
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
    eapply obls_cond_rel_split_cond. 4,5: eauto. all: simpl.
    - intros. rewrite dom_insert_L. set_solver.
    - intros. destruct (decide (k = i)); auto. subst. left. by apply not_elem_of_dom.
    - repeat intro. auto.
  Qed.

  Lemma osat_progress_one_owner Ω k a t1 t2 c :
    (Ω !! k = Some (obligation_assigned a t1)) →
    (Ord.O < c)%ord →
    osat Ω ∗ oblG_owner k t1 (1/2 + 1/2/2)%Qp ∗ oblG_fuel k c
    ⊢ |==> ∃ a', osat (<[k:=(obligation_assigned a' t2)]>Ω) ∗ oblG_owner k t2 (1/2 + 1/2/2)%Qp ∗
              (⌜ obligation_progress (obligation_assigned a t1) (obligation_assigned a' t2) ⌝).
  Proof.
    intros LU Hc. iIntros "(Hsat& Go& Gf)".
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& Gak& %LEa& Gok)".
    iMod (oblG_fuel_spend with "[$Gfs $Gf]") as "(%&%&Gfs)".
    assert (LT : a2 w< α).
    { apply WFOCM.lt_exists_right. exists c. split; done. }
    iMod (oblG_owner_update_2 _ _ _ _ _ t2 with "[$Go $Gok]") as "[Go Gok]".
    { rewrite -Qp.add_assoc !Qp.div_2. done. }
    iModIntro. iExists a2.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (obligation_assigned a2 t2)) with "[HM Glk Gak Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gy". iExists μ. iPureIntro. split; last done.
      etrans; last eauto. apply WFOCM.lt_le. auto. }
    rewrite -lock. rewrite dom_insert_lookup_L; last done. iFrame "HE HS HF HO".
    rewrite insert_delete_eq. iFrame.
    iPureIntro. econstructor. eapply WFOCM.lt_le_lt; eauto.
  Qed.

  Lemma Qp_add_help_1 : (1 / 2 + 1 / 2 / 2 + 1 / 2 / 2 = 1)%Qp.
  Proof. by rewrite -Qp.add_assoc !Qp.div_2. Qed.

  Lemma osat_fulfill Ω k t :
    osat Ω ∗ oblG_elem k ∗ oblG_assigned k (1/2 + 1/2/2)%Qp ∗ oblG_owner k t (1/2 + 1/2/2)%Qp
    ⊢ |==> osat (<[k:=(obligation_fulfilled)]>Ω) ∗
        oblG_fulfilled k ∗
        (⌜ ∀ a, obligation_fulfill (obligation_assigned a t) (obligation_fulfilled) ⌝).
  Proof.
    iIntros "(Hsat& #Ge& Gl& Go)".
    iPoseProof (osat_lookup_assigned with "[$Hsat $Ge $Gl]") as "(%&%& %LU)".
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& Gak& %LEa& Gok)".
    iMod (oblG_assigned_to_fulfilled_2 with "[$Gl $Glk]") as "#Gf".
    { apply Qp_add_help_1. }
    iPoseProof (oblG_owner_agree with "[$Go $Gok]") as "(%& %)". clear H0. subst t0.
    iCombine "Go Gok" as "Gok". rewrite Qp_add_help_1.
    iModIntro.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (obligation_fulfilled)) with "[HM Gak Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gy Gf". eauto. }
    rewrite dom_insert_lookup_L; last done. iFrame "HE HS HF HO".
    rewrite insert_delete_eq. iFrame. iFrame "Gf".
    iPureIntro. intros. econstructor.
  Qed.

  Lemma osat_expire Ω k :
    osat Ω ∗ oblG_elem k ∗ oblG_fulfilled k ∗ oblG_alive k (1/2 + 1/2/2)%Qp
    ⊢ |==> osat (<[k:=(obligation_expired)]>Ω) ∗
        oblG_expired k ∗
        (⌜ obligation_expire (obligation_fulfilled) (obligation_expired) ⌝).
  Proof.
    iIntros "(Hsat& #Ge& #Gf& Ga)".
    iPoseProof (osat_lookup_fulfilled with "[$Hsat $Ge $Gf]") as "%LU".
    iPoseProof (osat_lookup_alive with "[$Hsat $Ge $Ga]") as "[%LU2 | %LU2]".
    { destruct LU2 as (?&?&?). rewrite H in LU. destruct LU; done. }
    destruct LU; cycle 1.
    { rewrite H in LU2; done. }
    clear H. rename LU2 into LU.
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& Gak& Gok)".
    iMod (oblG_alive_to_expired_2 with "[$Gf $Ga $Gak]") as "#Gr".
    { apply Qp_add_help_1. }
    iModIntro.
    iPoseProof ((big_sepM_insert _ (delete k Ω) k (obligation_expired)) with "[HM Gok Gfs]") as "HM".
    { apply lookup_delete_eq. }
    { iFrame "HM". iFrame. iFrame "Gy Gr". eauto. }
    rewrite dom_insert_lookup_L; last done. iFrame "HE HS HF HO".
    rewrite insert_delete_eq. iFrame. iFrame "Gr".
    iPureIntro. econstructor.
  Qed.

  Lemma osat_open_owner Ω k t q :
    osat Ω ∗ oblG_elem k ∗ oblG_owner k t q
    ⊢ oblG_owner k t q ∗
    (oblG_assigned k (1/2/2)%Qp ∗ oblG_alive k (1/2/2)%Qp ∗ oblG_owner k t (1/2/2)%Qp) ∗
    ((oblG_assigned k (1/2/2)%Qp ∗ oblG_alive k (1/2/2)%Qp ∗ oblG_owner k t (1/2/2)%Qp) -∗ osat Ω).
  Proof.
    iIntros "(Hsat& #Ge& Go)".
    iPoseProof (osat_lookup_owner with "[$Hsat $Ge $Go]") as "(%& %LU)".
    rewrite /osat -!lock. iDestruct "Hsat" as "(HE& HS& HF& HO& HM)".
    iPoseProof (big_sepM_delete with "HM") as "[Hk HM]"; [eapply LU |].
    iDestruct "Hk" as "(%& #Gy& %& Gfs& %& %Bound& Mk)".
    iDestruct "Mk" as "(Glk& Gak& %LEa& Gok)".
    iFrame "Go Glk Gak Gok". iIntros "(Glk& Gak& Gok)".
    iFrame "HE HS HF HO". iApply (big_sepM_delete _ _ _ _ LU).
    iFrame "HM". iFrame. eauto.
  Qed.

End osat.

(* Allocation of an initial obligation protocol. *)
Lemma osat_alloc `{SI : indexT} `{!osatGpreS Σ} `{!ord_mono_fun_class} :
  ⊢ |==> ∃ _ : osatGS Σ, osat ∅.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR oid (agreeR (layerO)))) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=(prodUR mono_natUR mono_natUR)) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bankUR) ⊤)) as (γF) "HF";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=dfrac_agreeR (leibnizO obligation_owner)) ⊤)) as (γO) "HO";
    first by apply reservation_map_token_valid.
  iModIntro; iExists (OsatG SI _ _ γE γS γF γO).
  rewrite /osat -lock.
  iSplitL "HE".
  { iExists ∅. iFrame. done. }
  replace (⊤ ∖ gset_to_coPset (dom (∅ : obligations))) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
