From iris.algebra Require Import agree gset gmap gmap_view reservation_map mono_nat.
From iris.bi Require Import cmra lib.fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From lantana.algebra Require Import map_of_sets bcred ordinal_ucmra.
From lantana.base_logic Require Export osat othread.
From transfinite.base_logic.lib Require Import ghost_map.

Definition ocid := positive.

(** The ghost state for maintaining obligation carriers *)
Module ocarrierGS.

  (* Assumes thread ids are positive *)
  Class ocarrierGpreS `{SI : sidx} (Σ : gFunctors) : Set :=
    OcarrierGpreS {
        ocarrierGpreS_thread : inG Σ (reservation_mapUR (gmap_viewR ocid unit));
        ocarrierGpreS_carrier : inG Σ (reservation_mapUR (gmap_viewR ocid (gsetUR oid)));
        ocarrierGpreS_fuel : inG Σ (reservation_mapUR (bcredUR));
        #[local] ocarrierGpreS_owned :: ghost_mapG Σ ocid positive;
      }.

  Class ocarrierGS `{SI : sidx} (Σ : gFunctors) : Set :=
    OcarrierG {
        ocarrier_inG : ocarrierGpreS Σ;
        thread_name : gname;
        carrier_name : gname;
        fuel_name : gname;
        owned_name : gname;
      }.

  Definition ocarrierΣ `{SI : sidx} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR ocid unit));
      GFunctor (reservation_mapUR (gmap_viewR ocid (gsetUR oid)));
      GFunctor (reservation_mapUR bcredUR);
      ghost_mapΣ ocid positive
      ].

  Global Instance subG_ocarrierΣ `{SI : sidx} {Σ} : subG (ocarrierΣ) Σ → (ocarrierGpreS Σ).
  Proof. solve_inG. Qed.

End ocarrierGS.
Import ocarrierGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances ocarrier_inG ocarrierGpreS_thread ocarrierGpreS_owned ocarrierGpreS_carrier ocarrierGpreS_fuel.

(* Thread *)
Definition ocarrierG_thread `{SI : sidx} `{!ocarrierGS Σ} (i : positive) (g : ocid) : iProp Σ :=
  own thread_name (reservation_map_data (A:=(gmap_viewR ocid (unit)))
                     i (gmap_view_frag g (DfracOwn 1) (tt))).
Global Typeclasses Opaque ocarrierG_thread.
Global Instance: Params (@ocarrierG_thread) 3 := {}.

Definition ocarrierG_thread_auth `{SI : sidx} `{!ocarrierGS Σ} (i : positive) (G : gset ocid) (q : Qp) : iProp Σ :=
  own thread_name (reservation_map_data (A:=(gmap_viewR ocid (unit)))
                     i (gmap_view_auth (DfracOwn q) (gset_to_gmap tt G))).
Global Typeclasses Opaque ocarrierG_thread_auth.
Global Instance: Params (@ocarrierG_thread_auth) 3 := {}.

Local Definition ocarrierG_thread_token `{SI : sidx} `{!ocarrierGS Σ} TP : iProp Σ :=
  (own thread_name (reservation_map_token (A:=gmap_viewR ocid (unit)) (⊤ ∖ gset_to_coPset TP))).

(* Owned *)
Definition ocarrierG_owned `{SI : sidx} `{!ocarrierGS Σ} (g : ocid) (i : positive) q : iProp Σ :=
  ghost_map_elem owned_name g (DfracOwn q) i.
Global Typeclasses Opaque ocarrierG_owned.
Global Instance: Params (@ocarrierG_owned) 3 := {}.

Definition ocarrierG_owned_auth `{SI : sidx} `{!ocarrierGS Σ} (G : gmap ocid positive) : iProp Σ :=
  ghost_map_auth_frac owned_name 1 G.
Global Typeclasses Opaque ocarrierG_owned_auth.
Global Instance: Params (@ocarrierG_owned_auth) 3 := {}.

(* Carrier *)
Definition ocarrierG_carrier `{SI : sidx} `{!ocarrierGS Σ} (i : positive) (g : ocid) (K : oids) : iProp Σ :=
  own carrier_name (reservation_map_data (A:=(gmap_viewR ocid (gsetUR oid)))
                    i (gmap_view_frag g (DfracOwn 1) K)).
Global Typeclasses Opaque ocarrierG_carrier.
Global Instance: Params (@ocarrierG_carrier) 3 := {}.

Local Definition ocarrierG_carrier_token `{SI : sidx} `{!ocarrierGS Σ} TP : iProp Σ :=
  (own carrier_name (reservation_map_token (A:=gmap_viewR ocid (gsetUR oid)) (⊤ ∖ gset_to_coPset TP))).

Local Definition ocarrierG_carrier_auth `{SI : sidx} `{!ocarrierGS Σ} i (KM : gmap ocid oids) : iProp Σ :=
  (own carrier_name (reservation_map_data (A:=(gmap_viewR ocid (gsetUR oid)))
                     i (gmap_view_auth (DfracOwn 1) (KM)))).

(* Fuel: manage fuels for ocarriers *)
Definition ocarrierG_bound `{SI : sidx} `{!ocarrierGS Σ} (g : ocid) (β : obl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bcredUR) g (credit_bound β)).
Global Typeclasses Opaque ocarrierG_bound.
Global Instance: Params (@ocarrierG_bound) 3 := {}.

Definition ocarrierG_fuel `{SI : sidx} `{!ocarrierGS Σ} (g : ocid) (a : obl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bcredUR) g (credit a)).
Global Typeclasses Opaque ocarrierG_fuel.
Global Instance: Params (@ocarrierG_fuel) 3 := {}.

Local Definition ocarrierG_fuel_token_id `{SI : sidx} `{!ocarrierGS Σ} (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_token (A:=bcredUR) E).

(* Global invariant for the obligation carriers. *)
Definition ocarrier `{SI : sidx} `{!@osatGS.osatGS _ Σ} `{!othreadGS.othreadGS Σ} `{!ocarrierGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (Dg : gmap ocid positive),
        ocarrierG_fuel_token_id (⊤ ∖ (gset_to_coPset (dom Dg))) ∗
        ocarrierG_owned_auth Dg ∗
        ocarrierG_thread_token TP ∗
        ocarrierG_carrier_token TP ∗
        ([∗ set] i ∈ TP,
           ∃ (KM : gmap ocid (oids)) (G : gset ocid),
             ⌜ dom KM = G ⌝ ∗
             ocarrierG_thread_auth i G (1/2)%Qp ∗
             ocarrierG_carrier_auth i KM ∗
             ((∃ K, othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i K ∗ ⌜ K = union_sets KM ∧ disjoint_sets KM ⌝) ∨
                (othreadG_done i ∗ ocarrierG_thread_auth i G (1/2)%Qp ∗ ⌜ KM = ∅ ∧ G = ∅ ⌝)) ∗
             ([∗ map] g ↦ K ∈ KM,
                ∃ β, ocarrierG_bound g β ∗
                     ([∗ set] k ∈ K, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)))
    )%I.

Section ocarrier.
  Context `{SI : sidx} `{OSAT : !osatGS.osatGS Σ} `{OTH : !othreadGS.othreadGS Σ} `{!ocarrierGS Σ} `{OMF : !ord_mono_fun_class}.

  (* Thread *)
  Global Instance ocarrierG_thread_timeless i g : Timeless (ocarrierG_thread i g).
  Proof. rewrite /ocarrierG_thread. apply _. Qed.

  Global Instance ocarrierG_thread_auth_timeless i G q : Timeless (ocarrierG_thread_auth i G q).
  Proof. rewrite /ocarrierG_thread_auth. apply _. Qed.

  Global Instance ocarrierG_thread_auth_fractional i G :
    Fractional (ocarrierG_thread_auth i G).
  Proof.
    rewrite /ocarrierG_thread_auth. intros p q.
    by rewrite -own_op -!reservation_map_data_op -gmap_view_auth_dfrac_op.
  Qed.
  Global Instance ocarrierG_thread_auth_as_fractional i G q :
    AsFractional (ocarrierG_thread_auth i G q) (ocarrierG_thread_auth i G) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance ocarrierG_thread_token_timeless TP : Timeless (ocarrierG_thread_token TP).
  Proof. rewrite /ocarrierG_thread_token. apply _. Qed.

  (* Carrier *)
  Global Instance ocarrierG_carrier_timeless i g K : Timeless (ocarrierG_carrier i g K).
  Proof. rewrite /ocarrierG_carrier. apply _. Qed.

  Local Instance ocarrierG_carrier_token_timeless TP : Timeless (ocarrierG_carrier_token TP).
  Proof. rewrite /ocarrierG_carrier_token. apply _. Qed.

  Local Instance ocarrierG_carrier_auth_timeless i KM : Timeless (ocarrierG_carrier_auth i KM).
  Proof. rewrite /ocarrierG_carrier_auth. apply _. Qed.

  (* Fuel *)
  Global Instance ocarrierG_bound_persistent g β : Persistent (ocarrierG_bound g β).
  Proof. rewrite /ocarrierG_bound. apply _. Qed.
  Global Instance ocarrierG_bound_timeless g β : Timeless (ocarrierG_bound g β).
  Proof. rewrite /ocarrierG_bound. apply _. Qed.

  Global Instance ocarrierG_fuel_timeless g a : Timeless (ocarrierG_fuel g a).
  Proof. rewrite /ocarrierG_fuel. apply _. Qed.

  Local Instance ocarrierG_fuel_token_id_timeless E : Timeless (ocarrierG_fuel_token_id E).
  Proof. rewrite /ocarrierG_fuel_token_id. apply _. Qed.

  (** Thread rules *)
  Lemma ocarrierG_thread_alloc_auth D i :
    i ∉ D →
    ocarrierG_thread_token D
    ⊢ |==> ocarrierG_thread_token ({[i]} ∪ D) ∗
        ocarrierG_thread_auth i ∅ 1.
  Proof.
    rewrite /ocarrierG_thread_token /ocarrierG_thread_auth.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (∅ : gmap ocid unit)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma ocarrierG_thread_alloc i (G : gset ocid) g :
    g ∉ G →
    ocarrierG_thread_auth i G 1
    ⊢ |==> ocarrierG_thread_auth i ({[g]} ∪ G) 1 ∗ ocarrierG_thread i g.
  Proof.
    rewrite /ocarrierG_thread_auth /ocarrierG_thread.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ g (DfracOwn 1) (tt)); try done.
      apply lookup_gset_to_gmap_None. auto. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]". iFrame "Ho".
    rewrite gset_to_gmap_union_singleton. done.
  Qed.

  Lemma ocarrierG_thread_delete i (G : gset ocid) g :
    ocarrierG_thread_auth i G 1 ∗ ocarrierG_thread i g
    ⊢ |==> ocarrierG_thread_auth i (G ∖ {[g]}) 1.
  Proof.
    rewrite /ocarrierG_thread_auth /ocarrierG_thread -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update. rewrite gset_to_gmap_difference_singleton. apply gmap_view_delete.
  Qed.

  Lemma ocarrierG_thread_elem_of i G q g :
    ocarrierG_thread_auth i G q ∗ ocarrierG_thread i g
    ⊢ ⌜ g ∈ G ⌝.
  Proof.
    rewrite /ocarrierG_thread_auth /ocarrierG_thread -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H.
    destruct H as (?&_&_&?&?&?). iPureIntro.
    apply lookup_gset_to_gmap_Some in H. by destruct H.
  Qed.

  Lemma ocarrierG_thread_auth_valid i G1 G2 q1 q2 :
    ocarrierG_thread_auth i G1 q1 ∗ ocarrierG_thread_auth i G2 q2
    ⊢ ⌜ G1 = G2 ∧ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /ocarrierG_thread_auth -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_auth_dfrac_op_valid in H.
    destruct H as (?&?). iPureIntro.
    (* FIXME: hacky proof *)
    rewrite /gset_to_gmap in H0. apply map_fmap_equiv_inj in H0.
    2:{ done. }
    apply leibniz_equiv in H0. split; auto.
    destruct G1, G2; simpl in *. subst. auto.
  Qed.

  (** Carrier rules *)
  Lemma ocarrierG_carrier_alloc_auth D i :
    i ∉ D →
    ocarrierG_carrier_token D
    ⊢ |==> ocarrierG_carrier_token ({[i]} ∪ D) ∗
        ocarrierG_carrier_auth i ∅.
  Proof.
    rewrite /ocarrierG_carrier_token /ocarrierG_carrier_auth.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (∅ : gmap ocid oids)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma ocarrierG_carrier_alloc i (KM : gmap ocid oids) g :
    KM !! g = None →
    ocarrierG_carrier_auth i KM
    ⊢ |==> ocarrierG_carrier_auth i (<[g:=∅]>KM) ∗ ocarrierG_carrier i g ∅.
  Proof.
    rewrite /ocarrierG_carrier_auth /ocarrierG_carrier.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ g (DfracOwn 1) ∅); done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]". iFrame "Ho". done.
  Qed.

  Lemma ocarrierG_carrier_delete i (KM : gmap ocid oids) g G :
    ocarrierG_carrier_auth i KM ∗ ocarrierG_carrier i g G
    ⊢ |==> ocarrierG_carrier_auth i (delete g KM).
  Proof.
    rewrite /ocarrierG_carrier_auth /ocarrierG_carrier -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update. apply gmap_view_delete.
  Qed.

  Lemma ocarrierG_carrier_update i KM g G1 G2 :
    ocarrierG_carrier_auth i KM ∗
    ocarrierG_carrier i g G1
    ⊢ |==> ocarrierG_carrier_auth i (<[g:=G2]>KM) ∗ ocarrierG_carrier i g G2.
  Proof.
    rewrite /ocarrierG_carrier_auth /ocarrierG_carrier -!own_op -!reservation_map_data_op.
    apply own_update, reservation_map_update, gmap_view_replace. done.
  Qed.

  Lemma ocarrierG_carrier_lookup i KM g G :
    ocarrierG_carrier_auth i KM ∗ ocarrierG_carrier i g G
    ⊢ ⌜ KM !! g = Some G ⌝.
  Proof.
    rewrite /ocarrierG_carrier_auth /ocarrierG_carrier -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_valid in H.
    destruct H as (?&?&?). iPureIntro. apply leibniz_equiv in H1. auto.
  Qed.

  Lemma ocarrierG_carrier_valid i g1 g2 K1 K2 :
    ocarrierG_carrier i g1 K1 ∗ ocarrierG_carrier i g2 K2
    ⊢ ⌜ g1 ≠ g2 ⌝.
  Proof.
    rewrite /ocarrierG_carrier -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    destruct (decide (g1 = g2)); auto. subst.
    apply reservation_map_data_valid, gmap_view_frag_op_valid in H. destruct H. done.
  Qed.

  (** Fuel rules *)
  Lemma ocarrierG_fuel_eq k a0 a1 :
    a0 w= a1 →
    ocarrierG_fuel k a0 = ocarrierG_fuel k a1.
  Proof. intros EQ. rewrite /ocarrierG_fuel. by erewrite credit_eq. Qed.

  Lemma ocarrierG_fuel_mon k a0 a1 :
    a0 w≤ a1 →
    ocarrierG_fuel k a1 ⊢ |==> ocarrierG_fuel k a0.
  Proof.
    intros LE. rewrite /ocarrierG_fuel. apply own_update.
    by apply reservation_map_update, credit_update.
  Qed.

  Lemma ocarrierG_fuel_split k a0 a1 :
    ocarrierG_fuel k (a0 w+ a1) ⊣⊢ ocarrierG_fuel k a0 ∗ ocarrierG_fuel k a1.
  Proof.
    rewrite /ocarrierG_fuel. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite credit_split). iSplitL "H1"; iFrame.
  Qed.

  Lemma ocarrierG_fuel_mon_split k a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    ocarrierG_fuel k a2 ⊢ |==> ocarrierG_fuel k a0 ∗ ocarrierG_fuel k a1.
  Proof.
    intros LE. iIntros "H". iApply ocarrierG_fuel_split. iApply ocarrierG_fuel_mon; done.
  Qed.

  Lemma ocarrierG_fuel_lt k a0 a1 :
    a0 w< a1 →
    ocarrierG_fuel k a1 ⊢ |==> ocarrierG_fuel k a0 ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ ocarrierG_fuel k c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (ocarrierG_fuel_mon_split _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.

  Lemma ocarrierG_bound_mon k a0 a1 :
    a0 w≤ a1 →
    ocarrierG_bound k a0 ⊢ |==> ocarrierG_bound k a1.
  Proof.
    intros LE. rewrite /ocarrierG_bound. apply own_update.
    by apply reservation_map_update, cmra_update_included, credit_bound_included.
  Qed.

  Lemma ocarrierG_fuel_spend_gen k a0 a1 :
    ocarrierG_bound k a0 ∗ ocarrierG_fuel k a1
    ⊢ |==> ∃ a2, ⌜(a1 w+ a2) w≤ a0⌝ ∗ ocarrierG_bound k a2.
  Proof.
    rewrite -own_op. iIntros "H". iMod (own_updateP with "H") as "(% & H)".
    { rewrite -!reservation_map_data_op.
      eapply (reservation_map_updateP
                (λ x, ∃ a2, (x = (credit_bound a2)) ∧ (a1 w+ a2 w≤ a0))
                (λ r, ∃ a2, (r = {[k := (credit_bound a2)]}) ∧ (a1 w+ a2 w≤ a0))
             ).
      { eapply credit_spend. }
      { intros. destruct H as (a2&A0&A1). eexists. by subst. }
    }
    iSimpl. iDestruct "H" as "((%a2 & %EQ & %LE) & H)".
    iExists a2. subst. iModIntro. iSplitR; done.
  Qed.
  Lemma ocarrierG_fuel_spend k a0 a1 :
    wzero w< a1 →
    ocarrierG_bound k a0 ∗ ocarrierG_fuel k a1 ⊢ |==> ∃ a2, ⌜a2 w< a0⌝ ∗ ocarrierG_bound k a2.
  Proof.
    iIntros (LT) "[Ow Oc]". iMod (ocarrierG_fuel_spend_gen with "[$]") as "(%&%&$)".
    iPureIntro. eapply WFOCM.lt_exists_right; eauto.
  Qed.

  Lemma ocarrierG_bound_fuel_compare k a0 a1 :
    ocarrierG_bound k a0 ∗ ocarrierG_fuel k a1 ⊢ ⌜ a1 w≤ a0 ⌝.
  Proof.
    rewrite -own_op -!reservation_map_data_op. iIntros "H".
    iPoseProof (own_valid with "H") as "%". apply reservation_map_data_valid in H.
    apply credit_bound_credit_valid_compare in H. done.
  Qed.

  Lemma ocarrierG_bound_id_alloc D k a :
    k ∉ D →
    ocarrierG_fuel_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> ocarrierG_fuel_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        ocarrierG_bound k a ∗ ocarrierG_fuel k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (credit_bound a ⋅ credit a) with "Htk") as "[Htk >H]"; auto.
    { apply credit_bound_credit_valid_eq. }
    iDestruct "H" as "[H1 H2]". rewrite /ocarrierG_bound /ocarrierG_fuel. by iFrame.
  Qed.

  Lemma ocarrierG_bound_op k a0 a1 :
    ocarrierG_bound k a0 ∗ ocarrierG_bound k a1 ⊢ ∃ a2, ocarrierG_bound k a2 ∧ ⌜ a2 w≤ a0 ∧ a2 w≤ a1 ⌝.
  Proof.
    rewrite -own_op -!reservation_map_data_op. destruct (credit_bound_op a0 a1) as (?&?&?&?).
    rewrite H. rewrite /ocarrierG_bound. iIntros "$". iPureIntro. split; auto.
  Qed.

  (** ocarrier rules *)
  Lemma ocarrier_alloc_thread i TP :
    i ∉ TP →
    ocarrier TP ∗ othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅
    ⊢ |==> ocarrier ({[i]} ∪ TP) ∗ ocarrierG_thread_auth i ∅ (1/2).
  Proof.
    iIntros (Hi) "(F& Tx& TG)".
    rewrite /ocarrier -!lock. iDestruct "F" as "(%& FT& WA& ST& OT& M)".
    iMod (ocarrierG_thread_alloc_auth _ i with "ST") as "[ST [Sa $]]". 1: auto.
    iMod (ocarrierG_carrier_alloc_auth _ i with "OT") as "[OT Oa]". 1: auto.
    iModIntro. iFrame "ST OT FT WA". iApply big_sepS_union. 1: set_solver.
    iFrame "M". iApply big_sepS_singleton. iFrame. iSplitR; first done.
    iSplitL; last done. iLeft. iFrame. done.
  Qed.

  Lemma ocarrier_alloc_threads Θ TP :
    Θ ## TP →
    ocarrier TP ∗ ([∗ set] i ∈ Θ, othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅)
    ⊢ |==> ocarrier (TP ∪ Θ) ∗ ([∗ set] i ∈ Θ, ocarrierG_thread_auth i ∅ (1/2)).
  Proof.
    revert TP. pattern Θ. revert Θ. apply set_ind.
    { solve_proper. }
    { iIntros (??) "[T _]". rewrite union_empty_r_L. iFrame. by iModIntro. }
    iIntros (i Θ Nin IH TP Disj) "[F M]".
    rewrite !big_sepS_union. 2,3: set_solver. rewrite !big_sepS_singleton. iDestruct "M" as "(Mi& M)".
    iMod (IH with "[$F $M]") as "(F& $)". 1: set_solver.
    iMod (ocarrier_alloc_thread i with "[$F $Mi]") as "(F& Hi)"; first set_solver.
    iModIntro. replace ({[i]} ∪ (TP ∪ Θ)) with (TP ∪ ({[i]} ∪ Θ)) by set_solver.
    iFrame.
  Qed.

  Lemma ocarrier_exec_to_done TP i :
    i ∈ TP →
    othread TP ∗ ocarrier TP ∗
    othreadG_exec i (1/2)%Qp ∗ ocarrierG_thread_auth i ∅ (1/2)%Qp
    ⊢ |==> othread TP ∗ ocarrier TP ∗ othreadG_done i.
  Proof.
    iIntros (Ini) "(T& G& Tx& Gta)".
    rewrite /ocarrier -!lock. iDestruct "G" as "(%& FT& WA& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta0& Gga& Hex& OFs)".
    iPoseProof (ocarrierG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    apply dom_empty_inv_L in Dom. subst. iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)". iCombine "Gta Gta0" as "Gta".
      iPoseProof (ocarrierG_thread_auth_valid with "[$Gta $Gta1]") as "%". destruct H. done. }
    iDestruct "Hex" as "(%& Tx2& TG& %)". destruct H as [Uni Disj].
    rewrite union_sets_empty in Uni. subst.
    iCombine "Tx Tx2" as "Tx".
    iMod (othread_exec_to_done with "[$T $Tx $TG]") as "[T #Td]".
    iModIntro. iFrame "T FT WA TT GT Td".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gta0 Gga". iSplit. 1: done.
    iSplitL "Gta".
    { iRight. iFrame. eauto. }
    done.
  Qed.

  Lemma ocarrier_alloc_carrier TP i G β :
    i ∈ TP →
    ocarrier TP ∗ ocarrierG_thread_auth i G (1/2)
    ⊢ |==> ∃ g, ocarrier TP ∗
             ⌜ g ∉ G ⌝ ∗ ocarrierG_thread_auth i ({[g]} ∪ G) (1/2) ∗
             ocarrierG_thread i g ∗ ocarrierG_carrier i g ∅ ∗
             ocarrierG_bound g β ∗ ocarrierG_fuel g β ∗
             ocarrierG_owned g i 1.
  Proof.
    iIntros (Ini) "(G& Gta)".
    rewrite /ocarrier -!lock. iDestruct "G" as "(%& FT& WA& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta0& Gga& Hex& OFs)".
    iPoseProof (ocarrierG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    iCombine "Gta Gta0" as "Gta". iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)".
      iPoseProof (ocarrierG_thread_auth_valid with "[$Gta $Gta1]") as "%". destruct H. done. }
    assert (∃ g, g ∉ ((dom Dg) ∪ G)) as (g&Hg).
    { eexists. eapply is_fresh. }
    iMod (ocarrierG_bound_id_alloc _ g β with "FT") as "(FT& #Bs& Hfs)". 1: set_solver.
    iMod (ocarrierG_thread_alloc _ _ g with "Gta") as "(Gta& Ps)". 1: set_solver.
    iMod (ghost_map_insert g i with "WA") as "[WA We]".
    { apply not_elem_of_dom. set_solver. }
    assert (LUg : KM !! g = None).
    { apply not_elem_of_dom. simplify_eq. set_solver. }
    iMod(ocarrierG_carrier_alloc _ _ g with "Gga") as "(Gga& Po)". 1: auto.
    iDestruct "Gta" as "[Gta Gta0]".
    iModIntro. iExists g. rewrite /ocarrierG_owned_auth /ocarrierG_owned.
    iFrame "Gta Ps Po Bs Hfs TT GT WA We". rewrite dom_insert_L. iFrame "FT".
    iSplit.
    2:{ iPureIntro. set_solver. }
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gta0 Gga". iSplit.
    { iPureIntro. rewrite !dom_insert_L Dom. auto. }
    iSplitL "Hex".
    { iLeft. iDestruct "Hex" as "(%& $& $& %)". iPureIntro. destruct H. simplify_eq.
      rewrite union_sets_insert_L. 2: auto. split; first set_solver.
      apply disjoint_sets_insert_2; auto. set_solver. }
    iApply big_sepM_insert; auto.
  Qed.

  Lemma ocarrier_delete_carrier TP i G g :
    i ∈ TP →
    ocarrier TP ∗ ocarrierG_thread_auth i G (1/2) ∗
    ocarrierG_thread i g ∗ ocarrierG_carrier i g ∅
    ⊢ |==> ocarrier TP ∗ ocarrierG_thread_auth i (G ∖ {[g]}) (1/2).
  Proof.
    iIntros (Ini) "(G& Gta& Ps& Po)".
    rewrite /ocarrier -!lock. iDestruct "G" as "(%& FT& WA& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta0& Gga& Hex& OFs)".
    iPoseProof (ocarrierG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    iCombine "Gta Gta0" as "Gta". iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)".
      iPoseProof (ocarrierG_thread_auth_valid with "[$Gta $Gta1]") as "%". destruct H. done. }
    iPoseProof (ocarrierG_thread_elem_of with "[$Gta $Ps]") as "%LUs".
    iMod (ocarrierG_thread_delete with "[$Gta $Ps]") as "[Gta Gta0]".
    iPoseProof (ocarrierG_carrier_lookup with "[$Gga $Po]") as "%LUo".
    iMod(ocarrierG_carrier_delete with "[$Gga $Po]") as "Gga".
    iModIntro. iFrame "Gta TT GT FT WA".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gta0 Gga". iSplit.
    { iPureIntro. rewrite !dom_delete_L Dom. auto. }
    iSplitL "Hex".
    { iLeft. iDestruct "Hex" as "(%& $& $& %)". iPureIntro. destruct H. subst.
      erewrite (union_sets_delete_L KM g). 2: eauto.
      split; first set_solver. apply disjoint_sets_delete; auto. }
    iPoseProof (big_sepM_delete _ _ g with "OFs") as "[_ $]"; eauto.
  Qed.

  Lemma ocarrier_alloc_obl Ω TP i g K β k :
    i ∈ TP →
    osat Ω ∗ othread TP ∗ ocarrier TP ∗
    ocarrierG_carrier i g K ∗ ocarrierG_thread i g ∗ ocarrierG_bound g β ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp ∗ oblG_fuel k β
    ⊢ |==> osat Ω ∗ othread TP ∗ ocarrier TP ∗
        ⌜k ∉ K⌝ ∗ ocarrierG_carrier i g ({[k]} ∪ K) ∗ ocarrierG_thread i g ∗
        othreadG_owns i k 1 ∗ oblG_owner k i (1/2 + 1/2/2/2 + 1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ini) "(S& T& G& Po& Ps& #Tb& #Oe& Oo& Of)".
    rewrite /ocarrier -!lock. iDestruct "G" as "(%& FT& WA& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta& Gga& Hex& OFs)".
    iPoseProof (ocarrierG_thread_elem_of with "[$Gta $Ps]") as "%LUs".
    iPoseProof (ocarrierG_carrier_lookup with "[$Gga $Po]") as "%LUo".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (big_sepM_delete _ _ _ _ LUo with "OFs") as "[Hp OFs]".
    iDestruct "Hp" as "(%& #Tb0& Hfs)".
    iPoseProof (ocarrierG_bound_op _ β β0 with "[$Tb $Tb0]") as "(%β1& #Tb1& %Hb)".
    destruct Hb as [Hb1 Hb2]. iClear "Tb Tb0".
    iMod (othread_alloc_obl with "[$S $T $TG $Oe $Oo]") as "(S& T& %Nink& TG& To& Oo)".
    iMod (ocarrierG_carrier_update _ _ _ _ ({[k]} ∪ K) with "[$Gga $Po]") as "[Gga Po]".
    iModIntro. iFrame "S T FT WA TT GT Ps To Oo Po".
    assert (Nink2 : k ∉ K).
    { simplify_eq. rewrite not_elem_of_union_sets in Nink. eapply Nink; eauto. }
    iSplit. 2: auto.
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gga Gta". iSplitR.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUo. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. replace ({[k]} ∪ K) with (K ∪ {[k]}) by set_solver. simplify_eq. split.
      - rewrite union_sets_insert_union_L; auto.
      - apply disjoint_sets_insert_union_singleton_not_in; auto. }
    iApply big_sepM_insert_delete. iFrame "OFs Tb1". iApply (big_sepS_union). 1: set_solver.
    iSplitR "Hfs".
    { iApply big_sepS_singleton. iFrame "Of Oe". iPureIntro. eauto. }
    { iApply (big_sepS_impl with "Hfs"). iIntros "!> %% (%&%&$&$)". iPureIntro. etrans; eauto. }
  Qed.

  Lemma ocarrier_delete_obl TP i g K k :
    i ∈ TP →
    k ∈ K →
    othread TP ∗ ocarrier TP ∗
    ocarrierG_carrier i g K ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ ocarrier TP ∗
        ocarrierG_carrier i g (K ∖ {[k]}) ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ini Ink) "(T& G& Po& To)".
    rewrite /ocarrier -!lock. iDestruct "G" as "(%& FT& WA& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta& Gga& Hex& OFs)".
    iPoseProof (ocarrierG_carrier_lookup with "[$Gga $Po]") as "%LUo".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (big_sepM_delete _ _ _ _ LUo with "OFs") as "(Hp& OFs)".
    iDestruct "Hp" as "(%& #Tb& Hfs)".
    iMod (othread_delete_obl with "[$T $TG $To]") as "(T& TG& Oo)".
    iMod (ocarrierG_carrier_update _ _ _ _ (K ∖ {[k]}) with "[$Gga $Po]") as "[Gga Po]".
    iModIntro. iFrame "T FT WA TT GT Oo Po".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gga Gta". iSplitR.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUo. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. simplify_eq. split.
      - rewrite union_sets_insert_difference_singleton_L; auto.
      - apply disjoint_sets_insert_difference; auto. }
    iApply big_sepM_insert_delete. iFrame "OFs". iFrame "Tb".
    iPoseProof (big_sepS_delete with "Hfs") as "[_ $]". auto.
  Qed.

  Lemma ocarrier_exchange_fuel TP i GS q c :
    i ∈ TP →
    (Ord.O < c)%ord →
    ocarrier TP ∗
    ocarrierG_thread_auth i GS q ∗
    ([∗ set] g ∈ GS, ocarrierG_fuel g c)
    ⊢ |==> ∃ G, (othreadG_exec i (1 / 2 / 2) -∗ othreadG_obls i G -∗ ocarrier TP) ∗
             ocarrierG_thread_auth i GS q ∗
             othreadG_exec i (1 / 2 / 2) ∗ othreadG_obls i G ∗
             ([∗ set] k ∈ G, oblG_fuel k Ord.one ∗ oblG_elem k).
  Proof.
    iIntros (Ini Ltc) "(G& Gta& Tfs)".
    rewrite /ocarrier -!lock. iDestruct "G" as "(%& FT& WA& TT& GT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta0& Gga& Hex& OFs)".
    iPoseProof (ocarrierG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H as [<- _].
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Gta1& _)". iCombine "Gta0 Gta1" as "Gta0".
      iPoseProof (ocarrierG_thread_auth_valid with "[$Gta $Gta0]") as "%". destruct H.
      apply Qp.not_add_le_r in H0. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iAssert (
        |==> ([∗ map] g ↦ K ∈ KM,
             ∃ β, ocarrierG_bound g β ∗ ([∗ set] k ∈ K, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)) ∗
          ([∗ map] K ∈ KM, ([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k)))%I
      with "[Tfs OFs]" as ">[OFs Fs]".
    { simplify_eq. iPoseProof (big_sepM_dom with "Tfs") as "Tfs".
      iPoseProof (big_sepM_sep with "[$OFs $Tfs]") as "F".
      iApply big_sepM_sep. iApply big_sepM_bupd.
      iApply (big_sepM_impl with "F"). iIntros "!> %%% [H F]".
      iDestruct "H" as "(%& #Tb& KFs)". rename x into K.
      iMod (ocarrierG_fuel_spend with "[$Tb $F]") as "(%β1& %HB& #Tb1)". 1: auto.
      iAssert (|==> ([∗ set] k ∈ K, ∃ a : Ord.t, ⌜(β1 <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k) ∗
                 ([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k))%I with "[KFs]" as ">[Fvs Rvs]".
      { iApply big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "KFs").
        iIntros "!> %% (%&%& F& #E)". iFrame "E". iMod (oblG_fuel_lt _ β1 with "F") as "(F& %& %& F1)".
        { eapply Ord.lt_le_lt; eauto. }
        iMod (oblG_fuel_mon _ Ord.one with "F1") as "F1".
        { apply Ord.S_supremum. auto. }
        iModIntro. iSplitR "F1"; iFrame. done. }
      iFrame. eauto. }
    iModIntro. iFrame "Gta Tx TG". iSplitR "Fs".
    - iIntros "Tx TG". iFrame "FT WA TT GT". 
      iApply (big_sepS_delete _ _ _ Ini). iFrame "M". iFrame "Gta0 Gga". iSplit. 1: done.
      iFrame "OFs". iLeft. iFrame. eauto.
    - subst. clear dependent TP i q c Dg. iInduction KM as [ | g K ?? LUp] using map_ind.
      { rewrite union_sets_empty. done. }
      rewrite union_sets_insert_L; last auto. iApply (big_sepS_union).
      { eapply disjoint_sets_insert_disjoint_union_sets; eauto. }
      iPoseProof (big_sepM_insert with "Fs") as "[F Fs]". 1: auto.
      apply disjoint_sets_insert in Disj; last auto. destruct Disj as [MF Disj].
      iPoseProof ("LUp" with "[//] Fs") as "$". iFrame.
  Qed.

  Lemma ocarrier_obl_change_carrier TP i g1 g2 K1 K2 β k :
    i ∈ TP →
    k ∈ K1 →
    ocarrier TP ∗ ocarrierG_carrier i g1 K1 ∗ ocarrierG_carrier i g2 K2 ∗
    ocarrierG_bound g2 β ∗ oblG_fuel k β
    ⊢ |==> ocarrier TP ∗ ocarrierG_carrier i g1 (K1 ∖ {[k]}) ∗ ocarrierG_carrier i g2 (K2 ∪ {[k]}).
  Proof.
    iIntros (Ini Ink) "(G& Po1& Po2& #Tb& Of)".
    rewrite /ocarrier -!lock. iDestruct "G" as "(%& FT& WA& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%& %Dom& Gta& Gga& Hex& OFs)".
    iPoseProof (ocarrierG_carrier_lookup with "[$Gga $Po1]") as "%LUo1".
    assert (LUs1 : g1 ∈ G).
    { apply elem_of_dom_2 in LUo1. rewrite -Dom. auto. }
    iPoseProof (ocarrierG_carrier_lookup with "[$Gga $Po2]") as "%LUo2".
    assert (LUs2 : g2 ∈ G).
    { apply elem_of_dom_2 in LUo2. rewrite -Dom. auto. }
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (ocarrierG_carrier_valid _ g1 g2 with "[$Po1 $Po2]") as "%Neqp".
    iMod (ocarrierG_carrier_update _ _ _ _ (K1 ∖ {[k]}) with "[$Gga $Po1]") as "[Gga Po1]".
    iMod (ocarrierG_carrier_update _ _ _ _ (K2 ∪ {[k]}) with "[$Gga $Po2]") as "[Gga Po2]".
    iModIntro. iFrame "FT WA ST PT Po1 Po2".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Gga Gta". iSplitR.
    { iPureIntro. rewrite !dom_insert_L. apply elem_of_dom_2 in LUo1, LUo2. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. assert (Ink2 : k ∈ union_sets KM).
      { apply elem_of_union_sets; eauto. }
      simplify_eq. split.
      - rewrite union_sets_insert_union_L; cycle 1.
        { rewrite lookup_insert_ne; auto. }
        rewrite union_sets_insert_difference_singleton_L; auto. rewrite -union_difference_L; set_solver.
      - apply disjoint_sets_insert_union_singleton_not_in.
        { rewrite lookup_insert_ne; auto. }
        { apply disjoint_sets_insert_difference; auto. }
        { apply not_elem_of_union_sets. intros. destruct (decide (k0 = g1)).
          - subst. rewrite lookup_insert_eq in H. simplify_eq. set_solver.
          - rewrite lookup_insert_ne in H; auto. specialize (Disj _ _ _ _ n H LUo1). set_solver. }
    }
    iApply big_sepM_insert_delete.
    iPoseProof (big_sepM_delete _ _ _ _ LUo2 with "OFs") as "[Fs2 OFs]".
    iPoseProof (big_sepM_delete _ _ g1 K1 with "OFs") as "[Fs1 OFs]".
    { rewrite lookup_delete_ne; auto. }
    iDestruct "Fs1" as "(%βp1& #Bp1& Fs1)". iPoseProof (big_sepS_delete _ _ _ Ink with "Fs1") as "[Fk Fs1]".
    iSplitL "Of Fk Fs2".
    { iDestruct "Fk" as "(%&%&_&#Oe)". iDestruct "Fs2" as "(%& #Tb0& Fs)".
      iPoseProof (ocarrierG_bound_op _ β β0 with "[$Tb $Tb0]") as "(%β1& #Tb1& %Hb)".
      destruct Hb as [Hb1 Hb2]. iClear "Tb Tb0".
      iFrame "Tb1". iApply big_sepS_union.
      { specialize (Disj _ _ _ _ Neqp LUo1 LUo2). set_solver. }
      iSplitL "Fs".
      { iApply (big_sepS_impl with "Fs"). iIntros "!> %% (%& %& $& $)". iPureIntro. etrans; eauto. }
      iApply big_sepS_singleton. iFrame "Oe Of". iPureIntro. auto. }
    rewrite !delete_insert_ne; auto. iApply big_sepM_insert_delete. iFrame "OFs".
    iFrame "Bp1". iFrame.
  Qed.

  Lemma ocarrier_obl_change_thread TP i1 i2 g1 g2 K1 K2 β k :
    i1 ∈ TP →
    i2 ∈ TP →
    k ∈ K1 →
    i1 ≠ i2 →
    ocarrier TP ∗ ocarrierG_carrier i1 g1 K1 ∗ ocarrierG_carrier i2 g2 K2 ∗
    ocarrierG_bound g2 β ∗ oblG_fuel k β
    ⊢ |==> ∃ G1 G2,
      (⌜ k ∉ G2 ⌝ -∗ othreadG_exec i1 (1/2/2) -∗ othreadG_obls i1 (G1 ∖ {[k]}) -∗
       othreadG_exec i2 (1/2/2) -∗ othreadG_obls i2 ({[k]} ∪ G2) -∗ ocarrier TP) ∗
      ⌜ k ∈ G1 ⌝ ∗
      othreadG_exec i1 (1/2/2) ∗ othreadG_obls i1 G1 ∗
      othreadG_exec i2 (1/2/2) ∗ othreadG_obls i2 G2 ∗
      ocarrierG_carrier i1 g1 (K1 ∖ {[k]}) ∗ ocarrierG_carrier i2 g2 (K2 ∪ {[k]}).
  Proof.
    iIntros (Ini1 Ini2 Ink Nei) "(G& Po1& Po2& #Tb& Of)".
    rewrite /ocarrier -!lock. iDestruct "G" as "(%& FT& WA& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini1 with "M") as "[Mi M]".
    iDestruct "Mi" as "(%KM1& %B1& %Dom1& Gta1& Gga1& Hex1& OFs1)".
    iPoseProof (ocarrierG_carrier_lookup with "[$Gga1 $Po1]") as "%LUo1".
    assert (LUs1 : g1 ∈ B1).
    { apply elem_of_dom_2 in LUo1. rewrite -Dom1. auto. }
    assert (Ini2' : i2 ∈ (TP ∖ {[i1]})) by set_solver.
    iPoseProof (big_sepS_delete _ _ _ Ini2' with "M") as "[Mi M]".
    iDestruct "Mi" as "(%KM2& %B2& %Dom2& Gta2& Gga2& Hex2& OFs2)".
    iPoseProof (ocarrierG_carrier_lookup with "[$Gga2 $Po2]") as "%LUo2".
    assert (LUs2 : g2 ∈ B2).
    { apply elem_of_dom_2 in LUo2. rewrite -Dom2. auto. }
    iDestruct "Hex1" as "[Hex1 | Hex1]"; cycle 1.
    { iDestruct "Hex1" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex1" as "(%G1& Tx1& TG1& %)". destruct H as [Uni1 Disj1].
    iDestruct "Hex2" as "[Hex2 | Hex2]"; cycle 1.
    { iDestruct "Hex2" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex2" as "(%G2& Tx2& TG2& %)". destruct H as [Uni2 Disj2].
    iMod (ocarrierG_carrier_update _ _ _ _ (K1 ∖ {[k]}) with "[$Gga1 $Po1]") as "[Gga1 Po1]".
    iMod (ocarrierG_carrier_update _ _ _ _ (K2 ∪ {[k]}) with "[$Gga2 $Po2]") as "[Gga2 Po2]".
    assert (Ink2 : k ∈ G1).
    { subst. apply elem_of_union_sets; eauto. }
    iModIntro. iFrame "Tx1 Tx2 TG1 TG2 Po1 Po2". iSplit; last auto.
    iIntros (Nink) "Tx1 TG1 Tx2 TG2". iFrame "FT WA ST PT".
    iPoseProof (big_sepM_delete _ _ _ _ LUo1 with "OFs1") as "[OF OFs1]".
    iDestruct "OF" as "(%& #Tb0& OF)". iPoseProof (big_sepS_delete _ _ _ Ink with "OF") as "[Hof OF]".
    iApply (big_sepS_delete _ _ _ Ini1). iSplitL "Gta1 Gga1 Tx1 TG1 OFs1 OF".
    { iFrame "Gta1 Gga1". iSplit.
      { iPureIntro. rewrite dom_insert_L Dom1. set_solver. }
      iSplitL "Tx1 TG1".
      { iLeft. iFrame. iPureIntro. simplify_eq. split.
        - rewrite union_sets_insert_difference_singleton_L; auto.
        - apply disjoint_sets_insert_difference; auto. }
      iApply big_sepM_insert_delete. iFrame "OFs1". iFrame "Tb0 OF". }
    iApply (big_sepS_delete _ _ _ Ini2'). iFrame "M".
    iFrame "Gta2 Gga2". iSplitR.
    { iPureIntro. rewrite !dom_insert_L. apply elem_of_dom_2 in LUo2. set_solver. }
    iSplitL "Tx2 TG2".
    { iLeft. iFrame. iPureIntro. simplify_eq. split.
      - rewrite union_sets_insert_union_L; auto.
      - apply disjoint_sets_insert_union_singleton_not_in; auto. }
    iApply big_sepM_insert_delete.
    iPoseProof (big_sepM_delete _ _ _ _ LUo2 with "OFs2") as "[Fs2 OFs2]". iFrame "OFs2".
    iDestruct "Fs2" as "(%& #Tb1& F)". iPoseProof (ocarrierG_bound_op _ β β1 with "[$Tb $Tb1]") as "(%& #Tb'& %)".
    destruct H. iFrame "Tb'". iApply (big_sepS_union_2 with "[F] [-]").
    { iApply (big_sepS_impl with "F"). iIntros "!> %% (%& %& $& $)". iPureIntro. etrans; eauto. }
    { iDestruct "Hof" as "(%& _& _& #Ok)". iApply big_sepS_singleton. iFrame "Of Ok". iPureIntro. auto. }
  Qed.

End ocarrier.

(* Allocation of an initial ocarrier protocol. *)
Definition ocarrier_alloc `{SI : sidx} {Σ}
  `{!@osatGS.osatGS _ Σ} `{!othreadGS.othreadGS Σ} `{!ocarrierGpreS Σ} :
  ⊢ |==> ∃ _ : ocarrierGS Σ, ocarrier ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR ocid (unit))) ⊤)) as (γI) "HI";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR ocid (gsetUR oid))) ⊤)) as (γP) "HP";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=bcredUR) ⊤)) as (γF) "HF";
    first by apply reservation_map_token_valid.
  iMod (ghost_map_alloc_empty) as (γW) "HW".
  iModIntro. iExists (OcarrierG SI _ _ γI γP γF γW).
  rewrite /ocarrier -!lock.
  iExists ∅. rewrite /ocarrierG_owned_auth /ocarrierG_thread_token /ocarrierG_carrier_token.
  rewrite dom_empty_L.
  do 3 replace (⊤ ∖ gset_to_coPset (∅ : gset _)) with (⊤ : coPset) by set_solver.
  iFrame. done.
Qed.
