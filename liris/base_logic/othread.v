From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_map.
From liris.algebra Require Export wfocm.
From liris.algebra Require Import bcred ordinal_ucmra.
From liris.base_logic Require Export osat.

Definition term := positive.

(** The ghost state for thread obls *)
Module othreadGS.

  (* Assumes thread ids are positive *)
  Class othreadGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadGpreS {
        othreadGpreS_owns : inG Σ (reservation_mapUR (gmap_viewR oid (unitUR)));
        othreadGpreS_obls : inG Σ (gmap_viewR positive (gsetUR oid));
        othreadGpreS_exec : inG Σ (reservation_mapUR mono_natUR);
        othreadGpreS_elem : inG Σ (gmap_viewR positive unitUR);
        (* othreadGpreS_term : inG Σ (gmap_viewR positive (agreeR term)); *)
        othreadGpreS_fuel : inG Σ (reservation_mapUR (bcredUR));
        (* othreadGpreS_ceil : inG Σ (gmap_viewR positive (agreeR obl_fuel)); *)
        othreadGpreS_frag : inG Σ (gmap_viewR positive (gset_disjUR oid));
      }.

  Class othreadGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadG {
        othread_inG : othreadGpreS Σ;
        owns_name : gname;
        obls_name : gname;
        exec_name : gname;
        elem_name : gname;
        fuel_name : gname;
        frag_name : gname;
        term_inG :: ghost_mapG Σ positive term;
        term_name : gname;
        ceil_inG :: ghost_mapG Σ positive obl_fuel;
        ceil_name : gname;
      }.

  Definition othreadΣ_pre `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR oid (unitUR)));
      GFunctor (gmap_viewR positive (gsetUR oid));
      GFunctor (reservation_mapUR mono_natUR);
      GFunctor (gmap_viewR positive unitUR);
      (* GFunctor (gmap_viewR positive (agreeR term)); *)
      GFunctor (reservation_mapUR bcredUR);
      (* GFunctor (gmap_viewR positive (agreeR obl_fuel)) *)
      GFunctor (gmap_viewR positive (gset_disjUR oid))
      ].

  Definition othreadΣ `{SI : indexT} : gFunctors  :=
    gFunctors.app othreadΣ_pre (gFunctors.app (ghost_mapΣ positive term) (ghost_mapΣ positive obl_fuel)).

  Global Instance subG_othreadΣ_0 `{SI : indexT} {Σ} : subG (othreadΣ) Σ → (othreadGpreS Σ).
  Proof. intros. apply subG_inv in H. destruct H. clear s0. solve_inG. Qed.
  Global Instance subG_othreadΣ_1 `{SI : indexT} {Σ} : subG (othreadΣ) Σ → (ghost_mapG Σ positive term).
  Proof. intros. apply subG_inv in H. destruct H. apply subG_inv in s0. destruct s0. apply subG_ghost_mapΣ. auto. Qed.
  Global Instance subG_othreadΣ_2 `{SI : indexT} {Σ} : subG (othreadΣ) Σ → (ghost_mapG Σ positive obl_fuel).
  Proof. intros. apply subG_inv in H. destruct H. apply subG_inv in s0. destruct s0. apply subG_ghost_mapΣ. auto. Qed.

End othreadGS.
Import othreadGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances othread_inG
  othreadGpreS_owns othreadGpreS_obls othreadGpreS_exec othreadGpreS_elem
  othreadGpreS_fuel othreadGpreS_frag.
  (* othreadGpreS_term *) (* othreadGpreS_ceil *)

(* Owns: thread currently has this obl *)
Definition othreadG_owns `{SI : indexT} `{!othreadGS Σ} (i : positive) (k : oid) (q : Qp) : iProp Σ :=
  own owns_name (reservation_map_data i (gmap_view_frag k (DfracOwn q) ())).
Global Typeclasses Opaque othreadG_owns.
Global Instance: Params (@othreadG_owns) 3 := {}.

Local Definition othreadG_owns_token_id `{SI : indexT} `{!othreadGS Σ} TP : iProp Σ :=
  (own owns_name (reservation_map_token (A:=gmap_viewR oid (unitUR)) (⊤ ∖ gset_to_coPset TP))).

Local Definition othreadG_owns_auth_obls `{SI : indexT} `{!othreadGS Σ}
  i (TObls : gmap oid unit) : iProp Σ :=
  (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (TObls)))).

(* Obls: live obls assigned to this thread, also fix to empty when thread terminates *)
Definition othreadG_obls `{SI : indexT} `{!othreadGS Σ} (i : positive) (G : oids) : iProp Σ :=
  own obls_name (gmap_view_frag i (DfracOwn 1) (G)).
Global Typeclasses Opaque othreadG_obls.
Global Instance: Params (@othreadG_obls) 3 := {}.

Local Definition othreadG_obls_auth_id `{SI : indexT} `{!othreadGS Σ}
  (Tgls : gmap positive (gmap oid unit)) : iProp Σ :=
  (own obls_name (gmap_view_auth (DfracOwn 1) (dom <$> Tgls))).

(* Exec: tracks whether thread is executing or terminated *)
Definition othreadG_exec `{SI : indexT} `{!othreadGS Σ} (i : positive) (q : Qp) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN{#q} 0)).
Global Typeclasses Opaque othreadG_exec.
Global Instance: Params (@othreadG_exec) 3 := {}.

Definition othreadG_done_auth `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN 1)).
Global Typeclasses Opaque othreadG_done_auth.
Global Instance: Params (@othreadG_done_auth) 3 := {}.

Definition othreadG_done `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (◯MN 1)).
Global Typeclasses Opaque othreadG_done.
Global Instance: Params (@othreadG_done) 3 := {}.

Local Definition othreadG_exec_token_id `{SI : indexT} `{!othreadGS Σ} TP : iProp Σ :=
  (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset TP))).

(* Elem: keeps the fact that a key is inside a map *)
Definition othreadG_elem `{SI : indexT} `{!othreadGS Σ} (i : positive) : iProp Σ :=
  own elem_name (gmap_view_frag i DfracDiscarded ()).
Global Typeclasses Opaque othreadG_elem.
Global Instance: Params (@othreadG_elem) 3 := {}.

Local Definition othreadG_elem_auth_id `{SI : indexT} `{!othreadGS Σ}
  (Tgls : gmap positive (gmap oid unit)) : iProp Σ :=
  (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> Tgls))).

(* Term: tracks current term of the thread *)
Definition othreadG_term `{SI : indexT} `{!othreadGS Σ} (i : positive) (e : term) (q : Qp) : iProp Σ :=
  i ↪[ term_name ]{#q} e.
Global Typeclasses Opaque othreadG_term.
Global Instance: Params (@othreadG_term) 3 := {}.

Local Definition othreadG_term_auth_id `{SI : indexT} `{!othreadGS Σ}
  (Tes : gmap positive term) : iProp Σ :=
  ghost_map_auth term_name 1 Tes.

(* Fuel: manage fuels for the thread's obligations *)
Definition othreadG_bound `{SI : indexT} `{!othreadGS Σ}
  (e : term) (β : obl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bcredUR) e (credit_bound β)).
Global Typeclasses Opaque othreadG_bound.
Global Instance: Params (@othreadG_bound) 3 := {}.

Definition othreadG_fuel `{SI : indexT} `{!othreadGS Σ}
  (e : term) (a : obl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bcredUR) e (credit a)).
Global Typeclasses Opaque othreadG_fuel.
Global Instance: Params (@othreadG_fuel) 3 := {}.

Local Definition othreadG_fuel_token_id `{SI : indexT} `{!othreadGS Σ}
  (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_token (A:=bcredUR) E).

(* Ceil: ceil (upperbound) of the thread's fuel *)
Definition othreadG_ceil `{SI : indexT} `{!othreadGS Σ} (i : positive) (ℵ : obl_fuel) (q : Qp) : iProp Σ :=
  i ↪[ ceil_name ]{#q} ℵ.
Global Typeclasses Opaque othreadG_ceil.
Global Instance: Params (@othreadG_ceil) 3 := {}.

Local Definition othreadG_ceil_auth_id `{SI : indexT} `{!othreadGS Σ}
  (Tcs : gmap positive obl_fuel) : iProp Σ :=
  ghost_map_auth ceil_name 1 Tcs.

(* Frag: tracks fragments of the thread's obligations *)
Definition othreadG_frag `{SI : indexT} `{!othreadGS Σ} (i : positive) (G : oids) (q : Qp) : iProp Σ :=
  own frag_name (gmap_view_frag i (DfracOwn q) (GSet G)).
Global Typeclasses Opaque othreadG_frag.
Global Instance: Params (@othreadG_frag) 3 := {}.

Local Definition othreadG_frag_auth_id `{SI : indexT} `{!othreadGS Σ}
  (Tos : gmap positive (oids)) : iProp Σ :=
  (own frag_name (gmap_view_auth (DfracOwn 1) (GSet <$> Tos))).

(* Global invariant for threads' obligations. *)
Definition othread `{SI : indexT} {Σ} `{!@osatGS.osatGS _ Σ} `{!othreadGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (Tgls : gmap positive (gmap oid unit)),
        (⌜ dom Tgls = TP ⌝) ∗
        othreadG_owns_token_id TP ∗
        othreadG_obls_auth_id Tgls ∗
        othreadG_exec_token_id TP ∗
        othreadG_elem_auth_id Tgls ∗
        ([∗ map] i ↦ TObls ∈ Tgls,
           (othreadG_exec i (1/2/2)%Qp ∨ (othreadG_done_auth i ∗ othreadG_obls i ∅)) ∗
           othreadG_owns_auth_obls i TObls ∗
           ([∗ map] k ↦ _ ∈ TObls, oblG_owner k i (1/2/2/2/2)%Qp)
        )
    )%I.

(* Global invariant that relates obligations to the thread pool. *)
Definition oassigned `{SI : indexT} {Σ} `{!@osatGS.osatGS _ Σ} `{!othreadGS Σ}
  (Gls : oids) : iProp Σ :=
  locked
    ([∗ set] k ∈ Gls,
       oblG_elem k ∗
       ((∃ i, oblG_owner k i (1/2/2/2/2)%Qp ∗ othreadG_owns i k (1/2/2)%Qp ∗ othreadG_elem i) ∨
          (oblG_fulfilled k)))%I.

(* Global invariant for threads' obligation fragments, terms, and fuels. *)
Definition ofrag `{SI : indexT} {Σ} `{!@osatGS.osatGS _ Σ} `{!othreadGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (Tes : gmap positive term) (Tcs : gmap positive obl_fuel) (Tos : gmap positive oids) (FD : gset positive),
        (⌜ dom Tes = TP ∧ dom Tcs = TP ∧ dom Tos = TP ⌝) ∗
        othreadG_term_auth_id Tes ∗
        othreadG_ceil_auth_id Tcs ∗
        othreadG_frag_auth_id Tos ∗
        othreadG_fuel_token_id (⊤ ∖ (gset_to_coPset FD)) ∗
        ([∗ set] i ∈ TP,
           ∃ (e : term) (β ℵ : obl_fuel) (G : oids),
             ⌜ Tes !! i = Some e ∧ Tcs !! i = Some ℵ ∧ (β <= ℵ)%ord ∧ Tos !! i = Some G ⌝ ∗
             ((othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i G) ∨ (othreadG_done i ∗ ⌜ G = ∅ ⌝)) ∗
             othreadG_bound e β ∗
             ([∗ set] g ∈ G, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel g a))
    )%I.

Section othread.
  Context `{SI : indexT} `{OSAT : !osatGS.osatGS Σ} `{!othreadGS Σ} `{OMF : !ord_mono_fun_class}.

  (* Owns *)
  Global Instance othreadG_owns_timeless i k q : Timeless (othreadG_owns i k q).
  Proof. rewrite /othreadG_owns. apply _. Qed.

  Global Instance othreadG_owns_fractional i k :
    Fractional (othreadG_owns i k).
  Proof.
    rewrite /othreadG_owns. intros p q.
    by rewrite -own_op -!reservation_map_data_op -gmap_view_frag_op.
  Qed.
  Global Instance othreadG_owns_as_fractional i k q :
    AsFractional (othreadG_owns i k q) (othreadG_owns i k) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance othreadG_owns_token_id_timeless TP : Timeless (othreadG_owns_token_id TP).
  Proof. rewrite /othreadG_owns_token_id. apply _. Qed.
  Local Instance othreadG_owns_auth_obls_timeless i TObls : Timeless (othreadG_owns_auth_obls i TObls).
  Proof. rewrite /othreadG_owns_auth_obls. apply _. Qed.

  (* Obls *)
  Global Instance othreadG_obls_timeless i G : Timeless (othreadG_obls i G).
  Proof. rewrite /othreadG_obls. apply _. Qed.

  Local Instance othreadG_obls_auth_id_timeless Tgls : Timeless (othreadG_obls_auth_id Tgls).
  Proof. rewrite /othreadG_obls_auth_id. apply _. Qed.

  (* Exec *)
  Global Instance othreadG_exec_timeless i q : Timeless (othreadG_exec i q).
  Proof. rewrite /othreadG_exec. apply _. Qed.

  Global Instance othreadG_exec_fractional i :
    Fractional (othreadG_exec i).
  Proof.
    rewrite /othreadG_exec. intros p q.
    by rewrite -own_op -!reservation_map_data_op -mono_nat_auth_dfrac_op.
  Qed.
  Global Instance othreadG_exec_as_fractional i q :
    AsFractional (othreadG_exec i q) (othreadG_exec i) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance othreadG_done_auth_timeless i : Timeless (othreadG_done_auth i).
  Proof. rewrite /othreadG_done_auth. apply _. Qed.

  Global Instance othreadG_done_persistent i : Persistent (othreadG_done i).
  Proof. rewrite /othreadG_done. apply _. Qed.
  Global Instance othreadG_done_timeless i : Timeless (othreadG_done i).
  Proof. rewrite /othreadG_done. apply _. Qed.

  Local Instance othreadG_exec_token_id_timeless TP : Timeless (othreadG_exec_token_id TP).
  Proof. rewrite /othreadG_exec_token_id. apply _. Qed.

  (* Elem *)
  Global Instance othreadG_elem_persistent i : Persistent (othreadG_elem i).
  Proof. rewrite /othreadG_elem. apply _. Qed.
  Global Instance othreadG_elem_timeless i : Timeless (othreadG_elem i).
  Proof. rewrite /othreadG_elem. apply _. Qed.

  Local Instance othreadG_elem_auth_id_timeless Tgls : Timeless (othreadG_elem_auth_id Tgls).
  Proof. rewrite /othreadG_elem_auth_id. apply _. Qed.

  (* Term *)
  Global Instance othreadG_term_timeless i e q : Timeless (othreadG_term i e q).
  Proof. rewrite /othreadG_term. apply _. Qed.

  Global Instance othreadG_term_fractional i e :
    Fractional (othreadG_term i e).
  Proof.
    rewrite /othreadG_term. apply _.
  Qed.
  Global Instance othreadG_term_as_fractional i e q :
    AsFractional (othreadG_term i e q) (othreadG_term i e) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance othreadG_term_auth_id_timeless Tes : Timeless (othreadG_term_auth_id Tes).
  Proof. rewrite /othreadG_term_auth_id. apply _. Qed.

  (* Fuel *)
  Global Instance othreadG_bound_persistent e β : Persistent (othreadG_bound e β).
  Proof. rewrite /othreadG_bound. apply _. Qed.
  Global Instance othreadG_bound_timeless e β : Timeless (othreadG_bound e β).
  Proof. rewrite /othreadG_bound. apply _. Qed.

  Global Instance othreadG_fuel_timeless e a : Timeless (othreadG_fuel e a).
  Proof. rewrite /othreadG_fuel. apply _. Qed.

  Local Instance othreadG_fuel_token_id_timeless E : Timeless (othreadG_fuel_token_id E).
  Proof. rewrite /othreadG_fuel_token_id. apply _. Qed.

  (* Ceil *)
  Global Instance othreadG_ceil_timeless i ℵ q : Timeless (othreadG_ceil i ℵ q).
  Proof. rewrite /othreadG_ceil. apply _. Qed.

  Global Instance othreadG_ceil_fractional i ℵ :
    Fractional (othreadG_ceil i ℵ).
  Proof.
    rewrite /othreadG_ceil. apply _.
  Qed.
  Global Instance othreadG_ceil_as_fractional i ℵ q :
    AsFractional (othreadG_ceil i ℵ q) (othreadG_ceil i ℵ) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance othreadG_ceil_auth_id_timeless Tcs : Timeless (othreadG_ceil_auth_id Tcs).
  Proof. rewrite /othreadG_ceil_auth_id. apply _. Qed.

  (* Frag *)
  Global Instance othreadG_frag_timeless i G q : Timeless (othreadG_frag i G q).
  Proof. rewrite /othreadG_frag. apply _. Qed.

  Local Instance othreadG_frag_auth_id_timeless Tgls : Timeless (othreadG_frag_auth_id Tgls).
  Proof. rewrite /othreadG_frag_auth_id. apply _. Qed.

  (* Invs *)
  Global Instance othread_timeless TP : Timeless (othread TP).
  Proof. rewrite /othread -lock. apply _. Qed.

  Global Instance oassigned_timeless Gls : Timeless (oassigned Gls).
  Proof. rewrite /oassigned -lock. apply _. Qed.

  Global Instance ofrag_timeless TP : Timeless (ofrag TP).
  Proof. rewrite /ofrag -lock. apply _. Qed.

  (** Elem rules *)
  Lemma othreadG_elem_alloc (Tgls : gmap positive (gmap oid unit)) i M :
    Tgls !! i = None →
    othreadG_elem_auth_id Tgls
    ⊢  |==> othreadG_elem_auth_id (<[i:=M]>Tgls) ∗
         othreadG_elem i.
  Proof.
    rewrite /othreadG_elem_auth_id.
    iIntros (Hi) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracDiscarded) ()); try done.
      rewrite !lookup_fmap Hi. done.
    }
    iDestruct "H" as "[H He]". rewrite /othreadG_elem. iFrame "He".
    rewrite fmap_insert. done.
  Qed.

  Lemma othreadG_elem_elem i (Tgls : gmap positive (gmap oid unit)) :
    othreadG_elem_auth_id Tgls ∗ othreadG_elem i
    ⊢ ⌜ i ∈ dom Tgls ⌝.
  Proof.
    rewrite /othreadG_elem_auth_id /othreadG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro. apply elem_of_dom_2 in H. by rewrite dom_fmap_L in H.
  Qed.

  (** Owns rules *)
  Lemma othreadG_owns_alloc_id D i :
    i ∉ D →
    othreadG_owns_token_id D
    ⊢ |==> othreadG_owns_token_id ({[i]} ∪ D) ∗
        othreadG_owns_auth_obls i ∅.
  Proof.
    rewrite /othreadG_owns_token_id /othreadG_owns_auth_obls.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (∅ : gmap oid unit)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma othreadG_owns_alloc i (TObls : gmap oid unit) k :
    TObls !! k = None →
    othreadG_owns_auth_obls i TObls
    ⊢ |==> othreadG_owns_auth_obls i (<[k:=()]>TObls) ∗
        othreadG_owns i k 1.
  Proof.
    rewrite /othreadG_owns_auth_obls /othreadG_owns.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ k (DfracOwn 1) ()); try done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]".
    iFrame "Ho". done.
  Qed.

  Lemma othreadG_owns_delete i (TObls : gmap oid unit) k :
    othreadG_owns_auth_obls i TObls ∗ othreadG_owns i k 1
    ⊢ |==> othreadG_owns_auth_obls i (delete k TObls).
  Proof.
    rewrite /othreadG_owns_auth_obls /othreadG_owns -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update. apply gmap_view_delete.
  Qed.

  Lemma othreadG_owns_lookup i TObls k q :
    othreadG_owns_auth_obls i TObls ∗ othreadG_owns i k q
    ⊢ ⌜ TObls !! k = Some tt ⌝.
  Proof.
    rewrite /othreadG_owns_auth_obls /othreadG_owns -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H.
    destruct H as (?&_&_&?&?&?).
    iPureIntro. by destruct x.
  Qed.

  Lemma othreadG_owns_valid i k q :
    othreadG_owns i k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_owns. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. done.
  Qed.

  (** Obls rules *)
  Lemma othreadG_obls_alloc Tgls i :
    Tgls !! i = None →
    othreadG_obls_auth_id Tgls
    ⊢ |==> othreadG_obls_auth_id (<[i:=∅]>Tgls) ∗
          othreadG_obls i ∅.
  Proof.
    rewrite /othreadG_obls_auth_id /othreadG_obls.
    iIntros (Hi) "H".
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracOwn 1) (∅ : oids)); try done.
      rewrite !lookup_fmap Hi. done. }
    iDestruct "H" as "[H Ho]". iFrame "Ho".
    rewrite !fmap_insert. done.
  Qed.

  Lemma othreadG_obls_lookup Tgls i G :
    othreadG_obls_auth_id Tgls ∗
    othreadG_obls i G
    ⊢ ⌜ (dom <$> Tgls) !! i = Some G ⌝.
  Proof.
    rewrite /othreadG_obls_auth_id /othreadG_obls -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H. destruct H as (_&_&?).
    iPureIntro. apply leibniz_equiv, lookup_fmap_Some in H. destruct H as (?&?&?).
    rewrite lookup_fmap H0. inv H. done.
  Qed.

  Lemma othreadG_obls_update Tgls i G M :
    othreadG_obls_auth_id Tgls ∗
    othreadG_obls i G
    ⊢ |==> othreadG_obls_auth_id (<[i:=M]>Tgls) ∗
        othreadG_obls i (dom M).
  Proof.
    rewrite /othreadG_obls_auth_id /othreadG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. apply gmap_view_replace. done.
  Qed.

  (** Exec rules *)
  Lemma othreadG_exec_done_false k q :
    othreadG_exec k q ∗ othreadG_done k ⊢ False.
  Proof.
    rewrite /othreadG_exec /othreadG_done. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma othreadG_exec_to_done k :
    othreadG_exec k 1 ⊢ |==> othreadG_done_auth k.
  Proof.
    rewrite /othreadG_exec /othreadG_done_auth.
    apply own_update.
    apply reservation_map_update. apply mono_nat_update. auto.
  Qed.
  Lemma othreadG_done_auth_done k :
    othreadG_done_auth k ⊢ othreadG_done k.
  Proof.
    rewrite /othreadG_done_auth /othreadG_done.
    apply own_mono.
    apply reservation_map_data_mono. apply mono_nat_included.
  Qed.

  Lemma othreadG_exec_valid k q :
    othreadG_exec k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_exec. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply mono_nat_auth_dfrac_valid in V. by apply dfrac_valid in V.
  Qed.

  Lemma othreadG_exec_alloc D k :
    k ∉ D →
    othreadG_exec_token_id D
    ⊢ |==> othreadG_exec_token_id ({[k]} ∪ D) ∗
        othreadG_exec k 1.
  Proof.
    rewrite /othreadG_exec_token_id /othreadG_exec.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN 0) with "Htk") as "[Htk >H]"; auto.
    { apply mono_nat_auth_valid. }
    by iFrame.
  Qed.

  (** Term rules *)
  (* Use ghost_map_elem rules. *)

  (** Fuel rules *)
  Lemma othreadG_fuel_eq k a0 a1 :
    a0 w= a1 →
    othreadG_fuel k a0 = othreadG_fuel k a1.
  Proof. intros EQ. rewrite /othreadG_fuel. by erewrite credit_eq. Qed.

  Lemma othreadG_fuel_mon k a0 a1 :
    a0 w≤ a1 →
    othreadG_fuel k a1 ⊢ |==> othreadG_fuel k a0.
  Proof.
    intros LE. rewrite /othreadG_fuel. apply own_update.
    by apply reservation_map_update, credit_update.
  Qed.

  Lemma othreadG_fuel_split k a0 a1 :
    othreadG_fuel k (a0 w+ a1) ⊣⊢ othreadG_fuel k a0 ∗ othreadG_fuel k a1.
  Proof.
    rewrite /othreadG_fuel. iSplit; [iIntros "H" | iIntros "[H1 H2]"].
    - iEval (rewrite credit_split) in "H". iDestruct "H" as "[H1 H2]". iFrame.
    - iEval (rewrite credit_split). iSplitL "H1"; iFrame.
  Qed.

  Lemma othreadG_fuel_mon_split k a0 a1 a2 :
    a0 w+ a1 w≤ a2 →
    othreadG_fuel k a2 ⊢ |==> othreadG_fuel k a0 ∗ othreadG_fuel k a1.
  Proof.
    intros LE. iIntros "H". iApply othreadG_fuel_split. iApply othreadG_fuel_mon; done.
  Qed.

  Lemma othreadG_fuel_lt k a0 a1 :
    a0 w< a1 →
    othreadG_fuel k a1 ⊢ |==> othreadG_fuel k a0 ∗ ∃ c, ⌜ wzero w< c ⌝ ∗ othreadG_fuel k c.
  Proof.
    intros LT. apply WFOCM.lt_exists_left in LT. destruct LT as (?& ?& ?).
    iIntros "H". iMod (othreadG_fuel_mon_split _ _ _ _ H0 with "H") as "[H1 H2]".
    iModIntro. iSplitL "H1"; iFrame. done.
  Qed.

  Lemma othreadG_bound_mon k a0 a1 :
    a0 w≤ a1 →
    othreadG_bound k a0 ⊢ |==> othreadG_bound k a1.
  Proof.
    intros LE. rewrite /othreadG_bound. apply own_update.
    by apply reservation_map_update, cmra_update_included, credit_bound_included.
  Qed.

  Lemma othreadG_fuel_spend_gen k a0 a1 :
    othreadG_bound k a0 ∗ othreadG_fuel k a1
    ⊢ |==> ∃ a2, ⌜(a1 w+ a2) w≤ a0⌝ ∗ othreadG_bound k a2.
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
  Lemma othreadG_fuel_spend k a0 a1 :
    wzero w< a1 →
    othreadG_bound k a0 ∗ othreadG_fuel k a1 ⊢ |==> ∃ a2, ⌜a2 w< a0⌝ ∗ othreadG_bound k a2.
  Proof.
    iIntros (LT) "[Ow Oc]". iMod (othreadG_fuel_spend_gen with "[$]") as "(%&%&$)".
    iPureIntro. eapply WFOCM.lt_exists_right; eauto.
  Qed.

  Lemma witG_compare k a0 a1 :
    othreadG_bound k a0 ∗ othreadG_fuel k a1 ⊢ ⌜ a1 w≤ a0 ⌝.
  Proof.
    rewrite -own_op -!reservation_map_data_op. iIntros "H".
    iPoseProof (own_valid with "H") as "%". apply reservation_map_data_valid in H.
    apply credit_bound_credit_valid_compare in H. done.
  Qed.

  Lemma othreadG_bound_id_alloc D k a :
    k ∉ D →
    othreadG_fuel_token_id (⊤ ∖ gset_to_coPset D)
    ⊢ |==> othreadG_fuel_token_id (⊤ ∖ gset_to_coPset ({[k]} ∪ D)) ∗
        othreadG_bound k a ∗ othreadG_fuel k a.
  Proof.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (credit_bound a ⋅ credit a) with "Htk") as "[Htk >H]"; auto.
    { apply credit_bound_credit_valid_eq. }
    iDestruct "H" as "[H1 H2]". rewrite /othreadG_bound /othreadG_fuel. by iFrame.
  Qed.

  (** Ceil rules *)
  (* Use ghost_map_elem rules. *)

  (** Frag rules *)
  Lemma othreadG_frag_alloc Tos i :
    Tos !! i = None →
    othreadG_frag_auth_id Tos
    ⊢ |==> othreadG_frag_auth_id (<[i:=∅]>Tos) ∗
          othreadG_frag i ∅ 1.
  Proof.
    rewrite /othreadG_frag_auth_id /othreadG_frag.
    iIntros (Hi) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracOwn 1) (GSet ∅ : gset_disj _)); try done.
      rewrite !lookup_fmap Hi. done.
    }
    iDestruct "H" as "[H Ho]". iFrame "Ho".
    rewrite !fmap_insert. done.
  Qed.

  Lemma othreadG_frag_lookup Tos i G :
    othreadG_frag_auth_id Tos ∗
    othreadG_frag i G 1
    ⊢ ⌜ (Tos) !! i = Some G ⌝.
  Proof.
    rewrite /othreadG_frag_auth_id /othreadG_frag -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H. destruct H as (_&_&?).
    iPureIntro. apply leibniz_equiv, lookup_fmap_Some in H. destruct H as (?&?&?). inv H. done.
  Qed.
  Lemma othreadG_frag_lookup_frac Tos i G q :
    othreadG_frag_auth_id Tos ∗
    othreadG_frag i G q
    ⊢ ∃ G', ⌜ (Tos) !! i = Some G' ∧ G ⊆ G' ⌝.
  Proof.
    rewrite /othreadG_frag_auth_id /othreadG_frag -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_dfrac_valid_discrete_total in H. destruct H as (?&_&_&?&?&?).
    iPureIntro. destruct x; last done. apply gset_disj_included in H1.
    eexists. split; last eauto.
    apply lookup_fmap_Some in H. destruct H as (?&?&?). inv H. done.
  Qed.

  Lemma othreadG_frag_update Tos i G M :
    othreadG_frag_auth_id Tos ∗
    othreadG_frag i G 1
    ⊢ |==> othreadG_frag_auth_id (<[i:=M]>Tos) ∗
        othreadG_frag i (M) 1.
  Proof.
    rewrite /othreadG_frag_auth_id /othreadG_frag -!own_op. apply own_update.
    rewrite !fmap_insert. apply gmap_view_replace. done.
  Qed.
  Lemma othreadG_frag_update_local Tos i q M1 M2 X1 X2 :
    (Tos !! i = Some M1) →
    (GSet (M1), GSet X1) ~l~> (GSet (M2), GSet X2) →
    othreadG_frag_auth_id Tos ∗
    othreadG_frag i X1 q
    ⊢ |==> othreadG_frag_auth_id (<[i:=M2]>Tos) ∗
        othreadG_frag i X2 q.
  Proof.
    intros Hlookup Hlu. rewrite /othreadG_frag_auth_id /othreadG_frag -!own_op. apply own_update.
    rewrite !fmap_insert. eapply gmap_view_update_local; eauto.
    rewrite !lookup_fmap Hlookup. done.
  Qed.

  Lemma othreadG_frag_valid i G q :
    othreadG_frag i G q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_frag. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. apply gmap_view_frag_valid in V. destruct V. done.
  Qed.
  Lemma othreadG_frag_valid_2 i G1 G2 q1 q2 :
    othreadG_frag i G1 q1 ∗ othreadG_frag i G2 q2 ⊢ ⌜ (q1 + q2 ≤ 1)%Qp ∧ G1 ## G2 ⌝.
  Proof.
    rewrite /othreadG_frag. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. apply gmap_view_frag_valid in V. destruct V. split; first done.
    apply gset_disj_valid_op in H0. done.
  Qed.

  Lemma othreadG_frag_op_1 i G1 G2 q1 q2 :
    othreadG_frag i G1 q1 ∗ othreadG_frag i G2 q2 ⊢ othreadG_frag i (G1 ∪ G2) (q1 + q2)%Qp.
  Proof.
    rewrite /othreadG_frag -own_op -gmap_view_frag_op dfrac_op_own.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_frag_valid in H. destruct H. apply gset_disj_valid_op in H0.
    rewrite gset_disj_union; done.
  Qed.
  Lemma othreadG_frag_op_2 i G1 G2 q1 q2 :
    G1 ## G2 →
    othreadG_frag i (G1 ∪ G2) (q1 + q2)%Qp ⊢ othreadG_frag i G1 q1 ∗ othreadG_frag i G2 q2.
  Proof.
    intros Hdj. rewrite /othreadG_frag -own_op -gmap_view_frag_op dfrac_op_own.
    rewrite gset_disj_union; done.
  Qed.

  TODO

  (** othread rules *)
  Lemma othread_elem i TP :
    othread TP ∗ othreadG_elem i ⊢ ⌜i ∈ TP⌝.
  Proof.
    rewrite /othread -!lock. iIntros "(O & He)".
    iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_elem_elem with "[$]") as "%".
    by rewrite -Hdom.
  Qed.

  Lemma othread_alloc_thread i TP :
    i ∉ TP →
    othread TP
    ⊢ |==> othread ({[i]} ∪ TP) ∗
        othreadG_elem i ∗ othreadG_obls i ∅ 1 ∗ othreadG_exec i (1/2 + 1/2/2)%Qp.
  Proof.
    iIntros (Hi) "O".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    assert (Hlu : Tgls !! i = None).
    { apply not_elem_of_dom. rewrite Hdom. auto. }
    iMod (othreadG_elem_alloc _ i ∅ with "HE") as "[HE He]"; first auto.
    iMod (othreadG_owns_alloc_id with "HO") as "[HO Ho]"; first done.
    iMod (othreadG_obls_alloc _ i with "HB") as "[HB Hb]"; first auto.
    iMod (othreadG_exec_alloc _ i with "HX") as "[HX Hx]"; first auto.
    iDestruct "Hx" as "[Hx [Hx' Hx0]]". iCombine "Hx Hx'" as "Hx".
    iModIntro. iFrame "He Hb Hx". iExists (<[i:=∅]>Tgls). iFrame "HE HO HB HX".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom. done. }
    iApply big_sepM_insert; first done.
    iFrame. done.
  Qed.

  Lemma othread_alloc_threads Θ TP :
    Θ ## TP →
    othread TP
    ⊢ |==> othread (TP ∪ Θ) ∗
        ([∗ set] i ∈ Θ, othreadG_elem i ∗ othreadG_obls i ∅ 1 ∗ othreadG_exec i (1/2 + 1/2/2)%Qp).
  Proof.
    revert TP. pattern Θ. revert Θ. apply set_ind.
    { solve_proper. }
    { iIntros (??) "T". rewrite union_empty_r_L. iFrame. by iModIntro. }
    iIntros (i Θ Nin IH TP Disj) "O".
    iMod (IH with "O") as "(O& Hs)"; first set_solver.
    iMod (othread_alloc_thread i with "O") as "(O& Hi)"; first set_solver.
    iModIntro. replace ({[i]} ∪ (TP ∪ Θ)) with (TP ∪ ({[i]} ∪ Θ)) by set_solver.
    iFrame. iApply big_sepS_union; first set_solver. rewrite big_sepS_singleton. iFrame.
  Qed.

  Local Lemma othread_alloc_obl_1 j TP i G q k :
    oblG_owner k j (1/2 + 1/2/2/2 + 1/2/2 + 1/2/2/2/2)%Qp ∗
    othread TP ∗ othreadG_obls i G q ∗ oblG_owner k i (1/2/2/2/2)%Qp
    ⊢ |==> ⌜k ∉ G⌝ ∗ oblG_owner k j (1/2 + 1/2/2/2 + 1/2/2 + 1/2/2/2/2)%Qp ∗
        othread TP ∗ othreadG_obls i ({[k]} ∪ G) q ∗ othreadG_owns i k 1.
  Proof.
    iIntros "(Go0& O& Obs& Go)".
    iPoseProof (oblG_owner_agree with "[$Go0 $Go]") as "(%EQ& %F)". subst j. clear F.
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup_frac with "[$HB $Obs]") as "%".
    destruct H as (G0& Hlui0& Hsub).
    assert (Hlui : ∃ m, dom m = G0 ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. eauto. }
    destruct Hlui as (TObls& Hm& Hlui).
    iAssert (⌜ TObls !! k = None ⌝)%I with "[Go0 Go Hm]" as "%Hluk".
    { destruct (TObls !! k) eqn:LU; last done. iExFalso.
      iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi _]".
      iDestruct "Hi" as "(Hix & His & Him)".
      iDestruct (big_sepM_delete _ _ k _ LU with "Him") as "[Hk Him]".
      iDestruct "Hk" as "Go1".
      iDestruct "Go0" as "(((Go0& Go2)& Go3)& Go4)".
      iCombine "Go1 Go" as "Go". iCombine "Go2 Go" as "Go". iCombine "Go3 Go" as "Go".
      iCombine "Go0 Go" as "Go". iCombine "Go Go4" as "Go".
      iPoseProof (oblG_owner_valid with "Go") as "%". done.
    }
    iFrame "Go0".
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iMod (othreadG_owns_alloc _ _ _ Hluk with "His") as "[His Hw]".
    iFrame "Hw".
    iMod (othreadG_obls_update_local _ _ _ TObls (<[k:=tt]>TObls) _ ({[k]} ∪ G) with "[$HB $Obs]") as "[HB Obs]";
      [eauto | | ].
    { rewrite dom_insert_L. apply gset_disj_alloc_local_update. apply not_elem_of_dom in Hluk. set_solver. }
    iFrame "Obs". iModIntro. iSplitR.
    { iPureIntro. apply not_elem_of_dom in Hluk. rewrite Hm in Hluk. set_solver. }
    iExists (<[i:=(<[k:=tt]>TObls)]>Tgls). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HB HX HO". iSplitL "HE".
    { rewrite /othreadG_elem_auth_id. rewrite !fmap_insert insert_id; first done.
      rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq Tgls i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame "Hm Hix His". iApply (big_sepM_insert _ _ k); first done. iFrame.
  Qed.
  Lemma othread_alloc_obl Ω TP i G q k :
    osat Ω ∗ othread TP ∗
    othreadG_obls i G q ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp
    ⊢ |==> osat Ω ∗ othread TP ∗
        ⌜k ∉ G⌝ ∗ othreadG_obls i ({[k]} ∪ G) q ∗
        othreadG_owns i k 1 ∗ oblG_owner k i (1/2 + 1/2/2/2 + 1/2/2/2/2)%Qp.
  Proof.
    iIntros "(S& O& Obs& #Ge& Go)".
    iDestruct "Go" as "(Go& (Go1& Go2))". iDestruct "Go2" as "(Go2& Go3)".
    iPoseProof (osat_open_owner with "[$S $Ge $Go]") as "(Go& (%& Gl'& Go')& ACC)".
    iCombine "Go Go1 Go' Go2" as "Go". rewrite !Qp.add_assoc.
    iMod (othread_alloc_obl_1 with "[$Go $O $Obs $Go3]") as "(%Nin& Go& O& Obs& Oo)".
    iDestruct "Go" as "((Go& Go')& Go0)". iPoseProof ("ACC" with "[$Gl' $Go']") as "S".
    iCombine "Go Go0" as "Go". iFrame. done.
  Qed.

  Lemma othread_obls_owns_elem TP i G k q :
    othread TP ∗ othreadG_obls i G 1 ∗ othreadG_owns i k q
    ⊢ ⌜ k ∈ G ⌝.
  Proof.
    iIntros "(O& Ho& Hw)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup with "[$HB $Ho]") as "%".
    assert (Hlui : ∃ m, dom m = G ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in H. eauto. }
    destruct Hlui as (TObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[$His $Hw]") as "%Hluk".
    iPureIntro. rewrite -Hm. by apply elem_of_dom.
  Qed.

  Lemma othread_delete_obl_frac TP i G q k :
    k ∈ G →
    othread TP ∗ othreadG_obls i G q ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ othreadG_obls i (G ∖ {[k]}) q ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros (Hink) "(O& Ho& Hw)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup_frac with "[$HB $Ho]") as "%".
    destruct H as (G0&Hlui0&Hsub).
    assert (Hlui : ∃ m, dom m = G0 ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. eauto. }
    destruct Hlui as (TObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[$His $Hw]") as "%Hluk".
    iMod (othreadG_owns_delete with "[$His $Hw]") as "His".
    iMod (othreadG_obls_update_local _ _ _ TObls (delete k TObls) _ (G ∖ {[k]}) with "[$HB $Ho]") as "[HB Ho]";
      [eauto | | ].
    { replace (GSet (dom TObls)) with (GSet ({[k]}) ⋅ GSet (dom (delete k TObls))).
      2:{ rewrite dom_delete_L gset_disj_union.
          - f_equal. apply elem_of_dom_2 in Hluk. rewrite -union_difference_L; set_solver.
          - set_solver.
      }
      replace (GSet G) with (GSet {[k]} ⋅ GSet (G ∖ {[k]})).
      2:{ rewrite gset_disj_union; last set_solver. f_equal. rewrite -union_difference_L; auto. set_solver. }
      apply gset_disj_dealloc_op_local_update.
    }
    iFrame "Ho".
    iDestruct (big_sepM_delete _ _ k _ Hluk with "Him") as "[Hik Him]".
    iDestruct "Hik" as "$".
    iModIntro. iExists (<[i:=(delete k TObls)]>Tgls). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HO HX HB". iSplitL "HE".
    { rewrite /othreadG_elem_auth_id. rewrite !fmap_insert. rewrite insert_id; first done.
      rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq Tgls i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame.
  Qed.
  Lemma othread_delete_obl TP i G k :
    othread TP ∗ othreadG_obls i G 1 ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ othreadG_obls i (G ∖ {[k]}) 1 ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof using Type*.
    iIntros "(O & Ho & Hw)". iPoseProof (othread_obls_owns_elem with "[$]") as "%Hkin".
    iApply (othread_delete_obl_frac with "[$]"). auto.
  Qed.

  Lemma othread_exec_to_done TP i :
    othread TP ∗ othreadG_exec i (1/2 + 1/2/2)%Qp ∗ othreadG_obls i ∅ 1
    ⊢ |==> othread TP ∗ othreadG_done i.
  Proof.
    iIntros "(O& Hx& Ho)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup with "[$HB $Ho]") as "%".
    assert (Hlui : Tgls !! i = Some ∅).
    { rewrite lookup_fmap_Some in H. destruct H as (?&?&?). apply dom_empty_inv_L in H. by subst. }
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix _]] & His & Him)"; last first.
    { iExFalso. iPoseProof (othreadG_done_auth_done with "[$]") as "Hxt".
      iPoseProof (othreadG_exec_done_false with "[$]") as "%F". done. }
    iMod (othreadG_exec_to_done with "[Hx Hix]") as "Hx".
    { iCombine "Hx Hix" as "Hx". rewrite -Qp.add_assoc !Qp.div_2. done. }
    iPoseProof (othreadG_done_auth_done with "Hx") as "#Hxt".
    iModIntro. iSplitL; last done.
    iExists Tgls. iSplitR; first done. iFrame "HO HB HX HE".
    iApply (big_sepM_delete _ _ i _ Hlui). iFrame. iRight. iFrame.
  Qed.

  Lemma othread_done_open TP i :
    othread TP ∗ othreadG_elem i ∗ othreadG_done i
    ⊢ othreadG_obls i ∅ 1 ∗ (othreadG_obls i ∅ 1 -∗ othread TP).
  Proof.
    iIntros "(O & #He & #Hx)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_elem_elem with "[$]") as "%Hini".
    assert (Hlui : ∃ m, Tgls !! i = Some m).
    { rewrite elem_of_dom in Hini. eauto. }
    destruct Hlui as (TObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix Ho]] & His & Him)".
    { iExFalso. iPoseProof (othreadG_exec_done_false with "[$]") as "%F". done. }
    iFrame "Ho". iIntros "Ho".
    iExists Tgls. iSplitR; first done. iFrame "HO HB HX HE".
    iApply (big_sepM_delete _ _ i _ Hlui). iFrame. iRight. iFrame.
  Qed.

  Lemma othread_owns_open TP i k q :
    othread TP ∗ othreadG_elem i ∗ othreadG_owns i k q
    ⊢ othreadG_owns i k q ∗
    (oblG_owner k i (1/2/2/2/2)%Qp) ∗
    ((oblG_owner k i (1/2/2/2/2)%Qp) -∗ othread TP).
  Proof.
    iIntros "(O & #He & Hw)".
    iPoseProof (othread_elem with "[$O $He]") as "%Hin".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    assert (Hlui : is_Some (Tgls !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (TObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[$His $Hw]") as "%Hluk".
    iPoseProof (big_sepM_delete _ _ _ _ Hluk with "Him") as "[Hk Him]".
    iFrame "Hw Hk". iIntros "Hk". iExists Tgls. iFrame "HO HB HX HE".
    iSplit; first done. iApply (big_sepM_delete _ _ _ _ Hlui). iFrame.
    iApply (big_sepM_delete _ _ _ _ Hluk). iFrame.
  Qed.

  Lemma othread_obls_open TP i k G q :
    k ∈ G →
    othread TP ∗ othreadG_elem i ∗ othreadG_obls i G q
    ⊢ othreadG_obls i G q ∗
    (oblG_owner k i (1/2/2/2/2)%Qp) ∗
    ((oblG_owner k i (1/2/2/2/2)%Qp) -∗ othread TP).
  Proof.
    iIntros (Ink) "(O& #He& Hobls)". 
    iPoseProof (othread_elem with "[$O $He]") as "%Hin".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    assert (Hlui : is_Some (Tgls !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (TObls&Hlui).
    iPoseProof (othreadG_obls_lookup_frac with "[$HB $Hobls]") as "(%& %& %)".
    rewrite lookup_fmap in H. rewrite Hlui in H. inv H.
    assert (Hluk : is_Some (TObls !! k)).
    { apply elem_of_dom. set_solver. }
    destruct Hluk as (fk&Hluk).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (big_sepM_delete _ _ _ _ Hluk with "Him") as "[Hk Him]".
    iFrame "Hk Hobls". iIntros "Bl".
    iExists Tgls. iFrame. iSplitR; first done.
    iApply (big_sepM_delete _ _ _ _ Hlui). iFrame.
    iApply (big_sepM_delete _ _ _ _ Hluk). iFrame.
  Qed.

  (** oassigned rules *)
  Lemma oassigned_add_obl Gls k :
    oassigned Gls ∗
    (oblG_elem k ∗ ((∃ i, oblG_owner k i (1/2/2/2/2) ∗ othreadG_owns i k (1/2/2) ∗ othreadG_elem i) ∨ oblG_fulfilled k))
    ⊢ oassigned ({[k]} ∪ Gls).
  Proof.
    iIntros "(A& H)". rewrite /oassigned -!lock. destruct (decide (k ∈ Gls)).
    - iPoseProof (big_sepS_delete _ _ _ e with "A") as "[_ A]".
      replace ({[k]} ∪ Gls) with ({[k]} ∪ (Gls ∖ {[k]})).
      2:{ rewrite -union_difference_L; set_solver. }
      iApply big_sepS_insert.
      { set_solver. }
      iFrame.
    - iApply big_sepS_insert; first auto. iFrame.
  Qed.

  Lemma oassigned_delete_obl Gls k :
    k ∈ Gls →
    oassigned Gls
    ⊢ oassigned (Gls ∖ {[k]}) ∗
    (oblG_elem k ∗ ((∃ i, oblG_owner k i (1/2/2/2/2) ∗ othreadG_owns i k (1/2/2) ∗ othreadG_elem i) ∨ oblG_fulfilled k)).
  Proof.
    rewrite /oassigned -!lock. iIntros (INk) "A".
    iPoseProof (big_sepS_delete with "A") as "[$ $]". auto.
  Qed.

  Lemma othread_assigned_obls_lookup Ω TP k a i G :
    Ω !! k = Some (obl_assigned a i) →
    osat Ω ∗ othread TP ∗ oassigned (dom Ω) ∗ othreadG_obls i G 1
    ⊢ ⌜ k ∈ G ⌝.
  Proof.
    rewrite /oassigned -lock. iIntros (LUOk) "(S& O& A& Tbs)".
    iPoseProof (big_sepS_delete _ _ k with "A") as "[A _]".
    { apply elem_of_dom_2 in LUOk. auto. }
    iDestruct "A" as "(#Gek& [(%& Gok& Ook& #Tei) | #Guk])".
    - iPoseProof (osat_lookup_owner with "[$S $Gek $Gok]") as "(%&%)".
      rewrite LUOk in H. inv H. iApply (othread_obls_owns_elem with "[$O $Tbs $Ook]").
    - iPoseProof (osat_lookup_fulfilled with "[$S $Gek $Guk]") as "%H".
      rewrite LUOk in H. inv H.
  Qed.

  Lemma othread_obls_lookup Ω TP k i G q :
    k ∈ G →
    osat Ω ∗ othread TP ∗ othreadG_elem i ∗ othreadG_obls i G q ∗ oblG_elem k
    ⊢ ∃ a, ⌜ Ω !! k = Some (obl_assigned a i) ⌝.
  Proof.
    iIntros (Ink) "(S& O& #Oei& Tbs& #Gek)".
    iPoseProof (othread_obls_open with "[$O $Oei $Tbs]") as "(Tbs& Go& Acc)". 1: eauto.
    iPoseProof (osat_lookup_owner with "[$S $Gek $Go]") as "(%& %)". eauto.
  Qed.

  Lemma othread_assigned_thread_elem Ω TP k a i :
    Ω !! k = Some (obl_assigned a i) →
    osat Ω ∗ othread TP ∗ oassigned (dom Ω)
    ⊢ ⌜i ∈ TP⌝.
  Proof.
    rewrite /oassigned -lock. iIntros (LUOk) "(S& O& A)".
    iPoseProof (big_sepS_delete _ _ k with "A") as "[A _]".
    { apply elem_of_dom_2 in LUOk. auto. }
    iDestruct "A" as "(#Gek& [(%& Gok& Ook& #Tei) | #Guk])".
    - iPoseProof (osat_lookup_owner with "[$S $Gek $Gok]") as "%". destruct H. rewrite LUOk in H. inv H.
      iPoseProof (othread_elem with "[$O $Tei]") as "%".  auto.
    - iPoseProof (osat_lookup_fulfilled with "[$S $Gek $Guk]") as "%". rewrite LUOk in H. inv H.
  Qed.

  Lemma othread_assigned_done_false Ω TP k a i :
    Ω !! k = Some (obl_assigned a i) →
    osat Ω ∗ othread TP ∗ oassigned (dom Ω) ∗ othreadG_elem i ∗ othreadG_done i ⊢ False.
  Proof.
    iIntros (LUk) "(S& O& A& #He & #Hx)".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_elem_elem with "[$HE $He]") as "%Hini".
    assert (Hlui : ∃ m, Tgls !! i = Some m).
    { rewrite elem_of_dom in Hini. eauto. }
    destruct Hlui as (TObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix Ho]] & His & Him)".
    { iExFalso. iPoseProof (othreadG_exec_done_false with "[$Hix $Hx]") as "%F". done. }
    iPoseProof (othreadG_obls_lookup with "[$HB $Ho]") as "%LUempty".
    rewrite /oassigned -lock. iPoseProof (big_sepS_delete _ _ k with "A") as "[A _]".
    { apply elem_of_dom_2 in LUk. auto. }
    iDestruct "A" as "(#Gek& [(%& Gok& Ook& #Tei) | #Guk])".
    - iPoseProof (osat_lookup_owner with "[$S $Gek $Gok]") as "(%&%)". rewrite LUk in H. inv H.
      iPoseProof (othreadG_owns_lookup with "[$His $Ook]") as "%".
      rewrite lookup_fmap_Some in LUempty. destruct LUempty as (?&?&?). apply dom_empty_inv_L in H0. subst x.
      rewrite Hlui in H1. inv H1.
    - iPoseProof (osat_lookup_fulfilled with "[$S $Gek $Guk]") as "%H".
      rewrite LUk in H. inv H.
  Qed.

End othread.

(* Allocation of initial invariant. *)
Lemma othread_alloc `{SI : indexT} {Σ}
  `{!@osatGS.osatGS _ Σ} `{!othreadGpreS Σ} :
  ⊢ |==> ∃ _ : othreadGS Σ, othread ∅ ∗ oassigned ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR oid (unitUR))) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive (gset_disjUR _))) as (γO) "HO";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γX) "HX";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive unitUR)) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (OthreadG SI _ _ γS γO γX γE).
  rewrite /othread /oassigned -!lock. iSplitL; last done.
  iExists ∅. iSplitR; first done.
  replace (⊤ : coPset) with (⊤ ∖ gset_to_coPset ∅); [iFrame; done|].
  set_solver.
Qed.
