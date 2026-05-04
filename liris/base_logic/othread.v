From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import ghost_map.
From liris.algebra Require Export wfocm.
From liris.algebra Require Import map_of_sets bcred ordinal_ucmra.
From liris.base_logic Require Export osat.

Definition proxy := positive.
Definition session := positive.

(** The ghost state for thread obls *)
Module othreadGS.

  (* Assumes thread ids are positive *)
  Class othreadGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadGpreS {
        othreadGpreS_owns : inG Σ (reservation_mapUR (gmap_viewR oid (unitUR)));
        othreadGpreS_obls : inG Σ (gmap_viewR positive (gsetUR oid));
        othreadGpreS_exec : inG Σ (reservation_mapUR mono_natUR);
        othreadGpreS_elem : inG Σ (gmap_viewR positive unitUR);
        othreadGpreS_fuel : inG Σ (reservation_mapUR (bcredUR));
        othreadGpreS_prox : inG Σ (reservation_mapUR (gmap_viewR proxy (gsetUR oid)));
        othreadGpreS_sess : inG Σ (reservation_mapUR (gmap_viewR proxy (agreeR session)));
      }.

  Class othreadGS `{SI : indexT} (Σ : gFunctors) : Set :=
    OthreadG {
        othread_inG : othreadGpreS Σ;
        owns_name : gname;
        obls_name : gname;
        exec_name : gname;
        elem_name : gname;
        fuel_name : gname;
        prox_name : gname;
        sess_name : gname;
      }.

  Definition othreadΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR oid (unitUR)));
      GFunctor (gmap_viewR positive (gsetUR oid));
      GFunctor (reservation_mapUR mono_natUR);
      GFunctor (gmap_viewR positive unitUR);
      GFunctor (reservation_mapUR bcredUR);
      GFunctor (reservation_mapUR (gmap_viewR proxy (gsetUR oid)));
      GFunctor (reservation_mapUR (gmap_viewR proxy (agreeR session)))
      ].

  Global Instance subG_othreadΣ `{SI : indexT} {Σ} : subG (othreadΣ) Σ → (othreadGpreS Σ).
  Proof. solve_inG. Qed.

End othreadGS.
Import othreadGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances othread_inG
  othreadGpreS_owns othreadGpreS_obls othreadGpreS_exec othreadGpreS_elem
  othreadGpreS_fuel othreadGpreS_prox othreadGpreS_sess.

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

(* Fuel: manage fuels for the thread's obligations *)
Definition othreadG_bound `{SI : indexT} `{!othreadGS Σ}
  (s : session) (β : obl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bcredUR) s (credit_bound β)).
Global Typeclasses Opaque othreadG_bound.
Global Instance: Params (@othreadG_bound) 3 := {}.

Definition othreadG_fuel `{SI : indexT} `{!othreadGS Σ}
  (s : session) (a : obl_fuel) : iProp Σ :=
  own fuel_name (reservation_map_data (A:=bcredUR) s (credit a)).
Global Typeclasses Opaque othreadG_fuel.
Global Instance: Params (@othreadG_fuel) 3 := {}.

Local Definition othreadG_fuel_token_id `{SI : indexT} `{!othreadGS Σ}
  (E : coPset) : iProp Σ :=
  own fuel_name (reservation_map_token (A:=bcredUR) E).

(* Prox: tracks proxies of a thread's obligations *)
Definition othreadG_proxy_obls `{SI : indexT} `{!othreadGS Σ} (i : positive) (π : proxy) (G : oids) : iProp Σ :=
  own prox_name (reservation_map_data (A:=(gmap_viewR proxy (gsetUR oid)))
                   i (gmap_view_frag π (DfracOwn 1) G)).
Global Typeclasses Opaque othreadG_proxy_obls.
Global Instance: Params (@othreadG_proxy_obls) 3 := {}.

Local Definition othreadG_proxy_obls_token `{SI : indexT} `{!othreadGS Σ} TP : iProp Σ :=
  (own prox_name (reservation_map_token (A:=gmap_viewR proxy (gsetUR oid)) (⊤ ∖ gset_to_coPset TP))).

Local Definition othreadG_proxy_obls_auth `{SI : indexT} `{!othreadGS Σ}
  i (POs : gmap proxy oids) : iProp Σ :=
  (own prox_name (reservation_map_data (A:=(gmap_viewR proxy (gsetUR oid)))
                    i (gmap_view_auth (DfracOwn 1) (POs)))).

(* Sess: tracks current proxies' sessions of the thread *)
Definition othreadG_proxy_session `{SI : indexT} `{!othreadGS Σ} (i : positive) (π : proxy) (s : session) (q : Qp) : iProp Σ :=
  own sess_name (reservation_map_data (A:=(gmap_viewR proxy (agreeR session)))
                   i (gmap_view_frag π (DfracOwn q) (to_agree s))).
Global Typeclasses Opaque othreadG_proxy_session.
Global Instance: Params (@othreadG_proxy_session) 3 := {}.

Definition othreadG_proxy_session_auth `{SI : indexT} `{!othreadGS Σ} (i : positive) (ss : gmap proxy session) (q : Qp) : iProp Σ :=
  own sess_name (reservation_map_data (A:=(gmap_viewR proxy (agreeR session)))
                   i (gmap_view_auth (DfracOwn q) (to_agree <$> ss))).
Global Typeclasses Opaque othreadG_proxy_session_auth.
Global Instance: Params (@othreadG_proxy_session_auth) 3 := {}.

Local Definition othreadG_proxy_session_token `{SI : indexT} `{!othreadGS Σ} TP : iProp Σ :=
  (own sess_name (reservation_map_token (A:=gmap_viewR proxy (agreeR session)) (⊤ ∖ gset_to_coPset TP))).

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

(* Global invariant for threads' obligation fragments and sessions. *)
Definition oproxy `{SI : indexT} {Σ} `{!@osatGS.osatGS _ Σ} `{!othreadGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (Df : gset session),
        othreadG_fuel_token_id (⊤ ∖ (gset_to_coPset Df)) ∗
        othreadG_proxy_session_token TP ∗
        othreadG_proxy_obls_token TP ∗
        ([∗ set] i ∈ TP,
           ∃ (Ks : gmap proxy (oids)) (Ss : gmap proxy (session)),
             ⌜ dom Ks = dom Ss ⌝ ∗
             othreadG_proxy_obls_auth i Ks ∗
             othreadG_proxy_session_auth i Ss (1/2)%Qp ∗
             ((∃ G, othreadG_exec i (1/2/2)%Qp ∗ othreadG_obls i G ∗
                    ⌜ G = union_sets Ks ∧ disjoint_sets Ks ⌝) ∨
                (othreadG_done i ∗ othreadG_proxy_session_auth i Ss (1/2)%Qp ∗ ⌜ Ks = ∅ ∧ Ss = ∅ ⌝)) ∗
             ([∗ map] K;s ∈ Ks;Ss,
                ∃ β, othreadG_bound s β ∗
                     ([∗ set] k ∈ K, ∃ a, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)))
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

  (* Fuel *)
  Global Instance othreadG_bound_persistent e β : Persistent (othreadG_bound e β).
  Proof. rewrite /othreadG_bound. apply _. Qed.
  Global Instance othreadG_bound_timeless e β : Timeless (othreadG_bound e β).
  Proof. rewrite /othreadG_bound. apply _. Qed.

  Global Instance othreadG_fuel_timeless e a : Timeless (othreadG_fuel e a).
  Proof. rewrite /othreadG_fuel. apply _. Qed.

  Local Instance othreadG_fuel_token_id_timeless E : Timeless (othreadG_fuel_token_id E).
  Proof. rewrite /othreadG_fuel_token_id. apply _. Qed.

  (* Proxy *)
  Global Instance othreadG_proxy_obls_timeless i π G : Timeless (othreadG_proxy_obls i π G).
  Proof. rewrite /othreadG_proxy_obls. apply _. Qed.

  Local Instance othreadG_proxy_obls_token_timeless TP : Timeless (othreadG_proxy_obls_token TP).
  Proof. rewrite /othreadG_proxy_obls_token. apply _. Qed.

  Local Instance othreadG_proxy_obls_auth_timeless i POs : Timeless (othreadG_proxy_obls_auth i POs).
  Proof. rewrite /othreadG_proxy_obls_auth. apply _. Qed.

  (* Session *)
  Global Instance othreadG_proxy_session_timeless i π s q : Timeless (othreadG_proxy_session i π s q).
  Proof. rewrite /othreadG_proxy_session. apply _. Qed.

  Global Instance othreadG_proxy_session_fractional i π s :
    Fractional (othreadG_proxy_session i π s).
  Proof.
    rewrite /othreadG_proxy_session. intros p q.
    by rewrite -own_op -!reservation_map_data_op -gmap_view_frag_op agree_idemp.
  Qed.
  Global Instance othreadG_proxy_session_as_fractional i π s q :
    AsFractional (othreadG_proxy_session i π s q) (othreadG_proxy_session i π s) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance othreadG_proxy_session_auth_timeless i Ss q : Timeless (othreadG_proxy_session_auth i Ss q).
  Proof. rewrite /othreadG_proxy_session_auth. apply _. Qed.

  Global Instance othreadG_proxy_session_auth_fractional i Ss :
    Fractional (othreadG_proxy_session_auth i Ss).
  Proof.
    rewrite /othreadG_proxy_session_auth. intros p q.
    by rewrite -own_op -!reservation_map_data_op -gmap_view_auth_dfrac_op.
  Qed.
  Global Instance othreadG_proxy_session_auth_as_fractional i Ss q :
    AsFractional (othreadG_proxy_session_auth i Ss q) (othreadG_proxy_session_auth i Ss) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance othreadG_proxy_session_token_timeless TP : Timeless (othreadG_proxy_session_token TP).
  Proof. rewrite /othreadG_proxy_session_token. apply _. Qed.

  (* Invs *)
  Global Instance othread_timeless TP : Timeless (othread TP).
  Proof. rewrite /othread -lock. apply _. Qed.

  Global Instance oassigned_timeless Gls : Timeless (oassigned Gls).
  Proof. rewrite /oassigned -lock. apply _. Qed.

  Global Instance oproxy_timeless TP : Timeless (oproxy TP).
  Proof. rewrite /oproxy -lock. apply _. Qed.

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

  Lemma othreadG_bound_fuel_compare k a0 a1 :
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

  Lemma othreadG_bound_op k a0 a1 :
    othreadG_bound k a0 ∗ othreadG_bound k a1 ⊢ ∃ a2, othreadG_bound k a2 ∧ ⌜ a2 w≤ a0 ∧ a2 w≤ a1 ⌝.
  Proof.
    rewrite -own_op -!reservation_map_data_op. destruct (credit_bound_op a0 a1) as (?&?&?&?).
    rewrite H. rewrite /othreadG_bound. iIntros "$". iPureIntro. split; auto.
  Qed.

  (** Proxy rules *)
  Lemma othreadG_proxy_obls_alloc_auth D i :
    i ∉ D →
    othreadG_proxy_obls_token D
    ⊢ |==> othreadG_proxy_obls_token ({[i]} ∪ D) ∗
        othreadG_proxy_obls_auth i ∅.
  Proof.
    rewrite /othreadG_proxy_obls_token /othreadG_proxy_obls_auth.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (∅ : gmap proxy oids)) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma othreadG_proxy_obls_alloc i (POs : gmap proxy oids) π :
    POs !! π = None →
    othreadG_proxy_obls_auth i POs
    ⊢ |==> othreadG_proxy_obls_auth i (<[π:=∅]>POs) ∗
        othreadG_proxy_obls i π ∅.
  Proof.
    rewrite /othreadG_proxy_obls_auth /othreadG_proxy_obls.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ π (DfracOwn 1) ∅); done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]". iFrame "Ho". done.
  Qed.

  Lemma othreadG_proxy_obls_delete i (POs : gmap proxy oids) π G :
    othreadG_proxy_obls_auth i POs ∗ othreadG_proxy_obls i π G
    ⊢ |==> othreadG_proxy_obls_auth i (delete π POs).
  Proof.
    rewrite /othreadG_proxy_obls_auth /othreadG_proxy_obls -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update. apply gmap_view_delete.
  Qed.

  Lemma othreadG_proxy_obls_update i POs π G1 G2 :
    othreadG_proxy_obls_auth i POs ∗
    othreadG_proxy_obls i π G1
    ⊢ |==> othreadG_proxy_obls_auth i (<[π:=G2]>POs) ∗
        othreadG_proxy_obls i π G2.
  Proof.
    rewrite /othreadG_proxy_obls_auth /othreadG_proxy_obls -!own_op -!reservation_map_data_op.
    apply own_update, reservation_map_update, gmap_view_replace. done.
  Qed.

  Lemma othreadG_proxy_obls_lookup i POs π G :
    othreadG_proxy_obls_auth i POs ∗ othreadG_proxy_obls i π G
    ⊢ ⌜ POs !! π = Some G ⌝.
  Proof.
    rewrite /othreadG_proxy_obls_auth /othreadG_proxy_obls -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_valid in H.
    destruct H as (?&?&?). iPureIntro. apply leibniz_equiv in H1. auto.
  Qed.

  Lemma othreadG_proxy_obls_valid i π1 π2 K1 K2 :
    othreadG_proxy_obls i π1 K1 ∗ othreadG_proxy_obls i π2 K2
    ⊢ ⌜ π1 ≠ π2 ⌝.
  Proof.
    rewrite /othreadG_proxy_obls -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    destruct (decide (π1 = π2)); auto. subst.
    apply reservation_map_data_valid, gmap_view_frag_op_valid in H. destruct H. done.
  Qed.

  (** Session rules *)
  Lemma othreadG_proxy_session_alloc_auth D i :
    i ∉ D →
    othreadG_proxy_session_token D
    ⊢ |==> othreadG_proxy_session_token ({[i]} ∪ D) ∗
        othreadG_proxy_session_auth i ∅ 1.
  Proof.
    rewrite /othreadG_proxy_session_token /othreadG_proxy_session_auth.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap proxy session))) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma othreadG_proxy_session_alloc i (Ss : gmap proxy session) π s :
    Ss !! π = None →
    othreadG_proxy_session_auth i Ss 1
    ⊢ |==> othreadG_proxy_session_auth i (<[π:=s]>Ss) 1 ∗
        othreadG_proxy_session i π s 1.
  Proof.
    rewrite /othreadG_proxy_session_auth /othreadG_proxy_session.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ π (DfracOwn 1) (to_agree s)); try done.
      rewrite lookup_fmap Hk. done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]". iFrame "Ho".
    rewrite fmap_insert. done.
  Qed.

  Lemma othreadG_proxy_session_delete i (Ss : gmap proxy session) π s :
    othreadG_proxy_session_auth i Ss 1 ∗ othreadG_proxy_session i π s 1
    ⊢ |==> othreadG_proxy_session_auth i (delete π Ss) 1.
  Proof.
    rewrite /othreadG_proxy_session_auth /othreadG_proxy_session -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update. rewrite fmap_delete. apply gmap_view_delete.
  Qed.

  Lemma othreadG_proxy_session_update i Ss π s1 s2 :
    othreadG_proxy_session_auth i Ss 1 ∗
    othreadG_proxy_session i π s1 1
    ⊢ |==> othreadG_proxy_session_auth i (<[π:=s2]>Ss) 1 ∗
        othreadG_proxy_session i π s2 1.
  Proof.
    rewrite /othreadG_proxy_session_auth /othreadG_proxy_session -!own_op -!reservation_map_data_op.
    apply own_update, reservation_map_update. rewrite fmap_insert. apply gmap_view_replace. done.
  Qed.

  Lemma othreadG_proxy_session_lookup i Ss π s q1 q2 :
    othreadG_proxy_session_auth i Ss q1 ∗ othreadG_proxy_session i π s q2
    ⊢ ⌜ Ss !! π = Some s ⌝.
  Proof.
    rewrite /othreadG_proxy_session_auth /othreadG_proxy_session -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H.
    destruct H as (?&_&_&?&?&?). iPureIntro.
    apply lookup_fmap_Some in H. destruct H as (?&?&?). subst x.
    apply to_agree_included, leibniz_equiv in H1. subst. auto.
  Qed.

  Lemma othreadG_proxy_session_auth_valid i Ss1 Ss2 q1 q2 :
    othreadG_proxy_session_auth i Ss1 q1 ∗ othreadG_proxy_session_auth i Ss2 q2
    ⊢ ⌜ Ss1 = Ss2 ∧ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_proxy_session_auth -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_auth_dfrac_op_valid in H.
    destruct H as (?&?). iPureIntro.
    apply map_fmap_equiv_inj in H0.
    2:{ apply _. }
    apply leibniz_equiv in H0. split; auto.
  Qed.

  Lemma othreadG_proxy_session_valid i π s1 s2 q1 q2 :
    othreadG_proxy_session i π s1 q1 ∗ othreadG_proxy_session i π s2 q2
    ⊢ ⌜ s1 = s2 ∧ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /othreadG_proxy_session -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_frag_op_valid in H.
    destruct H as (?&?). iPureIntro.
    apply to_agree_op_valid, leibniz_equiv in H0. split; auto.
  Qed.

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
        othreadG_elem i ∗ othreadG_obls i ∅ ∗ othreadG_exec i (1/2 + 1/2/2)%Qp.
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
        ([∗ set] i ∈ Θ, othreadG_elem i ∗ othreadG_obls i ∅ ∗ othreadG_exec i (1/2 + 1/2/2)%Qp).
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

  Local Lemma othread_alloc_obl_1 j TP i G k :
    oblG_owner k j (1/2 + 1/2/2/2 + 1/2/2 + 1/2/2/2/2)%Qp ∗
    othread TP ∗ othreadG_obls i G ∗ oblG_owner k i (1/2/2/2/2)%Qp
    ⊢ |==> ⌜k ∉ G⌝ ∗ oblG_owner k j (1/2 + 1/2/2/2 + 1/2/2 + 1/2/2/2/2)%Qp ∗
        othread TP ∗ othreadG_obls i ({[k]} ∪ G) ∗ othreadG_owns i k 1.
  Proof.
    iIntros "(Go0& O& Obs& Go)".
    iPoseProof (oblG_owner_agree with "[$Go0 $Go]") as "(%EQ& %F)". subst j. clear F.
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup with "[$HB $Obs]") as "%Hlui0".
    assert (Hlui : ∃ m, dom m = G ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. destruct Hlui0 as (?&?&?). eauto. }
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
    iMod (othreadG_obls_update _ _ _ (<[k:=tt]>TObls) with "[$HB $Obs]") as "[HB Obs]".
    rewrite dom_insert_L Hm. iFrame "Obs". iModIntro. iSplitR.
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
  Lemma othread_alloc_obl Ω TP i G k :
    osat Ω ∗ othread TP ∗
    othreadG_obls i G ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp
    ⊢ |==> osat Ω ∗ othread TP ∗
        ⌜k ∉ G⌝ ∗ othreadG_obls i ({[k]} ∪ G) ∗
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
    othread TP ∗ othreadG_obls i G ∗ othreadG_owns i k q
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

  Lemma othread_delete_obl TP i G k :
    othread TP ∗ othreadG_obls i G ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ othreadG_obls i (G ∖ {[k]}) ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros "(O & Ho & Hw)". iPoseProof (othread_obls_owns_elem with "[$]") as "%Hkin".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (othreadG_obls_lookup with "[$HB $Ho]") as "%Hlui0".
    assert (Hlui : ∃ m, dom m = G ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. eauto. }
    destruct Hlui as (TObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (othreadG_owns_lookup with "[$His $Hw]") as "%Hluk".
    iMod (othreadG_owns_delete with "[$His $Hw]") as "His".
    iMod (othreadG_obls_update _ _ _ (delete k TObls) with "[$HB $Ho]") as "[HB Ho]".
    rewrite dom_delete_L Hm. iFrame "Ho".
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

  Lemma othread_exec_to_done TP i :
    othread TP ∗ othreadG_exec i (1/2 + 1/2/2)%Qp ∗ othreadG_obls i ∅
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
    ⊢ othreadG_obls i ∅ ∗ (othreadG_obls i ∅ -∗ othread TP).
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

  Lemma othread_obls_open TP i k G :
    k ∈ G →
    othread TP ∗ othreadG_elem i ∗ othreadG_obls i G
    ⊢ othreadG_obls i G ∗
    (oblG_owner k i (1/2/2/2/2)%Qp) ∗
    ((oblG_owner k i (1/2/2/2/2)%Qp) -∗ othread TP).
  Proof.
    iIntros (Ink) "(O& #He& Hobls)". 
    iPoseProof (othread_elem with "[$O $He]") as "%Hin".
    rewrite /othread -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    assert (Hlui : is_Some (Tgls !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (TObls&Hlui).
    iPoseProof (othreadG_obls_lookup with "[$HB $Hobls]") as "%".
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
    osat Ω ∗ othread TP ∗ oassigned (dom Ω) ∗ othreadG_obls i G
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

  Lemma othread_obls_lookup Ω TP k i G :
    k ∈ G →
    osat Ω ∗ othread TP ∗ othreadG_elem i ∗ othreadG_obls i G ∗ oblG_elem k
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

  (** oproxy rules *)
  Lemma oproxy_alloc_thread i TP :
    i ∉ TP →
    oproxy TP ∗ othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅
    ⊢ |==> oproxy ({[i]} ∪ TP) ∗ othreadG_proxy_session_auth i ∅ (1/2).
  Proof.
    iIntros (Hi) "(F& Tx& TG)".
    rewrite /oproxy -!lock. iDestruct "F" as "(%& FT& ST& OT& M)".
    iMod (othreadG_proxy_session_alloc_auth _ i with "ST") as "[ST [Sa $]]". 1: auto.
    iMod (othreadG_proxy_obls_alloc_auth _ i with "OT") as "[OT Oa]". 1: auto.
    iModIntro. iFrame "ST OT FT". iApply big_sepS_union. 1: set_solver.
    iFrame "M". iApply big_sepS_singleton. iFrame. iSplitR; first done.
    iSplitL; last done. iLeft. iFrame. done.
  Qed.

  Lemma oproxy_alloc_threads Θ TP :
    Θ ## TP →
    oproxy TP ∗ ([∗ set] i ∈ Θ, othreadG_exec i (1/2/2) ∗ othreadG_obls i ∅)
    ⊢ |==> oproxy (TP ∪ Θ) ∗ ([∗ set] i ∈ Θ, othreadG_proxy_session_auth i ∅ (1/2)).
  Proof.
    revert TP. pattern Θ. revert Θ. apply set_ind.
    { solve_proper. }
    { iIntros (??) "[T _]". rewrite union_empty_r_L. iFrame. by iModIntro. }
    iIntros (i Θ Nin IH TP Disj) "[F M]".
    rewrite !big_sepS_union. 2,3: set_solver. rewrite !big_sepS_singleton. iDestruct "M" as "(Mi& M)".
    iMod (IH with "[$F $M]") as "(F& $)". 1: set_solver.
    iMod (oproxy_alloc_thread i with "[$F $Mi]") as "(F& Hi)"; first set_solver.
    iModIntro. replace ({[i]} ∪ (TP ∪ Θ)) with (TP ∪ ({[i]} ∪ Θ)) by set_solver.
    iFrame.
  Qed.

  Lemma oproxy_alloc_proxy TP i Ss β :
    i ∈ TP →
    oproxy TP ∗ othreadG_proxy_session_auth i Ss (1/2)
    ⊢ |==> ∃ π s, oproxy TP ∗
               ⌜ Ss !! π = None ⌝ ∗
               othreadG_proxy_session_auth i (<[π:=s]>Ss) (1/2) ∗
               othreadG_proxy_session i π s 1 ∗ othreadG_proxy_obls i π ∅ ∗
               othreadG_bound s β ∗ othreadG_fuel s β.
  Proof.
    iIntros (Ini) "(P& Psa)".
    rewrite /oproxy -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    assert (∃ s, s ∉ Df) as (s&Hs).
    { eexists. eapply is_fresh. }
    iMod (othreadG_bound_id_alloc _ _ β Hs with "FT") as "(FT& #Bs& Hfs)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa0& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H as [<- _].
    iCombine "Psa Psa0" as "Psa". iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Psa1& _)".
      iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa1]") as "%". destruct H. done. }
    assert (∃ π, Ss !! π = None) as (π&Hp).
    { eexists. eapply not_elem_of_dom, is_fresh. }
    iMod (othreadG_proxy_session_alloc _ _ _ s Hp with "Psa") as "(Psa& Ps)".
    assert (Hp2 : Ks !! π = None).
    { apply not_elem_of_dom. apply not_elem_of_dom in Hp. rewrite Dom. auto. }
    iMod(othreadG_proxy_obls_alloc _ _ π with "Poa") as "(Poa& Po)". 1: auto.
    iDestruct "Psa" as "[Psa Psa0]".
    iModIntro. iExists π, s. iFrame "Psa Ps Po Bs Hfs ST PT FT".
    iSplit; last auto. iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Psa0 Poa". iSplit.
    { iPureIntro. rewrite !dom_insert_L Dom. auto. }
    iSplitL "Hex".
    { iLeft. iDestruct "Hex" as "(%& $& $& %)". iPureIntro. destruct H. subst.
      rewrite union_sets_insert_L. 2: auto.
      split; first set_solver. apply disjoint_sets_insert_2; auto. set_solver. }
    iApply big_sepM2_insert; auto.
  Qed.

  Lemma oproxy_delete_proxy TP i Ss π s :
    i ∈ TP →
    oproxy TP ∗ othreadG_proxy_session_auth i Ss (1/2) ∗
    othreadG_proxy_session i π s 1 ∗ othreadG_proxy_obls i π ∅
    ⊢ |==> oproxy TP ∗ othreadG_proxy_session_auth i (delete π Ss) (1/2).
  Proof.
    iIntros (Ini) "(P& Psa& Ps& Po)".
    rewrite /oproxy -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa0& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H as [<- _].
    iCombine "Psa Psa0" as "Psa". iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Psa1& _)".
      iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa1]") as "%". destruct H. done. }
    iPoseProof (othreadG_proxy_session_lookup with "[$Psa $Ps]") as "%LUs".
    iMod (othreadG_proxy_session_delete with "[$Psa $Ps]") as "[Psa Psa0]".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po]") as "%LUo".
    iMod(othreadG_proxy_obls_delete with "[$Poa $Po]") as "Poa".
    iModIntro. iFrame "Psa ST PT FT".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Psa0 Poa". iSplit.
    { iPureIntro. rewrite !dom_delete_L Dom. auto. }
    iSplitL "Hex".
    { iLeft. iDestruct "Hex" as "(%& $& $& %)". iPureIntro. destruct H. subst.
      erewrite (union_sets_delete_L Ks π). 2: eauto.
      split; first set_solver. apply disjoint_sets_delete; auto. }
    iPoseProof (big_sepM2_delete _ _ _ π with "OFs") as "[_ $]"; eauto.
  Qed.

  Lemma oproxy_alloc_obl Ω TP i π s q K β k :
    i ∈ TP →
    osat Ω ∗ othread TP ∗ oproxy TP ∗
    othreadG_proxy_obls i π K ∗ othreadG_proxy_session i π s q ∗ othreadG_bound s β ∗
    oblG_elem k ∗ oblG_owner k i (1/2 + 1/2/2)%Qp ∗ oblG_fuel k β
    ⊢ |==> osat Ω ∗ othread TP ∗ oproxy TP ∗
        ⌜k ∉ K⌝ ∗ othreadG_proxy_obls i π ({[k]} ∪ K) ∗ othreadG_proxy_session i π s q ∗
        othreadG_owns i k 1 ∗ oblG_owner k i (1/2 + 1/2/2/2 + 1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ini) "(S& T& P& Po& Ps& #Tb& #Oe& Oo& Of)".
    rewrite /oproxy -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_lookup with "[$Psa $Ps]") as "%LUs".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po]") as "%LUo".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo LUs with "OFs") as "[Hp OFs]".
    iDestruct "Hp" as "(%& #Tb0& Hfs)".
    iPoseProof (othreadG_bound_op _ β β0 with "[$Tb $Tb0]") as "(%β1& #Tb1& %Hb)".
    destruct Hb as [Hb1 Hb2]. iClear "Tb Tb0".
    iMod (othread_alloc_obl with "[$S $T $TG $Oe $Oo]") as "(S& T& %Nink& TG& To& Oo)".
    iMod (othreadG_proxy_obls_update _ _ _ _ ({[k]} ∪ K) with "[$Poa $Po]") as "[Poa Po]".
    iModIntro. iFrame "S T FT ST PT Ps To Oo Po".
    assert (Nink2 : k ∉ K).
    { simplify_eq. rewrite not_elem_of_union_sets in Nink. eapply Nink; eauto. }
    iSplit. 2: auto.
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Poa Psa". iSplitR.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUo. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. replace ({[k]} ∪ K) with (K ∪ {[k]}) by set_solver. simplify_eq. split.
      - rewrite union_sets_insert_union_L; auto.
      - apply disjoint_sets_insert_union_singleton_not_in; auto. }
    iEval (rewrite -(insert_id _ _ _ LUs)). iApply big_sepM2_insert_delete.
    iFrame "OFs Tb1". iApply (big_sepS_union). 1: set_solver.
    iSplitR "Hfs".
    { iApply big_sepS_singleton. iFrame "Of Oe". iPureIntro. eauto. }
    { iApply (big_sepS_impl with "Hfs"). iIntros "!> %% (%&%&$&$)". iPureIntro. etrans; eauto. }
  Qed.

  Lemma oproxy_delete_obl TP i π K k :
    i ∈ TP →
    k ∈ K →
    othread TP ∗ oproxy TP ∗
    othreadG_proxy_obls i π K ∗ othreadG_owns i k 1
    ⊢ |==> othread TP ∗ oproxy TP ∗
        othreadG_proxy_obls i π (K ∖ {[k]}) ∗ oblG_owner k i (1/2/2/2/2)%Qp.
  Proof.
    iIntros (Ini Ink) "(T& P& Po& To)".
    rewrite /oproxy -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa& Hex& OFs)".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po]") as "%LUo".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (big_sepM2_delete_l _ _ _ _ _ LUo with "OFs") as "(%s& %LUs& Hp& OFs)".
    iDestruct "Hp" as "(%& #Tb& Hfs)".
    iMod (othread_delete_obl with "[$T $TG $To]") as "(T& TG& Oo)".
    iMod (othreadG_proxy_obls_update _ _ _ _ (K ∖ {[k]}) with "[$Poa $Po]") as "[Poa Po]".
    iModIntro. iFrame "T FT ST PT Oo Po".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Poa Psa". iSplitR.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUo. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. simplify_eq. split.
      - rewrite union_sets_insert_difference_singleton_L; auto.
      - apply disjoint_sets_insert_difference; auto. }
    iEval (rewrite -(insert_id _ _ _ LUs)). iApply big_sepM2_insert_delete.
    iFrame "OFs". iFrame "Tb". iPoseProof (big_sepS_delete with "Hfs") as "[_ $]". auto.
  Qed.

  Lemma oproxy_obl_change_proxy TP i π1 π2 K1 K2 s2 q2 β k :
    i ∈ TP →
    k ∈ K1 →
    oproxy TP ∗
    othreadG_proxy_obls i π1 K1 ∗
    othreadG_proxy_obls i π2 K2 ∗ othreadG_proxy_session i π2 s2 q2 ∗
    othreadG_bound s2 β ∗ oblG_fuel k β
    ⊢ |==> oproxy TP ∗
        othreadG_proxy_obls i π1 (K1 ∖ {[k]}) ∗
        othreadG_proxy_obls i π2 (K2 ∪ {[k]}) ∗ othreadG_proxy_session i π2 s2 q2.
  Proof.
    iIntros (Ini Ink) "(P& Po1& Po2& Ps2& #Tb& Of)".
    rewrite /oproxy -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa& Hex& OFs)".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po1]") as "%LUo1".
    assert (is_Some (Ss !! π1)) as (s1& LUs1).
    { apply elem_of_dom. apply elem_of_dom_2 in LUo1. rewrite -Dom. auto. }
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po2]") as "%LUo2".
    iPoseProof (othreadG_proxy_session_lookup with "[$Psa $Ps2]") as "%LUs2".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& _& %)". destruct H. subst. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iPoseProof (othreadG_proxy_obls_valid _ π1 π2 with "[$Po1 $Po2]") as "%Neqp".
    iMod (othreadG_proxy_obls_update _ _ _ _ (K1 ∖ {[k]}) with "[$Poa $Po1]") as "[Poa Po1]".
    iMod (othreadG_proxy_obls_update _ _ _ _ (K2 ∪ {[k]}) with "[$Poa $Po2]") as "[Poa Po2]".
    iModIntro. iFrame "FT ST PT Po1 Po2 Ps2".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Poa Psa". iSplitR.
    { iPureIntro. rewrite !dom_insert_L. apply elem_of_dom_2 in LUo1, LUo2. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. iPureIntro. assert (Ink2 : k ∈ union_sets Ks).
      { apply elem_of_union_sets; eauto. }
      simplify_eq. split.
      - rewrite union_sets_insert_union_L; cycle 1.
        { rewrite lookup_insert_ne; auto. }
        rewrite union_sets_insert_difference_singleton_L; auto. rewrite -union_difference_L; set_solver.
      - apply disjoint_sets_insert_union_singleton_not_in.
        { rewrite lookup_insert_ne; auto. }
        { apply disjoint_sets_insert_difference; auto. }
        { apply not_elem_of_union_sets. intros. destruct (decide (k0 = π1)).
          - subst. rewrite lookup_insert_eq in H. simplify_eq. set_solver.
          - rewrite lookup_insert_ne in H; auto. specialize (Disj _ _ _ _ n H LUo1). set_solver. }
    }
    iEval (rewrite -(insert_id _ _ _ LUs1)). assert (LUs3 : <[π1:=s1]> Ss !! π2 = Some s2).
    { rewrite lookup_insert_ne; auto. }
    iEval (rewrite -(insert_id _ _ _ LUs3)). iApply big_sepM2_insert_delete.
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo2 LUs2 with "OFs") as "[Fs2 OFs]".
    iPoseProof (big_sepM2_delete _ _ _ π1 K1 s1 with "OFs") as "[Fs1 OFs]".
    { rewrite lookup_delete_ne; auto. }
    { rewrite lookup_delete_ne; auto. }
    iDestruct "Fs1" as "(%βp1& #Bp1& Fs1)". iPoseProof (big_sepS_delete _ _ _ Ink with "Fs1") as "[Fk Fs1]".
    iSplitL "Of Fk Fs2".
    { iDestruct "Fk" as "(%&%&_&#Oe)". iDestruct "Fs2" as "(%& #Tb0& Fs)".
      iPoseProof (othreadG_bound_op _ β β0 with "[$Tb $Tb0]") as "(%β1& #Tb1& %Hb)".
      destruct Hb as [Hb1 Hb2]. iClear "Tb Tb0".
      iFrame "Tb1". iApply big_sepS_union.
      { specialize (Disj _ _ _ _ Neqp LUo1 LUo2). set_solver. }
      iSplitL "Fs".
      { iApply (big_sepS_impl with "Fs"). iIntros "!> %% (%& %& $& $)". iPureIntro. etrans; eauto. }
      iApply big_sepS_singleton. iFrame "Oe Of". iPureIntro. auto. }
    rewrite !delete_insert_ne; auto. iApply big_sepM2_insert_delete. iFrame "OFs".
    iFrame "Bp1". iFrame.
  Qed.

  Lemma oproxy_exec_to_done TP i :
    i ∈ TP →
    othread TP ∗ oproxy TP ∗
    othreadG_exec i (1/2)%Qp ∗ othreadG_proxy_session_auth i ∅ (1/2)%Qp
    ⊢ |==> othread TP ∗ oproxy TP ∗ othreadG_done i.
  Proof.
    iIntros (Ini) "(T& P& Tx& Psa)".
    rewrite /oproxy -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa0& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H as [<- _].
    apply dom_empty_inv_L in Dom. subst. iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Psa1& _)". iCombine "Psa Psa0" as "Psa".
      iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa1]") as "%". destruct H. done. }
    iDestruct "Hex" as "(%& Tx2& TG& %)". destruct H as [Uni Disj].
    rewrite union_sets_empty in Uni. subst.
    iCombine "Tx Tx2" as "Tx".
    iMod (othread_exec_to_done with "[$T $Tx $TG]") as "[T #Td]".
    iModIntro. iFrame "T FT ST PT Td".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Psa0 Poa". iSplit. 1: done.
    iSplitL "Psa".
    { iRight. iFrame. eauto. }
    done.
  Qed.

  Lemma oproxy_proxy_new_session TP i π K PS s1 β :
    i ∈ TP →
    oproxy TP ∗ othreadG_proxy_obls i π K ∗
    othreadG_proxy_session_auth i PS (1/2)%Qp ∗ othreadG_proxy_session i π s1 1 ∗
    ([∗ set] k ∈ K, oblG_fuel k β)
    ⊢ |==> ∃ s2, oproxy TP ∗ othreadG_proxy_obls i π K ∗
              othreadG_proxy_session_auth i (<[π:=s2]>PS) (1/2)%Qp ∗ othreadG_proxy_session i π s2 1 ∗
              othreadG_bound s2 β ∗ othreadG_fuel s2 β.
  Proof.
    iIntros (Ini) "(P& Po& Psa& Ps& KFs)".
    rewrite /oproxy -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa0& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H as [<- _].
    iCombine "Psa Psa0" as "Psa".
    iPoseProof (othreadG_proxy_obls_lookup with "[$Poa $Po]") as "%LUo".
    iPoseProof (othreadG_proxy_session_lookup with "[$Psa $Ps]") as "%LUs".
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Psa1& _)".
      iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa1]") as "%". destruct H. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    assert (∃ s2, s2 ∉ Df) as (s2&Hs).
    { eexists. eapply is_fresh. }
    iMod (othreadG_bound_id_alloc _ _ β Hs with "FT") as "(FT& #Tb& Hfs)".
    iMod (othreadG_proxy_session_update _ _ _ _ s2 with "[$Psa $Ps]") as "[[Psa Psa0] Ps]".
    iModIntro. iFrame "FT ST PT Po Hfs Psa Ps Tb".
    iApply (big_sepS_delete _ _ _ Ini). iFrame "M".
    iFrame "Poa Psa0". iSplit.
    { iPureIntro. rewrite dom_insert_L. apply elem_of_dom_2 in LUs. set_solver. }
    iSplitL "Tx TG".
    { iLeft. iFrame. eauto. }
    iEval (rewrite -(insert_id _ _ _ LUo)). iApply big_sepM2_insert_delete.
    iPoseProof (big_sepM2_delete _ _ _ _ _ _ LUo LUs with "OFs") as "[Fs $]".
    iDestruct "Fs" as "(%& _& Fs)". iPoseProof (big_sepS_sep_2 with "KFs Fs") as "Fs".
    iFrame "Tb". iApply (big_sepS_impl with "Fs"). iIntros "!> %% ($& %& _& _& $)". auto.
  Qed.

  Lemma oproxy_exchange_fuel TP i PS q c :
    i ∈ TP →
    (Ord.O < c)%ord →
    oproxy TP ∗
    othreadG_proxy_session_auth i PS q ∗
    ([∗ map] s ∈ PS, othreadG_fuel s c)
    ⊢ |==> ∃ G, (othreadG_exec i (1 / 2 / 2) -∗ othreadG_obls i G -∗ oproxy TP) ∗
             othreadG_proxy_session_auth i PS q ∗
             othreadG_exec i (1 / 2 / 2) ∗ othreadG_obls i G ∗
             ([∗ set] k ∈ G, oblG_fuel k Ord.one ∗ oblG_elem k).
  Proof.
    iIntros (Ini Ltc) "(P& Psa& Tfs)".
    rewrite /oproxy -!lock. iDestruct "P" as "(%& FT& ST& PT& M)".
    iPoseProof (big_sepS_delete _ _ _ Ini with "M") as "[Mi M]".
    iDestruct "Mi" as "(%&%&%Dom& Poa& Psa0& Hex& OFs)".
    iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H as [<- _].
    iDestruct "Hex" as "[Hex | Hex]"; cycle 1.
    { iDestruct "Hex" as "(_& Psa1& _)". iCombine "Psa0 Psa1" as "Psa0".
      iPoseProof (othreadG_proxy_session_auth_valid with "[$Psa $Psa0]") as "%". destruct H.
      apply Qp.not_add_le_r in H0. done. }
    iDestruct "Hex" as "(%& Tx& TG& %)". destruct H as [Uni Disj].
    iAssert (
        |==> ([∗ map] K;s ∈ Ks;PS,
             ∃ β : obl_fuel, othreadG_bound s β ∗ ([∗ set] k ∈ K, ∃ a : Ord.t, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k)) ∗
          ([∗ map] K ∈ Ks, ([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k)))%I
      with "[Tfs OFs]" as ">[OFs Fs]".
    { iAssert ([∗ map] K;s ∈ Ks;PS, True ∗ othreadG_fuel s c)%I with "[Tfs]" as "Tfs".
      { iApply big_sepM2_sepM.
        - intros. rewrite -!elem_of_dom Dom. auto.
        - iFrame. done. }
      iAssert (|==> ([∗ map] K;s ∈ Ks;PS,
                    (([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k) ∗ True) ∗
                    (∃ β, othreadG_bound s β ∗ ([∗ set] k ∈ K, ∃ a : Ord.t, ⌜(β <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k))))%I
        with "[-]" as ">H"; cycle 1.
      { iPoseProof (big_sepM2_sep with "H") as "[H1 H2]". iFrame.
        iPoseProof (big_sepM2_sepM with "H1") as "[H _]".
        - intros. rewrite -!elem_of_dom Dom. auto.
        - iFrame. done. }
      iPoseProof (big_sepM2_sep with "[$Tfs $OFs]") as "OFs".
      iPoseProof (big_sepM2_alt with "OFs") as "[_ OFs]".
      iApply big_sepM2_alt. iSplitR. 1: eauto. iApply big_sepM_bupd.
      iApply (big_sepM_impl with "OFs"). iIntros "!> %%% [(_& F) H]".
      destruct x as [K s]. simpl. iDestruct "H" as "(%& #Tb& KFs)".
      iMod (othreadG_fuel_spend with "[$Tb $F]") as "(%β1& %HB& #Tb1)". 1: auto.
      iAssert (|==> ([∗ set] k ∈ K, ∃ a : Ord.t, ⌜(β1 <= a)%ord⌝ ∗ oblG_fuel k a ∗ oblG_elem k) ∗
                 ([∗ set] k ∈ K, oblG_fuel k Ord.one ∗ oblG_elem k))%I with "[KFs]" as ">[Fvs Rvs]".
      { iApply big_sepS_sep. iApply big_sepS_bupd. iApply (big_sepS_impl with "KFs").
        iIntros "!> %% (%&%& F& #E)". iFrame "E". iMod (oblG_fuel_lt _ β1 with "F") as "(F& %& %& F1)".
        { eapply Ord.lt_le_lt; eauto. }
        iMod (oblG_fuel_mon _ Ord.one with "F1") as "F1".
        { apply Ord.S_supremum. auto. }
        iModIntro. iSplitR "F1"; iFrame. done. }
      iFrame. eauto. }
    iModIntro. iFrame "Psa Tx TG". iSplitR "Fs".
    - iIntros "Tx TG". iFrame "FT ST PT". 
      iApply (big_sepS_delete _ _ _ Ini). iFrame "M". iFrame "Psa0 Poa". iSplit. 1: done.
      iFrame "OFs". iLeft. iFrame. eauto.
    - subst. clear dependent TP i PS q c Df. iInduction Ks as [ | π K ?? LUp] using map_ind.
      { rewrite union_sets_empty. done. }
      rewrite union_sets_insert_L; last auto. iApply (big_sepS_union).
      { eapply disjoint_sets_insert_disjoint_union_sets; eauto. }
      iPoseProof (big_sepM_insert with "Fs") as "[F Fs]". 1: auto.
      apply disjoint_sets_insert in Disj; last auto. destruct Disj as [MF Disj].
      iPoseProof ("LUp" with "[//] Fs") as "$". iFrame.
  Qed.

End othread.

(* Allocation of initial invariant. *)
Lemma othread_alloc `{SI : indexT} {Σ}
  `{!@osatGS.osatGS _ Σ} `{!othreadGpreS Σ} :
  ⊢ |==> ∃ _ : othreadGS Σ, othread ∅ ∗ oassigned ∅ ∗ oproxy ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR oid (unitUR))) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive (gsetUR _))) as (γO) "HO";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γX) "HX";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive unitUR)) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=bcredUR) ⊤)) as (γF) "HF";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR proxy (gsetUR oid))) ⊤)) as (γP) "HP";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR proxy (agreeR session))) ⊤)) as (γI) "HI";
    first by apply reservation_map_token_valid.
  iModIntro. iExists (OthreadG SI _ _ γS γO γX γE γF γP γI).
  rewrite /othread /oassigned /oproxy -!lock. iSplitL "HS HO HX HE".
  { iExists ∅. iSplitR; first done. replace (⊤ : coPset) with (⊤ ∖ gset_to_coPset ∅); [iFrame; done|]. set_solver. }
  iSplitR; first done.
  iExists ∅. rewrite /othreadG_proxy_session_token /othreadG_proxy_obls_token.
  do 3 replace (⊤ ∖ gset_to_coPset ∅) with (⊤ : coPset) by set_solver. iFrame. done.
Qed.
