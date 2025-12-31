From iris.algebra Require Import agree gset gmap_view reservation_map mono_nat.
From iris.bi.lib Require Import cmra fractional.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From liris.base_logic Require Export glsat.

(** The ghost state for thread obligations *)
Module globlGS.

  Notation gl_versionO := (leibnizO gl_version).

  (* Assumes thread ids are positive *)
  Class globlGpreS `{SI : indexT} (Σ : gFunctors) : Set :=
    GloblGpreS {
        globlGpreS_owns : inG Σ (reservation_mapUR (gmap_viewR gl_id (agreeR gl_versionO)));
        globlGpreS_obls : inG Σ (gmap_viewR positive (gset_disjUR gl_id));
        globlGpreS_exec : inG Σ (reservation_mapUR mono_natUR);
        globlGpreS_elem : inG Σ (gmap_viewR positive unitUR);
      }.

  Class globlGS `{SI : indexT} (Σ : gFunctors) : Set :=
    GloblG {
        globl_inG : globlGpreS Σ;
        owns_name : gname;
        obls_name : gname;
        exec_name : gname;
        elem_name : gname;
      }.

  Definition globlΣ `{SI : indexT} : gFunctors :=
    #[GFunctor (reservation_mapUR (gmap_viewR gl_id (agreeR gl_versionO)));
      GFunctor (gmap_viewR positive (gset_disjUR gl_id));
      GFunctor (reservation_mapUR mono_natUR);
      GFunctor (gmap_viewR positive unitUR)
      ].

  Global Instance subG_globlΣ `{SI : indexT} {Σ} : subG (globlΣ) Σ → (globlGpreS Σ).
  Proof. solve_inG. Qed.

End globlGS.
Import globlGS.

(** User interface *)
(* Make the instances local to this file. We cannot use #[local] in the code *)
(* above, as that would make the instances local to the module. *)
Local Existing Instances globl_inG
  globlGpreS_owns globlGpreS_obls globlGpreS_exec globlGpreS_elem.

(* Owns: thread currently has this obl *)
Definition globlG_owns `{SI : indexT} `{!globlGS Σ} (i : positive) (k : gl_id) (v : gl_version) (q : Qp) : iProp Σ :=
  own owns_name (reservation_map_data i (gmap_view_frag k (DfracOwn q) (to_agree v))).
Global Typeclasses Opaque globlG_owns.
Global Instance: Params (@globlG_owns) 4 := {}.

Local Definition globlG_owns_token_id `{SI : indexT} `{!globlGS Σ} TP : iProp Σ :=
  (own owns_name (reservation_map_token (A:=gmap_viewR gl_id (agreeR gl_versionO)) (⊤ ∖ gset_to_coPset TP))).

Local Definition globlG_owns_auth_obls `{SI : indexT} `{!globlGS Σ}
  i (TObls : gmap gl_id gl_version) : iProp Σ :=
  (own owns_name (reservation_map_data i (gmap_view_auth (DfracOwn 1) (to_agree <$> TObls)))).

(* Thread: live obligations that this thread knows, also fix to empty when thread terminates *)
Definition globlG_obls `{SI : indexT} `{!globlGS Σ} (i : positive) (G : gset gl_id) (q : Qp) : iProp Σ :=
  own obls_name (gmap_view_frag i (DfracOwn q) (GSet G)).
Global Typeclasses Opaque globlG_obls.
Global Instance: Params (@globlG_obls) 4 := {}.

Local Definition globlG_obls_auth_id `{SI : indexT} `{!globlGS Σ}
  (Tgls : gmap positive (gmap gl_id gl_version)) : iProp Σ :=
  (own obls_name (gmap_view_auth (DfracOwn 1) (GSet <$> (dom <$> Tgls)))).

(* Exec: tracks whether thread is executing or terminated *)
Definition globlG_exec `{SI : indexT} `{!globlGS Σ} (i : positive) (q : Qp) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN{#q} 0)).
Global Typeclasses Opaque globlG_exec.
Global Instance: Params (@globlG_exec) 4 := {}.

Definition globlG_term_auth `{SI : indexT} `{!globlGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (●MN 1)).
Global Typeclasses Opaque globlG_term_auth.
Global Instance: Params (@globlG_term_auth) 4 := {}.

Definition globlG_term `{SI : indexT} `{!globlGS Σ} (i : positive) : iProp Σ :=
  own exec_name (reservation_map_data i (◯MN 1)).
Global Typeclasses Opaque globlG_term.
Global Instance: Params (@globlG_term) 4 := {}.

Local Definition globlG_exec_token_id `{SI : indexT} `{!globlGS Σ} TP : iProp Σ :=
  (own exec_name (reservation_map_token (A:=mono_natUR) (⊤ ∖ gset_to_coPset TP))).

(* Elem: keeps the fact that a key is inside a map *)
Definition globlG_elem `{SI : indexT} `{!globlGS Σ} (i : positive) : iProp Σ :=
  own elem_name (gmap_view_frag i DfracDiscarded ()).
Global Typeclasses Opaque globlG_elem.
Global Instance: Params (@globlG_elem) 4 := {}.

Local Definition globlG_elem_auth_id `{SI : indexT} `{!globlGS Σ}
  (Tgls : gmap positive (gmap gl_id gl_version)) : iProp Σ :=
  (own elem_name (gmap_view_auth (DfracOwn 1) ((λ _, ()) <$> Tgls))).

(* Global invariant for the thread obligations state. *)
Definition globl `{SI : indexT} `{GL : ghost_lock_class} {Σ}
  `{!@glsatGS.glsatGS _ GL Σ} `{!globlGS Σ}
  (TP : gset positive) : iProp Σ :=
  locked
    (∃ (Tgls : gmap positive (gmap gl_id gl_version)),
        (⌜ dom Tgls = TP ⌝) ∗
        globlG_owns_token_id TP ∗
        globlG_obls_auth_id Tgls ∗
        globlG_exec_token_id TP ∗
        globlG_elem_auth_id Tgls ∗
        ([∗ map] i ↦ TObls ∈ Tgls,
           (globlG_exec i (1/2/2)%Qp ∨ (globlG_term_auth i ∗ globlG_obls i ∅ 1)) ∗
           globlG_owns_auth_obls i TObls ∗
           ([∗ map] k ↦ v ∈ TObls, glG_locked k v (1/2/2/2)%Qp ∗ glG_owner k i (1/2/2/2/2)%Qp)
        )
    )%I.

(* Global invariant that relates obl_states to the thread pool. *)
Definition glassigned `{SI : indexT} `{GL : ghost_lock_class} {Σ}
  `{!@glsatGS.glsatGS _ GL Σ} `{!globlGS Σ}
  (Gls : gmap gl_id gl_version) : iProp Σ :=
  locked
    ([∗ map] k ↦ v ∈ Gls,
       glG_elem k ∗
       ((∃ i, glG_owner k i (1/2/2/2/2)%Qp ∗ globlG_owns i k v (1/2/2)%Qp) ∨
          (glG_unlocked k v)))%I.

Section globl.
  Context `{SI : indexT} `{GL : ghost_lock_class} `{GLSAT : !glsatGS.glsatGS Σ} `{!globlGS Σ}.

  (* Owns *)
  Global Instance globlG_owns_timeless i k v q : Timeless (globlG_owns i k v q).
  Proof. rewrite /globlG_owns. apply _. Qed.

  Global Instance globlG_owns_fractional i k v :
    Fractional (globlG_owns i k v).
  Proof.
    rewrite /globlG_owns. intros p q.
    by rewrite -own_op -!reservation_map_data_op -gmap_view_frag_op agree_idemp.
  Qed.
  Global Instance globlG_owns_as_fractional i k v q :
    AsFractional (globlG_owns i k v q) (globlG_owns i k v) q.
  Proof. split; [auto|apply _]. Qed.

  Local Instance globlG_owns_token_id_timeless TP : Timeless (globlG_owns_token_id TP).
  Proof. rewrite /globlG_owns_token_id. apply _. Qed.
  Local Instance globlG_owns_auth_obls_timeless i TObls : Timeless (globlG_owns_auth_obls i TObls).
  Proof. rewrite /globlG_owns_auth_obls. apply _. Qed.

  (* Obls *)
  Global Instance globlG_obls_timeless i G q : Timeless (globlG_obls i G q).
  Proof. rewrite /globlG_obls. apply _. Qed.

  Local Instance globlG_obls_auth_id_timeless Tgls : Timeless (globlG_obls_auth_id Tgls).
  Proof. rewrite /globlG_obls_auth_id. apply _. Qed.

  (* Exec *)
  Global Instance globlG_exec_timeless i q : Timeless (globlG_exec i q).
  Proof. rewrite /globlG_exec. apply _. Qed.

  Global Instance globlG_exec_fractional i :
    Fractional (globlG_exec i).
  Proof.
    rewrite /globlG_exec. intros p q.
    by rewrite -own_op -!reservation_map_data_op -mono_nat_auth_dfrac_op.
  Qed.
  Global Instance globlG_exec_as_fractional i q :
    AsFractional (globlG_exec i q) (globlG_exec i) q.
  Proof. split; [auto|apply _]. Qed.

  Global Instance globlG_term_auth_timeless i : Timeless (globlG_term_auth i).
  Proof. rewrite /globlG_term_auth. apply _. Qed.

  Global Instance globlG_term_persistent i : Persistent (globlG_term i).
  Proof. rewrite /globlG_term. apply _. Qed.
  Global Instance globlG_term_timeless i : Timeless (globlG_term i).
  Proof. rewrite /globlG_term. apply _. Qed.

  Local Instance globlG_exec_token_id_timeless TP : Timeless (globlG_exec_token_id TP).
  Proof. rewrite /globlG_exec_token_id. apply _. Qed.

  (* Elem *)
  Global Instance globlG_elem_persistent i : Persistent (globlG_elem i).
  Proof. rewrite /globlG_elem. apply _. Qed.
  Global Instance globlG_elem_timeless i : Timeless (globlG_elem i).
  Proof. rewrite /globlG_elem. apply _. Qed.

  Local Instance globlG_elem_auth_id_timeless Tgls : Timeless (globlG_elem_auth_id Tgls).
  Proof. rewrite /globlG_elem_auth_id. apply _. Qed.

  (* Invs *)
  Global Instance globl_timeless TP : Timeless (globl TP).
  Proof. rewrite /globl -lock. apply _. Qed.

  Global Instance glassigned_timeless Gls : Timeless (glassigned Gls).
  Proof. rewrite /glassigned -lock. apply _. Qed.

  (** Elem rules *)
  Lemma globlG_elem_alloc (Tgls : gmap positive (gmap gl_id gl_version)) i M :
    Tgls !! i = None →
    globlG_elem_auth_id Tgls
    ⊢  |==> globlG_elem_auth_id (<[i:=M]>Tgls) ∗
         globlG_elem i.
  Proof.
    rewrite /globlG_elem_auth_id.
    iIntros (Hi) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracDiscarded) ()); try done.
      rewrite !lookup_fmap Hi. done.
    }
    iDestruct "H" as "[H He]". rewrite /globlG_elem. iFrame "He".
    rewrite fmap_insert. done.
  Qed.

  Lemma globlG_elem_elem i (Tgls : gmap positive (gmap gl_id gl_version)) :
    globlG_elem_auth_id Tgls ∗ globlG_elem i
    ⊢ ⌜ i ∈ dom Tgls ⌝.
  Proof.
    rewrite /globlG_elem_auth_id /globlG_elem -own_op own_valid gmap_view_both_validI_total.
    iIntros "[%Q' (_& _ & HQ' & Hval & Hincl)]".
    iPoseProof "HQ'" as "%". iPureIntro. apply elem_of_dom_2 in H. by rewrite dom_fmap_L in H.
  Qed.

  (** Owns rules *)
  Lemma globlG_owns_alloc_id D i :
    i ∉ D →
    globlG_owns_token_id D
    ⊢ |==> globlG_owns_token_id ({[i]} ∪ D) ∗
        globlG_owns_auth_obls i ∅.
  Proof.
    rewrite /globlG_owns_token_id /globlG_owns_auth_obls.
    iIntros (Hi) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ i (gmap_view_auth (DfracOwn 1) (to_agree <$> (∅ : gmap gl_id gl_version))) with "Htk") as "[Htk >H]"; auto.
    { apply gmap_view_auth_valid. }
    by iFrame.
  Qed.

  Lemma globlG_owns_alloc i (TObls : gmap gl_id gl_version) k v :
    TObls !! k = None →
    globlG_owns_auth_obls i TObls
    ⊢ |==> globlG_owns_auth_obls i (<[k:=v]>TObls) ∗
        globlG_owns i k v 1.
  Proof.
    rewrite /globlG_owns_auth_obls /globlG_owns.
    iIntros (Hk) "H". 
    iMod (own_update with "H") as "H".
    { eapply reservation_map_update. eapply (gmap_view_alloc _ k (DfracOwn 1) (to_agree v)); try done.
      rewrite lookup_fmap Hk. done. }
    rewrite reservation_map_data_op. iDestruct "H" as "[H Ho]".
    iFrame "Ho". rewrite fmap_insert. done.
  Qed.

  Lemma globlG_owns_delete i (TObls : gmap gl_id gl_version) k v :
    globlG_owns_auth_obls i TObls ∗ globlG_owns i k v 1
    ⊢ |==> globlG_owns_auth_obls i (delete k TObls).
  Proof.
    rewrite /globlG_owns_auth_obls /globlG_owns -own_op -reservation_map_data_op.
    apply own_update, reservation_map_update.
    rewrite fmap_delete. apply gmap_view_delete.
  Qed.

  Lemma globlG_owns_lookup i TObls k v q :
    globlG_owns_auth_obls i TObls ∗ globlG_owns i k v q
    ⊢ ⌜ TObls !! k = Some v ⌝.
  Proof.
    rewrite /globlG_owns_auth_obls /globlG_owns -!own_op -reservation_map_data_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply reservation_map_data_valid, gmap_view_both_dfrac_valid_discrete_total in H.
    destruct H as (?&_&_&?&?&?).
    iPureIntro. rewrite lookup_fmap in H. destruct (TObls !! k) eqn:HO.
    - inv H. apply to_agree_included_L in H1. subst; auto.
    - done.
  Qed.

  Lemma globlG_owns_valid i k v q :
    globlG_owns i k v q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /globlG_owns. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. done.
  Qed.
  Lemma globlG_owns_valid_2 i k v1 v2 q1 q2 :
    globlG_owns i k v1 q1 ∗ globlG_owns i k v2 q2 ⊢ ⌜ (v1 = v2) ∧ (q1 + q2 ≤ 1)%Qp ⌝.
  Proof.
    rewrite /globlG_owns. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply gmap_view_frag_valid in V. destruct V. apply to_agree_op_valid_L in H0.
    done.
  Qed.

  (** Obls rules *)
  Lemma globlG_obls_alloc Tgls i :
    Tgls !! i = None →
    globlG_obls_auth_id Tgls
    ⊢ |==> globlG_obls_auth_id (<[i:=∅]>Tgls) ∗
          globlG_obls i ∅ 1.
  Proof.
    rewrite /globlG_obls_auth_id /globlG_obls.
    iIntros (Hi) "H". 
    iMod (own_update with "H") as "H".
    { eapply (gmap_view_alloc _ i (DfracOwn 1) (GSet ∅ : gset_disj _)); try done.
      rewrite !lookup_fmap Hi. done.
    }
    iDestruct "H" as "[H Ho]". iFrame "Ho".
    rewrite !fmap_insert. done.
  Qed.

  Lemma globlG_obls_lookup Tgls i G :
    globlG_obls_auth_id Tgls ∗
    globlG_obls i G 1
    ⊢ ⌜ (dom <$> Tgls) !! i = Some G ⌝.
  Proof.
    rewrite /globlG_obls_auth_id /globlG_obls -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_valid in H. destruct H as (_&_&?).
    iPureIntro. apply leibniz_equiv, lookup_fmap_Some in H. destruct H as (?&?&?). inv H. done.
  Qed.
  Lemma globlG_obls_lookup_frac Tgls i G q :
    globlG_obls_auth_id Tgls ∗
    globlG_obls i G q
    ⊢ ∃ G', ⌜ (dom <$> Tgls) !! i = Some G' ∧ G ⊆ G' ⌝.
  Proof.
    rewrite /globlG_obls_auth_id /globlG_obls -!own_op.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_both_dfrac_valid_discrete_total in H. destruct H as (?&_&_&?&?&?).
    iPureIntro. destruct x; last done. apply gset_disj_included in H1.
    eexists. split; last eauto.
    apply lookup_fmap_Some in H. destruct H as (?&?&?). inv H. done.
  Qed.

  Lemma globlG_obls_update Tgls i G M :
    globlG_obls_auth_id Tgls ∗
    globlG_obls i G 1
    ⊢ |==> globlG_obls_auth_id (<[i:=M]>Tgls) ∗
        globlG_obls i (dom M) 1.
  Proof.
    rewrite /globlG_obls_auth_id /globlG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. apply gmap_view_replace. done.
  Qed.
  Lemma globlG_obls_update_local Tgls i q M1 M2 X1 X2 :
    (Tgls !! i = Some M1) →
    (GSet (dom M1), GSet X1) ~l~> (GSet (dom M2), GSet X2) →
    globlG_obls_auth_id Tgls ∗
    globlG_obls i X1 q
    ⊢ |==> globlG_obls_auth_id (<[i:=M2]>Tgls) ∗
        globlG_obls i X2 q.
  Proof.
    intros Hlookup Hlu. rewrite /globlG_obls_auth_id /globlG_obls -!own_op. apply own_update.
    rewrite !fmap_insert. eapply gmap_view_update_local; eauto.
    rewrite !lookup_fmap Hlookup. done.
  Qed.

  Lemma globlG_obls_valid i G q :
    globlG_obls i G q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /globlG_obls. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. apply gmap_view_frag_valid in V. destruct V. done.
  Qed.
  Lemma globlG_obls_valid_2 i G1 G2 q1 q2 :
    globlG_obls i G1 q1 ∗ globlG_obls i G2 q2 ⊢ ⌜ (q1 + q2 ≤ 1)%Qp ∧ G1 ## G2 ⌝.
  Proof.
    rewrite /globlG_obls. iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. apply gmap_view_frag_valid in V. destruct V. split; first done.
    apply gset_disj_valid_op in H0. done.
  Qed.

  Lemma globlG_obls_op_1 i G1 G2 q1 q2 :
    globlG_obls i G1 q1 ∗ globlG_obls i G2 q2 ⊢ globlG_obls i (G1 ∪ G2) (q1 + q2)%Qp.
  Proof.
    rewrite /globlG_obls -own_op -gmap_view_frag_op dfrac_op_own.
    iIntros "H". iPoseProof (own_valid with "H") as "%".
    apply gmap_view_frag_valid in H. destruct H. apply gset_disj_valid_op in H0.
    rewrite gset_disj_union; done.
  Qed.
  Lemma globlG_obls_op_2 i G1 G2 q1 q2 :
    G1 ## G2 →
    globlG_obls i (G1 ∪ G2) (q1 + q2)%Qp ⊢ globlG_obls i G1 q1 ∗ globlG_obls i G2 q2.
  Proof.
    intros Hdj. rewrite /globlG_obls -own_op -gmap_view_frag_op dfrac_op_own.
    rewrite gset_disj_union; done.
  Qed.

  (** Exec rules *)
  Lemma globlG_exec_term_false k q :
    globlG_exec k q ∗ globlG_term k ⊢ False.
  Proof.
    rewrite /globlG_exec /globlG_term. iIntros "[Hl Hd]".
    iCombine "Hl Hd" as "V". iPoseProof (own_valid with "V") as "%V".
    iPureIntro. apply reservation_map_data_valid in V.
    apply mono_nat_both_dfrac_valid in V. destruct V. lia.
  Qed.

  Lemma globlG_exec_to_term k :
    globlG_exec k 1 ⊢ |==> globlG_term_auth k.
  Proof.
    rewrite /globlG_exec /globlG_term_auth.
    apply own_update.
    apply reservation_map_update. apply mono_nat_update. auto.
  Qed.
  Lemma globlG_term_auth_term k :
    globlG_term_auth k ⊢ globlG_term k.
  Proof.
    rewrite /globlG_term_auth /globlG_term.
    apply own_mono.
    apply reservation_map_data_mono. apply mono_nat_included.
  Qed.

  Lemma globlG_exec_valid k q :
    globlG_exec k q ⊢ ⌜ (q ≤ 1)%Qp ⌝.
  Proof.
    rewrite /globlG_exec. iIntros "H".
    iPoseProof (own_valid with "H") as "%V".
    iPureIntro. rewrite reservation_map_data_valid in V.
    apply mono_nat_auth_dfrac_valid in V. by apply dfrac_valid in V.
  Qed.

  Lemma globlG_exec_alloc D k :
    k ∉ D →
    globlG_exec_token_id D
    ⊢ |==> globlG_exec_token_id ({[k]} ∪ D) ∗
        globlG_exec k 1.
  Proof.
    rewrite /globlG_exec_token_id /globlG_exec.
    iIntros (Hk) "Htk".
    iPoseProof (reservation_map_token_alloc_singleton _ _ k (●MN 0) with "Htk") as "[Htk >H]"; auto.
    { apply mono_nat_auth_valid. }
    by iFrame.
  Qed.

  (** globl rules *)
  Lemma globl_elem i TP :
    globl TP ∗ globlG_elem i ⊢ ⌜i ∈ TP⌝.
  Proof.
    rewrite /globl -!lock. iIntros "(O & He)".
    iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (globlG_elem_elem with "[$]") as "%".
    by rewrite -Hdom.
  Qed.

  Lemma globl_alloc_thread i TP :
    i ∉ TP →
    globl TP
    ⊢ |==> globl ({[i]} ∪ TP) ∗
        globlG_elem i ∗ globlG_obls i ∅ 1 ∗ globlG_exec i (1/2 + 1/2/2)%Qp.
  Proof.
    iIntros (Hi) "O".
    rewrite /globl -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    assert (Hlu : Tgls !! i = None).
    { apply not_elem_of_dom. rewrite Hdom. auto. }
    iMod (globlG_elem_alloc _ i ∅ with "HE") as "[HE He]"; first auto.
    iMod (globlG_owns_alloc_id with "HO") as "[HO Ho]"; first done.
    iMod (globlG_obls_alloc _ i with "HB") as "[HB Hb]"; first auto.
    iMod (globlG_exec_alloc _ i with "HX") as "[HX Hx]"; first auto.
    iDestruct "Hx" as "[Hx [Hx' Hx0]]". iCombine "Hx Hx'" as "Hx".
    iModIntro. iFrame "He Hb Hx". iExists (<[i:=∅]>Tgls). iFrame "HE HO HB HX".
    iSplitR.
    { iPureIntro. rewrite dom_insert_L Hdom. done. }
    iApply big_sepM_insert; first done.
    iFrame. done.
  Qed.

  Lemma globl_alloc_threads Θ TP :
    Θ ## TP →
    globl TP
    ⊢ |==> globl (TP ∪ Θ) ∗
        ([∗ set] i ∈ Θ, globlG_elem i ∗ globlG_obls i ∅ 1 ∗ globlG_exec i (1/2 + 1/2/2)%Qp).
  Proof.
    revert TP. pattern Θ. revert Θ. apply set_ind.
    { solve_proper. }
    { iIntros (??) "T". rewrite union_empty_r_L. iFrame. by iModIntro. }
    iIntros (i Θ Nin IH TP Disj) "O".
    iMod (IH with "O") as "(O& Hs)"; first set_solver.
    iMod (globl_alloc_thread i with "O") as "(O& Hi)"; first set_solver.
    iModIntro. replace ({[i]} ∪ (TP ∪ Θ)) with (TP ∪ ({[i]} ∪ Θ)) by set_solver.
    iFrame. iApply big_sepS_union; first set_solver. rewrite big_sepS_singleton. iFrame.
  Qed.

  Local Lemma globl_alloc_obl_1 j TP i G q k v :
    glG_owner k j (1/2 + 1/2/2/2 + 1/2/2 + 1/2/2/2/2)%Qp ∗
    globl TP ∗ globlG_obls i G q ∗
    glG_locked k v (1/2/2/2)%Qp ∗ glG_owner k i (1/2/2/2/2)%Qp
    ⊢ |==> ⌜k ∉ G⌝ ∗ glG_owner k j (1/2 + 1/2/2/2 + 1/2/2 + 1/2/2/2/2)%Qp ∗
        globl TP ∗ globlG_obls i ({[k]} ∪ G) q ∗ globlG_owns i k v 1.
  Proof.
    iIntros "(Go0& O& Obs& Gl& Go)".
    iPoseProof (glG_owner_agree with "[$Go0 $Go]") as "(%EQ& %F)". subst j. clear F.
    rewrite /globl -!lock. iDestruct "O" as "(%& %Hdom& HO& HB& HX& HE& Hm)".
    iPoseProof (globlG_obls_lookup_frac with "[$HB $Obs]") as "%".
    destruct H as (G0& Hlui0& Hsub).
    assert (Hlui : ∃ m, dom m = G0 ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. eauto. }
    destruct Hlui as (TObls& Hm& Hlui).
    iAssert (⌜ TObls !! k = None ⌝)%I with "[Go0 Go Hm]" as "%Hluk".
    { destruct (TObls !! k) eqn:LU; last done. iExFalso.
      iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi _]".
      iDestruct "Hi" as "(Hix & His & Him)".
      iDestruct (big_sepM_delete _ _ k _ LU with "Him") as "[Hk Him]".
      iDestruct "Hk" as "(Gl1 & Go1)".
      iDestruct "Go0" as "(((Go0& Go2)& Go3)& Go4)".
      iCombine "Go1 Go" as "Go". iCombine "Go2 Go" as "Go". iCombine "Go3 Go" as "Go".
      iCombine "Go0 Go" as "Go". iCombine "Go Go4" as "Go".
      iPoseProof (glG_owner_valid with "Go") as "%". done.
    }
    iFrame "Go0".
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iMod (globlG_owns_alloc _ _ _ v Hluk with "His") as "[His Hw]".
    iFrame "Hw".
    iMod (globlG_obls_update_local _ _ _ TObls (<[k:=v]>TObls) _ ({[k]} ∪ G) with "[$HB $Obs]") as "[HB Obs]";
      [eauto | | ].
    { rewrite dom_insert_L. apply gset_disj_alloc_local_update. apply not_elem_of_dom in Hluk. set_solver. }
    iFrame "Obs". iModIntro. iSplitR.
    { iPureIntro. apply not_elem_of_dom in Hluk. rewrite Hm in Hluk. set_solver. }
    iExists (<[i:=(<[k:=v]>TObls)]>Tgls). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HB HX HO". iSplitL "HE".
    { rewrite /globlG_elem_auth_id. rewrite !fmap_insert insert_id; first done.
      rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq Tgls i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame "Hm Hix His". iApply (big_sepM_insert _ _ k); first done. iFrame.
  Qed.

  TODO
  Lemma globl_alloc_obl Ω TP i G q k v :
    glsat Ω ∗ globl TP ∗
    globlG_obls i G q ∗ globlG_elem k ∗
    glG_locked k v (1/2/2/2)%Qp ∗ glG_owner k i (1/2 + 1/2/2)%Qp
    ⊢ |==> glsat Ω ∗ globl TP ∗
        ⌜k ∉ G⌝ ∗ globlG_obls i ({[k]} ∪ G) q ∗
        globlG_owns i k v 1 ∗ glG_owner k i (1/2 + 1/2/2/2 + 1/2/2/2/2)%Qp.
  Proof.
    iIntros "(Osat & Hthread & Ho & #He & Os & Oo)".
    iPoseProof (osat_live_open with "[Osat Os]") as "(Os & Os0 & Osacc)"; first by iFrame.
    iMod (globl_alloc_obl_1 with "[$]") as "(%& Os0 & Os1 & Hthread & Ho & Hw)".
    iModIntro. iFrame. iSplitL; first by iApply "Osacc". done.
  Qed.

  Lemma globl_obls_owns_elem TP i G k q :
    globl TP ∗ globlG_obls i G 1 ∗ globlG_owns i k q
    ⊢ ⌜ k ∈ G ⌝.
  Proof.
    iIntros "(Hthread & Ho & Hw)".
    rewrite /globl -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (globlG_obls_lookup with "[HO Ho]") as "%"; first iFrame.
    assert (Hlui : ∃ m, dom m = G ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in H0. eauto. }
    destruct Hlui as (TObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (globlG_owns_lookup with "[His Hw]") as "%Hluk"; first iFrame.
    iPureIntro. rewrite -Hm. by apply elem_of_dom.
  Qed.

  Lemma globl_delete_obl_frac TP i G q k :
    k ∈ G →
    globl TP ∗ globlG_obls i G q ∗ globlG_owns i k 1
    ⊢ |==> globl TP ∗ globlG_obls i (G ∖ {[k]}) q ∗
           globlG_live k (1/2/2)%Qp ∗ globlG_owner k i (1 / 2 / 2)%Qp.
  Proof using Type*.
    iIntros (Hink) "(Hthread & Ho & Hw)".
    rewrite /globl -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (globlG_obls_lookup_frac with "[HO Ho]") as "%"; first iFrame.
    destruct H0 as (G0&Hlui0&Hsub).
    assert (Hlui : ∃ m, dom m = G0 ∧ Tgls !! i = Some m).
    { rewrite lookup_fmap_Some in Hlui0. eauto. }
    destruct Hlui as (TObls&Hm&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (globlG_owns_lookup with "[His Hw]") as "%Hluk"; first iFrame.
    iMod (globlG_owns_delete with "[His Hw]") as "His"; first iFrame.
    iMod (globlG_obls_update_local _ _ _ TObls (delete k TObls) _ (G ∖ {[k]}) with "[HO Ho]") as "[HO Ho]";
      [eauto | | iFrame |].
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
    iDestruct "Hik" as "[Hik1 Hik2]". iFrame "Hik1 Hik2".
    iModIntro. iExists (<[i:=(delete k TObls)]>Tgls). iSplitR.
    { rewrite dom_insert_lookup_L; done. }
    iFrame "HS HX HO". iSplitL "HE".
    { rewrite !fmap_insert. rewrite insert_id; first done. rewrite lookup_fmap Hlui. done. }
    rewrite -(insert_delete_eq Tgls i). iApply (big_sepM_insert _ _ i).
    { apply lookup_delete_eq. }
    iFrame.
  Qed.
  Lemma globl_delete_obl TP i G k :
    globl TP ∗ globlG_obls i G 1 ∗ globlG_owns i k 1
    ⊢ |==> globl TP ∗ globlG_obls i (G ∖ {[k]}) 1 ∗
           globlG_live k (1/2/2)%Qp ∗ globlG_owner k i (1 / 2 / 2)%Qp.
  Proof using Type*.
    iIntros "(Hthread & Ho & Hw)". iPoseProof (globl_obls_owns_elem with "[$]") as "%Hkin".
    iApply (globl_delete_obl_frac with "[$]"). auto.
  Qed.

  Lemma globl_exec_to_term TP i :
    globl TP ∗ globlG_exec i (1/2)%Qp ∗ globlG_obls i ∅ 1
    ⊢ |==> globl TP ∗ globlG_term i.
  Proof.
    iIntros "(Hthread & Hx & Ho)".
    rewrite /globl -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (globlG_obls_lookup with "[HO Ho]") as "%"; first iFrame.
    assert (Hlui : Tgls !! i = Some ∅).
    { rewrite lookup_fmap_Some in H0. destruct H0 as (?&?&?). apply dom_empty_inv_L in H0. subst; eauto. }
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix _]] & His & Him)"; last first.
    { iExFalso. iPoseProof (globlG_term_auth_term with "[$]") as "Hxt".
      iPoseProof (globlG_exec_term_false with "[$]") as "%F". inversion F.
    }
    iMod (globlG_exec_to_term with "[Hx Hix]") as "Hx".
    { rewrite -(globlG_exec_div_2 _ 1). iFrame. }
    iPoseProof (globlG_term_auth_term with "Hx") as "#Hxt".
    iModIntro. iSplitL; last done.
    iExists Tgls. iSplitR; first done. iFrame "HS HX HO HE".
    iApply (big_sepM_delete _ _ i _ Hlui). iFrame. iRight. iFrame.
  Qed.

  Lemma globl_term_open TP i :
    globl TP ∗ globlG_elem i ∗ globlG_term i
    ⊢ globlG_obls i ∅ 1 ∗ (globlG_obls i ∅ 1 -∗ globl TP).
  Proof.
    iIntros "(Hthread & He & Hx)".
    rewrite /globl -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    iPoseProof (globlG_elem_elem with "[$]") as "%Hini".
    assert (Hlui : ∃ m, Tgls !! i = Some m).
    { rewrite elem_of_dom in Hini. eauto. }
    destruct Hlui as (TObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "([Hix | [Hix Ho]] & His & Him)".
    { iExFalso. iPoseProof (globlG_exec_term_false with "[$]") as "%F". inversion F. }
    iFrame "Ho". iIntros "Ho".
    iExists Tgls. iSplitR; first done. iFrame "HS HX HO HE".
    iApply (big_sepM_delete _ _ i _ Hlui). iFrame. iRight. iFrame.
  Qed.

  Lemma globl_live_open TP i k q :
    globl TP ∗ globlG_elem i ∗ globlG_owns i k q
    ⊢ globlG_owns i k q ∗
    (globlG_live k (1/2/2)%Qp ∗ globlG_owner k i (1 / 2 / 2)%Qp) ∗
    ((globlG_live k (1/2/2)%Qp ∗ globlG_owner k i (1 / 2 / 2)%Qp) -∗ globl TP).
  Proof.
    iIntros "(Hthread & He & Hw)".
    iPoseProof (globl_elem with "[Hthread He]") as "%Hin"; first iFrame.
    rewrite /globl -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    assert (Hlui : is_Some (Tgls !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (TObls&Hlui).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (globlG_owns_lookup with "[His Hw]") as "%Hluk"; first iFrame.
    iPoseProof (big_sepM_delete _ _ _ _ Hluk with "Him") as "[Hk Him]".
    iFrame "Hw Hk". iIntros "Hk". iExists Tgls. iFrame "HS HX HO HE".
    iSplit; first done. iApply (big_sepM_delete _ _ _ _ Hlui). iFrame.
    iApply (big_sepM_delete _ _ _ _ Hluk). iFrame.
  Qed.

  Lemma globl_obls_open TP i k G q :
    k ∈ G →
    globl TP ∗ globlG_elem i ∗ globlG_obls i G q
    ⊢ globlG_obls i G q ∗
    (globlG_live k (1/2/2) ∗ globlG_owner k i (1/2/2)) ∗
    ((globlG_live k (1/2/2) ∗ globlG_owner k i (1/2/2)) -∗ globl TP).
  Proof.
    iIntros (Ink) "(Hthread & He & Hobls)". 
    iPoseProof (globl_elem with "[Hthread He]") as "%Hin"; first iFrame.
    rewrite /globl -!lock. iDestruct "Hthread" as "(%&%Hdom& HS & HX & HO & HE & Hm)".
    assert (Hlui : is_Some (Tgls !! i)).
    { subst TP. by apply elem_of_dom. }
    destruct Hlui as (TObls&Hlui).
    iPoseProof (globlG_obls_lookup_frac with "[$HO $Hobls]") as "(%& (%& %))".
    rewrite lookup_fmap in H0. rewrite Hlui in H0. inv H0.
    assert (Hluk : is_Some (TObls !! k)).
    { apply elem_of_dom. set_solver. }
    destruct Hluk as (fk&Hluk).
    iDestruct (big_sepM_delete _ _ i _ Hlui with "Hm") as "[Hi Hm]".
    iDestruct "Hi" as "(Hix & His & Him)".
    iPoseProof (big_sepM_delete _ _ _ _ Hluk with "Him") as "[Hk Him]".
    iDestruct "Hk" as "[Bl Hk]". iFrame "Bl Hk Hobls". iIntros "Bl".
    iExists Tgls. iFrame. iSplitR; first done.
    iApply (big_sepM_delete _ _ _ _ Hlui). iFrame.
    iApply (big_sepM_delete _ _ _ _ Hluk). iFrame.
  Qed.

  (** oassigned rules *)
  Lemma oassigned_add_obl OS k :
    oassigned OS ∗
    (globlG_elem k ∗ ((∃ i, globlG_owner k i (1/2/2)%Qp ∗ globlG_owns i k (1/2/2)%Qp) ∨ globlG_done k))
    ⊢ oassigned ({[k]} ∪ OS).
  Proof.
    iIntros "(A& H)". rewrite /oassigned -!lock. destruct (decide (k ∈ OS)).
    - replace ({[k]} ∪ OS) with OS; last set_solver. iFrame.
    - iApply big_sepS_union; first set_solver. rewrite big_sepS_singleton. iFrame.
  Qed.

  Lemma oassigned_delete_obl OS k :
    k ∈ OS →
    oassigned OS
    ⊢ oassigned (OS ∖ {[k]}) ∗
    (globlG_elem k ∗ ((∃ i, globlG_owner k i (1/2/2)%Qp ∗ globlG_owns i k (1/2/2)%Qp) ∨ globlG_done k)).
  Proof.
    rewrite /oassigned -!lock. iIntros (INk) "A".
    iPoseProof (big_sepS_delete with "A") as "[$ $]". auto.
  Qed.

  Lemma globl_assigned_lookup Ω TP k d i G :
    Ω !! k = Some (obl_live d) →
    obl_owner d = i →
    osat Ω ∗ globl TP ∗ oassigned (dom Ω) ∗ globlG_obls i G 1
    ⊢ ⌜ k ∈ G ⌝.
  Proof.
    rewrite /oassigned -lock. iIntros (LUOk Okd) "(S& T& A& Tbs)".
    iPoseProof (big_sepS_delete _ _ k with "A") as "[A _]".
    { by apply elem_of_dom. }
    iDestruct "A" as "(#Bek& [(%& Bok& Tok) | #Bdk])".
    - iPoseProof (osat_lookup_owner with "[$S $Bek $Bok]") as "(%&%&%)". rewrite LUOk in H0. inv H0.
      iApply (globl_obls_owns_elem with "[$T $Tbs $Tok]").
    - iPoseProof (osat_obl_is_done_weak with "[$S $Bek $Bdk]") as "(%&%)". rewrite LUOk in H0. inv H0.
  Qed.

  Lemma globl_obls_lookup Ω TP k i G q :
    k ∈ G →
    osat Ω ∗ globl TP ∗ globlG_elem i ∗ globlG_obls i G q ∗ globlG_elem k
    ⊢ ∃ d, ⌜ Ω !! k = Some (obl_live d) ∧ obl_owner d = i ⌝.
  Proof.
    iIntros (Ink) "(S& T& #Tei& Tbs& #Bek)".
    iPoseProof (globl_obls_open with "[$T $Tei $Tbs]") as "(Tbs& (Bli& Bok)& Acc)". 1: eauto.
    iPoseProof (osat_lookup_owner with "[$S $Bek $Bok]") as "(%& %)". iExists d. done.
  Qed.

End globl.

(* Allocation of initial invariant. *)
Lemma globl_alloc `{SI : indexT} `{WFA : WFOCM.pack A} {ps} {Σ} `{!@osatGS.osatGS _ _ WFA ps positive Σ} `{!globlGpreS Σ} :
  ⊢ |==> ∃ _ : globlGS Σ, globl ∅ ∗ oassigned ∅.
Proof.
  iIntros.
  iMod (own_alloc (reservation_map_token (A:=(gmap_viewR gl_id unitUR)) ⊤)) as (γS) "HS";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive (gset_disjUR _))) as (γO) "HO";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (reservation_map_token (A:=mono_natUR) ⊤)) as (γX) "HX";
    first by apply reservation_map_token_valid.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅ : gmap_viewR positive unitUR)) as (γE) "HE";
    first by apply gmap_view_auth_valid.
  iModIntro; iExists (GloblsG SI _ _ γS γO γX γE).
  rewrite /globl /oassigned -!lock. iSplitL; last done.
  iExists ∅. iSplitR; first done.
  replace (⊤ ∖ gset_to_coPset ∅) with (⊤ : coPset); [iFrame; done|].
  set_solver.
Qed.
