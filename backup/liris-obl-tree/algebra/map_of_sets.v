From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.

Definition union_sets `{!EqDecision K} `{!Countable K} `{!EqDecision E} `{!Countable E} (M : gmap K (gset E)) : gset E :=
  map_fold (λ _ K A, K ∪ A) (∅ : gset E) M.
Definition disjoint_sets `{!EqDecision K} `{!Countable K} `{!EqDecision E} `{!Countable E} (M : gmap K (gset E)) : Prop :=
  ∀ j1 j2 s1 s2, j1 ≠ j2 → M !! j1 = Some s1 → M !! j2 = Some s2 → s1 ## s2.

Section map_of_sets.
  Context `{!EqDecision K, !Countable K, !EqDecision E, !Countable E}.
  Implicit Type M : gmap K (gset E).
  Implicit Type s : gset E.
  Implicit Type k j : K.
  Implicit Type e : E.

  (** ** Basic properties of [union_sets] *)

  (** [union_sets] of the empty map is empty. *)
  Lemma union_sets_empty : union_sets (∅ : gmap K (gset E)) = ∅.
  Proof using. by rewrite /union_sets map_fold_empty. Qed.

  (** Inserting at a fresh key amounts to taking the union with the inserted set.
      This is the analogue of [forest_fold_insert_L] in the tree development. *)
  Lemma union_sets_insert_L M k s :
    M !! k = None →
    union_sets (<[k:=s]> M) = s ∪ union_sets M.
  Proof using.
    intros. rewrite /union_sets. rewrite map_fold_insert_L; auto.
    intros; set_solver.
  Qed.

  (** Singleton case. *)
  Lemma union_sets_singleton k s :
    union_sets ({[k := s]} : gmap K (gset E)) = s.
  Proof using.
    rewrite -insert_empty union_sets_insert_L; last apply lookup_empty.
    rewrite union_sets_empty. set_solver.
  Qed.

  (** Deleting a present key splits off its set. Analogue of [forest_fold_delete_L]. *)
  Lemma union_sets_delete_L M k s :
    M !! k = Some s →
    union_sets M = s ∪ union_sets (delete k M).
  Proof using.
    intros. rewrite /union_sets.
    rewrite (map_fold_delete_L _ _ k s); auto.
    intros; set_solver.
  Qed.

  (** ** Membership characterisation of [union_sets] *)

  (** [e] is in [union_sets M] iff some value of [M] contains [e].
      This is one of the most useful lemmas about [union_sets]. *)
  Lemma elem_of_union_sets M e :
    e ∈ union_sets M ↔ ∃ k s, M !! k = Some s ∧ e ∈ s.
  Proof using.
    induction M as [|k s M Hk IH] using map_ind.
    - rewrite union_sets_empty.
      split; [set_solver|].
      intros (?&?&Hlu&_). by rewrite lookup_empty in Hlu.
    - rewrite union_sets_insert_L; auto.
      rewrite elem_of_union IH. split.
      + intros [Hin | (k' & s' & ? & ?)].
        * exists k, s. rewrite lookup_insert_eq. auto.
        * exists k', s'. split; auto. rewrite lookup_insert_ne; auto.
          intros ->; congruence.
      + intros (k' & s' & Hk' & He).
        destruct (decide (k' = k)) as [->|Hne].
        * rewrite lookup_insert_eq in Hk'. by simplify_eq; left.
        * rewrite lookup_insert_ne in Hk'; auto. right. eauto.
  Qed.

  (** Negated form. *)
  Lemma not_elem_of_union_sets M e :
    e ∉ union_sets M ↔ ∀ k s, M !! k = Some s → e ∉ s.
  Proof using.
    rewrite elem_of_union_sets. split; first naive_solver.
    intros HF (k & s & ? & ?). by eapply HF.
  Qed.

  (** ** [union_sets] interacts with subset and union of maps *)

  (** Each value is contained in [union_sets].  Analogue of [forest_fold_subseteq]. *)
  Lemma union_sets_lookup_subseteq M k s :
    M !! k = Some s → s ⊆ union_sets M.
  Proof using.
    intros ? e ?. apply elem_of_union_sets. eauto.
  Qed.

  (** [union_sets] is monotone with respect to map inclusion. *)
  Lemma union_sets_mono M1 M2 :
    M1 ⊆ M2 → union_sets M1 ⊆ union_sets M2.
  Proof using.
    intros HM e He. apply elem_of_union_sets in He as (k & s & ? & ?).
    apply elem_of_union_sets. exists k, s. split; auto.
    eapply lookup_weaken; eauto.
  Qed.

  (** Alternative description: [union_sets] is the union of the values list. *)
  Lemma union_sets_union_list M :
    union_sets M = ⋃ ((map_to_list M).*2).
  Proof using.
    apply set_eq. intros e. rewrite elem_of_union_sets elem_of_union_list.
    split.
    - intros (k & s & Hk & He). exists s. split; last auto.
      apply list_elem_of_fmap. exists (k, s). split; first done.
      by apply elem_of_map_to_list.
    - intros (s & Hs & He). apply list_elem_of_fmap in Hs as ([k s'] & -> & Hin).
      apply elem_of_map_to_list in Hin. eauto.
  Qed.

  (** [union_sets] commutes with disjoint map union. *)
  Lemma union_sets_disj_union_L M1 M2 :
    M1 ##ₘ M2 →
    union_sets (M1 ∪ M2) = union_sets M1 ∪ union_sets M2.
  Proof using.
    revert M2. induction M1 as [|k s M1 Hk IH] using map_ind; intros M2 Hd.
    - rewrite map_empty_union union_sets_empty. set_solver.
    - apply map_disjoint_insert_l in Hd as [Hl Hd].
      rewrite -insert_union_l !union_sets_insert_L; auto.
      + rewrite IH; auto. set_solver.
      + by apply lookup_union_None.
  Qed.

  (** ** Basic properties of [disjoint_sets] *)

  (** Recovering the definition: equivalent to a pairwise statement. *)
  Lemma disjoint_sets_lookup M k1 k2 s1 s2 :
    disjoint_sets M →
    k1 ≠ k2 → M !! k1 = Some s1 → M !! k2 = Some s2 → s1 ## s2.
  Proof using. intros HD; eauto. Qed.

  (** The empty map trivially has disjoint values. *)
  Lemma disjoint_sets_empty : disjoint_sets (∅ : gmap K (gset E)).
  Proof using. intros ?????? Hk. by rewrite lookup_empty in Hk. Qed.

  (** A singleton trivially has disjoint values. *)
  Lemma disjoint_sets_singleton k s :
    disjoint_sets ({[k := s]} : gmap K (gset E)).
  Proof using.
    intros j1 j2 s1 s2 Hne H1 H2.
    apply lookup_singleton_Some in H1 as [-> _].
    apply lookup_singleton_Some in H2 as [-> _]. done.
  Qed.

  (** ** [disjoint_sets] is preserved by submaps *)

  Lemma disjoint_sets_subseteq M1 M2 :
    M1 ⊆ M2 → disjoint_sets M2 → disjoint_sets M1.
  Proof using.
    intros Hsub HD k1 k2 s1 s2 Hne H1 H2.
    eapply HD; eauto using lookup_weaken.
  Qed.

  Lemma disjoint_sets_delete M k :
    disjoint_sets M → disjoint_sets (delete k M).
  Proof using.
    intros. eapply disjoint_sets_subseteq; last eassumption.
    apply delete_subseteq.
  Qed.

  (** ** [disjoint_sets] under insertion *)

  (** Bridge between [map_Forall (λ _ s', s ## s')] and [s ## union_sets]. *)
  Lemma map_Forall_disjoint_union_sets M s :
    map_Forall (λ _ s', s ## s') M ↔ s ## union_sets M.
  Proof using.
    rewrite elem_of_disjoint. split.
    - intros HF e He1 He2. apply elem_of_union_sets in He2 as (k & s' & ? & ?).
      eapply (HF k s'); eauto.
    - intros Hd k s' Hk. apply elem_of_disjoint. intros e He1 He2.
      apply (Hd e); auto. apply elem_of_union_sets. eauto.
  Qed.

  (** [disjoint_sets] under [insert] is equivalent to inserting a set disjoint
      from every existing value, plus disjointness of the rest.
      This is the analogue of [forest_trees_disjoint_insert]. *)
  Lemma disjoint_sets_insert M k s :
    M !! k = None →
    disjoint_sets (<[k:=s]> M) ↔
    map_Forall (λ _ s', s ## s') M ∧ disjoint_sets M.
  Proof using.
    intros Hk. split.
    - intros HD. split.
      + intros k' s' Hk'. assert (k ≠ k') by congruence.
        eapply (HD k k'); auto.
        * by rewrite lookup_insert_eq.
        * rewrite lookup_insert_ne; auto.
      + intros k1 k2 s1 s2 Hne H1 H2.
        assert (k1 ≠ k) by congruence.
        assert (k2 ≠ k) by congruence.
        eapply (HD k1 k2); auto; rewrite lookup_insert_ne; auto.
    - intros [HF HD] k1 k2 s1 s2 Hne H1 H2.
      destruct (decide (k1 = k)) as [->|Hne1].
      + rewrite lookup_insert_eq in H1. simplify_eq.
        rewrite lookup_insert_ne in H2; last done.
        eapply HF; eassumption.
      + rewrite lookup_insert_ne in H1; last done.
        destruct (decide (k2 = k)) as [->|Hne2].
        * rewrite lookup_insert_eq in H2. simplify_eq.
          symmetry. eapply HF; eassumption.
        * rewrite lookup_insert_ne in H2; last done.
          eapply (HD k1 k2 s1 s2); eassumption.
  Qed.

  (** Equivalent variant using [union_sets] instead of [map_Forall]. *)
  Lemma disjoint_sets_insert_union_sets M k s :
    M !! k = None →
    disjoint_sets (<[k:=s]> M) ↔
    s ## union_sets M ∧ disjoint_sets M.
  Proof using.
    intros. rewrite disjoint_sets_insert; auto.
    by rewrite map_Forall_disjoint_union_sets.
  Qed.

  (** Pulling out the disjointness of an inserted value with [union_sets]. *)
  Lemma disjoint_sets_insert_disjoint_union_sets M k s :
    M !! k = None →
    disjoint_sets (<[k:=s]> M) →
    s ## union_sets M.
  Proof using.
    intros Hk HD. by apply (disjoint_sets_insert_union_sets _ _ _ Hk) in HD as [? _].
  Qed.

  (** Constructive form: build [disjoint_sets] by insertion. *)
  Lemma disjoint_sets_insert_2 M k s :
    M !! k = None →
    s ## union_sets M →
    disjoint_sets M →
    disjoint_sets (<[k:=s]> M).
  Proof using.
    intros. by apply disjoint_sets_insert_union_sets; auto.
  Qed.

  (** Each value of a [disjoint_sets] map is disjoint from the union of the
      remaining values. *)
  Lemma disjoint_sets_lookup_disjoint_union_sets_delete M k s :
    disjoint_sets M →
    M !! k = Some s → s ## union_sets (delete k M).
  Proof using.
    intros HD Hk.
    apply map_Forall_disjoint_union_sets. intros k' s' Hk'.
    rewrite lookup_delete_Some in Hk'. destruct Hk' as [Hne Hk'].
    eapply HD; eauto.
  Qed.

  (** ** [disjoint_sets] under disjoint map union *)

  (** [disjoint_sets] of a disjoint union: necessary direction.
      Analogue of [forest_trees_disjoint_union_inv]. *)
  Lemma disjoint_sets_disj_union_inv M1 M2 :
    M1 ##ₘ M2 →
    disjoint_sets (M1 ∪ M2) →
    disjoint_sets M1 ∧ disjoint_sets M2 ∧
    map_Forall (λ _ s, s ## union_sets M2) M1.
  Proof using.
    intros Hd HD. split_and!.
    - eapply disjoint_sets_subseteq; last eassumption.
      apply map_union_subseteq_l.
    - eapply disjoint_sets_subseteq; last eassumption.
      apply map_union_subseteq_r; auto.
    - intros k1 s1 Hk1.
      apply map_Forall_disjoint_union_sets. intros k2 s2 Hk2.
      assert (k1 ≠ k2).
      { intros <-. eapply map_disjoint_Some_l in Hd; last eassumption.
        congruence. }
      eapply (HD k1 k2); eauto.
      + apply lookup_union_Some_l; auto.
      + rewrite lookup_union_r; auto. eapply map_disjoint_Some_l; eauto.
  Qed.

  (** [disjoint_sets] of a disjoint union: sufficient direction.
      Analogue of [forest_trees_disjoint_union]. *)
  Lemma disjoint_sets_disj_union M1 M2 :
    M1 ##ₘ M2 →
    disjoint_sets M1 → disjoint_sets M2 →
    map_Forall (λ _ s, s ## union_sets M2) M1 →
    disjoint_sets (M1 ∪ M2).
  Proof using.
    intros Hd HD1 HD2 HF k1 k2 s1 s2 Hne H1 H2.
    apply lookup_union_Some in H1; auto.
    apply lookup_union_Some in H2; auto.
    destruct H1 as [H1|H1], H2 as [H2|H2].
    - eapply HD1; eauto.
    - specialize (HF _ _ H1). rewrite -map_Forall_disjoint_union_sets in HF.
      eapply HF; eauto.
    - specialize (HF _ _ H2). rewrite -map_Forall_disjoint_union_sets in HF.
      symmetry. eapply HF; eauto.
    - eapply HD2; eauto.
  Qed.

  (** Combined iff form. *)
  Lemma disjoint_sets_disj_union_iff M1 M2 :
    M1 ##ₘ M2 →
    disjoint_sets (M1 ∪ M2) ↔
    disjoint_sets M1 ∧ disjoint_sets M2 ∧
    map_Forall (λ _ s, s ## union_sets M2) M1.
  Proof using.
    intros. split.
    - by apply disjoint_sets_disj_union_inv.
    - intros (?&?&?). by apply disjoint_sets_disj_union.
  Qed.

  (** ** [union_sets] under set operations on individual values *)

  (** Replacing the value at key [k] with [s']: the result is independent of
      whether [k] was already present.  Generalises [union_sets_insert_L]. *)
  Lemma union_sets_insert_replace M k s' :
    union_sets (<[k:=s']> M) = s' ∪ union_sets (delete k M).
  Proof using.
    rewrite -insert_delete_eq. apply union_sets_insert_L, lookup_delete_eq.
  Qed.

  (** Extending the value at [k] by [s']: the new union adds exactly [s']. *)
  Lemma union_sets_insert_union_L M k s s' :
    M !! k = Some s →
    union_sets (<[k:= s ∪ s']> M) = s' ∪ union_sets M.
  Proof using.
    intros Hk. rewrite union_sets_insert_replace.
    rewrite (union_sets_delete_L M k s); auto. set_solver.
  Qed.

  (** Shrinking the value at [k] by [s']: the result is contained in the
      original union.  Note this only requires a [⊆], not [=], because
      elements of [s'] that also belong to other values of [M] still appear
      in the resulting union. *)
  Lemma union_sets_insert_difference_subseteq M k s s' :
    M !! k = Some s →
    union_sets (<[k:= s ∖ s']> M) ⊆ union_sets M.
  Proof using.
    intros Hk. rewrite union_sets_insert_replace.
    rewrite (union_sets_delete_L M k s); auto. set_solver.
  Qed.

  (** When [M] is [disjoint_sets], shrinking by [s'] removes exactly
      [s' ∩ s] from the union. *)
  Lemma union_sets_insert_difference_L M k s s' :
    disjoint_sets M →
    M !! k = Some s →
    union_sets (<[k:= s ∖ s']> M) = union_sets M ∖ (s' ∩ s).
  Proof using.
    intros HD Hk.
    pose proof (disjoint_sets_lookup_disjoint_union_sets_delete _ _ _ HD Hk) as Hdj.
    rewrite union_sets_insert_replace.
    rewrite (union_sets_delete_L M k s); auto.
    apply set_eq. intros e. set_solver.
  Qed.

  (** When also [s' ⊆ s], the formula simplifies: shrinking removes [s']
      itself. *)
  Lemma union_sets_insert_difference_subseteq_L M k s s' :
    disjoint_sets M →
    M !! k = Some s →
    s' ⊆ s →
    union_sets (<[k:= s ∖ s']> M) = union_sets M ∖ s'.
  Proof using.
    intros. rewrite union_sets_insert_difference_L; auto.
    f_equal. set_solver.
  Qed.

  (** Singleton-element variants: removing a single element from [s]. *)
  Lemma union_sets_insert_difference_singleton_L M k s e :
    disjoint_sets M →
    M !! k = Some s →
    e ∈ s →
    union_sets (<[k:= s ∖ {[e]}]> M) = union_sets M ∖ {[e]}.
  Proof using.
    intros. apply union_sets_insert_difference_subseteq_L; auto.
    set_solver.
  Qed.

  (** ** [disjoint_sets] under set operations on individual values *)

  (** Splitting [disjoint_sets] around a key: equivalent to the disjointness
      of the rest of the map, plus the disjointness of the value at [k]
      from everything else. *)
  Lemma disjoint_sets_lookup_iff M k s :
    M !! k = Some s →
    disjoint_sets M ↔
    disjoint_sets (delete k M) ∧ s ## union_sets (delete k M).
  Proof using.
    intros Hk. split.
    - intros HD. split.
      + by apply disjoint_sets_delete.
      + by eapply disjoint_sets_lookup_disjoint_union_sets_delete.
    - intros [HDdel Hsd].
      rewrite -(insert_delete_id _ _ _ Hk).
      apply disjoint_sets_insert_2; [apply lookup_delete_eq | done | done].
  Qed.

  (** Replacing the value at [k] with a subset preserves [disjoint_sets]. *)
  Lemma disjoint_sets_insert_subseteq M k s s' :
    M !! k = Some s →
    s' ⊆ s →
    disjoint_sets M →
    disjoint_sets (<[k:=s']> M).
  Proof using.
    intros Hk Hsub HD.
    apply (disjoint_sets_lookup_iff _ k s) in HD as [HDdel Hsd]; last done.
    rewrite -insert_delete_eq.
    apply disjoint_sets_insert_2.
    - apply lookup_delete_eq.
    - set_solver.
    - done.
  Qed.

  (** Shrinking the value at [k] by [s'] always preserves [disjoint_sets].
      Special case of [disjoint_sets_insert_subseteq] with [s' := s ∖ s']. *)
  Lemma disjoint_sets_insert_difference M k s s' :
    M !! k = Some s →
    disjoint_sets M →
    disjoint_sets (<[k:= s ∖ s']> M).
  Proof using.
    intros. eapply disjoint_sets_insert_subseteq; eauto. set_solver.
  Qed.

  (** Extending the value at [k] by [s'] preserves [disjoint_sets] iff
      [s'] is disjoint from every other value of [M].  This is the analogue
      of [disjoint_sets_insert_union_sets] for the case [k ∈ dom M]. *)
  Lemma disjoint_sets_insert_union_iff M k s s' :
    M !! k = Some s →
    disjoint_sets (<[k:= s ∪ s']> M) ↔
    disjoint_sets M ∧ s' ## union_sets (delete k M).
  Proof using.
    intros Hk.
    rewrite -insert_delete_eq.
    rewrite disjoint_sets_insert_union_sets; last apply lookup_delete_eq.
    rewrite disjoint_union_l.
    rewrite (disjoint_sets_lookup_iff M k s); last done.
    tauto.
  Qed.

  (** Convenience: forward direction. *)
  Lemma disjoint_sets_insert_union M k s s' :
    M !! k = Some s →
    disjoint_sets M →
    s' ## union_sets (delete k M) →
    disjoint_sets (<[k:= s ∪ s']> M).
  Proof using.
    intros. by apply disjoint_sets_insert_union_iff.
  Qed.

  (** Inverse direction. *)
  Lemma disjoint_sets_insert_union_inv M k s s' :
    M !! k = Some s →
    disjoint_sets (<[k:= s ∪ s']> M) →
    disjoint_sets M ∧ s' ## union_sets (delete k M).
  Proof using.
    intros Hk HD. by apply (disjoint_sets_insert_union_iff _ _ _ _ Hk).
  Qed.

  (** Adding a single fresh element [e] to the value at [k]: this preserves
      [disjoint_sets] iff [e] is not in any other value of [M].  In
      particular, it is enough that [e ∉ union_sets M]. *)
  Lemma disjoint_sets_insert_union_singleton M k s e :
    M !! k = Some s →
    disjoint_sets M →
    e ∉ union_sets (delete k M) →
    disjoint_sets (<[k:= s ∪ {[e]}]> M).
  Proof using.
    intros. apply disjoint_sets_insert_union; auto. set_solver.
  Qed.

  (** Even simpler: [e ∉ union_sets M] suffices. *)
  Lemma disjoint_sets_insert_union_singleton_not_in M k s e :
    M !! k = Some s →
    disjoint_sets M →
    e ∉ union_sets M →
    disjoint_sets (<[k:= s ∪ {[e]}]> M).
  Proof using.
    intros Hk HD He. apply disjoint_sets_insert_union_singleton; auto.
    rewrite (union_sets_delete_L M k s) in He; auto. set_solver.
  Qed.

End map_of_sets.
