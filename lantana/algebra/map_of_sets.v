From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.

(** Maps of sets. [union_sets M] is the union of the values of [M]; [disjoint_sets M] says that
    they are pairwise disjoint. [filter_sets M ks] (below) keeps the keys in [ks]. *)
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

  Lemma union_sets_empty : union_sets (∅ : gmap K (gset E)) = ∅.
  Proof using. by rewrite /union_sets map_fold_empty. Qed.

  (** Inserting at a fresh key amounts to taking the union with the inserted set. *)
  Lemma union_sets_insert_L M k s :
    M !! k = None →
    union_sets (<[k:=s]> M) = s ∪ union_sets M.
  Proof using.
    intros. rewrite /union_sets. rewrite map_fold_insert_L; auto.
    intros; set_solver.
  Qed.

  Lemma union_sets_singleton k s :
    union_sets ({[k := s]} : gmap K (gset E)) = s.
  Proof using.
    rewrite -insert_empty union_sets_insert_L; last apply lookup_empty.
    rewrite union_sets_empty. set_solver.
  Qed.

  (** Deleting a present key splits off its set. *)
  Lemma union_sets_delete_L M k s :
    M !! k = Some s →
    union_sets M = s ∪ union_sets (delete k M).
  Proof using.
    intros. rewrite /union_sets.
    rewrite (map_fold_delete_L _ _ k s); auto.
    intros; set_solver.
  Qed.

  (** ** Membership characterisation of [union_sets] *)

  (** [e] is in [union_sets M] iff some value of [M] contains [e]. *)
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

  (** Each value is contained in [union_sets]. *)
  Lemma union_sets_lookup_subseteq M k s :
    M !! k = Some s → s ⊆ union_sets M.
  Proof using.
    intros ? e ?. apply elem_of_union_sets. eauto.
  Qed.

  Lemma union_sets_mono M1 M2 :
    M1 ⊆ M2 → union_sets M1 ⊆ union_sets M2.
  Proof using.
    intros HM e He. apply elem_of_union_sets in He as (k & s & ? & ?).
    apply elem_of_union_sets. exists k, s. split; auto.
    eapply lookup_weaken; eauto.
  Qed.

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

  Lemma disjoint_sets_lookup M k1 k2 s1 s2 :
    disjoint_sets M →
    k1 ≠ k2 → M !! k1 = Some s1 → M !! k2 = Some s2 → s1 ## s2.
  Proof using. intros HD; eauto. Qed.

  Lemma disjoint_sets_empty : disjoint_sets (∅ : gmap K (gset E)).
  Proof using. intros ?????? Hk. by rewrite lookup_empty in Hk. Qed.

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
      from every existing value, plus disjointness of the rest. *)
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

  (** [disjoint_sets] of a disjoint union: necessary direction. *)
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

  (** [disjoint_sets] of a disjoint union: sufficient direction. *)
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

  (** Singleton-element variant: removing a single element from [s]. *)
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

  (** Adding an element [e] to the value at [k] preserves [disjoint_sets] if [e] is in no other
      value of [M]. *)
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

Definition filter_sets `{!EqDecision K} `{!Countable K} `{!EqDecision E} `{!Countable E} (M : gmap K (gset E)) (ks : gset K) : gmap K (gset E) :=
  filter (λ '(k, _), k ∈ ks) M.

Section filter_sets.
  Context `{!EqDecision K, !Countable K, !EqDecision E, !Countable E}.
  Implicit Type M : gmap K (gset E).
  Implicit Type s : gset E.
  Implicit Type ks : gset K.
  Implicit Type k j : K.
  Implicit Type e : E.

  (** ** [filter_sets] and basic map operations ([insert], [delete], [∈], [dom], [⊆]) *)

  Lemma filter_sets_lookup_Some M ks k s :
    filter_sets M ks !! k = Some s ↔
    M !! k = Some s ∧ k ∈ ks.
  Proof using.
    split.
    - intros H.
      apply map_lookup_filter_Some in H.
      destruct H as [H Hk]. simpl in Hk. done.
    - intros [H Hk].
      apply map_lookup_filter_Some. split; auto.
  Qed.

  Lemma filter_sets_lookup_None M ks k :
    filter_sets M ks !! k = None ↔
    M !! k = None ∨ k ∉ ks.
  Proof using.
    split.
    - intros Hfilt.
      destruct (M !! k) as [s|] eqn:Hlu; [right|left]; auto.
      intros Hk.
      assert (filter_sets M ks !! k = Some s).
      { apply filter_sets_lookup_Some. split; auto. }
      rewrite Hfilt in H. discriminate.
    - intros [Hnone|Hnot].
      + destruct (filter_sets M ks !! k) as [s|] eqn:Hfilt; auto.
        apply filter_sets_lookup_Some in Hfilt as [Hlu _].
        rewrite Hnone in Hlu. discriminate.
      + destruct (filter_sets M ks !! k) as [s|] eqn:Hfilt; auto.
        apply filter_sets_lookup_Some in Hfilt as [_ Hk].
        contradiction.
  Qed.

  Lemma filter_sets_lookup_None_notin M ks k :
    k ∉ ks ->
    filter_sets M ks !! k = None.
  Proof using.
    intros Hk.
    apply filter_sets_lookup_None. right. done.
  Qed.

  Lemma filter_sets_lookup_is_Some M ks k :
    is_Some (filter_sets M ks !! k) ↔
    is_Some (M !! k) ∧ k ∈ ks.
  Proof using.
    split.
    - intros [s Hs].
      apply filter_sets_lookup_Some in Hs as [HM Hk].
      split; [eexists; exact HM|done].
    - intros [[s HM] Hk].
      exists s. apply filter_sets_lookup_Some. split; done.
  Qed.

  Lemma filter_sets_empty M :
    filter_sets M ∅ = ∅.
  Proof using.
    apply map_eq=>k.
    rewrite lookup_empty.
    apply filter_sets_lookup_None. right. set_solver.
  Qed.

  Lemma filter_sets_subseteq M ks :
    filter_sets M ks ⊆ M.
  Proof using.
    rewrite /filter_sets.
    apply map_filter_subseteq.
  Qed.

  Lemma filter_sets_dom M ks :
    dom (filter_sets M ks) = dom M ∩ ks.
  Proof using.
    apply set_eq=>k.
    rewrite elem_of_dom.
    split.
    - intros [s Hs].
      apply filter_sets_lookup_Some in Hs as [HM Hk].
      apply elem_of_intersection. split.
      + apply elem_of_dom. eauto.
      + done.
    - intros Hk.
      apply elem_of_intersection in Hk as [Hdom Hks].
      apply elem_of_dom in Hdom as [s Hs].
      exists s. apply filter_sets_lookup_Some. split; auto.
  Qed.

  Lemma elem_of_dom_filter_sets M ks k :
    k ∈ dom (filter_sets M ks) ↔
    k ∈ dom M ∧ k ∈ ks.
  Proof using.
    rewrite filter_sets_dom elem_of_intersection. done.
  Qed.

  Lemma filter_sets_full M ks :
    dom M ⊆ ks ->
    filter_sets M ks = M.
  Proof using.
    intros Hsub.
    apply map_eq=>k.
    destruct (M !! k) as [s|] eqn:Hlu.
    - apply filter_sets_lookup_Some. split; auto.
      apply Hsub. apply elem_of_dom. eauto.
    - apply filter_sets_lookup_None. left. done.
  Qed.

  Lemma filter_sets_mono M ks1 ks2 :
    ks1 ⊆ ks2 ->
    filter_sets M ks1 ⊆ filter_sets M ks2.
  Proof using.
    intros Hsub.
    rewrite map_subseteq_spec.
    intros k s Hk.
    apply filter_sets_lookup_Some in Hk as [HM Hks].
    apply filter_sets_lookup_Some. split; auto.
  Qed.

  Lemma filter_sets_insert M ks k s :
    filter_sets (<[k:=s]> M) ks =
    if decide (k ∈ ks)
    then <[k:=s]> (filter_sets M ks)
    else filter_sets M ks.
  Proof using.
    destruct (decide (k ∈ ks)) as [Hk|Hk].
    - apply map_eq=>j.
      destruct (decide (j = k)) as [->|Hne].
      + rewrite lookup_insert_eq.
        apply filter_sets_lookup_Some. split; [rewrite lookup_insert_eq; done|done].
      + rewrite lookup_insert_ne; [|done].
        destruct (filter_sets M ks !! j) as [sj|] eqn:Hj; auto.
        * apply filter_sets_lookup_Some in Hj as [HM Hjs].
          apply filter_sets_lookup_Some. split; auto.
          rewrite lookup_insert_ne; auto.
        * apply filter_sets_lookup_None in Hj as Hnone.
          apply filter_sets_lookup_None.
          destruct Hnone as [Hnone|Hnot]; [left|right]; auto.
          by rewrite lookup_insert_ne.
    - apply map_eq=>j.
      destruct (decide (j = k)) as [->|Hne].
      + rewrite filter_sets_lookup_None_notin; [|done].
        symmetry. apply filter_sets_lookup_None. right. done.
      + destruct (filter_sets M ks !! j) as [sj|] eqn:Hj; auto.
        * apply filter_sets_lookup_Some in Hj as [HM Hjs].
          apply filter_sets_lookup_Some. split; auto.
          rewrite lookup_insert_ne; auto.
        * apply filter_sets_lookup_None in Hj as Hnone.
          apply filter_sets_lookup_None.
          destruct Hnone as [Hnone|Hnot]; [left|right]; auto.
          by rewrite lookup_insert_ne.
  Qed.

  Lemma filter_sets_insert_in M ks k s :
    k ∈ ks ->
    filter_sets (<[k:=s]> M) ks =
    <[k:=s]> (filter_sets M ks).
  Proof using.
    intros Hk.
    rewrite filter_sets_insert.
    destruct (decide (k ∈ ks)); [done|contradiction].
  Qed.

  Lemma filter_sets_insert_notin M ks k s :
    k ∉ ks ->
    filter_sets (<[k:=s]> M) ks =
    filter_sets M ks.
  Proof using.
    intros Hk.
    rewrite filter_sets_insert.
    destruct (decide (k ∈ ks)); [contradiction|done].
  Qed.

  Lemma filter_sets_delete M ks k :
    filter_sets (delete k M) ks =
    delete k (filter_sets M ks).
  Proof using.
    apply map_eq=>j.
    destruct (decide (j = k)) as [->|Hne].
    - rewrite lookup_delete_eq.
      apply filter_sets_lookup_None. left. apply lookup_delete_eq.
    - rewrite lookup_delete_ne; [|done].
      destruct (filter_sets M ks !! j) as [sj|] eqn:Hj; auto.
      + apply filter_sets_lookup_Some in Hj as [HM Hjs].
        apply filter_sets_lookup_Some. split; auto.
        rewrite lookup_delete_ne; auto.
      + apply filter_sets_lookup_None in Hj as Hnone.
        apply filter_sets_lookup_None.
        destruct Hnone as [Hnone|Hnot]; [left|right]; auto.
        rewrite lookup_delete_ne; auto.
  Qed.

  (** ** [filter_sets] with [union_sets] and [disjoint_sets] *)
  Lemma union_sets_filter_sets_subseteq M ks :
    union_sets (filter_sets M ks) ⊆ union_sets M.
  Proof using.
    eapply union_sets_mono.
    apply filter_sets_subseteq.
  Qed.

  Lemma disjoint_sets_filter_sets M ks :
    disjoint_sets M ->
    disjoint_sets (filter_sets M ks).
  Proof using.
    intros HD.
    eapply disjoint_sets_subseteq; last exact HD.
    apply filter_sets_subseteq.
  Qed.

  (** ** More precise characterisations of [union_sets] and [disjoint_sets] for [filter_sets]. *)

  Lemma elem_of_union_sets_filter_sets M ks e :
    e ∈ union_sets (filter_sets M ks) ↔
    ∃ k s, M !! k = Some s ∧ k ∈ ks ∧ e ∈ s.
  Proof using.
    rewrite elem_of_union_sets.
    split.
    - intros (k&s&Hfilt&He).
      apply filter_sets_lookup_Some in Hfilt as [HM Hks].
      eauto.
    - intros (k&s&HM&Hks&He).
      exists k, s. split; last done.
      apply filter_sets_lookup_Some. split; done.
  Qed.

  Lemma not_elem_of_union_sets_filter_sets M ks e :
    e ∉ union_sets (filter_sets M ks) ↔
    ∀ k s, M !! k = Some s → k ∈ ks → e ∉ s.
  Proof using.
    rewrite elem_of_union_sets_filter_sets.
    split.
    - intros Hnot k s HM Hks He.
      apply Hnot. eauto.
    - intros Hall Hin.
      destruct Hin as (k&s&HM&Hks&He).
      eapply Hall; eauto.
  Qed.

  Lemma union_sets_filter_sets_full M ks :
    dom M ⊆ ks ->
    union_sets (filter_sets M ks) = union_sets M.
  Proof using.
    intros Hsub.
    rewrite filter_sets_full; auto.
  Qed.

  Lemma disjoint_sets_filter_sets_iff M ks :
    disjoint_sets (filter_sets M ks) ↔
    ∀ j1 j2 s1 s2,
      j1 ≠ j2 ->
      j1 ∈ ks ->
      j2 ∈ ks ->
      M !! j1 = Some s1 ->
      M !! j2 = Some s2 ->
      s1 ## s2.
  Proof using.
    split.
    - intros HD j1 j2 s1 s2 Hne Hj1 Hj2 H1 H2.
      eapply HD; eauto;
        apply filter_sets_lookup_Some; split; auto.
    - intros H j1 j2 s1 s2 Hne H1 H2.
      apply filter_sets_lookup_Some in H1 as [HM1 Hj1].
      apply filter_sets_lookup_Some in H2 as [HM2 Hj2].
      eapply H; eauto.
  Qed.

  Lemma disjoint_sets_filter_sets_full M ks :
    dom M ⊆ ks ->
    disjoint_sets (filter_sets M ks) ↔ disjoint_sets M.
  Proof using.
    intros Hsub.
    rewrite filter_sets_full; auto.
  Qed.

  (** ** Structural lemmas for [filter_sets] *)

  Lemma filter_sets_intersection M ks1 ks2 :
    filter_sets (filter_sets M ks1) ks2 =
    filter_sets M (ks1 ∩ ks2).
  Proof using.
    apply map_eq=>k.
    destruct (filter_sets (filter_sets M ks1) ks2 !! k) as [s1|] eqn:H1;
    destruct (filter_sets M (ks1 ∩ ks2) !! k) as [s2|] eqn:H2; auto.
    - apply filter_sets_lookup_Some in H1 as [H1 Hk2].
      apply filter_sets_lookup_Some in H1 as [HM Hk1].
      apply filter_sets_lookup_Some in H2 as [HM' _].
      by rewrite HM in HM'; simplify_eq.
    - exfalso.
      apply filter_sets_lookup_Some in H1 as [H1 Hk2].
      apply filter_sets_lookup_Some in H1 as [HM Hk1].
      assert (filter_sets M (ks1 ∩ ks2) !! k = Some s1).
      { apply filter_sets_lookup_Some. split; [done|].
        apply elem_of_intersection. split; done. }
      rewrite H2 in H. discriminate.
    - exfalso.
      apply filter_sets_lookup_Some in H2 as [HM Hks].
      apply elem_of_intersection in Hks as [Hk1 Hk2].
      assert (filter_sets (filter_sets M ks1) ks2 !! k = Some s2).
      { apply filter_sets_lookup_Some. split.
        - apply filter_sets_lookup_Some. split; done.
        - done.
      }
      rewrite H1 in H. discriminate.
  Qed.

  Lemma filter_sets_idemp M ks :
    filter_sets (filter_sets M ks) ks =
    filter_sets M ks.
  Proof using.
    rewrite filter_sets_intersection.
    f_equal. set_solver.
  Qed.

  Lemma filter_sets_union M ks1 ks2 :
    filter_sets M (ks1 ∪ ks2) =
    filter_sets M ks1 ∪ filter_sets M ks2.
  Proof using.
    apply map_eq=>k.
    destruct (M !! k) as [s|] eqn:HM.
    - destruct (decide (k ∈ ks1)) as [Hk1|Hk1].
      + assert (Hl : filter_sets M (ks1 ∪ ks2) !! k = Some s).
        { apply filter_sets_lookup_Some. split; [done|set_solver]. }
        assert (Hr : (filter_sets M ks1 ∪ filter_sets M ks2) !! k = Some s).
        { apply lookup_union_Some_l.
          apply filter_sets_lookup_Some. split; done. }
        by rewrite Hl Hr.
      + destruct (decide (k ∈ ks2)) as [Hk2|Hk2].
        * assert (Hl : filter_sets M (ks1 ∪ ks2) !! k = Some s).
          { apply filter_sets_lookup_Some. split; [done|set_solver]. }
          assert (Hr : (filter_sets M ks1 ∪ filter_sets M ks2) !! k = Some s).
          { rewrite lookup_union_r.
            - apply filter_sets_lookup_Some. split; done.
            - apply filter_sets_lookup_None. right. done.
          }
          by rewrite Hl Hr.
        * assert (Hl : filter_sets M (ks1 ∪ ks2) !! k = None).
          { apply filter_sets_lookup_None. right. set_solver. }
          assert (Hr : (filter_sets M ks1 ∪ filter_sets M ks2) !! k = None).
          { apply lookup_union_None. split.
            - apply filter_sets_lookup_None. right. done.
            - apply filter_sets_lookup_None. right. done.
          }
          by rewrite Hl Hr.
    - assert (Hl : filter_sets M (ks1 ∪ ks2) !! k = None).
      { apply filter_sets_lookup_None. left. done. }
      assert (Hr : (filter_sets M ks1 ∪ filter_sets M ks2) !! k = None).
      { apply lookup_union_None. split;
          apply filter_sets_lookup_None; left; done. }
      by rewrite Hl Hr.
  Qed.

  Lemma filter_sets_disjoint_keys M ks1 ks2 :
    ks1 ## ks2 ->
    filter_sets M ks1 ##ₘ filter_sets M ks2.
  Proof using.
    intros Hdisj.
    apply map_disjoint_spec=>k s1 s2 H1 H2.
    apply filter_sets_lookup_Some in H1 as [_ Hk1].
    apply filter_sets_lookup_Some in H2 as [_ Hk2].
    set_solver.
  Qed.

  Lemma union_sets_filter_sets_disjoint_union M ks1 ks2 :
    ks1 ## ks2 ->
    union_sets (filter_sets M (ks1 ∪ ks2)) =
    union_sets (filter_sets M ks1) ∪ union_sets (filter_sets M ks2).
  Proof using.
    intros Hdisj.
    rewrite filter_sets_union.
    apply union_sets_disj_union_L.
    by apply filter_sets_disjoint_keys.
  Qed.

  Lemma union_sets_filter_sets_partition M ks1 ks2 :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    union_sets M =
    union_sets (filter_sets M ks1) ∪ union_sets (filter_sets M ks2).
  Proof using.
    intros Hdisj Hdom.
    rewrite <- (filter_sets_full M (ks1 ∪ ks2) Hdom).
    rewrite -union_sets_filter_sets_disjoint_union; auto.
    rewrite filter_sets_idemp. auto.
  Qed.

  Lemma filter_sets_add_key M ks k s :
    M !! k = Some s ->
    k ∉ ks ->
    filter_sets M (ks ∪ {[k]}) =
    <[k:=s]> (filter_sets M ks).
  Proof using.
    intros Hk Hnot.
    apply map_eq=>j.
    destruct (decide (j = k)) as [->|Hne].
    - rewrite lookup_insert_eq.
      apply filter_sets_lookup_Some. split; [done|set_solver].
    - rewrite lookup_insert_ne; [|done].
      destruct (filter_sets M ks !! j) as [sj|] eqn:Hj; auto.
      + apply filter_sets_lookup_Some in Hj as [HM Hjs].
        apply filter_sets_lookup_Some. split; [done|set_solver].
      + apply filter_sets_lookup_None in Hj as Hnone.
        apply filter_sets_lookup_None.
        destruct Hnone as [Hnone|Hnotj]; [left|right]; auto.
        set_solver.
  Qed.

  Lemma filter_sets_remove_key M ks k :
    k ∈ ks ->
    filter_sets M (ks ∖ {[k]}) =
    delete k (filter_sets M ks).
  Proof using.
    intros Hk.
    apply map_eq=>j.
    destruct (decide (j = k)) as [->|Hne].
    - rewrite lookup_delete_eq.
      apply filter_sets_lookup_None. right. set_solver.
    - rewrite lookup_delete_ne; [|done].
      destruct (filter_sets M ks !! j) as [sj|] eqn:Hj; auto.
      + apply filter_sets_lookup_Some in Hj as [HM Hjs].
        apply filter_sets_lookup_Some. split; [done|set_solver].
      + apply filter_sets_lookup_None in Hj as Hnone.
        apply filter_sets_lookup_None.
        destruct Hnone as [Hnone|Hnotj]; [left|right]; auto.
        set_solver.
  Qed.

  (** ** Interaction of [filter_sets] with updates on values, viewed through [union_sets] *)

  Lemma union_sets_filter_sets_insert M ks k s :
    union_sets (filter_sets (<[k:=s]> M) ks) =
    if decide (k ∈ ks)
    then s ∪ union_sets (filter_sets (delete k M) ks)
    else union_sets (filter_sets M ks).
  Proof using.
    destruct (decide (k ∈ ks)) as [Hk|Hk].
    - rewrite filter_sets_insert_in; auto.
      rewrite union_sets_insert_replace.
      rewrite -(filter_sets_delete M ks k).
      done.
    - rewrite filter_sets_insert_notin; auto.
  Qed.

  Lemma union_sets_filter_sets_insert_L M ks k s :
    M !! k = None ->
    k ∈ ks ->
    union_sets (filter_sets (<[k:=s]> M) ks) =
    s ∪ union_sets (filter_sets M ks).
  Proof using.
    intros Hnone Hk.
    rewrite union_sets_filter_sets_insert.
    destruct (decide (k ∈ ks)); last contradiction.
    by rewrite delete_id.
  Qed.

  Lemma union_sets_filter_sets_insert_notin M ks k s :
    k ∉ ks ->
    union_sets (filter_sets (<[k:=s]> M) ks) =
    union_sets (filter_sets M ks).
  Proof using.
    intros Hk.
    rewrite union_sets_filter_sets_insert.
    destruct (decide (k ∈ ks)); [contradiction|done].
  Qed.

  Lemma union_sets_filter_sets_delete_L M ks k s :
    k ∈ ks ->
    M !! k = Some s ->
    union_sets (filter_sets M ks) =
    s ∪ union_sets (filter_sets (delete k M) ks).
  Proof using.
    intros Hk HM.
    assert (filter_sets M ks !! k = Some s) as Hf.
    { apply filter_sets_lookup_Some. split; auto. }
    rewrite (union_sets_delete_L (filter_sets M ks) k s Hf).
    rewrite -(filter_sets_delete M ks k).
    done.
  Qed.

  Lemma union_sets_filter_sets_delete_notin M ks k :
    k ∉ ks ->
    union_sets (filter_sets (delete k M) ks) =
    union_sets (filter_sets M ks).
  Proof using.
    intros Hk.
    rewrite filter_sets_delete.
    rewrite delete_id.
    - done.
    - apply filter_sets_lookup_None_notin. done.
  Qed.

  Lemma union_sets_filter_sets_delete_diff M ks k s :
    k ∈ ks ->
    disjoint_sets M ->
    M !! k = Some s ->
    union_sets (filter_sets (delete k M) ks) =
    union_sets (filter_sets M ks) ∖ s.
  Proof using.
    intros Hk HD HM.
    assert (Hf : filter_sets M ks !! k = Some s).
    { apply filter_sets_lookup_Some. split; auto. }
    assert (HDf : disjoint_sets (filter_sets M ks)).
    { by apply disjoint_sets_filter_sets. }
    pose proof (disjoint_sets_lookup_disjoint_union_sets_delete _ _ _ HDf Hf) as Hdj.
    rewrite filter_sets_delete.
    rewrite (union_sets_delete_L (filter_sets M ks) k s Hf).
    apply set_eq=>e.
    set_solver.
  Qed.

  Lemma union_sets_filter_sets_insert_union_L M ks k s s' :
    k ∈ ks ->
    M !! k = Some s ->
    union_sets (filter_sets (<[k:= s ∪ s']> M) ks) =
    s' ∪ union_sets (filter_sets M ks).
  Proof using.
    intros Hk HM.
    rewrite filter_sets_insert_in; auto.
    apply union_sets_insert_union_L.
    apply filter_sets_lookup_Some. split; auto.
  Qed.

  Lemma union_sets_filter_sets_insert_difference_subseteq M ks k s s' :
    k ∈ ks ->
    M !! k = Some s ->
    union_sets (filter_sets (<[k:= s ∖ s']> M) ks) ⊆
    union_sets (filter_sets M ks).
  Proof using.
    intros Hk HM.
    rewrite filter_sets_insert_in; auto.
    eapply union_sets_insert_difference_subseteq.
    apply filter_sets_lookup_Some. split; auto.
  Qed.

  Lemma union_sets_filter_sets_insert_difference_L M ks k s s' :
    k ∈ ks ->
    disjoint_sets M ->
    M !! k = Some s ->
    union_sets (filter_sets (<[k:= s ∖ s']> M) ks) =
    union_sets (filter_sets M ks) ∖ (s' ∩ s).
  Proof using.
    intros Hk HD HM.
    rewrite filter_sets_insert_in; auto.
    eapply union_sets_insert_difference_L.
    - by apply disjoint_sets_filter_sets.
    - apply filter_sets_lookup_Some. split; auto.
  Qed.

  Lemma union_sets_filter_sets_insert_difference_subseteq_L M ks k s s' :
    k ∈ ks ->
    disjoint_sets M ->
    M !! k = Some s ->
    s' ⊆ s ->
    union_sets (filter_sets (<[k:= s ∖ s']> M) ks) =
    union_sets (filter_sets M ks) ∖ s'.
  Proof using.
    intros Hk HD HM Hsub.
    rewrite union_sets_filter_sets_insert_difference_L; auto.
    f_equal. set_solver.
  Qed.

  Lemma union_sets_filter_sets_insert_difference_singleton_L M ks k s e :
    k ∈ ks ->
    disjoint_sets M ->
    M !! k = Some s ->
    e ∈ s ->
    union_sets (filter_sets (<[k:= s ∖ {[e]}]> M) ks) =
    union_sets (filter_sets M ks) ∖ {[e]}.
  Proof using.
    intros Hk HD HM He.
    eapply union_sets_filter_sets_insert_difference_subseteq_L; eauto.
    set_solver.
  Qed.

  (** ** Exact [disjoint_sets] preservation/decomposition under key partitions *)

  Lemma disjoint_sets_filter_sets_partition_inv M ks1 ks2 :
    ks1 ## ks2 ->
    disjoint_sets (filter_sets M (ks1 ∪ ks2)) ->
    disjoint_sets (filter_sets M ks1) ∧
    disjoint_sets (filter_sets M ks2) ∧
    map_Forall (λ _ s, s ## union_sets (filter_sets M ks2)) (filter_sets M ks1).
  Proof using.
    intros Hdisj HD.
    rewrite filter_sets_union in HD.
    eapply disjoint_sets_disj_union_inv in HD.
    - exact HD.
    - by apply filter_sets_disjoint_keys.
  Qed.

  Lemma disjoint_sets_filter_sets_partition M ks1 ks2 :
    ks1 ## ks2 ->
    disjoint_sets (filter_sets M ks1) ->
    disjoint_sets (filter_sets M ks2) ->
    map_Forall (λ _ s, s ## union_sets (filter_sets M ks2)) (filter_sets M ks1) ->
    disjoint_sets (filter_sets M (ks1 ∪ ks2)).
  Proof using.
    intros Hdisj HD1 HD2 HF.
    rewrite filter_sets_union.
    eapply disjoint_sets_disj_union; eauto.
    by apply filter_sets_disjoint_keys.
  Qed.

  Lemma disjoint_sets_filter_sets_partition_iff M ks1 ks2 :
    ks1 ## ks2 ->
    disjoint_sets (filter_sets M (ks1 ∪ ks2)) ↔
    disjoint_sets (filter_sets M ks1) ∧
    disjoint_sets (filter_sets M ks2) ∧
    map_Forall (λ _ s, s ## union_sets (filter_sets M ks2)) (filter_sets M ks1).
  Proof using.
    intros Hdisj.
    split.
    - by apply disjoint_sets_filter_sets_partition_inv.
    - intros (?&?&?).
      by eapply disjoint_sets_filter_sets_partition.
  Qed.

  Lemma disjoint_sets_filter_sets_partition_cross M ks1 ks2 :
    ks1 ## ks2 ->
    disjoint_sets M ->
    map_Forall (λ _ s, s ## union_sets (filter_sets M ks2)) (filter_sets M ks1).
  Proof using.
    intros Hdisj HD.
    pose proof (disjoint_sets_filter_sets M (ks1 ∪ ks2) HD) as HDf.
    apply (disjoint_sets_filter_sets_partition_inv M ks1 ks2 Hdisj) in HDf.
    tauto.
  Qed.

  Lemma disjoint_sets_filter_sets_full_partition_iff M ks1 ks2 :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    disjoint_sets M ↔
    disjoint_sets (filter_sets M ks1) ∧
    disjoint_sets (filter_sets M ks2) ∧
    map_Forall (λ _ s, s ## union_sets (filter_sets M ks2)) (filter_sets M ks1).
  Proof using.
    intros Hdisj Hdom.
    rewrite <- (filter_sets_full M (ks1 ∪ ks2) Hdom) at 1.
    apply disjoint_sets_filter_sets_partition_iff.
    done.
  Qed.

  (** ** Interaction with adding/removing a key from the filtering set [ks] *)

  Lemma union_sets_filter_sets_add_key M ks k s :
    M !! k = Some s ->
    k ∉ ks ->
    union_sets (filter_sets M (ks ∪ {[k]})) =
    s ∪ union_sets (filter_sets M ks).
  Proof using.
    intros Hk Hnot.
    rewrite (filter_sets_add_key M ks k s Hk Hnot).
    apply union_sets_insert_L.
    apply filter_sets_lookup_None_notin. done.
  Qed.

  Lemma union_sets_filter_sets_remove_key M ks k s :
    M !! k = Some s ->
    k ∈ ks ->
    union_sets (filter_sets M ks) =
    s ∪ union_sets (filter_sets M (ks ∖ {[k]})).
  Proof using.
    intros Hk Hks.
    assert (filter_sets M ks !! k = Some s) as Hf.
    { apply filter_sets_lookup_Some. split; auto. }
    rewrite (union_sets_delete_L (filter_sets M ks) k s Hf).
    rewrite <- (filter_sets_remove_key M ks k Hks).
    done.
  Qed.

  Lemma disjoint_sets_filter_sets_add_key_iff M ks k s :
    M !! k = Some s ->
    k ∉ ks ->
    disjoint_sets (filter_sets M (ks ∪ {[k]})) ↔
    s ## union_sets (filter_sets M ks) ∧ disjoint_sets (filter_sets M ks).
  Proof using.
    intros Hk Hnot.
    rewrite (filter_sets_add_key M ks k s Hk Hnot).
    apply disjoint_sets_insert_union_sets.
    apply filter_sets_lookup_None_notin. done.
  Qed.

  Lemma disjoint_sets_filter_sets_add_key M ks k s :
    M !! k = Some s ->
    k ∉ ks ->
    s ## union_sets (filter_sets M ks) ->
    disjoint_sets (filter_sets M ks) ->
    disjoint_sets (filter_sets M (ks ∪ {[k]})).
  Proof using.
    intros Hk Hnot Hdisj Hds.
    rewrite disjoint_sets_filter_sets_add_key_iff; eauto.
  Qed.

  Lemma disjoint_sets_filter_sets_add_key_inv M ks k s :
    M !! k = Some s ->
    k ∉ ks ->
    disjoint_sets (filter_sets M (ks ∪ {[k]})) ->
    s ## union_sets (filter_sets M ks) ∧ disjoint_sets (filter_sets M ks).
  Proof using.
    intros Hk Hnot Hds.
    rewrite disjoint_sets_filter_sets_add_key_iff in Hds; eauto.
  Qed.

  Lemma disjoint_sets_filter_sets_remove_key_iff M ks k s :
    M !! k = Some s ->
    k ∈ ks ->
    disjoint_sets (filter_sets M ks) ↔
    disjoint_sets (filter_sets M (ks ∖ {[k]})) ∧
    s ## union_sets (filter_sets M (ks ∖ {[k]})).
  Proof using.
    intros Hk Hks.
    assert (filter_sets M ks !! k = Some s) as Hf.
    { apply filter_sets_lookup_Some. split; auto. }
    rewrite (disjoint_sets_lookup_iff (filter_sets M ks) k s Hf).
    rewrite <- (filter_sets_remove_key M ks k Hks).
    done.
  Qed.

  (** ** Exact kept/removed decomposition using the complementary keys [dom M ∖ ks] *)

  Lemma filter_sets_partition_complement_disjoint M ks :
    filter_sets M ks ##ₘ filter_sets M (dom M ∖ ks).
  Proof using.
    apply filter_sets_disjoint_keys.
    set_solver.
  Qed.

  Lemma union_difference_subseteq `{!EqDecision A, !Countable A} (a b : gset A) :
    a ⊆ b ∪ a ∖ b.
  Proof using.
    apply elem_of_subseteq. intros. destruct (decide (x ∈ b)).
    { apply elem_of_union_l; auto. }
    apply elem_of_union_r. set_solver.
  Qed.

  Lemma filter_sets_partition_complement M ks :
    filter_sets M ks ∪ filter_sets M (dom M ∖ ks) = M.
  Proof using.
    rewrite <- (filter_sets_union M ks (dom M ∖ ks)).
    apply filter_sets_full. eapply union_difference_subseteq.
  Qed.

  Lemma elem_of_union_sets_filter_sets_complement M ks e :
    e ∈ union_sets (filter_sets M (dom M ∖ ks)) ↔
    ∃ k s, M !! k = Some s ∧ k ∉ ks ∧ e ∈ s.
  Proof using.
    rewrite elem_of_union_sets_filter_sets.
    split.
    - intros (k&s&Hk&Hdiff&He).
      apply elem_of_difference in Hdiff as [_ Hnot].
      eauto.
    - intros (k&s&Hk&Hnot&He).
      exists k, s. split; [done|]. split.
      + apply elem_of_difference. split.
        * apply elem_of_dom. eauto.
        * done.
      + done.
  Qed.

  Lemma not_elem_of_union_sets_filter_sets_complement M ks e :
    e ∉ union_sets (filter_sets M (dom M ∖ ks)) ↔
    ∀ k s, M !! k = Some s -> k ∉ ks -> e ∉ s.
  Proof using.
    rewrite elem_of_union_sets_filter_sets_complement.
    split.
    - intros Hnot k s Hk Hks He.
      apply Hnot. eauto.
    - intros Hall Hin.
      destruct Hin as (k&s&Hk&Hks&He).
      eapply Hall; eauto.
  Qed.

  Lemma union_sets_filter_sets_complement M ks :
    union_sets M =
    union_sets (filter_sets M ks) ∪
    union_sets (filter_sets M (dom M ∖ ks)).
  Proof using.
    rewrite -union_sets_disj_union_L.
    2: apply filter_sets_partition_complement_disjoint.
    rewrite (filter_sets_partition_complement M ks). auto.
  Qed.

  Lemma elem_of_union_sets_filter_sets_partition M ks e :
    e ∈ union_sets M ↔
    e ∈ union_sets (filter_sets M ks) ∨
    e ∈ union_sets (filter_sets M (dom M ∖ ks)).
  Proof using.
    rewrite (union_sets_filter_sets_complement M ks).
    rewrite elem_of_union. done.
  Qed.

  Lemma union_sets_filter_sets_complement_disjoint M ks :
    disjoint_sets M ->
    union_sets (filter_sets M ks) ##
    union_sets (filter_sets M (dom M ∖ ks)).
  Proof using.
    intros HD.
    rewrite elem_of_disjoint.
    intros e He1 He2.
    apply elem_of_union_sets_filter_sets in He1 as (k1&s1&H1&Hks1&He1').
    apply elem_of_union_sets_filter_sets_complement in He2 as (k2&s2&H2&Hks2&He2').
    assert (k1 ≠ k2) as Hne.
    { intros ->. contradiction. }
    pose proof (HD k1 k2 s1 s2 Hne H1 H2) as Hdisj.
    rewrite elem_of_disjoint in Hdisj.
    eauto.
  Qed.

  Lemma disjoint_sets_filter_sets_complement_iff M ks :
    disjoint_sets M ↔
    disjoint_sets (filter_sets M ks) ∧
    disjoint_sets (filter_sets M (dom M ∖ ks)) ∧
    map_Forall
      (λ _ s, s ## union_sets (filter_sets M (dom M ∖ ks)))
      (filter_sets M ks).
  Proof using.
    apply disjoint_sets_filter_sets_full_partition_iff.
    - set_solver.
    - apply union_difference_subseteq.
  Qed.

  (** ** A small partition API for [filter_sets] *)

  Lemma filter_sets_partition_union M ks1 ks2 :
    dom M ⊆ ks1 ∪ ks2 ->
    filter_sets M ks1 ∪ filter_sets M ks2 = M.
  Proof using.
    intros Hcover.
    rewrite <- filter_sets_union.
    apply filter_sets_full. done.
  Qed.

  Lemma filter_sets_partition_disjoint M ks1 ks2 :
    ks1 ## ks2 ->
    filter_sets M ks1 ##ₘ filter_sets M ks2.
  Proof using.
    apply filter_sets_disjoint_keys.
  Qed.

  Lemma filter_sets_partition M ks1 ks2 :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    filter_sets M ks1 ##ₘ filter_sets M ks2 ∧
    filter_sets M ks1 ∪ filter_sets M ks2 = M.
  Proof using.
    intros Hdisj Hcover.
    split.
    - apply filter_sets_partition_disjoint. done.
    - apply filter_sets_partition_union. done.
  Qed.

  Lemma filter_sets_partition_dom M ks1 ks2 :
    dom M ⊆ ks1 ∪ ks2 ->
    dom M = dom (filter_sets M ks1) ∪ dom (filter_sets M ks2).
  Proof using.
    intros Hcover.
    rewrite !filter_sets_dom.
    apply set_eq=>k.
    set_solver.
  Qed.

  Lemma filter_sets_partition_dom_disjoint M ks1 ks2 :
    ks1 ## ks2 ->
    dom (filter_sets M ks1) ## dom (filter_sets M ks2).
  Proof using.
    intros Hdisj.
    rewrite elem_of_disjoint.
    intros k H1 H2.
    rewrite !filter_sets_dom in H1, H2.
    apply elem_of_intersection in H1 as [_ Hk1].
    apply elem_of_intersection in H2 as [_ Hk2].
    rewrite elem_of_disjoint in Hdisj.
    eapply (Hdisj k); eauto.
  Qed.

  Lemma filter_sets_partition_lookup_l M ks1 ks2 k s :
    ks1 ## ks2 ->
    M !! k = Some s ->
    k ∈ ks1 ->
    filter_sets M ks1 !! k = Some s ∧
    filter_sets M ks2 !! k = None.
  Proof using.
    intros Hdisj HM Hk1.
    split.
    - apply filter_sets_lookup_Some. split; auto.
    - apply filter_sets_lookup_None. right.
      rewrite elem_of_disjoint in Hdisj.
      intros Hk2. eapply (Hdisj k); eauto.
  Qed.

  Lemma filter_sets_partition_lookup_r M ks1 ks2 k s :
    ks1 ## ks2 ->
    M !! k = Some s ->
    k ∈ ks2 ->
    filter_sets M ks1 !! k = None ∧
    filter_sets M ks2 !! k = Some s.
  Proof using.
    intros Hdisj HM Hk2.
    split.
    - apply filter_sets_lookup_None. right.
      rewrite elem_of_disjoint in Hdisj.
      intros Hk1. eapply (Hdisj k); eauto.
    - apply filter_sets_lookup_Some. split; auto.
  Qed.

  Lemma filter_sets_partition_lookup M ks1 ks2 k s :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    M !! k = Some s ->
    (filter_sets M ks1 !! k = Some s ∧ filter_sets M ks2 !! k = None) ∨
    (filter_sets M ks1 !! k = None ∧ filter_sets M ks2 !! k = Some s).
  Proof using.
    intros Hdisj Hcover HM.
    assert (Hdom : k ∈ dom M) by (apply elem_of_dom; eauto).
    specialize (Hcover _ Hdom).
    destruct (decide (k ∈ ks1)) as [Hk1|Hnot1].
    - left. by apply filter_sets_partition_lookup_l.
    - right.
      apply elem_of_union in Hcover as [Hk1|Hk2].
      + contradiction.
      + by apply filter_sets_partition_lookup_r.
  Qed.

  Lemma filter_sets_partition_union_sets M ks1 ks2 :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    union_sets M =
    union_sets (filter_sets M ks1) ∪ union_sets (filter_sets M ks2).
  Proof using.
    apply union_sets_filter_sets_partition.
  Qed.

  Lemma elem_of_union_sets_filter_sets_partition_subseteq M ks1 ks2 e :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    e ∈ union_sets M ↔
    e ∈ union_sets (filter_sets M ks1) ∨
    e ∈ union_sets (filter_sets M ks2).
  Proof using.
    intros Hdisj Hcover.
    rewrite (filter_sets_partition_union_sets M ks1 ks2 Hdisj Hcover).
    rewrite elem_of_union. done.
  Qed.

  Lemma union_sets_filter_sets_partition_disjoint M ks1 ks2 :
    ks1 ## ks2 ->
    disjoint_sets M ->
    union_sets (filter_sets M ks1) ## union_sets (filter_sets M ks2).
  Proof using.
    intros Hdisj HD.
    rewrite elem_of_disjoint.
    intros e He1 He2.
    apply elem_of_union_sets_filter_sets in He1 as (k1&s1&H1&Hks1&He1').
    apply elem_of_union_sets_filter_sets in He2 as (k2&s2&H2&Hks2&He2').
    assert (Hne : k1 ≠ k2).
    { intros ->.
      rewrite elem_of_disjoint in Hdisj.
      eapply (Hdisj k2); eauto.
    }
    pose proof (HD k1 k2 s1 s2 Hne H1 H2) as Hdisj12.
    rewrite elem_of_disjoint in Hdisj12.
    eauto.
  Qed.

  Lemma filter_sets_partition_disjoint_sets_inv M ks1 ks2 :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    disjoint_sets M ->
    disjoint_sets (filter_sets M ks1) ∧
    disjoint_sets (filter_sets M ks2) ∧
    map_Forall (λ _ s, s ## union_sets (filter_sets M ks2)) (filter_sets M ks1).
  Proof using.
    intros Hdisj Hcover HD.
    apply (proj1 (disjoint_sets_filter_sets_full_partition_iff M ks1 ks2 Hdisj Hcover)).
    done.
  Qed.

  Lemma filter_sets_partition_disjoint_sets M ks1 ks2 :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    disjoint_sets (filter_sets M ks1) ->
    disjoint_sets (filter_sets M ks2) ->
    map_Forall (λ _ s, s ## union_sets (filter_sets M ks2)) (filter_sets M ks1) ->
    disjoint_sets M.
  Proof using.
    intros Hdisj Hcover H1 H2 H12.
    apply (proj2 (disjoint_sets_filter_sets_full_partition_iff M ks1 ks2 Hdisj Hcover)).
    repeat split; auto.
  Qed.

  Lemma filter_sets_partition_disjoint_sets_iff M ks1 ks2 :
    ks1 ## ks2 ->
    dom M ⊆ ks1 ∪ ks2 ->
    disjoint_sets M ↔
    disjoint_sets (filter_sets M ks1) ∧
    disjoint_sets (filter_sets M ks2) ∧
    map_Forall (λ _ s, s ## union_sets (filter_sets M ks2)) (filter_sets M ks1).
  Proof using.
    apply disjoint_sets_filter_sets_full_partition_iff.
  Qed.

End filter_sets.
