(** Lists of finite sets: their union [union_list_of_sets] and pairwise disjointness
    [disjoint_list_of_sets], under list and set operations. *)

From iris.proofmode Require Import proofmode.

Definition union_list_of_sets `{!EqDecision E} `{!Countable E} (L : list (gset E)) : gset E :=
  foldr (λ B A, B ∪ A) ∅ L.
Definition disjoint_list_of_sets `{!EqDecision E} `{!Countable E} (L : list (gset E)) : Prop :=
  ∀ j1 j2 s1 s2, j1 ≠ j2 → L !! j1 = Some s1 → L !! j2 = Some s2 → s1 ## s2.

Section list_of_sets.
  Context `{!EqDecision E, !Countable E}.
  Implicit Type L : list (gset E).
  Implicit Type s : gset E.
  Implicit Type i j : nat.
  Implicit Type e : E.

  (** ** Basic properties of [union_list_of_sets] *)

  Lemma union_list_of_sets_nil : union_list_of_sets ([] : list (gset E)) = ∅.
  Proof using. done. Qed.

  Lemma union_list_of_sets_cons s L :
    union_list_of_sets (s :: L) = s ∪ union_list_of_sets L.
  Proof using. done. Qed.

  Lemma union_list_of_sets_singleton s :
    union_list_of_sets [s] = s.
  Proof using.
    rewrite union_list_of_sets_cons union_list_of_sets_nil. set_solver.
  Qed.

  Lemma union_list_of_sets_app L1 L2 :
    union_list_of_sets (L1 ++ L2) =
    union_list_of_sets L1 ∪ union_list_of_sets L2.
  Proof using.
    induction L1 as [|s L1 IH]; simpl.
    - set_solver.
    - rewrite IH. set_solver.
  Qed.

  (** ** Membership characterisation of [union_list_of_sets] *)

  Lemma elem_of_union_list_of_sets L e :
    e ∈ union_list_of_sets L ↔ ∃ j s, L !! j = Some s ∧ e ∈ s.
  Proof using.
    induction L as [|x L IH].
    - rewrite union_list_of_sets_nil.
      split; [set_solver|].
      intros (j&s&Hj&_). by destruct j.
    - rewrite union_list_of_sets_cons elem_of_union IH.
      split.
      + intros [He | (j&s'&Hj&He)].
        * exists 0, x. by split.
        * exists (S j), s'. by split.
      + intros (j&s'&Hj&He).
        destruct j as [|j']; simpl in Hj.
        * injection Hj as ->. by left.
        * right. eauto.
  Qed.

  Lemma not_elem_of_union_list_of_sets L e :
    e ∉ union_list_of_sets L ↔ ∀ j s, L !! j = Some s → e ∉ s.
  Proof using.
    rewrite elem_of_union_list_of_sets. split; first naive_solver.
    intros HF (j&s&?&?). by eapply HF.
  Qed.

  (** ** [union_list_of_sets] interacts with lookups and sublists *)

  Lemma union_list_of_sets_lookup_subseteq L j s :
    L !! j = Some s → s ⊆ union_list_of_sets L.
  Proof using.
    intros ? e ?. apply elem_of_union_list_of_sets. eauto.
  Qed.

  Lemma union_list_of_sets_delete_L L j s :
    L !! j = Some s →
    union_list_of_sets L = s ∪ union_list_of_sets (delete j L).
  Proof using.
    intros Hj.
    replace L with (take j L ++ s :: drop (S j) L) at 1
      by (apply take_drop_middle; done).
    rewrite delete_take_drop.
    rewrite !union_list_of_sets_app union_list_of_sets_cons.
    set_solver.
  Qed.

  Lemma union_list_of_sets_eq_union_list L :
    union_list_of_sets L = ⋃ L.
  Proof using. done. Qed.

  Lemma elem_of_union_list_of_sets_elem_of L e :
    e ∈ union_list_of_sets L ↔ ∃ s, s ∈ L ∧ e ∈ s.
  Proof using.
    rewrite union_list_of_sets_eq_union_list elem_of_union_list. done.
  Qed.

  Lemma union_list_of_sets_mono L1 L2 :
    (∀ s, s ∈ L1 → s ∈ L2) →
    union_list_of_sets L1 ⊆ union_list_of_sets L2.
  Proof using.
    intros Hsub e He.
    apply elem_of_union_list_of_sets_elem_of in He as (s&Hs&He).
    apply elem_of_union_list_of_sets_elem_of. eauto.
  Qed.

  Lemma union_list_of_sets_sublist L1 L2 :
    L1 `sublist_of` L2 → union_list_of_sets L1 ⊆ union_list_of_sets L2.
  Proof using.
    intros Hsub. apply union_list_of_sets_mono.
    intros s Hs. eapply elem_of_submseteq; first eassumption.
    by apply sublist_submseteq.
  Qed.

  (** ** Basic properties of [disjoint_list_of_sets] *)

  Lemma disjoint_list_of_sets_lookup L j1 j2 s1 s2 :
    disjoint_list_of_sets L →
    j1 ≠ j2 → L !! j1 = Some s1 → L !! j2 = Some s2 → s1 ## s2.
  Proof using. intros HD; eauto. Qed.

  Lemma disjoint_list_of_sets_nil : disjoint_list_of_sets ([] : list (gset E)).
  Proof using. intros ?????? Hj. by destruct j1. Qed.

  Lemma disjoint_list_of_sets_singleton s :
    disjoint_list_of_sets [s].
  Proof using.
    intros [|[|?]] [|[|?]] s1 s2 Hne H1 H2; try done; simpl in *;
      try (by injection H1; injection H2; intros; subst).
  Qed.

  (** ** [disjoint_list_of_sets] is preserved by deleting an element *)

  Lemma disjoint_list_of_sets_delete L j :
    disjoint_list_of_sets L → disjoint_list_of_sets (delete j L).
  Proof using.
    intros HD j1 j2 s1 s2 Hne H1 H2.
    destruct (decide (j1 < j)) as [Hj1|Hj1];
      destruct (decide (j2 < j)) as [Hj2|Hj2].
    - rewrite list_lookup_delete_lt in H1; last done.
      rewrite list_lookup_delete_lt in H2; last done.
      eapply HD; eauto.
    - rewrite list_lookup_delete_lt in H1; last done.
      rewrite list_lookup_delete_ge in H2; last lia.
      eapply (HD j1 (S j2)); [lia | done | done].
    - rewrite list_lookup_delete_ge in H1; last lia.
      rewrite list_lookup_delete_lt in H2; last done.
      eapply (HD (S j1) j2); [lia | done | done].
    - rewrite list_lookup_delete_ge in H1; last lia.
      rewrite list_lookup_delete_ge in H2; last lia.
      eapply (HD (S j1) (S j2)); [lia | done | done].
  Qed.

  (** ** [disjoint_list_of_sets] under cons *)

  Lemma Forall_disjoint_union_list_of_sets L s :
    Forall (λ s', s ## s') L ↔ s ## union_list_of_sets L.
  Proof using.
    rewrite Forall_lookup elem_of_disjoint. split.
    - intros HF e He1 He2.
      apply elem_of_union_list_of_sets in He2 as (j&s'&Hj&He).
      eapply (HF j s'); eauto.
    - intros Hd j s' Hj. apply elem_of_disjoint. intros e He1 He2.
      apply (Hd e); auto. apply elem_of_union_list_of_sets. eauto.
  Qed.

  Lemma disjoint_list_of_sets_cons_iff s L :
    disjoint_list_of_sets (s :: L) ↔
    Forall (λ s', s ## s') L ∧ disjoint_list_of_sets L.
  Proof using.
    split.
    - intros HD. split.
      + apply Forall_lookup. intros j s' Hj.
        eapply (HD 0 (S j)); [done | done | done].
      + intros j1 j2 s1 s2 Hne H1 H2.
        eapply (HD (S j1) (S j2)); [lia | done | done].
    - intros [HF HD] j1 j2 s1 s2 Hne H1 H2.
      destruct j1 as [|j1']; destruct j2 as [|j2']; simpl in H1, H2.
      + congruence.
      + injection H1 as ->. rewrite Forall_lookup in HF.
        eapply HF; eauto.
      + injection H2 as ->. rewrite Forall_lookup in HF.
        symmetry. eapply HF; eauto.
      + eapply (HD j1' j2'); [lia | done | done].
  Qed.

  Lemma disjoint_list_of_sets_cons_union_list_of_sets s L :
    disjoint_list_of_sets (s :: L) ↔
    s ## union_list_of_sets L ∧ disjoint_list_of_sets L.
  Proof using.
    rewrite disjoint_list_of_sets_cons_iff.
    by rewrite Forall_disjoint_union_list_of_sets.
  Qed.

  Lemma disjoint_list_of_sets_cons_2 s L :
    s ## union_list_of_sets L →
    disjoint_list_of_sets L →
    disjoint_list_of_sets (s :: L).
  Proof using.
    intros. by apply disjoint_list_of_sets_cons_union_list_of_sets.
  Qed.

  Lemma disjoint_list_of_sets_cons_inv s L :
    disjoint_list_of_sets (s :: L) →
    s ## union_list_of_sets L ∧ disjoint_list_of_sets L.
  Proof using.
    intros. by apply disjoint_list_of_sets_cons_union_list_of_sets.
  Qed.

  Lemma disjoint_list_of_sets_lookup_disjoint_union_list_of_sets_delete L j s :
    disjoint_list_of_sets L →
    L !! j = Some s → s ## union_list_of_sets (delete j L).
  Proof using.
    intros HD Hj.
    apply Forall_disjoint_union_list_of_sets. apply Forall_lookup.
    intros j' s' Hj'.
    destruct (decide (j' < j)) as [Hlt|Hge].
    - rewrite list_lookup_delete_lt in Hj'; last done.
      eapply HD; [|exact Hj|exact Hj']. lia.
    - rewrite list_lookup_delete_ge in Hj'; last lia.
      eapply HD; [|exact Hj|exact Hj']. lia.
  Qed.

  (** ** [disjoint_list_of_sets] under append *)

  Lemma disjoint_list_of_sets_app_inv L1 L2 :
    disjoint_list_of_sets (L1 ++ L2) →
    disjoint_list_of_sets L1 ∧ disjoint_list_of_sets L2 ∧
    Forall (λ s, s ## union_list_of_sets L2) L1.
  Proof using.
    induction L1 as [|s L1 IH]; simpl.
    - intros HD. split_and!; auto using disjoint_list_of_sets_nil.
    - intros HD.
      apply disjoint_list_of_sets_cons_iff in HD as [HF HD].
      apply Forall_app in HF as [HF1 HF2].
      apply IH in HD as (HD1 & HD2 & HFcross).
      split_and!.
      + apply disjoint_list_of_sets_cons_iff. done.
      + done.
      + apply Forall_cons. split; auto.
        by apply Forall_disjoint_union_list_of_sets.
  Qed.

  Lemma disjoint_list_of_sets_app L1 L2 :
    disjoint_list_of_sets L1 → disjoint_list_of_sets L2 →
    Forall (λ s, s ## union_list_of_sets L2) L1 →
    disjoint_list_of_sets (L1 ++ L2).
  Proof using.
    induction L1 as [|s L1 IH]; simpl.
    - done.
    - intros HD1 HD2 HF.
      apply disjoint_list_of_sets_cons_iff in HD1 as [HFL1 HDL1].
      apply Forall_cons in HF as [Hcross HF].
      apply disjoint_list_of_sets_cons_iff. split.
      + apply Forall_app. split; auto.
        by apply Forall_disjoint_union_list_of_sets.
      + by apply IH.
  Qed.

  Lemma disjoint_list_of_sets_app_iff L1 L2 :
    disjoint_list_of_sets (L1 ++ L2) ↔
    disjoint_list_of_sets L1 ∧ disjoint_list_of_sets L2 ∧
    Forall (λ s, s ## union_list_of_sets L2) L1.
  Proof using.
    split.
    - by apply disjoint_list_of_sets_app_inv.
    - intros (?&?&?). by apply disjoint_list_of_sets_app.
  Qed.

  Lemma disjoint_list_of_sets_app_disjoint_iff L1 L2 :
    disjoint_list_of_sets (L1 ++ L2) ↔
    disjoint_list_of_sets L1 ∧ disjoint_list_of_sets L2 ∧
    union_list_of_sets L1 ## union_list_of_sets L2.
  Proof using.
    rewrite disjoint_list_of_sets_app_iff.
    do 2 (apply Morphisms_Prop.and_iff_morphism; [done|]).
    rewrite elem_of_disjoint.
    split.
    - intros HF e He1 He2.
      apply elem_of_union_list_of_sets in He1 as (j&s&Hj&He).
      rewrite Forall_lookup in HF. specialize (HF j s Hj).
      rewrite elem_of_disjoint in HF. eapply HF; eauto.
    - intros Hd. apply Forall_lookup. intros j s Hj.
      apply elem_of_disjoint. intros e He1 He2.
      apply (Hd e); auto. apply elem_of_union_list_of_sets. eauto.
  Qed.

  Lemma disjoint_list_of_sets_lookup_iff L j s :
    L !! j = Some s →
    disjoint_list_of_sets L ↔
    disjoint_list_of_sets (delete j L) ∧ s ## union_list_of_sets (delete j L).
  Proof using.
    intros Hj. split.
    - intros HD. split.
      + by apply disjoint_list_of_sets_delete.
      + by eapply disjoint_list_of_sets_lookup_disjoint_union_list_of_sets_delete.
    - intros [HDdel Hsd].
      pose proof (take_drop_middle L j s Hj) as Heq.
      rewrite delete_take_drop in HDdel, Hsd.
      rewrite union_list_of_sets_app in Hsd.
      apply disjoint_list_of_sets_app_inv in HDdel as (HD1 & HD2 & HF).
      rewrite -Heq. apply disjoint_list_of_sets_app.
      + done.
      + apply disjoint_list_of_sets_cons_2.
        * set_solver.
        * done.
      + apply Forall_lookup. intros j' s' Hj'.
        rewrite union_list_of_sets_cons disjoint_union_r. split.
        * apply elem_of_disjoint. intros e He' He.
          apply elem_of_disjoint in Hsd. eapply (Hsd e); first done.
          apply elem_of_union_l, elem_of_union_list_of_sets. eauto.
        * rewrite Forall_lookup in HF. by eapply HF.
  Qed.

  (** ** [union_list_of_sets] under set operations on individual values *)

  Lemma union_list_of_sets_insert_replace L j s s' :
    L !! j = Some s →
    union_list_of_sets (<[j:=s']>L) = s' ∪ union_list_of_sets (delete j L).
  Proof using.
    intros Hj.
    pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
    rewrite (insert_take_drop _ _ s' Hlt) delete_take_drop.
    rewrite !union_list_of_sets_app union_list_of_sets_cons.
    set_solver.
  Qed.

  Lemma union_list_of_sets_insert_union_L L j s s' :
    L !! j = Some s →
    union_list_of_sets (<[j:= s ∪ s']>L) = s' ∪ union_list_of_sets L.
  Proof using.
    intros Hj. rewrite (union_list_of_sets_insert_replace _ _ s); last done.
    rewrite (union_list_of_sets_delete_L _ _ _ Hj). set_solver.
  Qed.

  Lemma union_list_of_sets_insert_difference_subseteq L j s s' :
    L !! j = Some s →
    union_list_of_sets (<[j:= s ∖ s']>L) ⊆ union_list_of_sets L.
  Proof using.
    intros Hj. rewrite (union_list_of_sets_insert_replace _ _ s); last done.
    rewrite (union_list_of_sets_delete_L _ _ _ Hj). set_solver.
  Qed.

  Lemma union_list_of_sets_insert_difference_L L j s s' :
    disjoint_list_of_sets L →
    L !! j = Some s →
    union_list_of_sets (<[j:= s ∖ s']>L) = union_list_of_sets L ∖ (s' ∩ s).
  Proof using.
    intros HD Hj.
    pose proof (disjoint_list_of_sets_lookup_disjoint_union_list_of_sets_delete
                  _ _ _ HD Hj) as Hdj.
    rewrite (union_list_of_sets_insert_replace _ _ s); last done.
    rewrite (union_list_of_sets_delete_L _ _ _ Hj).
    apply set_eq. intros e. set_solver.
  Qed.

  Lemma union_list_of_sets_insert_difference_subseteq_L L j s s' :
    disjoint_list_of_sets L →
    L !! j = Some s →
    s' ⊆ s →
    union_list_of_sets (<[j:= s ∖ s']>L) = union_list_of_sets L ∖ s'.
  Proof using.
    intros. rewrite union_list_of_sets_insert_difference_L; auto.
    f_equal. set_solver.
  Qed.

  Lemma union_list_of_sets_insert_difference_singleton_L L j s e :
    disjoint_list_of_sets L →
    L !! j = Some s →
    e ∈ s →
    union_list_of_sets (<[j:= s ∖ {[e]}]>L) = union_list_of_sets L ∖ {[e]}.
  Proof using.
    intros. apply union_list_of_sets_insert_difference_subseteq_L; auto.
    set_solver.
  Qed.

  (** ** [disjoint_list_of_sets] under set operations on individual values *)

  Lemma disjoint_list_of_sets_insert_subseteq L j s s' :
    L !! j = Some s →
    s' ⊆ s →
    disjoint_list_of_sets L →
    disjoint_list_of_sets (<[j:=s']>L).
  Proof using.
    intros Hj Hsub HD j1 j2 s1 s2 Hne H1 H2.
    apply list_lookup_insert_Some in H1 as [(<- & <- & _)|[Hne1 H1]];
    apply list_lookup_insert_Some in H2 as [(<- & <- & _)|[Hne2 H2]].
    - exfalso. by apply Hne.
    - assert (s ## s2) by
        (eapply (HD j j2 s s2); [exact Hne | exact Hj | exact H2]).
      set_solver.
    - assert (s ## s1) by
        (eapply (HD j j1 s s1); [exact Hne1 | exact Hj | exact H1]).
      set_solver.
    - eapply (HD j1 j2 s1 s2); [exact Hne | exact H1 | exact H2].
  Qed.

  Lemma disjoint_list_of_sets_insert_difference L j s s' :
    L !! j = Some s →
    disjoint_list_of_sets L →
    disjoint_list_of_sets (<[j:= s ∖ s']>L).
  Proof using.
    intros. eapply disjoint_list_of_sets_insert_subseteq; eauto. set_solver.
  Qed.

  Lemma disjoint_list_of_sets_insert_union_iff L j s s' :
    L !! j = Some s →
    disjoint_list_of_sets (<[j:= s ∪ s']>L) ↔
    disjoint_list_of_sets L ∧ s' ## union_list_of_sets (delete j L).
  Proof using.
    intros Hj.
    pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
    assert ((<[j:= s ∪ s']>L) !! j = Some (s ∪ s')) as Hi.
    { by apply list_lookup_insert_eq. }
    rewrite (disjoint_list_of_sets_lookup_iff _ _ _ Hi).
    assert (delete j (<[j:= s ∪ s']>L) = delete j L) as ->.
    { apply list_eq=>k. destruct (decide (k < j)) as [Hlt2|Hge2].
      - rewrite !list_lookup_delete_lt; auto.
        rewrite list_lookup_insert_ne; [done|lia].
      - rewrite !list_lookup_delete_ge; try lia.
        rewrite list_lookup_insert_ne; [done|lia]. }
    rewrite (disjoint_list_of_sets_lookup_iff _ _ _ Hj).
    rewrite disjoint_union_l. tauto.
  Qed.

  Lemma disjoint_list_of_sets_insert_union L j s s' :
    L !! j = Some s →
    disjoint_list_of_sets L →
    s' ## union_list_of_sets (delete j L) →
    disjoint_list_of_sets (<[j:= s ∪ s']>L).
  Proof using.
    intros. by apply disjoint_list_of_sets_insert_union_iff.
  Qed.

  Lemma disjoint_list_of_sets_insert_union_inv L j s s' :
    L !! j = Some s →
    disjoint_list_of_sets (<[j:= s ∪ s']>L) →
    disjoint_list_of_sets L ∧ s' ## union_list_of_sets (delete j L).
  Proof using.
    intros Hj HD. by apply (disjoint_list_of_sets_insert_union_iff _ _ _ _ Hj).
  Qed.

  Lemma disjoint_list_of_sets_insert_union_singleton L j s e :
    L !! j = Some s →
    disjoint_list_of_sets L →
    e ∉ union_list_of_sets (delete j L) →
    disjoint_list_of_sets (<[j:= s ∪ {[e]}]>L).
  Proof using.
    intros. apply disjoint_list_of_sets_insert_union; auto. set_solver.
  Qed.

  Lemma disjoint_list_of_sets_insert_union_singleton_not_in L j s e :
    L !! j = Some s →
    disjoint_list_of_sets L →
    e ∉ union_list_of_sets L →
    disjoint_list_of_sets (<[j:= s ∪ {[e]}]>L).
  Proof using.
    intros Hj HD He. apply disjoint_list_of_sets_insert_union_singleton; auto.
    rewrite (union_list_of_sets_delete_L L j s) in He; auto. set_solver.
  Qed.

End list_of_sets.
